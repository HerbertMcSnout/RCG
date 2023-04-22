--ghc -main-is RCGtoPERPL rcgToPerpl.hs rcg.hs
module RCGtoPERPL where
import System.Environment (getArgs, getProgName)
import RCG hiding (main)
import qualified Data.Set as Set
import qualified Data.Map as Map
import qualified Data.List as List
import Control.Monad.State

-- See https://link.springer.com/content/pdf/10.1007/978-3-642-14846-0_6.pdf


preamble :: RCG -> String
preamble rcg =
  "data Char = " ++ List.intercalate " | " (map show (Set.toList (rcgT rcg))) ++ ";\n" ++
  "data String = Nil | Cons Char String;\n\
  \data Streeng = Eps | Trm Char | Cat Streeng Streeng | And Streeng Streeng;\n\
  \data Maybe a = None | Some a;\n\
  \\n\
  \define streeqh st s =\n\
  \  case st of\n\
  \    | Eps -> Some s\n\
  \    | Trm c -> (case s of Nil -> None | Cons c' s -> if c == c' then Some s else None)\n\
  \    | Cat st1 st2 ->\n\
  \      let s' = streeqh st1 s in\n\
  \        (case s' of None -> None | Some s' -> streeqh st2 s')\n\
  \    | And st1 st2 ->\n\
  \      (case streeqh st1 s of None -> None | Some s' ->\n\
  \        (case streeqh st2 s of None -> None | Some s'' ->\n\
  \          if s' == s'' then Some s' else None));\n\
  \define streeq st s =\n\
  \  let s' = streeqh st s in\n\
  \    case s' of None -> False | Some s' -> case s' of Nil -> True | Cons _ _ -> False;\n\n"

anyName = "_ANY_"

-- Clauses for rule that accepts any arbitrary string
anyClauses :: [Terminal] -> [Clause]
anyClauses alphabet =
  -- ANY() ->
  -- ANY(XY) -> ANY(X) ANY(Y)
  -- ANY(c) ->
  let nt = (Nonterminal anyName)
      x = Variable 'X'
      y = Variable 'Y' in
    (Predicate nt [Arg []] :->: []) :
    (Predicate nt [Arg [AtomVar x, AtomVar y]] :->:
       [Predicate nt [Arg [AtomVar x]],
        Predicate nt [Arg [AtomVar y]]]) :
    map (\c -> Predicate nt [Arg [AtomTrm c]] :->: []) alphabet

-- TODO: "normalize" rcgs, and use _ANY_ for unused vars

postamble :: String -> RCG -> String
postamble input rcg =
  "streeq " ++ show (rcgS rcg) ++ " " ++ foldr (\c rest -> "(Cons " ++ c : " " ++ rest ++ ")") "Nil" input
  
type RenameM a = State (Map.Map Variable [Variable], Map.Map Variable Variable) a

rcgToPerpl :: String -> RCG -> String
rcgToPerpl input rcg =
  preamble rcg ++
  List.intercalate "\n" [clauseToPerpl nt rhss | (nt, rhss) <- Map.toList (clauseMap (rcgP rcg))] ++ "\n" ++ postamble input rcg
  where
    clauseMap :: [Clause] -> Map.Map Nonterminal [([Arg], [Predicate])]
    clauseMap cls = Map.unionsWith (++) [Map.singleton (predN lhs) [(predA lhs, rhs)] | (lhs :->: rhs) <- cls ++ anyCs]

    anyCs = anyClauses (Set.toList (rcgT rcg))

    ambs :: [String] -> String
    ambs [] = "fail"
    ambs [s] = "\n  " ++ s
    ambs ss = "amb\n  " ++ List.intercalate "\n  " ss

    cats :: [String] -> String
    cats [] = "Eps"
    cats [s] = s
    cats (s : ss) = "(Cat " ++ s ++ " " ++ cats ss ++ ")"

    ands :: [String] -> String
    ands [] = anyName
    ands [s] = s
    ands (s : ss) = "(And " ++ s ++ " " ++ ands ss ++ ")"

    atomToPerpl :: Atom -> RenameM String
    atomToPerpl (AtomVar v) =
      get >>= \(vs, rs) ->
      return (ands (map show (maybe [v] id (vs Map.!? v))))
    atomToPerpl (AtomTrm t) = return ("(Trm " ++ show t ++ ")")

    argToPerpl :: Arg -> RenameM String
    argToPerpl (Arg as) = cats <$> mapM atomToPerpl as

    argsToPerpl :: [Arg] -> RenameM String
    argsToPerpl [a] = argToPerpl a
    argsToPerpl as =
      mapM argToPerpl as >>= \as' ->
      return ("(" ++ List.intercalate ", " as' ++ ")")

    argsToPerpl' :: [Arg] -> String
    argsToPerpl' [a] = argToPerpl' a
    argsToPerpl' as = "(" ++ List.intercalate ", " (map argToPerpl' as) ++ ")"

    argToPerpl' :: Arg -> String
    argToPerpl' (Arg [AtomVar v]) = show v
    argToPerpl' (Arg as) = concatMap atomToPerpl' as

    atomToPerpl' :: Atom -> String
    atomToPerpl' (AtomVar v) = show v
    atomToPerpl' (AtomTrm t) = show t

    addRename :: Variable -> Variable -> RenameM ()
    addRename v v' =
      modify $ \(vs, rs) -> (Map.insertWith (++) v [v'] vs, Map.insert v' v rs)

    freshVar :: Variable -> RenameM Variable
    freshVar t =
      get >>= \(vs, rs) ->
      h t vs rs ts
      where
        -- pick a new terminal until we find an unused one
        ts = Variable <$> (['A'..'Z'] ++ ['a'..'z'] ++ map toEnum [128..])
        h t' vs rs (t'' : ts)
          | t' `Map.member` rs || t' `Map.member` vs = h t'' vs rs ts
          | otherwise = addRename t t' >> return t'
    
    renamePred :: Predicate -> RenameM Predicate
    renamePred (Predicate nt as) = Predicate nt <$> mapM renameArg as
    
    renameArg :: Arg -> RenameM Arg
    renameArg (Arg as) = Arg <$> mapM renameAtom as

    renameAtom :: Atom -> RenameM Atom
    renameAtom (AtomVar v) = AtomVar <$> freshVar v
    renameAtom (AtomTrm t) = return (AtomTrm t)

    clauseh' :: [Arg] -> [Predicate] -> RenameM String
    clauseh' as ps =
      mapM renamePred ps >>=
      foldr
        (\(Predicate nt' as') rest ->
           rest >>= \restr ->
           return ("let " ++ argsToPerpl' as' ++ " = " ++ show nt' ++ " in " ++ restr))
        (argsToPerpl as)

    clauseh :: [Arg] -> [Predicate] -> String
    clauseh as ps =
      let (s, (vs, rs)) = runState (clauseh' as ps) (mempty, mempty) in s

    clauseToPerpl :: Nonterminal -> [([Arg], [Predicate])] -> String
    clauseToPerpl nt rhss =
      "define " ++ show nt ++ " = " ++
      ambs ["(" ++ clauseh as rhs ++ ") -- " ++ show (Predicate nt as :->: rhs)
           | (as, rhs) <- rhss] ++ "\n  ;"

main :: IO ()
main =
  getArgs >>= \as ->
  getProgName >>= \nm ->
  case as of
    [fn, input] -> parseRCG <$> readFile fn >>= maybe (parseError fn) (putStrLn . rcgToPerpl input)
    _ -> putStrLn ("Usage: " ++ nm ++ " <grammar file> <input string>")

