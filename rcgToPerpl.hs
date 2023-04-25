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
  \    case s' of None -> fail | Some s' -> case s' of Nil -> () | Cons _ _ -> fail;\n\n"

anyNT = Nonterminal "_ANY_"
oneNT = Nonterminal "_ONE_"

-- Clauses for rule that accepts any arbitrary string
anyClauses :: [Terminal] -> [Clause]
anyClauses alphabet =
  -- ANY() ->
  -- ANY(XY) -> ONE(X) ANY(Y)
  -- ONE(c) ->      [foreach terminal c]
  let x = Variable 'X'
      y = Variable 'Y' in
    (Predicate anyNT [Arg []] :->: []) :
    (Predicate anyNT [Arg [AtomVar x, AtomVar y]] :->:
       [Predicate oneNT [Arg [AtomVar x]],
        Predicate anyNT [Arg [AtomVar y]]]) :
    map (\c -> Predicate oneNT [Arg [AtomTrm c]] :->: []) alphabet

postamble :: String -> RCG -> String
postamble input rcg =
  "streeq " ++ show (rcgS rcg) ++ " "
    ++ foldr (\c rest -> "(Cons " ++ c : " " ++ rest ++ ")") "Nil" input
  
type RenameM a = State (Map.Map Variable [Variable], Map.Map Variable Arg) a

-- For two lists A and B where A is a sublist of B,
-- returns the rest of B that surrounds A
-- Returns at first match if A is a sublist of B in
-- multiple places (e.g. A = [0] and B = [1,0,1,0,1])
findSublist :: Eq a => [a] -> [a] -> Maybe ([a], [a])
findSublist = h [] where
  prefix [] bs = Just bs
  prefix (a : as) (b : bs)
    | a == b = prefix as bs
    | otherwise = Nothing
  prefix (a : as) [] = Nothing
  
  h acc as [] = Nothing
  h acc as (b : bs) = maybe (h (b : acc) as bs) (\(s) -> Just (reverse acc, s)) (prefix as (b : bs))

rcgToPerpl :: String -> RCG -> String
rcgToPerpl input rcg =
  preamble rcg ++
  List.intercalate "\n"
    [clauseToPerpl nt rhss
      | (nt, rhss) <- Map.toList (clauseMap (rcgP rcg))]
  ++ "\n" ++ postamble input rcg
  where
    clauseMap :: [Clause] -> Map.Map Nonterminal [([Arg], [Predicate])]
    clauseMap cls = Map.unionsWith (++)
      [Map.singleton (predN lhs) [(predA lhs, rhs)]
        | (lhs :->: rhs) <- cls ++ anyCs]

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
    ands [] = show anyNT
    ands [s] = s
    ands (s : ss) = "(And " ++ s ++ " " ++ ands ss ++ ")"

    atomToPerpl :: Atom -> RenameM String
    atomToPerpl (AtomVar v) =
      get >>= \(vs, rs) ->
      return (ands (map show (maybe [v] id (vs Map.!? v))))
    atomToPerpl (AtomTrm t) = return ("(Trm " ++ show t ++ ")")

    argToPerpl :: Arg -> RenameM String
    argToPerpl (Arg as) =
      get >>= \(vs, rs) ->
      cats <$> mapM atomToPerpl as >>= \s ->
      composites (Arg as) rs >>= \cs ->
      return (ands (s : cs))

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
      modify $ \(vs, rs) -> (Map.insertWith (++) v [v'] vs, Map.insert v' (Arg [AtomVar v]) rs)

    addComposite :: Arg -> Variable -> RenameM ()
    addComposite a t =
      modify $ \(vs, rs) -> (vs, Map.insert t a rs)

    freshVar :: Variable -> RenameM Variable
    freshVar t =
      get >>= \(vs, rs) ->
      h t vs rs ts
      where
        -- pick a new terminal until we find an unused one
        ts = Variable <$> (['A'..'Z'] ++ ['a'..'z'] ++ map toEnum [128..])
        h t'@(Variable s) vs rs (t'' : ts)
          |  t' `Map.member` rs
          || t' `Map.member` vs
          || Nonterminal [s] `Set.member` rcgN rcg -- avoid conflicts with nonterminals
          || Terminal     s  `Set.member` rcgT rcg -- avoid conflicts with terminals
            = h t'' vs rs ts
          | otherwise = return t'

    newVar :: Variable -> RenameM Variable
    newVar t = freshVar t >>= \t' -> addRename t t' >> return t'

    -- TODO: can we do negative RCGs?
    -- TODO: if PERPL can do isPrime... then have we shown PRCG = NRCG?

    renamePred :: Predicate -> RenameM Predicate
    renamePred (Predicate nt as) = Predicate nt <$> mapM renameArg as
    
    renameArg :: Arg -> RenameM Arg
    renameArg (Arg as)
      | length as >= 2 =
        --let h (AtomVar v) = modify $ \(vs, rs) -> (Map.insert v [] vs, rs)
        --    h (AtomTrm c) = return () in
        freshVar (Variable 'A') >>= \v ->
        mapM renameAtom as >>= \as' ->
        --let as' = as in
        --mapM h as' >>
        addComposite (Arg as') v >>
        return (Arg [AtomVar v])
      | otherwise = Arg <$> mapM renameAtom as
      -- S(XX) -> A(X, X) B(XX) becomes let (X, Y) = A in let Z = B in And B (Cat X Y)

    renameAtom :: Atom -> RenameM Atom
    renameAtom (AtomVar v) = AtomVar <$> newVar v
    renameAtom (AtomTrm t) = return (AtomTrm t)

    -- Reconstructs all partial composite args (e.g. S(XYZ) -> A(XY) B(YZ))
    -- to be like And (Cat X (Cat Y Z)) (And (Cat M Z) (Cat X N)), thereby
    -- forcing M = XY and N = YZ
    composites :: Arg -> Map.Map Variable Arg -> RenameM [String]
    composites a m =
      foldr (maybe id (:)) []
      <$> mapM (composite a) (filter (\(v, Arg as) -> length as > 1) (Map.toList m))

    composite :: Arg -> (Variable, Arg) -> RenameM (Maybe String)
    composite (Arg a') (v, Arg a) =
      maybe
        (return Nothing)
        (\(pfx, sfx) -> Just <$> cats <$> mapM atomToPerpl (pfx ++ AtomVar v : sfx))
        (findSublist a a')

    defaultEmpty :: [Atom] -> String -> RenameM String
    defaultEmpty [] s = return s
    defaultEmpty (AtomTrm c : as) s = defaultEmpty as s
    defaultEmpty (AtomVar v : as) s =
      defaultEmpty as s >>= \s' ->
      get >>= \(vs, rs) ->
      maybe
        (-- vvv don't repeat this, e.g. for `S(XX)->` we don't want two `let X = ANY`'s
         put (Map.insert v [v] vs, rs) >>
         return ("let " ++ show v ++ " = " ++ show anyNT ++ " in " ++ s'))
        (\_ -> return s')
        (vs Map.!? v)
    defaultEmptyArg :: [Arg] -> String -> RenameM String
    defaultEmptyArg [] s = return s
    defaultEmptyArg (Arg a : as) s =
      defaultEmptyArg as s >>= \s' ->
      defaultEmpty a s'

    clauseh' :: [Arg] -> [Predicate] -> RenameM String
    clauseh' as ps =
      mapM renamePred ps >>= \ps' ->
      get >>= \(vs, rs) ->
      foldr
        (\(Predicate nt' as') rest ->
           rest >>= \restr ->
           return ("let " ++ argsToPerpl' as' ++ " = " ++ show nt' ++ " in " ++ restr))
        (argsToPerpl as >>= defaultEmptyArg as) ps'

    clauseh :: [Arg] -> [Predicate] -> String
    clauseh as ps =
      let (s, (vs, rs)) = runState (clauseh' as ps) (Map.empty, Map.empty) in s

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

