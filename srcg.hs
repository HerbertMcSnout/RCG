--ghc -main-is SRCG srcg.hs rcg.hs
module SRCG where
import System.Environment (getArgs, getProgName)
import RCG hiding (main)
import qualified Data.Set as Set
import qualified Data.Map as Map
import qualified Data.List as List

-- See https://link.springer.com/content/pdf/10.1007/978-3-642-14846-0_6.pdf


-- An RCG has an equivalent SRCG iff two conditions hold:
--   1. Each argument appearing in the rhs of a clause is a single variable
--   2. Each variable of the lhs of a clause appears exactly once in the rhs, and vice-versa
isSRCG :: RCG -> Bool
isSRCG (RCG n t v s p) = all linearClause p
  where
    singleVar :: [Atom] -> Maybe [Variable]
    singleVar [] = Just []
    singleVar [AtomVar v] = Just [v]
    singleVar _ = Nothing
    
    -- List of all the variables from a list of atoms
    vars :: [Atom] -> [Variable]
    vars = concatMap (\a -> case a of {(AtomTrm t) -> []; (AtomVar v) -> [v]})

    -- Makes sure there are no terminals (for use in rhs clauses)
    allvars :: [Atom] -> Maybe ()
    allvars as = if length (vars as) == length as then Just () else Nothing

    toSetNoDups :: Ord a => [a] -> Maybe (Set.Set a)
    toSetNoDups = foldr (\a as -> as >>= \as ->
                            if a `Set.member` as then
                              Nothing
                            else
                              Just (Set.insert a as))
                        (Just mempty)

    predArgs :: Predicate -> Maybe (Set.Set Variable)
    predArgs (Predicate nt as) = toSetNoDups (concatMap (\(Arg a) -> vars a) as)

    rhsArgs :: Predicate -> Maybe (Set.Set Variable)
    rhsArgs (Predicate nt as) = concat <$> mapM (\(Arg a) -> singleVar a) as >>= toSetNoDups

    -- Decides if a clause uses each var exactly once, has no dup args on the lhs,
    -- and no terminals on the rhs
    linearClause :: Clause -> Bool
    linearClause (lhs :->: rhs) =
      maybe False Set.null
        (mapM rhsArgs rhs >>=
         foldr (\r vs -> vs >>= \vs ->
                   if r `Set.isSubsetOf` vs then
                     Just (vs Set.\\ r)
                   else
                     Nothing)
               (predArgs lhs))

preamble :: RCG -> String
preamble rcg =
  "data Char = " ++ List.intercalate " | " (map show (Set.toList (rcgT rcg))) ++ ";\n" ++
  "data String = Nil | Cons Char String;\n\
  \data Streeng = Eps | Trm Char | Cat Streeng Streeng;\n\
  \data Maybe a = None | Some a;\n\
  \\n\
  \define streeqh st s =\n\
  \  case st of\n\
  \    | Eps -> Some s\n\
  \    | Trm c -> (case s of Nil -> None | Cons c' s -> if c == c' then Some s else None)\n\
  \    | Cat st1 st2 ->\n\
  \      let s' = streeqh st1 s in\n\
  \        case s' of None -> None | Some s' -> streeqh st2 s';\n\
  \define streeq st s =\n\
  \  let s' = streeqh st s in\n\
  \    case s' of None -> False | Some s' -> case s' of Nil -> True | Cons _ _ -> False;\n\n"

postamble :: String -> RCG -> String
postamble input rcg =
  "streeq " ++ show (rcgS rcg) ++ " " ++ foldr (\c rest -> "(Cons " ++ c : " " ++ rest ++ ")") "Nil" input

srcgToPerpl :: String -> RCG -> String
--srcgToPerpl input rcg
--  | not (isSRCG rcg) = error ("Not a valid SRCG: " ++ show rcg)
srcgToPerpl input rcg =
  preamble rcg ++
  List.intercalate "\n" [clauseToPerpl nt rhss | (nt, rhss) <- Map.toList (clauseMap (rcgP rcg))] ++ "\n" ++ postamble input rcg
  where
    clauseMap :: [Clause] -> Map.Map Nonterminal [([Arg], [Predicate])]
    clauseMap cls = Map.unionsWith (++) [Map.singleton (predN lhs) [(predA lhs, rhs)] | (lhs :->: rhs) <- cls]

    ambs :: [String] -> String
    ambs [] = "fail"
    --ambs [s] = s
    ambs ss = "amb\n  " ++ List.intercalate "\n  " ss

    atomToPerpl :: Atom -> String
    atomToPerpl (AtomVar v) = show v
    atomToPerpl (AtomTrm t) = "(Trm " ++ show t ++ ")"

    argToPerpl :: Arg -> String
    argToPerpl (Arg []) = "Eps"
    argToPerpl (Arg as) =
      let as' = init as
          a = last as in
      foldr (\a rest -> "(Cat " ++ atomToPerpl a ++ " " ++ rest ++ ")") (atomToPerpl a) as'

    argsToPerpl :: [Arg] -> String
    argsToPerpl as = "(" ++ List.intercalate ", " [argToPerpl a | a <- as] ++ ")"

    clauseToPerpl :: Nonterminal -> [([Arg], [Predicate])] -> String
    clauseToPerpl nt rhss =
      "define " ++ show nt ++ " = " ++
      ambs ["(" ++ foldr (\(Predicate nt' as') rest -> "let " ++ argsToPerpl as' ++ " = " ++ show nt' ++ " in " ++ rest)
                  (argsToPerpl as) rhs ++ ") -- " ++ show (Predicate nt as :->: rhs) | (as, rhs) <- rhss] ++ "\n  ;"

main :: IO ()
main =
  getArgs >>= \as ->
  getProgName >>= \nm ->
  case as of
    [fn, input] -> parseRCG <$> readFile fn >>= maybe (parseError fn) (putStrLn . srcgToPerpl input)
    _ -> putStrLn ("Usage: " ++ nm ++ " <grammar file> <input string>")

