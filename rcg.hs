module RCG where
import Data.List (intercalate)
import Data.Maybe (catMaybes)
import qualified Data.Set as Set -- (Set, member, delete, fromList, toList)
import qualified Data.Map as Map -- (Map, member, lookup, insert)
import Control.Monad.State
import Debug.Trace (trace)

-- (Positive) Range Concatenation Grammar
data RCG = RCG {
  rcgN :: Set.Set Nonterminal,
  rcgT :: Set.Set Terminal,
  rcgV :: Set.Set Variable,
  rcgS :: Nonterminal,
  rcgP :: [Clause]
  }
newtype Nonterminal = Nonterminal String deriving (Eq, Ord)
newtype Terminal = Terminal Char deriving (Eq, Ord)
newtype Variable = Variable Char deriving (Eq, Ord)
data Atom =
    AtomTrm Terminal
  | AtomVar Variable
  deriving (Eq, Ord)
newtype Arg = Arg [Atom] deriving (Eq, Ord)
data Predicate = Predicate {predN :: Nonterminal, predA :: [Arg]} deriving (Eq, Ord)

infix 8 :->:
data Clause = (:->:) {clauseLHS :: Predicate, clauseRHS :: [Predicate]}

instance Show Nonterminal where
  show (Nonterminal n) = n
instance Show Terminal where
  show (Terminal c) = [c]
instance Show Variable where
  show (Variable s) = [s]
instance Show Atom where
  show (AtomTrm t) = show t
  show (AtomVar v) = show v
instance Show Arg where
  show (Arg as) = concatMap show as
instance Show Clause where
  show (lhs :->: rhs) =
    show lhs ++ " -> " ++ concatMap show rhs
instance Show Predicate where
  show (Predicate n a) =
    show n ++ '(' : intercalate "," (map show a) ++ ")"
instance Show RCG where
  show (RCG n t v s p) =
    intercalate "\n" [
      "N: " ++ intercalate " " (map show $ Set.toList n),
      "T: " ++ concat (map show $ Set.toList t),
      "V: " ++ concat (map show $ Set.toList v),
      "S: " ++ show s
      ] ++ "\n" ++
    intercalate "\n" (map show p)

parseNonterminals :: String -> Set.Set Nonterminal
parseNonterminals = Set.fromList . map Nonterminal . words

parseVariables :: String -> Set.Set Variable
parseVariables = Set.delete (Variable ' ') . Set.fromList . map Variable

parseTerminals :: String -> Set.Set Terminal
parseTerminals = Set.delete (Terminal ' ') . Set.fromList . map Terminal

parseClause :: Set.Set Nonterminal -> Set.Set Terminal -> Set.Set Variable -> String -> Maybe Clause
parseClause n t v s =
  parsePred s >>= \(lhs, s') ->
  parseArrow s' >>= \s'' ->
  parsePreds s'' >>= \rhs ->
  Just (lhs :->: rhs)
  where
    parsePreds :: String -> Maybe [Predicate]
    parsePreds "" = Just []
    parsePreds s = parsePred s >>= \(p, s') -> ((:) p) <$> parsePreds s'
    
    parseArrow :: String -> Maybe String
    parseArrow (' ' : s) = parseArrow s
    parseArrow ('-' : '>' : rhs) = Just rhs
    parseArrow _ = Nothing

    parseArg :: String -> Maybe Arg
    parseArg = parseArgh []

    parseArgh :: [Atom] -> String -> Maybe Arg
    parseArgh atoms [] = Just (Arg (reverse atoms))
    parseArgh atoms (c : s)
      | Terminal c `Set.member` t = parseArgh (AtomTrm (Terminal c) : atoms) s
      | Variable c `Set.member` v = parseArgh (AtomVar (Variable c) : atoms) s
      | otherwise = Nothing

    parsePred :: String -> Maybe (Predicate, String)
    parsePred s = parsePredh (Left "") s >>= \(n, a, rest) -> Just (Predicate n a, rest)
    
    parsePredh :: Either String (Nonterminal, [Arg], String) -> String -> Maybe (Nonterminal, [Arg], String)
    parsePredh (Left "") (' ' : s) = parsePredh (Left "") s
    parsePredh (Left acc) [] =
      Nothing
    parsePredh (Left acc) ('(' : as) =
      let ns = Nonterminal (reverse acc) in
        if ns `Set.member` n then
          parsePredh (Right (ns, [], "")) as
        else
          Nothing
    parsePredh (Left acc) (c : as) =
      parsePredh (Left (c : acc)) as
    parsePredh (Right (n, a, acc)) (' ' : as) =
      parsePredh (Right (n, a, acc)) as
    parsePredh (Right (n, a, acc)) (',' : as) =
      parseArg (reverse acc) >>= \arg ->
      parsePredh (Right (n, arg : a, "")) as
    --parsePredh (Right (n, a, [])) (')' : rest) =
    --  Just (n, reverse a, rest)
    parsePredh (Right (n, a, acc)) (')' : rest) =
      parseArg (reverse acc) >>= \arg ->
      Just (n, reverse (arg : a), rest)
    parsePredh (Right (n, a, acc)) (c : as) =
      parsePredh (Right (n, a, c : acc)) as

parseRCG :: String -> Maybe RCG
parseRCG s =
  case lines s of
    n' : t' : v' : s' : p' ->
      let n = parseNonterminals (dropPrefix "N:" n')
          t = parseTerminals (dropPrefix "T:" t')
          v = parseVariables (dropPrefix "V:" v')
          s = Nonterminal (stripWS $ dropPrefix "S:" s') in
        (if s `Set.member` n then Just () else Nothing) >>
        mapM (parseClause n t v) (filter (not . null) p') >>= \p ->
        Just (RCG n t v s p)
  where
    stripWS :: String -> String
    stripWS (' ' : s) = stripWS s
    stripWS s = s
    
    dropPrefix :: String -> String -> String
    dropPrefix pre s
      | pre == take (length pre) s = drop (length pre) s
      | otherwise = s

enumerate :: (Num n, Enum n) => [a] -> [(n, a)]
enumerate = zip [0..]

-- Union two maps, but fail if they share keys with distinct values
strictUnion :: (Ord a, Eq b) => Map.Map a b -> Map.Map a b -> Maybe (Map.Map a b)
strictUnion ab1 ab2 = h (Map.toList ab1) ab2
  where
    h :: (Ord a, Eq b) => [(a, b)] -> Map.Map a b -> Maybe (Map.Map a b)
    h [] ab2 = Just ab2
    h ((a, b) : ab1) ab2 =
      maybe (Just (Map.insert a b ab2))
            (\b' -> if b == b' then Just ab2 else Nothing)
            (Map.lookup a ab2)
      >>= h ab1

type Range = (Int, Int)
type Memo = Map.Map (Int, [Range]) Bool
data RCGState = RCGState {clauseMemo :: Memo, prdctMemo :: Memo}

parseString :: RCG -> String -> Bool
parseString g@(RCG n t v s p) str =
  let (b, mem) = runState (prdct (ni s) [(0, length str)]) (RCGState mempty mempty) in
    b
  where
    n' = Set.toList n
    t' = Set.toList t
    v' = Set.toList v

    ni :: Nonterminal -> Int
    ni nt = foldr (\(i, nt') next -> if nt == nt' then i else next) (-1) (enumerate n')
    
    clause :: Int -> [Range] -> State RCGState Bool
    clause i rho =
      clauseMemo <$> get >>= \memo ->
      maybe
        (state (\m -> ((), m {clauseMemo = Map.insert (i, rho) False (clauseMemo m)})) >>
         clauseh (p !! i) rho >>= \b ->
         state (\m -> (b, m {clauseMemo = Map.insert (i, rho) b (clauseMemo m)})))
        return
        (Map.lookup (i, rho) memo)

    prdct :: Int -> [Range] -> State RCGState Bool
--    prdct i rho | trace ("prdct " ++ show i ++ " " ++ show rho) False = undefined
    prdct i rho =
      prdctMemo <$> get >>= \memo ->
      maybe
        (state (\m -> ((), m {prdctMemo = Map.insert (i, rho) False (prdctMemo m)})) >>
         prdcth (n' !! i) rho >>= \b ->
         state (\m -> (b, m {prdctMemo = Map.insert (i, rho) b (prdctMemo m)})))
        return
        (Map.lookup (i, rho) memo)

    -- Returns possible ranges for each variable in the predicate args,
    -- provided that all terminals match those positions in s
    argRanges :: Range -> Arg -> [Map.Map Variable Range]
    argRanges (l, r) (Arg as) = h (l, r) as
      where
        h :: Range -> [Atom] -> [Map.Map Variable Range]
        h (l, r) [] = if l == r then [mempty] else []
        h (l, r) (AtomTrm (Terminal t) : as)
          | l < r && str !! l == t = h (l+1, r) as
          | otherwise = []
        h (l, r) (AtomVar v : as) =
          let rests = [(m, vrs) | m <- [l..r], vrs <- h (m, r) as] in
            [Map.insert v (l, m) vrs | (m, vrs) <- rests,
                                      -- Make sure all occurrences of var have same range
                                      maybe True ((==) (l, m)) (Map.lookup v vrs)]

    argsRanges :: [(Range, Arg)] -> [Map.Map Variable Range]
--    argsRanges ras | trace ("argsRanges " ++ show ras) False = undefined
    argsRanges [] = [mempty]
    argsRanges ((rho, a) : ras) =
      catMaybes [strictUnion vr vr' | vr <- argRanges rho a, vr' <- argsRanges ras]

    allVars :: [Atom] -> [Variable]
    allVars [] = []
    allVars (AtomTrm t : _) = error ("Terminal " ++ show t ++ " appears in a clause! (should be converted away as preprocessing step)")
    allVars (AtomVar v : as) = v : allVars as

    -- Ensures all ranges line up consecutively, returning the whole range they span
    canConcat :: [Range] -> Maybe Range
    canConcat [] = Nothing
    canConcat ((l, r') : rs) =
      foldr (\ (l', r') next prev ->
                if prev == l' then next r' else Nothing) Just rs r' >>= \r ->
      return (l, r)

    -- Performs substitution, and makes sure concatentation is correct, e.g. only (i,j)(j,k)
    argToRanges :: Map.Map Variable Range -> Arg -> Maybe Range
--    argToRanges vr as | trace ("argToRanges " ++ show vr ++ " " ++ show as) False = undefined
    argToRanges vr (Arg []) = error "Epsilon can't appear as an argument on the rhs"
    argToRanges vr (Arg atoms) =
      let vs = allVars atoms
          rs = [maybe (error (show v ++ " not in map " ++ show vr)) id (Map.lookup v vr) | v <- vs]
      in
        canConcat rs
    
    clauseh :: Clause -> [Range] -> State RCGState Bool
--    clauseh c rhos | trace ("clauseh " ++ show c ++ " " ++ show rhos) False = undefined
    clauseh (lhs :->: rhs) rhos =
      any id <$>
      mapM (\vr -> all id <$>
             mapM (\(Predicate n a) ->
                     maybe (return False) id (prdct (ni n) <$> mapM (argToRanges vr) a))
                  rhs)
           (argsRanges (zip rhos (predA lhs)))
    
    prdcth :: Nonterminal -> [Range] -> State RCGState Bool
--    prdcth a rho | trace ("prdcth " ++ show a ++ " " ++ show rho) False = undefined
    prdcth a rho =
      let pas = filter (\(i, lhs :->: rhs) -> predN lhs == a) (enumerate p) in
        any id <$> mapM (\(i, lhs :->: rhs) -> clause i rho) pas


main :: IO ()
main =
  readFile "example.rcg" >>=
  maybe (putStrLn "Parse error") (\g -> getContents >>= foldr (\line next -> putStrLn (show (parseString g line)) >> next) (return ()) . lines) . parseRCG
