{-# LANGUAGE LambdaCase, OverloadedStrings #-}
-- Copyright (c) 2026 Devon Tuma. Apache-2.0.
-- Serialize Cryptol 3.6.0's typechecked AST without erasing proof applications,
-- polymorphic binders, recursive groups, guards, or foreign fallback bodies.
module Main (main) where

import Control.Monad (unless)
import Data.Aeson (Value, object, (.=), toJSON, encode)
import Data.Graph (SCC(..), stronglyConnComp)
import qualified Data.ByteString as BS
import qualified Data.ByteString.Lazy.Char8 as BL
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import qualified Data.Text as Text
import System.Directory (canonicalizePath)
import System.Environment (getArgs)
import System.FilePath (makeRelative, takeFileName, isRelative, splitDirectories)
import System.Exit (die)

import qualified Cryptol.TypeCheck.AST as C
import qualified Cryptol.TypeCheck.Type as T
import qualified Cryptol.ModuleSystem.Name as N
import qualified Cryptol.ModuleSystem.Env as M
import qualified Cryptol.Parser.Selector as S
import qualified Cryptol.Parser.AST as P
import qualified Cryptol.Utils.RecordMap as R
import qualified Cryptol.IR.FreeVars as F
import qualified Cryptol.REPL.Command as Cmd
import qualified Cryptol.REPL.Monad as Repl
import Cryptol.Utils.Ident (Ident, unpackIdent, preludeReferenceName, prelPrim, identText)
import Cryptol.Utils.PP (PP, pp)
import qualified Cryptol.TypeCheck.Solver.InfNat as Num
import qualified Cryptol.TypeCheck.Solver.Class as Class
import qualified Cryptol.TypeCheck.Solver.Types as Solve
import qualified Cryptol.Eval as Eval
import qualified Cryptol.Eval.Type as EvalType
import Cryptol.Utils.Logger (stderrLogger)
import Cryptol.ModuleSystem.Fingerprint (fingerprint, fingerprintHexString)

node :: String -> [Value] -> Value
node tag args = object ["tag" .= tag, "args" .= args]

shown :: Show a => a -> Value
shown = toJSON . show

pretty :: PP a => a -> String
pretty = show . pp

name :: N.Name -> Value
name n = object ["id" .= N.nameUnique n, "text" .= unpackIdent (N.nameIdent n),
                 "origin" .= pretty n]

kind :: T.Kind -> Value
kind = \case
  T.KNum -> node "num" []
  T.KType -> node "type" []
  T.KProp -> node "prop" []
  a T.:-> b -> node "arrow" [kind a, kind b]

parameter :: T.TParam -> Value
parameter p = object ["id" .= T.tpUnique p, "kind" .= kind (T.tpKind p)]

selector :: S.Selector -> Value
selector = \case
  S.TupleSel i shape -> node "tuple" [toJSON i, toJSON shape]
  S.RecordSel f shape -> node "record"
    [toJSON (unpackIdent f), toJSON (map unpackIdent <$> shape)]
  S.ListSel i shape -> node "list" [toJSON i, toJSON shape]

ty :: T.Type -> Value
ty = \case
  T.TVar (T.TVBound p) -> node "var" [parameter p]
  T.TVar (T.TVFree i k _ _) -> node "free" [toJSON i, kind k]
  T.TCon (T.TC (T.TCNum n)) [] -> node "num" [shown n]
  T.TCon (T.TC (T.TCTuple n)) ts -> node "tuple" [toJSON n, toJSON (map ty ts)]
  T.TCon (T.PC (T.PHas sel)) ts -> node "has" [selector sel, toJSON (map ty ts)]
  T.TCon con ts -> node "con" [shown con, toJSON (map ty ts)]
  T.TUser n args body -> node "synonym" [name n, toJSON (map ty args), ty body]
  T.TRec fs -> node "record" [fields ty fs]
  T.TNominal nt args -> node "nominal" [name (T.ntName nt), toJSON (map ty args)]

fields :: (a -> Value) -> R.RecordMap Ident a -> Value
fields f = toJSON . map (\(label, x) -> (unpackIdent label, f x)) . R.canonicalFields

schema :: T.Schema -> Value
schema (T.Forall ps cs body) = object
  ["parameters" .= map parameter ps, "constraints" .= map ty cs, "body" .= ty body]

expr :: C.Expr -> Value
expr = \case
  C.EList es t -> node "list" [ty t, toJSON (map expr es)]
  C.ETuple es -> node "tuple" [toJSON (map expr es)]
  C.ERec fs -> node "record" [fields expr fs]
  C.ESel e s -> node "select" [expr e, selector s]
  C.ESet t e s v -> node "update" [ty t, expr e, selector s, expr v]
  C.EIf c a b -> node "if" [expr c, expr a, expr b]
  C.ECase e arms def -> node "case" [expr e,
    toJSON [(unpackIdent n, alt a) | (n, a) <- Map.toAscList arms], toJSON (alt <$> def)]
  C.EComp n t e bs -> node "comprehension" [ty n, ty t, expr e,
    toJSON (map (map match) bs)]
  C.EVar n -> node "var" [name n]
  C.ETAbs p e -> node "typeAbs" [parameter p, expr e]
  C.ETApp e t -> node "typeApp" [expr e, ty t]
  C.EApp f x -> node "app" [expr f, expr x]
  C.EAbs n t e -> node "abs" [name n, ty t, expr e]
  C.ELocated _ e -> expr e
  C.EProofAbs c e -> node "proofAbs" [ty c, expr e]
  C.EProofApp e -> node "proofApp" [expr e]
  C.EWhere e gs -> node "where" [expr e, toJSON (map group gs)]
  C.EPropGuards gs t -> node "guards" [ty t,
    toJSON [(map ty cs, expr e) | (cs, e) <- gs]]
  where
    alt (C.CaseAlt bs e) = object
      ["bindings" .= [(name n, ty t) | (n,t) <- bs], "body" .= expr e]

match :: C.Match -> Value
match = \case
  C.From n len t e -> node "from" [name n, ty len, ty t, expr e]
  C.Let d -> node "let" [decl d]

decl :: C.Decl -> Value
decl d = object ["name" .= name (C.dName d), "schema" .= schema (C.dSignature d),
                 "definition" .= definition (C.dDefinition d)]
  where
    definition C.DPrim = node "primitive" []
    definition (C.DExpr e) = node "expression" [expr e]
    definition (C.DForeign ffi body) = node "foreign" [shown ffi, toJSON (expr <$> body)]

group :: C.DeclGroup -> Value
group = \case
  C.NonRecursive d -> node "nonrecursive" [decl d]
  C.Recursive ds -> node "recursive" [toJSON (map decl ds)]

-- Retain entire recursive groups whenever any member is reachable.
closure :: Map.Map N.Name N.Name -> [C.DeclGroup] -> [C.Expr] -> Either String [C.DeclGroup]
closure fallbacks groups roots
  | length bindings /= Map.size owners = Left "Duplicate global declaration identity"
  | otherwise = go (F.valDeps (F.freeVars roots))
  where
    bindings = [(C.dName d, g) | g <- groups, d <- C.groupDecls g]
    owners = Map.fromList bindings
    go needed
      | not (Set.null missing) = Left ("Unresolved globals: " ++ show (map pretty (Set.toList missing)))
      | expanded == needed = dependencyOrder selected
      | otherwise = go expanded
      where
        missing = Set.difference needed (Map.keysSet owners)
        selected = filter (any ((`Set.member` needed) . C.dName) . C.groupDecls) groups
        redirects = Set.fromList [target | n <- Set.toList needed,
          Just target <- [Map.lookup n fallbacks]]
        expanded = Set.unions (needed : redirects : [Set.union (F.valDeps (F.freeVars g))
          (Set.fromList (map C.dName (C.groupDecls g))) | g <- selected])

dependencyOrder :: [C.DeclGroup] -> Either String [C.DeclGroup]
dependencyOrder groups = mapM acyclic (stronglyConnComp vertices)
  where
    indexed = zip [0 :: Int ..] groups
    owners = Map.fromList [(C.dName d, i) | (i,g) <- indexed, d <- C.groupDecls g]
    vertices = [(g, i, Set.toList (Set.fromList [j |
      n <- Set.toList (F.valDeps (F.freeVars g)), Just j <- [Map.lookup n owners]])) |
      (i,g) <- indexed]
    acyclic (AcyclicSCC g) = Right g
    acyclic (CyclicSCC _) = Left "Dependency cycle crosses declared recursive groups"

moduleInfo :: FilePath -> FilePath -> M.LoadedModule -> IO Value
moduleInfo base entry lm = do
  (path, bytes) <- case M.lmFilePath lm of
    M.InFile p -> do
      absolute <- canonicalizePath p
      let relative = makeRelative base absolute
          portable = if isRelative relative && not (".." `elem` splitDirectories relative)
                     then relative else
                       (if absolute == entry then "$entry/" else "$cryptol/") ++ takeFileName absolute
      contents <- BS.readFile absolute
      pure (portable, contents)
    M.InMem label bytes -> pure ("$builtin/" ++ label, bytes)
  pure $ object ["name" .= pretty (M.lmName lm), "path" .= path,
    "sha256" .= fingerprintHexString (fingerprint bytes),
    "aliases" .= [(name n, pretty target) | (n,target) <-
      Map.toAscList (C.mModAliases (M.lmModule lm))]]

numericCases :: Value
numericCases = toJSON $
  [entry op [a,b] (f a b) | (op,f) <- binary, a <- sizes, b <- sizes] ++
  [entry op [a] (Just (f a)) | (op,f) <- unary, a <- sizes] ++
  [entry "rangeLength" [a,b,c] (Num.nLenFromThenTo a b c) | a <- sizes, b <- sizes, c <- sizes]
  where
    sizes = map Num.Nat [0,1,2,7,8,17,63,64,65] ++ [Num.Inf]
    lengthValue Num.Inf = toJSON ("inf" :: String)
    lengthValue (Num.Nat n) = toJSON (show n)
    entry op args value = object ["op" .= (op :: String), "arguments" .= map lengthValue args,
                                 "result" .= fmap lengthValue value]
    unary = [("width",Num.nWidth),("lg2",Num.nLg2)]
    binary = [("add",\a b -> Just (Num.nAdd a b)), ("sub",Num.nSub),
      ("mul",\a b -> Just (Num.nMul a b)), ("div",Num.nDiv), ("mod",Num.nMod),
      ("exp",\a b -> Just (Num.nExp a b)), ("min",\a b -> Just (Num.nMin a b)),
      ("max",\a b -> Just (Num.nMax a b)), ("ceilDiv",Num.nCeilDiv), ("ceilMod",Num.nCeilMod)]

-- Resolve structural obligations with the official class solver, then evaluate
-- its closed numeric side conditions with the official numeric evaluator.
classHolds :: T.Prop -> Bool
classHolds p = case p of
  T.TCon (T.PC pc) [a] | Just solve <- lookup pc classes -> solved (solve a)
  T.TCon (T.PC T.PLiteral) [n,a] -> solved (Class.solveLiteralInst n a)
  T.TCon (T.PC T.PLiteralLessThan) [n,a] -> solved (Class.solveLiteralLessThanInst n a)
  T.TCon (T.PC T.PAnd) ps -> all classHolds ps
  T.TCon con args -> Eval.checkProp
    (T.TCon con (map (EvalType.tNumTy . EvalType.evalNumType mempty) args))
  _ -> error ("Unsupported closed obligation: " ++ pretty p)
  where
    solved (Solve.SolvedIf ps) = all classHolds ps
    solved Solve.Unsolvable = False
    solved Solve.Unsolved = error ("Unresolved closed obligation: " ++ pretty p)
    classes = [(T.PZero,Class.solveZeroInst), (T.PLogic,Class.solveLogicInst),
      (T.PRing,Class.solveRingInst), (T.PIntegral,Class.solveIntegralInst),
      (T.PEq,Class.solveEqInst), (T.PCmp,Class.solveCmpInst),
      (T.PSignedCmp,Class.solveSignedCmpInst)]

classCases :: Value
classCases = toJSON [object ["constraint" .= ty p, "result" .= classHolds p] | p <- cases]
  where
    sizes = map (T.tNum :: Integer -> T.Type) [0,1,2,7,8,255,256] ++ [T.tInf]
    scalars = [T.tBit, T.tInteger]
    sequences = [T.tSeq n a | n <- [T.tNum (0 :: Integer), T.tNum (8 :: Integer), T.tInf],
                 a <- scalars]
    types = scalars ++ sequences ++ [T.tTuple [], T.tTuple [T.tBit,T.tInteger],
      T.tTuple [T.tSeq (T.tNum (8 :: Integer)) T.tBit, T.tInteger],
      T.tRec (R.recordFromFields [("flag",T.tBit),("word",T.tSeq (T.tNum (8 :: Integer)) T.tBit)]),
      T.tFun T.tInteger T.tBit, T.tFun T.tBit T.tInteger,
      T.tSeq (T.tNum (2 :: Integer)) (T.tSeq (T.tNum (0 :: Integer)) T.tBit)]
    classes = [T.PZero,T.PLogic,T.PRing,T.PIntegral,T.PEq,T.PCmp,T.PSignedCmp]
    cases = [T.TCon (T.PC pc) [a] | pc <- classes, a <- types] ++
      [T.TCon (T.PC pc) [n,a] | pc <- [T.PLiteral,T.PLiteralLessThan], n <- sizes, a <- types]

main :: IO ()
main = do
  args <- getArgs
  case args of
    ["--numeric"] -> BL.putStrLn (encode numericCases)
    ["--classes"] -> BL.putStrLn (encode classCases)
    foundation : file : roots@(_ : _) -> do
      base <- canonicalizePath foundation
      entry <- canonicalizePath file
      bundle <- Repl.runREPL True False stderrLogger $ do
        Repl.prependSearchPath [base]
        loaded <- Cmd.loadCmd file
        unless (Cmd.crSuccess loaded) (Repl.io (die "Cryptol module loading failed"))
        checked <- mapM (\text -> do
          parsed <- Cmd.replParseExpr text (1,1) Nothing
          (_, e, s) <- Cmd.replCheckExpr (P.noPos parsed)
          pure (text, e, s)) roots
        env <- Repl.getModuleEnv
        let modules = M.loadedModules env
            allGroups = concatMap C.mDecls modules
            referenceNames = [C.dName d | m <- modules, C.mName m == preludeReferenceName,
              g <- C.mDecls m, d <- C.groupDecls g]
            fallbacks = Map.fromList [(C.dName d, n) | g <- allGroups, d <- C.groupDecls g,
              C.DPrim <- [C.dDefinition d], n <- referenceNames,
              N.asPrim (C.dName d) == Just (prelPrim (identText (N.nameIdent n)))]
        groups <- either (Repl.io . die) pure
          (closure fallbacks allGroups [e | (_,e,_) <- checked])
        let retained = Set.fromList [C.dName d | g <- groups, d <- C.groupDecls g]
        provenance <- Repl.io $ mapM (moduleInfo base entry)
          (M.getLoadedModules (M.meLoadedModules env))
        pure $ object ["format" .= ("cryptol-typed-ast" :: Text.Text), "version" .= (1 :: Int),
          "cryptol_revision" .= ("61dd17b0c45ddf8c5c1e952afd5e789c4dc4ec4b" :: Text.Text),
          "roots" .= [object ["text" .= t, "expression" .= expr e, "schema" .= schema s]
                       | (t,e,s) <- checked],
          "groups" .= map group groups, "modules" .= provenance,
          "primitive_fallbacks" .= [(name n, name target) | (n,target) <- Map.toAscList fallbacks,
            Set.member n retained]]
      BL.putStrLn (encode bundle)
    _ -> die "Usage: cryptol-lean-export FOUNDATION MODULE ROOT [ROOT ...]"
