{-# LANGUAGE StandaloneDeriving, DeriveDataTypeable, ScopedTypeVariables, FlexibleInstances #-}
module Benchmark where

import qualified Main
import System.IO.Strict as S
import System.Environment
import Criterion.Config
import Criterion.Main
import Control.Monad
import Control.Monad.Trans.Error ( ErrorT(..) )
import Control.Monad.Trans.State.Strict ( execStateT )

import Data.Generics

import Idris.REPL
import Idris.Parser
import Idris.AbsSyntaxTree
import Idris.Core.TT
import Idris.CmdOptions

import Text.Trifecta hiding (whiteSpace)
--import Text.Parsec
--import Text.Parsec.Indentation
--import Text.Parsec.Indentation.Char

data Mode = Check | Benchmark | Profile

config = defaultConfig
main = do
  cmdArgs <- getArgs

  let mode = head cmdArgs

  let (c_args, _ : args) = break ("--"==) (tail cmdArgs)
      (i_args, _ : files) = break ("--"==) args

  state <- withArgs (["--check"] ++ i_args ++ files) main'

  strings <- sequence [S.readFile f >>= \s -> return (f, s) | f <- files]

  case mode of
    "--check" ->
      forM_ strings $ \(file, str) -> do
        let p = loadSource'' state file str
        case p of
          Failure err -> print err
          Success p'@(_, _, ns) -> do
            putStrLn $ "check: " ++ file
            putStrLn $ showParse p
            putStrLn $ "number of nodes: " ++ show (countNodes ns)
    "--benchmark" ->
      withArgs c_args $ defaultMainWith config (return ())
        [bench ("parse/"++file) $ whnf (loadSource'' state file) str | (file, str) <- strings]
    "--profile" ->
      foldl1 seq
         [loadSource'' state file str | (file, str) <- concat (replicate (read (head c_args)) strings)]
         `seq` return ()
    "--countnodes" ->
      forM_ strings $ \(file, str) -> do
        let p = loadSource'' state file str
        case p of
          Failure err -> putStrLn $ file ++ " failed to parse"
          Success p' -> putStrLn $ file ++ " " ++ show (gsize (scrubString p'))


countNodes :: Data d => d -> Int
countNodes = gmapQl (+) 1 countNodes

showParse :: Result ([String], [(String, Maybe String, FC)], [[PDecl]]) -> String
showParse p@(Failure _) = "X:"++show p
showParse (Success x) = show (gsize x) ++ ":" ++ show (gsize (scrubFC x)) ++ ":" ++ show (gsize (scrubString x)) ++ ": Right "++show x

scrubFC = everywhere (mkT (\(FC _ _ _) -> FC "" (0,0) (0,0)))
scrubString = everywhere (mkT (\_ -> ""))

deriving instance Data (PClause' PTerm)
deriving instance Data (DSL' PTerm)
deriving instance Data (PData' PTerm)
deriving instance Data (PTactic' PTerm)
deriving instance Data (PDo' PTerm)
deriving instance Data (PArg' PTerm)
deriving instance Data UExp
deriving instance Data Const
deriving instance Data (TT Name)
deriving instance Data PTerm
deriving instance Data FC
deriving instance Data Name
deriving instance Data Idris.Core.TT.Err
deriving instance Data Plicity
deriving instance Data NameType
deriving instance Data Static
deriving instance Data Raw
deriving instance Data Syntax
deriving instance Data SSymbol
deriving instance Data SynContext
deriving instance Data SyntaxInfo
deriving instance Data FnOpt
deriving instance Data Using
deriving instance Data Idris.AbsSyntaxTree.Fixity

deriving instance Data SpecialName
deriving instance Data ArithTy
deriving instance Data IntTy
deriving instance Data NativeTy
deriving instance Data DataOpt
deriving instance Data Universe
deriving instance Data ErrorReportPart
deriving instance Data ArgOpt
deriving instance Data PunInfo
deriving instance Data ProvideWhat

--deriving instance Data (Binder (TT Name))
--deriving instance Data (Binder Raw)

deriving instance Typeable Idris.AbsSyntaxTree.Fixity
deriving instance Typeable1 PClause'
deriving instance Typeable1 PArg'
deriving instance Typeable1 PData'
deriving instance Typeable1 PDecl'
deriving instance Typeable1 Binder
deriving instance Typeable PTerm
deriving instance Typeable FnOpt
deriving instance Typeable Const
deriving instance Typeable UExp
deriving instance Typeable Err'
deriving instance Typeable1 PTactic'
deriving instance Typeable1 TT
deriving instance Typeable1 PDo'
deriving instance Typeable Name
deriving instance Typeable NameType
deriving instance Typeable Plicity
deriving instance Typeable FC
deriving instance Typeable Static
deriving instance Typeable Raw
deriving instance Typeable SSymbol
deriving instance Typeable Syntax
deriving instance Typeable SynContext
deriving instance Typeable1 DSL'
deriving instance Typeable Using
deriving instance Typeable SyntaxInfo
deriving instance Typeable ErrorReportPart
deriving instance Typeable ArgOpt


deriving instance Typeable SpecialName
deriving instance Typeable ArithTy
deriving instance Typeable IntTy
deriving instance Typeable NativeTy
deriving instance Typeable DataOpt
deriving instance Typeable ProvideWhat'
deriving instance Typeable Universe
deriving instance Typeable PunInfo

idrisConstr :: Constr
idrisConstr   = mkConstr idrisDataType "<Idris ()>"  [] Data.Generics.Prefix

idrisDataType :: DataType
idrisDataType = mkDataType "<Idris ()>" [idrisConstr]

binderLamConstr = mkConstr binderDataType "Lam" [] Data.Generics.Prefix
binderPiConstr = mkConstr binderDataType "Pi" [] Data.Generics.Prefix
binderLetConstr = mkConstr binderDataType "Let" [] Data.Generics.Prefix
binderNLetConstr = mkConstr binderDataType "NLet" [] Data.Generics.Prefix
binderHoleConstr = mkConstr binderDataType "Hole" [] Data.Generics.Prefix
binderGHoleConstr = mkConstr binderDataType "GHole" [] Data.Generics.Prefix
binderGuessConstr = mkConstr binderDataType "Guess" [] Data.Generics.Prefix
binderPVarConstr = mkConstr binderDataType "PVar" [] Data.Generics.Prefix
binderPVTyConstr = mkConstr binderDataType "PVTy" [] Data.Generics.Prefix

binderDataType :: DataType
binderDataType = mkDataType "Binder" [binderLamConstr, binderPiConstr, binderLetConstr, binderNLetConstr, binderHoleConstr, binderGHoleConstr, binderGuessConstr, binderPVarConstr, binderPVTyConstr]

instance (Data b) => Data (Binder b) where
  gfoldl k z (Lam x) = z Lam `k` x
  gfoldl k z (Pi x y) = z Pi `k` x `k` y
  gfoldl k z (Let x y) = z Let `k` x `k` y
  gfoldl k z (NLet x y) = z NLet `k` x `k` y
  gfoldl k z (Hole x) = z Hole `k` x
  gfoldl k z (GHole x y) = z GHole `k` x `k` y
  gfoldl k z (Guess x y) = z Guess `k` x `k` y
  gfoldl k z (PVar x) = z PVar `k` x
  gfoldl k z (PVTy x) = z PVTy `k` x

  toConstr Lam{} = binderLamConstr
  toConstr Pi{} = binderPiConstr
  toConstr Let{} = binderLetConstr
  toConstr NLet{} = binderNLetConstr
  toConstr Hole{} = binderHoleConstr
  toConstr GHole{} = binderGHoleConstr
  toConstr Guess{} = binderGuessConstr
  toConstr PVar{} = binderPVarConstr
  toConstr PVTy{} = binderPVTyConstr

  dataTypeOf _ = binderDataType

pdeclPFixConstr = mkConstr pdeclDataType "PFix" [] Data.Generics.Prefix
pdeclPTyConstr = mkConstr pdeclDataType "PTy" [] Data.Generics.Prefix
pdeclPPostulateConstr = mkConstr pdeclDataType "PPostulate" [] Data.Generics.Prefix
pdeclPClausesConstr = mkConstr pdeclDataType "PClauses" [] Data.Generics.Prefix
pdeclPCAFConstr = mkConstr pdeclDataType "PCAF" [] Data.Generics.Prefix
pdeclPDataConstr = mkConstr pdeclDataType "PData" [] Data.Generics.Prefix
pdeclPParamsConstr = mkConstr pdeclDataType "PParams" [] Data.Generics.Prefix
pdeclPNamespaceConstr = mkConstr pdeclDataType "PNamespace" [] Data.Generics.Prefix
pdeclPRecordConstr = mkConstr pdeclDataType "PRecord" [] Data.Generics.Prefix
pdeclPClassConstr = mkConstr pdeclDataType "PClass" [] Data.Generics.Prefix
pdeclPInstanceConstr = mkConstr pdeclDataType "PInstance" [] Data.Generics.Prefix
pdeclPDSLConstr = mkConstr pdeclDataType "PDSL" [] Data.Generics.Prefix
pdeclPSyntaxConstr = mkConstr pdeclDataType "PSyntax" [] Data.Generics.Prefix
pdeclPMutualConstr = mkConstr pdeclDataType "PMutual" [] Data.Generics.Prefix
pdeclPProviderConstr = mkConstr pdeclDataType "PProvider" [] Data.Generics.Prefix
pdeclPDirectiveConstr = mkConstr pdeclDataType "PDirective" [] Data.Generics.Prefix

pdeclDataType :: DataType
pdeclDataType = mkDataType "PDecl'" [pdeclPFixConstr,
                                     pdeclPTyConstr,
                                     pdeclPPostulateConstr,
                                     pdeclPClausesConstr,
                                     pdeclPCAFConstr,
                                     pdeclPDataConstr,
                                     pdeclPParamsConstr,
                                     pdeclPNamespaceConstr,
                                     pdeclPRecordConstr,
                                     pdeclPClassConstr,
                                     pdeclPInstanceConstr,
                                     pdeclPDSLConstr,
                                     pdeclPSyntaxConstr,
                                     pdeclPMutualConstr,
                                     pdeclPProviderConstr,
                                     pdeclPDirectiveConstr]

instance Data (PDecl' PTerm) where
  gfoldl k z (PFix a b c) = z PFix `k` a `k` b `k` c
  gfoldl k z (PTy a b c d e f g) = z PTy `k` a `k` b `k` c `k` d `k` e `k` f `k` g
  gfoldl k z (PPostulate a b c d e f) = z PPostulate `k` a `k` b `k` c `k` d `k` e `k` f
  gfoldl k z (PClauses a b c d) = z PClauses `k` a `k` b `k` c `k` d
  gfoldl k z (PCAF a b c) = z PCAF `k` a `k` b `k` c
  gfoldl k z (PData a b c d e f) = z PData `k` a `k` b `k` c `k` d `k` e `k` f
  gfoldl k z (PParams a b c) = z PParams `k` a `k` b `k` c
  gfoldl k z (PNamespace a b) = z PNamespace `k` a `k` b
  gfoldl k z (PRecord a b c d e f g h i) = z PRecord `k` a `k` b `k` c `k` d `k` e `k` f `k` g `k` h `k` i
  gfoldl k z (PClass a b c d e f g h) = z PClass `k` a `k` b `k` c `k` d `k` e `k` f `k` g `k` h
  gfoldl k z (PInstance a b c d e f g h) = z PInstance `k` a `k` b `k` c `k` d `k` e `k` f `k` g `k` h
  gfoldl k z (PDSL a b) = z PDSL `k` a `k` b
  gfoldl k z (PSyntax a b) = z PSyntax `k` a `k` b
  gfoldl k z (PMutual a b) = z PMutual `k` a `k` b
  gfoldl k z (PProvider a b c d) = z PProvider `k` a `k` b `k` c `k` d

  gfoldl k z (PDirective a) = z (PDirective a) -- Hack around the Idris monad

  toConstr PFix{} = pdeclPFixConstr
  toConstr PTy{} = pdeclPTyConstr
  toConstr PPostulate{} = pdeclPPostulateConstr
  toConstr PClauses{} = pdeclPClausesConstr
  toConstr PCAF{} = pdeclPCAFConstr
  toConstr PData{} = pdeclPDataConstr
  toConstr PParams{} = pdeclPParamsConstr
  toConstr PNamespace{} = pdeclPNamespaceConstr
  toConstr PRecord{} = pdeclPRecordConstr
  toConstr PClass{} = pdeclPClassConstr
  toConstr PInstance{} = pdeclPInstanceConstr
  toConstr PDSL{} = pdeclPDSLConstr
  toConstr PSyntax{} = pdeclPSyntaxConstr
  toConstr PMutual{} = pdeclPMutualConstr
  toConstr PProvider{} = pdeclPProviderConstr
  toConstr PDirective{} = pdeclPDirectiveConstr

  dataTypeOf _ = pdeclDataType

loadSource'' :: IState -> FilePath -> String -> Result ([String], [(String, Maybe String, FC)], [[PDecl]])
loadSource'' i fname input =
    runparser (do whiteSpace
                  mname <- moduleHeader
                  imps <- many import_
                  decls <- many (decl (defaultSyntax {syn_namespace = reverse mname }))
                  eof
                  return (mname, imps, decls))
      i fname input

main' = do xs <- getArgs
           let opts = pureArgParser xs
           --execStateT (Main.runIdris opts) idrisInit
           result <- runErrorT $ execStateT (Main.runIdris opts) idrisInit
           case result of
             Left err -> (putStrLn $ "Uncaught error: " ++ show err) >> undefined
             Right x -> return x

{-
          case result of
            Left err -> putStrLn $ "Uncaught error: " ++ show err
            Right _ -> return ()
-}