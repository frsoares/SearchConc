{-# LANGUAGE CPP, TemplateHaskell, ScopedTypeVariables, RankNTypes, DoAndIfThenElse #-}
-----------------------------------------------------------------------------
--
-- Module      :  Main
-- Copyright   :
-- License     :  GPL2
--
-- Maintainer  :  Francisco Soares
-- Stability   :  unstable
-- Portability :
--
-- |
--
-----------------------------------------------------------------------------

module Main (
    main
) where

import GHC
import GHC.Paths ( libdir )
import DynFlags
import Outputable

import MonadUtils
import Control.Monad (unless)

import Data.Data
import Data.Maybe (isJust, fromJust)
import Data.List (stripPrefix, isPrefixOf)
import System.Exit (exitFailure)

import qualified Data.Generics.Schemes as SYB
import qualified Data.Generics.Aliases as SYB
import qualified GHC.SYB.Utils         as SYB
import NameSet

powerPutStrLn :: MonadIO m => String -> m ()
powerPutStrLn = liftIO . putStrLn

targetFile0 = "main.hs" -- TODO: make the filename customizable.

main = do
    runningGhc example


runningGhc annotatedAST = do
    defaultErrorHandler defaultLogAction $ do
        runGhc (Just libdir) annotatedAST

example :: Ghc (ParsedSource, String, TypecheckedSource)
example = do
    dflags <- getSessionDynFlags
    let dflags' = foldl xopt_set dflags
                        [Opt_Cpp, Opt_ImplicitPrelude, Opt_MagicHash, Opt_BangPatterns]
    setSessionDynFlags dflags'
    target0 <- guessTarget targetFile0 Nothing
    setTargets [target0]
    load LoadAllTargets
    moduleName <- return $ "Main" -- TODO: make the module's name customizable.
    modSum <- getModSummary $ mkModuleName moduleName


    p <- parseModule modSum

    t <- typecheckModule p

    d <- desugarModule t

    l <- loadModule t

    n <- getNamesInScope

    c <- return $ coreModule d

    g <- getModuleGraph
    mapM doAllTheStuff g
    moduleInfoStrings <- mapM showModule g
    mapM powerPutStrLn moduleInfoStrings

    return $ (parsedSource d,"\n--\n",  typecheckedSource d)


doAllTheStuff modSum = do
    powerPutStrLn $ "Analyzing module \""++((moduleNameString . ms_mod_name) modSum)++"\".\n"

    p <- parseModule modSum
    t <- typecheckModule p
    d <- desugarModule t
    typeCheckedSource  <- return $ tm_typechecked_source t

    maybeRenamedSource <- return $ tm_renamed_source t

    if isJust maybeRenamedSource then do
        renamedSource  <- return $ fromJust maybeRenamedSource
        matches <- readMod' renamedSource
        mapM (powerPutStrLn.showPpr) matches
        
--        readMod renamedSource
        return ()
    else do return ()

    powerPutStrLn ""

    return $ coreModule d

readMod' :: Monad m => GHC.RenamedSource -> m [GHC.HsExpr GHC.Name]
readMod' renamed = return $ listifyStaged' SYB.Renamer isDesiredVar renamed-- SYB.listify applyIsDesired renamed

applyIsDesired :: Typeable r => r -> Bool
applyIsDesired = (const False `SYB.extQ` postTcType `SYB.extQ` fixity `SYB.extQ` nameSet) `SYB.extQ`  isDesiredVar
    where
      nameSet    = const False :: NameSet    -> Bool
      postTcType = const True  :: PostTcType -> Bool
      fixity     = const False :: GHC.Fixity -> Bool


readMod renamed =
    everywhereMStaged SYB.Renamer (SYB.mkM inMod) renamed

-- SYB.extQ extends a generic query by a type-specific case.
--


teste stage x = (const False `SYB.extQ` postTcType `SYB.extQ` fixity `SYB.extQ` nameSet) x
  where nameSet    = const (stage `elem` [SYB.Parser,SYB.TypeChecker]) :: NameSet    -> Bool
        postTcType = const (stage<SYB.TypeChecker)                     :: PostTcType -> Bool
        fixity     = const (stage<SYB.Renamer)                         :: GHC.Fixity -> Bool


-- | Applies a transformation to a specified AST, taking into account the 
-- stage of processing it's at.
-- The stage must be provided to avoid trying to modify elements which
-- may not be present at all stages of AST processing.
everywhereMStaged :: Monad m => SYB.Stage  -- ^ The current stage of processing
                             -> SYB.GenericM m -- ^ Transformation to be applied
                             -> SYB.GenericM m -- ^ Transformed AST
everywhereMStaged stage f x
  | teste stage x = return x 
  | otherwise = do x' <- gmapM (everywhereMStaged stage f) x
                   f x'

everywhereStaged ::
                   SYB.Stage
                -> SYB.GenericT
                -> SYB.GenericT
everywhereStaged stage f x
  | teste stage x = x
  | otherwise = let mapped = gmapT (everywhereStaged stage f) x
                in f mapped

everythingStaged :: SYB.Stage -> (r -> r -> r) -> r -> SYB.GenericQ r -> SYB.GenericQ r
everythingStaged stage k z f x
  | teste stage x = z
  | otherwise = foldl k (f x) (gmapQ (everythingStaged stage k z f) x)


-- listify :: Typeable r => (r -> Bool) -> GenericQ [r]
-- listify p = everything (++) ([] `mkQ` (\x -> if p x then [x] else []))

listifyStaged' stage p = everythingStaged stage (++) [] ([] `SYB.mkQ` (\x -> if p x then [x] else []))

listifyStaged :: (Data a, Typeable r) 
                          => SYB.Stage
                          -> (r -> Bool)
                          -> a 
                          -> [r]
listifyStaged stage f x
  | teste stage x = []
  | otherwise = (SYB.listify applyIsDesired x) ++ rest
                -- rest
              where 
                rest = concat $ gmapQ (listifyStaged stage f) x
 


isDesiredVar :: GHC.HsExpr GHC.Name -> Bool 
isDesiredVar (varNv@(GHC.HsVar nv)::(GHC.HsExpr GHC.Name)) =
       if matchesAnyPrefix ["GHC.MVar.", "Control.Concurrent.", "GHC.Conc.Sync"] $ nameToString nv then True
       else False
isDesiredVar _ = False

inMod (varNv@(GHC.HsVar nv)::(GHC.HsExpr GHC.Name))
       | matchesAnyPrefix ["GHC.MVar.", "Control.Concurrent.", "GHC.Conc.Sync"] $ nameToString nv
        = do
            powerPutStrLn $ nameToString nv

            return varNv

inMod func = return func

nameToString = showPpr

matchesAnyPrefix :: [String] -> String -> Bool
matchesAnyPrefix prefixes text = or [ isPrefixOf x text | x <- prefixes ]

