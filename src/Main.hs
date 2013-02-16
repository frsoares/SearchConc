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

targetFile0 = "main.hs"

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
        readMod renamedSource
        return ()
    else do return ()

    powerPutStrLn ""

    return $ coreModule d

readMod renamed =
    everywhereMStaged SYB.Renamer (SYB.mkM inMod) renamed

everywhereMStaged :: Monad m => SYB.Stage -> SYB.GenericM m -> SYB.GenericM m
everywhereMStaged stage f x
  | (const False `SYB.extQ` postTcType `SYB.extQ` fixity `SYB.extQ` nameSet) x = return x
  | otherwise = do x' <- gmapM (everywhereMStaged stage f) x
                   f x'
  where nameSet    = const (stage `elem` [SYB.Parser,SYB.TypeChecker]) :: NameSet -> Bool
        postTcType = const (stage<SYB.TypeChecker)                 :: PostTcType -> Bool
        fixity     = const (stage<SYB.Renamer)                     :: GHC.Fixity -> Bool

inMod (varNv@(GHC.HsVar nv)::(GHC.HsExpr GHC.Name))
       | matchesAnyPrefix ["GHC.MVar.", "Control.Concurrent.", "GHC.Conc.Sync"] $ nameToString nv
        = do
            powerPutStrLn $ nameToString nv

            return varNv

inMod func = return func

nameToString = showPpr

matchesAnyPrefix :: [String] -> String -> Bool
matchesAnyPrefix prefixes text = or [ isPrefixOf x text | x <- prefixes ]

