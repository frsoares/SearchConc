{-# LANGUAGE CPP, ScopedTypeVariables, RankNTypes, DoAndIfThenElse #-}
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
import Control.Monad (unless, when)

import Data.Data
import Data.Maybe (isJust, fromJust)
import Data.List (isPrefixOf)
import System.Exit (exitFailure)

import qualified Data.Generics.Schemes as SYB
import qualified Data.Generics.Aliases as SYB
import qualified GHC.SYB.Utils         as SYB
import NameSet

powerPutStrLn :: MonadIO m => String -> m ()
powerPutStrLn = liftIO . putStrLn

targetFile0 = "main.hs" -- TODO: make the filename customizable.

main = runningGhc example


runningGhc annotatedAST = 
    defaultErrorHandler defaultLogAction $ 
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
    let moduleName = "Main" -- TODO: make the module's name customizable.
    modSum <- getModSummary $ mkModuleName moduleName


    p <- parseModule modSum

    t <- typecheckModule p

    d <- desugarModule t

    l <- loadModule t

    n <- getNamesInScope

    let c = coreModule d

    g <- getModuleGraph
    mapM_ doAllTheStuff g
    moduleInfoStrings <- mapM showModule g
    mapM_ powerPutStrLn moduleInfoStrings

    return (parsedSource d,"\n--\n",  typecheckedSource d)


doAllTheStuff modSum = do
    powerPutStrLn $ "Analyzing module \""++(moduleNameString . ms_mod_name) modSum++"\".\n"

    p <- parseModule modSum
    t <- typecheckModule p
    d <- desugarModule t
    let typeCheckedSource = tm_typechecked_source t
    let maybeRenamedSource = tm_renamed_source t

    when (isJust maybeRenamedSource) $ do
        let renamedSource = fromJust maybeRenamedSource
        matches <- readMod' renamedSource
        mapM_ (powerPutStrLn.showPpr) matches
        
--        readMod renamedSource
        return ()
    

    powerPutStrLn ""

    return $ coreModule d

-- | Core parsing function, using the listify approach.
readMod' :: Monad m => GHC.RenamedSource -> m [GHC.HsExpr GHC.Name]
readMod' renamed = return $ listifyStaged SYB.Renamer isDesiredVar renamed


-- | Core parsing function, using the putStrLn approach.
readMod renamed =
    everywhereMStaged SYB.Renamer (SYB.mkM inMod) renamed

-- --------
-- Reminder: SYB.extQ extends a generic query by a type-specific case.
-- --------

-- | Checks whether the current item is undesirable for analysis in the current
-- AST Stage.
checkItemStage stage x = (const False `SYB.extQ` postTcType `SYB.extQ` fixity `SYB.extQ` nameSet) x
  where nameSet    = const (stage `elem` [SYB.Parser,SYB.TypeChecker]) :: NameSet    -> Bool
        postTcType = const (stage<SYB.TypeChecker)                     :: PostTcType -> Bool
        fixity     = const (stage<SYB.Renamer)                         :: GHC.Fixity -> Bool

-- | Variant of SYB.everywhere in which a Stage is supplied.
-- The stage must be provided to avoid trying to modify elements which
-- may not be present at all stages of AST processing.
everywhereStaged ::
                   SYB.Stage    -- ^ The current stage of processing
                -> SYB.GenericT -- ^ Transformation to be applied
                -> SYB.GenericT -- ^ Transformed AST (both argument and result)
everywhereStaged stage f x
  | checkItemStage stage x = x
  | otherwise = let mapped = gmapT (everywhereStaged stage f) x
                in f mapped

-- | Monadic variation of everywhereStaged
everywhereMStaged :: Monad m => SYB.Stage  -- ^ The current stage of processing
                         -> SYB.GenericM m -- ^ Transformation to be applied
                         -> SYB.GenericM m -- ^ Transformed AST (both argument and result)
everywhereMStaged stage f x
  | checkItemStage stage x = return x 
  | otherwise = do x' <- gmapM (everywhereMStaged stage f) x
                   f x'

-- | Staged variation of SYB.everything
-- The stage must be provided to avoid trying to modify elements which
-- may not be present at all stages of AST processing.
everythingStaged :: SYB.Stage -> (r -> r -> r) -> r -> SYB.GenericQ r -> SYB.GenericQ r
everythingStaged stage k z f x
  | checkItemStage stage x = z
  | otherwise = foldl k (f x) (gmapQ (everythingStaged stage k z f) x)


-- listify :: Typeable r => (r -> Bool) -> GenericQ [r]
-- listify p = everything (++) ([] `mkQ` (\x -> if p x then [x] else []))

-- | Staged variation of SYB.listify
-- The stage must be provided to avoid trying to modify elements which
-- may not be present at all stages of AST processing.
listifyStaged stage p = everythingStaged stage (++) [] ([] `SYB.mkQ` (\x -> [ x | p x ]))


-- | Checks whether the argument is an GHC.HsExpr in the form of a GHC.HsVar. 
-- If true, it tries to match the beginning of its name to one of the default 
-- concurrency modules.
isDesiredVar :: GHC.HsExpr GHC.Name -> Bool 
isDesiredVar (varNv@(GHC.HsVar nv)::(GHC.HsExpr GHC.Name)) =
        matchesAnyPrefix ["GHC.MVar.", "Control.Concurrent.", "GHC.Conc.Sync"] $ nameToString nv
isDesiredVar _ = False

inMod (varNv@(GHC.HsVar nv)::(GHC.HsExpr GHC.Name))
       | matchesAnyPrefix ["GHC.MVar.", "Control.Concurrent.", "GHC.Conc.Sync"] $ nameToString nv
        = do
            powerPutStrLn $ nameToString nv

            return varNv

inMod x = return x

nameToString = showPpr

matchesAnyPrefix :: [String] -> String -> Bool
matchesAnyPrefix prefixes text = or [ x `isPrefixOf` text | x <- prefixes ]

