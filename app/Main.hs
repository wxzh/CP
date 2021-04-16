{-# LANGUAGE OverloadedStrings #-}


module Main where

import           Control.Exception (SomeException, try)
import           Control.Monad.State.Strict
import           Data.List (isPrefixOf)
import           Data.Maybe (fromMaybe)
import qualified Data.Text.IO as TIO
import           System.IO                    (hPutStrLn, stderr)
import           Data.Text.Prettyprint.Doc ((<+>), (<>))
import qualified Data.Text.Prettyprint.Doc as Pretty
import qualified Data.Text.Prettyprint.Doc.Render.Text as Pretty
import           System.Console.GetOpt
import           System.Console.Repline
import           System.Environment (getArgs)
import           System.Exit

import           CP
import           CP.Environment
import           CP.Parser.Parser
import           CP.Source.Desugar
import           CP.Source.Syntax
import           CP.PrettyPrint


data ReplState = ReplState
  { replCtx :: Ctx
  , verbose :: Bool
  }

initState :: ReplState
initState = ReplState {replCtx = emptyCtx, verbose = False}

type Repl a = HaskelineT (StateT ReplState IO) a


getCtx :: Repl ReplState
getCtx = lift get

putCtx :: ReplState -> Repl ()
putCtx = lift . put

readTry :: IO String -> Repl (Either SomeException String)
readTry = liftIO . try

putMsg :: String -> Repl ()
putMsg = liftIO . putStrLn


prettyOpts :: Pretty.LayoutOptions
prettyOpts =
    Pretty.defaultLayoutOptions
    { Pretty.layoutPageWidth = Pretty.AvailablePerLine 80 1.0 }

ppMsg :: FDoc -> Repl ()
ppMsg d =
  liftIO . TIO.putStrLn $ Pretty.renderStrict (Pretty.layoutSmart prettyOpts d)

-- Execution
exec :: String -> Repl ()
exec source =
  case parseModule source of
    Left err -> ppMsg $ "Syntax error" <+> Pretty.pretty err
    Right abt -> do
      ctx <- getCtx
      res <- liftIO $ driver (replCtx ctx) abt
      case res of
        Right r -> ppMsg (render r)
        Left err -> do
          when (verbose ctx) $ do
            putMsg "AST after desugaring:"
            ppMsg $ "=>" <+> Pretty.pretty (show (desugar (moduleEntries abt))) <> Pretty.line
          ppMsg err


-- :load command
load :: [String] -> Repl ()
load args = do
  contents <- readTry $ readFile (unwords args)
  case contents of
    Left err -> ppMsg $ "Load file error" <+> Pretty.pretty (show err)
    Right s -> exec s

-- :quit command
quit :: a -> Repl ()
quit _ = liftIO exitSuccess


resetCtx :: Repl ()
resetCtx = do
  _ <- getCtx
  putCtx ReplState {replCtx = emptyCtx, verbose = False}

reset :: [String] -> Repl ()
reset _ = do
  resetCtx
  putMsg "Context cleaned"

debug :: [String] -> Repl ()
debug _ = do
  st <- getCtx
  putCtx ReplState {replCtx = replCtx st, verbose = True}
  putMsg "Enter debug mode"


-- Prefix tab completer
defaultMatcher :: MonadIO m => [(String, CompletionFunc m)]
defaultMatcher = [(":load"  , fileCompleter)]

-- Default tab completer
comp :: Monad m => WordCompleter m
comp n = do
  let cmds = [":load", ":quit", ":reset", ":debug"]
  return $ filter (isPrefixOf n) cmds


optionsWithHelp :: [(String, [String] -> Repl (), String)]
optionsWithHelp =
  [ ("help", help, "Show this text")
  , ("?", help, "Show help")
  , ("quit", quit, "Quit interactive")
  , ("load", load, "Load file and evaluate")
  , ("reset", reset, "Reset configuration")
  , ("debug", debug, "Toggle debugging")
  ]

help :: [String] -> Repl ()
help _ = putMsg . unlines $
  "Usage:" : helpText

helpText :: [String]
helpText =
  map
    (\(c, _, h) -> " :" ++ c ++ replicate (10 - length c) ' ' ++ h)
    optionsWithHelp

options :: [(String, [String] -> Repl ())]
options = map (\(a, b, _) -> (a, b)) optionsWithHelp
  -- [("load", load), ("reset", reset), ("quit", quit), ("debug", debug)]

shell :: Repl a -> IO ()
shell pre =
  flip evalStateT initState $
  evalRepl "> " exec options (Prefix (wordCompleter comp) defaultMatcher) pre

verStr :: String
verStr = "CP, version TOPLAS"

ini :: Repl ()
ini = putMsg $ verStr ++ ", :? for help"

-- Top level

data Flag
  = Version
  | Help
  | Run
  | Input String
  | Output String
  deriving (Eq, Show)

flags :: [OptDescr Flag]
flags = [
  Option ['h'] ["help"]    (NoArg Help)               "show this help",
  Option ['r'] ["run"]     (NoArg Run)                "run the code",
  Option ['v'] ["version"] (NoArg Version)            "show version info",
  Option ['i'] ["input"]   (OptArg makeOutput "FILE") "input source file (or without -i)",
  Option ['o'] ["output"]  (OptArg makeOutput "FILE") "output javascript file (optional)"
  ]

makeOutput :: Maybe String -> Flag
makeOutput ms = Output (fromMaybe "" ms)

exitSucc :: Bool -> String -> IO ()
exitSucc ok s = do
  hPutStrLn stderr s
  exitWith $ if ok then ExitSuccess else ExitFailure 1

parseArgs :: [String] -> IO ()
parseArgs args =
  case getOpt RequireOrder flags args of
    (opts, nonOpts, [])
      | Help `elem` opts -> exitSucc True (usageInfo header flags)
      | Version `elem` opts -> exitSucc True verStr
      | otherwise -> do
          let isRun = Run `elem` opts
              findInput [] = ""
              findInput (x:xs) = case x of
                Input f -> f
                _ -> findInput xs
              findOutput [] = ""
              findOutput (x:xs) = case x of
                Output f -> f
                _ -> findInput xs
              inputArg = findInput opts
              inputPath
                | not (null inputArg) = inputArg
                | not (null nonOpts) = head nonOpts
                | otherwise = ""
              outputArg = findOutput opts
              -- outputPath = if null outputArg then
              --                dropExtension inputPath ++ fileExt else outputArg
          if null inputPath then do
            putStrLn "missing arguments: input filename is empty"
            exitWith (ExitFailure 1)
            else do res <- readAndEval inputPath
                    TIO.putStrLn (Pretty.renderStrict (Pretty.layoutSmart prettyOpts res))
            -- compile isDebug isRun isHask inputPath $
            --      if inputPath == outputPath then inputPath ++ fileExt else outputPath
    (_, _, msgs)   ->
      exitSucc False $ concat msgs ++ usageInfo header flags
  where header = "To start the REPL, run the program without parameters.\n" ++
          "Usage: cp-exe [OPTIONS] [FILE]"


main :: IO ()
main = do
  args <- getArgs
  if null args
    then shell ini
    else parseArgs args
