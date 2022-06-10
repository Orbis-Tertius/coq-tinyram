{-# LANGUAGE EmptyCase #-}

module Main where

import System.IO
import System.IO.Unsafe
import System.Environment
import Control.Monad
import Text.Read

import Tinyram_VM

-- Note: this is taken from synthesizer-alsa-0.5.0.6
lazySequence :: [IO a] -> IO [a]
lazySequence [] = return []
lazySequence (m:ms) =
   unsafeInterleaveIO $ liftM2 (:) m $ lazySequence ms

data Void

run_itree :: Itree Void a -> a
run_itree (Go t) =
  case t of
    RetF r -> r
    TauF t -> run_itree t
    VisF e _ -> case e of

run_program_steps :: Integer -> Program -> Tape -> Tape -> Maybe Tinyram_VM.Word
run_program_steps i p t0 t1 = run_itree $ interp_program_for i p t0 t1 

run_program :: Program -> Tape -> Tape -> Tinyram_VM.Word
run_program p t0 t1 = 
  case run_program_steps 9999999 p t0 t1 of
    Nothing -> take (fromIntegral wordSize) (repeat False)
    Just w -> w

parseWord :: Integer -> String -> Either String (Tinyram_VM.Word, String)
parseWord 0 str = Right ([], str)
parseWord i [] = 
  let Right (sb, str) = parseWord (i-1) []
  in Right (False:sb, str)
parseWord i (x:xs) =
  case x of
    '0' -> do
      (sb, str) <- parseWord (i-1) xs
      Right (False:sb, str)
    '1' -> do
      (sb, str) <- parseWord (i-1) xs
      Right (True:sb, str)
    ' ' -> parseWord i xs
    '\n' -> parseWord i xs
    '\r' -> parseWord i xs
    '\t' -> parseWord i xs
    _ -> Left "Non-binary, non-whitespace character encountered while parsing program."

parseInstruction :: String -> Either String ((Tinyram_VM.Word, Tinyram_VM.Word), String)
parseInstruction str = do
  (w1, str') <- parseWord wordSize str
  (w2, str'') <- parseWord wordSize str'
  return ((w1, w2), str'')

parseWords :: String -> Either String (Tinyram_VM.Word, String)
parseWords str = do
  (w1, str') <- parseWord wordSize str
  return (w1, str')

parseProgram :: String -> Either String Program
parseProgram [] = Right []
parseProgram str = do
  (ws, str') <- parseInstruction str
  prg <- parseProgram str'
  Right (ws:prg)

parseTape :: String -> Either String Tape
parseTape [] = Right []
parseTape str = do
  (ws, str') <- parseWords str
  prg <- parseTape str'
  Right (ws:prg)

readProgram :: String -> IO (Either String Program)
readProgram str = do
  handle <- openFile str ReadMode
  text <- hGetContents handle
  return (parseProgram text)

readTape :: String -> IO (Either String Tape)
readTape str = do
  handle <- openFile str ReadMode
  text <- hGetContents handle
  return (parseTape text)

interactionRequest :: String -> IO Tinyram_VM.Word
interactionRequest str = do
  putStr (str ++ "> ")
  hFlush stdout
  input <- getLine
  case readMaybe input of
    Nothing -> do
      putStrLn "Input must be a number. Please try again."
      interactionRequest str
    Just n -> return (n_bitvector_big wordSize n)

interactiveLoopSteps :: Integer -> Program -> IO (Maybe Tinyram_VM.Word)
interactiveLoopSteps n p =
  let mainTape = repeat (interactionRequest "Main Tape Input\n")
      auxTape = repeat (interactionRequest "Auxiliary Tape Input\n")
  in do
    mt <- lazySequence mainTape
    at <- lazySequence auxTape
    return (run_program_steps n p mt at)

interactiveLoop :: Program -> IO Tinyram_VM.Word
interactiveLoop p =
  let mainTape = repeat (interactionRequest "Main Tape Input\n")
      auxTape = repeat (interactionRequest "Auxiliary Tape Input\n")
  in do
    mt <- lazySequence mainTape
    at <- lazySequence auxTape
    return (run_program p mt at)

showWord :: Tinyram_VM.Word -> String
showWord [] = ""
showWord (True:r) = '1':showWord r
showWord (False:r) = '0':showWord r

helpString =
  "Help for Coq TinyRam:\n" ++
  "-h:\n"++
  "\tDisplay help text.\n" ++
  "<Arg>:\n"++
  "\tWill run the program <Arg> in an interactive mode,\n\trequesting inputs whenever the tapes are used.\n" ++
  "<Args> -s <n>\n" ++
  "\tWill run the program in an interactive mode for n steps.\n" ++
  "<Prog> <Main> <Aux> <Step>\n" ++
  "\tWill run the program \"Prog\" on \"Main\" and \"Aux\" inputs for \"Step\" steps in noninteractive mode."

printAnswer :: Tinyram_VM.Word -> IO ()
printAnswer wrd = do
  putStrLn ("\n\tBitString: " ++ showWord wrd ++ "\n\t" ++
            "Nat: " ++ show (bitvector_N_big wordSize wrd) ++ "\n\t" ++
            "Int: " ++ show (twos_complement wordSize wrd))

helpMultErr n =
  "Error: Help expects no arguments, but " ++ show n ++ " were given."

stepArgErr n =
  "Error: Step flag 1 argument, but " ++ show n ++ " were given."

stepAftErr =
  "Error: Step counter must be given after program argument."

mainTapeParseErr =
  "Error: Main tape could not be parsed into a list of integers."

auxTapeParseErr =
  "Error: Aux tape could not be parsed into a list of integers."

ignoreWarn =
  "Warning: Trailing arguments are being ignored."

oneArg :: String -> IO ()
oneArg x = 
  case x of
    "-s" -> putStrLn stepAftErr
    "-h" -> putStrLn helpString
    _ -> do
      putStrLn ("Running program " ++ x ++ " in interactive mode.")
      mb <- readProgram x
      case mb of
        Left err -> putStrLn ("Error: " ++ err) 
        Right prg -> do
          wrd <- interactiveLoop prg
          printAnswer wrd

threeArg :: String -> String -> String -> IO ()
threeArg x mt at = case x of
  "-s" -> putStrLn stepAftErr
  "-h" -> putStrLn (helpMultErr 2)
  _ -> case mt of
    "-s" -> do
      putStrLn ("Running program " ++ x ++ " in interactive mode for " ++ at ++ " steps.\n")
      case readMaybe at of
        Nothing -> putStrLn ("Error: Could not parse " ++ at ++ " into value stepcount.")
        Just n -> do
          mb <- readProgram x
          case mb of
            Left err -> putStrLn ("Error: " ++ err) 
            Right prg -> do
              mwrd <- interactiveLoopSteps n prg
              case mwrd of
                Nothing -> putStrLn ("Error: Program did not halt within " ++ show n ++ " steps.")
                Just wrd -> printAnswer wrd
    "-h" -> putStrLn (helpMultErr 2)

fourArg :: String -> String -> String -> String -> IO ()
fourArg x mt at sc = do
  putStrLn ("Running program " ++ x ++ " in non-interactive mode with main tape\n" ++ 
            mt ++ " and auxiliary tape " ++ at ++ " for " ++ sc ++ " steps.\n")
  prog <- readProgram x
  case prog of
    Left err -> putStrLn ("Error: " ++ err) 
    Right prg -> do
      mainTape <- readTape mt
      case mainTape of
        Left err -> putStrLn ("Error: " ++ err) 
        Right mtp -> do
          auxTape <- readTape at
          case auxTape of
            Left err -> putStrLn ("Error: " ++ err) 
            Right atp -> 
              case run_program_steps (read sc) prg mtp atp of
                Nothing -> putStrLn ("Error: Program did not halt within " ++ sc ++ " steps.")
                Just wrd -> printAnswer wrd

main :: IO ()
main = do
  name <- getArgs
  case name of
    [] -> putStrLn "Error: Executable must be called with some argument or flag.\nUse \"-h\" for help."
    (x:[]) -> oneArg x
    (x:mt:[]) -> putStrLn "Error: Executable called with wrong number of arguments.\nUse \"-h\" for help."
    (x:mt:at:[]) -> threeArg x mt at
    (x:mt:at:ki:[]) -> fourArg x mt at ki
    (x:mt:at:ki:_) -> do
      putStrLn ignoreWarn
      threeArg x mt at

