module Main (main) where

import Control.Monad.IO.Class (liftIO)
import Heap
import System.IO

main :: IO ()
main = execute [("main", \_ -> replay [] >> pure (Number 0))] [] False (pure ()) (pure ())

say :: String -> R ()
say line = liftIO (putStrLn line >> hFlush stdout)

builtin :: Maybe CType -> String -> [Value] -> R Value
builtin expected name arguments = invoke expected (function name) (map pure arguments)

replay :: [Value] -> R ()
replay table = do
  finished <- liftIO isEOF
  if finished then pure () else do
    request <- words <$> liftIO getLine
    let located p o = offset (read o) (table !! read p)
        integer w = IntegerType (8 * w) False
        continue = replay table
        value result = say ("value " ++ show (number result)) >> continue
        done = say "done" >> continue
        pointer result = say ("pointer " ++ show (number result)) >> replay (table ++ [result])
    case request of
      ["alloc", size] -> builtin (Just PointerType) "malloc" [Number (read size)] >>= pointer
      ["loadbyte", p, o] -> load (integer 1) (located p o) >>= value
      ["storebyte", p, o, v] -> store (integer 1) (located p o) (Number (read v)) >> done
      ["loadword", p, o, w] -> load (integer (read w)) (located p o) >>= value
      ["storeword", p, o, w, v] -> store (integer (read w)) (located p o) (Number (read v)) >> done
      ["loadpointer", p, o] -> load PointerType (located p o) >>= pointer
      ["storepointer", p, o, q] -> store PointerType (located p o) (table !! read q) >> done
      ["copy", s, so, d, o, n] -> builtin Nothing "memcpy" [located d o, located s so, Number (read n)] >> done
      ["free", p] -> builtin Nothing "free" [table !! read p] >> done
      _ -> panic ("malformed request: " ++ unwords request)
