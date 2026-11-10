{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MagicHash #-}
module Heap
  ( Value(Number, Single, DoublePrecision, Extended), CType(..), Flow(..), R, nullPointer, noValue, marshal, convert, extendedLiteral
  , number, truth, normalise, cast, panic, at, atFlow, offset, load, store
  , frame, declare, variable, parameter, global, literal, materialise, clear
  , freeze
  , chain, discard, statementValue, redirectFlow, branch, loop, postloop, selection, dispatch, indirectJump, logic, conditional, boolean, binary, unary
  , assign, update, realBinary, realUpdate, function, invoke, execute
  , asmBarrier, asmRegisters
  , imaginary, makeComplex, complexPart, complexBinary, complexUpdate
  , argumentArea, vaStart, vaCopy, vaArg, vaAvailable
  , AtomicMode(..), atomicAccess, atomicTransfer, atomicModify, atomicCompare, atomicPointerStep
  , vlaDeclare, vlaBind, vlaSize, vlaIndex, vlaBinary, vlaUpdate, vlaExtent, vlaAlias, vlaFromAlias
  ) where

import Control.Monad
import Control.Concurrent (MVar, ThreadId, forkIOWithUnmask, modifyMVar, modifyMVar_, myThreadId, newEmptyMVar, newMVar, putMVar, takeMVar, throwTo, withMVar)
import qualified Control.Exception as E
import Control.Monad.Except
import Control.Monad.State.Strict
import Data.Bits
import qualified Data.ByteString.Char8 as B
import Data.Char
import Data.IORef
import Data.List (intercalate)
import qualified Data.Sequence as Q
import Data.Ratio (numerator, denominator, (%))
import GHC.Environment (getFullArgs)
import GHC.Exts (Int(I#))
import qualified GHC.Foreign as F
import GHC.Float (castFloatToWord32, castWord32ToFloat, castDoubleToWord64, castWord64ToDouble, float2Double, double2Float)
import GHC.IO.Encoding (getFileSystemEncoding)
import GHC.Integer.Logarithms (integerLog2#)
import qualified Data.IntMap.Strict as M
import qualified Data.IntSet as I
import qualified Data.Map.Strict as S
import Numeric (showHex, showOct)
import System.Environment
import System.Exit
import System.IO
import System.IO.Error (tryIOError, ioeGetErrorString)

data Capability = NoCapability | Capability !Int !(IORef Object) deriving Eq
instance Show Capability where
  show NoCapability = "0"
  show (Capability ident _) = show ident
data Value = Number !Integer | Wide !Integer | Pointer !Capability !Integer | Function !Integer !String | Stream !Int !Integer
  | Single !Float | DoublePrecision !Double | Extended !Integer | Complex !Int !Value !Value
  | Aggregate !Int !Int !(M.IntMap Integer) !(M.IntMap Value) | NoValue deriving (Eq, Show)
data CType = IntegerType !Int !Bool | PointerType | FloatingType !Int | ComplexType !Int | AggregateType !Int !Int
  | BitField !Int !Int !Bool | AtomicType !CType | AtomicAggregate !Int !CType !AtomicMode deriving (Eq, Show)
data AtomicMode = AtomicBytes | AtomicCapability | AtomicCopy deriving (Eq, Show)
data Flow = Next | Return !Value | Break | Continue | Jump !Int deriving (Eq, Show)
data Fault = Panic !String | Finish !Int | Transfer !Flow deriving (Eq, Show)
instance E.Exception Fault
data Synchronisation
  = Mutex !(Maybe Integer) !(Q.Seq (Integer, MVar ()))
  | Condition !(Q.Seq (MVar ()))
  | Destroyed
data Object = Object
  { base :: !Integer, extent :: !Int, live :: !Bool, storage :: !String
  , bytes :: !(M.IntMap Integer), shadow :: !(M.IntMap Value), atomicSlots :: !I.IntSet
  , synchronisation :: !(M.IntMap Synchronisation), arraySpans :: ![Integer], origin :: !String }
data World = World
  { allocationCounter :: !(IORef (Int, Integer))
  , frames :: ![S.Map String Value], globals :: !(S.Map String Value)
  , literals :: !(S.Map String Value), functions :: !(S.Map String ([Value] -> R Value))
  , symbols :: !(S.Map String Integer)
  , location :: !String, events :: !Int, recent :: ![String], tracing :: !Bool, history :: !Bool
  , streamTable :: !(IORef (Int, M.IntMap Handle))
  , memoryGate :: !(Maybe (MVar ())), threadTable :: !(MVar (S.Map Integer (MVar Value)))
  , rootThread :: !ThreadId, currentThread :: !Value, threadInitialiser :: !(R ()) }
newtype R a = R { unR :: ExceptT Fault (StateT World IO) a }
  deriving (Functor, Applicative, Monad, MonadIO, MonadState World, MonadError Fault)

runWorld :: World -> R a -> IO (Either Fault a, World)
runWorld world action = runStateT (runExceptT (unR action)) world

locked :: R a -> R a
locked action = R $ ExceptT $ StateT $ \world ->
  case memoryGate world of
    Nothing -> runWorld world action
    Just gate -> withMVar gate (\_ -> runWorld world action)

number :: Value -> Integer
number (Number n) = n
number (Wide n) = n
number (Pointer _ n) = n
number (Function code _) = code
number (Stream _ raw) = raw
number (Single value) = toInteger (castFloatToWord32 value)
number (DoublePrecision value) = toInteger (castDoubleToWord64 value)
number (Extended bits) = bits
number (Complex width real imag) = number real .|. shiftL (number imag) (8 * widthOf (FloatingType width))
number (Aggregate _ _ _ _) = 0
number NoValue = 0

truth :: Value -> Bool
truth (Single value) = value /= 0
truth (DoublePrecision value) = value /= 0
truth (Extended bits) = case unpackExtended bits of Finite _ value -> value /= 0; _ -> True
truth (Complex _ real imag) = truth real || truth imag
truth v = number v /= 0

normalise :: Int -> Bool -> Integer -> Integer
normalise width signed n =
  let modulus = 2 ^ width
      bits = n `mod` modulus
  in if signed && bits >= modulus `div` 2 then bits - modulus else bits

cast :: CType -> Value -> Value
cast (IntegerType w s) v = Number (normalise w s (number v))
cast PointerType p@(Pointer _ _) = p
cast PointerType f@(Function _ _) = f
cast PointerType s@(Stream _ _) = s
cast PointerType (Number n) = Pointer NoCapability (normalise 64 False n)
cast PointerType (Wide n) = Pointer NoCapability (normalise 64 False n)
cast PointerType NoValue = nullPointer
cast PointerType (Aggregate _ _ _ _) = nullPointer
cast PointerType (Single _) = nullPointer
cast PointerType (DoublePrecision _) = nullPointer
cast PointerType (Extended _) = nullPointer
cast PointerType (Complex _ _ _) = nullPointer
cast (FloatingType 32) value = Single (castWord32ToFloat (fromInteger (number value)))
cast (FloatingType 80) value = Extended (normalise 80 False (number value))
cast (FloatingType _) value = DoublePrecision (castWord64ToDouble (fromInteger (number value)))
cast (ComplexType width) value =
  let ty = FloatingType width
      half = 8 * widthOf ty
      raw = number value
  in Complex width (cast ty (Number (normalise half False raw))) (cast ty (Number (shiftR raw half)))
cast (AggregateType _ _) v = v
cast (BitField _ width signed) v = Number (normalise width signed (number v))
cast (AtomicType ty) value = cast ty value
cast (AtomicAggregate _ ty _) value = cast ty value

convert :: CType -> Value -> R Value
convert (ComplexType width) value =
  Complex width <$> convert (FloatingType width) (complexPart False value)
                <*> convert (FloatingType width) (complexPart True value)
convert ty (Complex _ real _) = convert ty real
convert (FloatingType 32) value = pure (Single (asSingle value))
convert (FloatingType 80) value = pure (packExtended (asExtended value))
convert (FloatingType _) value = pure (DoublePrecision (asDouble value))
convert ty@(IntegerType width signed) value = case value of
  Single real -> integer (hostExtended (float2Double real))
  DoublePrecision real -> integer (hostExtended real)
  Extended real -> integer (unpackExtended real)
  _ -> pure (cast ty value)
  where
    integer (Finite negative real) =
          let result = (if negative then negate else id) (truncate real)
          in if normalise width signed result == result then pure (Number result)
             else panic "floating-to-integer conversion out of range"
    integer _ = panic "non-finite floating-to-integer conversion"
convert ty value = pure (cast ty value)

nullPointer :: Value
nullPointer = Pointer NoCapability 0

noValue :: Value
noValue = NoValue

marshal :: CType -> Value -> Value
marshal (IntegerType 128 _) value = Wide (normalise 128 False (number value))
marshal (IntegerType width _) value = Number (normalise width False (number value))
marshal PointerType value = cast PointerType value
marshal (FloatingType 80) value = cast (FloatingType 80) value
marshal (FloatingType width) value = Number (normalise width False (number value))
marshal (ComplexType width) value = cast (ComplexType width) value
marshal (AggregateType _ _) value = value
marshal (BitField _ width _) value = Number (normalise width False (number value))
marshal (AtomicType ty) value = marshal ty value
marshal (AtomicAggregate _ ty _) value = marshal ty value

slotSize :: Int -> Integer
slotSize size = ((toInteger size + 7) `div` 8) * 8

addSlot :: Integer -> CType -> (Integer, Integer)
addSlot from ty =
  let alignment = case ty of
        FloatingType 80 -> 16
        ComplexType 80 -> 16
        AggregateType _ a -> max 8 (toInteger a)
        _ -> 8
  in alignedSlot from ty alignment

alignedSlot :: Integer -> CType -> Integer -> (Integer, Integer)
alignedSlot from ty alignment =
  let start = ((from + alignment - 1) `div` alignment) * alignment
  in (start, start + slotSize (widthOf ty))

argumentArea :: [Value] -> R Value
argumentArea values = do
  let slot value = case value of
        Aggregate size alignment _ _ -> (AggregateType size alignment, value)
        Extended _ -> (FloatingType 80, value)
        Complex width _ _ -> (ComplexType width, value)
        Wide _ -> (IntegerType 128 False, value)
        _ | addressed value -> (PointerType, value)
          | otherwise -> (IntegerType 64 False, value)
      slots = map slot values
      offsets = scanl (\index (ty, _) -> snd (addSlot index ty)) 0 slots
  size <- hostSize (last offsets)
  area <- allocate "argument" size
  forM_ (zip offsets slots) $ \(index, (ty, value)) ->
    void (store ty (offset (fst (addSlot index ty)) area) value)
  freeze (pure area)
  pure area

vaStart :: Value -> [CType] -> R Value -> R Value
vaStart area named list = do
  pointer <- list
  let start = foldl (\index ty -> snd (addSlot index ty)) 0 named
  store PointerType pointer (offset start area) >> pure (Number 0)

vaCopy :: R Value -> R Value -> R Value
vaCopy destination source = do
  pointer <- destination
  cursor <- source >>= load PointerType
  store PointerType pointer cursor >> pure (Number 0)

vaArg :: CType -> R Value -> R Value
vaArg ty list = do
  pointer <- list
  cursor <- load PointerType pointer
  let (start, next) = case ty of
        IntegerType 128 _ -> alignedSlot (number cursor) ty 16
        _ -> addSlot (number cursor) ty
  value <- load ty (offset (start - number cursor) cursor)
  void (store PointerType pointer (offset (next - number cursor) cursor))
  pure value

vaAvailable :: R Value -> R Value
vaAvailable list = do
  cursor <- list >>= load PointerType
  case cursor of
    Pointer NoCapability _ -> pure (boolean False)
    Pointer capability raw -> do
      object <- readObject capability
      pure (boolean (live object && raw >= base object && raw + 8 <= base object + toInteger (extent object)))
    _ -> pure (boolean False)

readObject :: Capability -> R Object
readObject NoCapability = panic "access through a pointer with no allocation capability"
readObject (Capability _ reference) = liftIO (readIORef reference)

writeObject :: Capability -> Object -> R ()
writeObject NoCapability _ = panic "access through a pointer with no allocation capability"
writeObject (Capability _ reference) object = liftIO (writeIORef reference object)

panic :: String -> R a
panic message = do
  loc <- gets location
  throwError (Panic (loc ++ ": " ++ message))

at :: String -> R a -> R a
at loc action = do
  old <- gets location
  modify' (\w -> w { location = loc })
  result <- action
  modify' (\w -> w { location = old })
  pure result

atFlow :: String -> R Flow -> R Flow
atFlow loc action = at loc (action `catchError` transfer)
  where
    transfer (Transfer flow) = pure flow
    transfer fault = throwError fault

event :: String -> R ()
event message = do
  recorded <- gets history
  when recorded $ do
    n <- gets events
    loc <- gets location
    let packed = B.pack (show (n + 1) ++ "  " ++ message ++ "  [" ++ loc ++ "]")
    B.length packed `seq` modify' (\w -> w { events = n + 1, recent = take 8 (B.unpack packed : recent w) })
    enabled <- gets tracing
    when enabled (liftIO (B.hPutStrLn stderr packed))

allocate :: String -> Int -> R Value
allocate kind size = do
  let alignment = if kind == "global" then 8 else 16
  when (size < 0 || size > maxBound - (alignment - 1)) (panic "allocation size exceeds the host representation")
  counter <- gets allocationCounter
  loc <- gets location
  let rounded = ((size + (alignment - 1)) `div` alignment) * alignment
  entry <- liftIO $ atomicModifyIORef' counter $ \old@(ident, address) ->
    let start = ((address + 15) `div` 16) * 16 in
    if ident == maxBound || start + toInteger rounded >= 4611686018427387904 then (old, Nothing)
    else ((ident + 1, start + toInteger (max rounded 1) + 16), Just (ident, start))
  (ident, start) <- maybe (panic "virtual address space exhausted") pure entry
  let object = Object start rounded True kind M.empty M.empty I.empty M.empty [] loc
  reference <- liftIO (newIORef object)
  event ("allocate #" ++ show ident ++ " " ++ show rounded ++ " bytes (" ++ kind ++ ")")
  pure (Pointer (Capability ident reference) start)

checked :: Int -> Value -> R (Capability, Object, Int)
checked size (Pointer capability raw) = do
  object <- readObject capability
  unless (live object) (panic ("use after free of allocation #" ++ show capability ++ "; allocated at " ++ origin object))
  let displacement = raw - base object
  when (size < 0 || displacement < 0 || displacement > toInteger (extent object) || toInteger size > toInteger (extent object) - displacement)
    (panic ("out of bounds in allocation #" ++ show capability ++ ": offset " ++ show displacement ++ ", access " ++ show size ++ ", extent " ++ show (extent object)))
  pure (capability, object, fromInteger displacement)
checked _ _ = panic "memory access requires a data pointer"

widthOf :: CType -> Int
widthOf PointerType = 8
widthOf (IntegerType width _) = width `div` 8
widthOf (AggregateType width _) = width
widthOf (FloatingType 80) = 16
widthOf (FloatingType width) = width `div` 8
widthOf (ComplexType width) = 2 * widthOf (FloatingType width)
widthOf (BitField bitOffset width _) = (bitOffset + width + 7) `div` 8
widthOf (AtomicType ty) = widthOf ty
widthOf (AtomicAggregate width _ _) = width

aggregateBytes :: Int -> Int -> M.IntMap a -> M.IntMap a
aggregateBytes start count values =
  M.mapKeysMonotonic (subtract start) (M.takeWhileAntitone (< start + count) (M.dropWhileAntitone (< start) values))

aggregateShadow :: Int -> Int -> M.IntMap Value -> M.IntMap Value
aggregateShadow start count = aggregateBytes start (max 0 (count - 7))

encodeBytes :: Int -> Integer -> M.IntMap Integer
encodeBytes size raw = M.fromDistinctAscList [(i, shiftR raw (8 * i) .&. 255) | i <- [0 .. size - 1]]

decodeBytes :: M.IntMap Integer -> Integer
decodeBytes = M.foldlWithKey' (\raw index byte -> raw .|. shiftL byte (8 * index)) 0

readScalar :: Int -> Int -> M.IntMap Integer -> Integer
readScalar displacement width payload =
  sum [M.findWithDefault 0 (displacement + i) payload * 256 ^ i | i <- [0 .. width - 1]]

writeScalar :: Int -> Int -> Integer -> M.IntMap Integer -> M.IntMap Integer
writeScalar displacement width raw payload =
  foldl (\m i -> M.insert (displacement + i) ((raw `div` (256 ^ i)) `mod` 256) m) payload [0 .. width - 1]

load :: CType -> Value -> R Value
load ty pointer = locked (loadCell ty pointer)

loadCell :: CType -> Value -> R Value
loadCell (AtomicAggregate width ty@(AggregateType size alignment) mode) pointer =
  case mode of
    AtomicCopy -> loadCell ty pointer
    AtomicBytes -> do
      value <- loadCell (IntegerType (8 * width) False) pointer
      pure (Aggregate size alignment (encodeBytes size (number value)) M.empty)
    AtomicCapability -> do
      value <- loadCell (AtomicType PointerType) pointer
      pure (Aggregate size alignment (encodeBytes size (number value)) (M.singleton 0 value))
loadCell declared pointer = do
  let ty = case declared of AtomicType inner -> inner; other -> other
  (ident, object, displacement) <- checked (widthOf declared) pointer
  when (ty == PointerType && number pointer `mod` 8 /= 0) (panic "unaligned pointer load")
  let raw = readScalar displacement (widthOf ty) (bytes object)
      value = case ty of
        IntegerType width signed -> Number (normalise width signed raw)
        BitField bitOffset width signed -> Number (normalise width signed (shiftR raw bitOffset))
        FloatingType _ -> cast ty (Number raw)
        ComplexType _ -> cast ty (Number raw)
        AggregateType size alignment -> Aggregate size alignment (aggregateBytes displacement size (bytes object)) (aggregateShadow displacement size (shadow object))
        AtomicType _ -> NoValue
        AtomicAggregate _ _ _ -> NoValue
        PointerType -> case M.lookup displacement (shadow object) of
          Just stored | declared == AtomicType PointerType && I.member displacement (atomicSlots object) -> stored
          Just (Pointer cap _) -> Pointer cap raw
          Just (Function _ name) -> Function raw name
          Just (Stream streamId _) -> Stream streamId raw
          _ -> Pointer NoCapability raw
  unless (storage object == "literal") (event ("load #" ++ show ident ++ "+" ++ show displacement ++ " = " ++ describe value))
  pure value

store :: CType -> Value -> Value -> R Value
store ty pointer value = locked (storeCell ty pointer value)

storeCell :: CType -> Value -> Value -> R Value
storeCell (AtomicAggregate width ty@(AggregateType size _) mode) pointer value@(Aggregate actual _ payload caps)
  | size == actual = do
      let raw = decodeBytes payload
      case mode of
        AtomicCopy -> void (storeCell ty pointer value)
        AtomicBytes -> void (storeCell (IntegerType (8 * width) False) pointer (Number raw))
        AtomicCapability -> do
          let capability = case M.lookup 0 caps of
                Just (Pointer cap _) -> Pointer cap raw
                Just (Function _ name) -> Function raw name
                Just (Stream ident _) -> Stream ident raw
                _ -> Pointer NoCapability raw
          void (storeCell (AtomicType PointerType) pointer capability)
      pure value
storeCell (AggregateType size _) pointer value@(Aggregate actual _ payload caps) | size == actual = do
  (ident, object, displacement) <- checked size pointer
  when (readOnly object) (panic "write to read-only memory")
  when (not (M.null caps) && number pointer `mod` 8 /= 0) (panic "unaligned aggregate pointer store")
  let replace start count new old =
        let before = M.takeWhileAntitone (< start) old
            after = M.dropWhileAntitone (< start + count) old
        in M.unions [before, M.mapKeysMonotonic (+ start) new, after]
      firstWord = ((displacement + 7) `div` 8) * 8
      pastWords = max firstWord (displacement + size - 7)
      updated = replace displacement size payload (bytes object)
      retained = M.union (M.takeWhileAntitone (< firstWord) (shadow object)) (M.dropWhileAntitone (< pastWords) (shadow object))
      capabilities = M.union (M.mapKeysMonotonic (+ displacement) caps) retained
      modes = I.filter (\i -> i < firstWord || i >= pastWords) (atomicSlots object)
  writeObject ident (object { bytes = updated, shadow = capabilities, atomicSlots = modes })
  pure value
storeCell (AggregateType _ _) _ _ = panic "incompatible aggregate value"
storeCell _ _ (Aggregate _ _ _ _) = panic "aggregate value used as a scalar"
storeCell declared pointer value = do
  let ty = case declared of AtomicType inner -> inner; other -> other
  (ident, object, displacement) <- checked (widthOf declared) pointer
  when (readOnly object) (panic "write to read-only memory")
  when (ty == PointerType && number pointer `mod` 8 /= 0) (panic "unaligned pointer store")
  let converted = cast ty value
      raw = case ty of
        BitField bitOffset width _ ->
          let word = readScalar displacement (widthOf ty) (bytes object)
              mask = shiftL (2 ^ width - 1) bitOffset
          in (word .&. complement mask) .|. (shiftL (normalise width False (number converted)) bitOffset)
        _ -> number converted
      updated = writeScalar displacement (widthOf ty) raw (bytes object)
      caps = if ty == PointerType then M.insert displacement converted (shadow object) else shadow object
      modes
        | declared == AtomicType PointerType = I.insert displacement (atomicSlots object)
        | ty == PointerType = I.delete displacement (atomicSlots object)
        | otherwise = atomicSlots object
  writeObject ident (object { bytes = updated, shadow = caps, atomicSlots = modes })
  event ("store #" ++ show ident ++ "+" ++ show displacement ++ " = " ++ describe converted)
  pure converted

describe :: Value -> String
describe (Number n) = show n
describe (Wide n) = show n
describe (Single value) = show value
describe (DoublePrecision value) = show value
describe (Extended bits) = "extended(0x" ++ showHex bits ")"
describe (Complex _ real imag) = "(" ++ describe real ++ ", " ++ describe imag ++ ")"
describe (Pointer cap raw) = "pointer(#" ++ show cap ++ ", " ++ show raw ++ ")"
describe (Function _ name) = "function(" ++ name ++ ")"
describe (Stream ident _) = "stream(#" ++ show ident ++ ")"
describe (Aggregate size _ _ _) = "aggregate(" ++ show size ++ " bytes)"
describe NoValue = "void"

offset :: Integer -> Value -> Value
offset n (Pointer cap raw) = Pointer cap (normalise 64 False (raw + n))
offset n (Function raw name) = Function (normalise 64 False (raw + n)) name
offset n (Stream ident raw) = Stream ident (normalise 64 False (raw + n))
offset _ v = v

addressed :: Value -> Bool
addressed (Pointer _ _) = True
addressed (Function _ _) = True
addressed (Stream _ _) = True
addressed _ = False

release :: Value -> R ()
release pointer = locked (releaseCell pointer)

releaseCell :: Value -> R ()
releaseCell (Pointer NoCapability 0) = pure ()
releaseCell pointer@(Pointer ident _) = do
  (_, object, displacement) <- checked 0 pointer
  unless (storage object == "heap" && displacement == 0) (panic "free requires the start of a heap allocation")
  writeObject ident (object { live = False, bytes = M.empty, shadow = M.empty, atomicSlots = I.empty, synchronisation = M.empty })
  event ("free #" ++ show ident ++ "; all aliases invalidated")
releaseCell _ = panic "free requires a data pointer"

frame :: R Flow -> R Value
frame action = do
  modify' (\w -> w { frames = S.empty : frames w })
  flow <- action `catchError` (\fault -> modify' (\w -> w { frames = tail (frames w) }) >> throwError fault)
  modify' (\w -> w { frames = tail (frames w) })
  case flow of
    Return value -> pure value
    Next -> pure (Number 0)
    _ -> panic "loop control escaped its function"

declare :: String -> Int -> R Value
declare name size = do
  p <- allocate "local" size
  modify' (\w -> w { frames = case frames w of
    [] -> []
    env : rest -> S.insert name p env : rest })
  pure p

vlaDeclare :: String -> Integer -> [R Value] -> R Flow
vlaDeclare name width bounds = do
  spans <- vlaSpans width bounds
  size <- hostSize (head spans)
  pointer <- declare name size
  attachSpans pointer spans
  pure Next

vlaSpans :: Integer -> [R Value] -> R [Integer]
vlaSpans width bounds = do
  dimensions <- mapM (fmap number) bounds
  when (any (<= 0) dimensions) (panic "nonpositive variable-length array bound")
  pure (scanr (*) width dimensions)

vlaExtent :: Integer -> [R Value] -> R Value
vlaExtent width bounds = do
  spans <- vlaSpans width bounds
  Number . toInteger <$> hostSize (head spans)

attachSpans :: Value -> [Integer] -> R ()
attachSpans pointer spans = locked $
  case pointer of
    Pointer capability _ -> do
      object <- readObject capability
      writeObject capability (object { arraySpans = spans })
    _ -> panic "variable-length array needs a data capability"

vlaBind :: Int -> Value -> Integer -> [R Value] -> R ()
vlaBind skip pointer width bounds = vlaSpans width bounds >>= attachSpans pointer . drop skip

vlaAlias :: String -> Integer -> [R Value] -> R Flow
vlaAlias name width bounds = do
  spans <- vlaSpans width bounds
  pointer <- declare name 0
  attachSpans pointer spans
  pure Next

vlaFromAlias :: String -> R Value -> R Flow
vlaFromAlias name alias = do
  pointer <- alias
  spans <- case pointer of
    Pointer capability _ -> arraySpans <$> readObject capability
    _ -> panic "variable-length typedef has no shape"
  size <- case spans of
    whole : _ -> hostSize whole
    [] -> panic "variable-length typedef has no shape"
  object <- declare name size
  attachSpans object spans
  pure Next

vlaSpan :: Int -> Value -> R Integer
vlaSpan rank (Pointer capability _) = do
  object <- readObject capability
  case drop rank (arraySpans object) of
    size : _ -> pure size
    [] -> panic "missing variable-length array extent"
vlaSpan _ _ = panic "variable-length array needs a data capability"

vlaSize :: Int -> R Value -> R Value
vlaSize rank pointer = Number <$> (pointer >>= vlaSpan rank)

vlaIndex :: Int -> R Value -> R Value -> R Value -> R Value
vlaIndex rank shape pointer index = vlaBinary "+" rank shape pointer index

vlaBinary :: String -> Int -> R Value -> R Value -> R Value -> R Value
vlaBinary op rank shape left right = do
  a <- left
  b <- right
  stride <- shape >>= vlaSpan rank
  let signed = op == "-" && addressed a && addressed b
  either panic pure (calculate op 64 signed stride a b)

vlaUpdate :: String -> Int -> R Value -> Bool -> R Value -> R Value -> R Value
vlaUpdate op rank shape postfix destination expression = do
  stride <- shape >>= vlaSpan rank
  update op PointerType 64 False stride postfix destination expression

variable :: String -> R Value
variable name = do
  w <- get
  case (case frames w of [] -> Nothing; env : _ -> S.lookup name env) of
    Just pointer -> pure pointer
    Nothing -> maybe (panic ("unknown variable " ++ name)) pure (S.lookup name (globals w))

parameter :: String -> CType -> Value -> R ()
parameter name ty value = declare name (widthOf ty) >>= \p -> void (store ty p value)

temporary :: Int -> (Value -> R ()) -> R Value
temporary size initialiseObject = do
  pointer <- allocate "local" size
  initialiseObject pointer
  pure pointer

materialise :: CType -> R Value -> R Value
materialise ty action = do
  value <- action
  temporary (widthOf ty) (\pointer -> void (store ty pointer value))

clear :: Int -> Value -> R ()
clear size pointer = void (store (AggregateType size 1) pointer (Aggregate size 1 M.empty M.empty))

global :: String -> Int -> R Value
global name size = do
  p <- allocate "global" size
  modify' (\w -> w { globals = S.insert name p (globals w) })
  pure p

readOnly :: Object -> Bool
readOnly object = storage object `elem` ["literal", "constant"]

freeze :: R Value -> R ()
freeze action = do
  pointer <- action
  case pointer of
    Pointer capability _ -> locked $ do
      object <- readObject capability
      writeObject capability (object { storage = "constant" })
    _ -> panic "read-only storage requires a data pointer"

literal :: String -> R Value
literal text = do
  found <- gets (S.lookup text . literals)
  case found of
    Just p -> pure p
    Nothing -> do
      oldEvents <- gets events
      oldRecent <- gets recent
      oldTracing <- gets tracing
      oldHistory <- gets history
      modify' (\w -> w { tracing = False, history = False })
      pointer <- allocate "global" (length text + 1)
      forM_ (zip [0..] (map ord text ++ [0])) $ \(i, c) -> void (store (IntegerType 8 False) (offset i pointer) (Number (toInteger c)))
      case pointer of
        Pointer capability _ -> do
          locked $ do
            object <- readObject capability
            writeObject capability (object { storage = "literal" })
          modify' (\w -> w { literals = S.insert text pointer (literals w) })
        _ -> pure ()
      modify' (\w -> w { events = oldEvents, recent = oldRecent, tracing = oldTracing, history = oldHistory })
      pure pointer

argument :: String -> R Value
argument text = do
  payload <- liftIO $ do
    encoding <- getFileSystemEncoding
    F.withCString encoding text B.packCString
  pointer <- allocate "argument" (B.length payload + 1)
  forM_ (zip [0..] (B.unpack payload ++ ['\0'])) $ \(i, c) -> void (store (IntegerType 8 False) (offset i pointer) (Number (toInteger (ord c))))
  pure pointer

readString :: Value -> R String
readString pointer = collect pointer []
  where
    collect current reversed = do
      value <- load (IntegerType 8 False) current
      if number value == 0 then pure (reverse reversed)
        else collect (offset 1 current) (chr (fromInteger (number value)) : reversed)

chain :: [R Flow] -> R Flow
chain [] = pure Next
chain (action : rest) = action >>= \flow -> if flow == Next then chain rest else pure flow

discard :: R Value -> R Flow
discard action = action >> pure Next

statementValue :: R Flow -> R Value -> R Value
statementValue action result = do
  flow <- action
  case flow of
    Next -> result
    _ -> throwError (Transfer flow)

redirectFlow :: Int -> Int -> R Flow -> R Flow
redirectFlow stop restart action = do
  result <- action
  case result of
    Break -> pure (Jump stop)
    Continue -> pure (Jump restart)
    _ -> pure result

branch :: R Value -> R Flow -> R Flow -> R Flow
branch condition yes no = condition >>= \v -> if truth v then yes else no

loop :: R Value -> R Flow -> R Value -> R Flow
loop condition body advance = do
  value <- condition
  if not (truth value) then pure Next else do
    result <- body
    case result of
      Return v -> pure (Return v)
      Break -> pure Next
      _ -> advance >> loop condition body advance

postloop :: R Flow -> R Value -> R Flow
postloop body condition = do
  result <- body
  case result of
    Return value -> pure (Return value)
    Break -> pure Next
    _ -> do
      value <- condition
      if truth value then postloop body condition else pure Next

selection :: R Value -> [(Maybe (R Value, R Value), R Flow)] -> R Flow
selection condition entries = do
  value <- number <$> condition
  let search fallback [] = pure fallback
      search fallback remaining@((label, _) : rest) = case label of
        Nothing -> search (Just remaining) rest
        Just (lower, upper) -> do
          lo <- number <$> lower
          hi <- number <$> upper
          if lo <= value && value <= hi then pure (Just remaining) else search fallback rest
  selected <- search Nothing entries
  result <- maybe (pure Next) (chain . map snd) selected
  pure (if result == Break then Next else result)

dispatch :: (Int, [[Int]]) -> [R Flow] -> R Flow
dispatch (entry, edges) actions
  | length edges /= length actions = panic "incomplete control-flow graph"
  | otherwise = go entry
  where
    table = M.fromDistinctAscList (zip [0 ..] (zip (map I.fromList edges) actions))
    go index = case M.lookup index table of
      Nothing -> panic "invalid control-flow target"
      Just (targets, action) -> do
        result <- action
        case result of
          Jump next | I.member next targets -> go next
                    | otherwise -> panic "unlisted control-flow target"
          _ -> pure result

indirectJump :: [(String, Int)] -> R Value -> R Flow
indirectJump targets expression = do
  value <- expression
  case value of
    Function raw name -> do
      canonical <- gets (S.lookup name . symbols)
      case lookup name targets of
        Just target | canonical == Just raw -> pure (Jump target)
        _ -> panic "invalid computed jump target"
    _ -> panic "invalid computed jump target"

logic :: Bool -> R Value -> R Value -> R Value
logic conjunction left right = do
  a <- left
  if truth a == conjunction then boolean . truth <$> right else pure (boolean (not conjunction))

conditional :: R Value -> (Value -> R Value) -> (Value -> R Value) -> R Value -> R Value
conditional common test convertValue fallback = do
  shared <- common
  tested <- test shared
  if truth tested then convertValue shared else fallback

boolean :: Bool -> Value
boolean b = Number (if b then 1 else 0)

calculate :: String -> Int -> Bool -> Integer -> Value -> Value -> Either String Value
calculate op width signed stride a b =
  let x = number a; y = number b
      wrap n = Right (Number (normalise width signed n))
      comparison f = Right (boolean (f x y))
      arithmetic n = if signed && (n < negate (2 ^ (width - 1)) || n >= 2 ^ (width - 1))
        then Left "signed integer overflow" else wrap n
  in case op of
    "+" -> case (a, b) of
      (_, Number _) | addressed a -> Right (offset (y * stride) a)
      (Number _, _) | addressed b -> Right (offset (x * stride) b)
      _ -> arithmetic (x + y)
    "-" -> case (a, b) of
      (_, Number _) | addressed a -> Right (offset (negate y * stride) a)
      _ | addressed a && addressed b -> if stride == 0 then Left "zero pointer stride" else wrap ((x - y) `quot` stride)
      _ -> arithmetic (x - y)
    "*" -> arithmetic (x * y)
    "/" -> if y == 0 then Left "division by zero" else arithmetic (x `quot` y)
    "%" -> if y == 0 then Left "division by zero" else if signed && x == negate (2 ^ (width - 1)) && y == -1 then Left "signed division overflow" else wrap (x `rem` y)
    "&" -> wrap (x .&. y)
    "|" -> wrap (x .|. y)
    "^" -> wrap (xor x y)
    "<<" -> if y < 0 || y >= toInteger width then Left "invalid shift count" else if signed && x < 0 then Left "left shift of a negative integer" else arithmetic (shiftL x (fromInteger y))
    ">>" -> if y < 0 || y >= toInteger width then Left "invalid shift count" else wrap (shiftR x (fromInteger y))
    "==" -> comparison (==)
    "!=" -> comparison (/=)
    "<" -> comparison (<)
    "<=" -> comparison (<=)
    ">" -> comparison (>)
    ">=" -> comparison (>=)
    _ -> Left ("unsupported binary operator " ++ op)

binary :: String -> Int -> Bool -> Integer -> R Value -> R Value -> R Value
binary op width signed stride left right = do
  a <- left
  b <- right
  either panic pure (calculate op width signed stride a b)

unary :: String -> CType -> R Value -> R Value
unary op ty expression = do
  value <- expression
  case op of
    "!" -> pure (boolean (not (truth value)))
    "~" | ComplexType width <- ty ->
      Complex width (complexPart False value) <$> unary "-" (FloatingType width) (pure (complexPart True value))
    "~" -> pure (cast ty (Number (complement (number value))))
    "-" -> case ty of
      IntegerType w s -> either panic pure (calculate "-" w s 1 (Number 0) value)
      FloatingType 32 -> pure (Single (negate (asSingle value)))
      FloatingType 80 -> pure (packExtended (negateExtended (asExtended value)))
      FloatingType _ -> pure (DoublePrecision (negate (asDouble value)))
      ComplexType width ->
        Complex width <$> unary "-" (FloatingType width) (pure (complexPart False value))
                      <*> unary "-" (FloatingType width) (pure (complexPart True value))
      _ -> panic "invalid unary minus"
    "+" -> pure value
    _ -> panic ("unsupported unary operator " ++ op)

assign :: CType -> R Value -> R Value -> R Value
assign ty destination expression = do
  p <- destination
  value <- expression
  store ty p value

update :: String -> CType -> Int -> Bool -> Integer -> Bool -> R Value -> R Value -> R Value
update op ty width signed stride postfix destination expression = do
  pointer <- destination
  old <- load ty pointer
  value <- expression
  result <- either panic pure (calculate op width signed stride old value)
  stored <- store ty pointer result
  pure (if postfix then old else stored)

asSingle :: Value -> Float
asSingle (Single value) = value
asSingle (DoublePrecision value) = double2Float value
asSingle (Extended bits) = fromExtended (unpackExtended bits)
asSingle value = fromInteger (number value)

asDouble :: Value -> Double
asDouble (DoublePrecision value) = value
asDouble (Single value) = float2Double value
asDouble (Extended bits) = fromExtended (unpackExtended bits)
asDouble value = fromInteger (number value)

data ExtendedReal = Finite !Bool !Rational | Infinite !Bool | NotANumber !Integer

unpackExtended :: Integer -> ExtendedReal
unpackExtended raw
  | exponentBits == 32767 =
      if significandBits == bit 63 then Infinite negative else NotANumber raw
  | otherwise = Finite negative (scaleBinary (fromInteger significandBits) (max 1 exponentBits - 16446))
  where
    negative = testBit raw 79
    exponentBits = fromInteger (shiftR raw 64 .&. 32767)
    significandBits = raw .&. (bit 64 - 1)

scaleBinary :: Rational -> Int -> Rational
scaleBinary value power
  | power >= 0 = (shiftL (numerator value) power) % denominator value
  | otherwise = numerator value % (shiftL (denominator value) (negate power))

encodeExtended :: ExtendedReal -> Integer
encodeExtended (NotANumber raw) = normalise 80 False (raw .|. shiftL 32767 64 .|. bit 63 .|. bit 62)
encodeExtended (Infinite negative) = (if negative then bit 79 else 0) .|. shiftL 32767 64 .|. bit 63
encodeExtended (Finite negative magnitude)
  | magnitude == 0 = sign
  | finalExponent > 16383 = encodeExtended (Infinite negative)
  | otherwise = sign .|. shiftL expBits 64 .|. finalSignificand
  where
    sign = if negative then bit 79 else 0
    logarithm value = I# (integerLog2# value)
    guess = logarithm (numerator magnitude) - logarithm (denominator magnitude)
    binaryExponent = if scaleBinary magnitude (negate guess) < 1 then guess - 1 else guess
    roundedExponent = max (-16382) binaryExponent
    rounded = round (scaleBinary magnitude (63 - roundedExponent)) :: Integer
    carry = rounded == bit 64
    finalExponent = if carry then roundedExponent + 1 else roundedExponent
    finalSignificand = if carry then bit 63 else rounded
    expBits = if finalSignificand < bit 63 then 0 else toInteger (finalExponent + 16383)

packExtended :: ExtendedReal -> Value
packExtended = Extended . encodeExtended

extendedLiteral :: Rational -> Value
extendedLiteral value = packExtended (Finite (value < 0) (abs value))

hostExtended :: Double -> ExtendedReal
hostExtended value
  | isNaN value = NotANumber (sign .|. shiftL (toInteger (castDoubleToWord64 value .&. (bit 52 - 1))) 11)
  | isInfinite value = Infinite negative
  | otherwise = Finite negative (toRational (abs value))
  where
    negative = testBit (castDoubleToWord64 value) 63
    sign = if negative then bit 79 else 0

asExtended :: Value -> ExtendedReal
asExtended (Extended bits) = unpackExtended bits
asExtended (Single value) = hostExtended (float2Double value)
asExtended (DoublePrecision value) = hostExtended value
asExtended value = let integer = number value in Finite (integer < 0) (fromInteger (abs integer))

fromExtended :: RealFloat a => ExtendedReal -> a
fromExtended (Finite negative magnitude) = if negative then negate (fromRational magnitude) else fromRational magnitude
fromExtended (Infinite negative) = if negative then -1 / 0 else 1 / 0
fromExtended (NotANumber _) = 0 / 0

negateExtended :: ExtendedReal -> ExtendedReal
negateExtended (Finite negative magnitude) = Finite (not negative) magnitude
negateExtended (Infinite negative) = Infinite (not negative)
negateExtended (NotANumber raw) = NotANumber (xor raw (bit 79))

invalidExtended :: ExtendedReal
invalidExtended = NotANumber (bit 79)

extendedAdd :: ExtendedReal -> ExtendedReal -> ExtendedReal
extendedAdd left@(NotANumber _) _ = left
extendedAdd _ right@(NotANumber _) = right
extendedAdd left@(Infinite negative) (Infinite other) = if negative == other then left else invalidExtended
extendedAdd left@(Infinite _) _ = left
extendedAdd _ right@(Infinite _) = right
extendedAdd (Finite negative left) (Finite other right) =
  let signed isNegative value = if isNegative then negate value else value
      result = signed negative left + signed other right
      sign = result < 0 || (left == 0 && right == 0 && negative && other)
  in Finite sign (abs result)

extendedScale :: Bool -> ExtendedReal -> ExtendedReal -> ExtendedReal
extendedScale _ left@(NotANumber _) _ = left
extendedScale _ _ right@(NotANumber _) = right
extendedScale divide (Infinite a) (Infinite b) = if divide then invalidExtended else Infinite (a /= b)
extendedScale divide (Finite a left) (Infinite b)
  | divide = Finite (a /= b) 0
  | left == 0 = invalidExtended
  | otherwise = Infinite (a /= b)
extendedScale divide (Infinite a) (Finite b right)
  | not divide && right == 0 = invalidExtended
  | otherwise = Infinite (a /= b)
extendedScale divide (Finite a left) (Finite b right)
  | divide && right == 0 = if left == 0 then invalidExtended else Infinite (a /= b)
  | divide = Finite (a /= b) (left / right)
  | otherwise = Finite (a /= b) (left * right)

extendedCompare :: ExtendedReal -> ExtendedReal -> Maybe Ordering
extendedCompare (NotANumber _) _ = Nothing
extendedCompare _ (NotANumber _) = Nothing
extendedCompare (Infinite a) (Infinite b) = Just (compare b a)
extendedCompare (Infinite negative) _ = Just (if negative then LT else GT)
extendedCompare _ (Infinite negative) = Just (if negative then GT else LT)
extendedCompare (Finite a left) (Finite b right) =
  Just (compare (if a then negate left else left) (if b then negate right else right))

extendedOperation :: String -> ExtendedReal -> ExtendedReal -> R Value
extendedOperation op left right = case op of
  "+" -> pure (packExtended (extendedAdd left right))
  "-" -> pure (packExtended (extendedAdd left (negateExtended right)))
  "*" -> pure (packExtended (extendedScale False left right))
  "/" -> pure (packExtended (extendedScale True left right))
  "==" -> pure (boolean (comparison == Just EQ))
  "!=" -> pure (boolean (comparison /= Just EQ))
  "<" -> pure (boolean (comparison == Just LT))
  "<=" -> pure (boolean (comparison `elem` [Just LT, Just EQ]))
  ">" -> pure (boolean (comparison == Just GT))
  ">=" -> pure (boolean (comparison `elem` [Just GT, Just EQ]))
  _ -> panic ("unsupported extended floating operator " ++ op)
  where comparison = extendedCompare left right

realOperation :: (Ord a, Fractional a) => String -> (a -> Value) -> a -> a -> R Value
realOperation op wrap left right = case op of
  "+" -> pure (wrap (left + right))
  "-" -> pure (wrap (left - right))
  "*" -> pure (wrap (left * right))
  "/" -> pure (wrap (left / right))
  "==" -> pure (boolean (left == right))
  "!=" -> pure (boolean (left /= right))
  "<" -> pure (boolean (left < right))
  "<=" -> pure (boolean (left <= right))
  ">" -> pure (boolean (left > right))
  ">=" -> pure (boolean (left >= right))
  _ -> panic ("unsupported floating operator " ++ op)

realBinary :: String -> Int -> R Value -> R Value -> R Value
realBinary op width left right = do
  a <- left
  b <- right
  case width of
    32 -> realOperation op Single (asSingle a) (asSingle b)
    80 -> extendedOperation op (asExtended a) (asExtended b)
    _ -> realOperation op DoublePrecision (asDouble a) (asDouble b)

realUpdate :: String -> Int -> CType -> Bool -> R Value -> R Value -> R Value
realUpdate op width ty postfix destination expression = do
  pointer <- destination
  old <- load ty pointer
  result <- realBinary op width (pure old) expression >>= convert ty
  stored <- store ty pointer result
  pure (if postfix then old else stored)

complexPart :: Bool -> Value -> Value
complexPart imag (Complex _ real imaginaryPart) = if imag then imaginaryPart else real
complexPart imag value = if imag then Number 0 else value

imaginary :: CType -> R Value -> R Value
imaginary (ComplexType width) expression =
  Complex width (cast (FloatingType width) (Number 0)) <$> expression
imaginary _ _ = panic "imaginary literal requires complex type"

makeComplex :: CType -> R Value -> R Value -> R Value
makeComplex (ComplexType width) real imag = Complex width <$> real <*> imag
makeComplex _ _ _ = panic "complex construction requires complex type"

complexBinary :: String -> Int -> R Value -> R Value -> R Value
complexBinary op width left right = do
  a <- left
  b <- right
  let ar = complexPart False a
      ai = complexPart True a
      br = complexPart False b
      bi = complexPart True b
      scalar (Complex _ _ _) = False
      scalar _ = True
      real operation x y = realBinary operation width (pure x) (pure y)
      pair = Complex width
      neg x = unary "-" (FloatingType width) (pure x)
      comparePair equal = do
        sameReal <- real "==" ar br
        sameImag <- real "==" ai bi
        pure (boolean ((truth sameReal && truth sameImag) == equal))
      isNan value = case asExtended value of NotANumber _ -> True; _ -> False
      infinite value = case asExtended value of Infinite _ -> True; _ -> False
      finite value = case asExtended value of Finite _ _ -> True; _ -> False
      sign value = case asExtended value of
        Finite negative _ -> negative
        Infinite negative -> negative
        NotANumber raw -> testBit raw 79
      typed = convert (FloatingType width) . packExtended
      signOf magnitude value = typed (Finite (sign value) magnitude)
      unit value = signOf (if infinite value then 1 else 0) value
      dropNan value = if isNan value then signOf 0 value else pure value
      productPair x y u v = do
        ac <- real "*" x u
        bd <- real "*" y v
        ad <- real "*" x v
        bc <- real "*" y u
        (,) <$> real "-" ac bd <*> real "+" ad bc
      scaledPair factor (x, y) = do
        r <- real "*" factor x
        i <- real "*" factor y
        pure (pair r i)
      multiply = do
        result@(r, i) <- productPair ar ai br bi
        if not (isNan r && isNan i) then pure (uncurry pair result) else do
          let leftInf = any infinite [ar, ai]
              rightInf = any infinite [br, bi]
          ac <- real "*" ar br
          bd <- real "*" ai bi
          ad <- real "*" ar bi
          bc <- real "*" ai br
          if not (leftInf || rightInf || any infinite [ac, bd, ad, bc]) then pure (uncurry pair result) else do
            x <- (if leftInf then unit else dropNan) ar
            y <- (if leftInf then unit else dropNan) ai
            u <- (if rightInf then unit else dropNan) br
            v <- (if rightInf then unit else dropNan) bi
            factor <- typed (Infinite False)
            productPair x y u v >>= scaledPair factor
      scale power value = case asExtended value of
        Finite negative magnitude -> typed (Finite negative (scaleBinary magnitude power))
        _ -> pure value
      divide = do
        let largest = maximum (0 : [m | Finite _ m <- map asExtended [br, bi]])
            logarithm value = I# (integerLog2# value)
            guess = logarithm (numerator largest) - logarithm (denominator largest)
            power
              | largest == 0 || any infinite [br, bi] = 0
              | scaleBinary largest (negate guess) < 1 = guess - 1
              | otherwise = guess
        c <- scale (negate power) br
        d <- scale (negate power) bi
        cc <- real "*" c c
        dd <- real "*" d d
        denominatorValue <- real "+" cc dd
        numeratorValues <- productPair ar ai c =<< neg d
        r <- real "/" (fst numeratorValues) denominatorValue >>= scale (negate power)
        i <- real "/" (snd numeratorValues) denominatorValue >>= scale (negate power)
        if not (isNan r && isNan i) then pure (pair r i)
        else if not (truth denominatorValue) && not (isNan ar && isNan ai) then do
          factor <- typed (Infinite (sign br))
          scaledPair factor (ar, ai)
        else if any infinite [ar, ai] && all finite [c, d] then do
          x <- unit ar
          y <- unit ai
          factor <- typed (Infinite False)
          (neg d >>= productPair x y c) >>= scaledPair factor
        else if any infinite [br, bi] && all finite [ar, ai] then do
          cUnit <- unit br
          dUnit <- unit bi
          factor <- typed (Finite False 0)
          (neg dUnit >>= productPair ar ai cUnit) >>= scaledPair factor
        else pure (pair r i)
  case op of
    "==" -> comparePair True
    "!=" -> comparePair False
    "+" -> pair <$> real "+" ar br <*> (if scalar a then pure bi else if scalar b then pure ai else real "+" ai bi)
    "-" -> pair <$> real "-" ar br <*> (if scalar a then neg bi else if scalar b then pure ai else real "-" ai bi)
    "*" | scalar a -> pair <$> real "*" ar br <*> real "*" ar bi
        | scalar b -> pair <$> real "*" ar br <*> real "*" ai br
        | otherwise -> multiply
    "/" | scalar b -> pair <$> real "/" ar br <*> real "/" ai br
        | otherwise -> divide
    _ -> panic ("unsupported complex operator " ++ op)

complexUpdate :: String -> Int -> CType -> Bool -> R Value -> R Value -> R Value
complexUpdate op width ty postfix destination expression = do
  pointer <- destination
  old <- load ty pointer
  result <- complexBinary op width (pure old) expression >>= convert ty
  stored <- store ty pointer result
  pure (if postfix then old else stored)

atomicAccess :: String -> CType -> R Value -> [R Value] -> R Value
atomicAccess op ty target operands = do
  pointer <- target
  values <- sequence operands
  case (op, values) of
    ("load", [_]) -> load ty pointer
    ("init", [value]) -> locked $ do
      let ordinary = plainType ty
          size = widthOf ordinary
          padding = widthOf ty - size
      void (storeCell ordinary pointer value)
      when (padding > 0) (void (storeCell (IntegerType (8 * padding) False) (offset (toInteger size) pointer) (Number 0)))
      pure (Number 0)
    ("store", [_, value]) -> store ty pointer value >> pure (Number 0)
    ("exchange", [_, value]) -> locked $ do
      old <- loadCell ty pointer
      void (storeCell ty pointer value)
      pure old
    _ -> panic "invalid atomic operands"

plainType :: CType -> CType
plainType (AtomicType ty) = ty
plainType (AtomicAggregate _ ty _) = ty
plainType ty = ty

atomicTransfer :: String -> CType -> R Value -> [R Value] -> R Value
atomicTransfer op ty target operands = do
  pointer <- target
  values <- sequence operands
  let ordinary = plainType ty
  locked $ do
    _ <- case (op, values) of
      ("load", [_, destination]) -> loadCell ty pointer >>= storeCell ordinary destination
      ("store", [_, source]) -> loadCell ordinary source >>= storeCell ty pointer
      ("exchange", [_, source, destination]) -> do
        desired <- loadCell ordinary source
        old <- loadCell ty pointer
        void (storeCell ty pointer desired)
        storeCell ordinary destination old
      _ -> panic "invalid atomic transfer operands"
    pure (Number 0)

atomicModify :: String -> CType -> Integer -> Bool -> R Value -> R Value -> R Value -> R Value
atomicModify op ty stride oldResult target ordering expression = do
  pointer <- target
  void ordering
  value <- expression
  locked $ do
    old <- loadCell (AtomicType ty) pointer
    result <- case ty of
      IntegerType width _ -> either panic pure (calculate op width False stride old value)
      PointerType -> either panic pure (calculate op 64 False stride old value)
      FloatingType width -> realBinary op width (pure old) (pure value)
      _ -> panic "unsupported atomic update type"
    stored <- storeCell (AtomicType ty) pointer result
    pure (if oldResult then old else stored)

atomicPointerStep :: String -> Integer -> Bool -> R Value -> R Value -> R Value -> R Value
atomicPointerStep op stride oldResult target ordering expression = do
  pointer <- target
  void ordering
  amount <- expression
  locked $ do
    let ty = IntegerType 64 False
    old <- loadCell ty pointer
    result <- either panic pure (calculate op 64 False 1 old (Number (number amount * stride)))
    void (storeCell ty pointer result)
    pure (cast PointerType (if oldResult then old else result))

asmBarrier :: R Flow
asmBarrier = locked (pure Next)

carryBit :: Maybe Bool -> R Integer
carryBit Nothing = panic "assembly reads an undefined carry flag"
carryBit (Just carry) = pure (if carry then 1 else 0)

asmArithmetic :: String -> Int -> Integer -> Integer -> Maybe Bool -> R (Integer, Maybe Bool)
asmArithmetic op width left right carry =
  let addition amount = let result = left + right + amount in (result, Just (result >= bit width))
      subtraction amount = let result = left - right - amount in (result, Just (result < 0))
      count = fromInteger (right .&. if width == 64 then 63 else 31)
      rotation = count `mod` width
      shifted result bitIndex defined =
        if count == 0 then (left, carry) else (result, if defined then Just (testBit left bitIndex) else Nothing)
      rotated result bitIndex = if count == 0 then (left, carry) else (result, Just (testBit result bitIndex))
  in case op of
    "+" -> pure (addition 0)
    "-" -> pure (subtraction 0)
    "adc" -> addition <$> carryBit carry
    "sbb" -> subtraction <$> carryBit carry
    "cmp" -> pure (left, Just (left < right))
    "inc" -> pure (left + 1, carry)
    "dec" -> pure (left - 1, carry)
    "neg" -> pure (negate left, Just (left /= 0))
    "not" -> pure (complement left, carry)
    "&" -> pure (left .&. right, Just False)
    "|" -> pure (left .|. right, Just False)
    "^" -> pure (xor left right, Just False)
    "shl" -> pure (shifted (shiftL left count) (width - count) (count < width))
    "shr" -> pure (shifted (shiftR left count) (count - 1) (count < width))
    "sar" -> pure (shifted (shiftR (normalise width True left) count) (min (width - 1) (count - 1)) True)
    "rol" -> pure (rotated (shiftL left rotation .|. shiftR left (width - rotation)) 0)
    "ror" -> pure (rotated (shiftR left rotation .|. shiftL left (width - rotation)) (width - 1))
    _ -> panic ("unknown assembly operation " ++ op)

asmRegisters :: [(CType, Bool, R Value)] -> [(Int, R Value)] ->
  [(String, Int, Int, Either Int Integer)] -> R Flow
asmRegisters outputs inputs instructions = do
  destinations <- mapM (\(ty, readWrite, action) -> (,,) ty readWrite <$> action) outputs
  arguments <- mapM (\(reg, action) -> (,) reg <$> action) inputs
  locked $ do
    initial <- forM (zip [0..] destinations) $ \(reg, (ty, readWrite, destination)) -> do
      value <- if readWrite then loadCell ty destination else pure NoValue
      pure (reg, value)
    let getRegister registers reg =
          case M.lookup reg registers of
            Just value | value /= NoValue -> pure value
            _ -> panic "assembly reads an uninitialised register"
        evaluate (registers, carry) (op, width, destination, source) =
          case op of
            "clc" -> pure (registers, Just False)
            "stc" -> pure (registers, Just True)
            "cmc" -> do
              old <- carryBit carry
              pure (registers, Just (old == 0))
            _ -> do
              let word = normalise width False . number
              operand <- either (getRegister registers) (pure . Number) source
              (result, flag) <- case op of
                "mov" -> pure (word operand, carry)
                "setc" -> (\value -> (value, carry)) <$> carryBit carry
                _ -> do
                  left <- word <$> getRegister registers destination
                  asmArithmetic op width left (word operand) carry
              pure (M.insert destination (Number (normalise width False result)) registers, flag)
    (result, _) <- foldM evaluate (M.fromList (initial ++ arguments), Nothing) instructions
    forM_ (zip [0..] destinations) $ \(reg, (ty, _, destination)) ->
      getRegister result reg >>= void . storeCell ty destination
    pure Next

atomicCompare :: Bool -> CType -> R Value -> R Value -> R Value -> R Value -> R Value -> R Value
atomicCompare indirect ty target successOrder expected failureOrder desired = do
  pointer <- target
  void successOrder
  expectation <- expected
  void failureOrder
  desiredValue <- desired
  locked $ do
    let ordinary = plainType ty
        bits value = case value of Aggregate _ _ payload _ -> decodeBytes payload; _ -> number value
    replacement <- if indirect then loadCell ordinary desiredValue else pure desiredValue
    old <- loadCell ty pointer
    wanted <- loadCell ordinary expectation
    (_, object, _) <- checked (widthOf ty) pointer
    when (readOnly object) (panic "write to read-only memory")
    matches <- case (ty, old, wanted) of
      (AtomicAggregate _ _ AtomicCopy, Aggregate _ _ actual _, Aggregate _ _ expectedBytes _) ->
        pure (M.filter (/= 0) actual == M.filter (/= 0) expectedBytes)
      (AtomicAggregate width _ AtomicBytes, _, _) | width /= widthOf ordinary -> do
        observed <- loadCell (IntegerType (8 * width) False) pointer
        pure (number observed == bits wanted)
      _ -> pure (bits old == bits wanted)
    if matches then storeCell ty pointer replacement >> pure (boolean True) else do
      case ty of
        AtomicAggregate width _ AtomicBytes ->
          when (width == widthOf ordinary) $
            void (storeCell (IntegerType (8 * width) False) expectation (Number (bits old)))
        _ -> void (storeCell ordinary expectation old)
      pure (boolean False)

function :: String -> R Value
function name = do
  ident <- gets (S.lookup name . symbols)
  maybe (panic ("unknown function " ++ name)) (\code -> pure (Function code name)) ident

pthreadArities :: [(String, Int)]
pthreadArities =
  [ ("pthread_create", 4), ("pthread_join", 2), ("pthread_self", 0), ("pthread_equal", 2)
  , ("pthread_mutex_init", 2), ("pthread_mutex_destroy", 1), ("pthread_mutex_lock", 1)
  , ("pthread_mutex_trylock", 1), ("pthread_mutex_unlock", 1)
  , ("pthread_cond_init", 2), ("pthread_cond_destroy", 1), ("pthread_cond_wait", 2)
  , ("pthread_cond_signal", 1), ("pthread_cond_broadcast", 1)
  ]

invoke :: Maybe CType -> R Value -> [R Value] -> R Value
invoke expected callee arguments = do
  target <- callee
  values <- sequence arguments
  result <- case target of
    Function raw name -> do
      canonical <- gets (S.lookup name . symbols)
      unless (canonical == Just raw) (panic "call through an invalid function pointer")
      defined <- gets (S.lookup name . functions)
      case defined of
        Just action -> action values
        Nothing -> do
          let arities = [("malloc",1),("calloc",2),("free",1),("memcpy",3),("memmove",3),("memset",3),("strlen",1),("strcmp",2),
                ("puts",1),("putchar",1),("vprintf",2),("exit",1),("fopen",2),("fclose",1),("fread",4),("fwrite",4),
                ("zhasvalidcap",1),("zis_readonly",1),("zgetlower",1),("zgetupper",1)] ++ pthreadArities
              accepted = maybe values (`take` values) (lookup name arities)
          value <- builtin name accepted
          let resultType
                | name `elem` ["free", "exit"] = Nothing
                | name `elem` ["malloc", "calloc", "memcpy", "memmove", "memset", "fopen", "zgetlower", "zgetupper", "pthread_self"] = Just PointerType
                | name `elem` ["strlen", "fread", "fwrite"] = Just (IntegerType 64 False)
                | name `elem` ["zhasvalidcap", "zis_readonly"] = Just (IntegerType 8 False)
                | otherwise = Just (IntegerType 32 True)
          pure (maybe NoValue (\ty -> marshal ty value) resultType)
    _ -> panic "call through an invalid function pointer"
  case (expected, result) of
    (Nothing, _) -> pure (Number 0)
    (Just _, NoValue) -> panic "callee returned no value to a non-void callsite"
    (Just (AggregateType size _), Aggregate actual _ _ _) | size == actual -> pure result
    (Just (AggregateType _ _), _) -> panic "callee returned an incompatible aggregate value"
    (Just _, Aggregate _ _ _ _) -> panic "callee returned an aggregate to a scalar callsite"
    (Just ty, value) -> pure (cast ty value)

decimalField :: String -> R Int
decimalField = foldM step 0
  where
    step n c = do
      let digit = digitToInt c
      if n > (maxBound - digit) `div` 10 then panic "printf field exceeds the host representation"
        else pure (n * 10 + digit)

fixedDecimal :: Int -> Double -> String
fixedDecimal precision = fixedExtended precision . hostExtended

fixedExtended :: Int -> ExtendedReal -> String
fixedExtended _ (Infinite negative) = if negative then "-inf" else "inf"
fixedExtended _ (NotANumber raw) = if testBit raw 79 then "-nan" else "nan"
fixedExtended precision (Finite negative value)
  | precision == 0 = sign ++ digits
  | otherwise = sign ++ integer ++ "." ++ fractional
  where
    sign = if negative then "-" else ""
    scale = 10 ^ precision :: Integer
    digits = show (round (value * fromInteger scale) :: Integer)
    padded = replicate (max 0 (precision - length digits + 1)) '0' ++ digits
    (integer, fractional) = splitAt (length padded - precision) padded

format :: (CType -> arguments -> R (Value, arguments)) -> String -> arguments -> R String
format _ [] _ = pure []
format takeArgument ('%' : '%' : rest) values = ('%' :) <$> format takeArgument rest values
format takeArgument ('%' : rest) values = do
  let (digits, following) = span isDigit rest
      (fraction, remainingFormat) = case following of
        '.' : afterDot -> let (places, remaining) = span isDigit afterDot in (Just places, remaining)
        _ -> (Nothing, following)
      (modifier, suffix) = span (`elem` "lhzL") remainingFormat
      bits = case modifier of "hh" -> 8; "h" -> 16; "l" -> 64; "ll" -> 64; "z" -> 64; _ -> 32
  unless (modifier `elem` ["", "h", "hh", "l", "ll", "z", "L"]) (panic "invalid printf length modifier")
  width <- decimalField digits
  case suffix of
    specifier : more -> do
      when (fraction /= Nothing && specifier /= 'f') (panic "unsupported printf precision")
      let ty = case specifier of
            's' -> PointerType
            'f' -> FloatingType (if modifier == "L" then 80 else 64)
            _ -> IntegerType (max 32 bits) False
      (value, remaining) <- takeArgument ty values
      let real = castWord64ToDouble (fromInteger (number value))
          extended = unpackExtended (number value)
          finite = if modifier == "L" then case extended of Finite _ _ -> True; _ -> False
                   else not (isNaN real || isInfinite real)
      piece <- case specifier of
        'd' -> pure (show (normalise bits True (number value)))
        'i' -> pure (show (normalise bits True (number value)))
        'u' -> pure (show (normalise bits False (number value)))
        'x' -> pure (showHex (normalise bits False (number value)) "")
        'X' -> pure (map toUpper (showHex (normalise bits False (number value)) ""))
        'o' -> pure (showOct (normalise bits False (number value)) "")
        'c' -> pure [chr (fromInteger (number value `mod` 256))]
        's' -> readString value
        'f' -> do
          unless (modifier `elem` ["", "l", "L"]) (panic "unsupported floating printf length")
          precision <- maybe (pure 6) decimalField fraction
          pure (if modifier == "L" then fixedExtended precision extended else fixedDecimal precision real)
        _ -> panic ("unsupported printf conversion %" ++ [specifier])
      let zero = take 1 digits == "0" && specifier `elem` "diuxXof" &&
            (specifier /= 'f' || finite)
          padding = replicate (max 0 (width - length piece)) (if zero then '0' else ' ')
          padded = if zero && take 1 piece == "-" then "-" ++ padding ++ drop 1 piece else padding ++ piece
      remainingText <- format takeArgument more remaining
      pure (padded ++ remainingText)
    _ -> panic "invalid printf argument list"
format takeArgument (c : rest) values = (c :) <$> format takeArgument rest values

takeValue :: CType -> [Value] -> R (Value, [Value])
takeValue _ (value : rest) = pure (value, rest)
takeValue _ [] = panic "invalid printf argument list"

takeVariadic :: CType -> Value -> R (Value, Value)
takeVariadic ty cursor = do
  value <- vaArg ty (pure cursor)
  pure (value, cursor)

printBytes :: String -> R Value
printBytes text = do
  liftIO (B.putStr (B.pack text))
  pure (Number (toInteger (length text)))

copyMemory :: Value -> Value -> Int -> R Value
copyMemory destination _ 0 = pure destination
copyMemory destination source count = locked $ do
  when (count < 0) (panic "invalid memory copy length")
  (_, src, srcOffset) <- checked count source
  (ident, dst, dstOffset) <- checked count destination
  when (readOnly dst) (panic "write to read-only memory")
  let end = dstOffset + count
      payload = M.mapKeysMonotonic (+ dstOffset) (aggregateBytes srcOffset count (bytes src))
      untouchedBytes = M.union (M.takeWhileAntitone (< dstOffset) (bytes dst)) (M.dropWhileAntitone (< end) (bytes dst))
      aligned = srcOffset `mod` 8 == dstOffset `mod` 8
      caps = if aligned then M.mapKeysMonotonic (+ dstOffset) (aggregateShadow srcOffset count (shadow src)) else M.empty
      outside slot = slot <= dstOffset - 8 || slot >= end
  writeObject ident (dst { bytes = M.union payload untouchedBytes
                         , shadow = M.union caps (M.filterWithKey (\slot _ -> outside slot) (shadow dst))
                         , atomicSlots = I.filter outside (atomicSlots dst) })
  event ("copy " ++ show count ++ " bytes to #" ++ show ident ++ "+" ++ show dstOffset)
  pure destination

io :: IO a -> R a
io action = liftIO (tryIOError action) >>= either (panic . ("file I/O: " ++) . ioeGetErrorString) pure

stream :: Value -> R Handle
stream (Stream ident raw) = do
  unless (raw == 4611686018427387904 + toInteger ident) (panic "closed or invalid file stream")
  table <- gets streamTable >>= liftIO . readIORef
  let handle = M.lookup ident (snd table)
  maybe (panic "closed or invalid file stream") pure handle
stream _ = panic "file operation requires a valid stream"

transferSize :: Value -> Value -> R Int
transferSize size count = do
  hostSize (number size * number count)

hostSize :: Integer -> R Int
hostSize count = do
  when (count < 0 || count > toInteger (maxBound :: Int)) (panic "size exceeds the host representation")
  pure (fromInteger count)

builtin :: String -> [Value] -> R Value
builtin "fopen" [path, mode] = do
  raw <- readString path
  name <- io $ do
    encoding <- getFileSystemEncoding
    B.useAsCString (B.pack raw) (F.peekCString encoding)
  access <- readString mode
  selected <- case access of
    "rb" -> pure ReadMode
    "wb" -> pure WriteMode
    _ -> panic "fopen supports rb and wb modes"
  table <- gets streamTable
  opened <- liftIO (tryIOError (openBinaryFile name selected))
  case opened of
    Left _ -> pure nullPointer
    Right handle -> do
      entry <- liftIO $ atomicModifyIORef' table $ \old@(ident, entries) ->
        if toInteger ident >= 4611686018427387904 then (old, Nothing)
        else ((ident + 1, M.insert ident handle entries), Just ident)
      ident <- case entry of
        Nothing -> io (hClose handle) >> panic "stream identity space exhausted"
        Just available -> pure available
      pure (Stream ident (4611686018427387904 + toInteger ident))
builtin "fclose" [value@(Stream ident _)] = do
  handle <- stream value
  io (hClose handle)
  table <- gets streamTable
  liftIO $ atomicModifyIORef' table $ \(next, entries) -> ((next, M.delete ident entries), ())
  pure (Number 0)
builtin "fread" [destination, size, count, value] = do
  total <- transferSize size count
  handle <- stream value
  if total == 0 then pure (Number 0) else do
    (_, object, _) <- checked total destination
    when (readOnly object) (panic "file read into read-only memory")
    payload <- io (B.hGet handle total)
    locked $ do
      (ident, updatedObject, displacement) <- checked total destination
      when (readOnly updatedObject) (panic "file read into read-only memory")
      let updated = B.foldl' (\(i, m) byte -> (i + 1, M.insert i (toInteger (ord byte)) m)) (displacement, bytes updatedObject) payload
      writeObject ident (updatedObject { bytes = snd updated })
      event ("read " ++ show (B.length payload) ++ " bytes into #" ++ show ident)
    pure (Number (toInteger (B.length payload) `div` number size))
builtin "fwrite" [source, size, count, value] = do
  total <- transferSize size count
  handle <- stream value
  if total == 0 then pure (Number 0) else do
    (_, object, displacement) <- checked total source
    let payload = B.pack [chr (fromInteger (M.findWithDefault 0 (displacement + i) (bytes object))) | i <- [0 .. total - 1]]
    io (B.hPut handle payload)
    event ("write " ++ show total ++ " bytes")
    pure count
builtin "malloc" [size] = hostSize (number size) >>= allocate "heap"
builtin "calloc" [n, size] = hostSize (number n * number size) >>= allocate "heap"
builtin "free" [p] = release p >> pure (Number 0)
builtin "memcpy" [destination, source, count] = hostSize (number count) >>= copyMemory destination source
builtin "memmove" [destination, source, count] = hostSize (number count) >>= copyMemory destination source
builtin "memset" [destination, value, count] = do
  n <- hostSize (number count)
  when (n /= 0) (void (checked n destination))
  forM_ [0 .. n - 1] $ \i -> void (store (IntegerType 8 False) (offset (toInteger i) destination) value)
  pure destination
builtin "strlen" [p] = Number . toInteger . length <$> readString p
builtin "strcmp" [a, b] = do
  x <- readString a
  y <- readString b
  pure (Number (case compare x y of LT -> -1; EQ -> 0; GT -> 1))
builtin "zhasvalidcap" [Pointer NoCapability _] = pure (boolean False)
builtin "zhasvalidcap" [Pointer capability _] = boolean . live <$> readObject capability
builtin "zhasvalidcap" [Function _ _] = pure (boolean True)
builtin "zhasvalidcap" [Stream ident _] = do
  table <- gets streamTable >>= liftIO . readIORef
  pure (boolean (M.member ident (snd table)))
builtin "zhasvalidcap" [_] = pure (boolean False)
builtin "zis_readonly" [Pointer NoCapability _] = pure (boolean False)
builtin "zis_readonly" [Pointer capability _] = boolean . readOnly <$> readObject capability
builtin "zis_readonly" [_] = pure (boolean False)
builtin name [Pointer capability _] | name == "zgetlower" || name == "zgetupper" =
  case capability of
    NoCapability -> pure nullPointer
    _ -> do
      object <- readObject capability
      pure (Pointer capability (base object + if name == "zgetupper" && live object then toInteger (extent object) else 0))
builtin "puts" [p] = do
  text <- readString p
  liftIO (B.putStr (B.pack (text ++ "\n")))
  pure (Number 0)
builtin "putchar" [v] = do
  let byte = number v `mod` 256
  liftIO (B.putStr (B.singleton (chr (fromInteger byte))))
  pure (Number byte)
builtin "printf" (p : values) = readString p >>= \pattern -> format takeValue pattern values >>= printBytes
builtin "vprintf" [p, list] = readString p >>= \pattern -> format takeVariadic pattern list >>= printBytes
builtin "pthread_create" [destination, attributes, callable, argumentValue] = do
  when (truth attributes) (panic "unsupported pthread attributes")
  unless (case callable of Function _ _ -> True; _ -> False) (panic "invalid thread start function")
  childHandle <- allocate "thread" 0
  void (store PointerType destination childHandle)
  cell <- liftIO newEmptyMVar
  world <- get
  let ident = number childHandle
      child = world { frames = [], currentThread = childHandle, events = 0, recent = [] }
  liftIO $ E.mask_ $ do
    modifyMVar_ (threadTable world) (pure . S.insert ident cell)
    void $ forkIOWithUnmask (\unmask -> unmask (worker child cell callable argumentValue))
  pure (Number 0)
builtin "pthread_join" [thread, result] = do
  world <- get
  valid <- case thread of
    Pointer capability@(Capability _ _) raw -> do
      object <- readObject capability
      pure (live object && storage object == "thread" && raw == base object)
    _ -> pure False
  if not valid then pure (Number 3)
  else if thread == currentThread world then pure (Number 35) else do
    let ident = number thread
    entry <- liftIO $ modifyMVar (threadTable world) $ \table -> pure (S.delete ident table, S.lookup ident table)
    case entry of
      Nothing -> pure (Number 3)
      Just cell -> do
        value <- liftIO (takeMVar cell)
        when (truth result) (void (store PointerType result value))
        pure (Number 0)
builtin "pthread_self" [] = gets currentThread
builtin "pthread_equal" [a, b] = pure (boolean (number a == number b))
builtin "pthread_mutex_init" [pointer, attributes] = initialiseSync mutexWidth pointer attributes emptyMutex
builtin "pthread_mutex_destroy" [pointer] = destroySync mutexWidth pointer emptyMutex
builtin "pthread_mutex_lock" [pointer] = acquireMutex False pointer
builtin "pthread_mutex_trylock" [pointer] = acquireMutex True pointer
builtin "pthread_mutex_unlock" [pointer] = do
  result <- locked (releaseMutex pointer)
  finishRelease result
builtin "pthread_cond_init" [pointer, attributes] = initialiseSync conditionWidth pointer attributes emptyCondition
builtin "pthread_cond_destroy" [pointer] = destroySync conditionWidth pointer emptyCondition
builtin "pthread_cond_wait" [condition, mutex] = waitCondition condition mutex
builtin "pthread_cond_signal" [pointer] = notifyCondition False pointer
builtin "pthread_cond_broadcast" [pointer] = notifyCondition True pointer
builtin "exit" [code] = throwError (Finish (fromInteger (number code `mod` 256)))
builtin name _ = panic ("unsupported external call " ++ name)

mutexWidth, conditionWidth :: Int
mutexWidth = 32
conditionWidth = 48

emptyMutex, emptyCondition :: Synchronisation
emptyMutex = Mutex Nothing Q.empty
emptyCondition = Condition Q.empty

changeSync :: Int -> Value -> Synchronisation -> (Synchronisation -> R (Synchronisation, a)) -> R a
changeSync width pointer initial change = do
  (ident, object, displacement) <- checked width pointer
  when (number pointer `mod` 8 /= 0) (panic "unaligned pthread object")
  when (readOnly object) (panic "pthread operation on read-only memory")
  let cell = M.findWithDefault initial displacement (synchronisation object)
  (updated, value) <- change cell
  current <- readObject ident
  writeObject ident (current { synchronisation = M.insert displacement updated (synchronisation current) })
  pure value

initialiseSync :: Int -> Value -> Value -> Synchronisation -> R Value
initialiseSync width pointer attributes initial = do
  when (truth attributes) (panic "unsupported pthread synchronisation attributes")
  locked (changeSync width pointer initial (\_ -> pure (initial, Number 0)))

destroySync :: Int -> Value -> Synchronisation -> R Value
destroySync width pointer initial = locked $ changeSync width pointer initial $ \cell ->
  case cell of
    Mutex Nothing waiters | Q.null waiters -> pure (Destroyed, Number 0)
    Condition waiters | Q.null waiters -> pure (Destroyed, Number 0)
    Destroyed -> pure (cell, Number 22)
    _ -> pure (cell, Number 16)

acquireMutex :: Bool -> Value -> R Value
acquireMutex tryOnly pointer = do
  caller <- gets (number . currentThread)
  waiter <- liftIO newEmptyMVar
  result <- locked $ changeSync mutexWidth pointer emptyMutex $ \cell ->
    case cell of
      Mutex Nothing waiting -> pure (Mutex (Just caller) waiting, Left 0)
      Mutex (Just _) _ | tryOnly -> pure (cell, Left 16)
      Mutex (Just owner) waiting
        | owner == caller -> pure (cell, Left 35)
        | otherwise -> pure (Mutex (Just owner) (waiting Q.|> (caller, waiter)), Right waiter)
      _ -> pure (cell, Left 22)
  case result of
    Left status -> pure (Number status)
    Right signal -> liftIO (takeMVar signal) >> pure (Number 0)

releaseMutex :: Value -> R (Either Integer (Maybe (MVar ())))
releaseMutex pointer = do
  caller <- gets (number . currentThread)
  changeSync mutexWidth pointer emptyMutex $ \cell ->
    case cell of
      Mutex (Just owner) waiting | owner == caller ->
        case Q.viewl waiting of
          Q.EmptyL -> pure (emptyMutex, Right Nothing)
          (next, waiter) Q.:< remaining -> pure (Mutex (Just next) remaining, Right (Just waiter))
      Mutex _ _ -> pure (cell, Left 1)
      _ -> pure (cell, Left 22)

finishRelease :: Either Integer (Maybe (MVar ())) -> R Value
finishRelease result = case result of
  Left status -> pure (Number status)
  Right signal -> liftIO (mapM_ (\waiter -> putMVar waiter ()) signal) >> pure (Number 0)

waitCondition :: Value -> Value -> R Value
waitCondition condition mutex
  | number condition == number mutex = pure (Number 22)
  | otherwise = do
      waiter <- liftIO newEmptyMVar
      released <- locked $ changeSync conditionWidth condition emptyCondition $ \cell ->
        case cell of
          Condition waiting -> do
            result <- releaseMutex mutex
            case result of
              Left _ -> pure (cell, result)
              Right _ -> pure (Condition (waiting Q.|> waiter), result)
          _ -> pure (cell, Left 22)
      case released of
        Left status -> pure (Number status)
        Right _ -> do
          void (finishRelease released)
          liftIO (takeMVar waiter)
          acquireMutex False mutex

notifyCondition :: Bool -> Value -> R Value
notifyCondition allWaiters pointer = do
  result <- locked $ changeSync conditionWidth pointer emptyCondition $ \cell ->
    case cell of
      Condition waiting
        | allWaiters -> pure (emptyCondition, Just waiting)
        | otherwise -> case Q.viewl waiting of
            Q.EmptyL -> pure (cell, Just Q.empty)
            waiter Q.:< remaining -> pure (Condition remaining, Just (Q.singleton waiter))
      _ -> pure (cell, Nothing)
  case result of
    Nothing -> pure (Number 22)
    Just signals -> liftIO (mapM_ (\waiter -> putMVar waiter ()) signals) >> pure (Number 0)

worker :: World -> MVar Value -> Value -> Value -> IO ()
worker child cell callable argumentValue = do
  outcome <- E.try (runWorld child (threadInitialiser child >> invoke (Just PointerType) (pure callable) [pure argumentValue]))
  case outcome of
    Left exception -> throwTo (rootThread child) (Panic (E.displayException (exception :: E.SomeException)))
    Right (Left fault, _) -> throwTo (rootThread child) fault
    Right (Right result, _) -> putMVar cell result

execute :: [(String, [Value] -> R Value)] -> [String] -> Bool -> R () -> R () -> IO ()
execute entries labels parallel initialiser initThread = do
  args <- getArgs
  original <- getFullArgs
  program <- case original of [] -> getProgName; name : _ -> pure name
  traceMode <- lookupEnv "HERESY_TRACE"
  unless (traceMode `elem` [Nothing, Just "0", Just "1", Just "recent"]) $ do
    hPutStrLn stderr "HERESY_TRACE must be 0, 1 or recent"
    exitWith (ExitFailure 64)
  let enabled = traceMode == Just "1"
      recorded = enabled || traceMode == Just "recent"
  counter <- newIORef (1, 4096)
  table <- newIORef (1, M.empty)
  gate <- if parallel then Just <$> newMVar () else pure Nothing
  threads <- newMVar S.empty
  owner <- myThreadId
  let names = map fst entries ++ labels ++ map fst pthreadArities ++
        ["malloc", "calloc", "free", "memcpy", "memmove", "memset", "strlen", "strcmp", "puts", "putchar", "printf", "vprintf", "exit", "zhasvalidcap", "zis_readonly", "zgetlower", "zgetupper", "fopen", "fread", "fwrite", "fclose"]
      codes = S.fromList (zip names [9223372036854775808..])
      initial = World counter [] S.empty S.empty (S.fromList entries) codes "startup" 0 [] False False table gate threads owner nullPointer initThread
      action = do
        initialiser
        when parallel $ do
          handle <- allocate "thread" 0
          modify' (\w -> w { currentThread = handle })
        initThread
        strings <- mapM argument (program : args)
        argv <- allocate "argument" ((length strings + 1) * 8)
        forM_ (zip [0..] (strings ++ [nullPointer])) $ \(i,p) -> void (store PointerType (offset (i * 8) argv) p)
        modify' (\w -> w { events = 0, recent = [], tracing = enabled, history = recorded })
        mainFunction <- gets (S.lookup "main" . functions)
        case mainFunction of
          Nothing -> panic "no main function"
          Just f -> f [Number (toInteger (length strings)), argv]
  outcome <- E.try (runWorld initial action)
  let (result, final) = either (\fault -> (Left fault, initial)) id outcome
  handles <- snd <$> readIORef table
  forM_ (M.elems handles) (void . tryIOError . hClose)
  hFlush stdout
  case result of
    Right value -> let code = fromInteger (number value `mod` 256) in exitWith (if code == 0 then ExitSuccess else ExitFailure code)
    Left (Finish code) -> exitWith (if code == 0 then ExitSuccess else ExitFailure code)
    Left (Transfer _) -> hPutStrLn stderr "heresy panic: control transfer escaped its function" >> exitWith (ExitFailure 70)
    Left (Panic message) -> do
      hPutStrLn stderr ("heresy panic: " ++ message)
      unless (enabled || null (recent final)) $ hPutStrLn stderr (intercalate "\n" (reverse (recent final)))
      exitWith (ExitFailure 70)
