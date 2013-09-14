{-# LANGUAGE GADTs #-}

module Data.MatFile where

import Data.Binary
import Data.Binary.Get
import Data.Binary.IEEE754
import Data.Text.Encoding
import Data.Text hiding (map, zipWith)
import Control.Monad (replicateM)
import Data.Int
import Data.Word
import Codec.Compression.GZip (decompress)
import Data.Bits (testBit, (.&.))
import qualified Data.Map (fromList, Map(..))
import Data.List (elem)
import Data.Complex
import GHC.Float (float2Double)

-- | Parsing in either little-endian or big-endian mode
data Endian = LE 
            | BE

data DataType = [NumericType]
              | ArrayType
              | Text
  deriving (Show, Eq)

data NumericType = Int8
                 | Word8
                 | Int16
                 | Word16
                 | Int32
                 | Word32
                 | Int64
                 | Word64
                 | Float
                 | Double
                 | Complex Double
  deriving (Show, Eq)  

data ArrayType = NumericArray Text [Int] DataType -- Name, dimensions and values
               | SparseArray Text [Int] (Data.Map.Map (Word32, Word32) NumericType)-- Name, dimensions
  deriving (Show, Eq)

class ToDoubles x where
  toDoubles :: x -> [Double]

instance ToDoubles [NumericType] where
  toDoubles (x :: [Int8]) = map fromIntegral

align = do
  bytes <- bytesRead
  skip $ (8 - (fromIntegral bytes `mod` 8)) `mod` 8

leHeader = do
  skip 124
  version <- getWord16le
  endian <- getWord16le
  case (version, endian) of
    (0x0100, 0x4d49) -> return ()
    _ -> fail "Not a little-endian .mat file"

beHeader = do
  skip 124
  version <- getWord16be
  endian <- getWord16be
  case (version, endian) of
    (0x0100, 0x4d49) -> return ()
    _ -> fail "Not a big-endian .mat file"

-- | Parses a data field from the file. In general a data field of the numeric types will be an array (list in Haskell)
leDataField = do
  align
  smallDataElementCheck <- lookAhead getWord16le
  (dataType, length) <- case smallDataElementCheck of
    0 -> smallDataElement
    _ -> normalDataElement
  case dataType of
    1 -> getMiInt8 length
    2 -> getMiUInt8 length
    3 -> getMiInt16le length
    4 -> getMiUInt16le length
    5 -> getMiInt32le length
    6 -> getMiUInt32le length
    7 -> getMiSingleLe length
    --8
    9 -> getMiDoubleLe length
    --10
    --11
    12 -> getMiInt64le length
    13 -> getMiUInt64le length
    14 -> getMatrixLe length
    15 -> getCompressedLe length
    16 -> getUtf8 length
    17 -> getUtf16le length
    18 -> getUtf32le length
 where
  smallDataElement = do
    length <- getWord16le
    dataType <- getWord16le
    return (fromIntegral dataType, fromIntegral length)
  normalDataElement = do
    dataType <- getWord32le
    length <- getWord32le
    return (fromIntegral dataType, fromIntegral length)

getMatrixLe _ = do
  align
  flagsArray <- lookAhead leDataField
  case flagsArray of
    MiUInt32 (flags : _) -> do 
      let arrayClass = flags .&. 0xFF
      case arrayClass of
        a | elem a [4, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15] -> getNumericMatrixLe a
          | a == 1 -> getCellArrayLe
          | a == 2 -> getStructureLe 
          | a == 3 -> getObjectLe 
          | a == 5 -> getSparseArrayLe a
    _ -> fail "Invalid matrix flags"

getNumericMatrixLe arrayType = do
  MiUInt32 [flags] <- leDataField
  let (complex, global, logical) = extractFlags flags
  MiInt32 dimensions <- leDataField
  name <- getArrayName
  real <- fmap (promoteArrayValues arrayType) leDataField
  case complex of
    False -> return $ MiMatrix $ NumericArray name (Prelude.map fromIntegral dimensions) real
    True -> do
      c <- fmap toDoubles leDataField -- Since Haskell only has a complex type for doubles, we automatically convert to doubles
      let r = toDoubles real
          complex = MiComplex $ zipWith (:+) r c
      return $ MiMatrix $ NumericArray name (map fromIntegral dimensions) complex

           
getSparseArrayLe arrayType = do
  MiUInt32 [flags] <- leDataField
  let (complex, global, logical) = extractFlags flags
  MiInt32 dimensions <- leDataField
  name <- getArrayName
  MiInt32 rowIndices <- leDataField
  MiInt32 colIndices <- leDataField
  real <- fmap (toNumericType . (promoteArrayValues arrayType)) leDataField
  case complex of
    False -> do
      let result = zipWith3 combineIndices rowIndices colIndices real
      return $ MiMatrix $ SparseArray name dimensions result
    True -> do
      c <- fmap toDoubles leDataField
      let r = toDoubles real
          complex = zipWith (:+) r c
      return $ MiMatrix $ SparseArray name dimensions complex
 where
  combineIndices row col real = ((row, col), real)

getCellArrayLe = undefined

getStructureLe = undefined

getObjectLe = undefined


extractFlags word = 
  (testBit word 4, testBit word 5, testBit word 6)

getArrayName :: Get Text
getArrayName = do
  MiInt8 name <- leDataField
  return $ pack $ Prelude.map (toEnum . fromEnum) name


getCompressedLe bytes = do
  element <- fmap decompress $ getLazyByteString $ fromIntegral bytes
  let result = runGetOrFail leDataField element
  case result of
    Left (_, _, msg) -> fail msg
    Right (_, _, a) -> return a

getMiInt8 length = 
  fmap MiInt8 $ replicateM length (fmap fromIntegral getWord8)

getMiUInt8 length = 
  fmap MiUInt8 $ replicateM length getWord8

getMiInt16le bytes = do
  let length = bytes `div` 2
  fmap MiInt16 $ replicateM length (fmap fromIntegral getWord16le)

getMiUInt16le bytes = do
  let length = bytes `div` 2
  fmap MiUInt16 $ replicateM length getWord16le

getMiInt32le bytes = do
  let length = bytes `div` 4
  fmap MiInt32 $ replicateM length (fmap fromIntegral getWord32le)

getMiUInt32le bytes = do
  let length = bytes `div`4
  fmap MiUInt32 $ replicateM length getWord32le

getMiInt64le bytes = do
  let length = bytes `div`8
  fmap MiInt64 $ replicateM length (fmap fromIntegral getWord64le)

getMiUInt64le bytes = do
  let length = bytes `div` 8
  fmap MiUInt64 $ replicateM length getWord64le

getMiSingleLe bytes = do
  let length = bytes `div` 4
  fmap MiSingle $ replicateM length getFloat32le

getMiDoubleLe bytes = do
  let length = bytes `div` 8
  fmap MiDouble $ replicateM length getFloat64le

getUtf8 bytes =
  fmap (MiUtf8 . decodeUtf8) $ getByteString bytes

getUtf16le bytes =
  fmap (MiUtf16 . decodeUtf16LE) $ getByteString bytes

getUtf32le bytes = 
  fmap (MiUtf32 . decodeUtf32LE) $ getByteString bytes


-- Array types can be different from the stored value due to compression.
-- This promotes to the correct type.

promoteArrayValues 6 dataType = promoteToSingle dataType
promoteArrayValues 7 dataType = promoteToDouble dataType
promoteArrayValues 10 dataType = promoteTo16Int dataType
promoteArrayValues 11 dataType = promoteTo16UInt dataType
promoteArrayValues 12 dataType = promoteTo32Int dataType
promoteArrayValues 13 dataType = promoteTo32UInt dataType
promoteArrayValues 14 dataType = promoteTo64Int dataType
promoteArrayValues 15 dataType = promoteTo64UInt dataType

promoteToSingle dataType = MiSingle $ promoteFloat dataType

promoteToDouble (MiSingle v) = MiDouble $ map float2Double v
promoteToDouble dataType = MiDouble $ promoteFloat dataType

promoteTo16Int dataType = MiInt16 $ promoteInt dataType

promoteTo16UInt dataType = MiUInt16 $ promoteInt dataType

promoteTo32Int dataType = MiInt32 $ promoteInt dataType

promoteTo32UInt dataType = MiUInt32 $ promoteInt dataType

promoteTo64Int dataType = MiInt64 $ promoteInt dataType

promoteTo64UInt dataType = MiUInt64 $ promoteInt dataType


promoteInt (MiInt8 v) = map fromIntegral v
promoteInt (MiUInt8 v) = map fromIntegral v
promoteInt (MiInt16 v) = map fromIntegral v
promoteInt (MiUInt16 v) = map fromIntegral v
promoteInt (MiInt32 v) = map fromIntegral v
promoteInt (MiUInt32 v) = map fromIntegral v
promoteInt (MiInt64 v) = map fromIntegral v
promoteInt (MiUInt64 v) = map fromIntegral v

promoteFloat (MiInt8 v) = map fromIntegral v
promoteFloat (MiUInt8 v) = map fromIntegral v
promoteFloat (MiInt16 v) = map fromIntegral v
promoteFloat (MiUInt16 v) = map fromIntegral v
promoteFloat (MiInt32 v) = map fromIntegral v
promoteFloat (MiUInt32 v) = map fromIntegral v
promoteFloat (MiInt64 v) = map fromIntegral v
promoteFloat (MiUInt64 v) = map fromIntegral v

