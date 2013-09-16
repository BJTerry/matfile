{-# LANGUAGE GADTs, ExistentialQuantification, StandaloneDeriving, BangPatterns #-}

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
import Foreign.Storable (Storable)
import qualified Data.ByteString.Lazy as LBS (takeWhile, length, pack, toStrict)
import qualified Data.ByteString as BS (takeWhile, length, pack)
import Data.Typeable (Typeable(..))

import Debug.Trace

-- | Parsing in either little-endian or big-endian mode
data Endian = LE 
            | BE
  deriving (Show, Eq)

data DataType = MiInt8 [Int8]
              | MiUInt8 [Word8]
              | MiInt16 [Int16]
              | MiUInt16 [Word16]
              | MiInt32 [Int32]
              | MiUInt32 [Word32]
              | MiInt64 [Int64]
              | MiUInt64 [Word64]
              | MiSingle [Float]
              | MiDouble [Double]
              | MiMatrix ArrayType
              | MiUtf8 Text
              | MiUtf16 Text
              | MiUtf32 Text
              | MiComplex [Complex Double]
  deriving (Show)

data ArrayType = NumericArray Text [Int] DataType -- Name, dimensions and values
               | forall a. (Integral a, Storable a, Show a, Eq a, Typeable a) => SparseIntArray Text [Int] (Data.Map.Map (Word32, Word32) a)-- Name, dimensions
               | forall a. (RealFrac a, Storable a, Show a, Eq a, Typeable a) => SparseFloatArray Text [Int] (Data.Map.Map (Word32, Word32) a)
               | SparseComplexArray Text [Int] (Data.Map.Map (Word32, Word32) (Complex Double))
               | CellArray Text [Int] [ArrayType]
               | StructureArray Text [Int] [ArrayType]
               | ObjectArray Text Text [Int] [ArrayType]

instance Show ArrayType where
  show (NumericArray t dim dt) = "NumericArray " ++ show t ++ " " ++ show dim ++ " " ++ show dt
  show (SparseIntArray t dim dt) = "SparseIntArray " ++ show t ++ " " ++ show dim ++ " " ++ show dt
  show (SparseFloatArray t dim dt) = "SparseFloatArray " ++ show t ++ " " ++ show dim ++ " " ++ show dt
  show (SparseComplexArray t dim dt) = "SparseComplexArray " ++ show t ++ " " ++ show dim ++ " " ++ show dt
  show (CellArray t dim dt) = "CellArray " ++ show t ++ " " ++ show dim ++ " " ++ show dt
  show (StructureArray t dim dt) = "StructureArray " ++ show t ++ " " ++ show dim ++ " " ++ show dt
  show (ObjectArray t cname dim dt) = "ObjectArray " ++ show t ++ " " ++ show cname ++ " " ++ show dim ++ " " ++ show dt



toDoubles (MiInt8 x) = map fromIntegral x
toDoubles (MiUInt8 x) = map fromIntegral x
toDoubles (MiInt16 x) = map fromIntegral x
toDoubles (MiUInt16 x) = map fromIntegral x
toDoubles (MiInt32 x) = map fromIntegral x
toDoubles (MiUInt32 x) = map fromIntegral x
toDoubles (MiInt64 x) = map fromIntegral x
toDoubles (MiUInt64 x) = map fromIntegral x
toDoubles (MiSingle x) = map float2Double x
toDoubles (MiDouble x) = x


getMatFile = do
  endian <- getHeader
  case endian of
    LE -> bodyLe
    BE -> undefined

bodyLe = do
  align
  emp <- isEmpty
  case emp of
    True -> return []
    False -> do
      field <- leDataField
      fmap (field :) bodyLe





align = do
  bytes <- bytesRead
  skip $ (8 - (fromIntegral bytes `mod` 8)) `mod` 8

getHeader = do
  skip 124
  version <- getWord16le
  endian <- getWord16le
  case (version, endian) of
    (0x0100, 0x4d49) -> return LE
    (0x0001, 0x494d) -> return BE
    _ -> fail "Not a .mat file"

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
  smallDataElementCheck <- fmap (.&. 0xffff0000) $ lookAhead getWord32le
  (dataType, length) <- case smallDataElementCheck of
    0 -> normalDataElement
    _ -> smallDataElement
  res <- case dataType of
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
  return res
 where
  smallDataElement = do
    dataType <- getWord16le
    length <- getWord16le
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
  MiUInt32 (flags:_) <- leDataField
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
  MiUInt32 (flags:_) <- leDataField
  let (complex, global, logical) = extractFlags flags
  MiInt32 dimensions <- leDataField
  name <- getArrayName
  MiInt32 rowIndices <- leDataField
  MiInt32 colIndices <- leDataField
  real <- fmap (promoteArrayValues arrayType) leDataField
  case complex of
    False -> do
      return $ MiMatrix $ makeArrayType real name dimensions (map (+ 1) rowIndices) $ processCol 1 colIndices
    True -> do
      c <- fmap toDoubles leDataField
      let r = toDoubles real
          complex = zipWith (:+) r c
      return $ MiMatrix $ SparseComplexArray name (map fromIntegral dimensions) $ buildMap rowIndices colIndices complex
      
 where
  combineIndices row col real = ((fromIntegral row, fromIntegral col), real)
  buildMap row col val = Data.Map.fromList (zipWith3 combineIndices row col val)
  makeIntArrayType ints name dimensions rowIndices colIndices =
    SparseIntArray name (map fromIntegral dimensions) $ buildMap rowIndices colIndices ints
  makeFloatArrayType floats name dimensions rowIndices colIndices = 
    SparseFloatArray name (map fromIntegral dimensions) $ buildMap rowIndices colIndices floats
  makeArrayType (MiInt8 x) = makeIntArrayType x
  makeArrayType (MiUInt8 x) = makeIntArrayType x
  makeArrayType (MiInt16 x) = makeIntArrayType x
  makeArrayType (MiUInt16 x) = makeIntArrayType x
  makeArrayType (MiInt32 x) = makeIntArrayType x
  makeArrayType (MiUInt32 x) = makeIntArrayType x
  makeArrayType (MiInt64 x) = makeIntArrayType x
  makeArrayType (MiUInt64 x) = makeIntArrayType x
  makeArrayType (MiSingle x) = makeFloatArrayType x
  makeArrayType (MiDouble x) = makeFloatArrayType x
  -- processCol replicates column entries because Matlab only includes unique column entries. The last item doesn't matter
  processCol j (x:y:xs) | x < y - 1 = Prelude.replicate (fromIntegral (y - x)) j ++ processCol (j+1) (y:xs)
  processCol j (x:y:xs) | x == y = processCol (j+1) (y:xs)
  processCol j (x:[]) = []
  processCol j (x:xs) = j : processCol (j+1) xs


getCellArrayLe = do
  MiUInt32 (flags:_) <- leDataField
  let (complex, global, logical) = extractFlags flags
  MiInt32 dimensions <- leDataField
  let entries = fromIntegral $ product dimensions
  name <- getArrayName
  matrices <- replicateM entries (fmap removeMiMatrix $ skip 8 >> getMatrixLe undefined)
  return $ MiMatrix $ CellArray name (map fromIntegral dimensions) matrices
 where
  removeMiMatrix (MiMatrix arrayType) = arrayType

 
getStructureFieldNames fieldNameLength = do
  MiInt8 nameData <- leDataField
  let nameDataBytes = LBS.pack $ (map fromIntegral nameData)
  let names = flip runGet nameDataBytes $ 
                replicateM (fromIntegral (LBS.length nameDataBytes) `div` fromIntegral fieldNameLength) getName
  return names
 where
  getName = do
    bytes <- getByteString $ fromIntegral fieldNameLength
    let nameBytes = BS.takeWhile (/= 0) bytes
    return $ decodeUtf8 nameBytes

getStructureHelperLe classAction = do
  MiUInt32 (flags:_) <- leDataField
  let (complex, global, logical) = extractFlags flags
  MiInt32 dimensions <- leDataField
  name <- getArrayName
  align
  className <- classAction
  align
  loc <- bytesRead
  temp <- leDataField
  let MiInt32 (fieldNameLength:_) = temp
  names <- getStructureFieldNames fieldNameLength
  fields <- replicateM (Prelude.length names) leDataField
  return $ (name, className, map fromIntegral dimensions, zipWith renameField names fields)
 where
  renameField name (MiMatrix (NumericArray _ dim dt)) = NumericArray name dim dt
  renameField name (MiMatrix (SparseIntArray _ dim dt)) = SparseIntArray name dim dt
  renameField name (MiMatrix (SparseFloatArray _ dim dt)) = SparseFloatArray name dim dt
  renameField name (MiMatrix (SparseComplexArray _ dim dt)) = SparseComplexArray name dim dt
  renameField name (MiMatrix (CellArray _ dim dt)) = CellArray name dim dt
  renameField name (MiMatrix (StructureArray _ dim dt)) = StructureArray name dim dt
  renameField name (MiMatrix (ObjectArray _ className dim dt)) = ObjectArray name className dim dt

getStructureLe = do
  (name, _, dim, fields) <- getStructureHelperLe (return undefined) 
  return $ MiMatrix $ StructureArray name dim fields

getObjectLe = do
  (name, className, dim, fields) <- getStructureHelperLe getArrayName
  return $ MiMatrix $ ObjectArray name className dim fields

extractFlags word = 
  (testBit word 11, testBit word 10, testBit word 9)

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

promoteArrayValues 4 dataType = promoteTo16UInt dataType
promoteArrayValues 6 dataType = promoteToDouble dataType
promoteArrayValues 7 dataType = promoteToSingle dataType
promoteArrayValues 10 dataType = promoteTo16Int dataType
promoteArrayValues 11 dataType = promoteTo16UInt dataType
promoteArrayValues 12 dataType = promoteTo32Int dataType
promoteArrayValues 13 dataType = promoteTo32UInt dataType
promoteArrayValues 14 dataType = promoteTo64Int dataType
promoteArrayValues 15 dataType = promoteTo64UInt dataType
promoteArrayValues _ dataType = dataType

promoteToSingle dataType = MiSingle $ promoteFloat dataType

promoteToDouble (MiSingle v) = MiDouble $ map float2Double v
promoteToDouble v@(MiDouble _) = v
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

