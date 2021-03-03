{-# LANGUAGE LambdaCase, TemplateHaskell, BlockArguments #-}

import System.IO
import Data.Bits
import Lens.Micro.Platform
import Control.Monad.State
import qualified Data.Sequence as Seq
import qualified Data.ByteString.Lazy as BS
import qualified Data.Binary.Get as DBG
import qualified Data.Binary as DB
import Data.Word
import Control.Applicative

type Cell = Int

type Memory = Seq.Seq Cell

{-# INLINE memSize #-}
memSize :: Cell
memSize = 242000

{-# INLINE numDevices #-}
numDevices :: Cell
numDevices = 2

data NgaState = NgaState
  { _ds :: ![Cell]
  , _rs :: ![Cell]
  , _im :: !Memory 
  , _ip :: !Cell
  }

makeLenses 'NgaState

type Nga a = StateT NgaState IO a

{-# INLINE pushData #-}
pushData :: Cell -> Nga ()
pushData val = ds %= (val :)

{-# INLINE pushAddress #-}
pushAddress :: Cell -> Nga ()
pushAddress val = rs %= (val :)

{-# INLINE popData #-}
popData :: Nga Cell
popData = do
  x : xs <- use ds
  ds .= xs
  pure x

{-# INLINE popAddress #-}
popAddress :: Nga Cell
popAddress = do
  x : xs <- use rs
  rs .= xs
  pure x

{-# INLINE load #-}
load :: Cell -> Nga Cell
load idx = flip Seq.index idx <$> use im

{-# INLINE store #-}
store :: Cell -> Cell -> Nga ()
store val addr = im %= Seq.update addr val

{-# INLINE instCmp #-}
instCmp :: (Cell -> Cell -> Bool) -> Nga ()
instCmp f = do
  a : b : xs <- use ds
  if f b a
  then ds .= -1 : xs
  else ds .= 0 : xs

{-# INLINE instOp #-}
instOp :: (Cell -> Cell -> Cell) -> Nga ()
instOp f = do
  a : b : xs <- use ds
  ds .= f b a : xs

{-# INLINE toInst #-}
toInst :: Cell -> Nga ()
toInst op = case op of
  0 -> pure ()
  1 -> do
    ip += 1
    pushData =<< load =<< use ip
  2 -> do
    x : xs <- use ds
    ds .= x : x : xs
  3 -> do
    _ : xs <- use ds
    ds .= xs
  4 -> do
    a : b : xs <- use ds
    ds .= b : a : xs
  5 -> popData >>= pushAddress
  6 -> popAddress >>= pushData
  7 -> do
    ip <~ popData
    ip -= 1
  8 -> do
    pushAddress =<< use ip
    ip <~ popData
    ip -= 1
  9 -> do
    a : b : xs <- use ds
    ds .= xs
    when (b /= 0) do
      pushAddress =<< use ip
      ip .= a - 1
  10 -> ip <~ popAddress
  11 -> instCmp (==)
  12 -> instCmp (/=)
  13 -> instCmp (<)
  14 -> instCmp (>)
  15 -> popData >>= \case
    -1 -> pushData . length =<< use ds
    -2 -> pushData . length =<< use rs
    -3 -> pushData memSize
    -4 -> pushData minBound
    -5 -> pushData maxBound
    pt -> pushData =<< load pt
  16 -> do
    a : v : xs <- use ds
    ds .= xs
    store v a
  17 -> instOp (+)
  18 -> instOp (-)
  19 -> instOp (*)
  20 -> do
    a : b : xs <- use ds
    let (d, m) = divMod b a
    ds .= d : m : xs
  21 -> instOp (.&.)
  22 -> instOp (.|.)
  23 -> instOp xor
  24 -> instOp shift
  25 -> do
    x : xs <- use ds
    when (x == 0) do
      ip <~ popAddress
      ds .= xs
  26 -> ip .= memSize
  27 -> pushData numDevices
  28 -> popData >>= \case
    0 -> pushData 0 >> pushData 0
    1 -> pushData 0 >> pushData 1
  29 -> popData >>= \case
    0 -> do
      output <- popData
      liftIO do
        putChar $ toEnum output
    1 -> do
      input <- liftIO getChar
      pushData $ fromEnum input

{-# INLINE validateOpcodeBundle #-}
validateOpcodeBundle :: Cell -> Bool
validateOpcodeBundle raw = all id $ map test [0..3]
  where test i = let op = raw `shiftR` (8 * i) .&. 0xFF in op >= 0 && op <= 29

{-# INLINE processOpcodeBundle #-}
processOpcodeBundle :: Cell -> Nga ()
processOpcodeBundle op = forM_ [0..3] \i -> do
  processOpcode (op `shiftR` (8 * i) .&. 0xFF)

{-# INLINE processOpcode #-}
processOpcode :: Cell -> Nga ()
processOpcode op =
  when (op /= 0) do
    toInst op

mkState :: Memory -> NgaState
mkState image = NgaState { _ds = [], _rs = [], _im = image, _ip = 0 }

stepper :: Nga ()
stepper = do
  forever do
    opcode <- load =<< use ip
    when (validateOpcodeBundle opcode) do
      processOpcodeBundle opcode
    ip += 1

readImage :: FilePath -> IO ([Cell], Int)
readImage filename = do
  raw <- BS.readFile filename
  let filesize = fromIntegral $ BS.length raw `div` 4
  let result = map fromIntegral $ DBG.runGet (replicateM filesize DBG.getInt32le) raw
  return (result, filesize)

main :: IO ()
main = do
  (rawImage, size) <- readImage "ngaImage"
  let heap = Seq.replicate (memSize - size) 0
  let image = Seq.fromList rawImage
  runStateT stepper $ mkState (image <> heap)
  return ()
