module Midi.IOMidi(SizeBytes, openBinaryOutputFile, hPutByte, hPutBytes, hPut32, hPut16, hPutVarLen) where
--import Midi.IOHugs
import Midi.IOGhc
import System.IO
import Data.Char

type SizeBytes = Integer

hPutByte :: Handle -> Integer -> IO SizeBytes
hPutByte h x
  | x < 0 || x > 255 =
     error $ "el valor de un byte debe estar entre 0 y 255 (= " ++ show x ++ ")"
  | otherwise = do
    hPutChar h . chr . fromIntegral $ x
    return 1

hPutBytes :: Handle -> [Integer] -> IO SizeBytes
hPutBytes h bs = do
  ls <- mapM (hPutByte h) bs
  return $ sum ls

enBase' :: Integer -> Int -> Integer -> [Integer]
enBase' b p n = take (p - length bs) (repeat 0) ++ bs
  where bs = enBase n b

enBase n b | n < b     = [n]
           | otherwise = enBase (n `div` b) b ++ [n `mod` b]

hPut32, hPut16, hPutVarLen :: Handle -> Integer -> IO SizeBytes

hPut32 h x = do
  hPutBytes h $ enBase' 256 4 x
  return 4

hPut16 h x = do
  hPutBytes h $ enBase' 256 2 x
  return 2

hPutVarLen h n = hPutBytes h bytes
  where 
    bytes = map (+ 128) (init b) ++ [last b]
    b = enBase n 128

