module Midi.IOGhc(openBinaryOutputFile) where

import System.IO

openBinaryOutputFile :: String -> IO Handle
openBinaryOutputFile fn = openFile fn WriteMode

