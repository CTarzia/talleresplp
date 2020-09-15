module Midi.IOHugs(openBinaryOutputFile) where

import Midi.IOExts
--import Hugs.IO
import IO

openBinaryOutputFile :: String -> IO Handle
openBinaryOutputFile fn = openBinaryFile fn WriteMode
  -- do
  --h <- openFile fn WriteMode
  --fd <- handleToFd h
  --openFd fd False WriteMode True

