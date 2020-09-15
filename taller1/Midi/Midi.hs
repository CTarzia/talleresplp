module Midi.Midi(midiCreateFile, midiNoteOn) where

import Midi.IOMidi
import System.IO

data MidiHeader = MidiHeader {
                    midiHeaderFormat   :: Integer,
                    midiHeaderNtracks  :: Integer,
                    midiHeaderDivision :: Integer
                  }
  deriving Show

hPutMidiHeader :: Handle -> MidiHeader -> IO ()
hPutMidiHeader h header
  | midiHeaderFormat header /= 0 = error "solo se soporta el formato 0"
  | otherwise = do
     hPutStr h "MThd"
     hPut32 h length
     hPut16 h $ midiHeaderFormat header
     hPut16 h $ midiHeaderNtracks header
     hPut16 h $ midiHeaderDivision header
     return ()
  where length = 6

--

data MidiTrack = MidiTrack { midiTrackEvents :: [MidiEvent] }

hPutMidiTrack :: Handle -> MidiTrack -> IO ()
hPutMidiTrack h track = do
     hPutStr h "MTrk"
     patchPos <- hGetPosn h
     -- leave space for the track length
     hPut32 h 0
     -- write the tracks
     b1 <- hPutBytes h [0x00, 0xff, 0x58, 0x04, 0x04, 0x02, 0x18, 0x08] -- time signature
     b2 <- hPutBytes h [0x00, 0xff, 0x51, 0x03, 0x07, 0xa1, 0x20]       -- tempo
     b3 <- hPutBytes h [0x00, 0xc0, 0x00]                               -- program change
     lengths <- mapM (hPutMidiEvent h) $ midiTrackEvents track
     b4 <- hPutBytes h [0x00, 0xff, 0x2f, 0] -- end of track
     -- patch the track length
     writePos <- hGetPosn h
     hSetPosn patchPos
     hPut32 h $ sum lengths + b1 + b2 + b3 + b4
     hSetPosn writePos
     return ()

--

data MidiEventType = MENoteOn        -- podria haber otros tipos de eventos
  deriving Show

midiEventTypeValue :: MidiEventType -> Integer
midiEventTypeValue MENoteOn  = 0x90

--

entre :: Integer -> Integer -> Integer -> Bool
entre x y z = y <= x && x <= z

data MidiEvent = MidiEvent {
                    midiEventDeltaTime :: Integer,
                    midiEventType      :: MidiEventType,
                    midiEventChannel   :: Integer,
                    midiEventData      :: [Integer]
                  }
  deriving Show

hPutMidiEvent :: Handle -> MidiEvent -> IO SizeBytes
hPutMidiEvent h event
  | not $ entre (midiEventChannel event) 0 15 = error "el canal debe estar entre 0 y 15"
  | otherwise = do
      l1 <- hPutVarLen h $ midiEventDeltaTime event
      l2 <- hPutByte h $ midiEventTypeValue (midiEventType event) + midiEventChannel event
      l3 <- hPutBytes h $ midiEventData event 
      return $ l1 + l2 + l3

--

midiCreateFile :: String -> [MidiEvent] -> IO ()
midiCreateFile fileName midiEvents = do
  h <- openBinaryOutputFile fileName
  hPutMidiHeader h $ MidiHeader 0 1 division
  hPutMidiTrack h $ MidiTrack midiEvents
  hFlush h
  hClose h
  where division = 10

midiNoteOn :: Integer -> Integer -> Integer -> Integer -> MidiEvent
midiNoteOn delta channel note volume = MidiEvent delta MENoteOn channel [note, volume]

