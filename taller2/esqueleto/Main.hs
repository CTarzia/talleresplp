module Main where

import ParserLC
import PrettyPrintLC
import Text.PrettyPrint
import Type
import TypeInference
import Examples
import Test.HUnit

plainExpr :: String -> Doc
plainExpr = ppExpr . parseLC

inferExpr :: String -> Doc
inferExpr = ppTypingResult . inferType . parseLC

inferExprN :: String -> Doc
inferExprN = ppTypingResult . inferNormal . parseLC

testExp :: [Int] -> [Test]
testExp = map (\n -> sol n ~=? show (inferExprN (expr n)))

runTest :: [Test] -> IO Counts
runTest = runTestTT . test

main :: IO (IO Counts)
main = return tests

-- Tests
tests :: IO Counts
tests = do runTestTT allTests

allTests = test [
  "ejercicio1" ~: testEj1,
  "ejercicio2" ~: testEj2,
  "ejercicio3" ~: testEj3
  ]

testEj1 = concat [testZeroExp, testVarExp, testAppExp, testLamExp]
testEj2 = concat [testPredExp, testIsZeroExp, testTrueExp, testFalseExp, testIfExp]
testEj3 = concat [testEmptyListExp, testConsExp, testZipWithExp]

-- tests ejercicio 1
testZeroExp = testExp [1,2]
testVarExp = testExp [3,4]
testAppExp = testExp [5..15]
testLamExp = testExp [16..22]

-- tests ejercicio 2
testPredExp = testExp [23,24]
testIsZeroExp = testExp [25..27]
testTrueExp = testExp [28]
testFalseExp = testExp [29]
testIfExp = testExp [30..33]

-- tests ejercicio 3
testEmptyListExp = testExp [34]
testConsExp = testExp [35]
testZipWithExp = testExp [36,37]