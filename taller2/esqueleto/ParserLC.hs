{-# OPTIONS_GHC -w #-}
module ParserLC where
import Exp
import Data.Char
import qualified Data.Array as Happy_Data_Array
import qualified Data.Bits as Bits
import Control.Applicative(Applicative(..))
import Control.Monad (ap)

-- parser produced by Happy Version 1.19.10

data HappyAbsSyn t4
	= HappyTerminal (Token)
	| HappyErrorToken Int
	| HappyAbsSyn4 t4

happyExpList :: Happy_Data_Array.Array Int Int
happyExpList = Happy_Data_Array.listArray (0,248) ([20464,37,1,0,0,40928,106,0,0,128,0,4,8192,0,0,0,0,21500,8201,0,65280,596,0,49156,38207,65024,3753,0,32768,47743,1,32,49120,106,21759,63490,4775,16320,149,0,61440,9551,32640,426,54268,57357,28319,65280,884,43000,49170,38207,0,0,20464,32805,43647,64517,3411,57312,106,0,0,0,0,0,43518,4100,0,0,2048,0,8192,0,0,8192,43000,49170,54591,0,0
	])

{-# NOINLINE happyExpListPerState #-}
happyExpListPerState st =
    token_strs_expected
  where token_strs = ["error","%dummy","%start_parse","Exp","var","'0'","succ","pred","iszero","true","false","if","then","else","'\\\\'","'->'","'('","')'","'['","']'","'::'","zip","and","with","','","'~>'","%eof"]
        bit_start = st * 27
        bit_end = (st + 1) * 27
        read_bit = readArrayBit happyExpList
        bits = map read_bit [bit_start..bit_end - 1]
        bits_indexed = zip bits [0..26]
        token_strs_expected = concatMap f bits_indexed
        f (False, _) = []
        f (True, nr) = [token_strs !! nr]

action_0 (5) = happyShift action_4
action_0 (6) = happyShift action_2
action_0 (7) = happyShift action_5
action_0 (8) = happyShift action_6
action_0 (9) = happyShift action_7
action_0 (10) = happyShift action_8
action_0 (11) = happyShift action_9
action_0 (12) = happyShift action_10
action_0 (15) = happyShift action_11
action_0 (17) = happyShift action_12
action_0 (19) = happyShift action_13
action_0 (22) = happyShift action_14
action_0 (4) = happyGoto action_3
action_0 _ = happyFail (happyExpListPerState 0)

action_1 (6) = happyShift action_2
action_1 _ = happyFail (happyExpListPerState 1)

action_2 _ = happyReduce_1

action_3 (5) = happyShift action_4
action_3 (6) = happyShift action_2
action_3 (7) = happyShift action_5
action_3 (8) = happyShift action_6
action_3 (9) = happyShift action_7
action_3 (10) = happyShift action_8
action_3 (11) = happyShift action_9
action_3 (12) = happyShift action_10
action_3 (15) = happyShift action_11
action_3 (17) = happyShift action_12
action_3 (19) = happyShift action_13
action_3 (21) = happyShift action_24
action_3 (22) = happyShift action_14
action_3 (27) = happyAccept
action_3 (4) = happyGoto action_23
action_3 _ = happyFail (happyExpListPerState 3)

action_4 _ = happyReduce_4

action_5 (17) = happyShift action_22
action_5 _ = happyFail (happyExpListPerState 5)

action_6 (17) = happyShift action_21
action_6 _ = happyFail (happyExpListPerState 6)

action_7 (17) = happyShift action_20
action_7 _ = happyFail (happyExpListPerState 7)

action_8 _ = happyReduce_2

action_9 _ = happyReduce_3

action_10 (5) = happyShift action_4
action_10 (6) = happyShift action_2
action_10 (7) = happyShift action_5
action_10 (8) = happyShift action_6
action_10 (9) = happyShift action_7
action_10 (10) = happyShift action_8
action_10 (11) = happyShift action_9
action_10 (12) = happyShift action_10
action_10 (15) = happyShift action_11
action_10 (17) = happyShift action_12
action_10 (19) = happyShift action_13
action_10 (22) = happyShift action_14
action_10 (4) = happyGoto action_19
action_10 _ = happyFail (happyExpListPerState 10)

action_11 (5) = happyShift action_18
action_11 _ = happyFail (happyExpListPerState 11)

action_12 (5) = happyShift action_4
action_12 (6) = happyShift action_2
action_12 (7) = happyShift action_5
action_12 (8) = happyShift action_6
action_12 (9) = happyShift action_7
action_12 (10) = happyShift action_8
action_12 (11) = happyShift action_9
action_12 (12) = happyShift action_10
action_12 (15) = happyShift action_11
action_12 (17) = happyShift action_12
action_12 (19) = happyShift action_13
action_12 (22) = happyShift action_14
action_12 (4) = happyGoto action_17
action_12 _ = happyFail (happyExpListPerState 12)

action_13 (20) = happyShift action_16
action_13 _ = happyFail (happyExpListPerState 13)

action_14 (5) = happyShift action_4
action_14 (6) = happyShift action_2
action_14 (7) = happyShift action_5
action_14 (8) = happyShift action_6
action_14 (9) = happyShift action_7
action_14 (10) = happyShift action_8
action_14 (11) = happyShift action_9
action_14 (12) = happyShift action_10
action_14 (15) = happyShift action_11
action_14 (17) = happyShift action_12
action_14 (19) = happyShift action_13
action_14 (22) = happyShift action_14
action_14 (4) = happyGoto action_15
action_14 _ = happyFail (happyExpListPerState 14)

action_15 (5) = happyShift action_4
action_15 (6) = happyShift action_2
action_15 (7) = happyShift action_5
action_15 (8) = happyShift action_6
action_15 (9) = happyShift action_7
action_15 (10) = happyShift action_8
action_15 (11) = happyShift action_9
action_15 (12) = happyShift action_10
action_15 (15) = happyShift action_11
action_15 (17) = happyShift action_12
action_15 (19) = happyShift action_13
action_15 (21) = happyShift action_24
action_15 (22) = happyShift action_14
action_15 (23) = happyShift action_32
action_15 (4) = happyGoto action_23
action_15 _ = happyFail (happyExpListPerState 15)

action_16 _ = happyReduce_12

action_17 (5) = happyShift action_4
action_17 (6) = happyShift action_2
action_17 (7) = happyShift action_5
action_17 (8) = happyShift action_6
action_17 (9) = happyShift action_7
action_17 (10) = happyShift action_8
action_17 (11) = happyShift action_9
action_17 (12) = happyShift action_10
action_17 (15) = happyShift action_11
action_17 (17) = happyShift action_12
action_17 (18) = happyShift action_31
action_17 (19) = happyShift action_13
action_17 (21) = happyShift action_24
action_17 (22) = happyShift action_14
action_17 (4) = happyGoto action_23
action_17 _ = happyFail (happyExpListPerState 17)

action_18 (16) = happyShift action_30
action_18 _ = happyFail (happyExpListPerState 18)

action_19 (5) = happyShift action_4
action_19 (6) = happyShift action_2
action_19 (7) = happyShift action_5
action_19 (8) = happyShift action_6
action_19 (9) = happyShift action_7
action_19 (10) = happyShift action_8
action_19 (11) = happyShift action_9
action_19 (12) = happyShift action_10
action_19 (13) = happyShift action_29
action_19 (15) = happyShift action_11
action_19 (17) = happyShift action_12
action_19 (19) = happyShift action_13
action_19 (21) = happyShift action_24
action_19 (22) = happyShift action_14
action_19 (4) = happyGoto action_23
action_19 _ = happyFail (happyExpListPerState 19)

action_20 (5) = happyShift action_4
action_20 (6) = happyShift action_2
action_20 (7) = happyShift action_5
action_20 (8) = happyShift action_6
action_20 (9) = happyShift action_7
action_20 (10) = happyShift action_8
action_20 (11) = happyShift action_9
action_20 (12) = happyShift action_10
action_20 (15) = happyShift action_11
action_20 (17) = happyShift action_12
action_20 (19) = happyShift action_13
action_20 (22) = happyShift action_14
action_20 (4) = happyGoto action_28
action_20 _ = happyFail (happyExpListPerState 20)

action_21 (5) = happyShift action_4
action_21 (6) = happyShift action_2
action_21 (7) = happyShift action_5
action_21 (8) = happyShift action_6
action_21 (9) = happyShift action_7
action_21 (10) = happyShift action_8
action_21 (11) = happyShift action_9
action_21 (12) = happyShift action_10
action_21 (15) = happyShift action_11
action_21 (17) = happyShift action_12
action_21 (19) = happyShift action_13
action_21 (22) = happyShift action_14
action_21 (4) = happyGoto action_27
action_21 _ = happyFail (happyExpListPerState 21)

action_22 (5) = happyShift action_4
action_22 (6) = happyShift action_2
action_22 (7) = happyShift action_5
action_22 (8) = happyShift action_6
action_22 (9) = happyShift action_7
action_22 (10) = happyShift action_8
action_22 (11) = happyShift action_9
action_22 (12) = happyShift action_10
action_22 (15) = happyShift action_11
action_22 (17) = happyShift action_12
action_22 (19) = happyShift action_13
action_22 (22) = happyShift action_14
action_22 (4) = happyGoto action_26
action_22 _ = happyFail (happyExpListPerState 22)

action_23 (4) = happyGoto action_23
action_23 _ = happyReduce_9

action_24 (5) = happyShift action_4
action_24 (6) = happyShift action_2
action_24 (7) = happyShift action_5
action_24 (8) = happyShift action_6
action_24 (9) = happyShift action_7
action_24 (10) = happyShift action_8
action_24 (11) = happyShift action_9
action_24 (12) = happyShift action_10
action_24 (15) = happyShift action_11
action_24 (17) = happyShift action_12
action_24 (19) = happyShift action_13
action_24 (22) = happyShift action_14
action_24 (4) = happyGoto action_25
action_24 _ = happyFail (happyExpListPerState 24)

action_25 (5) = happyShift action_4
action_25 (6) = happyShift action_2
action_25 (7) = happyShift action_5
action_25 (8) = happyShift action_6
action_25 (9) = happyShift action_7
action_25 (10) = happyShift action_8
action_25 (11) = happyShift action_9
action_25 (12) = happyShift action_10
action_25 (15) = happyShift action_11
action_25 (17) = happyShift action_12
action_25 (19) = happyShift action_13
action_25 (21) = happyShift action_24
action_25 (22) = happyShift action_14
action_25 (4) = happyGoto action_23
action_25 _ = happyReduce_13

action_26 (5) = happyShift action_4
action_26 (6) = happyShift action_2
action_26 (7) = happyShift action_5
action_26 (8) = happyShift action_6
action_26 (9) = happyShift action_7
action_26 (10) = happyShift action_8
action_26 (11) = happyShift action_9
action_26 (12) = happyShift action_10
action_26 (15) = happyShift action_11
action_26 (17) = happyShift action_12
action_26 (18) = happyShift action_38
action_26 (19) = happyShift action_13
action_26 (21) = happyShift action_24
action_26 (22) = happyShift action_14
action_26 (4) = happyGoto action_23
action_26 _ = happyFail (happyExpListPerState 26)

action_27 (5) = happyShift action_4
action_27 (6) = happyShift action_2
action_27 (7) = happyShift action_5
action_27 (8) = happyShift action_6
action_27 (9) = happyShift action_7
action_27 (10) = happyShift action_8
action_27 (11) = happyShift action_9
action_27 (12) = happyShift action_10
action_27 (15) = happyShift action_11
action_27 (17) = happyShift action_12
action_27 (18) = happyShift action_37
action_27 (19) = happyShift action_13
action_27 (21) = happyShift action_24
action_27 (22) = happyShift action_14
action_27 (4) = happyGoto action_23
action_27 _ = happyFail (happyExpListPerState 27)

action_28 (5) = happyShift action_4
action_28 (6) = happyShift action_2
action_28 (7) = happyShift action_5
action_28 (8) = happyShift action_6
action_28 (9) = happyShift action_7
action_28 (10) = happyShift action_8
action_28 (11) = happyShift action_9
action_28 (12) = happyShift action_10
action_28 (15) = happyShift action_11
action_28 (17) = happyShift action_12
action_28 (18) = happyShift action_36
action_28 (19) = happyShift action_13
action_28 (21) = happyShift action_24
action_28 (22) = happyShift action_14
action_28 (4) = happyGoto action_23
action_28 _ = happyFail (happyExpListPerState 28)

action_29 (5) = happyShift action_4
action_29 (6) = happyShift action_2
action_29 (7) = happyShift action_5
action_29 (8) = happyShift action_6
action_29 (9) = happyShift action_7
action_29 (10) = happyShift action_8
action_29 (11) = happyShift action_9
action_29 (12) = happyShift action_10
action_29 (15) = happyShift action_11
action_29 (17) = happyShift action_12
action_29 (19) = happyShift action_13
action_29 (22) = happyShift action_14
action_29 (4) = happyGoto action_35
action_29 _ = happyFail (happyExpListPerState 29)

action_30 (5) = happyShift action_4
action_30 (6) = happyShift action_2
action_30 (7) = happyShift action_5
action_30 (8) = happyShift action_6
action_30 (9) = happyShift action_7
action_30 (10) = happyShift action_8
action_30 (11) = happyShift action_9
action_30 (12) = happyShift action_10
action_30 (15) = happyShift action_11
action_30 (17) = happyShift action_12
action_30 (19) = happyShift action_13
action_30 (22) = happyShift action_14
action_30 (4) = happyGoto action_34
action_30 _ = happyFail (happyExpListPerState 30)

action_31 _ = happyReduce_11

action_32 (5) = happyShift action_4
action_32 (6) = happyShift action_2
action_32 (7) = happyShift action_5
action_32 (8) = happyShift action_6
action_32 (9) = happyShift action_7
action_32 (10) = happyShift action_8
action_32 (11) = happyShift action_9
action_32 (12) = happyShift action_10
action_32 (15) = happyShift action_11
action_32 (17) = happyShift action_12
action_32 (19) = happyShift action_13
action_32 (22) = happyShift action_14
action_32 (4) = happyGoto action_33
action_32 _ = happyFail (happyExpListPerState 32)

action_33 (5) = happyShift action_4
action_33 (6) = happyShift action_2
action_33 (7) = happyShift action_5
action_33 (8) = happyShift action_6
action_33 (9) = happyShift action_7
action_33 (10) = happyShift action_8
action_33 (11) = happyShift action_9
action_33 (12) = happyShift action_10
action_33 (15) = happyShift action_11
action_33 (17) = happyShift action_12
action_33 (19) = happyShift action_13
action_33 (21) = happyShift action_24
action_33 (22) = happyShift action_14
action_33 (24) = happyShift action_40
action_33 (4) = happyGoto action_23
action_33 _ = happyFail (happyExpListPerState 33)

action_34 (5) = happyShift action_4
action_34 (6) = happyShift action_2
action_34 (7) = happyShift action_5
action_34 (8) = happyShift action_6
action_34 (9) = happyShift action_7
action_34 (10) = happyShift action_8
action_34 (11) = happyShift action_9
action_34 (12) = happyShift action_10
action_34 (15) = happyShift action_11
action_34 (17) = happyShift action_12
action_34 (19) = happyShift action_13
action_34 (21) = happyShift action_24
action_34 (22) = happyShift action_14
action_34 (4) = happyGoto action_23
action_34 _ = happyReduce_10

action_35 (5) = happyShift action_4
action_35 (6) = happyShift action_2
action_35 (7) = happyShift action_5
action_35 (8) = happyShift action_6
action_35 (9) = happyShift action_7
action_35 (10) = happyShift action_8
action_35 (11) = happyShift action_9
action_35 (12) = happyShift action_10
action_35 (14) = happyShift action_39
action_35 (15) = happyShift action_11
action_35 (17) = happyShift action_12
action_35 (19) = happyShift action_13
action_35 (21) = happyShift action_24
action_35 (22) = happyShift action_14
action_35 (4) = happyGoto action_23
action_35 _ = happyFail (happyExpListPerState 35)

action_36 _ = happyReduce_7

action_37 _ = happyReduce_6

action_38 _ = happyReduce_5

action_39 (5) = happyShift action_4
action_39 (6) = happyShift action_2
action_39 (7) = happyShift action_5
action_39 (8) = happyShift action_6
action_39 (9) = happyShift action_7
action_39 (10) = happyShift action_8
action_39 (11) = happyShift action_9
action_39 (12) = happyShift action_10
action_39 (15) = happyShift action_11
action_39 (17) = happyShift action_12
action_39 (19) = happyShift action_13
action_39 (22) = happyShift action_14
action_39 (4) = happyGoto action_42
action_39 _ = happyFail (happyExpListPerState 39)

action_40 (5) = happyShift action_41
action_40 _ = happyFail (happyExpListPerState 40)

action_41 (25) = happyShift action_43
action_41 _ = happyFail (happyExpListPerState 41)

action_42 (5) = happyFail []
action_42 (6) = happyFail []
action_42 (7) = happyFail []
action_42 (8) = happyFail []
action_42 (9) = happyFail []
action_42 (10) = happyFail []
action_42 (11) = happyFail []
action_42 (12) = happyFail []
action_42 (15) = happyFail []
action_42 (17) = happyFail []
action_42 (19) = happyFail []
action_42 (22) = happyFail []
action_42 (4) = happyGoto action_23
action_42 _ = happyReduce_8

action_43 (5) = happyShift action_44
action_43 _ = happyFail (happyExpListPerState 43)

action_44 (26) = happyShift action_45
action_44 _ = happyFail (happyExpListPerState 44)

action_45 (5) = happyShift action_4
action_45 (6) = happyShift action_2
action_45 (7) = happyShift action_5
action_45 (8) = happyShift action_6
action_45 (9) = happyShift action_7
action_45 (10) = happyShift action_8
action_45 (11) = happyShift action_9
action_45 (12) = happyShift action_10
action_45 (15) = happyShift action_11
action_45 (17) = happyShift action_12
action_45 (19) = happyShift action_13
action_45 (22) = happyShift action_14
action_45 (4) = happyGoto action_46
action_45 _ = happyFail (happyExpListPerState 45)

action_46 (5) = happyShift action_4
action_46 (6) = happyShift action_2
action_46 (7) = happyShift action_5
action_46 (8) = happyShift action_6
action_46 (9) = happyShift action_7
action_46 (10) = happyShift action_8
action_46 (11) = happyShift action_9
action_46 (12) = happyShift action_10
action_46 (15) = happyShift action_11
action_46 (17) = happyShift action_12
action_46 (19) = happyShift action_13
action_46 (21) = happyShift action_24
action_46 (22) = happyShift action_14
action_46 (4) = happyGoto action_23
action_46 _ = happyReduce_14

happyReduce_1 = happySpecReduce_1  4 happyReduction_1
happyReduction_1 _
	 =  HappyAbsSyn4
		 (ZeroExp
	)

happyReduce_2 = happySpecReduce_1  4 happyReduction_2
happyReduction_2 _
	 =  HappyAbsSyn4
		 (TrueExp
	)

happyReduce_3 = happySpecReduce_1  4 happyReduction_3
happyReduction_3 _
	 =  HappyAbsSyn4
		 (FalseExp
	)

happyReduce_4 = happySpecReduce_1  4 happyReduction_4
happyReduction_4 (HappyTerminal (TokenVar happy_var_1))
	 =  HappyAbsSyn4
		 (VarExp happy_var_1
	)
happyReduction_4 _  = notHappyAtAll 

happyReduce_5 = happyReduce 4 4 happyReduction_5
happyReduction_5 (_ `HappyStk`
	(HappyAbsSyn4  happy_var_3) `HappyStk`
	_ `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn4
		 (SuccExp happy_var_3
	) `HappyStk` happyRest

happyReduce_6 = happyReduce 4 4 happyReduction_6
happyReduction_6 (_ `HappyStk`
	(HappyAbsSyn4  happy_var_3) `HappyStk`
	_ `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn4
		 (PredExp happy_var_3
	) `HappyStk` happyRest

happyReduce_7 = happyReduce 4 4 happyReduction_7
happyReduction_7 (_ `HappyStk`
	(HappyAbsSyn4  happy_var_3) `HappyStk`
	_ `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn4
		 (IsZeroExp happy_var_3
	) `HappyStk` happyRest

happyReduce_8 = happyReduce 6 4 happyReduction_8
happyReduction_8 ((HappyAbsSyn4  happy_var_6) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn4  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn4  happy_var_2) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn4
		 (IfExp happy_var_2 happy_var_4 happy_var_6
	) `HappyStk` happyRest

happyReduce_9 = happySpecReduce_2  4 happyReduction_9
happyReduction_9 (HappyAbsSyn4  happy_var_2)
	(HappyAbsSyn4  happy_var_1)
	 =  HappyAbsSyn4
		 (AppExp happy_var_1 happy_var_2
	)
happyReduction_9 _ _  = notHappyAtAll 

happyReduce_10 = happyReduce 4 4 happyReduction_10
happyReduction_10 ((HappyAbsSyn4  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyTerminal (TokenVar happy_var_2)) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn4
		 (LamExp happy_var_2 () happy_var_4
	) `HappyStk` happyRest

happyReduce_11 = happySpecReduce_3  4 happyReduction_11
happyReduction_11 _
	(HappyAbsSyn4  happy_var_2)
	_
	 =  HappyAbsSyn4
		 (happy_var_2
	)
happyReduction_11 _ _ _  = notHappyAtAll 

happyReduce_12 = happySpecReduce_2  4 happyReduction_12
happyReduction_12 _
	_
	 =  HappyAbsSyn4
		 (EmptyListExp ()
	)

happyReduce_13 = happySpecReduce_3  4 happyReduction_13
happyReduction_13 (HappyAbsSyn4  happy_var_3)
	_
	(HappyAbsSyn4  happy_var_1)
	 =  HappyAbsSyn4
		 (ConsExp happy_var_1 happy_var_3
	)
happyReduction_13 _ _ _  = notHappyAtAll 

happyReduce_14 = happyReduce 10 4 happyReduction_14
happyReduction_14 ((HappyAbsSyn4  happy_var_10) `HappyStk`
	_ `HappyStk`
	(HappyTerminal (TokenVar happy_var_8)) `HappyStk`
	_ `HappyStk`
	(HappyTerminal (TokenVar happy_var_6)) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn4  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn4  happy_var_2) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn4
		 (ZipWithExp happy_var_2 happy_var_4 happy_var_6 happy_var_8 happy_var_10
	) `HappyStk` happyRest

happyNewToken action sts stk [] =
	action 27 27 notHappyAtAll (HappyState action) sts stk []

happyNewToken action sts stk (tk:tks) =
	let cont i = action i i tk (HappyState action) sts stk tks in
	case tk of {
	TokenVar happy_dollar_dollar -> cont 5;
	TokenZero -> cont 6;
	TokenSucc -> cont 7;
	TokenPred -> cont 8;
	TokenIsZero -> cont 9;
	TokenTrue -> cont 10;
	TokenFalse -> cont 11;
	TokenIf -> cont 12;
	TokenThen -> cont 13;
	TokenElse -> cont 14;
	TokenLam -> cont 15;
	TokenArrow -> cont 16;
	TokenOB -> cont 17;
	TokenCB -> cont 18;
	TokenOSB -> cont 19;
	TokenCSB -> cont 20;
	TokenCons -> cont 21;
	TokenZip -> cont 22;
	TokenAnd -> cont 23;
	TokenWith -> cont 24;
	TokenComma -> cont 25;
	TokenOtherArrow -> cont 26;
	_ -> happyError' ((tk:tks), [])
	}

happyError_ explist 27 tk tks = happyError' (tks, explist)
happyError_ explist _ tk tks = happyError' ((tk:tks), explist)

newtype HappyIdentity a = HappyIdentity a
happyIdentity = HappyIdentity
happyRunIdentity (HappyIdentity a) = a

instance Functor HappyIdentity where
    fmap f (HappyIdentity a) = HappyIdentity (f a)

instance Applicative HappyIdentity where
    pure  = HappyIdentity
    (<*>) = ap
instance Monad HappyIdentity where
    return = pure
    (HappyIdentity p) >>= q = q p

happyThen :: () => HappyIdentity a -> (a -> HappyIdentity b) -> HappyIdentity b
happyThen = (>>=)
happyReturn :: () => a -> HappyIdentity a
happyReturn = (return)
happyThen1 m k tks = (>>=) m (\a -> k a tks)
happyReturn1 :: () => a -> b -> HappyIdentity a
happyReturn1 = \a tks -> (return) a
happyError' :: () => ([(Token)], [String]) -> HappyIdentity a
happyError' = HappyIdentity . (\(tokens, _) -> parseError tokens)
parse tks = happyRunIdentity happySomeParser where
 happySomeParser = happyThen (happyParse action_0 tks) (\x -> case x of {HappyAbsSyn4 z -> happyReturn z; _other -> notHappyAtAll })

happySeq = happyDontSeq


parseError :: [Token] -> a
parseError _ = error "Parse error"

data Token
      = TokenVar String
      | TokenZero
      | TokenSucc
      | TokenPred
      | TokenIsZero
      | TokenTrue
      | TokenFalse
      | TokenIf
      | TokenThen
      | TokenElse
      | TokenLam
      | TokenArrow
      | TokenOB
      | TokenCB 
      | TokenOSB
      | TokenCSB
      | TokenCons 
      | TokenZip
      | TokenAnd
      | TokenWith
      | TokenComma
      | TokenOtherArrow deriving Show

lexer :: String -> [Token]
lexer [] = []
lexer (c:cs) 
  | isSpace c = lexer cs
  | isAlpha c = lexVar (c:cs)
lexer ('0':cs) = TokenZero : lexer cs
lexer ('-':'>':cs) = TokenArrow : lexer cs
lexer ('.':cs) = TokenArrow : lexer cs
lexer ('\\':cs) = TokenLam : lexer cs
lexer ('(':cs) = TokenOB : lexer cs
lexer (')':cs) = TokenCB : lexer cs
lexer ('[':']':cs) = TokenOSB : TokenCSB : lexer cs
lexer (':':':':cs) = TokenCons : lexer cs
lexer (',':cs) = TokenComma : lexer cs
lexer ('~':'>':cs) = TokenOtherArrow : lexer cs

lexVar cs =
   case fstToLower $ span (\x->isAlpha x || isDigit x) cs of
     ("suc",rest) -> TokenSucc : lexer rest
     ("succ",rest) -> TokenSucc : lexer rest
     ("pred",rest) -> TokenPred : lexer rest
     ("iszero",rest)  -> TokenIsZero : lexer rest
     ("true",rest)  -> TokenTrue : lexer rest
     ("false",rest)  -> TokenFalse : lexer rest
     ("if",rest)  -> TokenIf : lexer rest
     ("then",rest)  -> TokenThen : lexer rest
     ("else",rest)  -> TokenElse : lexer rest
     ("lambda",rest)  -> TokenLam : lexer rest
     ("zip",rest) -> TokenZip : lexer rest
     ("and",rest) -> TokenAnd : lexer rest
     ("with",rest) -> TokenWith : lexer rest
     (var,rest)   -> TokenVar var : lexer rest
   where fstToLower (x, y) = (map toLower x, y)

parseLC :: String -> Exp ()
parseLC = parse . lexer
{-# LINE 1 "templates/GenericTemplate.hs" #-}
{-# LINE 1 "templates/GenericTemplate.hs" #-}
{-# LINE 1 "<built-in>" #-}
{-# LINE 15 "<built-in>" #-}
{-# LINE 1 "/Users/malena/.ghcup/ghc/8.6.3/lib/ghc-8.6.3/include/ghcversion.h" #-}
















{-# LINE 16 "<built-in>" #-}
{-# LINE 1 "/var/folders/6v/h9lwd7ms6hx5jt9txyz_vz880000gn/T/ghc50879_0/ghc_2.h" #-}













































































































































































































{-# LINE 17 "<built-in>" #-}
{-# LINE 1 "templates/GenericTemplate.hs" #-}
-- Id: GenericTemplate.hs,v 1.26 2005/01/14 14:47:22 simonmar Exp 










{-# LINE 43 "templates/GenericTemplate.hs" #-}

data Happy_IntList = HappyCons Int Happy_IntList








{-# LINE 65 "templates/GenericTemplate.hs" #-}


{-# LINE 75 "templates/GenericTemplate.hs" #-}










infixr 9 `HappyStk`
data HappyStk a = HappyStk a (HappyStk a)

-----------------------------------------------------------------------------
-- starting the parse

happyParse start_state = happyNewToken start_state notHappyAtAll notHappyAtAll

-----------------------------------------------------------------------------
-- Accepting the parse

-- If the current token is (1), it means we've just accepted a partial
-- parse (a %partial parser).  We must ignore the saved token on the top of
-- the stack in this case.
happyAccept (1) tk st sts (_ `HappyStk` ans `HappyStk` _) =
        happyReturn1 ans
happyAccept j tk st sts (HappyStk ans _) = 
         (happyReturn1 ans)

-----------------------------------------------------------------------------
-- Arrays only: do the next action


{-# LINE 137 "templates/GenericTemplate.hs" #-}


{-# LINE 147 "templates/GenericTemplate.hs" #-}
indexShortOffAddr arr off = arr Happy_Data_Array.! off


{-# INLINE happyLt #-}
happyLt x y = (x < y)






readArrayBit arr bit =
    Bits.testBit (indexShortOffAddr arr (bit `div` 16)) (bit `mod` 16)






-----------------------------------------------------------------------------
-- HappyState data type (not arrays)



newtype HappyState b c = HappyState
        (Int ->                    -- token number
         Int ->                    -- token number (yes, again)
         b ->                           -- token semantic value
         HappyState b c ->              -- current state
         [HappyState b c] ->            -- state stack
         c)



-----------------------------------------------------------------------------
-- Shifting a token

happyShift new_state (1) tk st sts stk@(x `HappyStk` _) =
     let i = (case x of { HappyErrorToken (i) -> i }) in
--     trace "shifting the error token" $
     new_state i i tk (HappyState (new_state)) ((st):(sts)) (stk)

happyShift new_state i tk st sts stk =
     happyNewToken new_state ((st):(sts)) ((HappyTerminal (tk))`HappyStk`stk)

-- happyReduce is specialised for the common cases.

happySpecReduce_0 i fn (1) tk st sts stk
     = happyFail [] (1) tk st sts stk
happySpecReduce_0 nt fn j tk st@((HappyState (action))) sts stk
     = action nt j tk st ((st):(sts)) (fn `HappyStk` stk)

happySpecReduce_1 i fn (1) tk st sts stk
     = happyFail [] (1) tk st sts stk
happySpecReduce_1 nt fn j tk _ sts@(((st@(HappyState (action))):(_))) (v1`HappyStk`stk')
     = let r = fn v1 in
       happySeq r (action nt j tk st sts (r `HappyStk` stk'))

happySpecReduce_2 i fn (1) tk st sts stk
     = happyFail [] (1) tk st sts stk
happySpecReduce_2 nt fn j tk _ ((_):(sts@(((st@(HappyState (action))):(_))))) (v1`HappyStk`v2`HappyStk`stk')
     = let r = fn v1 v2 in
       happySeq r (action nt j tk st sts (r `HappyStk` stk'))

happySpecReduce_3 i fn (1) tk st sts stk
     = happyFail [] (1) tk st sts stk
happySpecReduce_3 nt fn j tk _ ((_):(((_):(sts@(((st@(HappyState (action))):(_))))))) (v1`HappyStk`v2`HappyStk`v3`HappyStk`stk')
     = let r = fn v1 v2 v3 in
       happySeq r (action nt j tk st sts (r `HappyStk` stk'))

happyReduce k i fn (1) tk st sts stk
     = happyFail [] (1) tk st sts stk
happyReduce k nt fn j tk st sts stk
     = case happyDrop (k - ((1) :: Int)) sts of
         sts1@(((st1@(HappyState (action))):(_))) ->
                let r = fn stk in  -- it doesn't hurt to always seq here...
                happyDoSeq r (action nt j tk st1 sts1 r)

happyMonadReduce k nt fn (1) tk st sts stk
     = happyFail [] (1) tk st sts stk
happyMonadReduce k nt fn j tk st sts stk =
      case happyDrop k ((st):(sts)) of
        sts1@(((st1@(HappyState (action))):(_))) ->
          let drop_stk = happyDropStk k stk in
          happyThen1 (fn stk tk) (\r -> action nt j tk st1 sts1 (r `HappyStk` drop_stk))

happyMonad2Reduce k nt fn (1) tk st sts stk
     = happyFail [] (1) tk st sts stk
happyMonad2Reduce k nt fn j tk st sts stk =
      case happyDrop k ((st):(sts)) of
        sts1@(((st1@(HappyState (action))):(_))) ->
         let drop_stk = happyDropStk k stk





             _ = nt :: Int
             new_state = action

          in
          happyThen1 (fn stk tk) (\r -> happyNewToken new_state sts1 (r `HappyStk` drop_stk))

happyDrop (0) l = l
happyDrop n ((_):(t)) = happyDrop (n - ((1) :: Int)) t

happyDropStk (0) l = l
happyDropStk n (x `HappyStk` xs) = happyDropStk (n - ((1)::Int)) xs

-----------------------------------------------------------------------------
-- Moving to a new state after a reduction









happyGoto action j tk st = action j j tk (HappyState action)


-----------------------------------------------------------------------------
-- Error recovery ((1) is the error token)

-- parse error if we are in recovery and we fail again
happyFail explist (1) tk old_st _ stk@(x `HappyStk` _) =
     let i = (case x of { HappyErrorToken (i) -> i }) in
--      trace "failing" $ 
        happyError_ explist i tk

{-  We don't need state discarding for our restricted implementation of
    "error".  In fact, it can cause some bogus parses, so I've disabled it
    for now --SDM

-- discard a state
happyFail  (1) tk old_st (((HappyState (action))):(sts)) 
                                                (saved_tok `HappyStk` _ `HappyStk` stk) =
--      trace ("discarding state, depth " ++ show (length stk))  $
        action (1) (1) tk (HappyState (action)) sts ((saved_tok`HappyStk`stk))
-}

-- Enter error recovery: generate an error token,
--                       save the old token and carry on.
happyFail explist i tk (HappyState (action)) sts stk =
--      trace "entering error recovery" $
        action (1) (1) tk (HappyState (action)) sts ( (HappyErrorToken (i)) `HappyStk` stk)

-- Internal happy errors:

notHappyAtAll :: a
notHappyAtAll = error "Internal Happy error\n"

-----------------------------------------------------------------------------
-- Hack to get the typechecker to accept our action functions







-----------------------------------------------------------------------------
-- Seq-ing.  If the --strict flag is given, then Happy emits 
--      happySeq = happyDoSeq
-- otherwise it emits
--      happySeq = happyDontSeq

happyDoSeq, happyDontSeq :: a -> b -> b
happyDoSeq   a b = a `seq` b
happyDontSeq a b = b

-----------------------------------------------------------------------------
-- Don't inline any functions from the template.  GHC has a nasty habit
-- of deciding to inline happyGoto everywhere, which increases the size of
-- the generated parser quite a bit.









{-# NOINLINE happyShift #-}
{-# NOINLINE happySpecReduce_0 #-}
{-# NOINLINE happySpecReduce_1 #-}
{-# NOINLINE happySpecReduce_2 #-}
{-# NOINLINE happySpecReduce_3 #-}
{-# NOINLINE happyReduce #-}
{-# NOINLINE happyMonadReduce #-}
{-# NOINLINE happyGoto #-}
{-# NOINLINE happyFail #-}

-- end of Happy Template.

