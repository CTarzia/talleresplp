module Exp (Exp(..), PlainExp, AnnotExp, recExp, foldExp)
where

import Type

data Exp a = VarExp Symbol |
             ZeroExp |
             SuccExp (Exp a)|
             PredExp (Exp a) |
             IsZeroExp (Exp a) |
             TrueExp |
             FalseExp |
             IfExp (Exp a) (Exp a) (Exp a) |
             LamExp Symbol a (Exp a) |
             AppExp (Exp a) (Exp a) |
             EmptyListExp a |
             ConsExp (Exp a) (Exp a) |
             ZipWithExp (Exp a) (Exp a) Symbol Symbol (Exp a) deriving Show

type PlainExp = Exp ()
type AnnotExp = Exp Type

instance Substitutable a => Substitutable (Exp a) where
    (<.>) subst = foldExp VarExp
                          ZeroExp
                          SuccExp
                          PredExp
                          IsZeroExp
                          TrueExp
                          FalseExp
                          IfExp
                          (\x t e -> LamExp x (subst <.> t) e)
                          AppExp
                          (\t -> EmptyListExp (subst <.> t))
                          ConsExp
                          ZipWithExp

recExp :: (Symbol -> a)
               -> a
               -> (Exp b -> a -> a)
               -> (Exp b -> a -> a)
               -> (Exp b -> a -> a)
               -> a
               -> a
               -> (Exp b -> Exp b -> Exp b -> a -> a -> a -> a)
               -> (Exp b -> Symbol -> b -> a -> a)
               -> (Exp b -> Exp b -> a -> a -> a)
               -> (b -> a)
               -> (Exp b -> Exp b -> a -> a -> a)
               -> (Exp b -> Exp b -> Exp b -> a -> a -> Symbol -> Symbol -> a -> a)
               -> Exp b -> a
recExp fVar fZero fSucc fPred fIsZero fTrue fFalse fIf fLam fApp fEmpty fCons fZip e =
  case e of
    VarExp x                -> fVar x
    ZeroExp                 -> fZero
    SuccExp e'              -> fSucc e' $ rec e'
    PredExp e'              -> fPred e' $ rec e'
    IsZeroExp e'            -> fIsZero e' $ rec e'
    TrueExp                 -> fTrue
    FalseExp                -> fFalse
    IfExp e1 e2 e3          -> fIf e1 e2 e3 (rec e1) (rec e2) (rec e3)
    LamExp x b e'           -> fLam e' x b $ rec e'
    AppExp e1 e2            -> fApp e1 e2 (rec e1) (rec e2)
    EmptyListExp b          -> fEmpty b
    ConsExp e1 e2           -> fCons e1 e2 (rec e1) (rec e2)
    ZipWithExp e1 e2 x y e3 -> fZip e1 e2 e3 (rec e1) (rec e2) x y (rec e3)
  where rec = recExp fVar fZero fSucc fPred fIsZero fTrue fFalse fIf fLam fApp fEmpty fCons fZip

foldExp :: (Symbol -> a)
           -> a
           -> (a -> a)
           -> (a -> a)
           -> (a -> a)
           -> a
           -> a
           -> (a -> a -> a -> a)
           -> (Symbol -> b -> a -> a)
           -> (a -> a -> a)
           -> (b -> a)
           -> (a -> a -> a)
           -> (a -> a -> Symbol -> Symbol -> a -> a)
           -> Exp b -> a
foldExp fVar fZero fSucc fPred fIfZero fTrue fFalse fIf fLam fApp fEmpty fCons fZip =
    recExp fVar fZero (const fSucc) (const fPred) (const fIfZero) fTrue fFalse
                (const $ const $ const fIf) (const fLam) (const $ const fApp)
                fEmpty (const $ const fCons) (const $ const $ const fZip)
