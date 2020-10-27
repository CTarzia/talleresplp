module TypeInference (TypingJudgment, Result(..), inferType, inferNormal, normalize)

where

import Data.List(intersect, union, nub, sort)
import Exp
import Type
import Unification

------------
-- Errors --
------------
data Result a = OK a | Error String


--------------------
-- Type Inference --
--------------------
type TypingJudgment = (Context, AnnotExp, Type)

typeVarsT :: Type -> [Int]
typeVarsT = foldType (:[]) [] [] union id

typeVarsE :: Exp Type -> [Int]
typeVarsE = foldExp (const []) [] id id id [] [] (\r1 r2 r3 ->nub(r1++r2++r3)) (const setAdd) union typeVarsT union (\r1 r2 _ _ r3->nub(r1++r2++r3))
  where setAdd t r = union (typeVarsT t) r

typeVarsC :: Context -> [Int]
typeVarsC c = nub (concatMap (typeVarsT . evalC c) (domainC c))

typeVars :: TypingJudgment -> [Int]
typeVars (c, e, t) = sort $ union (typeVarsC c) (union (typeVarsE e) (typeVarsT t))

normalization :: [Int] -> [Subst]
normalization ns = foldr (\n rec (y:ys) -> extendS n (TVar  y) emptySubst : (rec ys)) (const []) ns [0..]

normalize :: TypingJudgment -> TypingJudgment
normalize j@(c, e, t) = let ss = normalization $ typeVars j in foldl (\(rc, re, rt) s ->(s <.> rc, s <.> re, s <.> rt)) j ss
  
inferType :: PlainExp -> Result TypingJudgment
inferType e = case infer' e 0 of
    OK (_, tj) -> OK tj
    Error s -> Error s
    
inferNormal :: PlainExp -> Result TypingJudgment
inferNormal e = case infer' e 0 of
    OK (_, tj) -> OK $ normalize tj
    Error s -> Error s


infer' :: PlainExp -> Int -> Result (Int, TypingJudgment)

infer' (SuccExp e)    n = case infer' e n of
                            OK (n', (c', e', t')) ->
                              case mgu [(t', TNat)] of
                                UOK subst -> OK (n',
                                                    (
                                                     subst <.> c',
                                                     subst <.> SuccExp e',
                                                     TNat
                                                    )
                                                )
                                UError u1 u2 -> uError u1 u2
                            res@(Error _) -> res

-- COMPLETAR DESDE AQUI

infer' ZeroExp                n = OK (n , (emptyContext, ZeroExp, TNat))
infer' (VarExp x)             n = OK (n+1, 
                                        (
                                          extendC emptyContext x (TVar n), 
                                          VarExp x,
                                          TVar n
                                        )
                                      )
                                
infer' (AppExp u v)           n = case infer' u n of
                                    OK (n1', (c1', e1', t1')) ->
                                      case infer' v n1' of 
                                        OK (n2', (c2', e2', t2')) ->
                                          case mgu ((t1', (TFun t2' (TVar n2'))) : (checkContexts c1' c2')) of
                                            UOK subst -> OK (n2'+1, 
                                                                    (
                                                                      joinC [subst <.> c1', subst <.> c2'],
                                                                      subst <.> AppExp e1' e2',
                                                                      subst <.> (TVar n2')
                                                                    )
                                                            )
                                            UError u1 u2 -> uError u1 u2
                                        res2@(Error _) -> res2  
                                    res1@(Error _) -> res1

infer' (LamExp x _ e)         n = case infer' e n of
                                    OK (n', (c', e', t')) ->
                                      OK ((if (variableIsInGamma c' x) then n' else n'+1),
                                            (
                                              removeC c' x,
                                              LamExp x (evalOrNew c' x n') e',
                                              TFun (evalOrNew c' x n') t'
                                            )
                                          )
                                    res@(Error _) -> res

-- OPCIONALES

infer' (PredExp e)            n = case infer' e n of
                                    OK (n', (c', e', t')) ->
                                      case mgu [(t', TNat)] of
                                        UOK subst -> OK (n',
                                                            (
                                                            subst <.> c',
                                                            subst <.> PredExp e',
                                                            TNat
                                                            )
                                                        )
                                        UError u1 u2 -> uError u1 u2
                                    res@(Error _) -> res

infer' (IsZeroExp e)          n = case infer' e n of
                                    OK (n', (c', e', t')) ->
                                      case mgu [(t', TNat)] of
                                        UOK subst -> OK (n',
                                                            (
                                                            subst <.> c',
                                                            subst <.> IsZeroExp e',
                                                            TBool
                                                            )
                                                        )
                                        UError u1 u2 -> uError u1 u2
                                    res@(Error _) -> res

infer' TrueExp                n = OK (n , (emptyContext, TrueExp, TBool))
infer' FalseExp               n = OK (n , (emptyContext, FalseExp, TBool))
infer' (IfExp u v w)          n = case infer' u n of
                                    OK (n1', (c1', e1', t1')) ->
                                      case infer' v n of
                                        OK (n2', (c2', e2', t2')) ->
                                          case infer' w n of
                                            OK (n3', (c3', e3', t3')) ->
                                              case mgu ([(t2', t3'), (t1', TBool)] ++ (checkThreeContexts c1' c2' c3')) of
                                                UOK subst -> OK (n3', 
                                                                  (
                                                                    joinC [subst <.> c1', subst <.> c2', subst <.> c3'],
                                                                    subst <.> IfExp e1' e2' e3',
                                                                    t2'
                                                                  )
                                                                )
                                                UError u1 u2 -> uError u1 u2
                                            res3@(Error _) -> res3
                                        res2@(Error _) -> res2
                                    res1@(Error _) -> res1

-- EXTENSIÓN

infer' (EmptyListExp _)       n = OK (n+1 , (emptyContext, EmptyListExp (TVar n), TList (TVar n)))
infer' (ConsExp u v)          n = case infer' u n of
                                    OK (n1', (c1', e1', t1')) ->
                                      case infer' v n1' of 
                                        OK (n2', (c2', e2', t2')) ->
                                          case mgu ((t2', TList t1') : (checkContexts c1' c2')) of
                                            UOK subst -> OK (n2', (
                                                                    joinC [subst <.> c1', subst <.> c2'],
                                                                    subst <.> ConsExp e1' e2',
                                                                    subst <.> (TList t1')
                                                                  )
                                                            )
                                            UError u1 u2 -> uError u1 u2
                                        res2@(Error _) -> res2  
                                    res1@(Error _) -> res1
infer' (ZipWithExp u v x y w) n = case infer' u n of
                                    OK (n1', (c1', e1', t1')) ->
                                      case infer' v n1' of 
                                        OK (n2', (c2', e2', t2')) ->
                                          case infer' w n2' of
                                            OK (n3', (c3', e3', t3')) ->
                                              case mgu ((t1', TList (evalOrNew c3' x n3')) : (t2', TList (evalOrNew c3' y (if variableIsInGamma c3' x then n3' else n3'+1))) : checkThreeContexts c1' c2' (removeXAndY c3')) of
                                                UOK subst -> OK (n3', (
                                                                        joinC [subst <.> c1', subst <.> c2', subst <.> (removeXAndY c3')],
                                                                        subst <.> ZipWithExp e1' e2' x y e3',
                                                                        subst <.> TList t3'
                                                                      )
                                                                )
                                                UError u1 u2 -> uError u1 u2
                                            res3@(Error _) -> res3
                                        res2@(Error _) -> res2  
                                    res1@(Error _) -> res1
                                where removeXAndY c = removeC (removeC c x) y

evalOrNew :: Context -> Symbol -> Int -> Type
evalOrNew c s n = (if (variableIsInGamma c s) then evalC c s else TVar n)

variableIsInGamma :: Context -> Symbol -> Bool
variableIsInGamma c s = elem s (domainC c)

listType :: Type -> Type
listType (TList t) = t
--------------------------------
-- YAPA: Error de unificacion --
--------------------------------
uError :: Type -> Type -> Result (Int, a)
uError t1 t2 = Error $ "Cannot unify " ++ show t1 ++ " and " ++ show t2

checkContexts :: Context -> Context -> [UnifGoal]
checkContexts c1 c2 = map (\s -> (evalC c1 s, evalC c2 s)) intersection
                     where intersection = intersect (domainC c1) (domainC c2)

checkThreeContexts :: Context -> Context -> Context -> [UnifGoal]
checkThreeContexts c1 c2 c3 = checkContexts c1 c2 ++ checkContexts c2 c3 ++ checkContexts c1 c3