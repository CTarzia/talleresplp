import Data.List
import Test.HUnit
import Midi.Midi

type Tono         = Integer
type Duracion     = Integer
type Instante     = Integer

data Melodia = 
     Silencio Duracion |
     Nota Tono Duracion |
     Secuencia Melodia Melodia | 
     Paralelo [Melodia]
  deriving Show

-- Funciones auxiliares dadas

foldNat :: a->(a->a)->Integer->a
foldNat caso0 casoSuc n | n == 0 = caso0
      | n > 0 = casoSuc (foldNat caso0 casoSuc (n-1))
      | otherwise = error "El argumento de foldNat no puede ser negativo."

-- Funciones pedidas

-- Ejercicio 1
superponer :: Melodia->Duracion->Melodia->Melodia
superponer m1 ds m2 = Paralelo [m1, (Secuencia (Silencio ds) m2)]

-- Sugerencia: usar foldNat
canon :: Duracion->Integer->Melodia->Melodia
canon ds repeticiones m = foldNat m (superponer m ds) (repeticiones-1)

-- ??
secuenciar :: [Melodia] -> Melodia--Se asume que la lista no es vacía.
secuenciar (m:ms) = foldl (\x rec -> Secuencia x rec) m ms 

-- Ejercicio 2

canonInfinito :: Duracion->Melodia->Melodia
canonInfinito ds m = foldr (\x rec -> Paralelo [x,(Secuencia (Silencio ds) rec)]) m (repeat m)

-- Ejercicio 3
foldMelodia :: (Duracion -> b) -> --caso silencio
               (Tono -> Duracion -> b) -> -- caso nota
               (b -> b -> b) -> --caso secuencia
               ([b] -> b) -> --caso paralelo
               Melodia -> b
foldMelodia cSil cN cSec cP m = case m of
                                (Silencio d) -> cSil d
                                (Nota t d) -> cN t d
                                (Secuencia m1 m2) -> cSec (rec m1) (rec m2)
                                (Paralelo l) -> cP (map rec l)
                where rec = foldMelodia cSil cN cSec cP

-- Ejercicio 4

mapMelodia :: (Tono -> Tono)->Melodia->Melodia
mapMelodia f = foldMelodia Silencio cNota Secuencia Paralelo
        where cNota = (\t d-> Nota (f t) d)

transportar :: Integer -> Melodia -> Melodia
transportar n = mapMelodia (\t -> t+n)

duracionTotal :: Melodia->Duracion
duracionTotal = foldMelodia cSil cN cSec cP
               where cSil = (\d -> d)
                     cN = (\t d -> d)
                     cSec = (\m1 m2 -> m1 + m2)
                     cP = (\l -> maximum l)

cambiarVelocidad :: Float->Melodia->Melodia--Sugerencia: usar round y fromIntegral
cambiarVelocidad factor = foldMelodia cSil cN Secuencia Paralelo
               where multiplicarFactor i = round ((fromIntegral i) * factor)
                     cSil = (\d -> Silencio (multiplicarFactor d))
                     cN = (\t d -> Nota t (multiplicarFactor d))

invertir :: Melodia -> Melodia
invertir = foldMelodia Silencio Nota cSec Paralelo
               where cSec = (\m1 m2 -> Secuencia m2 m1)

-- Ejercicio 5
-- En instantes menores que 0 no suena ninguna nota. Se puede usar recursión explícita. Resaltar las partes del código que hacen que no se ajuste al esquema fold.
notasQueSuenan :: Instante->Melodia->[Tono]
--Sugerencia: usar concatMap.
notasQueSuenan i m | (i < 0) = []
notasQueSuenan i (Silencio d) = []
notasQueSuenan i (Nota t d) = if (i < d) then [t] else []
notasQueSuenan i (Secuencia m1 m2) = (notasQueSuenan i m1) ++ (notasQueSuenan (i - (duracionTotal m1)) m2)
notasQueSuenan i (Paralelo l) = concatMap (notasQueSuenan i) l

{- No se puede definir notasQueSuenan usando el esquema de recursion foldMelodia porque al tener que hacer el 
llamado recursivo en los casos de Secuencia y Paralelo se perderia el contexto, particularmente el valor de i.
-}
{- 
  -}

-- Ejercicio 6

data Evento = On Instante Tono | Off Instante Tono deriving (Show, Eq)

--Sugerencia: usar listas por comprensión. No repetir eventos.
cambios :: Instante->[Tono]->[Tono]->[Evento]
cambios = undefined

--Sugerencia: usar foldl sobre la lista de 0 a la duración.
eventosPorNotas :: (Instante->[Tono])->Duracion->[Evento]
eventosPorNotas = undefined

eventos :: Melodia -> Duracion -> [Evento]
eventos = undefined

-- GENERADOR

unev (On i x)  = (i, Left x)
unev (Off i x) = (i, Right x)

generarMidi :: String -> [Evento] -> IO ()
generarMidi archivo eventos = midiCreateFile archivo midiEvents
  where
    eventos' = let e = map unev eventos in zipWith (\(t0, _) (t1, e) -> (t1 - t0, e)) ((0, error ""):e) e
    midiEvents = case eventos' of
                   [] -> [midiNoteOn 1 0 0 10, midiNoteOn 1 0 0 0]
                   es -> toMidi es

toMidi = map (\(d, ev) -> case ev of
                Left  n -> midiNoteOn d 0 n 127
                Right n -> midiNoteOn d 0 n 0)

--Notas para pruebas.

_sol0 = Nota 55
_si0  = Nota 59
_do = Nota 60
_reb  = Nota 61
_re = Nota 62
_mib  = Nota 63
_mi = Nota 64
_fa = Nota 65
_fas  = Nota 66
_sol = Nota 67
_lab  = Nota 68
_la = Nota 69
_sib  = Nota 70
_si = Nota 71
_do2  = Nota 72
_reb2 = Nota 73
_re2  = Nota 74
_mib2 = Nota 75
_fa2  = Nota 77

-- Melodías para pruebas.

acorde :: Melodia
acorde = Paralelo [_do 10, Secuencia (Silencio 3) (_mi 7), Secuencia (Silencio 6) (_sol 4)]

doremi :: Melodia
doremi = secuenciar [_do 3, _re 1, _mi 3, _do 1, _mi 2, _do 2, _mi 4]

-- Pongan sus propias pruebas y melodías. Pueden definir más notas, la numeración es por semitonos.

-- Canon APL (autor: Pablo Barenbaum)

rhoRhoRhoOfX, alwaysEqualsOne, rhoIsDimensionRhoRhoRank, aplIsFun :: Melodia
rhoRhoRhoOfX = secuenciar $ map (\(d, f)->f d) [(4, _do), (4, _do), (3, _do), (1, _re), (4, _mi)]
alwaysEqualsOne = secuenciar $ map (\(d, f)->f d) [(3, _mi), (1, _re), (3, _mi), (1, _fa), (8, _sol)]
rhoIsDimensionRhoRhoRank = secuenciar $ map (\(d, f)->f d) [(12, _do2), (12, _sol), (12, _mi), (12, _do)]
aplIsFun = secuenciar $ map (\(d, f)->f d) [(3, _sol), (1, _fa), (3, _mi), (1, _re), (8, _do)]

mezcla :: Melodia
mezcla = Paralelo [rhoRhoRhoOfX, Secuencia (Silencio 4) alwaysEqualsOne, Secuencia (Silencio 8) rhoIsDimensionRhoRhoRank, Secuencia (Silencio 12) aplIsFun]

-- Cangrejo (autor: Pablo Barenbaum)

stac :: Tono -> Melodia
stac t = Secuencia (Nota t 9) (Silencio 1)

stacatto :: Melodia -> Melodia
stacatto = foldMelodia Silencio (\t d->stac t) Secuencia Paralelo

cangrejo1 = secuenciar $ 
         [Silencio 4, _do 2, _mib 2]
      ++ [_sol 2, _lab 4, Silencio 2]
      ++ [_si0 4, Silencio 2, _sol 4] 
      ++ [_fas 4, _fa 4]              
      ++ [_mi 2, Silencio 2, _mib 4]  
      ++ [_re 2, _reb 2, _do 2]
      ++ [_si0 2, _sol0 2, _do 2, _fa 2]
      ++ [_mib 2, _re 4, Silencio 2]
      ++ [_do 2, _mi 2, Silencio 4]
cangrejo2 = secuenciar $ (map (\(d, f)->f d)) $
               [(2, _do), (2, _mib), (2, _sol), (2, _do2)]
            ++ [(1, _sib), (1, _do2), (1, _re2), (1, _mib2),
                (1, _fa2), (1, _mib2), (1, _re2), (1, _do2)]
            ++ [(1, _re2), (1, _sol), (1, _re2), (1, _fa2),
                (1, _mib2), (1, _re2), (1, _do2), (1, _si)]
            ++ [(1, _la), (1, _si), (1, _do2), (1, _mib2),
                (1, _re2), (1, _do2), (1, _si), (1, _la)]
            ++ [(1, _sol), (1, _lab), (1, _sib), (1, _reb2),
                (1, _do2), (1, _sib), (1, _lab), (1, _sol)]
            ++ [(1, _fa), (1, _sol), (1, _lab), (1, _sib),
                (1, _lab), (1, _sol), (1, _fa), (1, _mib)]
            ++ [(1, _re), (1, _mib), (1, _fa), (1, _sol),
                (1, _fa), (1, _mib), (1, _re), (1, _lab)]
            ++ [(1, _sol), (1, _fa), (1, _mib), (1, _do2),
                (1, _si), (1, _la), (1, _sol), (1, _fa)]
            ++ [(1, _mi), (1, _re), (1, _mi), (1, _sol),
                (1, _do2), (1, _sol), (1, _fa), (1, _sol)]
                
cangrejo = Secuencia c (invertir c)
  where c = Paralelo [cangrejo1, cangrejo2]

--

genMelodia :: String -> Melodia -> Duracion -> IO ()
genMelodia fn m dur = generarMidi fn (eventos m dur)

main :: IO ()
main = do
   putStr "Generando apl-is-fun.mid...\n"
   genMelodia "apl-is-fun.mid" (stacatto mezcla) 500
   putStr "Generando cangrejo.mid...\n"
   genMelodia "cangrejo.mid" (stacatto cangrejo) 1000

-- Tests
tests :: IO Counts
tests = do runTestTT allTests

allTests = test [
  "ejercicio1" ~: testsEj1,
  "ejercicio2" ~: testsEj2,
  "ejercicio3" ~: testsEj3,
  "ejercicio4" ~: testsEj4,
  "ejercicio5" ~: testsEj5,
  "ejercicio6" ~: testsEj6
  ]

-- Ejemplos sólo para mostrar cómo se escriben los tests. Reemplazar por los tests propios.

otroAcorde :: Melodia
otroAcorde = Paralelo [Secuencia (Silencio 2) (_fa2 8),_do 5,  Secuencia (Silencio 5) (_reb2 9)]

silencio = Silencio 1
notaDo = Nota 60 1
dore = Secuencia (Nota 60 1) (Nota 61 1)
doremiParalelo = Paralelo([Nota 60 1, Secuencia (Nota 60 1) (Nota 61 1), Nota 62 1])

transformarACero :: Melodia -> Melodia
transformarACero = foldMelodia cSil cN Secuencia Paralelo
               where cSil = (\d -> Silencio 0)
                     cN = (\t d -> Nota 0 0)

muchasSecuencias :: Melodia
muchasSecuencias = Paralelo [ Secuencia (Silencio 1) (Nota 1 1),
                             Secuencia (Nota 2 2) (Silencio 2) ,
                             Secuencia (Silencio 3) (Nota 3 3),
                             Secuencia (Nota 4 4) (Silencio 4)]

testsEj1 = test [
  --guido superponer

 --canon
  show (Paralelo [Nota 60 4,Secuencia (Silencio 2) (Paralelo [Nota 60 4, Secuencia (Silencio 2) (Nota 60 4)])]) ~=? (show (canon 2 3 (Nota 60 4))),
  show (Paralelo [Paralelo [Nota 60 10,Secuencia (Silencio 3) (Nota 64 7),Secuencia (Silencio 6) (Nota 67 4)],Secuencia (Silencio 1) (Paralelo [Nota 60 10,Secuencia (Silencio 3) (Nota 64 7),Secuencia (Silencio 6) (Nota 67 4)])]) ~=? (show (canon 1 2 acorde)),
  show (Paralelo [Secuencia (Nota 60 9) (Silencio 1),Secuencia (Silencio 3) (Secuencia (Nota 60 9) (Silencio 1))]) ~=? show (canon 3 2 (stac 60)),
  
  show (Secuencia (Secuencia (Nota 60 1) (Nota 60 2))(Nota 60 3)) ~=? show(secuenciar [Nota 60 1, Nota 60 2, Nota 60 3])
  --martin arregla: show (Secuencia (acorde, Secuencia (acorde, otroAcorde)) ) ~=? show(secuenciar [acorde, acorde, otroAcorde])
  ]
testsEj2 = test [
  --todos
  2 ~=? 1+1,
  4 ~=? 2*2
  ]
testsEj3 = test [
  --chiara
  show acorde ~=? show (foldMelodia Silencio Nota Secuencia Paralelo acorde),
  show (Paralelo [Nota 0 0,Secuencia (Silencio 0) (Nota 0 0),Secuencia (Silencio 0) (Nota 0 0)]) ~=? show (transformarACero acorde)
  ]
testsEj4 = test [
  --guido mapmelodia transportar y duraciontotal
  --chiara cambiarvelocidad invertir
  2 ~=? 1+1,
  --cambiarVelocidad
  show (Paralelo [Nota 60 20,Secuencia (Silencio 6) (Nota 64 14),Secuencia (Silencio 12) (Nota 67 8)]) ~=? show (cambiarVelocidad 2 acorde),
  show (Secuencia (Secuencia (Secuencia (Secuencia (Secuencia (Secuencia (Nota 60 0) (Nota 62 0)) (Nota 64 0)) (Nota 60 0)) (Nota 64 0)) (Nota 60 0)) (Nota 64 0)) ~=? show (cambiarVelocidad 0 doremi),
  --invertir
  show (Paralelo [Secuencia (Nota 1 1) (Silencio 1),Secuencia (Silencio 2) (Nota 2 2),Secuencia (Nota 3 3) (Silencio 3),Secuencia (Silencio 4) (Nota 4 4)]) ~=? show (invertir muchasSecuencias),
  show (Paralelo [(Silencio 1), (Silencio 2), (Silencio 3)]) ~=? show (invertir (Paralelo [(Silencio 1), (Silencio 2), (Silencio 3)]))
  ]
testsEj5 = test [
  --martin
  2 ~=? 1+1,
  2 ~=? 1+1,
  2 ~=? 1+1,
  2 ~=? 1+1,
  2 ~=? 1+1,
  2 ~=? 1+1,
  4 ~=? 2*2
  ]
testsEj6 = test [
  2 ~=? 1+1,
  4 ~=? 2*2
  ]