-- * Scott Encoding
-- In questo modulo andiamo a vedere l'encoding basato su case (generalmente
-- chiamato Scott encoding). Nonostante la difficolta' del tipare questo tipo di
-- termini (che richiedono tipi ricorsivi, per fix), riusciamo con questo encoding
-- a modellare in modo naturale gli schemi di ricorsione espressi in modo
-- categorico.

-- Questo accade perche' non siamo costretti a scegliere, a priori, un encoding
-- vincolato.
module ScottEncoding where

import Prelude hiding ((^), const, sum)

import Lib
import Common

-- Definiamo i numeri naturali con lo scott encoding:
i0 = z ^ s ^ z
suc = n ^ z ^ s ^ s # n

-- Definisco per convenienza altre costanti:
i1 = eval $ suc # i0
i2 = eval $ suc # i1
i3 = eval $ suc # i2
i4 = eval $ suc # i3
i5 = eval $ suc # i4
i6 = eval $ suc # i5

-- E una funzione per generare i lambda termini di un numero di peano arbitrario
-- (es. ~ii 3~ genera lo Scott encoding di ~3~).
is = i0 : map (\t -> eval $ suc # t) is
ii n = is !! n

-- Per comodita' enunciamo la funzione che esegue lo split, che e' ovviamente
-- l'identita', dato che questo e' il comportamento computazionale che volevamo
-- catturare con il nostro encoding.
natCase = (z ^ z)

-- A questo punto, possiamo definire con facilita' le due frecce dell'isomorfismo
-- dell'algebra dei naturali (Intendo ~1+Nat -> Nat~): il case-split infatti ci
-- consente di definire in modo ovvio cosa vuol dire tornare indietro.
inn = caseSplit # (const # i0) # suc
out = n ^ n # (inl # unit) # inr

-- Il combinatore di punto fisso (stare attento alle parentesi)
fix = f ^ (x ^ f # (x # x)) # (x ^ f # (x # x))

-- Lifting di una funzione nel funtore dei naturali. Questo schema di traduzione si
-- puo' estendere a funtori arbitrari.
fNat = f ^ funPlus # (i ^ i) # f

-- ** Catamorfismi
-- Questa e' la ricetta generale del catamorfismo: notare come ricalca il
-- corrispondente diagramma categoriale.
cata = p ^ (fix # (f ^ comp3 # p # (fNat # f) # out))

-- ** Paramorfismi
-- Qui andiamo a questo punto a seguire il modello categorico per i paramorfismi.

-- Diciamo che voglio scrivere i paramorfismi con le funzioni che userei quando
-- vado a scrivere il sistema di equazioni. Questo perche' voglio che in seguito la
-- chiamata di queste funzioni di alto livello si mantenga vicina a quanto dico
-- appunto con le equazioni.

-- #+BEGIN_SRC text
--                                      1 + pi2
-- 1 + Nat  --------->  1 + C x Nat   ---------> 1 + Nat
--    |                      |                      |
--    |                      |                      | in
--    v                      v           pi2        v
--   Nat    --------->    C x Nat     --------->   Nat
--                           |
--                           | pi1
--                           v
--                           C
-- #+END_SRC

-- Questo per dire che, se voglio chiamare ~g~ la freccia scritta seguendo le
-- equazioni in forma paramorfica, allora la freccia da ~1 + C Nat~ a ~C Nat~
-- dev'essere ~<g, in . T pi2>~.

-- Nel caso dei naturali, questo vuol dire che ho una ~g~ della forma ~1 + C Nat ->
-- C~.

para = f ^ comp # pi1
                # (cata # (split # f # (comp # inn # (fNat # pi2))))

-- * Case studies
-- ** Case study: la funzione (*2)
-- Questo e' l'ingrediente catamorfico
preCataDouble = caseSplit # (const # i0) # (comp # suc # suc)
-- Quindi il modo di scrivere questa funzione sarebbe ~cata preCataDouble~.

-- ** Case study: le funzioni (+) e (*)
-- Possiamo definire molto semplicemente somme e prodotti
sum  = n ^ m ^ (cata # (caseSplit # (const # n) # suc)) # m
prod = n ^ m ^ (cata # (caseSplit # (const # i0) # (sum # n))) # m

-- ** Case Study: la funzione predecessore
-- Questa e' la definizione del predecessore come catamorfismo:
predCata = cata # (fNat # inn)

-- Proviamo a ridefinire questa funzione come paramorfismo. Come sarebbe il
-- precursore? Sul caso 0 deve ritornare const (inl unit), sull'altro e' pi2
preParaPred = caseSplit # (const # (inl # unit)) # pi2

-- Notiamo che e' equivalente alla definizione con out:
predCataIsOut n = predCata # (ii n) === out # (ii n)
testPredCataIsOut = all predCataIsOut [0..10]

-- *** TODO Aggiungere i risultati sul numero di riduzioni
-- Naturalmente qui e' anche interessante porsi il problema di come varia nei due
-- casi il numero di riduzioni. E' ovvio che in un caso crescano con il crescere
-- del numero, nell'altro no.

-- ** TODO Pensare a qualcosa per fare vedere che i catamorfismi migliorano.
