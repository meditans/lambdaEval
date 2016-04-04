-- * Scott Encoding
-- In questo modulo andiamo a vedere l'encoding basato su case (generalmente
-- chiamato Scott encoding). Nonostante la difficolta' del tipare questo tipo di
-- termini (che richiedono tipi ricorsivi, per fix), riusciamo con questo encoding
-- a modellare in modo naturale gli schemi di ricorsione espressi in modo
-- categorico.

-- Questo accade perche' non siamo costretti a scegliere, a priori, un encoding
-- vincolato.
module ScottEncoding where

import Prelude hiding ((^), const, sum, id)

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
-- ** Anamorfismi

-- $\begin{CD}
-- F \nu \! F @<<< F C     \\
-- @AoutAA            @AAA \\
-- \nu \! F   @<<< C       \\
-- \end{CD}$

-- Analogamente a quanto abbiamo fatto con i catamorfismi, andiamo a definire gli
-- anamorfismi tramite un combinatore di punto fisso;

-- Partiamo da ana-CHARN:
-- $out \circ f = F f \circ \phi$

-- Nel nostro setting possiamo comodamente invertire, ottenendo:
-- $f = out^{-1} \circ F f \circ \phi$

-- Ovvero:
ana = p ^ (fix # (f ^ comp3 # inn # (fNat # f) # p))

-- A questo punto c'e' un unico problema: in generale il punto fisso algebrico non
-- coincide con quello coalgebrico, ad esempio per il funtore $F X = 1 + X$ abbiamo
-- sia i numeri naturali che i numeri conaturali.

-- Devo capire meglio quali sono i modi di integrare queste due visioni per i fini
-- che mi propongo.

-- ** Paramorfismi
-- Qui andiamo a questo punto a seguire il modello categorico per i paramorfismi.
-- Voglio scrivere i paramorfismi con le funzioni che userei scrivendo il sistema
-- di equazioni. Ricordiamo che:

-- $\begin{CD}
-- 1 + \mathbf{N} @>>> 1 + (C \times \mathbf{N}) @>1+\pi_2>> 1 + \mathbf{N} \\
-- @VVV                @VVV                                  @VinVV         \\
-- \mathbf{N}     @>>> C \times \mathbf{N}       @>\pi_2>>   \mathbf{N}     \\
-- @.                  @V\pi_1VV                             @.             \\
--                @. C                           @.                         \\
-- \end{CD}$

-- Questo per dire che, se voglio chiamare $g$ la freccia scritta seguendo le
-- equazioni in forma paramorfica, allora la freccia $1 + (C \times \mathbf{N})
-- \rightarrow C \times \mathbf{N}$
-- dev'essere $\langle g, in \circ T \pi_2 \rangle$.

-- Nel caso dei naturali, questo vuol dire che ho una $g$ della forma $1 + (C \times
-- \mathbf{N}) \rightarrow C$.

para = f ^ comp # pi1
                # (cata # (split # f # (comp # inn # (fNat # pi2))))

-- Questa definizione, con il punto fisso, ha invece delle buone proprieta'
-- computazionali.

paraCHARN = p ^ (fix # (f ^ comp3 # p
                                  # (fNat # (split # f # id))
                                  # out))

-- ** Apomorfismi

-- $\begin{CD}
-- F \nu\! F @<F [f,id]<< F (C + \nu\! F) \\
-- @AoutAA                @AA\phi A       \\
-- \nu\! F   @<<f<        C               \\
-- \end{CD}$

-- Questi si ottengono semplicemente dualizzando la costruzione per i catamorfismi.
-- In particolare, lo encodiamo direttamente tramite la proprieta' universale:

-- $out \circ f = F [f, id] \circ \phi \iff f = apo(\phi)$

-- Da cui, per noi che possiamo invertire:

-- $f = fix (out^{-1} \circ F [f, id] \circ \phi)$

apo = p ^ (fix # (f ^ comp3 # inn
                            # (fNat # (caseSplit # f # id))
                            # p))

-- Dovremmo a questo punto a fare un esempio di apomorfismo: la coricorsione
-- primitiva su conaturali o sulle coliste.

-- ** Histomorfismi
-- Per parlare degli histomorfismi dovremmo per prima cosa parlare delle cv-algebre.

-- Ricordiamo che dato un funtore $F$ abbiamo un funtore

-- $F^{\times} : \mathcal{C} \times \mathcal{C} \rightarrow \mathcal{C}$

-- $F^{\times}(A,X) = A \times F(X)$

-- Di conseguenza, possiamo parlare del funtore indotto:

-- $F^{\times}_A : \mathcal{C} \rightarrow \mathcal{C}$

-- che manda $X$ in $A \times F(X)$. Il punto fisso di questo funtore, come
-- coalgebra terminale, sara' $\nu F^{\times}_A$, e quindi posso definire il funtore

-- $F^{\nu} : \mathcal{C} \rightarrow \mathcal{C}$

-- $F^{\nu}(A) = \nu F^{\times}_A$

-- Nel caso dei numeri naturali, una cv-coalgebra non e' altro che una freccia
-- $1 + \nu F^{\times}_C \rightarrow C$

-- Rimandiamo l'implementazione di questo a dopo che avro' scritto il codice per
-- gli anamorfismi, visto che l'espressione libera con fix richiede l'uso degli
-- anamorfismi.


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

-- Notiamo che e' equivalente alla definizione con out:
predCataIsOut n = predCata # (ii n) === out # (ii n)
testPredCataIsOut = all predCataIsOut [0..10]

-- Proviamo a ridefinire questa funzione come paramorfismo. Come sarebbe il
-- precursore? Sul caso 0 deve ritornare const (inl unit), sull'altro e' pi2
preParaPred = caseSplit # (const # (inl # unit)) # pi2

-- da cui potremmo definire predPara = para # preParaPred, che funziona anche MA:

-- #+begin_src text
-- λ> map (\n -> nReductions $ para # preParaPred # ii n) [0..10]
-- [38,76,116,156,196,236,276,316,356,396,436]

-- λ> map (\n -> nReductions $ predCata # ii n) [0..10]
-- [28,57,87,117,147,177,207,237,267,297,327]
-- #+end_src

-- Da cui vediamo che, come ci aspettavamo, la performance del paramorfismo e' un
-- poco peggiore, ma inoltre non si ferma asintoticamente. AAAARGH! COME MAI!
-- Dipende dal fatto che le funzioni che sto usando per valutare questo lambda
-- calcolo non sono abbastanza lazy?

-- Questa cosa potrebbe migliorare se invece di codificare esplicitamente il
-- paramorfismo tramite il catamorfismo utilizzassimo =para-CHARN= per definirlo
-- direttamente con un punto fisso?

-- Si, implementando paraCHARN (vedi sopra)

-- A questo punto si ha che:
-- #+begin_src text
-- λ> map (\n -> nReductions $ paraCHARN # preParaPred # ii n) [0..10]
-- [27,32,32,32,32,32,32,32,32,32,32]
-- #+end_src

-- Quindi praticamente in questo caso siamo riusciti a riportare il nostro count ad
-- essere indipendente dalla grandezza dell'input. Questo in effetti avviene
-- perche' non stiamo costringendo la computazione a passare dal collo di bottiglia
-- del paramorfismo, ma semplicemente la stiamo definendo direttamente con il punto
-- fisso.

-- ** TODO Pensare a qualcosa per fare vedere che i catamorfismi migliorano.
  
