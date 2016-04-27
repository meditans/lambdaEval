{-# LANGUAGE RankNTypes #-}
{-# OPTIONS_GHC -fdefer-typed-holes #-}
-- * Scott Encoding
-- In questo modulo andiamo a vedere l'encoding basato su case (generalmente
-- chiamato Scott encoding). Nonostante la difficolta' del tipare questo tipo di
-- termini (che richiedono tipi ricorsivi, per fix), riusciamo con questo encoding
-- a modellare in modo naturale gli schemi di ricorsione espressi in modo
-- categorico.

-- Questo accade perche' non siamo costretti a scegliere, a priori, un encoding
-- vincolato.

-- ** Preliminari
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
-- F \nu \! F @<F f<< F C       \\
-- @AoutAA            @AA\phi A \\
-- \nu \! F   @<<f< C           \\
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

-- L'approccio che seguo adesso e' la codifica dei tipi coalgebrici seguendo gli
-- "Scott encoding per codata" cosi' come suggeriti da Geuvers: consideriamo in
-- particolare l'encoding degli stream, visto che era quello su cui trovavo piu'
-- difficolta'. Sappiamo che possiamo codificare uno stream di $A$ equivalentemente
-- come:

-- $Str_A = \mu \beta . \exists \alpha . \alpha \times (\alpha \rightarrow A) \times (\alpha \rightarrow \beta)$
-- $Str_A = \exists \alpha . \alpha \times (\alpha \rightarrow A) \times (\alpha \rightarrow Str_A)$
-- $Str_A = \forall \gamma . (\forall \alpha . \alpha \times (\alpha \rightarrow A) \times (\alpha \rightarrow Str_A) \rightarrow \gamma) \rightarrow \gamma$

-- Usando la traduzione standard degli esistenziali, che viene accennata alla fine
-- del paper di Geuvers, ma trovo piu' utile pensare come una generalizzazione del
-- currying: $\exists \alpha.A$ e' un particolare $\tilde{\alpha}$ mentre $\forall \alpha.A$ e' una funzione sui tipi.

-- - [ ] espandere meglio sulla traduzione standard

-- Il problema che si poneva allora era come generare un termine di tipo $Str_A$,
-- cosa che io trovavo difficile per via del non riuscire a scrivere un termine di
-- tipo $\alpha \rightarrow Str_A$.

-- L'intuizione che voglio testare adesso e' il funzionamento di un trucco, di
-- cui costruisco per prima cosa il corrispettivo in haskell; purtroppo notiamo
-- che in haskell siamo costretti a dare una presentazione isoricorsiva di
-- questo fatto, mentre per comodita' di scrittura nel caso generale terremo la
-- versione equiricorsiva.

newtype Stream o = Stream (forall g. (forall a.
  (a, a -> o, a -> Stream o) -> g) -> g)

stream :: a -> (a -> o) -> (a -> a) -> Stream o
stream seed extract update = Stream $
  \f -> f ( seed
          , extract
          , (\i -> stream (update i) extract update)
          )

naturals :: Stream Integer
naturals = stream 0 (\x->x) succ

-- La morale della favola e' questa, sono riuscito a creare un costruttore del
-- termine che mi serviva, sostituendo il termine problematico che avevo $\alpha \rightarrow Str_A$,
-- con un piu' ovvio $\alpha \rightarrow \alpha$, che parla in modo diretto del seed, utilizzando in fondo
-- un combinatore di punto fisso.

-- notiamo che il pattern del costruttore e':

-- $stream \; s \; e \; u = \lambda f. f \; s \; e \; (\lambda i. stream \; (u \; i) \; e \; u)$

-- - [ ] Capire come questo si mette a posto secondo lo schema dei costruttori di
--   Geuvers.

-- Possiamo parlare a questo punto dell'analogo per i numeri naturali, ovvero per
-- il funtore $F X = 1 + X$.

-- Sappiamo che questo da origine ai numeri CoNaturali, che dovrebbero quindi
-- essere definiti equivalentemente come:

-- $CoNat = \mu \beta. \forall \alpha. \alpha \times (\alpha \rightarrow 1 + \beta)$
-- $CoNat = \forall \alpha. \alpha \times (\alpha \rightarrow 1 + CoNat)$
-- $CoNat = \forall \gamma. (\forall \alpha. \alpha \times (\alpha \rightarrow 1 + CoNat) \rightarrow \gamma) \rightarrow \gamma$

-- Ricordiamo che Geuvers suggerisce che se i codata sono encodati in $\lambda 2 \mu$ come:
-- $\underline{D} = \mu \beta. \exists \alpha. \alpha \times (\alpha \rightarrow T^1(\beta)) \times \dots \times (\alpha \rightarrow T^n(\beta))$

-- allora il generico distruttore $\underline{D_i} : \underline{D} \rightarrow T^i(\underline{D})$ e' encodato da:
-- $\underline{D_i} \; s = s \; (\lambda p.(\pi_{i+1} \; p) \; (\pi_1 \; p))$

-- Nel mio caso, il distruttore sarebbe encodato da:
-- $D \; s = s \; (\lambda p. \pi_2 \; p \; (\pi_1 \; p))$

-- Abbiamo allora che:

newtype CoNatural = CoNatural (forall g. (forall a. (a, a -> Either () CoNatural) -> g) -> g)

conatural :: a -> (a -> Either () a) -> CoNatural
conatural seed a2Eua = CoNatural $ \f -> f (seed, \i -> fmap (\a -> conatural a a2Eua) (a2Eua i))

infinite :: CoNatural
infinite = conatural 0 Right

conaturalN :: Int -> CoNatural
conaturalN n = conatural n (\i -> if i == 0 then Left () else Right (i-1))

destructCoNatural :: CoNatural -> Either () CoNatural
destructCoNatural (CoNatural f) = f (\(p1,p2) -> p2 p1)

-- Vediamo un calcolo equazionale del fatto che se distruggiamo il conaturale
-- infinito otteniamo il conaturale infinito:

-- #+BEGIN_EXAMPLE
-- destructCoNatural infinite
-- = (unCoNatural (conatural 0 Right)) (\(p1,p2) -> p2 p1)
-- = (\f -> f (0, \i -> fmap (\a -> conatural a Right) (Right i))) (\(p1,p2) -> p2 p1)
-- = (\f -> f (0, \i -> conatural i Right)) (\(p1,p2) -> p2 p1)
-- = (\(p1,p2) -> p2 p1) (0, \i -> conatural i Right)
-- = (\i -> conatural i Right) 0
-- = conatural 0 Right
-- = infinite
-- #+END_EXAMPLE

-- Destrutturazione di un conaturale finito:
-- #+BEGIN_EXAMPLE
-- destructCoNatural (conaturalN (n+1))
-- = (unCoNatural (conatural (n+1) (\i -> if i == 0 then Left () else Right (i-1)))) (\(p1,p2) -> p2 p1)
-- = (\f -> f ((n+1), \i -> fmap (\a -> conatural a (\i -> if i == 0 then Left () else Right (i-1))) ((\j -> if j == 0 then Left () else Right (j-1)) i))) (\(p1,p2) -> p2 p1)
-- = (\i -> fmap (\a -> conatural a (\i -> if i == 0 then Left () else Right (i-1))) ((\j -> if j == 0 then Left () else Right (j-1)) i)) (n+1)
-- = fmap (\a -> conatural a (\i -> if i == 0 then Left () else Right (i-1))) ((\j -> if j == 0 then Left () else Right (j-1)) (n+1))
-- = fmap (\a -> conatural a (\i -> if i == 0 then Left () else Right (i-1))) (Right n)
-- = Right (conatural n (\i -> if i == 0 then Left () else Right (i-1)))
-- #+END_EXAMPLE

-- Destrutturazione del conaturale nullo:
-- #+BEGIN_EXAMPLE
-- destructCoNatural (conaturalN 0)
-- = (unCoNatural (conatural 0 (\i -> if i == 0 then Left () else Right (i-1)))) (\(p1,p2) -> p2 p1)
-- = (\f -> f (0, \i -> fmap (\a -> conatural a (\i -> if i == 0 then Left () else Right (i-1))) ((\j -> if j == 0 then Left () else Right (j-1)) i))) (\(p1,p2) -> p2 p1)
-- = (\i -> fmap (\a -> conatural a (\i -> if i == 0 then Left () else Right (i-1))) ((\j -> if j == 0 then Left () else Right (j-1)) i)) 0
-- = fmap (\a -> conatural a (\i -> if i == 0 then Left () else Right (i-1))) ((\j -> if j == 0 then Left () else Right (j-1)) 0)
-- = fmap (\a -> conatural a (\i -> if i == 0 then Left () else Right (i-1))) (Left ())
-- = Left ()
-- #+END_EXAMPLE

-- La domanda che mi pongo e': quante di queste dimostrazioni sintattiche riesco a
-- internalizzare una volta che ho tradotto queste cose in sottotipi?

-- E' arrivato il momento di tradurre queste trascrizione in $\lambda$ calcolo: in
-- particolare bisogna tradurre ~conatural~ e ~destructCoNatural~. Cominciamo da
-- ~conatural~, ricordando la definizione:

-- #+BEGIN_EXAMPLE
-- conatural :: a -> (a -> Either () a) -> CoNatural
-- conatural seed a2Eua = CoNatural $ \f -> f (seed, \i -> fmap (\a -> conatural a a2Eua) (a2Eua i))
-- #+END_EXAMPLE

-- Una traduzione diretta sarebbe quindi:

-- #+BEGIN_EXAMPLE
-- conat = seed ^ a2Eua ^ f ^ f # (couple # seed # (i ^ caseSplit # id # (a ^ conat # a # a2Eua) # (a2Eua # i)))
--   where
--     seed  = make_var "seed"
--     a2Eua = make_var "a2Eua"
-- #+END_EXAMPLE

-- A questo punto basta solamente fissare la ricorsione di ~conat~ utilizzando il
-- combinatore di punto fisso ~fix~:

conat = fix #
  (g ^ seed ^ a2Eua ^ f ^
   f # ( couple
       # seed
       # (i ^ caseSplit # id # (a ^ g # a # a2Eua) # (a2Eua # i))))
  where
    seed  = make_var "seed"
    a2Eua = make_var "a2Eua"

-- A questo punto scriviamo allora l'encoding del nostro conaturale infinito:
infty = conat # i0 # inr

-- Una cosa che non mi piace troppo e' che, avendo le definizioni con il fix
-- all'interno dei termini, di fatto non posso avere una forma chiusa, che posso
-- controllare come rappresentazione. Posso comunque controllarne un taglio
-- arbitrario, ad esempio facendo uso dell'istanza di Show.

-- Definiamo anche il distruttore di conaturali:
-- #+BEGIN_EXAMPLE
-- destructCoNatural :: CoNatural -> Either () CoNatural
-- destructCoNatural (CoNatural f) = f (\(p1,p2) -> p2 p1)
-- #+END_EXAMPLE

destrConat = f ^ f # (c ^ (pi2 # c) # (pi1 # c))

-- Naturalmente dovremmo chiederci se succede che:
-- #+BEGIN_EXAMPLE
-- λ> (show . eval) (destrConat # infty) == (show . eval) (inr # infty)
-- #+END_EXAMPLE

-- Inoltre probabilmente potremmo preoccuparci del fatto che i lambda  termini infiniti non hanno una rappresentazione finita, ovvero una forma normale.
-- Questo vuol dire che posso rapprensentarli solamente come un'espressione contentente ~fix~?
-- Trovo questo approccio abbastanza insoddisfacente.

-- Occupiamoci del problema di costruire il combinatore di anamorfismo per questo tipo di dato coinduttivo.
-- Una volta risolto il problema in generale, calcoleremo il termine per le coliste, che ci serve per costruire l'isomorfismo sui naturali.
-- All'inizio abbiamo scritto che:

-- $\begin{CD}
-- F \nu \! F @<F f<< F C       \\
-- @AoutAA            @AA\phi A \\
-- \nu \! F   @<<f< C           \\
-- \end{CD}$

-- Per prima cosa dobbiamo cercare di capire chi è la nostra funzione $out$ qui. Notiamo che non è l'inverso di $in$, visto che opera su tipi di dato diversi.
-- Per fortuna è chiaro a cosa corrisponda il nostro out una volta che abbiamo definito i nostri dati in modo coalgebrico.
-- Prendiamo ad esempio la nostra costruzione degli stream:

-- #+BEGIN_EXAMPLE
-- newtype Stream o = Stream (forall g. (forall a.
--   (a, a -> o, a -> Stream o) -> g) -> g)
-- #+END_EXAMPLE

-- È evidente che $out$ sia estraibile in generale da tutti i componenti della tupla tranne il seed.
-- Questo mi fa chiedermi come mai non rappresento direttamente la costruzione sopra come:

-- #+BEGIN_EXAMPLE
-- newtype Stream o = Stream (forall g. (forall a.
--   (a, a -> (o, Stream o)) -> g) -> g)
-- #+END_EXAMPLE

-- ovvero, per quale motivo non mi tengo più fedele alla definizione categoriale del funtore.

-- Notiamo che nel mondo induttivo l'encoding segue le somme di prodotti, mentre in quello coinduttivo segue i prodotti di somme.
-- Mi piacerebbe capire più in generale il perché di questo fenomeno.

-- Definiamo allora i combinatori in e out nel caso delle coliste di naturali, visto che questo è quello che ci serve per gli histomorfismi dei naturali.
-- Iniziamo dai distruttori: avremo due distruttori, $head$ e $tail$, che insieme formeranno il nostro $out$, nel senso che:

-- $\begin{CD}
-- Nat \times CoList(Nat)\\
-- @AoutA\langle head, tail \rangle A \\
-- CoList(Nat)  \\
-- \end{CD}$

-- sappiamo che possiamo codificare i due distruttori seguendo:
-- $\underline{D_i} = s (\lambda p. (\pi_{i+1} p) (\pi_1 p))$

headCoListNat :: CoList Int -> Int
headCoListNat (CoList cl) = cl (\p -> (snd3 p) (fst3 p))
  where
    fst3 (a,b,c) = a
    snd3 (a,b,c) = b

tailCoListNat :: CoList Int -> Either () (CoList Int)
tailCoListNat (CoList cl) = cl (\p -> (trd3 p) (fst3 p))
  where
    fst3 (a,b,c) = a
    trd3 (a,b,c) = c

-- questi, tradotti nel nostro linguaggio del lambda-calcolo:

head = cl ^ cl # (p ^ (pi23 # p) # (pi13 # p))
  where cl = make_var "cl"

tail = cl ^ cl # (p ^ (pi33 # p) # (pi13 # p))
  where cl = make_var "cl"

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

-- A questo punto si ha che:

-- $\begin{CD}
-- F \mu\! F @>F\; ana\langle f, in^{-1}\rangle >> F (F^{\nu} C) \\
-- @VinVV                                          @V\phi VV     \\
-- F         @>>f>                                 C             \\
-- \end{CD}$

-- Ovvero (histo-CHARN):
-- $f \circ in = \phi \circ F\; ana \langle f, in^{-1}\rangle$
-- da cui, invertendo, abbiamo:
-- $f = \phi \circ F\; ana \langle f, out \rangle \circ out$

-- Notiamo che in questo caso $ana$ è l'anamorfismo per le coliste, e non l'anamorfismo per i numeri naturali.

-- Al solito noi possiamo scriverlo con il punto fisso, dicendo che
histo = p ^ (fix # (f ^ comp3 # p
                              # (fNat # (ana # (split # f # out)))
                              # out))

-- Quello che vogliamo adesso e' un esempio di histomorfismo, ad esempio quello che
-- ci garantisce fibonacci:

-- l'idea e' come al solito partire dalle equazioni, per trascriverle:
-- $fib\; 0 = 0$
-- $fib\; 1 = 1$
-- $fib\; n = fib\; (pred\; n) + fib\; (pred\; (pred\; n))$

-- Vediamo chi e' $F(F^{\nu}C)$ nel caso dei numeri naturali. Ricordiamo che $F^{\mu}C$ e'
-- il punto fisso coalgebrico di $C\times (1+X) \equiv C + C\times X$, ovvero una lista non
-- vuota e potenzialmente infinita di $C$, che io posso nativamente distruggere.

-- La funzione con cui genero fibonacci e' quindi:
-- $preFibo = [const\; 0, [const\; 1, add \circ (id \times cur)] \circ distr \circ out] : 1 + F^{\nu}\mathbf{N} \rightarrow \mathbf{N}$

-- Quello che succede, e' che la seconda parte, $F^{\nu}C$ viene esplosa in $C \times (1 + F^{\nu}C)$,
-- trasformata da $distr$ in $C + C \times F^{\nu}C$ e infine consumata dalla funzione case.

-- Problemi da risolvere:
-- - out :: non e' l'out di Nat, ma l'out della coalgebra. Bisognerebbe quindi
--      scriverlo.
-- - distr :: bisogna scrivere la funzione distr che funzioni nel modo specificato.
-- - cur :: bisogna esplicitamente scrivere cur, che poi e' una componente della
--      coalgebra.

-- Allora, per quanto riguarda out, essenzialmente questo e' complicato dal fatto
-- che di solito io usavo la costruzione case per distinguere delle somme. Con
-- questa rappresentazione, invece, sono naturalmente portato a cercare di scrivere
-- un case per un prodotto, in cui dentro ci sono le distinzioni. Questo ovviamente
-- non si presta bene a quello che vorrei fare.

-- Per parlare bene della traduzione dei tipi coinduttivi devo capire bene perche'
-- $\exists \beta . A = \forall \alpha . (\forall \beta . A \rightarrow \alpha) \rightarrow \alpha$
-- Questo e' stato trattato nella sezione che riguarda gli anamorfismi.

-- Detto questo allora, ci rimangono solo un paio di preoccupazioni. Cerchiamo di
-- scrivere il caso che ci interessa per il trattamento categorico dei naturali:
-- Ci troviamo davanti ad una freccia del tipo $1 + \nu F^{\times}_C \rightarrow
-- C$,
-- e stiamo cercando di definire quel punto fisso coalgebrico. Sappiamo che quella
-- costruzione descrive le coliste, quindi liste di naturali non necessariamente
-- finite. Possiamo quindi collegarle alle espressioni equivalenti:

-- $\mu \beta. \exists \alpha. (\alpha \times (\alpha \rightarrow C) \times (\alpha
-- \rightarrow 1 + \beta))$
-- $CoList C = \exists \alpha. (\alpha \times (\alpha \rightarrow C) \times (\alpha \rightarrow 1 + CoList C))$
-- $CoList C = \exists \gamma. (\exists \alpha. (\alpha \times (\alpha \rightarrow C) \times (\alpha \rightarrow 1 + CoList C)) \rightarrow \gamma) \rightarrow \gamma$

-- Ovviamente potremmo sostituire i prodotti, almeno nell'ultima espressione, con
-- la loro forma uncurried, cosa che ci conviene fare se vogliamo evitare
-- l'overhead sintattico dei prodotti generici.

-- Quindi al solito si tratta di definire il combinatore di costruzione in analogia a quanto fatto nel capitolo degli anamorfismi:

newtype CoList c = CoList (forall g. (forall a.
  (a, a -> c, a -> Either () (CoList c)) -> g) -> g)

coList :: a -> (a -> c) -> (a -> Either () a) -> CoList c
coList seed head a2Eua = CoList $
  \f -> f ( seed
          , head
          , \i -> fmap (\a -> coList a head a2Eua) (a2Eua i)
          )



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
