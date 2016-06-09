{-# LANGUAGE RankNTypes #-}
{-# OPTIONS_GHC -fdefer-typed-holes #-}

-- * Scott Encoding

-- In questo modulo esploriamo l'implementazione degli schemi di ricorsione per
-- i naturali con lo Scott Encoding.

-- A differenza del Church encoding, le funzioni così definite hanno complessità
-- differente, perché l'encoding si limita a rappresentare, non a scegliere per
-- noi la forma della computazione.

-- ** Preliminari

module ScottEncoding where

-- Nascondiamo alcune funzioni di cui ridefiniremo il significato
import Prelude hiding ((^), const, sum, id)

-- Il modulo Lib contiene l'implementazione del nostro valutatore per il lambda
-- calcolo.
import Lib

-- Il modulo Common contiene alcuni lambda-termini che uso di frequente
import Common

-- Definiamo i numeri naturali con lo scott encoding: $i_0$ è il lambda-termine che
-- rappresenta lo $0$, e così via. L'operazione del successore è invece descritta dal
-- termine $succ$:

i0  = z ^ s ^ z
suc = n ^ z ^ s ^ s # n

-- Definisco per convenienza dei test alcuni altri interi piccoli:

i1 = eval (suc # i0)
i2 = eval (suc # i1)
i3 = eval (suc # i2)
i4 = eval (suc # i3)
i5 = eval (suc # i4)
i6 = eval (suc # i5)

-- E una funzione $termFor$ per generare il lambda termine corrispondente ad un
-- intero arbitrario (ad esempio $termFor \; 3$ genera lo Scott encoding di $3$).

termFor :: Int -> Term
termFor n = is !! n
  where
    is = i0 : map (eval . (suc #)) is

-- Questo encoding ci permette di definire direttamente la funzione $inN : 1+\mathcal{N} \rightarrow \mathcal{N}$,
-- e $outN : \mathcal{N} \rightarrow 1 + \mathcal{N}$, le due frecce dell'isomorfismo dell'algebra dei naturali.

inN, outN :: Term
inN  = caseSplit # (const # i0) # suc
outN = n ^ n # (inl # unit) # inr

-- Data una generica funzione di tipo $X \rightarrow Y$, possiamo sollevarla grazie
-- al funtore $F(X) = 1+X$ in una funzione di tipo $1+X \rightarrow 1+Y$. Questo
-- schema di traduzione si può estendere a funtori arbitrari, ma qui ci
-- limitiamo a scrivere la versione per i numeri naturali.

fNat :: Term
fNat = f ^ funPlus # id # f

-- ** Schemi di ricorsione per le algebre debolmente iniziali
-- *** Catamorfismi

-- Questa e' la ricetta generale del catamorfismo: notare come ricalca il
-- corrispondente diagramma categoriale.

cata = p ^ (fix # (f ^ comp3 # p # (fNat # f) # outN))

-- *** Paramorfismi

-- Guardiamo adesso il modello categorico per i paramorfismi, e capire che
-- relazione hanno con i catamorfisimi. La trattazione categorica ci dice in
-- generale che, data una funzione $g : T(B \times A) \rightarrow C$ possiamo
-- costruire la struttura:

-- \begin{center}
-- $\begin{CD}
-- T \; A   @>T \; cata \langle g, in \circ T\pi_2 \rangle>>   T(B \times A)                            @>T \pi_2>>    T \; A \\
-- @VinVV                                                      @V\langle g, in \circ T\pi_2 \rangle VV                 @VinVV \\
-- A        @>>cata \langle g, in \circ T\pi_2 \rangle>        B \times A                               @>\pi_2>>      A      \\
--          @.                                                 @V\pi_1VV                                @.                    \\
-- @.                                                          C                                                       @.     \\
-- \end{CD}$
-- \end{center}

-- e a questo punto possiamo possiamo definire dal punto di vista semantico il
-- paramorfismo di $g$ come:
-- \begin{equation}
-- \label{eq:1}
-- para \; g = \pi_1 \circ cata \langle g, in \circ T \pi_2 \rangle
-- \end{equation}

-- Ora, il problema è che ovviamente questa definizione si porta dietro tutto il
-- bagaglio computazionale del catamorfismo, quindi non è il modo in cui scriveremo
-- il termine che ci interessa; possiamo invece derivare un termine con migliori
-- proprietà computazionale dal diagramma della proprietà univerale per i
-- paramorfismi (~ana-CHARN~ nel paper originale di Meijer e Fokkinga):

-- \begin{center}
-- $\begin{CD}
-- T A   @>T \langle h, id \rangle>>   T(B \times A) \\
-- @VinVV                                    @VgVV         \\
-- A        @>>\exists ! h>                  B             \\
-- \end{CD}$
-- \end{center}


-- Nel caso dei naturali quello che abbiamo detto si traduce nel diagramma:

-- \begin{center}
-- $\begin{CD}
-- 1 + \mathbf{N} @>>> 1 + (C \times \mathbf{N}) @>1+\pi_2>> 1 + \mathbf{N} \\
-- @VVV                @VVV                                  @VinVV         \\
-- \mathbf{N}     @>>> C \times \mathbf{N}       @>\pi_2>>   \mathbf{N}     \\
-- @.                  @V\pi_1VV                             @.             \\
--                @. C                           @.                         \\
-- \end{CD}$
-- \end{center}

-- dove $g : 1 + (C \times \mathbf{N}) \rightarrow C$ rappresenta le nostre equazioni scritte in forma paramorfica.

-- Questa è allora la definizione poco efficiente che passa per il catamorfismo:

para = f ^ comp # pi1
                # (cata # (split # f # (comp # inN # (fNat # pi2))))

-- E questa è la definizione che, sfruttando il punto fisso, ha migliori proprietà
-- computazionali:

paraCHARN = p ^ (fix # (f ^ comp3 # p
                                  # (fNat # (split # f # id))
                                  # outN))


-- **** Case Study: la funzione predecessore
-- Questa e' la definizione del predecessore come catamorfismo:

predCata = cata # (fNat # inN)

-- Notiamo che e' equivalente alla definizione con outN:
predCataIsOut n = predCata # termFor n === outN # termFor n
testPredCataIsOut = all predCataIsOut [0..10]

-- Questa invece è la versione come paramorfismo, che ritorna ~const (inl unit)~ in
-- un caso e $\pi_2$ nell'altro.

preParaPred = caseSplit # (const # (inl # unit)) # pi2

-- da cui potremmo definire predPara = para # preParaPred, che funziona anche ma:

-- #+begin_verbatim
-- λ> map (\n -> nReductions $ para # preParaPred # termFor n) [0..10]
-- [38,76,116,156,196,236,276,316,356,396,436]

-- λ> map (\n -> nReductions $ predCata # termFor n) [0..10]
-- [28,57,87,117,147,177,207,237,267,297,327]
-- #+end_verbatim

-- Da cui vediamo che, come ci aspettavamo, la performance del paramorfismo
-- misurata in quantità di riduzioni non si ferma asintoticamente.

-- Questa è invece la versione in cui il paramorfismo è definito direttamente:

-- #+begin_verbatim
-- λ> map (\n -> nReductions $ paraCHARN # preParaPred # termFor n) [0..10]
-- [27,32,32,32,32,32,32,32,32,32,32]
-- #+end_verbatim

-- da cui si vede come il numero di riduzioni sia costante indipendentemente
-- dall'input (è ovviamente possibile dimostrare questi fatti direttamente).

-- *** Histomorfismi
-- Per parlare degli histomorfismi introduciamo un esempio classico: la codifica
-- della funzione che ad un intero $n$ associa l'$n$-esimo numero di Fibonacci. Il
-- modo naturale di scrivere questa ricorsione è quello di esplicitare le tre
-- equazioni che definiscono il comportamento della funzione (rispettivamente su
-- $0$, su $1$, e su un generico $n \ge 2$).

-- È ovviamente possibile scrivere le equazioni in forma paramorfica, ma sono delle
-- equazioni più complesse, in cui dobbiamo pensare manualmente ai dettagli
-- dell'"implementazione". Se questo è semplice nel caso degli interi, la cosa può
-- diventare rapidamente più complessa all'aumentare della complessità dei dati che
-- stiamo definendo.

-- Riassumendo allora, possiamo pensare alla "course of value iteration" come uno
-- schema di ricorsione in cui il valore dell'argomento corrente è costruito usando
-- il valore delle sottoparti dell'argomento ad una profondità arbitraria (ma
-- fissata!)

-- Per trattare questo modo di procedere, bisogna per prima cosa parlare delle
-- cv-algebre (course-of-value-algebras).

-- Ricordiamo che dato un funtore $F$ possiamo definire il (bi)funtore $F^{\times}$
-- tale che $F^{\times} : \mathcal{C} \times \mathcal{C} \rightarrow \mathcal{C}$ e $F^{\times}(A,X) = A \times F(X)$.
-- Di conseguenza, possiamo parlare del funtore indotto:
-- $F^{\times}_A : \mathcal{C} \rightarrow \mathcal{C}$
-- che manda $X$ in $A \times F(X)$. Il punto fisso di questo funtore, come
-- coalgebra terminale, sarà $\nu F^{\times}_A$, e quindi posso definire il funtore:
-- $F^{\nu} : \mathcal{C} \rightarrow \mathcal{C}$
-- $F^{\nu}(A) = \nu F^{\times}_A$

-- Nel caso dei numeri naturali, una cv-coalgebra non e' altro che una freccia
-- $1 + \nu F^{\times}_C \rightarrow C$

-- Salto il diagramma semantico per arrivare subito alla proprietà universale:

-- \begin{center}
-- $\begin{CD}
-- F \mu\! F @>F\; ana\langle f, in^{-1}\rangle >> F (F^{\nu} C) \\
-- @VinVV                                          @V\phi VV     \\
-- F         @>>f>                                 C             \\
-- \end{CD}$
-- \end{center}

-- Ovvero (histo-CHARN):

-- \begin{equation}
-- \label{eq:2}
-- f \circ in = \phi \circ F\; ana \langle f, in^{-1}\rangle
-- \end{equation}

-- da cui, invertendo, abbiamo:
-- \begin{equation}
-- \label{eq:3}
-- f = \phi \circ F\; ana \langle f, outN \rangle \circ outN
-- \end{equation}

-- Notiamo che in questo caso $ana$ è l'anamorfismo per le coliste, e non l'anamorfismo per i numeri naturali.

-- Al solito noi possiamo scriverlo con il punto fisso, dicendo che
histo = p ^ (fix # (f ^ comp3 # p
                              # (fNat # (ana # (split # f # outN)))
                              # outN))

-- Vediamo adesso come scrivere la funzione di Fibonacci seguendo le equazioni:

-- $fib\; 0 = 0$
-- $fib\; 1 = 1$
-- $fib\; n = fib\; (pred\; n) + fib\; (pred\; (pred\; n))$

-- Vediamo chi e' $F(F^{\nu}C)$ nel caso dei numeri naturali. Ricordiamo che $F^{\mu}C$ e'
-- il punto fisso coalgebrico di $C\times (1+X) \equiv C + C\times X$, ovvero una lista non
-- vuota e potenzialmente infinita di $C$, che io posso nativamente distruggere.

-- La funzione con cui genero fibonacci e' quindi:

-- \begin{equation}
-- \label{eq:4}
-- preFibo = [const\; 0, [const\; 1, add \circ (id \times cur)] \circ distr \circ outN] : 1 + F^{\nu}\mathbf{N} \rightarrow \mathbf{N}
-- \end{equation}

-- Quello che succede, e' che la seconda parte, $F^{\nu}C$ viene esplosa in $C \times (1 + F^{\nu}C)$,
-- trasformata da $distr$ in $C + C \times F^{\nu}C$ e infine consumata dalla funzione case.

-- I problemi che abbiamo nell'eseguire questo piano sono che ancora non abbiamo
-- pensato ad una codifica per la coalgebra, quindi non sappiamo come scrivere quei
-- termini. Vediamo questo nella funzione duale, quella sugli anamorfismi.


-- ** Schemi di ricorsione per le coalgebre debolmente finali
-- ** Anamorfismi
-- \begin{center}
-- $\begin{CD}
-- F \nu \! F @<F f<< F C       \\
-- @AoutAA            @AA\phi A \\
-- \nu \! F   @<<f< C           \\
-- \end{CD}$
-- \end{center}

-- Analogamente a quanto abbiamo fatto con i catamorfismi, andiamo a definire gli
-- anamorfismi tramite un combinatore di punto fisso;
-- Partiamo da ana-CHARN:

-- \begin{equation}
-- \label{eq:5}
-- outN \circ f = F f \circ \phi
-- \end{equation}

-- Nel nostro setting possiamo comodamente invertire, ottenendo $f = outN^{-1}
-- \circ F f \circ \phi$, ovvero:

ana = p ^ (fix # (f ^ comp3 # inN # (fNat # f) # p))

-- A questo punto c'è un problema: in generale il punto fisso algebrico non
-- coincide con quello coalgebrico, ad esempio per il funtore $F X = 1 + X$ abbiamo
-- sia i numeri naturali che i numeri conaturali. Nel folklore della comunità
-- funzionale si dice spesso che la lazyness annulla le differenze pragmatiche tra
-- i due concetti, ma c'è ancora bisogno di due encoding differenti.

-- *** Stream

-- L'approccio che seguo adesso èla codifica dei tipi coalgebrici seguendo gli
-- "Scott encoding per codata" cosi' come suggeriti da Geuvers: consideriamo in
-- particolare, come primo esempio, l'encoding degli stream.
-- Sappiamo che possiamo codificare uno stream di $A$ equivalentemente come:

-- $Str_A = \mu \beta . \exists \alpha . \alpha \times (\alpha \rightarrow A) \times (\alpha \rightarrow \beta)$

-- $Str_A = \exists \alpha . \alpha \times (\alpha \rightarrow A) \times (\alpha \rightarrow Str_A)$

-- $Str_A = \forall \gamma . (\forall \alpha . \alpha \times (\alpha \rightarrow A) \times (\alpha \rightarrow Str_A) \rightarrow \gamma) \rightarrow \gamma$

-- Usando la traduzione standard degli esistenziali, che viene accennata alla fine
-- del paper di Geuvers.

-- il problema che ho avuto nello scrivere il codice era come generare un termine
-- di tipo $Str_a$, cosa che io trovavo difficile per via del non riuscire a
-- scrivere un termine di tipo $\alpha \rightarrow Str_A$.

-- L'intuizione che voglio testare adesso èil funzionamento di un trucco, di
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
          , \i -> stream (update i) extract update
          )

naturals :: Stream Integer
naturals = stream 0 identity succ
  where identity x = x

-- La morale della favola è questa, sono riuscito a creare un costruttore del
-- termine che mi serviva, sostituendo il termine problematico che avevo $\alpha \rightarrow Str_A$,
-- con un piu' ovvio $\alpha \rightarrow \alpha$, che parla in modo diretto del seed, utilizzando in fondo
-- un combinatore di punto fisso.

-- notiamo che il pattern del costruttore e':

-- $stream \; s \; e \; u = \lambda f. f \; s \; e \; (\lambda i. stream \; (u \; i) \; e \; u)$

-- *** Conaturali

-- Possiamo parlare a questo punto dell'analogo per i numeri naturali, ovvero per
-- il funtore $F X = 1 + X$.

-- Sappiamo che questo da origine ai numeri CoNaturali, che dovrebbero quindi
-- essere definiti equivalentemente come:

-- $CoNat = \mu \beta. \forall \alpha. \alpha \times (\alpha \rightarrow 1 + \beta)$
-- $CoNat = \forall \alpha. \alpha \times (\alpha \rightarrow 1 + CoNat)$
-- $CoNat = \forall \gamma. (\forall \alpha. \alpha \times (\alpha \rightarrow 1 + CoNat) \rightarrow \gamma) \rightarrow \gamma$

-- Ricordiamo che Geuvers suggerisce che se i codata sono encodati in $\lambda 2 \mu$ come:
-- $\underline{D} = \mu \beta. \exists \alpha. \alpha \times (\alpha \rightarrow T^1(\beta)) \times \dots \times (\alpha \rightarrow T^n(\beta))$

-- allora il generico distruttore $\underline{D_i} : \underline{D} \rightarrow T^i(\underline{D})$ èencodato da:
-- $\underline{D_i} \; s = s \; (\lambda p.(\pi_{i+1} \; p) \; (\pi_1 \; p))$

-- Nel mio caso, il distruttore sarebbe encodato da:
-- $D \; s = s \; (\lambda p. \pi_2 \; p \; (\pi_1 \; p))$

-- Abbiamo allora che:

newtype CoNatural =
  CoNatural
    (forall g. (forall a. (a, a -> Either () CoNatural) -> g) -> g)

conatural :: a -> (a -> Either () a) -> CoNatural
conatural seed a2Eua =
  CoNatural $ \f -> f (seed, fmap (`conatural` a2Eua) . a2Eua)

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

-- Traduciamo ora queste trascrizione in $\lambda$ calcolo: in particolare bisogna
-- tradurre ~conatural~ e ~destructCoNatural~. Cominciamo da ~conatural~,
-- ricordando la definizione:

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

-- Una cosa che non mi piace è che, avendo le definizioni con il fix all'interno
-- dei termini, non posso averne una presentazione chiusa. Questo non va bene,
-- anche per gli scopi della teoria, e mi sembra che quello che fanno sia Geuvers
-- che Mendler sia internalizzare questo tipo di costanti per ogni tipo per non
-- dovere scrivere esplicitamente fix. Quella è una cosa da guardare meglio, perché
-- quest'approccio con il fix è abbastanza insoddisfacente.

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

-- *** Coliste

-- Cerchiamo di costruire in particolare le coliste perché ci servono quando
-- parliamo dell'histomorfismo dei naturali. All'inizio abbiamo scritto che:

-- $\begin{CD}
-- F \nu \! F @<F f<< F C       \\
-- @AoutAA            @AA\phi A \\
-- \nu \! F   @<<f< C           \\
-- \end{CD}$

-- Per prima cosa dobbiamo cercare di capire chi è la nostra funzione $outN$ qui.
-- Notiamo che non è l'inverso di $in$, visto che opera su tipi di dato diversi.
-- Per fortuna è chiaro a cosa corrisponda il nostro outN una volta che abbiamo
-- definito i nostri dati in modo coalgebrico. Prendiamo ad esempio la nostra
-- costruzione degli stream:

-- #+BEGIN_EXAMPLE
-- newtype Stream o = Stream (forall g. (forall a.
--   (a, a -> o, a -> Stream o) -> g) -> g)
-- #+END_EXAMPLE

-- È evidente che $outN$ sia estraibile in generale da tutti i componenti della tupla tranne il seed.
-- Questo mi fa chiedermi come mai non rappresento direttamente la costruzione sopra come:

-- #+BEGIN_EXAMPLE
-- newtype Stream o = Stream (forall g. (forall a.
--   (a, a -> (o, Stream o)) -> g) -> g)
-- #+END_EXAMPLE

-- ovvero, per quale motivo non mi tengo più fedele alla definizione categoriale del funtore.

-- Notiamo che nel mondo induttivo l'encoding segue le somme di prodotti, mentre in
-- quello coinduttivo segue i prodotti di somme. Mi piacerebbe capire più in
-- generale il perché di questo fenomeno.

-- Definiamo allora i combinatori in e outN nel caso delle coliste di naturali,
-- visto che questo è quello che ci serve per gli histomorfismi dei naturali.
-- Iniziamo dai distruttori: avremo due distruttori, $head$ e $tail$, che insieme
-- formeranno il nostro $outN$, nel senso che:
-- \begin{center}
-- $\begin{CD}
-- Nat \times CoList(Nat)\\
-- @AoutA\langle head, tail \rangle A \\
-- CoList(Nat)  \\
-- \end{CD}$
-- \end{center}

-- Il codice risulta quindi:

newtype CoList c = CoList (forall g. (forall a.
  (a, a -> c, a -> Either () (CoList c)) -> g) -> g)

coList :: a -> (a -> c) -> (a -> Either () a) -> CoList c
coList seed head a2Eua = CoList $
  \f -> f ( seed
          , head
          , fmap (\a -> coList a head a2Eua) . a2Eua
          )

-- Nel nostro $\lambda$-calcolo, il combinatore coList diventa:

colist' = seed ^ head ^ a2Eua ^ f ^
  f # (triple # seed
              # head
              # (i ^ (caseSplit # id # (a ^ colist # a # head # a2Eua)
                   # (a2Eua # i))))
  where
    [seed, head, a2Eua] = map make_var ["seed", "head", "a2Eua"]

-- che dobbiamo ridefinire nella versione con il fix come:

colist = fix # (g ^ (seed ^ head ^ a2Eua ^ f ^
  f # (triple # seed
              # head
              # (i ^ (caseSplit # id # (a ^ g # a # head # a2Eua)
                   # (a2Eua # i))))))
  where
    [seed, head, a2Eua] = map make_var ["seed", "head", "a2Eua"]

-- A questo punto tentiamo di costruire una versione della colista infinita dei numeri naturali, prima in Haskell:

infiniteCoList = colist # i0 # id # (a ^ inr # (suc # a))

-- Sappiamo che possiamo codificare i due distruttori seguendo:
-- $\underline{D_i} = s (\lambda p. (\pi_{i+1} p) (\pi_1 p))$

headCoListNat :: CoList Int -> Int
headCoListNat (CoList cl) = cl (\p -> snd3 p (fst3 p))
  where
    fst3 (a,b,c) = a
    snd3 (a,b,c) = b

tailCoListNat :: CoList Int -> Either () (CoList Int)
tailCoListNat (CoList cl) = cl (\p -> trd3 p (fst3 p))
  where
    fst3 (a,b,c) = a
    trd3 (a,b,c) = c

-- questi, tradotti nel nostro linguaggio del lambda-calcolo:

coListHead = cl ^ cl # (p ^ (pi23 # p) # (pi13 # p))
  where cl = make_var "cl"

coListTail = cl ^ cl # (p ^ (pi33 # p) # (pi13 # p))
  where cl = make_var "cl"

-- Questi schemi funzionano, nel senso che abbiamo:

-- #+BEGIN_EXAMPLE
-- λ> eval $ coListHead # infiniteCoList
-- (\z. (\s. z))
-- λ> eval $ coListHead # (coListTail # infiniteCoList)
-- (\z. (\s. s (\z. (\s. z))))
-- λ> eval $ coListHead # (coListTail # (coListTail # infiniteCoList))
-- (\z. (\s. s (\z. (\s. s (\z. (\s. z))))))
-- #+END_EXAMPLE

-- Vogliamo adesso scrivere l'$outN$ in generale, perché questo ci serve per gli
-- histomorfismi. Nel caso delle coliste, $outN$ è effettivamente il prodotto della
-- funzione $head$ con la funzione $tail$, per cui mi basta definire:

coListOut = split # coListHead # coListTail

-- Notiamo che ovviamente non possiamo valutare questa perché manca di una forma
-- normale, ma è quello che ci servirà nella costruzione degli histomorfismi.

-- Al solito, ci serve anche esplicitare l'inverso della funzione $coListOut$.
-- Seguendo Geuvers, nel caso generale dobbiamo aspettarci qualcosa come:

-- $cons : T^1(D) \rightarrow \dots \rightarrow T^n(D) \rightarrow D$
-- $cons = \lambda x_1, \dots, \lambda x_n.\lambda f.f \langle x_1, \lambda z. x_1, \dots, \lambda z. x_n \rangle$

-- che noi potremmo scrivere, nel caso delle coliste, come:

coListIn = h ^ t ^ f ^ f # (triple # h # (z ^ h) # (z ^ t))

-- Ci sono problemi nella valutazione di questi termini, ovviamente:

-- ** Apomorfismi

-- In generale la costruzione degli apomorfismi si ottiene dualizzando quello che
-- abbiamo visto per i catamorfismi. Quindi abbiamo che:

-- \begin{center}
-- $\begin{CD}
-- F \nu\! F @<F [f,id]<< F (C + \nu\! F) \\
-- @AoutAA                @AA\phi A       \\
-- \nu\! F   @<<f<        C               \\
-- \end{CD}$
-- \end{center}

-- In particolare, ne scriviamo un encoding direttamente tramite la proprietà universale:

-- $outN \circ f = F [f, id] \circ \phi \iff f = apo(\phi)$

-- Da cui, per noi che possiamo invertire:

-- $f = fix (outN^{-1} \circ F [f, id] \circ \phi)$

apo = p ^ (fix # (f ^ comp3 # inN
                            # (fNat # (caseSplit # f # id))
                            # p))

-- Dovremmo a questo punto a fare un esempio di apomorfismo: la coricorsione
-- primitiva su conaturali o sulle coliste.

-- * Interrogativi

-- Mi chiedo quale sia il punto della trascrizione dei tipi di dati coinduttivi
-- come sto facendo. Infatti, alla fine nella trascrizione in lambda calcolo, mi
-- trovo ad avere a che fare con l'operatore di punto fisso $fix$. Questo da un
-- lato presenta un problema di rappresentazione: mi piacerebbe poter rappresentare
-- in modo finito i termini di cui sto parlando anche all'interno del linguaggio
-- oggetto. Quello che succede nel paper di Mendler è che lui introduce nel
-- linguaggio oggetto anche delle costanti non interpretate, di cui da delle regole
-- di valutazione a parte.

-- Quello che non capisco pero è come tradurre eventualmente questi termini in
-- una rappresentazione come quella del lambda calcolo, ma mantenendo le
-- proprietà come la normalizzabilità forte?

-- Quando parlavo degli schemi ricorsivi anche io usavo il punto fisso per
-- encodare gli schemi di ricorsione. Almeno però avevo una presentazione finita
-- del termine, che potevo per esempio usare come mezzo per scrivere
-- l'uguaglianza. Con i tipi di dati coinduttivi purtroppo i termini stessi sono
-- definiti con il combinatore di punto fisso. Il problema è che a quel punto
-- non posso nemmeno paragonarli per uguaglianza, mentre a volte lo sono
-- chiaramente. Forse questo dipende dal fatto che le funzioni sono codata?
