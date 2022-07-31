{-
    Title:      Berghofer.HigmanT2
    Author:     Sergei Romanenko, KIAM Moscow

    This version is produced by rewriting the proof presented in

      S. Berghofer. A constructive proof of Higman's lemma in Isabelle.
      In Types for Proofs and Programs, TYPES'04. LNCS, 3085: 66-82.
      Springer Verlag, 2004. 

    from Isabelle to Agda.
-}

module Berghofer.HigmanT2

import Data.List
import Decidable.Equality

%default total

-- Words are modelled as lists of letters from
-- the two letter alphabet.

data Letter : Type where
  L0 : Letter
  L1 : Letter

Word : Type
Word = List Letter

-- The embedding relation on words is defined inductively.
-- Intuitively, a word `v` can be embedded into a word `w`,
-- if we can obtain `v` by deleting letters from `w`.
-- For example,
--   L1 :: L0 :: L1 :: [] ⊴ L0 :: L1 :: L0 :: L0 :: L1 :: []

infix 6 <<, *<<

data (<<) : (v, w : Word) -> Type where
  Empty : [] << []
  Drop  : v << w -> v << (a :: w)
  Keep  : v << w -> a :: v << a :: w

namespace TestEmb

  test1 : L1 :: L0 :: L1 :: [] << L0 :: L1 :: L0 :: L0 :: L1 :: []
  test1 = Drop (Keep (Drop (Keep (Keep Empty))))

-- [] is embeddable in any word.

%hint
emb_empty : (w : _) -> [] << w
emb_empty [] = Empty
emb_empty (w :: ws) = Drop (emb_empty ws)

-- We represent a finite sequence w_0, w_1, ... , w_n as
--   w_n :: ... :: w_1 :: w_0 :: []

Seq : Type
Seq = List Word

-- In order to formalize the notion of a good sequence,
-- we define an auxiliary relation *<<.
--   ws *<< v
-- means that ws contains a word w, such that w << v .

data (*<<) : (ws : Seq) -> (v : Word) -> Type where
  EHere  : w << v -> (w :: ws) *<< v
  EThere : ws *<< v -> (w :: ws) *<< v

-- A list of words is good if its tail is either good
-- or contains a word which can be embedded into the word
-- occurring at the head position of the list.

data Good : (ws : Seq) -> Type where
  Here  : ws *<< w -> Good (w :: ws)
  There : Good ws -> Good (w :: ws)

-- In order to express the fact that every infinite sequence is good,
-- we define a predicate Bar.
--
-- Intuitively, Bar ws means that either
-- (1) the list of words ws is already good, or
-- (2) successively adding words will turn it into a good list.

data Bar : Seq -> Type where
  Now   : {ws : _} -> Good ws -> Bar ws
  Later : ((w : _) -> Bar (w :: ws)) -> Bar ws

data IsLater : Bar xs -> Type where
  ItIsLater : IsLater (Later xs)

-- Consequently,
--   Bar []
-- means that every infinite sequence must be good,
-- since by successively adding words to the empty list, we must
-- eventually arrive at a list which is good.

-- (Note that the above definition of Bar is closely related to
-- Brouwer’s more general principle of bar induction.)

-- The following function adds a letter to each word in a word list. 

infixr 7 ::*

(::*) : (a : Letter) -> (ws : Seq) -> Seq
a ::* [] = []
a ::* (w :: ws) = (a :: w) :: (a ::* ws)

namespace Berghofer's_T

  -- This is the relation `T`, used in the original Berghofer's proof.

  -- `T a vs ws` means that vs is obtained from ws by
  -- (1) first copying the prefix of words starting with the letter b,
  --     where Not(a = b), and
  -- (2) then appending the tails of words starting with a.

  data T : (a : Letter) -> (vs, ws : Seq) -> Type where
    TInit : Not(a = b) ->
              T a (w ::(b ::* ws)) ((a :: w) :: (b ::* ws))
    TKeep : T a vs ws ->
              T a (w :: vs) ((a :: w) :: ws)
    TDrop : Not(a = b) ->
              T a vs ws -> T a vs ((b :: w) :: ws)

-- In Berghofer's proof `T` is always used as a comination
--   `T a xs zs -> T b ys zs -> ...`
-- So, we can simplify the proof by directly defining a relation T2, such that
-- `T2 xs ys zs` is equivalent to `(T a xs zs, T a xs zs)`.

-- The relation `T2` is the result of com

data T2 : (zs, xs, ys : Seq) -> Type where
  Init0 : T2 (w :: (L1 ::* ys)) ys ((L0 :: w) :: (L1 ::* ys))
  Init1 : T2 xs (w :: (L0 ::* xs)) ((L1 :: w) :: (L0 ::* xs))
  Step0 : T2 xs ys zs -> T2 (w :: xs) ys ((L0 :: w) :: zs)
  Step1 : T2 xs ys zs -> T2 xs (w :: ys) ((L1 :: w) :: zs)

--
-- The proof of Higman’s lemma is divided into several parts, namely
-- prop1, prop2 and prop3.
-- From the computational point of view, these theorems can be thought of
-- as functions transforming trees.

--
-- prop1 : Sequences “ending” with empty word (trivial)
-- A sequence ending with the empty word satisfies predicate Bar,
-- since it can trivially be extended to a good sequence
-- by appending any word.
--

%hint
bar_w_empty : (ws : _) -> Bar ([] :: ws)
bar_w_empty ws = Later (\w => Now (Here (EHere (emb_empty w))))

-- Lemmas. w *<< v ... -> (a :: w) *<< v ...

%hint
s_emb_drop : ws *<< v -> ws *<< a :: v
s_emb_drop (EHere w_emb_v) = EHere (Drop w_emb_v)
s_emb_drop (EThere ws_s_emb_v) = EThere (s_emb_drop ws_s_emb_v)

%hint
s_emb_keep : ws *<< v -> (a ::* ws) *<< a :: v
s_emb_keep (EHere w_emb_v) = EHere (Keep w_emb_v)
s_emb_keep (EThere ws_s_emb_v) = EThere (s_emb_keep ws_s_emb_v)

%hint
t2_semb_drop0 : T2 xs ys zs -> xs *<< w -> zs *<< L0 :: w
t2_semb_drop0 Init0 (EHere emb_w) =
  EHere (Keep emb_w)
t2_semb_drop0 Init0 (EThere semb_w) =
  EThere (s_emb_drop semb_w)
t2_semb_drop0 Init1 semb_w =
  EThere (s_emb_keep semb_w)
t2_semb_drop0 (Step0 t2) (EHere emb_w) =
  EHere (Keep emb_w)
t2_semb_drop0 (Step0 t2) (EThere semb_w) =
  EThere (t2_semb_drop0 t2 semb_w)
t2_semb_drop0 (Step1 t2) semb_w =
  EThere (t2_semb_drop0 t2 semb_w)

%hint
t2_semb_drop1 : T2 xs ys zs -> ys *<< w -> zs *<< L1 :: w
t2_semb_drop1 Init0 semb_w =
  EThere (s_emb_keep semb_w)
t2_semb_drop1 Init1 (EHere emb_w) =
  EHere (Keep emb_w)
t2_semb_drop1 Init1 (EThere semb_w) =
  EThere (s_emb_drop semb_w)
t2_semb_drop1 (Step0 t2) semb_w =
  EThere (t2_semb_drop1 t2 semb_w)
t2_semb_drop1 (Step1 t2) (EHere emb_w) =
  EHere (Keep emb_w)
t2_semb_drop1 (Step1 t2) (EThere emb_w) =
  EThere (t2_semb_drop1 t2 emb_w)

-- Lemmas. Good ... -> Good ...

%hint
good_drop : Good ws -> Good (a ::* ws)
good_drop (Here ws_s_emb_w) =
  Here (s_emb_keep ws_s_emb_w)
good_drop (There good_ws) =
  There (good_drop good_ws)

%hint
good_t0 : T2 xs ys zs -> Good xs -> Good zs
good_t0 Init0 (Here semb_w) =
  Here (s_emb_drop semb_w)
good_t0 Init0 (There good_l1ys) =
  There good_l1ys
good_t0 Init1 gx =
  There (good_drop gx)
good_t0 (Step0 t2) (Here semb_w) =
  Here (t2_semb_drop0 t2 semb_w)
good_t0 (Step0 t2) (There gx) =
  There (good_t0 t2 gx)
good_t0 (Step1 t2) gx =
  There (good_t0 t2 gx)


%hint
good_t1 : T2 xs ys zs -> Good ys -> Good zs
good_t1 Init0 gy =
  There (good_drop gy)
good_t1 Init1 (Here semb_w) =
  Here (s_emb_drop semb_w)
good_t1 Init1 (There good_l0xs) =
  There good_l0xs
good_t1 (Step0 t2) gy =
  There (good_t1 t2 gy)
good_t1 (Step1 t2) (Here semb_w) =
  good_t1 (Step1 t2) (Here semb_w)
good_t1 (Step1 t2) (There gy) =
  There (good_t1 t2 gy)

--
-- prop2 : Interleaving two trees
--
-- Proof idea: Induction on Bar xs and Bar ys,
-- then case distinction on first letter of first word following zs

mutual

  tt_bb : {zs, xs, ys : _} -> T2 xs ys zs -> Bar xs -> Bar ys -> Bar zs
  tt_bb t (Now nx) ny = Now (good_t0 t nx)
  tt_bb t (Later lx) (Now ny) = Now (good_t1 t ny)
  tt_bb t (Later lx) (Later ly) =
    Later $ tt_ll t (Later lx) (Later ly) ItIsLater ItIsLater

  tt_ll : {zs, xs, ys : _} -> T2 xs ys zs ->
    (b_x : Bar xs) -> (b_y : Bar ys) -> IsLater b_x -> IsLater b_y ->
    (w : Word) -> Bar (w :: zs)
  tt_ll t (Later lx) (Later ly) ItIsLater ItIsLater v = case v of
    [] => bar_w_empty zs
    (L0 :: w) => tt_bb (Step0 t) (lx w) (Later ly)
    (L1 :: w) => tt_bb (Step1 t) (Later lx) (ly w)

--
-- prop3 : Lifting to longer words
--
-- Proof idea: Induction on Bar ws, then induction on first word following ws
--

mutual

  bar_lift : (b, ws : _) -> Bar ws -> Bar (b ::* ws)
  bar_lift b ws (Now n) = Now (good_drop n)
  bar_lift b ws (Later l) = Later (later_lift b ws (Later l) ItIsLater)

  later_lift : (b, ws : _) -> (bw : Bar ws) -> IsLater bw ->
    (w : _) -> Bar (w :: (b ::* ws))
  later_lift L0 ws (Later l) ItIsLater v = case v of
    [] => bar_w_empty (L0 ::* ws)
    (L0 :: w) => bar_lift L0 (w :: ws) (l w) -- ===
    (L1 :: w) => tt_bb Init1 (Later l) (later_lift L0 ws (Later l) ItIsLater w)
  later_lift L1 ws (Later l) ItIsLater v = case v of
    [] => bar_w_empty (L1 ::* ws)
    (L0 :: w) => tt_bb Init0 (later_lift L1 ws (Later l) ItIsLater w) (Later l)
    (L1 :: w) => bar_lift L1 (w :: ws) (l w) -- ===

--
-- higman: Main theorem
--

later_empty :  (w : Word) -> Bar (w :: [])
later_empty [] = bar_w_empty []
later_empty (c :: w) =
  bar_lift c (w :: []) (later_empty w)

bar_empty : Bar []
bar_empty = Later later_empty

bar_ne : (w, ws : _) -> Bar ws -> Bar (w :: ws)
bar_ne w ws (Now n) = Now (There n)
bar_ne w ws (Later l) = l w

higman : (ws : Seq) -> Bar ws
higman [] = bar_empty
higman (w :: ws) = bar_ne w ws (higman ws)

--
-- good-prefix-lemma
--

data Prefix : (f : Nat -> Word) -> (Nat, Seq) -> Type where
  PZ : Prefix f (Z, [])
  PS : {i, xs : _} ->
        Prefix f (i, xs) -> Prefix f (S i, f i :: xs)

good_prefix' : (f : Nat -> Word) ->
    (s : _) -> Prefix f s -> Bar (snd s) ->
    (s' ** (Prefix f s', Good (snd s')))
good_prefix' f s p (Now n) =
  (s ** (p, n))
good_prefix' f (i, ws) p (Later l) =
  good_prefix' f (S i, f i :: ws) (PS p) (l (f i))


-- Finding good prefixes of infinite sequences

good_prefix : (f : Nat -> Word) ->
  (s ** (Prefix f s, Good (snd s)))
good_prefix f = good_prefix' f (Z, []) PZ bar_empty
