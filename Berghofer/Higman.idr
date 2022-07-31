{-
    Title:      Berghofer.Higman.idr
    Author:     Sergei Romanenko, KIAM Moscow

    This version is produced by rewriting the proof presented in

      S. Berghofer. A constructive proof of Higman's lemma in Isabelle.
      In Types for Proofs and Programs, TYPES'04. LNCS, 3085: 66-82.
      Springer Verlag, 2004. 

    from Isabelle to Idris 2.
-}

module Berghofer.Higman

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
--   L1 :: L0 :: L1 :: [] << L0 :: L1 :: L0 :: L0 :: L1 :: []

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
emb_empty (a :: w) = Drop (emb_empty w)

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

-- Inequality of letters.

infix 6 <>

data (<>) : (x, y : Letter) -> Type where
  L0neL1 : L0 <> L1
  L1neL0 : L1 <> L0

l_sym : x <> y -> y <> x
l_sym L0neL1 = L1neL0
l_sym L1neL0 = L0neL1

l_eq'ne : (x, y : Letter) -> (x = y) `Either` (x <> y)
l_eq'ne L0 L0 = Left Refl
l_eq'ne L0 L1 = Right L0neL1
l_eq'ne L1 L0 = Right L1neL0
l_eq'ne L1 L1 = Left Refl

--
-- Dirichlet's (pigeonhole) principle for 2 holes.
--

dirichlet2 : x <> y -> (z : Letter) -> Either(z = x) (z = y)
dirichlet2 L0neL1 L0 = Left Refl
dirichlet2 L0neL1 L1 = Right Refl
dirichlet2 L1neL0 L0 = Right Refl
dirichlet2 L1neL0 L1 = Left Refl

-- `T a ws vs` means that vs is obtained from ws by
-- (1) first copying the prefix of words starting with the letter b,
--     where a <> b, and
-- (2) then appending the tails of words starting with a.

data T : (a : Letter) -> (vs, ws : Seq) -> Type where
  TInit : a <> b ->
            T a ((a :: w) :: (b ::* ws)) (w ::(b ::* ws))
  TKeep : T a ws vs ->
            T a ((a :: w) :: ws) (w :: vs)
  TDrop : a <> b ->
            T a ws vs -> T a ((b :: w) :: ws) vs

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
t_s_emb_drop : T a ws vs -> vs *<< v -> ws *<< a :: v
t_s_emb_drop (TInit a_ne_b) (EHere here) =
  EHere (Keep here)
t_s_emb_drop (TInit a_ne_b) (EThere there) =
  EThere (s_emb_drop there)
t_s_emb_drop (TKeep keep) (EHere here) =
  EHere (Keep here)
t_s_emb_drop (TKeep keep) (EThere there) =
  EThere (t_s_emb_drop keep there)
t_s_emb_drop (TDrop a_ne_b drop) vs_s_emb_v =
  EThere (t_s_emb_drop drop vs_s_emb_v)

-- Lemmas. Good ... -> Good ...

%hint
good_drop : Good ws -> Good (a ::* ws)
good_drop (Here ws_s_emb_w) =
  Here (s_emb_keep ws_s_emb_w)
good_drop (There good_ws) =
  There (good_drop good_ws)

%hint
good_t : T a ws vs -> Good vs -> Good ws
good_t (TInit a_ne_b) (Here here) =
  Here (s_emb_drop here)
good_t (TInit a_ne_b) (There there) =
  There there
good_t (TKeep keep) (Here here) =
  Here (t_s_emb_drop keep here)
good_t (TKeep keep) (There there) =
  There (good_t keep there)
good_t (TDrop a_ne_b t) good_vs =
  There (good_t t good_vs)

-- Lemma. T a (a ::* ...) (...)

%hint
t_extend : (a : _) -> (ws : _) -> NonEmpty ws -> T a (a ::* ws) ws
t_extend _ [] IsNonEmpty impossible
t_extend a (v :: (w :: ws)) ne_ws =
  TKeep (t_extend a (w :: ws) IsNonEmpty)
t_extend L0 (v :: []) ne_ws =
  TInit {b = L1} {ws = []} L0neL1
t_extend L1 (v :: []) ne_ws =
  TInit {b = L0} {ws = []} L1neL0

--
-- prop2 : Interleaving two trees
--
-- Proof idea: Induction on Bar xs and Bar ys,
-- then case distinction on first letter of first word following zs

mutual

  tt_bb : {a, b : _} -> {zs, xs, ys : _} ->
    a <> b -> T a zs xs -> T b zs ys ->
    Bar xs -> Bar ys ->
    Bar zs
  tt_bb a_ne_b ta tb (Now nx) bar_ys =
    Now (good_t ta nx)
  tt_bb a_ne_b ta tb (Later lx) (Now ny) =
    Now (good_t tb ny)
  tt_bb a_ne_b ta tb (Later lx) (Later ly) =
    Later $ tt_ll (Later lx) (Later ly) ItIsLater ItIsLater a_ne_b ta tb

  tt_ll : {a, b : _} -> {zs, xs, ys : _} ->
    (b_xs : Bar xs) -> (b_ys : Bar ys) -> IsLater b_xs -> IsLater b_ys ->
    a <> b -> T a zs xs -> T b zs ys -> (w : Word) ->
    Bar (w :: zs)
  tt_ll (Later lx) (Later ly) ItIsLater ItIsLater a_ne_b ta tb [] =
    bar_w_empty zs
  tt_ll (Later lx) (Later ly) ItIsLater ItIsLater a_ne_b ta tb (c :: v) =
    case dirichlet2 a_ne_b c of
      Left c_eq_a => rewrite c_eq_a in
        the (Bar ((a :: v) :: zs)) $
        tt_bb a_ne_b (TKeep ta) (TDrop (l_sym a_ne_b) tb) (lx v) (Later ly) -- ===
      Right c_eq_b => rewrite c_eq_b in
        the (Bar ((b :: v) :: zs)) $
        tt_bb a_ne_b (TDrop a_ne_b ta) (TKeep tb) (Later lx) (ly v) -- ===

--
-- prop3 : Lifting to longer words
--
-- Proof idea: Induction on Bar ws, then induction on first word following ws

mutual

  bar_lift : (b, ws : _) -> NonEmpty ws -> Bar ws -> Bar (b ::* ws)
  bar_lift b ws ne_ws (Now n) =
    Now (good_drop n)
  bar_lift b ws ne_ws (Later l) =
    Later $ later_lift b ws ne_ws (Later l) ItIsLater

  later_lift : (b, ws : _) -> NonEmpty ws ->
    (b_ws : Bar ws) -> IsLater b_ws ->
    (w : Word) -> Bar (w :: (b ::* ws))
  later_lift b ws ne_ws (Later l) ItIsLater [] =
    bar_w_empty (b ::* ws)
  later_lift b ws ne_ws (Later l) ItIsLater (a :: w) =
    either
      (\a_eq_b =>
        the (Bar ((a :: w) :: (b ::* ws))) $
        replace {p = \t => Bar ((t :: w) :: (b ::* ws))} (sym a_eq_b) $
        the (Bar (b ::* (w :: ws))) $
        bar_lift b (w :: ws) IsNonEmpty (l w)) -- ===
      (\a_ne_b =>
        the (Bar ((a :: w) :: (b ::* ws))) $
        tt_bb
          a_ne_b
          (TInit a_ne_b)
          (TDrop (l_sym a_ne_b) (t_extend b ws ne_ws))
          (later_lift b ws ne_ws (Later l) ItIsLater w) -- ===
          (Later l))
      (l_eq'ne a b)

--
-- higman: Main theorem
--

later_empty :  (w : Word) -> Bar (w :: [])
later_empty [] = bar_w_empty []
later_empty (c :: w) =
  bar_lift c (w :: []) IsNonEmpty (later_empty w)

bar_empty : Bar []
bar_empty = Later later_empty

bar_ne : (w, ws : _) -> Bar ws -> Bar (w :: ws)
bar_ne w ws (Now n) = Now (There n)
bar_ne w ws (Later l) = l w

higman : (ws : Seq) -> Bar ws
higman [] = bar_empty
higman (w :: ws) = bar_ne w ws (higman ws)

--
-- good_prefix-lemma
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

--
-- Finding good prefixes of infinite sequences
--

good_prefix : (f : Nat -> Word) ->
  (s ** (Prefix f s, Good (snd s)))
good_prefix f = good_prefix' f (Z, []) PZ bar_empty
