import Mathlib.Data.Real.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.Finite.Defs
import Mathlib.Data.Multiset.Basic

/-!
---
title: Formal power series
type: definition
---
Formal power series over an alphabet `α` are functions from words `List α` to
the rationals.  They carry the pointwise vector-space structure, the left and
right derivatives (the series analogues of language quotients), the reversal,
the support, and the Parikh image.  A series is *commutative* when it is
constant on words with the same Parikh image.  This module records the basic
definitions of §2 of the paper together with the elementary facts about
derivatives and reversal that the later sections use.
-/

namespace Lax619925.Series

-- the type and the module carrying it have the same name on purpose
set_option linter.dupNamespace false in
/-- A formal power series over the alphabet `α`: a function from words to `ℚ`. -/
abbrev Series (α : Type*) := List α → ℚ

/-- The left derivative with respect to the letter `a`:
    `(leftDeriv a f) w = f (a :: w)`, i.e. the coefficient of `a · w` in `f`. -/
def leftDeriv (α : Type*) (a : α) (f : Series α) : Series α := fun w => f (a :: w)

/-- The right derivative with respect to the letter `a`:
    `(rightDeriv a f) w = f (w ++ [a])`, i.e. the coefficient of `w · a` in `f`. -/
def rightDeriv (α : Type*) (a : α) (f : Series α) : Series α := fun w => f (w ++ [a])

/-- The left derivative with respect to a word `w`, extended homomorphically:
    `(leftDerivWord w f) v = f (w ++ v)`.  This agrees with the paper's recursive
    definition `δ^L_ε f = f` and `δ^L_{a·w} f = δ^L_w (δ^L_a f)`. -/
def leftDerivWord (α : Type*) (w : List α) (f : Series α) : Series α := fun v => f (w ++ v)

/-- The right derivative with respect to a word `w`, extended homomorphically:
    `(rightDerivWord w f) v = f (v ++ w.reverse)`.  This agrees with the paper's
    recursive definition `δ^R_ε f = f` and `δ^R_{w·a} f = δ^R_a (δ^R_w f)`, which
    appends the letters of `w` in reversed order. -/
def rightDerivWord (α : Type*) (w : List α) (f : Series α) : Series α := fun v => f (v ++ w.reverse)

/-- The reversal of a series: `(reversal f) w = f (w.reverse)`. -/
def reversal (α : Type*) (f : Series α) : Series α := fun w => f w.reverse

/-- The support of a series: the set of words on which it is nonzero. -/
def support (α : Type*) (f : Series α) : Set (List α) := {w | f w ≠ 0}

/-- A series is a *polynomial* if its support is finite. -/
def IsPolynomial (α : Type*) (f : Series α) : Prop := (support α f).Finite

/-- The Parikh image (commutative image) of a word: the function counting, for each
    letter, its number of occurrences in the word.  The paper indexes this vector by a
    fixed ordering of the alphabet; the function form is equivalent and needs no order.
    Counting occurrences requires decidable equality on the alphabet. -/
def parikh (α : Type*) [DecidableEq α] (w : List α) : α → ℕ := fun a => w.count a

/-- Two words are *commutatively equivalent* if they have the same multiset of letters,
    i.e. one is obtained from the other by permuting the positions of the letters.
    (Equivalently, when the alphabet has decidable equality, they have the same Parikh
    image.) -/
def CommutativelyEquivalent (α : Type*) (u v : List α) : Prop :=
  Multiset.ofList u = Multiset.ofList v

/-- A series is *commutative* (échangeable) if it takes the same value on all
    commutatively equivalent words. -/
def IsCommutative (α : Type*) (f : Series α) : Prop :=
  ∀ u v, CommutativelyEquivalent α u v → f u = f v

/-- Left and right derivatives commute: for all letters `a, b`,
    `leftDeriv a ∘ rightDeriv b = rightDeriv b ∘ leftDeriv a`.
    (Paper, §2, lemma `leftRightComm`.)  Both sides send a series `f` to the series
    `w ↦ f (a :: w ++ [b])`. -/
axiom LeftRightDerivativesCommute (α : Type*) (a b : α) :
  leftDeriv α a ∘ rightDeriv α b = rightDeriv α b ∘ leftDeriv α a

/-- Reversal is an involution on series. -/
axiom ReversalInvolution (α : Type*) (f : Series α) : reversal α (reversal α f) = f

/-- Reversal interchanges left and right derivatives:
    `reversal (leftDeriv a f) = rightDeriv a (reversal f)`.
    Composing with the involution gives the paper's double-reversal identity
    `rightDeriv a f = reversal (leftDeriv a (reversal f))` used in §4. -/
axiom ReversalSwapsDerivatives (α : Type*) (a : α) (f : Series α) :
  reversal α (leftDeriv α a f) = rightDeriv α a (reversal α f)

end Lax619925.Series
