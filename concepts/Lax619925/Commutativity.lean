import Lax619925.Series
import Lax619925.Prevariety
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic

/-!
---
title: The commutativity problem
type: theorem
---
The commutativity problem asks whether a series is commutative, i.e. constant on
words with the same Parikh image.  The key observation (paper §3) is that
commutativity is characterised by two finite families of equations, *swap* and
*rotate*, which makes it decidable for effective prevarieties (the meta-theorem).
Conversely, the zeroness problem reduces to commutativity: given `f`, one builds
a series `g` over a two-letter-enlarged alphabet, supported on words beginning
with the two fresh letters, such that `g` is commutative exactly when `f = 0`.
-/

namespace Lax619925.Commutativity

open Lax619925.Series Lax619925.Prevariety

/-- The *swap* equation: for all letters `a, b`,
    `leftDeriv a (leftDeriv b f) = leftDeriv b (leftDeriv a f)`.
    It expresses that exchanging the first two letters of a word does not change
    the coefficient. -/
def SatisfiesSwap (α : Type*) (f : Series α) : Prop :=
  ∀ a b, leftDeriv α a (leftDeriv α b f) = leftDeriv α b (leftDeriv α a f)

/-- The *rotate* equation: for all letters `a`,
    `leftDeriv a f = rightDeriv a f`.
    It expresses that moving the first letter to the end does not change the
    coefficient. -/
def SatisfiesRotate (α : Type*) (f : Series α) : Prop :=
  ∀ a, leftDeriv α a f = rightDeriv α a f

/-- A series `g` is a *left anti-derivative* of the tuple of series `f` if
    `leftDeriv a g = f a` for every letter `a`.  Once the value `g ε` is fixed,
    left anti-derivatives are unique. -/
def IsLeftAntiDerivative (α : Type*) (g : Series α) (f : α → Series α) : Prop :=
  ∀ a, leftDeriv α a g = f a

/-- The alphabet `α` extended by two fresh letters `fresh0` and `fresh1`, modelling
    the paper's enlarged alphabet `Γ = Σ ∪ {a, b}`. -/
inductive Fresh2 (α : Type*) where
  | letter : α → Fresh2 α
  | fresh0 : Fresh2 α
  | fresh1 : Fresh2 α

/-- Lift a word over the extended alphabet back to a word over `α`, returning
    `some` of the original word when no fresh letter occurs and `none` otherwise. -/
def liftWordOpt (α : Type*) (w : List (Fresh2 α)) : Option (List α) :=
  match w with
  | [] => some []
  | s :: w' =>
      match s with
      | .letter a => (liftWordOpt α w').map (fun rest => a :: rest)
      | .fresh0 | .fresh1 => none

/-- The extension of a series over `α` to the extended alphabet `Fresh2 α`, by zero
    on words containing one of the two fresh letters. -/
def extendSeries (α : Type*) (f : Series α) : Series (Fresh2 α) := fun w =>
  match liftWordOpt α w with
  | some rest => f rest
  | none => 0

/-- The series `g` over the extended alphabet associated to `f` in the paper's
    equality-reduces-to-commutativity construction: `g` is zero except on words
    beginning with the two fresh letters, where `g (fresh0 :: fresh1 :: rest) = f (rest)`
    (with `f` extended by zero).  Hence `leftDeriv b (leftDeriv a g) = extendSeries f`
    for `a = fresh0`, `b = fresh1`, while every other second left derivative vanishes;
    in particular `g ε = g x = 0` for every letter `x`. -/
def antiDerivativeSeries (α : Type*) (f : Series α) : Series (Fresh2 α) := fun w =>
  match w with
  | .fresh0 :: .fresh1 :: rest => extendSeries α f rest
  | _ => 0

/-- A series is commutative if and only if it satisfies the swap and rotate equations
    for all letters (paper §3, lemma `commutativity`).  Swaps and rotations generate
    all commutatively equivalent words, so the two finite families of equations
    characterise commutativity. -/
axiom FiniteAxiomatisation (α : Type*) (f : Series α) :
  IsCommutative α f ↔ SatisfiesSwap α f ∧ SatisfiesRotate α f

/-- The commutativity problem is decidable for effective prevarieties of series
    (paper §3, theorem `commutativity for effective prevarieties`): over a finite
    alphabet, there is a procedure that, given a presentation `r`, decides whether
    `sem r` is commutative — it returns `true` exactly when `sem r` is commutative.
    By the finite axiomatisation this reduces to finitely many equality tests on
    presentations, decided by the prevariety's `decEq`. -/
axiom EffectivePrevarietyCommutativityDecidable (α : Type*) [Fintype α]
    (P : EffectivePrevariety α) :
  ∃ d : P.Rep → Bool, ∀ r, d r = true ↔ IsCommutative α (P.sem r)

/-- The series `antiDerivativeSeries f` is commutative if and only if `f = 0`
    (paper §3, lemma `equality reduces to commutativity`).  If `f ≠ 0` with
    `f (w) ≠ 0` for some word `w`, then `g (fresh0 · fresh1 · w) = f (w) ≠ 0` while
    `g (fresh1 · fresh0 · w) = 0`, and the two words are commutatively equivalent,
    so `g` is not commutative; conversely `f = 0` forces `g = 0`. -/
axiom AntiDerivativeCommutativeIffZero (α : Type*) (f : Series α) :
  IsCommutative (Fresh2 α) (antiDerivativeSeries α f) ↔ f = 0

end Lax619925.Commutativity
