import Lax619925.Series
import Lax619925.Prevariety
import Lax619925.Commutativity
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Span.Basic

/-!
---
title: Linearly-finite and recognisable series
type: theorem
---
A series is *linearly finite* if it lies in a finitely generated `ℚ`-space of
series closed under left derivatives; it is *recognisable* if it is recognised by
a linear representation `(k, x, y, M)`, i.e. `f (w) = x · M(w) · y`.  The two
notions coincide (a classical result).  The class of recognisable series is an
effective prevariety — equality is decidable by linear algebra — and hence the
commutativity problem is decidable for it (paper §4).  This is the fully closed
chain in the proof network: no open leaf is involved.
-/

namespace Lax619925.Recognisable

open Lax619925.Series Lax619925.Prevariety Lax619925.Commutativity

/-- A linear representation over `α`: a dimension `k`, a row vector `init` of
    initial weights, a column vector `final` of final weights, and a transition
    function `M` assigning to each letter a `k × k` matrix.  The transition function
    extends homomorphically to words by `M(ε) = 1` and `M(a·w) = M(a) · M(w)` (the
    definition `Mword`), and the series recognised is `f (w) = x · M(w) · y` (the
    definition `sem`).  Both are computed from the four core fields. -/
structure LinearRepresentation (α : Type*) where
  dim : ℕ
  init : Fin dim → ℚ
  final : Fin dim → ℚ
  M : α → Matrix (Fin dim) (Fin dim) ℚ

/-- The word product `M(w)`: `M(ε) = 1` and `M(a·w) = M(a) · M(w)`, the transition
    matrices composed right-to-left along the word. -/
def LinearRepresentation.Mword {α : Type*} (r : LinearRepresentation α) (w : List α) :
    Matrix (Fin r.dim) (Fin r.dim) ℚ :=
  w.foldr (fun a A => r.M a * A) 1

/-- The series recognised by the representation: `f (w) = x · M(w) · y`, the dot
    product of the initial vector with the word product applied to the final vector. -/
def LinearRepresentation.sem {α : Type*} (r : LinearRepresentation α) (w : List α) : ℚ :=
  dotProduct r.init (Matrix.mulVec (r.Mword w) r.final)

/-- A series is *recognisable* if it is recognised by some linear representation. -/
def IsRecognisable (α : Type*) (f : Series α) : Prop :=
  ∃ r : LinearRepresentation α, r.sem = f

/-- A series is *linearly finite* if it belongs to a finitely generated `ℚ`-space of
    series (the span of a finite set of generators `G`) that is closed under left
    derivatives: `f ∈ span G` and `leftDeriv a g ∈ span G` for all `a` and `g ∈ G`. -/
def IsLinearlyFinite (α : Type*) (f : Series α) : Prop :=
  ∃ G : Finset (Series α), f ∈ Submodule.span ℚ G ∧ ∀ a, ∀ g ∈ G, leftDeriv α a g ∈ Submodule.span ℚ G

/-- A series is recognisable if and only if it is linearly finite
    (paper §4, the classical coincidence lemma). -/
axiom RecognisableLinearlyFinite (α : Type*) (f : Series α) :
  IsRecognisable α f ↔ IsLinearlyFinite α f

/-- The class of linearly finite series is closed under scalar product, addition,
    and left derivatives (paper §4, lemma `recognisable closure properties`).  The
    closure is effective: each operation is witnessed by an explicit finite set of
    generators.  These three parts hold over any alphabet. -/
axiom LinearlyFiniteClosure (α : Type*) :
  (∀ (f g : Series α), IsLinearlyFinite α f → IsLinearlyFinite α g → IsLinearlyFinite α (f + g)) ∧
  (∀ (c : ℚ) (f : Series α), IsLinearlyFinite α f → IsLinearlyFinite α (c • f)) ∧
  (∀ (a : α) (f : Series α), IsLinearlyFinite α f → IsLinearlyFinite α (leftDeriv α a f))

/-- The class of linearly finite series over a *finite* alphabet is closed under left
    anti-derivatives (paper §4, lemma `recognisable closure properties`): if `g` is a
    left anti-derivative of a tuple `f` of linearly finite series, then `g` is linearly
    finite.  The finiteness of the alphabet is essential — the witnessing generator set
    is `{g} ∪ ⋃ₐ Gₐ`, one finite set `Gₐ` per letter, so it is finite only when the
    alphabet is. -/
axiom LinearlyFiniteAntiDerivativeClosure (α : Type*) [Fintype α] :
  ∀ (g : Series α) (f : α → Series α), IsLeftAntiDerivative α g f →
      (∀ a, IsLinearlyFinite α (f a)) → IsLinearlyFinite α g

/-- If `f` is recognisable, then its reversal is recognisable (paper §4): the
    transposed representation `(k, yᵀ, xᵀ, Mᵀ)` recognises `reversal f`. -/
axiom RecognisableReversal (α : Type*) (f : Series α) (hf : IsRecognisable α f) :
  IsRecognisable α (reversal α f)

/-- If `f` is recognisable, then its right derivative is recognisable
    (paper §4, corollary `recognisable derive right`), by double reversal:
    `rightDeriv a f = reversal (leftDeriv a (reversal f))`. -/
axiom RecognisableRightDeriv (α : Type*) (a : α) (f : Series α) (hf : IsRecognisable α f) :
  IsRecognisable α (rightDeriv α a f)

/-- The equality (zeroness) problem is decidable for recognisable series over a finite
    alphabet (paper §4): there is a procedure that, given a linear representation,
    decides whether the series it recognises is the zero series.  It checks, by linear
    algebra, that the initial vector annihilates the subspace reachable from the final
    vector.  This is condition (3) in the definition of effective prevariety. -/
axiom RecognisableEqualityDecidable (α : Type*) [Fintype α] :
  ∃ d : LinearRepresentation α → Bool, ∀ r, d r = true ↔ r.sem = 0

/-- The class of recognisable (= linearly finite) series is an effective prevariety
    (paper §4, theorem): there is an effective prevariety whose image is exactly the
    recognisable series, with presentations given by linear representations. -/
axiom RecognisableEffectivePrevariety (α : Type*) [Fintype α] :
  ∃ P : EffectivePrevariety α, ∀ f, IsRecognisable α f ↔ ∃ r : P.Rep, P.sem r = f

/-- In particular, the commutativity problem is decidable for recognisable series over
    a finite alphabet (paper §4): there is a procedure that, given a linear
    representation, decides whether the series it recognises is commutative.  This is
    the meta-theorem applied to the effective prevariety of recognisable series. -/
axiom RecognisableCommutativityDecidable (α : Type*) [Fintype α] :
  ∃ d : LinearRepresentation α → Bool, ∀ r, d r = true ↔ IsCommutative α (r.sem)

end Lax619925.Recognisable
