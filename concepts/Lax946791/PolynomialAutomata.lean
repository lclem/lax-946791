import Lax946791.Series
import Lax946791.Hadamard
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Eval

/-!
---
title: Polynomial automata and Hadamard automata
type: theorem
---
A *polynomial automaton* (paper appendix) is a weighted automaton whose
configuration space is the vector space `ℚ^k` and whose letter actions are
polynomial maps.  It is the dual of the Hadamard automaton: here the
configuration is a *point* and the final weight is a *polynomial*, whereas the
Hadamard automaton's configuration is a *polynomial* and its final weight is a
*point*.  The main result (paper appendix) is that a series is recognisable by a
polynomial automaton if and only if its reversal is Hadamard-recognisable: the
duality swaps the configuration and the final weight, and the reversal accounts
for the order in which the transitions are composed.
-/

namespace Lax946791.PolynomialAutomata

open Lax946791.Series Lax946791.Hadamard

/-- A *polynomial automaton* over `α`: a dimension `k ≥ 1`, an initial
    configuration `qI : ℚ^k`, a final polynomial `F : ℚ[X_1, …, X_k]`, and a
    transition `Δ` assigning to each letter `a` a polynomial map
    `Δ_a : ℚ^k → ℚ^k` (a `k`-tuple of polynomials).  The configuration space is
    the vector space `ℚ^k`, and the letter action is `q · a = Δ_a(q)` (evaluate
    the transition polynomials at the point `q`). -/
structure PolynomialAutomaton (α : Type*) where
  dim : ℕ
  hdim : 0 < dim
  qI : Fin dim → ℚ
  F : MvPolynomial (Fin dim) ℚ
  Δ : α → Fin dim → MvPolynomial (Fin dim) ℚ

/-- The action of a letter `a` on a configuration `q`: `q · a = Δ_a(q)`,
    evaluate the transition polynomials at the point `q`. -/
noncomputable def PolynomialAutomaton.action {α : Type*} (A : PolynomialAutomaton α)
    (q : Fin A.dim → ℚ) (a : α) : Fin A.dim → ℚ :=
  fun i => MvPolynomial.eval q (A.Δ a i)

/-- The action of a word `w` on a configuration `q`: `q · w`, the letter actions
    iterated left-to-right. -/
noncomputable def PolynomialAutomaton.wordAction {α : Type*} (A : PolynomialAutomaton α)
    (q : Fin A.dim → ℚ) (w : List α) : Fin A.dim → ℚ :=
  w.foldl (fun q a => A.action q a) q

/-- The series recognised by the automaton at a configuration `q`:
    `⟦A⟧_q (w) = F(q · w)`, the final polynomial `F` evaluated at the point
    `q · w` reached after reading `w`. -/
noncomputable def PolynomialAutomaton.sem {α : Type*} (A : PolynomialAutomaton α)
    (q : Fin A.dim → ℚ) : Series α :=
  fun w => MvPolynomial.eval (A.wordAction q w) A.F

/-- The series recognised by the automaton: the semantics at the initial
    configuration `qI`. -/
noncomputable def PolynomialAutomaton.recognised {α : Type*} (A : PolynomialAutomaton α) : Series α :=
  A.sem A.qI

/-- A series is *polynomial-recognisable* if it is recognised by some polynomial
    automaton. -/
def IsPolynomialRecognisable (α : Type*) (f : Series α) : Prop :=
  ∃ A : PolynomialAutomaton α, A.recognised = f

/-- A series is recognisable by a polynomial automaton if and only if its
    reversal is Hadamard-recognisable (paper appendix).  The duality swaps the
    configuration (point ↔ polynomial) and the final weight (polynomial ↔
    point), and the reversal accounts for the order of composition of the
    transitions. -/
axiom PolynomialHadamardEquivalence (α : Type*) (f : Series α) :
  IsPolynomialRecognisable α f ↔ IsHadamardRecognisable α (reversal α f)

end Lax946791.PolynomialAutomata
