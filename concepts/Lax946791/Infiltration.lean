import Lax946791.Series
import Lax946791.Prevariety
import Lax946791.Commutativity
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Eval

/-!
---
title: Infiltration automata and infiltration-finite series
type: theorem
---
A series is *infiltration-finite* if it is recognised by an *infiltration
automaton* `(k, F, Δ)`: a configuration space `ℚ[X_1, …, X_k]`, a final-weight
functional `F`, and a transition `Δ_a` that extends to an *infiltration* of the
configuration space (the paper's infiltration-algebra structure, §7).  By the
fundamental relationship an infiltration `Δ` is `S − id` for the endomorphism
`S = id + Δ`, so the extension is computed by substituting `X_i ↦ X_i + Δ_a X_i`
and subtracting the identity.  The infiltration-finite series form an effective
prevariety, so equality and the commutativity problem are decidable for them;
the equality decision reduces to ideal membership in the configuration polynomial
ring (the open leaf), via the same ideal-chain argument as for the Hadamard and
shuffle automata.
-/

namespace Lax946791.Infiltration

open Lax946791.Series Lax946791.Prevariety Lax946791.Commutativity

/-- The recursive core of the infiltration product, defined by primitive recursion on
    the word: `(f ↑ g) ε = f ε · g ε` and
    `(f ↑ g) (a·w) = ((leftDeriv a f) ↑ g) w + (f ↑ (leftDeriv a g)) w
     + ((leftDeriv a f) ↑ (leftDeriv a g)) w`.  The recursion measure is the word
    length (the series arguments change at each step). -/
noncomputable def infiltrationRec (α : Type*) (f g : Series α) (w : List α) : ℚ :=
  match w with
  | [] => f [] * g []
  | a :: w' => infiltrationRec α (leftDeriv α a f) g w'
    + infiltrationRec α f (leftDeriv α a g) w'
    + infiltrationRec α (leftDeriv α a f) (leftDeriv α a g) w'
  termination_by w.length

/-- The infiltration product of two series, characterised by the base case
    `(f ↑ g) ε = f ε · g ε` and the step rule
    `leftDeriv a (f ↑ g) = (leftDeriv a f) ↑ g + f ↑ (leftDeriv a g)
     + (leftDeriv a f) ↑ (leftDeriv a g)`.  It is the synchronising-interleaving
    analogue of the shuffle product (the extra last term allows the two series to
    consume the letter jointly). -/
noncomputable def infiltration (α : Type*) (f g : Series α) : Series α :=
  fun w => infiltrationRec α f g w

/-- An *infiltration automaton* over `α`: a dimension `k ≥ 1` (the number of
    nonterminals `X_1, …, X_k`), a final-weight functional `F`, and a transition
    `Δ` assigning to each letter `a` and nonterminal `X_i` a polynomial `Δ a i` in
    the nonterminals.  The configuration space is the polynomial ring
    `ℚ[X_1, …, X_k] = MvPolynomial (Fin k) ℚ`. -/
structure InfiltrationAutomaton (α : Type*) where
  dim : ℕ
  hdim : 0 < dim
  F : Fin dim → ℚ
  Δ : α → Fin dim → MvPolynomial (Fin dim) ℚ

/-- The word extension of the transition: `Δ_w` is the map of the configuration
    space obtained by composing the letter infiltrations along the word,
    right-to-left.  Each letter infiltration `Δ_a` is `S_a − id`, where `S_a` is
    the endomorphism substituting `X_i ↦ X_i + Δ_a X_i` (the fundamental
    relationship).  The composition law is unchanged from the Hadamard case:
    `Δ_ε` is the identity and `Δ_{a·w} = Δ_w ∘ Δ_a`. -/
noncomputable def InfiltrationAutomaton.Mword {α : Type*} (A : InfiltrationAutomaton α)
    (w : List α) : MvPolynomial (Fin A.dim) ℚ → MvPolynomial (Fin A.dim) ℚ :=
  w.foldr (fun a φ => fun β =>
    φ (MvPolynomial.aeval (fun i => MvPolynomial.X i + A.Δ a i) β - β)) id

/-- The series recognised by the automaton at a configuration `cfg`:
    `⟦A⟧_cfg (w) = F(Δ_w cfg)`, the final-weight functional applied to the
    configuration reached after reading `w`. -/
noncomputable def InfiltrationAutomaton.sem {α : Type*} (A : InfiltrationAutomaton α)
    (cfg : MvPolynomial (Fin A.dim) ℚ) : Series α :=
  fun w => MvPolynomial.eval (fun i => A.F i) (A.Mword w cfg)

/-- The series recognised by the automaton: the semantics at the initial
    configuration `X_0` (the first nonterminal). -/
noncomputable def InfiltrationAutomaton.recognised {α : Type*}
    (A : InfiltrationAutomaton α) : Series α :=
  A.sem (MvPolynomial.X (Fin.mk 0 A.hdim))

/-- A series is *infiltration-finite* if it is recognised by some infiltration
    automaton. -/
def IsInfiltrationFinite (α : Type*) (f : Series α) : Prop :=
  ∃ A : InfiltrationAutomaton α, A.recognised = f

/-- The class of infiltration-finite series is closed under addition, scalar
    multiplication, the infiltration product, and right derivatives (paper §7, the
    closure lemma).  These four parts hold over any alphabet. -/
axiom InfiltrationClosure (α : Type*) :
  (∀ (f g : Series α), IsInfiltrationFinite α f → IsInfiltrationFinite α g → IsInfiltrationFinite α (f + g)) ∧
  (∀ (c : ℚ) (f : Series α), IsInfiltrationFinite α f → IsInfiltrationFinite α (c • f)) ∧
  (∀ (f g : Series α), IsInfiltrationFinite α f → IsInfiltrationFinite α g → IsInfiltrationFinite α (infiltration α f g)) ∧
  (∀ (a : α) (f : Series α), IsInfiltrationFinite α f → IsInfiltrationFinite α (rightDeriv α a f))

/-- The class of infiltration-finite series over a *finite* alphabet is closed under
    left anti-derivatives (paper §7): if `g` is a left anti-derivative of a tuple
    `f` of infiltration-finite series, then `g` is infiltration-finite.  The
    finiteness of the alphabet is essential — the witnessing generator set is
    extended by one series per letter, so it is finite only when the alphabet is. -/
axiom InfiltrationAntiDerivativeClosure (α : Type*) [Fintype α] :
  ∀ (g : Series α) (f : α → Series α), IsLeftAntiDerivative α g f →
      (∀ a, IsInfiltrationFinite α (f a)) → IsInfiltrationFinite α g

/-- The class of infiltration-finite series is an effective prevariety over a finite
    alphabet (paper §7, theorem): there is an effective prevariety whose image is
    exactly the infiltration-finite series, with presentations given by infiltration
    automata. -/
axiom InfiltrationEffectivePrevariety (α : Type*) [Fintype α] :
  ∃ P : EffectivePrevariety α, ∀ f, IsInfiltrationFinite α f ↔ ∃ r : P.Rep, P.sem r = f

/-- The equality (zeroness) problem is decidable for infiltration automata over a
    finite alphabet (paper §7): there is a procedure that, given an infiltration
    automaton, decides whether the series it recognises is the zero series.  The
    decision reduces to ideal membership in the configuration polynomial ring, the
    open leaf. -/
axiom InfiltrationEqualityDecidable (α : Type*) [Fintype α] :
  ∃ d : InfiltrationAutomaton α → Bool, ∀ A, d A = true ↔ A.recognised = 0

/-- In particular, the commutativity problem is decidable for infiltration-finite
    series over a finite alphabet (paper §7): there is a procedure that, given an
    infiltration automaton, decides whether the series it recognises is commutative.
    This is the meta-theorem applied to the effective prevariety of
    infiltration-finite series. -/
axiom InfiltrationCommutativityDecidable (α : Type*) [Fintype α] :
  ∃ d : InfiltrationAutomaton α → Bool, ∀ A, d A = true ↔ IsCommutative α (A.recognised)

end Lax946791.Infiltration
