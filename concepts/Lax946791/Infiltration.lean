import Lax946791.Series
import Lax946791.Prevariety
import Lax946791.Commutativity
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finsupp.Basic
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Eval

/-!
---
title: Infiltration automata and infiltration-finite series
type: theorem
---
A series is *infiltration-finite* if it belongs to a finitely generated
differential infiltration algebra (paper §7): it is an infiltration polynomial in
a finite tuple of series that is closed under left derivatives.  Equivalently (the
coincidence), it is recognised by an *infiltration automaton* `(k, F, Δ)`: a
configuration space `ℚ[X_1, …, X_k]`, a final-weight functional `F`, and a
transition `Δ_a` that extends to an *infiltration* of the configuration space
(the paper's infiltration-algebra structure, §7).  By the fundamental relationship
an infiltration `Δ` is `S − id` for the endomorphism `S = id + Δ`, so the extension
is computed by substituting `X_i ↦ X_i + Δ_a X_i` and subtracting the identity.
The infiltration-finite series form an effective prevariety, so equality and the
commutativity problem are decidable for them; the equality decision reduces to
ideal membership in the configuration polynomial ring (the open leaf), via the same
ideal-chain argument as for the Hadamard and shuffle automata.
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

/-- The unit of the infiltration product: the delta series, `1` on the empty word and
    `0` elsewhere.  Unlike the constant-`1` series (the unit of the pointwise product),
    the delta series is the unit of the *infiltration* product. -/
def infiltrationUnit (α : Type*) : Series α := fun w => if w = [] then 1 else 0

/-- The `n`-fold iterated infiltration power of `f`: `infiltrationPow α f 0 =
    infiltrationUnit α` (the infiltration unit) and `infiltrationPow α f (n+1) = f ↑
    infiltrationPow α f n`.  This is the infiltration analogue of the pointwise power
    `f ^ n` used in `hadamardEval`. -/
noncomputable def infiltrationPow (α : Type*) (f : Series α) (n : ℕ) : Series α :=
  match n with
  | 0 => infiltrationUnit α
  | n + 1 => infiltration α f (infiltrationPow α f n)

/-- The infiltration product of the iterated infiltration powers
    `fs 0 ↑^[d 0] ⋯ fs (k-1) ↑^[d (k-1)]`, where `↑` is the infiltration product and
    `↑^[n]` is the iterated infiltration power (`infiltrationPow`).  This is the
    infiltration analogue of the pointwise monomial product `∏ i, (fs i) ^ (d i)` used in
    `hadamardEval`; it is the infiltration fold of the commutative-associative infiltration
    operation over all indices (the zero-exponent terms contribute the infiltration unit,
    which is the identity).  It is computed as a right-fold over the index list, so that
    the definition does not depend on the `Std.Commutative`/`Std.Associative` instances
    (which the axiom-free concept package cannot carry); the proof package shows it equals
    the corresponding `Finset.fold` (`infiltrationProd_eq_fold`). -/
noncomputable def infiltrationProd (α : Type*) (k : ℕ) (fs : Fin k → Series α) (d : Fin k →₀ ℕ) : Series α :=
  (((Finset.univ : Finset (Fin k)).toList).map (fun i => infiltrationPow α (fs i) (d i))).foldr
    (fun x acc => infiltration α x acc) (infiltrationUnit α)

/-- The evaluation of the polynomial `p` in the *infiltration* algebra, sending `X_i` to
    `fs i`: `infiltrationEval α k fs p = ∑ d ∈ p.support, p.coeff d · (fs 0 ↑^[d 0] ⋯
    fs (k-1) ↑^[d (k-1)])`, where `↑` is the infiltration product and `↑^[n]` is the
    iterated infiltration power.  This is the infiltration analogue of `hadamardEval`
    (which evaluates in the pointwise ring); because the infiltration ring cannot be a
    `CommRing` instance on `Series α` (which already carries the pointwise ring), it is
    defined directly as the sum over the polynomial's support of the coefficients times
    the infiltration product of the iterated powers. -/
noncomputable def infiltrationEval (α : Type*) (k : ℕ) (fs : Fin k → Series α)
    (p : MvPolynomial (Fin k) ℚ) : Series α :=
  p.support.sum fun m => p.coeff m • infiltrationProd α k fs m

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

/-- A series is *infiltration-finite* (working definition, paper §7) if it belongs to a
    finitely generated differential infiltration algebra: it is an infiltration polynomial
    in a finite tuple of series `fs` that is closed under left derivatives, i.e.
    `f = infiltrationEval k fs p` for some polynomial `p`, and `leftDeriv a (fs i)` is
    again an infiltration polynomial in `fs` for every letter `a` and index `i`.  Here
    `infiltrationEval k fs` is the evaluation in the infiltration algebra generated by
    `fs`. -/
def IsInfiltrationFinite (α : Type*) (f : Series α) : Prop :=
  ∃ k : ℕ, ∃ fs : Fin k → Series α, ∃ p : MvPolynomial (Fin k) ℚ,
    f = infiltrationEval α k fs p ∧
    ∀ a : α, ∀ i : Fin k, ∃ q : MvPolynomial (Fin k) ℚ,
      leftDeriv α a (fs i) = infiltrationEval α k fs q

/-- A series is *infiltration-recognisable* if it is recognised by some infiltration
    automaton. -/
def IsInfiltrationRecognisable (α : Type*) (f : Series α) : Prop :=
  ∃ A : InfiltrationAutomaton α, A.recognised = f

/-- A series is infiltration-finite if and only if it is infiltration-recognisable
    (paper §7, the coincidence lemma): the finitely generated differential infiltration
    algebras are exactly the languages of infiltration automata. -/
axiom InfiltrationCoincidence (α : Type*) (f : Series α) :
  IsInfiltrationFinite α f ↔ IsInfiltrationRecognisable α f

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
