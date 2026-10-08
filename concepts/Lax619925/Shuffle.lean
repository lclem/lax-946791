import Lax619925.Series
import Lax619925.Prevariety
import Lax619925.Commutativity
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finsupp.Basic
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Eval

/-!
---
title: Shuffle automata and shuffle-finite series
type: theorem
---
A series is *shuffle-finite* if it belongs to a finitely generated differential
shuffle algebra (paper §6.2.2): it is a shuffle polynomial in a finite tuple of
series that is closed under left derivatives.  Equivalently (the coincidence),
it is recognised by a *shuffle automaton* `(k, F, Δ)`: a configuration space
`ℚ[X_1, …, X_k]`, a final-weight functional `F`, and a transition `Δ_a` that
extends to a *derivation* of the configuration space (the paper's differential-
algebra structure, §6).  The shuffle-finite series form an effective prevariety,
so equality and the commutativity problem are decidable for them; the equality
decision reduces to ideal membership in the configuration polynomial ring (the
open leaf), via the same ideal-chain argument as for the Hadamard and
infiltration automata.
-/

namespace Lax619925.Shuffle

open Lax619925.Series Lax619925.Prevariety Lax619925.Commutativity

/-- The recursive core of the shuffle product, defined by primitive recursion on the
    word: `(f ⧢ g) ε = f ε · g ε` and
    `(f ⧢ g) (a·w) = ((leftDeriv a f) ⧢ g) w + (f ⧢ (leftDeriv a g)) w`, the Leibniz
    rule.  This is the unique series satisfying the characterisation.  The recursion
    measure is the word length (the series arguments `f`, `g` change at each step, so
    structural recursion on the word alone does not apply). -/
noncomputable def shuffleRec (α : Type*) (f g : Series α) (w : List α) : ℚ :=
  match w with
  | [] => f [] * g []
  | a :: w' => shuffleRec α (leftDeriv α a f) g w' + shuffleRec α f (leftDeriv α a g) w'
  termination_by w.length

/-- The shuffle product of two series, characterised by the Leibniz rule
    `leftDeriv a (f ⧢ g) = (leftDeriv a f) ⧢ g + f ⧢ (leftDeriv a g)` and the
    initial condition `(f ⧢ g) ε = f ε · g ε`.  Equivalently,
    `(f ⧢ g) w = Σ_{u·v = w} f u · g v`, the sum over all interleavings of `u`
    and `v` that yield `w`. -/
noncomputable def shuffle (α : Type*) (f g : Series α) : Series α :=
  fun w => shuffleRec α f g w

/-- The unit of the shuffle product: the delta series, `1` on the empty word and `0`
    elsewhere.  Unlike the constant-`1` series (the unit of the pointwise product), the
    delta series is the unit of the *shuffle* product. -/
def shuffleUnit (α : Type*) : Series α := fun w => if w = [] then 1 else 0

/-- The `n`-fold iterated shuffle power of `f`: `shufflePow α f 0 = shuffleUnit α` (the
    shuffle unit) and `shufflePow α f (n+1) = f ⧢ shufflePow α f n`.  This is the shuffle
    analogue of the pointwise power `f ^ n` used in `hadamardEval`. -/
noncomputable def shufflePow (α : Type*) (f : Series α) (n : ℕ) : Series α :=
  match n with
  | 0 => shuffleUnit α
  | n + 1 => shuffle α f (shufflePow α f n)

/-- The shuffle product of the iterated shuffle powers `fs 0 ⧢^[d 0] ⧢ ⋯ ⧢ fs (k-1) ⧢^[d (k-1)]`,
    where `⧢` is the shuffle product and `⧢^[n]` is the iterated shuffle power
    (`shufflePow`).  This is the shuffle analogue of the pointwise monomial product
    `∏ i, (fs i) ^ (d i)` used in `hadamardEval`; it is the shuffle fold of the
    commutative-associative shuffle operation over all indices (the zero-exponent terms
    contribute the shuffle unit, which is the identity).  It is computed as a right-fold
    over the index list, so that the definition does not depend on the `Std.Commutative`/
    `Std.Associative` instances (which the axiom-free concept package cannot carry); the
    proof package shows it equals the corresponding `Finset.fold` (`shuffleProd_eq_fold`). -/
noncomputable def shuffleProd (α : Type*) (k : ℕ) (fs : Fin k → Series α) (d : Fin k →₀ ℕ) : Series α :=
  (((Finset.univ : Finset (Fin k)).toList).map (fun i => shufflePow α (fs i) (d i))).foldr
    (fun x acc => shuffle α x acc) (shuffleUnit α)

/-- The evaluation of the polynomial `p` in the *shuffle* algebra, sending `X_i` to
    `fs i`: `shuffleEval α k fs p = ∑ d ∈ p.support, p.coeff d · (fs 0 ⧢^[d 0] ⧢ ⋯ ⧢
    fs (k-1) ⧢^[d (k-1)])`, where `⧢` is the shuffle product and `⧢^[n]` is the iterated
    shuffle power.  This is the shuffle analogue of `hadamardEval` (which evaluates in the
    pointwise ring); because the shuffle ring cannot be a `CommRing` instance on `Series α`
    (which already carries the pointwise ring), it is defined directly as the sum over the
    polynomial's support of the coefficients times the shuffle product of the iterated
    powers. -/
noncomputable def shuffleEval (α : Type*) (k : ℕ) (fs : Fin k → Series α)
    (p : MvPolynomial (Fin k) ℚ) : Series α :=
  p.support.sum fun m => p.coeff m • shuffleProd α k fs m

/-- The unique derivation of the polynomial ring `MvPolynomial σ R` sending the
    variable `X i` to `φ i`, defined by the Leibniz rule on monomials:
    `δ_φ(X^m) = Σ_i m_i · X^{m - e_i} · φ i`.  This is the extension of the
    letter transition `Δ_a` (a map on the variables) to a derivation of the whole
    configuration space. -/
noncomputable def derivationExt {σ : Type*} [Fintype σ] {R : Type*} [CommRing R]
    (φ : σ → MvPolynomial σ R) : MvPolynomial σ R → MvPolynomial σ R :=
  fun p => p.support.sum fun m =>
    p.coeff m • (∑ i : σ, ((m i : R) • MvPolynomial.monomial (m - Finsupp.single i 1) 1) * φ i)

/-- A *shuffle automaton* over `α`: a dimension `k ≥ 1` (the number of
    nonterminals `X_1, …, X_k`), a final-weight functional `F`, and a transition
    `Δ` assigning to each letter `a` and nonterminal `X_i` a polynomial `Δ a i` in
    the nonterminals.  The configuration space is the polynomial ring
    `ℚ[X_1, …, X_k] = MvPolynomial (Fin k) ℚ`. -/
structure ShuffleAutomaton (α : Type*) where
  dim : ℕ
  hdim : 0 < dim
  F : Fin dim → ℚ
  Δ : α → Fin dim → MvPolynomial (Fin dim) ℚ

/-- The word extension of the transition: `Δ_w` is the map of the configuration
    space obtained by composing the letter derivations `derivationExt (Δ a)` along
    the word, right-to-left.  The law is unchanged from the Hadamard case:
    `Δ_ε` is the identity and `Δ_{a·w} = Δ_w ∘ Δ_a`; the only difference is that
    each `Δ_a` is now a derivation rather than an endomorphism. -/
noncomputable def ShuffleAutomaton.Mword {α : Type*} (A : ShuffleAutomaton α) (w : List α) :
    MvPolynomial (Fin A.dim) ℚ → MvPolynomial (Fin A.dim) ℚ :=
  w.foldr (fun a φ => fun β => φ (derivationExt (A.Δ a) β)) id

/-- The series recognised by the automaton at a configuration `cfg`:
    `⟦A⟧_cfg (w) = F(Δ_w cfg)`, the final-weight functional applied to the
    configuration reached after reading `w`. -/
noncomputable def ShuffleAutomaton.sem {α : Type*} (A : ShuffleAutomaton α)
    (cfg : MvPolynomial (Fin A.dim) ℚ) : Series α :=
  fun w => MvPolynomial.eval (fun i => A.F i) (A.Mword w cfg)

/-- The series recognised by the automaton: the semantics at the initial
    configuration `X_0` (the first nonterminal). -/
noncomputable def ShuffleAutomaton.recognised {α : Type*} (A : ShuffleAutomaton α) :
    Series α :=
  A.sem (MvPolynomial.X (Fin.mk 0 A.hdim))

/-- A series is *shuffle-finite* (working definition, paper §6.2.2) if it belongs to a
    finitely generated differential shuffle algebra: it is a shuffle polynomial in a
    finite tuple of series `fs` that is closed under left derivatives, i.e.
    `f = shuffleEval k fs p` for some polynomial `p`, and `leftDeriv a (fs i)` is again a
    shuffle polynomial in `fs` for every letter `a` and index `i`.  Here `shuffleEval k fs`
    is the evaluation in the shuffle algebra generated by `fs`. -/
def IsShuffleFinite (α : Type*) (f : Series α) : Prop :=
  ∃ k : ℕ, ∃ fs : Fin k → Series α, ∃ p : MvPolynomial (Fin k) ℚ,
    f = shuffleEval α k fs p ∧
    ∀ a : α, ∀ i : Fin k, ∃ q : MvPolynomial (Fin k) ℚ,
      leftDeriv α a (fs i) = shuffleEval α k fs q

/-- A series is *shuffle-recognisable* if it is recognised by some shuffle automaton. -/
def IsShuffleRecognisable (α : Type*) (f : Series α) : Prop :=
  ∃ A : ShuffleAutomaton α, A.recognised = f

/-- A series is shuffle-finite if and only if it is shuffle-recognisable
    (paper §6, the coincidence lemma): the finitely generated differential shuffle
    algebras are exactly the languages of shuffle automata. -/
axiom ShuffleCoincidence (α : Type*) (f : Series α) :
  IsShuffleFinite α f ↔ IsShuffleRecognisable α f

/-- The class of shuffle-finite series is closed under addition, scalar
    multiplication, the shuffle product, and right derivatives (paper §6, the
    closure lemma).  These four parts hold over any alphabet. -/
axiom ShuffleClosure (α : Type*) :
  (∀ (f g : Series α), IsShuffleFinite α f → IsShuffleFinite α g → IsShuffleFinite α (f + g)) ∧
  (∀ (c : ℚ) (f : Series α), IsShuffleFinite α f → IsShuffleFinite α (c • f)) ∧
  (∀ (f g : Series α), IsShuffleFinite α f → IsShuffleFinite α g → IsShuffleFinite α (shuffle α f g)) ∧
  (∀ (a : α) (f : Series α), IsShuffleFinite α f → IsShuffleFinite α (rightDeriv α a f))

/-- The class of shuffle-finite series over a *finite* alphabet is closed under left
    anti-derivatives (paper §6): if `g` is a left anti-derivative of a tuple `f` of
    shuffle-finite series, then `g` is shuffle-finite.  The finiteness of the
    alphabet is essential — the witnessing generator set is extended by one series
    per letter, so it is finite only when the alphabet is. -/
axiom ShuffleAntiDerivativeClosure (α : Type*) [Fintype α] :
  ∀ (g : Series α) (f : α → Series α), IsLeftAntiDerivative α g f →
      (∀ a, IsShuffleFinite α (f a)) → IsShuffleFinite α g

/-- The class of shuffle-finite series is an effective prevariety over a finite
    alphabet (paper §6, theorem): there is an effective prevariety whose image is
    exactly the shuffle-finite series, with presentations given by shuffle
    automata. -/
axiom ShuffleEffectivePrevariety (α : Type*) [Fintype α] :
  ∃ P : EffectivePrevariety α, ∀ f, IsShuffleFinite α f ↔ ∃ r : P.Rep, P.sem r = f

/-- The equality (zeroness) problem is decidable for shuffle automata over a finite
    alphabet (paper §6): there is a procedure that, given a shuffle automaton,
    decides whether the series it recognises is the zero series.  The decision
    reduces to ideal membership in the configuration polynomial ring, the open
    leaf. -/
axiom ShuffleEqualityDecidable (α : Type*) [Fintype α] :
  ∃ d : ShuffleAutomaton α → Bool, ∀ A, d A = true ↔ A.recognised = 0

/-- In particular, the commutativity problem is decidable for shuffle-finite series
    over a finite alphabet (paper §6): there is a procedure that, given a shuffle
    automaton, decides whether the series it recognises is commutative.  This is the
    meta-theorem applied to the effective prevariety of shuffle-finite series. -/
axiom ShuffleCommutativityDecidable (α : Type*) [Fintype α] :
  ∃ d : ShuffleAutomaton α → Bool, ∀ A, d A = true ↔ IsCommutative α (A.recognised)

end Lax619925.Shuffle
