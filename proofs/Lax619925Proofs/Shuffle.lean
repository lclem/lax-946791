import Lax619925.Shuffle
import Lax619925.Series
import Lax619925.Prevariety
import Lax619925.Commutativity
import Lax619925.IdealMembership
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.Finset.Fold
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Bool.Basic
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.Derivation
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Algebra.Algebra.Basic
import Mathlib.RingTheory.Ideal.Basic
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Span
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.Tactic

-- `letI` is used to register the `IsNoetherianRing` instance required by
-- `Ideal.fg_of_isNoetherianRing`; the `haveILetI` linter's suggestion to use
-- `let` would drop that instance, so the linter is disabled here.
set_option linter.style.haveILetI false

/-!
---
title: Shuffle automata: closure, equality, and commutativity decidability
type: theorem
---
Proves the five statements of the `Lax619925.Shuffle` concept: the shuffle-finite
series are closed under addition, scalar multiplication, the shuffle product, and
right derivatives (the closure lemma); over a finite alphabet they are closed under
left anti-derivatives; they form an effective prevariety; the equality (zeroness)
problem is decidable for shuffle automata, reducing to ideal membership in the
configuration polynomial ring (the open leaf) via the ideal-chain argument; and the
commutativity problem is decidable (the meta-theorem applied to the effective
prevariety).

The key structural difference from the Hadamard case is that a shuffle transition
`Δ_a` extends to a *derivation* of the configuration space (linear, satisfying the
Leibniz rule) rather than an endomorphism (a ring homomorphism).  Consequently the
word map `Mword` is `ℚ`-linear but not multiplicative, and the stabilised orbit
ideal is a bi-ideal by *linearity* (the Leibniz rule) rather than by `Ideal.map_span`.
The semantics `sem A` is a homomorphism for the *shuffle* product (not the pointwise
product), which is what makes the shuffle-finite series closed under the shuffle
product.
-/

namespace Lax619925Proofs.Shuffle

open Lax619925.Series Lax619925.Prevariety Lax619925.Commutativity Lax619925.Shuffle
open Lax619925.IdealMembership
open MvPolynomial
open Classical

variable {α : Type*}

/-! ### The shuffle product is a commutative ring multiplication -/

/-- The left derivative is `ℚ`-linear: it preserves addition. -/
private theorem leftDeriv_add (a : α) (f g : Series α) :
    leftDeriv α a (f + g) = leftDeriv α a f + leftDeriv α a g := by
  funext w; dsimp [leftDeriv]

/-- The left derivative is `ℚ`-linear: it preserves scalar multiplication. -/
private theorem leftDeriv_smul (a : α) (c : ℚ) (f : Series α) :
    leftDeriv α a (c • f) = c • leftDeriv α a f := by
  funext w; dsimp [leftDeriv]

/-- The left derivative of the zero series is zero. -/
private theorem leftDeriv_zero (a : α) : leftDeriv α a 0 = 0 := by
  funext w; dsimp [leftDeriv]

/-- The left derivative of the shuffle unit is zero: a non-empty word is never the empty
    word, so `leftDeriv a shuffleUnit = 0`. -/
private theorem shuffleUnit_leftDeriv (a : α) : leftDeriv α a (shuffleUnit α) = 0 := by
  funext w
  dsimp [leftDeriv, shuffleUnit]

/-- The Leibniz rule: `leftDeriv a (f ⧢ g) = (leftDeriv a f) ⧢ g + f ⧢ (leftDeriv a g)`.
    This holds by definition: the shuffle recursion's step case is exactly the Leibniz
    rule, and the left derivative is the map `f ↦ f ∘ (a · -)`. -/
private theorem shuffleLeibniz (f g : Series α) (a : α) :
    leftDeriv α a (shuffle α f g) = shuffle α (leftDeriv α a f) g + shuffle α f (leftDeriv α a g) := by
  funext w
  dsimp [leftDeriv, shuffle]
  simp [shuffleRec]

/-- The two recursion equations for `shuffleRec`, as simp lemmas (the `match` is defined
    with `termination_by`, so it does not unfold definitionally; `simp [shuffleRec]` does).
    These are used in the ring-axiom proofs below. -/
theorem shuffleRec_nil (f g : Series α) : shuffleRec α f g [] = f [] * g [] := by
  simp [shuffleRec]
theorem shuffleRec_cons (f g : Series α) (a : α) (w : List α) :
    shuffleRec α f g (a :: w) = shuffleRec α (leftDeriv α a f) g w + shuffleRec α f (leftDeriv α a g) w := by
  simp [shuffleRec]

/-- The shuffle product with the zero series is zero. -/
private theorem shuffle_zero_right (f : Series α) : shuffle α f 0 = 0 := by
  funext w
  have : ∀ (f : Series α), shuffleRec α f 0 w = 0 := by
    induction w with
    | nil =>
        intro f
        simp [shuffleRec_nil]
    | cons a w' ih =>
        intro f
        simp [shuffleRec_cons]
        rw [leftDeriv_zero a, ih f, ih (leftDeriv α a f)]
        simp
  exact this f

/-- The shuffle product is commutative: `f ⧢ g = g ⧢ f`.  Both sides satisfy the same
    recursion (the Leibniz rule and the symmetric initial condition), proved by
    induction on the word. -/
private theorem shuffle_comm (f g : Series α) : shuffle α f g = shuffle α g f := by
  funext w
  have : ∀ (f g : Series α), shuffleRec α f g w = shuffleRec α g f w := by
    induction w with
    | nil =>
        intro f g
        simp [shuffleRec_nil]
        ring
    | cons a w' ih =>
        intro f g
        simp [shuffleRec_cons]
        rw [ih (leftDeriv α a f) g, ih f (leftDeriv α a g)]
        simp [add_comm]
  exact this f g

/-- The shuffle product with the zero series is zero, in the first argument. -/
private theorem shuffle_zero_left (f : Series α) : shuffle α 0 f = 0 := by
  rw [shuffle_comm, shuffle_zero_right]

/-- Pointwise form of `shuffle_zero_left`: `shuffleRec α 0 f w = 0`. -/
private theorem shuffleRec_zero_left (f : Series α) (w : List α) : shuffleRec α 0 f w = 0 := by
  have := shuffle_zero_left f
  simpa [shuffle] using congrArg (fun s => s w) this

/-- The shuffle product is left-distributive over addition:
    `(f + g) ⧢ h = f ⧢ h + g ⧢ h`. -/
private theorem shuffle_add_left (f g h : Series α) :
    shuffle α (f + g) h = shuffle α f h + shuffle α g h := by
  funext w
  have : ∀ (f g h : Series α), shuffleRec α (f + g) h w = shuffleRec α f h w + shuffleRec α g h w := by
    induction w with
    | nil =>
        intro f g h
        simp [shuffleRec_nil]
        ring
    | cons a w' ih =>
        intro f g h
        simp [shuffleRec_cons]
        rw [leftDeriv_add a f g, ih (leftDeriv α a f) (leftDeriv α a g) h, ih f g (leftDeriv α a h)]
        simp [add_assoc, add_comm, add_left_comm]
  exact this f g h

/-- The shuffle product is right-distributive over addition: `f ⧢ (g + h) = f ⧢ g + f ⧢ h`. -/
private theorem shuffle_add_right (f g h : Series α) :
    shuffle α f (g + h) = shuffle α f g + shuffle α f h := by
  have := shuffle_add_left g h f
  simpa [shuffle_comm] using this

/-- The shuffle product is associative: `(f ⧢ g) ⧢ h = f ⧢ (g ⧢ h)`.  The induction step
    uses the Leibniz rule and distributivity. -/
private theorem shuffle_assoc (f g h : Series α) :
    shuffle α (shuffle α f g) h = shuffle α f (shuffle α g h) := by
  funext w
  have : ∀ (f g h : Series α), shuffleRec α (shuffleRec α f g) h w =
      shuffleRec α f (shuffleRec α g h) w := by
    induction w with
    | nil =>
        intro f g h
        simp [shuffleRec_nil]
        ring
    | cons a w' ih =>
        intro f g h
        simp [shuffleRec_cons]
        -- LHS: `(leftDeriv a (f ⧢ g)) ⧢ h` + `(f ⧢ g) ⧢ (leftDeriv a h)`
        -- RHS: `(leftDeriv a f) ⧢ (g ⧢ h)` + `f ⧢ (leftDeriv a (g ⧢ h))`
        have hLeib_fg : leftDeriv α a (shuffleRec α f g) =
            shuffleRec α (leftDeriv α a f) g + shuffleRec α f (leftDeriv α a g) :=
          shuffleLeibniz f g a
        have hLeib_gh : leftDeriv α a (shuffleRec α g h) =
            shuffleRec α (leftDeriv α a g) h + shuffleRec α g (leftDeriv α a h) :=
          shuffleLeibniz g h a
        rw [hLeib_fg, hLeib_gh]
        -- Distribute the shuffle product over the added terms.
        have hdistL : shuffleRec α (shuffleRec α (leftDeriv α a f) g + shuffleRec α f (leftDeriv α a g)) h w' =
            shuffleRec α (shuffleRec α (leftDeriv α a f) g) h w' +
            shuffleRec α (shuffleRec α f (leftDeriv α a g)) h w' :=
          congrArg (fun s => s w') (shuffle_add_left (shuffleRec α (leftDeriv α a f) g)
              (shuffleRec α f (leftDeriv α a g)) h)
        have hdistR : shuffleRec α f (shuffleRec α (leftDeriv α a g) h + shuffleRec α g (leftDeriv α a h)) w' =
            shuffleRec α f (shuffleRec α (leftDeriv α a g) h) w' +
            shuffleRec α f (shuffleRec α g (leftDeriv α a h)) w' :=
          congrArg (fun s => s w') (shuffle_add_right f (shuffleRec α (leftDeriv α a g) h)
              (shuffleRec α g (leftDeriv α a h)))
        rw [hdistL, hdistR]
        -- Apply the induction hypothesis to each of the three LHS summands.
        rw [ih (leftDeriv α a f) g h, ih f (leftDeriv α a g) h, ih f g (leftDeriv α a h)]
        simp [add_assoc, add_comm]
  exact this f g h

/-- The delta series is the left unit of the shuffle product: `shuffleUnit ⧢ f = f`. -/
private theorem shuffle_unit_left (f : Series α) : shuffle α (shuffleUnit α) f = f := by
  funext w
  have : ∀ (f : Series α), shuffleRec α (shuffleUnit α) f w = f w := by
    induction w with
    | nil =>
        intro f
        simp [shuffleRec_nil, shuffleUnit]
    | cons a w' ih =>
        intro f
        simp [shuffleRec_cons]
        rw [shuffleUnit_leftDeriv a, shuffleRec_zero_left f w', ih (leftDeriv α a f)]
        simp [leftDeriv]
  exact this f

/-- The delta series is the right unit of the shuffle product: `f ⧢ shuffleUnit = f`. -/
private theorem shuffle_unit_right (f : Series α) : shuffle α f (shuffleUnit α) = f := by
  rw [shuffle_comm]
  exact shuffle_unit_left f

/-- The shuffle product is `ℚ`-bilinear: it preserves scalar multiplication in each
    argument, `(c • f) ⧢ g = c • (f ⧢ g)`. -/
private theorem shuffle_smul_left (c : ℚ) (f g : Series α) :
    shuffle α (c • f) g = c • shuffle α f g := by
  funext w
  have : ∀ (f g : Series α), shuffleRec α (c • f) g w = c • shuffleRec α f g w := by
    induction w with
    | nil =>
        intro f g
        simp [shuffleRec_nil]
        ring
    | cons a w' ih =>
        intro f g
        simp [shuffleRec_cons, leftDeriv_smul, ih, mul_add]
  exact this f g

/-- The shuffle product is `ℚ`-bilinear in the second argument: `f ⧢ (c • g) = c • (f ⧢ g)`. -/
private theorem shuffle_smul_right (c : ℚ) (f g : Series α) :
    shuffle α f (c • g) = c • shuffle α f g := by
  rw [shuffle_comm, shuffle_smul_left c g f, shuffle_comm]

/-! ### `derivationExt` is a derivation: it coincides with `MvPolynomial.mkDerivation` -/

/-- The value of the derivation on a monomial `X^m`:
    `D_φ m = Σ_i (m_i) · X^{m - e_i} · φ_i`.  The derivation `derivationExt φ` is the `ℚ`-linear
    extension of the map `X^m ↦ D_φ m` (and is in fact `MvPolynomial.mkDerivation φ`). -/
private noncomputable def derivMono {σ : Type*} [Fintype σ] {R : Type*} [CommRing R]
    (φ : σ → MvPolynomial σ R) (m : σ →₀ ℕ) : MvPolynomial σ R :=
  ∑ i : σ, ((m i : R) • monomial (m - Finsupp.single i 1) 1) * φ i

-- `derivationExt φ p` is the sum, over the support of `p`, of the coefficient times the monomial
-- derivative.  This is the definition, with the inner sum named `derivMono`.
private theorem derivationExt_eq_sum {σ : Type*} [Fintype σ] {R : Type*} [CommRing R]
    (φ : σ → MvPolynomial σ R) (p : MvPolynomial σ R) :
    derivationExt φ p = p.support.sum fun m => p.coeff m • derivMono φ m := by
  dsimp [derivationExt, derivMono]

-- A `ℚ`-linear map commutes with a finite sum.
private theorem linMap_finset_sum {R M N : Type*} [AddCommMonoid M] [AddCommMonoid N]
    [Semiring R] [Module R M] [Module R N] {ι : Type*} (f : M →ₗ[R] N)
    (s : Finset ι) (g : ι → M) : f (∑ i ∈ s, g i) = ∑ i ∈ s, f (g i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a is ih ha =>
      simp [ih, ha]

-- `MvPolynomial.mkDerivation` on a monomial is the monomial derivative.  The `mkDerivation` form
-- is a `Finsupp.sum` with the self-module action `•` (which is multiplication for `MvPolynomial`);
-- `derivMono` is a `Finset.sum` over all of `σ` with the `R`-module action.  Converting the
-- `Finsupp.sum` to the `univ` `Finset` sum (via `sum_fintype`, the summand vanishing at `k = 0`),
-- the self-module `•` to `*`, and the monomial `X^{m - e_i} (m_i)` to `(m_i) · X^{m - e_i}` gives
-- exactly `derivMono`.
private theorem mkDerivation_monomial_derivMono {σ : Type*} [Fintype σ] {R : Type*} [CommRing R]
    (φ : σ → MvPolynomial σ R) (m : σ →₀ ℕ) :
    MvPolynomial.mkDerivation R φ (monomial m 1) = derivMono φ m := by
  rw [MvPolynomial.mkDerivation_monomial R φ m 1, one_smul]
  -- The goal is `∑ i : σ, X^{m - e_i} (m_i) • φ_i` (the self-module `•`, which is `*` for
  -- `MvPolynomial`) = `derivMono φ m`.  Restate the LHS with `*` (definitionally the same).
  -- The self-module `•` resolves only in the `mkDerivation` context, so we do not re-type it.
  change Finsupp.sum m (fun i k => monomial (m - Finsupp.single i 1) (k : R) * φ i) = derivMono φ m
  -- Step 1: Finsupp sum = univ Finset sum (via sum_fintype; the summand vanishes at `k = 0`)
  have hfin : Finsupp.sum m (fun i k => monomial (m - Finsupp.single i 1) (k : R) * φ i) =
      (Finset.univ : Finset σ).sum (fun i => monomial (m - Finsupp.single i 1) ((m i) : R) * φ i) := by
    simpa using Finsupp.sum_fintype m (fun i k => monomial (m - Finsupp.single i 1) (k : R) * φ i)
        (fun i => by simp)
  rw [hfin]
  -- Step 2: `X^{m - e_i} (m_i)` = `(m_i) · X^{m - e_i}` (the `R`-module action, matching
  -- `derivMono`).
  have hmono : ∀ i, monomial (m - Finsupp.single i 1) ((m i) : R) =
      ((m i) : R) • monomial (m - Finsupp.single i 1) 1 := by
    intro i
    rw [MvPolynomial.smul_monomial]
    simp
  have hmono_sum : (Finset.univ : Finset σ).sum (fun i => monomial (m - Finsupp.single i 1) ((m i) : R) * φ i) =
      (Finset.univ : Finset σ).sum (fun i => (((m i) : R) • monomial (m - Finsupp.single i 1) 1) * φ i) := by
    simp [hmono]
  rw [hmono_sum]
  -- Step 3: LHS = `∑ i : σ, (m_i) · X^{m - e_i} · φ_i` = `derivMono φ m`
  dsimp [derivMono]

-- The bridge: `derivationExt φ = MvPolynomial.mkDerivation R φ`.  Both sides send a monomial `X^m`
-- to `derivMono φ m` (the two monomial lemmas above), and `mkDerivation` is `ℚ`-linear, so they
-- agree on the sum of monomials that is `p`.
private theorem derivationExt_eq_mkDerivation {σ : Type*} [Fintype σ] {R : Type*} [CommRing R]
    (φ : σ → MvPolynomial σ R) (p : MvPolynomial σ R) :
    derivationExt φ p = MvPolynomial.mkDerivation R φ p := by
  rw [derivationExt_eq_sum]
  -- `mkDerivation R φ p` is the sum over `p.support` of the coefficient times the monomial
  -- derivative: `p` is the sum of its monomials, `mkDerivation` is `ℚ`-linear (so it commutes
  -- with the sum) and `R`-linear (so it commutes with the scalar), and on a monomial it is
  -- `derivMono`.
  have hsum : MvPolynomial.mkDerivation R φ p = ∑ v ∈ p.support, p.coeff v • derivMono φ v := by
    have hp : p = ∑ v ∈ p.support, p.coeff v • monomial v 1 := by
      simp [MvPolynomial.smul_monomial]
    conv =>
      lhs
      rw [hp]
    have hlin : MvPolynomial.mkDerivation R φ (∑ v ∈ p.support, p.coeff v • monomial v 1) =
        ∑ v ∈ p.support, MvPolynomial.mkDerivation R φ (p.coeff v • monomial v 1) := by
      change (MvPolynomial.mkDerivation R φ).toLinearMap (∑ v ∈ p.support, p.coeff v • monomial v 1) =
          ∑ v ∈ p.support, (MvPolynomial.mkDerivation R φ).toLinearMap (p.coeff v • monomial v 1)
      exact linMap_finset_sum (MvPolynomial.mkDerivation R φ).toLinearMap p.support
          (fun v => p.coeff v • monomial v 1)
    rw [hlin]
    apply Finset.sum_congr rfl
    intro v hv
    rw [(MvPolynomial.mkDerivation R φ).map_smul, mkDerivation_monomial_derivMono]
  -- The LHS (`derivationExt_eq_sum`) and `hsum` are the same sum, up to the bound variable name.
  exact hsum.symm

/-- `derivationExt φ` is `ℚ`-linear: it preserves addition (it is `MvPolynomial.mkDerivation`, a
    `ℚ`-linear map). -/
private theorem derivationExt_add {σ : Type*} [Fintype σ] {R : Type*} [CommRing R]
    (φ : σ → MvPolynomial σ R) (p q : MvPolynomial σ R) :
    derivationExt φ (p + q) = derivationExt φ p + derivationExt φ q := by
  rw [derivationExt_eq_mkDerivation, map_add, derivationExt_eq_mkDerivation,
    derivationExt_eq_mkDerivation]

/-- `derivationExt φ` is `ℚ`-linear: it preserves scalar multiplication. -/
private theorem derivationExt_smul {σ : Type*} [Fintype σ] {R : Type*} [CommRing R]
    (φ : σ → MvPolynomial σ R) (c : R) (p : MvPolynomial σ R) :
    derivationExt φ (c • p) = c • derivationExt φ p := by
  simp [derivationExt_eq_mkDerivation]

/-- The Leibniz rule: `derivationExt φ (p * q) = derivationExt φ p * q + p * derivationExt φ q`
    (it is `MvPolynomial.mkDerivation`, a derivation; the module action of `MvPolynomial` on itself
    is multiplication, and the ring is commutative). -/
private theorem derivationExt_mul {σ : Type*} [Fintype σ] {R : Type*} [CommRing R]
    (φ : σ → MvPolynomial σ R) (p q : MvPolynomial σ R) :
    derivationExt φ (p * q) = derivationExt φ p * q + p * derivationExt φ q := by
  rw [derivationExt_eq_mkDerivation, derivationExt_eq_mkDerivation,
    derivationExt_eq_mkDerivation]
  have := (MvPolynomial.mkDerivation R φ).leibniz p q
  rw [this]
  simp [smul_eq_mul]
  ring

/-! ### The word extension: a `ℚ`-linear map built from derivations -/

/-- `Mword [] = id`. -/
theorem Mword_nil (A : ShuffleAutomaton α) : A.Mword [] = id := by
  rfl

/-- `Mword (a :: w) = Mword w ∘ derivationExt (Δ a)`: reading `a` then `w` applies the letter
    derivation `Δ_a` first, then the word map for `w`. -/
private theorem Mword_cons (A : ShuffleAutomaton α) (a : α) (w : List α) :
    A.Mword (a :: w) = A.Mword w ∘ derivationExt (A.Δ a) := by
  dsimp [ShuffleAutomaton.Mword]
  funext β
  simp

/-- `Mword (u ++ v) = Mword v ∘ Mword u` (the letters of `u` are applied after those of
    `v`, right-to-left). -/
private theorem Mword_append (A : ShuffleAutomaton α) (u v : List α) :
    A.Mword (u ++ v) = A.Mword v ∘ A.Mword u := by
  induction u with
  | nil =>
      funext β
      simp [Mword_nil]
  | cons a u ih =>
      funext β
      simp [Mword_cons, List.cons_append, ih, Function.comp_apply]

/-! ### Semantics properties -/

/-- The word map is `ℚ`-linear: `A.Mword w (p + q) = A.Mword w p + A.Mword w q`.  Each letter
    map `derivationExt (Δ a)` is `ℚ`-linear, and a composition of `ℚ`-linear maps is `ℚ`-linear.
    The induction hypothesis is stated for all `p q` so it can be applied to the derived terms. -/
private theorem Mword_add (A : ShuffleAutomaton α) (w : List α)
    (p q : MvPolynomial (Fin A.dim) ℚ) :
    A.Mword w (p + q) = A.Mword w p + A.Mword w q := by
  have : ∀ (w : List α) (p q : MvPolynomial (Fin A.dim) ℚ),
      A.Mword w (p + q) = A.Mword w p + A.Mword w q := by
    intro w
    induction w with
    | nil =>
        intro p q
        simp [Mword_nil]
    | cons a w' ih =>
        intro p q
        simp [Mword_cons, Function.comp_apply]
        rw [derivationExt_add, ih (derivationExt (A.Δ a) p) (derivationExt (A.Δ a) q)]
  exact this w p q

/-- The word map commutes with scalar multiplication: `A.Mword w (c • p) = c • A.Mword w p`. -/
private theorem Mword_smul (A : ShuffleAutomaton α) (w : List α) (c : ℚ)
    (p : MvPolynomial (Fin A.dim) ℚ) :
    A.Mword w (c • p) = c • A.Mword w p := by
  have : ∀ (w : List α) (c : ℚ) (p : MvPolynomial (Fin A.dim) ℚ),
      A.Mword w (c • p) = c • A.Mword w p := by
    intro w
    induction w with
    | nil =>
        intro c p
        simp [Mword_nil]
    | cons a w' ih =>
        intro c p
        simp [Mword_cons, Function.comp_apply]
        rw [derivationExt_smul, ih c (derivationExt (A.Δ a) p)]
  exact this w c p

/-- The semantics is `ℚ`-linear: `A.sem (p + q) = A.sem p + A.sem q`.  The word map is `ℚ`-linear
    and `eval` is a ring homomorphism. -/
private theorem sem_add (A : ShuffleAutomaton α) (p q : MvPolynomial (Fin A.dim) ℚ) :
    A.sem (p + q) = A.sem p + A.sem q := by
  funext w
  dsimp [ShuffleAutomaton.sem]
  rw [Mword_add A w p q, eval_add]

/-- The semantics commutes with scalar multiplication: `A.sem (c • p) = c • A.sem p`. -/
private theorem sem_smul (A : ShuffleAutomaton α) (c : ℚ) (p : MvPolynomial (Fin A.dim) ℚ) :
    A.sem (c • p) = c • A.sem p := by
  funext w
  dsimp [ShuffleAutomaton.sem]
  rw [Mword_smul A w c p]
  simp

/-- The derivation property: `leftDeriv a (A.sem p) = A.sem (derivationExt (Δ a) p)`.  Reading
    the word `a :: w` applies `Δ_a` first (`Mword_cons`), so the left derivative of the
    semantics at `p` is the semantics at `derivationExt (Δ a) p`. -/
theorem sem_deriv (A : ShuffleAutomaton α) (a : α) (p : MvPolynomial (Fin A.dim) ℚ) :
    leftDeriv α a (A.sem p) = A.sem (derivationExt (A.Δ a) p) := by
  funext w
  dsimp [ShuffleAutomaton.sem, leftDeriv]
  rw [Mword_cons]
  rfl

/-! ### The semantics is a homomorphism for the shuffle product -/

/-- The key homomorphism property (paper §6, Lemma "Properties of the semantics"):
    `sem A (p * q) = shuffle (sem A p) (sem A q)`.  The ring product of the configuration
    space maps to the *shuffle* product of the series.

    The proof is by induction on the word `w`, with the induction hypothesis quantified
    over all `p q` (so it applies to the derived polynomials).  It does NOT use the
    shuffle-product characterisation (whose Leibniz step would be circular); instead it
    reduces both sides to the word-level recursion, using `Mword_cons`, the Leibniz rule
    for `derivationExt`, and `sem_deriv`. -/
private theorem sem_shuffle (A : ShuffleAutomaton α)
    (p q : MvPolynomial (Fin A.dim) ℚ) :
    A.sem (p * q) = shuffle α (A.sem p) (A.sem q) := by
  funext w
  dsimp [ShuffleAutomaton.sem, shuffle]
  have : ∀ (p q : MvPolynomial (Fin A.dim) ℚ),
      eval (fun i => A.F i) (A.Mword w (p * q)) = shuffleRec α (A.sem p) (A.sem q) w := by
    induction w with
    | nil =>
        intro p q
        -- `A.Mword []` is definitionally `id`, and `shuffleRec _ _ []` is the product of the
        -- two series at `[]`; `eval` is a ring homomorphism.
        simp [Mword_nil, shuffleRec_nil, ShuffleAutomaton.sem, eval_mul]
    | cons a w' ih =>
        intro p q
        have hLHS : eval (fun i => A.F i) (A.Mword (a :: w') (p * q)) =
            eval (fun i => A.F i) (A.Mword w' (derivationExt (A.Δ a) p * q)) +
            eval (fun i => A.F i) (A.Mword w' (p * derivationExt (A.Δ a) q)) := by
          rw [Mword_cons, Function.comp_apply, derivationExt_mul, Mword_add, eval_add]
        rw [hLHS]
        have hRHS : shuffleRec α (A.sem p) (A.sem q) (a :: w') =
            shuffleRec α (leftDeriv α a (A.sem p)) (A.sem q) w' +
            shuffleRec α (A.sem p) (leftDeriv α a (A.sem q)) w' := by
          simp [shuffleRec_cons]
        rw [hRHS]
        -- Apply the induction hypothesis to the derived polynomials.
        have hih1 : eval (fun i => A.F i) (A.Mword w' (derivationExt (A.Δ a) p * q)) =
            shuffleRec α (A.sem (derivationExt (A.Δ a) p)) (A.sem q) w' :=
          ih (derivationExt (A.Δ a) p) q
        have hih2 : eval (fun i => A.F i) (A.Mword w' (p * derivationExt (A.Δ a) q)) =
            shuffleRec α (A.sem p) (A.sem (derivationExt (A.Δ a) q)) w' :=
          ih p (derivationExt (A.Δ a) q)
        rw [hih1, hih2]
        -- `sem A (derivationExt (Δ a) p) = leftDeriv a (sem A p)` (via `sem_deriv`).
        have hsem1 : A.sem (derivationExt (A.Δ a) p) = leftDeriv α a (A.sem p) :=
          sem_deriv A a p
        have hsem2 : A.sem (derivationExt (A.Δ a) q) = leftDeriv α a (A.sem q) :=
          sem_deriv A a q
        rw [hsem1, hsem2]
  exact this p q

/-! ### The shuffle-algebra evaluation (the semantic working definition) -/

/-- `shufflePow α f 0 = shuffleUnit α`. -/
private theorem shufflePow_zero (f : Series α) : shufflePow α f 0 = shuffleUnit α := rfl

/-- `shufflePow α f (n+1) = f ⧢ shufflePow α f n`. -/
private theorem shufflePow_succ (f : Series α) (n : ℕ) :
    shufflePow α f (n + 1) = shuffle α f (shufflePow α f n) := rfl

/-- `shufflePow α f (m + n) = shufflePow α f m ⧢ shufflePow α f n`. -/
private theorem shufflePow_add (f : Series α) (m n : ℕ) :
    shufflePow α f (m + n) = shuffle α (shufflePow α f m) (shufflePow α f n) := by
  induction m with
  | zero =>
      rw [Nat.zero_add, shufflePow_zero, shuffle_unit_left]
  | succ m ih =>
      -- LHS: `shufflePow f (succ m + n) = shuffle f (shufflePow f (m + n))` (since
      -- `succ m + n = m + n + 1`); apply `ih` to the inner power, then `shufflePow_succ`
      -- to the RHS, and associativity identifies the two.
      rw [Nat.succ_add, shufflePow_succ, ih, shufflePow_succ]
      simp [shuffle_assoc]

/-- `shufflePow α f 1 = f`. -/
private theorem shufflePow_one (f : Series α) : shufflePow α f 1 = f := by
  rw [shufflePow_succ, shufflePow_zero, shuffle_unit_right]

/-! ### The shuffle-algebra evaluation (the semantic working definition) -/

/-- The shuffle product is a commutative and associative operation on series, hence a
    commutative-associative operation in the sense of `Std`.  These instances let
    `Finset.fold` take the shuffle product of a finite family of series (see
    `shuffleProd` below).  (The shuffle ring cannot be a `CommRing` instance on `Series α`
    itself, because `Series α` already carries the pointwise `CommRing` instance; the
    evaluation is therefore defined directly as a sum over the polynomial's support.) -/
instance : Std.Commutative (shuffle α) := ⟨shuffle_comm⟩
instance : Std.Associative (shuffle α) := ⟨shuffle_assoc⟩

/-- The concept package's `shuffleProd` (a typeclass-free right-fold over the index list)
    equals the `Finset.fold` of the shuffle product over all indices: both compute the
    shuffle product of the iterated powers `fs i ⧢^[d i]`, and the shuffle product is
    commutative and associative, so the result is independent of the order of the factors. -/
theorem shuffleProd_eq_fold (k : ℕ) (fs : Fin k → Series α) (d : Fin k →₀ ℕ) :
    shuffleProd α k fs d =
      (Finset.univ : Finset (Fin k)).fold (shuffle α) (shuffleUnit α) (fun i => shufflePow α (fs i) (d i)) := by
  unfold shuffleProd
  -- The LHS folds with `fun x acc => shuffle α x acc`, eta-equivalent to `shuffle α`
  -- (the latter is the term carrying the `Std.Commutative`/`Std.Associative` instances,
  -- which `Multiset.coe_fold_r` requires).
  change List.foldr (shuffle α) (shuffleUnit α) (List.map (fun i => shufflePow α (fs i) (d i)) Finset.univ.toList) =
      (Finset.univ : Finset (Fin k)).fold (shuffle α) (shuffleUnit α) (fun i => shufflePow α (fs i) (d i))
  -- Both sides fold the shuffle product over the image of `Finset.univ` under
  -- `i ↦ shufflePow (fs i) (d i)`: the LHS is the `List.foldr` over the list representative
  -- (`Multiset.coe_fold_r`), the RHS the `Finset.fold`; the multiset being folded is the
  -- same in both (`Finset.coe_toList`, `Multiset.map_coe`).  The rewrite brings the LHS to a
  -- `Multiset.fold`; unfolding the RHS `Finset.fold` (whose definition is a `Multiset.fold`)
  -- makes the two sides identical, closing the goal.
  rw [← Multiset.coe_fold_r, ← Multiset.map_coe, Finset.coe_toList]
  dsimp only [Finset.fold]

/-- `shuffleProd α k fs 0 = shuffleUnit α`: every iterated power is the shuffle unit (the
    zero power), and shuffling the unit with itself is the unit. -/
private theorem shuffleProd_zero (k : ℕ) (fs : Fin k → Series α) :
    shuffleProd α k fs 0 = shuffleUnit α := by
  have : ∀ (s : Finset (Fin k)),
      s.fold (shuffle α) (shuffleUnit α) (fun _ => shuffleUnit α) = shuffleUnit α := by
    intro s
    apply Finset.induction_on
      (motive := fun s => s.fold (shuffle α) (shuffleUnit α) (fun _ => shuffleUnit α) = shuffleUnit α)
    · simp [Finset.fold_empty]
    · intro a s h ih
      rw [Finset.fold_insert h, ih]
      simp [shuffle_unit_left]
  rw [shuffleProd_eq_fold]
  have hLHS : (Finset.univ : Finset (Fin k)).fold (shuffle α) (shuffleUnit α)
      (fun i => shufflePow α (fs i) ((0 : Fin k →₀ ℕ) i)) =
      (Finset.univ : Finset (Fin k)).fold (shuffle α) (shuffleUnit α) (fun _ => shuffleUnit α) := by
    apply Finset.fold_congr
    intro i _
    simp [Finsupp.zero_apply, shufflePow_zero]
  rw [hLHS]
  exact this Finset.univ

/-- `shuffleProd α k fs (X i) = fs i`, where `X i` is the monomial with a single 1 at index
    `i`: the only non-unit iterated power is `fs i` (the first power), and shuffling with the
    unit is the identity. -/
private theorem shuffleProd_X (k : ℕ) (fs : Fin k → Series α) (i : Fin k) :
    shuffleProd α k fs (Finsupp.single i 1) = fs i := by
  have : ∀ (s : Finset (Fin k)),
      s.fold (shuffle α) (shuffleUnit α) (fun j => shufflePow α (fs j) ((Finsupp.single i 1) j)) =
      if i ∈ s then fs i else shuffleUnit α := by
    intro s
    apply Finset.induction_on
      (motive := fun s => s.fold (shuffle α) (shuffleUnit α)
        (fun j => shufflePow α (fs j) ((Finsupp.single i 1) j)) =
        if i ∈ s then fs i else shuffleUnit α)
    · simp [Finset.fold_empty]
    · intro a s h ih
      rw [Finset.fold_insert h, ih]
      have hfac : shufflePow α (fs a) ((Finsupp.single i 1) a) = if a = i then fs a else shuffleUnit α := by
        by_cases ha : a = i
        · rw [ha]
          simp [Finsupp.single_apply, shufflePow_one]
        · have hne : i ≠ a := by
            intro h; exact ha h.symm
          rw [Finsupp.single_apply]
          simp [ha, hne, shufflePow_zero]
      rw [hfac]
      by_cases ha : a = i
      · have hnot : i ∉ s := by
          intro hi
          exact h (by rwa [ha])
        simp [ha, hnot, Finset.mem_insert_self, shuffle_unit_right]
      · have hne : i ≠ a := by
          intro h; exact ha h.symm
        simp [ha, hne, shuffle_unit_left, Finset.mem_insert]
  rw [shuffleProd_eq_fold]
  simp [this, Finset.mem_univ]

/-- `shuffleProd α k fs (m + n) = shuffleProd α k fs m ⧢ shuffleProd α k fs n`: the
    iterated power of the sum of exponents is the shuffle product of the iterated powers
    (`shufflePow_add`), and the shuffle fold distributes over a product of folds
    (`Finset.fold_op_distrib`). -/
private theorem shuffleProd_add (k : ℕ) (fs : Fin k → Series α) (m n : Fin k →₀ ℕ) :
    shuffleProd α k fs (m + n) = shuffle α (shuffleProd α k fs m) (shuffleProd α k fs n) := by
  rw [shuffleProd_eq_fold, shuffleProd_eq_fold, shuffleProd_eq_fold]
  have hunit : shuffle α (shuffleUnit α) (shuffleUnit α) = shuffleUnit α := by
    simp [shuffle_unit_left]
  have hsplit : ∀ i, shufflePow α (fs i) (m i + n i) =
      shuffle α (shufflePow α (fs i) (m i)) (shufflePow α (fs i) (n i)) := by
    intro i; rw [shufflePow_add]
  have hLHS : (Finset.univ : Finset (Fin k)).fold (shuffle α) (shuffleUnit α)
      (fun i => shufflePow α (fs i) ((m + n) i)) =
      (Finset.univ : Finset (Fin k)).fold (shuffle α) (shuffleUnit α)
      (fun i => shuffle α (shufflePow α (fs i) (m i)) (shufflePow α (fs i) (n i))) := by
    apply Finset.fold_congr
    intro i _
    rw [Finsupp.add_apply, hsplit i]
  -- The shuffle product of a multiset of factors is independent of the grouping
  -- (shuffle is commutative and associative).
  have hkey : ∀ (A B U V : Series α),
      shuffle α (shuffle α A U) (shuffle α B V) = shuffle α (shuffle α A B) (shuffle α U V) := by
    intro A B U V
    -- Regroup the four factors `A U B V` as `A B` and `U V` (shuffle is commutative + associative).
    calc
      shuffle α (shuffle α A U) (shuffle α B V)
          = shuffle α A (shuffle α U (shuffle α B V)) := by rw [shuffle_assoc]
        _ = shuffle α A (shuffle α (shuffle α U B) V) := by
            conv =>
              lhs
              arg 3
              rw [← shuffle_assoc]
        _ = shuffle α A (shuffle α (shuffle α B U) V) := by
            conv =>
              lhs
              arg 3
              arg 2
              rw [shuffle_comm]
        _ = shuffle α A (shuffle α B (shuffle α U V)) := by
            conv =>
              lhs
              arg 3
              rw [shuffle_assoc]
        _ = shuffle α (shuffle α A B) (shuffle α U V) := by rw [← shuffle_assoc]
  -- The shuffle fold of the pointwise product is the shuffle product of the two folds.
  have hdist : ∀ (s : Finset (Fin k)),
      shuffle α (s.fold (shuffle α) (shuffleUnit α) (fun i => shufflePow α (fs i) (m i)))
        (s.fold (shuffle α) (shuffleUnit α) (fun i => shufflePow α (fs i) (n i))) =
      s.fold (shuffle α) (shuffleUnit α)
        (fun i => shuffle α (shufflePow α (fs i) (m i)) (shufflePow α (fs i) (n i))) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        simp [Finset.fold_empty, shuffle_unit_left, shuffle_unit_right]
    | insert a s h ih =>
        rw [Finset.fold_insert h, Finset.fold_insert h, Finset.fold_insert h, ← ih]
        exact hkey _ _ _ _
  rw [hLHS, hdist Finset.univ]

/-! ### `shuffleEval` is a homomorphism for the shuffle algebra -/

-- `shuffleEval` (the shuffle-algebra evaluation) is defined in the concept package
-- (`Lax619925.Shuffle.shuffleEval`); the theorems below are about that definition.

/-- `shuffleEval α k fs 0 = 0`. -/
private theorem shuffleEval_zero (k : ℕ) (fs : Fin k → Series α) :
    shuffleEval α k fs 0 = 0 := by
  simp [shuffleEval, MvPolynomial.support_zero]

/-- `shuffleEval α k fs 1 = shuffleUnit α`. -/
private theorem shuffleEval_one (k : ℕ) (fs : Fin k → Series α) :
    shuffleEval α k fs 1 = shuffleUnit α := by
  simp [shuffleEval, MvPolynomial.support_one, MvPolynomial.coeff_one, one_smul, shuffleProd_zero]

/-- `shuffleEval α k fs (X i) = fs i`. -/
private theorem shuffleEval_X (k : ℕ) (fs : Fin k → Series α) (i : Fin k) :
    shuffleEval α k fs (MvPolynomial.X i) = fs i := by
  simp [shuffleEval, MvPolynomial.support_X, MvPolynomial.coeff_X, one_smul, shuffleProd_X]

/-- `shuffleEval` is additive: `shuffleEval α k fs (p + q) = shuffleEval α k fs p +
    shuffleEval α k fs q`.  The support of the sum is contained in the union of the
    supports, and the coefficient of the sum is the sum of the coefficients; the sum over
    the union splits into the two sums (the terms outside each support vanish). -/
private theorem shuffleEval_add (k : ℕ) (fs : Fin k → Series α)
    (p q : MvPolynomial (Fin k) ℚ) :
    shuffleEval α k fs (p + q) = shuffleEval α k fs p + shuffleEval α k fs q := by
  rw [shuffleEval, shuffleEval, shuffleEval]
  have hsup : (p + q).support ⊆ p.support ∪ q.support := MvPolynomial.support_add
  have hcoeff : ∀ m, (p + q).coeff m = p.coeff m + q.coeff m := by
    intro m; rw [MvPolynomial.coeff_add]
  have hext1 : (p + q).support.sum (fun m => (p + q).coeff m • shuffleProd α k fs m) =
      (p.support ∪ q.support).sum (fun m => (p + q).coeff m • shuffleProd α k fs m) := by
    have h' : ∀ x ∈ p.support ∪ q.support, x ∉ (p + q).support →
        (p + q).coeff x • shuffleProd α k fs x = 0 := by
      intro x _ hx
      have hcoeff0 : (p + q).coeff x = 0 := by
        simpa using (MvPolynomial.notMem_support_iff (p := p + q) (m := x)).mp hx
      simp [hcoeff0, zero_smul]
    exact Finset.sum_subset hsup h'
  have hext2 : (p.support ∪ q.support).sum (fun m => p.coeff m • shuffleProd α k fs m) =
      p.support.sum (fun m => p.coeff m • shuffleProd α k fs m) := by
    have h' : ∀ x ∈ p.support ∪ q.support, x ∉ p.support →
        p.coeff x • shuffleProd α k fs x = 0 := by
      intro x _ hx
      have hcoeff0 : p.coeff x = 0 := by
        simpa using (MvPolynomial.notMem_support_iff (p := p) (m := x)).mp hx
      simp [hcoeff0, zero_smul]
    exact (Finset.sum_subset Finset.subset_union_left h').symm
  have hext3 : (p.support ∪ q.support).sum (fun m => q.coeff m • shuffleProd α k fs m) =
      q.support.sum (fun m => q.coeff m • shuffleProd α k fs m) := by
    have h' : ∀ x ∈ p.support ∪ q.support, x ∉ q.support →
        q.coeff x • shuffleProd α k fs x = 0 := by
      intro x _ hx
      have hcoeff0 : q.coeff x = 0 := by
        simpa using (MvPolynomial.notMem_support_iff (p := q) (m := x)).mp hx
      simp [hcoeff0, zero_smul]
    exact (Finset.sum_subset Finset.subset_union_right h').symm
  calc
    (p + q).support.sum (fun m => (p + q).coeff m • shuffleProd α k fs m)
        = (p.support ∪ q.support).sum (fun m => (p + q).coeff m • shuffleProd α k fs m) := hext1
    _ = (p.support ∪ q.support).sum (fun m => (p.coeff m + q.coeff m) • shuffleProd α k fs m) := by
      simp [hcoeff]
    _ = (p.support ∪ q.support).sum (fun m => p.coeff m • shuffleProd α k fs m +
          q.coeff m • shuffleProd α k fs m) := by
      simp [add_smul]
    _ = (p.support ∪ q.support).sum (fun m => p.coeff m • shuffleProd α k fs m) +
        (p.support ∪ q.support).sum (fun m => q.coeff m • shuffleProd α k fs m) := by
      rw [Finset.sum_add_distrib]
    _ = p.support.sum (fun m => p.coeff m • shuffleProd α k fs m) +
        q.support.sum (fun m => q.coeff m • shuffleProd α k fs m) := by
      rw [hext2, hext3]

/-- `shuffleEval` commutes with scalar multiplication: `shuffleEval α k fs (c • p) =
    c • shuffleEval α k fs p`.  The coefficient of the scalar multiple is the scalar
    multiple of the coefficient, and the support is contained in the original support. -/
private theorem shuffleEval_smul (k : ℕ) (fs : Fin k → Series α) (c : ℚ)
    (p : MvPolynomial (Fin k) ℚ) :
    shuffleEval α k fs (c • p) = c • shuffleEval α k fs p := by
  rw [shuffleEval, shuffleEval]
  have hsup : (c • p).support ⊆ p.support := MvPolynomial.support_smul
  have hcoeff : ∀ m, (c • p).coeff m = c • p.coeff m := by
    intro m; rw [MvPolynomial.coeff_smul]
  have hext : (c • p).support.sum (fun m => (c • p).coeff m • shuffleProd α k fs m) =
      p.support.sum (fun m => (c • p).coeff m • shuffleProd α k fs m) := by
    have h' : ∀ x ∈ p.support, x ∉ (c • p).support →
        (c • p).coeff x • shuffleProd α k fs x = 0 := by
      intro x _ hx
      have hcoeff0 : (c • p).coeff x = 0 := by
        simpa using (MvPolynomial.notMem_support_iff (p := c • p) (m := x)).mp hx
      simp [hcoeff0, zero_smul]
    exact Finset.sum_subset hsup h'
  calc
    (c • p).support.sum (fun m => (c • p).coeff m • shuffleProd α k fs m)
        = p.support.sum (fun m => (c • p).coeff m • shuffleProd α k fs m) := hext
    _ = p.support.sum (fun m => c • (p.coeff m • shuffleProd α k fs m)) := by
      simp [hcoeff, mul_smul]
    _ = c • p.support.sum (fun m => p.coeff m • shuffleProd α k fs m) := by
      rw [← Finset.smul_sum]

/-- `shuffleEval` is multiplicative for the shuffle product:
    `shuffleEval α k fs (p * q) = shuffle α (shuffleEval α k fs p) (shuffleEval α k fs q)`.
    Both sides equal the double sum `∑ n ∈ p.support, ∑ o ∈ q.support,
    (p.coeff n * q.coeff o) • shuffleProd α k fs (n + o)`: the RHS because the shuffle is
    `ℚ`-bilinear and `shuffleProd (n + o) = shuffleProd n ⧢ shuffleProd o` (`shuffleProd_add`),
    and the LHS because `shuffleEval` is `ℚ`-linear, `p * q` decomposes into its monomials
    (`monomial_mul`), and `shuffleEval (monomial m a) = a • shuffleProd m`. -/
private theorem shuffleEval_mul (k : ℕ) (fs : Fin k → Series α)
    (p q : MvPolynomial (Fin k) ℚ) :
    shuffleEval α k fs (p * q) = shuffle α (shuffleEval α k fs p) (shuffleEval α k fs q) := by
  -- The shuffle is additive in each argument over a finite sum.
  have haddL : ∀ (s : Finset (Fin k →₀ ℕ)) (f : (Fin k →₀ ℕ) → Series α) (g : Series α),
      shuffle α (s.sum f) g = s.sum (fun x => shuffle α (f x) g) := by
    intro s f g
    induction s using Finset.induction_on with
    | empty => simp [Finset.sum_empty, shuffle_zero_left]
    | insert a s h ih =>
        rw [Finset.sum_insert h, shuffle_add_left, ih, Finset.sum_insert h]
  have haddR : ∀ (f : Series α) (s : Finset (Fin k →₀ ℕ)) (g : (Fin k →₀ ℕ) → Series α),
      shuffle α f (s.sum g) = s.sum (fun x => shuffle α f (g x)) := by
    intro f s g
    induction s using Finset.induction_on with
    | empty => simp [Finset.sum_empty, shuffle_zero_right]
    | insert a s h ih =>
        rw [Finset.sum_insert h, shuffle_add_right, ih, Finset.sum_insert h]
  -- `shuffleEval` is additive over a finite sum (over the product index type used below).
  have hsum : ∀ (s : Finset ((Fin k →₀ ℕ) × (Fin k →₀ ℕ)))
      (f : ((Fin k →₀ ℕ) × (Fin k →₀ ℕ)) → MvPolynomial (Fin k) ℚ),
      shuffleEval α k fs (s.sum f) = s.sum (fun x => shuffleEval α k fs (f x)) := by
    intro s f
    induction s using Finset.induction_on with
    | empty => simp [shuffleEval, MvPolynomial.support_zero]
    | insert a s h ih =>
        rw [Finset.sum_insert h, shuffleEval_add, ih, Finset.sum_insert h]
  -- `shuffleEval` of a monomial is the scalar times the shuffle product.
  have hmono : ∀ (m : Fin k →₀ ℕ) (a : ℚ),
      shuffleEval α k fs (MvPolynomial.monomial m a) = a • shuffleProd α k fs m := by
    intro m a
    by_cases ha : a = 0
    · simp [ha, MvPolynomial.monomial_zero, shuffleEval_zero, zero_smul]
    · simp [shuffleEval, ha, MvPolynomial.support_monomial, MvPolynomial.coeff_monomial,
        Finset.sum_singleton]
  -- The RHS is the double sum (shuffle is ℚ-bilinear, shuffleProd_add).
  have hRHS : shuffle α (shuffleEval α k fs p) (shuffleEval α k fs q) =
      ∑ n ∈ p.support, ∑ o ∈ q.support, (p.coeff n * q.coeff o) • shuffleProd α k fs (n + o) := by
    rw [shuffleEval, shuffleEval]
    calc
      shuffle α (p.support.sum (fun n => p.coeff n • shuffleProd α k fs n))
          (q.support.sum (fun o => q.coeff o • shuffleProd α k fs o))
          = ∑ n ∈ p.support, shuffle α (p.coeff n • shuffleProd α k fs n)
              (q.support.sum (fun o => q.coeff o • shuffleProd α k fs o)) := by
        rw [haddL (s := p.support) (f := fun n => p.coeff n • shuffleProd α k fs n)
          (g := q.support.sum (fun o => q.coeff o • shuffleProd α k fs o))]
      _ = ∑ n ∈ p.support, ∑ o ∈ q.support,
          shuffle α (p.coeff n • shuffleProd α k fs n) (q.coeff o • shuffleProd α k fs o) := by
        apply Finset.sum_congr rfl
        intro n _
        exact haddR (f := p.coeff n • shuffleProd α k fs n) (s := q.support)
          (g := fun o => q.coeff o • shuffleProd α k fs o)
      _ = ∑ n ∈ p.support, ∑ o ∈ q.support,
          (p.coeff n * q.coeff o) • shuffleProd α k fs (n + o) := by
        apply Finset.sum_congr rfl
        intro n _
        apply Finset.sum_congr rfl
        intro o _
        rw [shuffle_smul_left, shuffle_smul_right, smul_smul, shuffleProd_add]
  -- The LHS is the same double sum (shuffleEval is ℚ-linear, p * q decomposes into monomials,
  -- shuffleEval (monomial m a) = a • shuffleProd m).
  have hLHS : shuffleEval α k fs (p * q) =
      ∑ n ∈ p.support, ∑ o ∈ q.support, (p.coeff n * q.coeff o) • shuffleProd α k fs (n + o) := by
    have hdecomp : p * q = ∑ w ∈ p.support ×ˢ q.support,
        MvPolynomial.monomial (w.1 + w.2) (p.coeff w.1 * q.coeff w.2) := by
      calc
        p * q = (∑ n ∈ p.support, MvPolynomial.monomial n (p.coeff n)) *
            (∑ o ∈ q.support, MvPolynomial.monomial o (q.coeff o)) := by
          conv_lhs =>
            rw [MvPolynomial.as_sum p, MvPolynomial.as_sum q]
        _ = ∑ n ∈ p.support, ∑ o ∈ q.support,
            MvPolynomial.monomial n (p.coeff n) * MvPolynomial.monomial o (q.coeff o) := by
          rw [Finset.sum_mul_sum]
        _ = ∑ n ∈ p.support, ∑ o ∈ q.support,
            MvPolynomial.monomial (n + o) (p.coeff n * q.coeff o) := by
          simp [MvPolynomial.monomial_mul]
        _ = ∑ w ∈ p.support ×ˢ q.support,
            MvPolynomial.monomial (w.1 + w.2) (p.coeff w.1 * q.coeff w.2) := by
          simp [Finset.sum_product]
    calc
      shuffleEval α k fs (p * q)
          = shuffleEval α k fs (∑ w ∈ p.support ×ˢ q.support,
              MvPolynomial.monomial (w.1 + w.2) (p.coeff w.1 * q.coeff w.2)) := by rw [hdecomp]
        _ = ∑ w ∈ p.support ×ˢ q.support,
            shuffleEval α k fs (MvPolynomial.monomial (w.1 + w.2) (p.coeff w.1 * q.coeff w.2)) := by
          rw [hsum (s := p.support ×ˢ q.support)
            (f := fun (w : (Fin k →₀ ℕ) × (Fin k →₀ ℕ)) =>
              MvPolynomial.monomial (w.1 + w.2) (p.coeff w.1 * q.coeff w.2))]
        _ = ∑ w ∈ p.support ×ˢ q.support,
            (p.coeff w.1 * q.coeff w.2) • shuffleProd α k fs (w.1 + w.2) := by
          simp [hmono]
        _ = ∑ n ∈ p.support, ∑ o ∈ q.support,
            (p.coeff n * q.coeff o) • shuffleProd α k fs (n + o) := by
          simp [Finset.sum_product]
  rw [hLHS, hRHS]

-- `IsShuffleFinite` (the semantic working definition, paper §6) and
-- `IsShuffleRecognisable` (recognised by a shuffle automaton) are both defined in the
-- concept package (`Lax619925.Shuffle`); the coincidence `ShuffleCoincidence` (below)
-- proves they coincide.

/-! ### The coincidence: shuffle-finite ↔ shuffle-recognisable -/

/-- The derivation of the constant `1` is `0`: `derivationExt φ 1 = 0` (it is
    `MvPolynomial.mkDerivation`, whose `map_one_eq_zero` gives this). -/
private theorem derivationExt_one {σ : Type*} [Fintype σ] {R : Type*} [CommRing R]
    (φ : σ → MvPolynomial σ R) : derivationExt φ 1 = 0 := by
  rw [derivationExt_eq_mkDerivation]
  exact (MvPolynomial.mkDerivation R φ).map_one_eq_zero

/-- The derivation sends the variable `X i` to `φ i`: `derivationExt φ (X i) = φ i`
    (it is `MvPolynomial.mkDerivation`, whose `mkDerivation_X` gives this). -/
theorem derivationExt_X {σ : Type*} [Fintype σ] {R : Type*} [CommRing R]
    (φ : σ → MvPolynomial σ R) (i : σ) : derivationExt φ (MvPolynomial.X i) = φ i := by
  rw [derivationExt_eq_mkDerivation, MvPolynomial.mkDerivation_X]

/-- The semantics of the zero configuration is the zero series: `A.sem 0 = 0` (the word map
    sends `0` to `0`, and `eval` of `0` is `0`). -/
private theorem sem_zero (A : ShuffleAutomaton α) : A.sem 0 = 0 := by
  funext w
  dsimp [ShuffleAutomaton.sem]
  have : A.Mword w 0 = 0 := by
    simpa using Mword_smul A w 0 0
  rw [this]
  simp

/-- The word map sends `1` to `1` at the empty word and `0` otherwise: a derivation kills
    `1`, so a non-empty word sends `1` to `0`. -/
private theorem Mword_one (A : ShuffleAutomaton α) (w : List α) :
    A.Mword w 1 = if w = [] then 1 else 0 := by
  induction w with
  | nil => simp [Mword_nil]
  | cons a w' ih =>
      rw [Mword_cons, Function.comp_apply, derivationExt_one]
      have : A.Mword w' 0 = 0 := by
        simpa using Mword_smul A w' 0 0
      rw [this]
      simp

/-- The semantics of the constant `1` configuration is the shuffle unit: `A.sem 1 =
    shuffleUnit α` (the word map sends `1` to `1` at the empty word and `0` otherwise, and
    `eval` of `1` is `1`). -/
private theorem sem_one (A : ShuffleAutomaton α) : A.sem 1 = shuffleUnit α := by
  funext w
  dsimp [ShuffleAutomaton.sem, shuffleUnit]
  rw [Mword_one]
  split_ifs with h
  · simp
  · simp

/-- The semantics of a variable power is the iterated shuffle power of the generator:
    `A.sem (X i ^ n) = (A.sem (X i)) ⧢^[n]` (by the shuffle-hom property `sem_shuffle` and
    induction on `n`; the commutativity of the shuffle product reorders the factors). -/
private theorem sem_pow (A : ShuffleAutomaton α) (i : Fin A.dim) (n : ℕ) :
    A.sem ((MvPolynomial.X i) ^ n) = shufflePow α (A.sem (MvPolynomial.X i)) n := by
  induction n with
  | zero =>
      rw [pow_zero, sem_one, shufflePow_zero]
  | succ n ih =>
      rw [pow_succ, sem_shuffle, ih, shufflePow_succ, shuffle_comm]

/-! The semantics agrees with the shuffle-algebra evaluation: `A.sem p =
    shuffleEval α A.dim (fun i => A.sem (X i)) p` for all `p`.  Both sides are
    shuffle-algebra homomorphisms sending `X_i` to `A.sem (X_i)`, so they coincide. -/

/-- The shuffle product of a finite product of variable powers is the shuffle fold of the
    iterated powers: `A.sem (∏_{i ∈ s} X_i ^ (m i)) = s.fold (⧢) (shuffleUnit) (fun i =>
    (A.sem (X i)) ⧢^[m i])`, by induction on `s` using `sem_shuffle` and `sem_pow`. -/
private theorem sem_prod (A : ShuffleAutomaton α) (m : Fin A.dim →₀ ℕ) (s : Finset (Fin A.dim)) :
    A.sem (s.prod (fun i => (MvPolynomial.X i) ^ m i)) =
      s.fold (shuffle α) (shuffleUnit α) (fun i => shufflePow α (A.sem (MvPolynomial.X i)) (m i)) := by
  induction s using Finset.induction_on with
  | empty =>
      rw [Finset.prod_empty, sem_one]
      simp [Finset.fold_empty, shuffleUnit]
  | insert a s h ih =>
      rw [Finset.prod_insert h, sem_shuffle, ih, Finset.fold_insert h, sem_pow A a (m a)]

/-- `shuffleProd` is unchanged when the fold is taken over the support of the exponent
    `m` rather than over all indices: the zero-exponent terms contribute the shuffle unit
    (the identity), so `shuffleProd α k fs m = (m.support).fold (⧢) (shuffleUnit) (fun i =>
    fs i ⧢^[m i])`. -/
private theorem shuffleProd_support (k : ℕ) (fs : Fin k → Series α) (m : Fin k →₀ ℕ) :
    shuffleProd α k fs m =
      (m.support).fold (shuffle α) (shuffleUnit α) (fun i => shufflePow α (fs i) (m i)) := by
  rw [shuffleProd_eq_fold]
  -- The fold over all indices equals the fold over the support: the zero-exponent terms
  -- contribute the shuffle unit (the identity), which disappears under the fold.
  have hfold : ∀ (s : Finset (Fin k)),
      s.fold (shuffle α) (shuffleUnit α) (fun i => shufflePow α (fs i) (m i)) =
        (m.support ∩ s).fold (shuffle α) (shuffleUnit α) (fun i => shufflePow α (fs i) (m i)) := by
    intro s
    apply Finset.induction_on
      (motive := fun s => s.fold (shuffle α) (shuffleUnit α) (fun i => shufflePow α (fs i) (m i)) =
        (m.support ∩ s).fold (shuffle α) (shuffleUnit α) (fun i => shufflePow α (fs i) (m i)))
    · simp [Finset.fold_empty, Finset.inter_empty]
    · intro a s h ih
      rw [Finset.fold_insert h, ih]
      by_cases ha : a ∈ m.support
      · have hnot : a ∉ m.support ∩ s := by
          intro h'
          exact h (Finset.mem_inter.mp h' |>.2)
        rw [Finset.inter_insert_of_mem ha, Finset.fold_insert hnot]
      · have hne : ¬(m a ≠ 0) := by
          intro h
          exact ha (Finsupp.mem_support_iff.mpr h)
        have hm0 : m a = 0 := by simpa using hne
        rw [Finset.inter_insert_of_notMem ha, hm0, shufflePow_zero]
        simp [shuffle_unit_left]
  rw [hfold Finset.univ]
  simp [Finset.inter_univ]

/-- The semantics of a monomial is the shuffle product of the iterated powers of the
    generators: `A.sem (monomial m 1) = shuffleProd α A.dim (fun i => A.sem (X i)) m`. -/
private theorem sem_monomial (A : ShuffleAutomaton α) (m : Fin A.dim →₀ ℕ) :
    A.sem (MvPolynomial.monomial m 1) =
      shuffleProd α A.dim (fun i => A.sem (MvPolynomial.X i)) m := by
  have hmono : MvPolynomial.monomial m (1 : ℚ) = (m.support).prod (fun i => (MvPolynomial.X i) ^ m i) := by
    rw [MvPolynomial.prod_X_pow_eq_monomial]
  -- `A.sem` returns a series (a function), so `A.sem (monomial m 1)` normalises to a
  -- lambda and `rw [hmono]` cannot find `monomial m 1` as a subterm.  Rewrite the whole
  -- LHS via `congrArg` instead (both sides normalise identically, so `rw` matches).
  have hstep : A.sem (MvPolynomial.monomial m 1) =
      A.sem ((m.support).prod (fun i => (MvPolynomial.X i) ^ m i)) :=
    congrArg (fun x => A.sem x) hmono
  rw [hstep, sem_prod A m m.support]
  exact (shuffleProd_support A.dim (fun i => A.sem (MvPolynomial.X i)) m).symm

/-- `shuffleEval` of a monomial is the scalar times the shuffle product:
    `shuffleEval α k fs (monomial m c) = c • shuffleProd α k fs m`. -/
private theorem shuffleEval_monomial (k : ℕ) (fs : Fin k → Series α) (m : Fin k →₀ ℕ) (c : ℚ) :
    shuffleEval α k fs (MvPolynomial.monomial m c) = c • shuffleProd α k fs m := by
  by_cases hc : c = 0
  · simp [hc, MvPolynomial.monomial_zero, shuffleEval_zero, zero_smul]
  · rw [shuffleEval]
    have hsup : (MvPolynomial.monomial m c).support = {m} := by
      rw [MvPolynomial.support_monomial]
      simp [hc]
    rw [hsup, Finset.sum_singleton]
    have hcoeff : (MvPolynomial.monomial m c).coeff m = c := by
      rw [MvPolynomial.coeff_monomial]
      simp [hc]
    rw [hcoeff]

/-- The semantics agrees with the shuffle-algebra evaluation: `A.sem p =
    shuffleEval α A.dim (fun i => A.sem (X i)) p`.  Both sides are shuffle-algebra
    homomorphisms sending `X_i` to `A.sem (X_i)`; they agree on monomials (`sem_monomial`
    and `shuffleEval_monomial`) and are `ℚ`-linear, so they agree on the sum of monomials
    that is `p`. -/
theorem sem_eq_shuffleEval (A : ShuffleAutomaton α) (p : MvPolynomial (Fin A.dim) ℚ) :
    A.sem p = shuffleEval α A.dim (fun i => A.sem (MvPolynomial.X i)) p := by
  let fs := fun i => A.sem (MvPolynomial.X i)
  have hsum : ∀ (s : Finset (Fin A.dim →₀ ℕ)) (f : (Fin A.dim →₀ ℕ) → MvPolynomial (Fin A.dim) ℚ),
      A.sem (s.sum f) = s.sum (fun x => A.sem (f x)) := by
    intro s f
    induction s using Finset.induction_on with
    | empty => simp [Finset.sum_empty, sem_zero]
    | insert a s h ih =>
        rw [Finset.sum_insert h, sem_add, ih, Finset.sum_insert h]
  have hdecomp : p = ∑ v ∈ p.support, p.coeff v • MvPolynomial.monomial v 1 := by
    simp [MvPolynomial.smul_monomial]
  calc
    A.sem p = A.sem (∑ v ∈ p.support, p.coeff v • MvPolynomial.monomial v 1) := by conv_lhs => rw [hdecomp]
    _ = ∑ v ∈ p.support, A.sem (p.coeff v • MvPolynomial.monomial v 1) := by
      rw [hsum (s := p.support) (f := fun v => p.coeff v • MvPolynomial.monomial v 1)]
    _ = ∑ v ∈ p.support, p.coeff v • A.sem (MvPolynomial.monomial v 1) := by
      apply Finset.sum_congr rfl
      intro v _
      rw [sem_smul]
    _ = ∑ v ∈ p.support, p.coeff v • shuffleProd α A.dim fs v := by
      apply Finset.sum_congr rfl
      intro v _
      rw [sem_monomial]
    _ = shuffleEval α A.dim fs p := by
      dsimp [shuffleEval]

/-! ### Extending the witnessing tuple -/

/-- The witnessing tuple extended by `f` at index `0`: `extTuple f k fs 0 = f` and
    `extTuple f k fs (Fin.succ i) = fs i`.  This lets a shuffle polynomial in `fs` be
    viewed as a shuffle polynomial in the extended tuple, with `f` as a generator. -/
noncomputable def extTuple (f : Series α) (k : ℕ) (fs : Fin k → Series α) : Fin (k+1) → Series α :=
  fun j => if h : j = 0 then f else fs ⟨j.val - 1, by
    have hlt : j.val < k + 1 := j.isLt
    have hne : j.val ≠ 0 := by
      intro hj
      exact h (Fin.ext hj)
    omega⟩

private theorem extTuple_zero (f : Series α) (k : ℕ) (fs : Fin k → Series α) :
    extTuple f k fs 0 = f := by
  simp [extTuple]

private theorem extTuple_succ (f : Series α) (k : ℕ) (fs : Fin k → Series α) (i : Fin k) :
    extTuple f k fs (Fin.succ i) = fs i := by
  simp [extTuple]

/-- The embedding of a polynomial in `Fin k` into `Fin (k+1)`, shifting each variable
    `X_i` to `X_{i+1}` (leaving `X_0` unused): `embedPoly k p = aeval (X ∘ Fin.succ) p`. -/
noncomputable def embedPoly (k : ℕ) (p : MvPolynomial (Fin k) ℚ) : MvPolynomial (Fin (k+1)) ℚ :=
  aeval (fun i => MvPolynomial.X (Fin.succ i)) p

/-! ### Two shuffle-algebra homomorphisms agreeing on the generators are equal -/

/-- Two `ℚ`-algebra homomorphisms (for the *shuffle* product) `h1 h2 :
    MvPolynomial (Fin k) ℚ → Series α` that agree on the unit `1` and on the generators
    `X i` are equal.  The polynomial ring is generated (as a ring) by `1` and the `X i`,
    and a shuffle-algebra hom is determined by those values: it commutes with the powers
    `X i ^ n` (induction on `n`, using multiplicativity), with the monomials
    `monomial m 1` (induction on the support, peeling off one generator at a time), and
    with all polynomials (additivity + scalar-linearity + the monomial case). -/
private theorem shuffleHom_ext (k : ℕ)
    (h1 h2 : MvPolynomial (Fin k) ℚ → Series α)
    (hadd1 : ∀ p q, h1 (p + q) = h1 p + h1 q)
    (hadd2 : ∀ p q, h2 (p + q) = h2 p + h2 q)
    (hsmul1 : ∀ (c : ℚ) p, h1 (c • p) = c • h1 p)
    (hsmul2 : ∀ (c : ℚ) p, h2 (c • p) = c • h2 p)
    (hmul1 : ∀ p q, h1 (p * q) = shuffle α (h1 p) (h1 q))
    (hmul2 : ∀ p q, h2 (p * q) = shuffle α (h2 p) (h2 q))
    (hone : h1 1 = h2 1)
    (hgen : ∀ i, h1 (MvPolynomial.X i) = h2 (MvPolynomial.X i)) :
    ∀ p, h1 p = h2 p := by
  -- The powers: `h1 (X i ^ n) = h2 (X i ^ n)` for all `n`.
  have hpow : ∀ (i : Fin k) (n : ℕ), h1 ((MvPolynomial.X i) ^ n) = h2 ((MvPolynomial.X i) ^ n) := by
    intro i n
    induction n with
    | zero =>
        rw [pow_zero, hone]
    | succ n ih =>
        rw [pow_succ, hmul1, ih, hmul2, hgen i]
  -- The monomials: `h1 (monomial m 1) = h2 (monomial m 1)` for all `m`, by induction on the
  -- support (peeling off one generator at a time).
  have hmono : ∀ (m : Fin k →₀ ℕ),
      h1 (MvPolynomial.monomial m (1 : ℚ)) = h2 (MvPolynomial.monomial m (1 : ℚ)) := by
    have : ∀ (s : Finset (Fin k)) (m : Fin k →₀ ℕ), m.support ⊆ s →
        h1 (MvPolynomial.monomial m (1 : ℚ)) = h2 (MvPolynomial.monomial m (1 : ℚ)) := by
      intro s
      induction s using Finset.induction_on with
      | empty =>
          intro m hm
          have hm0 : m = 0 := by
            rw [Finsupp.ext_iff]
            intro j
            by_contra hj
            have : j ∈ m.support := Finsupp.mem_support_iff.mpr hj
            exact Finset.notMem_empty j (Finset.mem_of_subset hm this)
          rw [hm0, ← MvPolynomial.one_def, hone]
      | insert i s h ih =>
          intro m hm
          by_cases him : i ∈ m.support
          · -- `i ∈ m.support`: peel off `X i ^ (m i)`
            have hmi : m i ≠ 0 := Finsupp.mem_support_iff.mp him
            have hsplit : MvPolynomial.monomial m (1 : ℚ) =
                (MvPolynomial.X i) ^ m i * MvPolynomial.monomial (m - Finsupp.single i (m i)) (1 : ℚ) := by
              have hx : (MvPolynomial.X i) ^ m i =
                  MvPolynomial.monomial (Finsupp.single i (m i)) (1 : ℚ) :=
                MvPolynomial.X_pow_eq_monomial
              rw [hx, MvPolynomial.monomial_mul]
              have hsum : Finsupp.single i (m i) + (m - Finsupp.single i (m i)) = m := by
                rw [Finsupp.ext_iff]
                intro j
                by_cases hj : j = i
                · subst hj
                  simp [Finsupp.tsub_apply, Finsupp.single_apply]
                · simp [hj, Finsupp.single_apply, Finsupp.tsub_apply]
              simp [hsum]
            have hsub : (m - Finsupp.single i (m i)).support ⊆ s := by
              intro j hjj
              have hjne : j ≠ i := by
                intro hj
                have : (m - Finsupp.single i (m i)) j = 0 := by
                  subst hj
                  simp [Finsupp.tsub_apply, Finsupp.single_apply]
                exact (Finsupp.mem_support_iff.mp hjj) this
              have hjm : j ∈ m.support := by
                rw [Finsupp.mem_support_iff]
                have hsubj : (m - Finsupp.single i (m i)) j = m j := by
                  rw [Finsupp.tsub_apply]
                  simp [hjne, Finsupp.single_apply]
                rw [← hsubj]
                exact Finsupp.mem_support_iff.mp hjj
              have hjin : j ∈ insert i s := Finset.mem_of_subset hm hjm
              have hjin' : j ∈ s := by
                rw [Finset.mem_insert] at hjin
                exact hjin.resolve_left hjne
              exact hjin'
            rw [hsplit, hmul1, hmul2, hpow i (m i), ih _ hsub]
          · -- `i ∉ m.support`: then `m.support ⊆ s`, so the induction hypothesis applies directly.
            have hsup : m.support ⊆ s := by
              intro j hjj
              have hjne : j ≠ i := by
                intro hj
                have : j ∉ m.support := by
                  subst hj
                  simpa [Finsupp.mem_support_iff] using him
                exact this hjj
              have hjin : j ∈ insert i s := Finset.mem_of_subset hm hjj
              have hjin' : j ∈ s := by
                rw [Finset.mem_insert] at hjin
                exact hjin.resolve_left hjne
              exact hjin'
            exact ih m hsup
    intro m
    exact this Finset.univ m (Finset.subset_univ m.support)
  -- All polynomials: decompose into monomials, use additivity + scalar-linearity + `hmono`.
  intro p
  have hsum : ∀ (s : Finset (Fin k →₀ ℕ)) (f : (Fin k →₀ ℕ) → MvPolynomial (Fin k) ℚ),
      h1 (s.sum f) = s.sum (fun x => h1 (f x)) := by
    intro s f
    induction s using Finset.induction_on with
    | empty => simp [Finset.sum_empty, show h1 0 = 0 from by simpa using hsmul1 0 0]
    | insert a s h ih =>
        rw [Finset.sum_insert h, hadd1, ih, Finset.sum_insert h]
  have hsum2 : ∀ (s : Finset (Fin k →₀ ℕ)) (f : (Fin k →₀ ℕ) → MvPolynomial (Fin k) ℚ),
      h2 (s.sum f) = s.sum (fun x => h2 (f x)) := by
    intro s f
    induction s using Finset.induction_on with
    | empty => simp [Finset.sum_empty, show h2 0 = 0 from by simpa using hsmul2 0 0]
    | insert a s h ih =>
        rw [Finset.sum_insert h, hadd2, ih, Finset.sum_insert h]
  have hdecomp : p = ∑ v ∈ p.support, p.coeff v • MvPolynomial.monomial v (1 : ℚ) := by
    simp [MvPolynomial.smul_monomial]
  calc
    h1 p = h1 (∑ v ∈ p.support, p.coeff v • MvPolynomial.monomial v (1 : ℚ)) := by
      conv_lhs => rw [hdecomp]
    _ = ∑ v ∈ p.support, h1 (p.coeff v • MvPolynomial.monomial v (1 : ℚ)) := by
      rw [hsum (s := p.support) (f := fun v => p.coeff v • MvPolynomial.monomial v (1 : ℚ))]
    _ = ∑ v ∈ p.support, p.coeff v • h1 (MvPolynomial.monomial v (1 : ℚ)) := by
      apply Finset.sum_congr rfl
      intro v _
      rw [hsmul1]
    _ = ∑ v ∈ p.support, p.coeff v • h2 (MvPolynomial.monomial v (1 : ℚ)) := by
      apply Finset.sum_congr rfl
      intro v _
      rw [hmono v]
    _ = ∑ v ∈ p.support, h2 (p.coeff v • MvPolynomial.monomial v (1 : ℚ)) := by
      apply Finset.sum_congr rfl
      intro v _
      rw [hsmul2]
    _ = h2 (∑ v ∈ p.support, p.coeff v • MvPolynomial.monomial v (1 : ℚ)) := by
      rw [hsum2 (s := p.support) (f := fun v => p.coeff v • MvPolynomial.monomial v (1 : ℚ))]
    _ = h2 p := by
      conv_rhs => rw [hdecomp]

/-- A shuffle polynomial in `fs` is the same series as the embedded shuffle polynomial
    in the extended tuple: `shuffleEval α k fs r = shuffleEval α (k+1) (extTuple f k fs)
    (embedPoly k r)`.  Both sides are shuffle-algebra homomorphisms sending `X_i` to
    `fs i` (the `X_0` slot of the extended tuple is unused by the embedded polynomial, so
    the value of `f` there is irrelevant), so they coincide by `shuffleHom_ext`. -/
private theorem shuffleEval_embed (f : Series α) (k : ℕ) (fs : Fin k → Series α)
    (r : MvPolynomial (Fin k) ℚ) :
    shuffleEval α k fs r = shuffleEval α (k+1) (extTuple f k fs) (embedPoly k r) := by
  let g := extTuple f k fs
  -- `embedPoly k = aeval (X ∘ Fin.succ)` is a `ℚ`-algebra hom, hence a ring hom; these are
  -- its ring-hom properties, stated for the embedded polynomial.  The `aeval` is given an
  -- explicit `AlgHom` type so its `σ`/`R`/`S₁` are determined (a bare `aeval (X ∘ Fin.succ)`
  -- leaves them as metavariables and the typeclass search gets stuck).  We use the
  -- `RingHomClass` typeclass methods (`map_add`/`map_mul`/`map_one`), which are stated for
  -- the plain `aeval` application (the structure fields `.map_add` etc. go through
  -- `.toRingHom` and don't `rw`-match the plain application).
  let aev : MvPolynomial (Fin k) ℚ →ₐ[ℚ] MvPolynomial (Fin (k+1)) ℚ :=
    MvPolynomial.aeval (fun i => MvPolynomial.X (Fin.succ i))
  have hadd2 : ∀ p q, shuffleEval α (k+1) g (embedPoly k (p + q)) =
      shuffleEval α (k+1) g (embedPoly k p) + shuffleEval α (k+1) g (embedPoly k q) := by
    intro p q
    rw [embedPoly, embedPoly, embedPoly]
    rw [map_add aev p q, shuffleEval_add]
  have hsmul2 : ∀ (c : ℚ) p, shuffleEval α (k+1) g (embedPoly k (c • p)) =
      c • shuffleEval α (k+1) g (embedPoly k p) := by
    intro c p
    rw [embedPoly, embedPoly]
    -- `aev` is a `ℚ`-algebra hom, hence `ℚ`-linear (`ModuleHomClass`): `aev (c • p) = c • aev p`.
    rw [map_smul aev c p, shuffleEval_smul]
  have hmul2 : ∀ p q, shuffleEval α (k+1) g (embedPoly k (p * q)) =
      shuffle α (shuffleEval α (k+1) g (embedPoly k p)) (shuffleEval α (k+1) g (embedPoly k q)) := by
    intro p q
    rw [embedPoly, embedPoly, embedPoly]
    rw [map_mul aev p q, shuffleEval_mul]
  have hone : shuffleEval α k fs 1 = shuffleEval α (k+1) g (embedPoly k 1) := by
    rw [embedPoly]
    rw [map_one aev, shuffleEval_one, shuffleEval_one]
  have hgen : ∀ i, shuffleEval α k fs (MvPolynomial.X i) =
      shuffleEval α (k+1) g (embedPoly k (MvPolynomial.X i)) := by
    intro i
    rw [shuffleEval_X, embedPoly, MvPolynomial.aeval_X, shuffleEval_X]
    dsimp [g]
    rw [extTuple_succ]
  exact shuffleHom_ext k
    (fun p => shuffleEval α k fs p)
    (fun p => shuffleEval α (k+1) g (embedPoly k p))
    (shuffleEval_add k fs) hadd2
    (shuffleEval_smul k fs) hsmul2
    (shuffleEval_mul k fs) hmul2
    hone hgen r

/-! ### The coincidence: shuffle-finite ↔ shuffle-finite-sem -/

/-- Every shuffle-finite series is shuffle-finite in the semantic sense (the
    "finite implies finite-sem" direction of the coincidence).  The witnessing
    tuple is the generator series `A.sem (X_i)`, closed under left derivatives by
    the derivation property `sem_deriv`; `f` is the shuffle polynomial `X_0` in
    that tuple. -/
private theorem shuffleFinite_of_recognisable (f : Series α)
    (hfin : IsShuffleRecognisable α f) : IsShuffleFinite α f := by
  obtain ⟨A, hA⟩ := hfin
  let X0 : MvPolynomial (Fin A.dim) ℚ := MvPolynomial.X (Fin.mk 0 A.hdim)
  let fs := fun i => A.sem (MvPolynomial.X i)
  have hf : f = A.sem X0 := by
    rw [← hA, ShuffleAutomaton.recognised]
  have h1 : f = shuffleEval α A.dim fs X0 := by
    rw [hf, sem_eq_shuffleEval]
  refine ⟨A.dim, fs, X0, h1, ?_⟩
  intro a i
  refine ⟨A.Δ a i, ?_⟩
  have hlhs : leftDeriv α a (fs i) = A.sem (A.Δ a i) := by
    dsimp [fs]
    rw [sem_deriv, derivationExt_X]
  rw [hlhs, sem_eq_shuffleEval]

-- The shuffle product in infix notation (matching the paper's `⧢`): `f ⧢ g =
-- shuffle α f g`.  Declared as a true *operator* notation (`infixl`) rather than a
-- pattern notation: pattern notations (`notation f " ⧢ " g => …`) do not participate
-- in Lean's precedence-based parsing, so `f ⧢ g = h` would mis-parse as `f ⧢ (g = h)`;
-- the operator form binds `⧢` at precedence 70 (like `*`), so `f ⧢ g = h` parses as
-- `(f ⧢ g) = h`.  The shuffle product is commutative, so left-associativity is harmless.
section
infixl:70 " ⧢ " => shuffle _

/-! ### The left derivative commutes with the shuffle evaluation -/

/-- The left derivative of a shuffle power: `leftDeriv a (shufflePow α f n) =
    n • (shufflePow α f (n - 1) ⧢ leftDeriv a f)`.  The shuffle power is the iterated
    shuffle product of `n` copies of `f`; the left derivative (a derivation of the shuffle
    algebra) hits each copy in turn, and by commutativity of the shuffle product all `n`
    terms coincide. -/
private theorem leftDeriv_shufflePow (f : Series α) (a : α) (n : ℕ) :
    leftDeriv α a (shufflePow α f n) = (n : ℚ) • (shufflePow α f (n - 1) ⧢ leftDeriv α a f) := by
  induction n with
  | zero =>
      simp [shufflePow_zero, shuffleUnit_leftDeriv a, zero_smul]
  | succ n ih =>
      rw [shufflePow_succ]
      -- `shufflePow α f (n+1) = f ⧢ shufflePow α f n`; apply the Leibniz rule.
      have hL : leftDeriv α a (shuffle α f (shufflePow α f n)) =
          shuffle α (leftDeriv α a f) (shufflePow α f n) +
          shuffle α f (leftDeriv α a (shufflePow α f n)) :=
        shuffleLeibniz f (shufflePow α f n) a
      rw [hL, ih]
      by_cases hn : n = 0
      · subst hn
        simp [shufflePow_zero, shuffleUnit_leftDeriv a, shuffle_unit_left, shuffle_unit_right,
            shuffle_zero_left, shuffle_zero_right, zero_smul, one_smul]
      · have hsub : n - 1 + 1 = n := by omega
        -- First summand: `(leftDeriv a f) ⧢ shufflePow α f n = shufflePow α f n ⧢ leftDeriv a f`.
        have h1 : shuffle α (leftDeriv α a f) (shufflePow α f n) =
            shufflePow α f n ⧢ leftDeriv α a f := by
          rw [shuffle_comm (leftDeriv α a f) (shufflePow α f n)]
        -- Second summand: `f ⧢ (n • (shufflePow α f (n-1) ⧢ leftDeriv a f)) =
        --   n • (f ⧢ (shufflePow α f (n-1) ⧢ leftDeriv a f)) =
        --   n • ((f ⧢ shufflePow α f (n-1)) ⧢ leftDeriv a f) = n • (shufflePow α f n ⧢ leftDeriv a f)`.
        have h2 : shuffle α f ((n : ℚ) • (shufflePow α f (n - 1) ⧢ leftDeriv α a f)) =
            (n : ℚ) • (shufflePow α f n ⧢ leftDeriv α a f) := by
          rw [shuffle_smul_right]
          have h2a : shuffle α f (shufflePow α f (n - 1) ⧢ leftDeriv α a f) =
              shufflePow α f n ⧢ leftDeriv α a f := by
            rw [← shuffle_assoc, ← hsub, shufflePow_succ]
            rfl
          rw [h2a]
        rw [h1, h2]
        simp [add_smul, Nat.cast_add, Nat.cast_one]
        ring

/-- The left derivative of a shuffle product (the generalized Leibniz rule):
    `leftDeriv a (shuffleProd α k fs m) = ∑ i, (m i) • (shuffleProd α k fs (m - e_i) ⧢
    leftDeriv a (fs i))`.  The shuffle product is a fold of the iterated powers
    `shufflePow α (fs i) (m i)`; the left derivative of the fold is the sum over the
    positions where it hits (`shuffleLeibniz` by induction on the Finset), and at each
    position it is `(m i) • (shufflePow α (fs i) (m i - 1) ⧢ leftDeriv a (fs i))`
    (`leftDeriv_shufflePow`).  The product with the `i`-th factor removed and the reduced
    power is `shuffleProd α k fs (m - e_i)`. -/
private theorem leftDeriv_shuffleProd (k : ℕ) (fs : Fin k → Series α) (a : α)
    (m : Fin k →₀ ℕ) :
    leftDeriv α a (shuffleProd α k fs m) =
      ∑ i : Fin k, (m i : ℚ) • (shuffleProd α k fs (m - Finsupp.single i 1) ⧢ leftDeriv α a (fs i)) := by
  let F := fun (s : Finset (Fin k)) =>
      s.fold (shuffle α) (shuffleUnit α) (fun i => shufflePow α (fs i) (m i))
  have hF_univ : F Finset.univ = shuffleProd α k fs m := (shuffleProd_eq_fold k fs m).symm
  -- The generalized Leibniz rule for the fold, by induction on the Finset.
  have hLeib : ∀ (s : Finset (Fin k)),
      leftDeriv α a (F s) =
        ∑ i ∈ s, (m i : ℚ) • (F (s \ {i}) ⧢ shufflePow α (fs i) (m i - 1) ⧢ leftDeriv α a (fs i)) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        simp [F, Finset.fold_empty, shuffleUnit_leftDeriv a]
    | insert j s hj ih =>
        have hF : F (insert j s) = F s ⧢ shufflePow α (fs j) (m j) := by
          dsimp [F] at ⊢
          rw [Finset.fold_insert hj, shuffle_comm]
        rw [hF]
        have hL : leftDeriv α a (F s ⧢ shufflePow α (fs j) (m j)) =
            shuffle α (leftDeriv α a (F s)) (shufflePow α (fs j) (m j)) +
            shuffle α (F s) (leftDeriv α a (shufflePow α (fs j) (m j))) :=
          shuffleLeibniz (F s) (shufflePow α (fs j) (m j)) a
        rw [hL, ih]
        -- The second summand: `F s ⧢ (m j) • (shufflePow α (fs j) (m j - 1) ⧢ leftDeriv a (fs j))`
        --   `= (m j) • (F s ⧢ shufflePow α (fs j) (m j - 1) ⧢ leftDeriv a (fs j))`
        --   `= (m j) • (F ((insert j s) \ {j}) ⧢ shufflePow α (fs j) (m j - 1) ⧢ leftDeriv a (fs j))`.
        have hsecond : shuffle α (F s) ((m j : ℚ) • (shufflePow α (fs j) (m j - 1) ⧢ leftDeriv α a (fs j))) =
            (m j : ℚ) • (F ((insert j s) \ {j}) ⧢ shufflePow α (fs j) (m j - 1) ⧢ leftDeriv α a (fs j)) := by
          rw [shuffle_smul_right]
          have hdel : F ((insert j s) \ {j}) = F s := by
            dsimp [F] at ⊢
            have hset : (insert j s) \ {j} = s := by
              ext x
              simp [Finset.mem_sdiff, Finset.mem_insert, hj]
              aesop
            rw [hset]
          rw [hdel]
          have hsh : F s ⧢ shufflePow α (fs j) (m j - 1) ⧢ leftDeriv α a (fs j) =
              F s ⧢ (shufflePow α (fs j) (m j - 1) ⧢ leftDeriv α a (fs j)) := by
            rw [shuffle_assoc]
          rw [hsh]
        -- The first summand: distribute `⧢ shufflePow α (fs j) (m j)` over the sum.
        have hfirst : (∑ i ∈ s, (m i : ℚ) • (F (s \ {i}) ⧢ shufflePow α (fs i) (m i - 1) ⧢ leftDeriv α a (fs i)))
            ⧢ shufflePow α (fs j) (m j) =
            ∑ i ∈ s, (m i : ℚ) • (F ((insert j s) \ {i}) ⧢ shufflePow α (fs i) (m i - 1) ⧢ leftDeriv α a (fs i)) := by
          have hdist : (∑ i ∈ s, (m i : ℚ) • (F (s \ {i}) ⧢ shufflePow α (fs i) (m i - 1) ⧢ leftDeriv α a (fs i)))
              ⧢ shufflePow α (fs j) (m j) =
              ∑ i ∈ s, ((m i : ℚ) • (F (s \ {i}) ⧢ shufflePow α (fs i) (m i - 1) ⧢ leftDeriv α a (fs i)))
                ⧢ shufflePow α (fs j) (m j) := by
            -- A finite sum distributes over the shuffle product (right argument fixed).
            have : ∀ (t : Finset (Fin k)) (g : Fin k → Series α),
                (∑ u ∈ t, g u) ⧢ shufflePow α (fs j) (m j) =
                  ∑ u ∈ t, g u ⧢ shufflePow α (fs j) (m j) := by
              intro t g
              induction t using Finset.induction_on with
              | empty => simp [shuffle_zero_left]
              | insert x t hx ih' =>
                  simp [Finset.sum_insert hx, shuffle_add_left, ih']
            exact this s (fun i => (m i : ℚ) • (F (s \ {i}) ⧢ shufflePow α (fs i) (m i - 1) ⧢ leftDeriv α a (fs i)))
          rw [hdist]
          apply Finset.sum_congr rfl
          intro i hi
          have hdel : F ((insert j s) \ {i}) = F (s \ {i}) ⧢ shufflePow α (fs j) (m j) := by
            have hne : i ≠ j := by
              intro hh
              rw [hh] at hi
              exact hj hi
            have hset : (insert j s) \ {i} = insert j (s \ {i}) := by
              ext x
              simp [Finset.mem_sdiff, Finset.mem_insert, hne]
              aesop
            rw [hset]
            dsimp [F]
            have hjn : j ∉ s \ {i} := by
              intro hh
              exact hj (Finset.mem_sdiff.mp hh).1
            rw [Finset.fold_insert hjn, shuffle_comm]
          rw [hdel]
          -- `(F (s \ {i}) ⧢ shufflePow α (fs j) (m j)) ⧢ (shufflePow α (fs i) (m i - 1) ⧢ leftDeriv a (fs i))`
          --   `= F (s \ {i}) ⧢ shufflePow α (fs i) (m i - 1) ⧢ leftDeriv a (fs i) ⧢ shufflePow α (fs j) (m j)`
          --   `= (F (s \ {i}) ⧢ shufflePow α (fs i) (m i - 1) ⧢ leftDeriv a (fs i)) ⧢ shufflePow α (fs j) (m j)`
          -- (commutativity + associativity of the shuffle product).
          have hre : (F (s \ {i}) ⧢ shufflePow α (fs j) (m j))
              ⧢ (shufflePow α (fs i) (m i - 1) ⧢ leftDeriv α a (fs i)) =
              (F (s \ {i}) ⧢ shufflePow α (fs i) (m i - 1) ⧢ leftDeriv α a (fs i))
                ⧢ shufflePow α (fs j) (m j) := by
            let A := F (s \ {i})
            let B := shufflePow α (fs j) (m j)
            let C := shufflePow α (fs i) (m i - 1)
            let D := leftDeriv α a (fs i)
            change (A ⧢ B) ⧢ (C ⧢ D) = (A ⧢ C ⧢ D) ⧢ B
            calc
              (A ⧢ B) ⧢ (C ⧢ D) = (C ⧢ D) ⧢ (A ⧢ B) := by rw [shuffle_comm]
              _ = C ⧢ (D ⧢ (A ⧢ B)) := by rw [shuffle_assoc]
              _ = C ⧢ ((D ⧢ A) ⧢ B) := by
                have h : D ⧢ (A ⧢ B) = (D ⧢ A) ⧢ B := by rw [← shuffle_assoc]
                rw [h]
              _ = C ⧢ ((A ⧢ D) ⧢ B) := by
                have h : D ⧢ A = A ⧢ D := by rw [shuffle_comm]
                rw [h]
              _ = (C ⧢ (A ⧢ D)) ⧢ B := by rw [← shuffle_assoc]
              _ = ((C ⧢ A) ⧢ D) ⧢ B := by
                have h : C ⧢ (A ⧢ D) = (C ⧢ A) ⧢ D := by rw [← shuffle_assoc]
                rw [h]
              _ = ((A ⧢ C) ⧢ D) ⧢ B := by
                have h : C ⧢ A = A ⧢ C := by rw [shuffle_comm]
                rw [h]
          conv =>
            rhs
            · rw [shuffle_assoc]
          rw [hre]
          simp [shuffle_smul_left]
        -- Expand `leftDeriv a (shufflePow (fs j) (m j))` so that `hsecond` applies.
        rw [leftDeriv_shufflePow, hfirst, hsecond]
        -- The two sums combine into the sum over `insert j s` (up to commutativity of `+`).
        rw [Finset.sum_insert hj]
        abel
  -- Specialise to `s = univ` and rewrite `F (univ \ {i}) ⧢ shufflePow α (fs i) (m i - 1)`
  -- to `shuffleProd α k fs (m - e_i)`.
  have hmain : leftDeriv α a (shuffleProd α k fs m) =
      ∑ i : Fin k, (m i : ℚ) • (F ((Finset.univ : Finset (Fin k)) \ {i}) ⧢
        shufflePow α (fs i) (m i - 1) ⧢ leftDeriv α a (fs i)) := by
    rw [← hF_univ]
    simpa using hLeib Finset.univ
  have hFdel : ∀ i, F ((Finset.univ : Finset (Fin k)) \ {i}) ⧢ shufflePow α (fs i) (m i - 1) =
      shuffleProd α k fs (m - Finsupp.single i 1) := by
    intro i
    dsimp [F]
    rw [shuffleProd_eq_fold]
    -- The LHS is the fold over `univ \ {i}` of `shufflePow α (fs j) (m j)`, times the `i`-th
    -- factor `shufflePow α (fs i) (m i - 1)`.  The RHS is the fold over `univ` of
    -- `shufflePow α (fs j) ((m - e_i) j)`.  Since `univ = insert i (univ \ {i})` with
    -- `i ∉ univ \ {i}`, the RHS fold splits by `Finset.fold_insert` into the `i`-th factor
    -- (`shufflePow α (fs i) ((m - e_i) i)`, which equals `shufflePow α (fs i) (m i - 1)`
    -- because `(e_i) i = 1`) times the fold over `univ \ {i}` (where `(e_i) j = 0`, so
    -- `(m - e_i) j = m j`).  We normalise `(m - e_i) ·` to the pointwise `m · - (e_i) ·`
    -- (`Finsupp.tsub_apply`) so the pointwise-stated `hexp_i`/`hfsub` apply, then use the
    -- commutativity of the shuffle product.
    have hno : i ∉ (Finset.univ : Finset (Fin k)) \ {i} := by
      simp [Finset.mem_sdiff]
    have huniv : (Finset.univ : Finset (Fin k)) = insert i ((Finset.univ : Finset (Fin k)) \ {i}) := by
      ext j
      simp [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert]
      <;> tauto
    conv =>
      rhs
      · rw [huniv, Finset.fold_insert hno]
    have hexp_i : shufflePow α (fs i) (m i - (Finsupp.single i (1 : ℕ)) i) = shufflePow α (fs i) (m i - 1) := by
      simp [Finsupp.single_apply]
    have hexp_ne : ∀ j, j ≠ i → shufflePow α (fs j) (m j - (Finsupp.single i (1 : ℕ)) j) = shufflePow α (fs j) (m j) := by
      intro j hj
      simp [hj, Finsupp.single_apply]
    have hfsub : ((Finset.univ : Finset (Fin k)) \ {i}).fold (shuffle α) (shuffleUnit α)
        (fun j => shufflePow α (fs j) (m j - (Finsupp.single i (1 : ℕ)) j)) =
        ((Finset.univ : Finset (Fin k)) \ {i}).fold (shuffle α) (shuffleUnit α)
          (fun j => shufflePow α (fs j) (m j)) := by
      apply Finset.fold_congr
      intro j hjm
      have hjne : j ≠ i := by
        intro h
        rw [h] at hjm
        simp [Finset.mem_sdiff] at hjm
      rw [hexp_ne j hjne]
    -- Normalise `(m - e_i) ·` to the pointwise form `m · - (e_i) ·` (via `Finsupp.tsub_apply`)
    -- so that `hexp_i`/`hfsub` (stated pointwise) match the goal; the two shuffle factors are
    -- then equal up to commutativity.
    simp only [Finsupp.tsub_apply]
    rw [hexp_i, hfsub]
    exact shuffle_comm _ _
  -- Rewrite each summand using `hFdel`.
  calc
    leftDeriv α a (shuffleProd α k fs m) =
        ∑ i : Fin k, (m i : ℚ) • (F ((Finset.univ : Finset (Fin k)) \ {i}) ⧢
          shufflePow α (fs i) (m i - 1) ⧢ leftDeriv α a (fs i)) := hmain
    _ = ∑ i : Fin k, (m i : ℚ) • (shuffleProd α k fs (m - Finsupp.single i 1) ⧢ leftDeriv α a (fs i)) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hFdel i]
      <;> rw [shuffle_assoc]

/-- The left derivative of a shuffle polynomial is the shuffle polynomial obtained by applying
    the derivation: if `leftDeriv a (fs i) = shuffleEval α k fs (q i)` for all `i`, then
    `leftDeriv a (shuffleEval α k fs p) = shuffleEval α k fs (derivationExt q p)`.  The left
    derivative is a derivation of the shuffle algebra, so it commutes with the shuffle-algebra
    homomorphism `shuffleEval`; on a monomial `X^m` both sides are `∑ i (m_i) • (X^{m-e_i} ⧢
    leftDeriv a (fs_i))`, and both sides are `ℚ`-linear, so they agree on all of `p`. -/
private theorem leftDeriv_shuffleEval_deriv (k : ℕ) (fs : Fin k → Series α) (a : α)
    (q : Fin k → MvPolynomial (Fin k) ℚ)
    (hq : ∀ i, leftDeriv α a (fs i) = shuffleEval α k fs (q i))
    (p : MvPolynomial (Fin k) ℚ) :
    leftDeriv α a (shuffleEval α k fs p) = shuffleEval α k fs (derivationExt q p) := by
  -- Both sides are `ℚ`-linear in `p`; it suffices to check on the monomial summands and
  -- commute with the support sum.
  have hLHS : leftDeriv α a (shuffleEval α k fs p) =
      ∑ m ∈ p.support, p.coeff m • leftDeriv α a (shuffleProd α k fs m) := by
    have hsum : leftDeriv α a (shuffleEval α k fs p) =
        leftDeriv α a (p.support.sum fun m => p.coeff m • shuffleProd α k fs m) := by
      rw [shuffleEval]
    rw [hsum]
    have hsum2 : leftDeriv α a (p.support.sum fun m => p.coeff m • shuffleProd α k fs m) =
        ∑ m ∈ p.support, p.coeff m • leftDeriv α a (shuffleProd α k fs m) := by
      -- `leftDeriv a` is `ℚ`-linear, so it commutes with the finite sum.
      have : ∀ (t : Finset (Fin k →₀ ℕ)) (g : (Fin k →₀ ℕ) → Series α),
          leftDeriv α a (∑ j ∈ t, g j) = ∑ j ∈ t, leftDeriv α a (g j) := by
        intro t g
        induction t using Finset.induction_on with
        | empty => simp [leftDeriv_zero]
        | insert x t hx ih' =>
            simp [Finset.sum_insert hx, ih', leftDeriv_add a]
      have hlin := this p.support (fun m => p.coeff m • shuffleProd α k fs m)
      rw [hlin]
      apply Finset.sum_congr rfl
      intro m _
      rw [leftDeriv_smul a]
    rw [hsum2]
  have hRHS : shuffleEval α k fs (derivationExt q p) =
      ∑ m ∈ p.support, p.coeff m • leftDeriv α a (shuffleProd α k fs m) := by
    have hderiv : derivationExt q p = p.support.sum fun m => p.coeff m • derivMono q m :=
      derivationExt_eq_sum q p
    rw [hderiv]
    have hsum : shuffleEval α k fs (p.support.sum fun m => p.coeff m • derivMono q m) =
        ∑ m ∈ p.support, p.coeff m • shuffleEval α k fs (derivMono q m) := by
      have : ∀ (t : Finset (Fin k →₀ ℕ)) (g : (Fin k →₀ ℕ) → MvPolynomial (Fin k) ℚ),
          shuffleEval α k fs (∑ j ∈ t, g j) = ∑ j ∈ t, shuffleEval α k fs (g j) := by
        intro t g
        induction t using Finset.induction_on with
        | empty => simp [shuffleEval_zero]
        | insert x t hx ih' =>
            simp [Finset.sum_insert hx, ih', shuffleEval_add]
      have hlin := this p.support (fun m => p.coeff m • derivMono q m)
      rw [hlin]
      apply Finset.sum_congr rfl
      intro m _
      rw [shuffleEval_smul]
    rw [hsum]
    apply Finset.sum_congr rfl
    intro m _
    -- `shuffleEval α k fs (derivMono q m) = leftDeriv α a (shuffleProd α k fs m)`.
    have hmono : derivMono q m = ∑ i : Fin k, ((m i : ℚ) • MvPolynomial.monomial (m - Finsupp.single i 1) 1) * q i := rfl
    have h1 : shuffleEval α k fs (derivMono q m) =
        ∑ i : Fin k, (m i : ℚ) • shuffleEval α k fs
          (MvPolynomial.monomial (m - Finsupp.single i 1) 1 * q i) := by
      rw [hmono]
      have : ∀ (t : Finset (Fin k)) (g : Fin k → MvPolynomial (Fin k) ℚ),
          shuffleEval α k fs (∑ j ∈ t, g j) = ∑ j ∈ t, shuffleEval α k fs (g j) := by
        intro t g
        induction t using Finset.induction_on with
        | empty => simp [shuffleEval_zero]
        | insert x t hx ih' =>
            simp [Finset.sum_insert hx, ih', shuffleEval_add]
      have hlin := this (Finset.univ : Finset (Fin k))
          (fun i => ((m i : ℚ) • MvPolynomial.monomial (m - Finsupp.single i 1) 1) * q i)
      rw [hlin]
      apply Finset.sum_congr rfl
      intro i _
      simp
      rw [shuffleEval_smul]
    rw [h1]
    have h2 : ∑ i : Fin k, (m i : ℚ) • shuffleEval α k fs
        (MvPolynomial.monomial (m - Finsupp.single i 1) 1 * q i) =
        ∑ i : Fin k, (m i : ℚ) • shuffle α
          (shuffleEval α k fs (MvPolynomial.monomial (m - Finsupp.single i 1) 1))
          (shuffleEval α k fs (q i)) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [shuffleEval_mul]
    rw [h2]
    have h3 : ∑ i : Fin k, (m i : ℚ) • shuffle α
        (shuffleEval α k fs (MvPolynomial.monomial (m - Finsupp.single i 1) 1))
        (shuffleEval α k fs (q i)) =
        ∑ i : Fin k, (m i : ℚ) • shuffle α
          (shuffleProd α k fs (m - Finsupp.single i 1)) (leftDeriv α a (fs i)) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [shuffleEval_monomial, hq i]
      <;> simp
    rw [h3]
    -- The summand `(m i) • (shuffleProd α k fs (m - e_i) ⧢ leftDeriv a (fs i))` is exactly the
    -- `i`-th term of `leftDeriv α a (shuffleProd α k fs m)` (`leftDeriv_shuffleProd`).
    have hlp : leftDeriv α a (shuffleProd α k fs m) =
        ∑ i : Fin k, (m i : ℚ) • (shuffleProd α k fs (m - Finsupp.single i 1) ⧢ leftDeriv α a (fs i)) :=
      leftDeriv_shuffleProd k fs a m
    -- Because `⧢` is definitionally `shuffle`, the two summands coincide and `rw [← hlp]`
    -- closes the goal.
    rw [← hlp]
  rw [hLHS, hRHS]

/-! ### The right derivative: linearity, the product rule, and the shuffle power/product -/

/-- The right derivative is `ℚ`-linear (additive). -/
private theorem rightDeriv_add (a : α) (f g : Series α) :
    rightDeriv α a (f + g) = rightDeriv α a f + rightDeriv α a g := by
  funext w; dsimp [rightDeriv]

/-- The right derivative is `ℚ`-linear (scalar multiplication). -/
private theorem rightDeriv_smul (a : α) (c : ℚ) (f : Series α) :
    rightDeriv α a (c • f) = c • rightDeriv α a f := by
  funext w; dsimp [rightDeriv]

/-- The right derivative of the zero series is zero. -/
private theorem rightDeriv_zero (a : α) : rightDeriv α a 0 = 0 := by
  funext w; dsimp [rightDeriv]

/-- The right derivative of the shuffle unit is zero: `shuffleUnit (w ++ [a]) = 0` for all
    `w` (the shuffle unit is supported only on the empty word, and `w ++ [a] ≠ []`). -/
private theorem shuffleUnit_rightDeriv (a : α) : rightDeriv α a (shuffleUnit α) = 0 := by
  funext w
  dsimp [rightDeriv, shuffleUnit]
  simp

/-- The product rule for right derivatives: `rightDeriv a (f ⧢ g) =
    (rightDeriv a f) ⧢ g + f ⧢ (rightDeriv a g)`.  Proven by induction on the word `w`,
    using the shuffle recursion (which is on the left derivative) and the commutativity of
    left and right derivatives (`LeftRightDerivativesCommute`) to match the terms. -/
private theorem rightDeriv_shuffle (f g : Series α) (a : α) :
    rightDeriv α a (shuffle α f g) = shuffle α (rightDeriv α a f) g + shuffle α f (rightDeriv α a g) := by
  funext w
  dsimp [rightDeriv, shuffle]
  have h : ∀ (w : List α), ∀ (F G : Series α),
      shuffleRec α F G (w ++ [a]) = shuffleRec α (rightDeriv α a F) G w + shuffleRec α F (rightDeriv α a G) w := by
    intro w
    induction w with
    | nil =>
        intro F G
        rw [List.nil_append]
        rw [shuffleRec_cons]
        repeat rw [shuffleRec_nil]
        simp [leftDeriv, rightDeriv]
    | cons b w' ih =>
        intro F G
        rw [List.cons_append]
        rw [shuffleRec_cons]
        have h1 := ih (leftDeriv α b F) G
        have h2 := ih F (leftDeriv α b G)
        rw [h1, h2]
        rw [shuffleRec_cons, shuffleRec_cons]
        have hc1 : rightDeriv α a (leftDeriv α b F) = leftDeriv α b (rightDeriv α a F) := by
          have := congrArg (fun h => h F) (LeftRightDerivativesCommute α b a)
          simp [Function.comp_apply] at this
          exact this.symm
        have hc2 : rightDeriv α a (leftDeriv α b G) = leftDeriv α b (rightDeriv α a G) := by
          have := congrArg (fun h => h G) (LeftRightDerivativesCommute α b a)
          simp [Function.comp_apply] at this
          exact this.symm
        rw [hc1, hc2]
        abel
  exact h w f g

/-- The right derivative of a shuffle power: `rightDeriv a (shufflePow α f n) =
    n • (shufflePow α f (n - 1) ⧢ rightDeriv a f)`.  Because the shuffle product is
    commutative, this has the same form as the left-derivative version; the right derivative
    (a derivation of the shuffle algebra) hits each of the `n` copies in turn, and all terms
    coincide. -/
private theorem rightDeriv_shufflePow (f : Series α) (a : α) (n : ℕ) :
    rightDeriv α a (shufflePow α f n) = (n : ℚ) • (shufflePow α f (n - 1) ⧢ rightDeriv α a f) := by
  induction n with
  | zero =>
      simp [shufflePow_zero, shuffleUnit_rightDeriv a, zero_smul]
  | succ n ih =>
      rw [shufflePow_succ]
      have hL : rightDeriv α a (shuffle α f (shufflePow α f n)) =
          shuffle α (rightDeriv α a f) (shufflePow α f n) +
          shuffle α f (rightDeriv α a (shufflePow α f n)) :=
        rightDeriv_shuffle f (shufflePow α f n) a
      rw [hL, ih]
      by_cases hn : n = 0
      · subst hn
        simp [shufflePow_zero, shuffle_unit_left, shuffle_unit_right,
            shuffle_zero_left, shuffle_zero_right, zero_smul, one_smul]
      · have hsub : n - 1 + 1 = n := by omega
        have h1 : shuffle α (rightDeriv α a f) (shufflePow α f n) =
            shufflePow α f n ⧢ rightDeriv α a f := by
          rw [shuffle_comm (rightDeriv α a f) (shufflePow α f n)]
        have h2 : shuffle α f ((n : ℚ) • (shufflePow α f (n - 1) ⧢ rightDeriv α a f)) =
            (n : ℚ) • (shufflePow α f n ⧢ rightDeriv α a f) := by
          rw [shuffle_smul_right]
          have h2a : shuffle α f (shufflePow α f (n - 1) ⧢ rightDeriv α a f) =
              shufflePow α f n ⧢ rightDeriv α a f := by
            rw [← shuffle_assoc, ← hsub, shufflePow_succ]
            rfl
          rw [h2a]
        rw [h1, h2]
        simp [add_smul, Nat.cast_add, Nat.cast_one]
        ring

/-- The right derivative of a shuffle product (the generalized Leibniz rule):
    `rightDeriv a (shuffleProd α k fs m) = ∑ i, (m i) • (shuffleProd α k fs (m - e_i) ⧢
    rightDeriv a (fs i))`.  This mirrors `leftDeriv_shuffleProd`: the shuffle product is a fold
    of the iterated powers `shufflePow α (fs i) (m i)`, the right derivative of the fold is the
    sum over the positions where it hits (`rightDeriv_shuffle` by induction on the Finset), and
    at each position it is `(m i) • (shufflePow α (fs i) (m i - 1) ⧢ rightDeriv a (fs i))`
    (`rightDeriv_shufflePow`). -/
private theorem rightDeriv_shuffleProd (k : ℕ) (fs : Fin k → Series α) (a : α)
    (m : Fin k →₀ ℕ) :
    rightDeriv α a (shuffleProd α k fs m) =
      ∑ i : Fin k, (m i : ℚ) • (shuffleProd α k fs (m - Finsupp.single i 1) ⧢ rightDeriv α a (fs i)) := by
  let F := fun (s : Finset (Fin k)) =>
      s.fold (shuffle α) (shuffleUnit α) (fun i => shufflePow α (fs i) (m i))
  have hF_univ : F Finset.univ = shuffleProd α k fs m := (shuffleProd_eq_fold k fs m).symm
  have hLeib : ∀ (s : Finset (Fin k)),
      rightDeriv α a (F s) =
        ∑ i ∈ s, (m i : ℚ) • (F (s \ {i}) ⧢ shufflePow α (fs i) (m i - 1) ⧢ rightDeriv α a (fs i)) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        simp [F, Finset.fold_empty, shuffleUnit_rightDeriv a]
    | insert j s hj ih =>
        have hF : F (insert j s) = F s ⧢ shufflePow α (fs j) (m j) := by
          dsimp [F] at ⊢
          rw [Finset.fold_insert hj, shuffle_comm]
        rw [hF]
        have hL : rightDeriv α a (F s ⧢ shufflePow α (fs j) (m j)) =
            shuffle α (rightDeriv α a (F s)) (shufflePow α (fs j) (m j)) +
            shuffle α (F s) (rightDeriv α a (shufflePow α (fs j) (m j))) :=
          rightDeriv_shuffle (F s) (shufflePow α (fs j) (m j)) a
        rw [hL, ih]
        have hsecond : shuffle α (F s) ((m j : ℚ) • (shufflePow α (fs j) (m j - 1) ⧢ rightDeriv α a (fs j))) =
            (m j : ℚ) • (F ((insert j s) \ {j}) ⧢ shufflePow α (fs j) (m j - 1) ⧢ rightDeriv α a (fs j)) := by
          rw [shuffle_smul_right]
          have hdel : F ((insert j s) \ {j}) = F s := by
            dsimp [F] at ⊢
            have hset : (insert j s) \ {j} = s := by
              ext x
              simp [Finset.mem_sdiff, Finset.mem_insert, hj]
              aesop
            rw [hset]
          rw [hdel]
          have hsh : F s ⧢ shufflePow α (fs j) (m j - 1) ⧢ rightDeriv α a (fs j) =
              F s ⧢ (shufflePow α (fs j) (m j - 1) ⧢ rightDeriv α a (fs j)) := by
            rw [shuffle_assoc]
          rw [hsh]
        have hfirst : (∑ i ∈ s, (m i : ℚ) • (F (s \ {i}) ⧢ shufflePow α (fs i) (m i - 1) ⧢ rightDeriv α a (fs i)))
            ⧢ shufflePow α (fs j) (m j) =
            ∑ i ∈ s, (m i : ℚ) • (F ((insert j s) \ {i}) ⧢ shufflePow α (fs i) (m i - 1) ⧢ rightDeriv α a (fs i)) := by
          have hdist : (∑ i ∈ s, (m i : ℚ) • (F (s \ {i}) ⧢ shufflePow α (fs i) (m i - 1) ⧢ rightDeriv α a (fs i)))
              ⧢ shufflePow α (fs j) (m j) =
              ∑ i ∈ s, ((m i : ℚ) • (F (s \ {i}) ⧢ shufflePow α (fs i) (m i - 1) ⧢ rightDeriv α a (fs i)))
                ⧢ shufflePow α (fs j) (m j) := by
            have : ∀ (t : Finset (Fin k)) (g : Fin k → Series α),
                (∑ u ∈ t, g u) ⧢ shufflePow α (fs j) (m j) =
                  ∑ u ∈ t, g u ⧢ shufflePow α (fs j) (m j) := by
              intro t g
              induction t using Finset.induction_on with
              | empty => simp [shuffle_zero_left]
              | insert x t hx ih' =>
                  simp [Finset.sum_insert hx, shuffle_add_left, ih']
            exact this s (fun i => (m i : ℚ) • (F (s \ {i}) ⧢ shufflePow α (fs i) (m i - 1) ⧢ rightDeriv α a (fs i)))
          rw [hdist]
          apply Finset.sum_congr rfl
          intro i hi
          have hdel : F ((insert j s) \ {i}) = F (s \ {i}) ⧢ shufflePow α (fs j) (m j) := by
            have hne : i ≠ j := by
              intro hh
              rw [hh] at hi
              exact hj hi
            have hset : (insert j s) \ {i} = insert j (s \ {i}) := by
              ext x
              simp [Finset.mem_sdiff, Finset.mem_insert, hne]
              aesop
            rw [hset]
            dsimp [F]
            have hjn : j ∉ s \ {i} := by
              intro hh
              exact hj (Finset.mem_sdiff.mp hh).1
            rw [Finset.fold_insert hjn, shuffle_comm]
          rw [hdel]
          have hre : (F (s \ {i}) ⧢ shufflePow α (fs j) (m j))
              ⧢ (shufflePow α (fs i) (m i - 1) ⧢ rightDeriv α a (fs i)) =
              (F (s \ {i}) ⧢ shufflePow α (fs i) (m i - 1) ⧢ rightDeriv α a (fs i))
                ⧢ shufflePow α (fs j) (m j) := by
            let A := F (s \ {i})
            let B := shufflePow α (fs j) (m j)
            let C := shufflePow α (fs i) (m i - 1)
            let D := rightDeriv α a (fs i)
            change (A ⧢ B) ⧢ (C ⧢ D) = (A ⧢ C ⧢ D) ⧢ B
            calc
              (A ⧢ B) ⧢ (C ⧢ D) = (C ⧢ D) ⧢ (A ⧢ B) := by rw [shuffle_comm]
              _ = C ⧢ (D ⧢ (A ⧢ B)) := by rw [shuffle_assoc]
              _ = C ⧢ ((D ⧢ A) ⧢ B) := by
                have h : D ⧢ (A ⧢ B) = (D ⧢ A) ⧢ B := by rw [← shuffle_assoc]
                rw [h]
              _ = C ⧢ ((A ⧢ D) ⧢ B) := by
                have h : D ⧢ A = A ⧢ D := by rw [shuffle_comm]
                rw [h]
              _ = (C ⧢ (A ⧢ D)) ⧢ B := by rw [← shuffle_assoc]
              _ = ((C ⧢ A) ⧢ D) ⧢ B := by
                have h : C ⧢ (A ⧢ D) = (C ⧢ A) ⧢ D := by rw [← shuffle_assoc]
                rw [h]
              _ = ((A ⧢ C) ⧢ D) ⧢ B := by
                have h : C ⧢ A = A ⧢ C := by rw [shuffle_comm]
                rw [h]
          conv =>
            rhs
            · rw [shuffle_assoc]
          rw [hre]
          simp [shuffle_smul_left]
        rw [rightDeriv_shufflePow, hfirst, hsecond]
        rw [Finset.sum_insert hj]
        abel
  have hmain : rightDeriv α a (shuffleProd α k fs m) =
      ∑ i : Fin k, (m i : ℚ) • (F ((Finset.univ : Finset (Fin k)) \ {i}) ⧢
        shufflePow α (fs i) (m i - 1) ⧢ rightDeriv α a (fs i)) := by
    rw [← hF_univ]
    simpa using hLeib Finset.univ
  have hFdel : ∀ i, F ((Finset.univ : Finset (Fin k)) \ {i}) ⧢ shufflePow α (fs i) (m i - 1) =
      shuffleProd α k fs (m - Finsupp.single i 1) := by
    intro i
    dsimp [F]
    rw [shuffleProd_eq_fold]
    have hno : i ∉ (Finset.univ : Finset (Fin k)) \ {i} := by
      simp [Finset.mem_sdiff]
    have huniv : (Finset.univ : Finset (Fin k)) = insert i ((Finset.univ : Finset (Fin k)) \ {i}) := by
      ext j
      simp [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert]
      <;> tauto
    conv =>
      rhs
      · rw [huniv, Finset.fold_insert hno]
    have hexp_i : shufflePow α (fs i) (m i - (Finsupp.single i (1 : ℕ)) i) = shufflePow α (fs i) (m i - 1) := by
      simp [Finsupp.single_apply]
    have hexp_ne : ∀ j, j ≠ i → shufflePow α (fs j) (m j - (Finsupp.single i (1 : ℕ)) j) = shufflePow α (fs j) (m j) := by
      intro j hj
      simp [hj, Finsupp.single_apply]
    have hfsub : ((Finset.univ : Finset (Fin k)) \ {i}).fold (shuffle α) (shuffleUnit α)
        (fun j => shufflePow α (fs j) (m j - (Finsupp.single i (1 : ℕ)) j)) =
        ((Finset.univ : Finset (Fin k)) \ {i}).fold (shuffle α) (shuffleUnit α)
          (fun j => shufflePow α (fs j) (m j)) := by
      apply Finset.fold_congr
      intro j hjm
      have hjne : j ≠ i := by
        intro h
        rw [h] at hjm
        simp [Finset.mem_sdiff] at hjm
      rw [hexp_ne j hjne]
    -- Normalise `(m - e_i) ·` to the pointwise form `m · - (e_i) ·` (via `Finsupp.tsub_apply`)
    -- so that `hexp_i`/`hfsub` (stated pointwise) match the goal; the two shuffle factors are
    -- then equal up to commutativity.
    simp only [Finsupp.tsub_apply]
    rw [hexp_i, hfsub]
    exact shuffle_comm _ _
  calc
    rightDeriv α a (shuffleProd α k fs m) =
        ∑ i : Fin k, (m i : ℚ) • (F ((Finset.univ : Finset (Fin k)) \ {i}) ⧢
          shufflePow α (fs i) (m i - 1) ⧢ rightDeriv α a (fs i)) := hmain
    _ = ∑ i : Fin k, (m i : ℚ) • (shuffleProd α k fs (m - Finsupp.single i 1) ⧢ rightDeriv α a (fs i)) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hFdel i]
      <;> rw [shuffle_assoc]

end

/-! ### The coincidence (semantic → automaton direction) -/

/-- The shuffle power at the empty word is the pointwise power: `shufflePow α f n [] =
    f [] ^ n`.  The shuffle product at the empty word is the pointwise product
    (`shuffleRec_nil`), and the shuffle unit at the empty word is `1`. -/
private theorem shufflePow_nil (f : Series α) (n : ℕ) : shufflePow α f n [] = f [] ^ n := by
  induction n with
  | zero =>
      simp [shufflePow_zero, shuffleUnit]
  | succ n ih =>
      rw [shufflePow_succ]
      simp [shuffle, shuffleRec_nil, ih]
      ring

/-- The shuffle monomial at the empty word is the pointwise monomial:
    `shuffleProd α k fs m [] = ∏ i, (fs i) [] ^ (m i)`.  The shuffle product at the empty
    word is the pointwise product (`shuffleRec_nil`), so the fold over the iterated powers
    becomes the pointwise product of the powers at the empty word. -/
private theorem shuffleProd_nil (k : ℕ) (fs : Fin k → Series α) (m : Fin k →₀ ℕ) :
    shuffleProd α k fs m [] = ∏ i : Fin k, (fs i) [] ^ (m i) := by
  have : ∀ (s : Finset (Fin k)),
      s.fold (shuffle α) (shuffleUnit α) (fun i => shufflePow α (fs i) (m i)) [] =
        ∏ i ∈ s, (fs i) [] ^ (m i) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        simp [Finset.fold_empty, shuffleUnit, Finset.prod_empty]
    | insert x s hx ih =>
        simp [shuffle, Finset.fold_insert hx, shuffleRec_nil, shufflePow_nil, ih, Finset.prod_insert hx]
  rw [shuffleProd_eq_fold]
  simpa using this Finset.univ

/-- Every shuffle-finite series in the semantic sense is shuffle-finite (the
    "finite-sem implies finite" direction of the coincidence).  Given
    `f = shuffleEval α k fs p` with `fs` closed under left derivatives, extend the tuple to
    `g = extTuple f k fs` (so `g 0 = f` and `g (Fin.succ i) = fs i`), show `g` is closed
    under left derivatives (the `g 0` slot via `leftDeriv_shuffleEval_deriv`, the `fs i`
    slots by the closure of `fs`), build an automaton `A` with `dim = k+1`, `F i = (g i) []`,
    and `Δ a i` the polynomial witnessing the closure of `g i`, and prove `A.sem p =
    shuffleEval α (k+1) g p` for all `p` by a word-length induction (the `cons` step uses
    `leftDeriv_shuffleEval_deriv`, since the letter maps are derivations, not ring
    endomorphisms).  Then `A.recognised = A.sem (X_0) = g 0 = f`. -/
private theorem shuffleRecognisable_of_finite (f : Series α)
    (hsem : IsShuffleFinite α f) : IsShuffleRecognisable α f := by
  obtain ⟨k, fs, p, hf, hclose⟩ := hsem
  let g := extTuple f k fs
  -- `g` is closed under left derivatives
  have hclose_g : ∀ (a : α) (j : Fin (k+1)),
      ∃ q, leftDeriv α a (g j) = shuffleEval α (k+1) g q := by
    intro a j
    by_cases h0 : j = 0
    · -- `j = 0`: `g 0 = f = shuffleEval α k fs p`
      let qf : Fin k → MvPolynomial (Fin k) ℚ := fun i => Classical.choose (hclose a i)
      have hqf : ∀ i, leftDeriv α a (fs i) = shuffleEval α k fs (qf i) := by
        intro i
        dsimp [qf]
        exact Classical.choose_spec (hclose a i)
      have hg0 : g 0 = f := by
        dsimp [g]
        rw [extTuple_zero]
      refine ⟨embedPoly k (derivationExt qf p), ?_⟩
      calc
        leftDeriv α a (g j) = leftDeriv α a (g 0) := by rw [h0]
        _ = leftDeriv α a f := by rw [hg0]
        _ = leftDeriv α a (shuffleEval α k fs p) := by rw [← hf]
        _ = shuffleEval α k fs (derivationExt qf p) := by
          rw [leftDeriv_shuffleEval_deriv k fs a qf hqf p]
        _ = shuffleEval α (k+1) g (embedPoly k (derivationExt qf p)) := by rw [shuffleEval_embed]
    · -- `j ≠ 0`: write `j = Fin.succ i` and use the closure of `fs i`
      have hj : j.val ≠ 0 := by
        intro hj0
        exact h0 (Fin.ext hj0)
      let i : Fin k := ⟨j.val - 1, by
        have := j.isLt
        omega⟩
      have hi : Fin.succ i = j := by
        apply Fin.ext
        simp [i]
        omega
      let qi := Classical.choose (hclose a i)
      have hqi : leftDeriv α a (fs i) = shuffleEval α k fs qi := by
        rw [show qi = Classical.choose (hclose a i) from rfl]
        exact Classical.choose_spec (hclose a i)
      have hgs : g (Fin.succ i) = fs i := by
        dsimp [g]
        rw [extTuple_succ]
      refine ⟨embedPoly k qi, ?_⟩
      calc
        leftDeriv α a (g j) = leftDeriv α a (g (Fin.succ i)) := by rw [← hi]
        _ = leftDeriv α a (fs i) := by rw [hgs]
        _ = shuffleEval α k fs qi := hqi
        _ = shuffleEval α (k+1) g (embedPoly k qi) := by rw [shuffleEval_embed]
  -- Choose the polynomials for the transition
  let Δ : α → Fin (k+1) → MvPolynomial (Fin (k+1)) ℚ :=
      fun a j => Classical.choose (hclose_g a j)
  have hΔ : ∀ (a : α) (j : Fin (k+1)),
      leftDeriv α a (g j) = shuffleEval α (k+1) g (Δ a j) := by
    intro a j
    rw [show Δ a j = Classical.choose (hclose_g a j) from rfl]
    exact Classical.choose_spec (hclose_g a j)
  -- Build the automaton
  let A : ShuffleAutomaton α :=
    { dim := k + 1,
      hdim := by omega,
      F := fun i => (g i) [],
      Δ := Δ }
  -- The semantics agrees with the shuffle evaluation in `g`, by a word-length induction
  have hsem : ∀ (w : List α) (p : MvPolynomial (Fin (k+1)) ℚ),
      A.sem p w = shuffleEval α (k+1) g p w := by
    intro w
    induction w with
    | nil =>
      intro p
      dsimp [ShuffleAutomaton.sem]
      rw [Mword_nil]
      simp only [id]
      dsimp [A]
      have hLHS : eval (fun i => (g i) []) p =
          ∑ m ∈ p.support, p.coeff m * ∏ i : Fin (k+1), (g i) [] ^ (m i) := by
        rw [MvPolynomial.eval_eq']
      have hRHS : shuffleEval α (k+1) g p [] =
          ∑ m ∈ p.support, p.coeff m * ∏ i : Fin (k+1), (g i) [] ^ (m i) := by
        rw [shuffleEval]
        have hsum : (∑ m ∈ p.support, p.coeff m • shuffleProd α (k+1) g m) [] =
            ∑ m ∈ p.support, p.coeff m * shuffleProd α (k+1) g m [] := by
          simp
        rw [hsum]
        apply Finset.sum_congr rfl
        intro m _
        rw [shuffleProd_nil]
      rw [hLHS, hRHS]
    | cons a w' ih =>
      intro p
      dsimp [ShuffleAutomaton.sem]
      rw [Mword_cons]
      change A.sem (derivationExt (A.Δ a) p) w' = _
      have h1 : A.sem (derivationExt (A.Δ a) p) w' =
          shuffleEval α (k+1) g (derivationExt (A.Δ a) p) w' := ih (derivationExt (A.Δ a) p)
      rw [h1]
      have h2 : shuffleEval α (k+1) g (derivationExt (A.Δ a) p) =
          leftDeriv α a (shuffleEval α (k+1) g p) := by
        rw [← leftDeriv_shuffleEval_deriv (k+1) g a (A.Δ a) (by intro i; exact hΔ a i) p]
      rw [h2]
      rfl
  -- `A.recognised = f`
  have hrec : A.recognised = f := by
    dsimp [ShuffleAutomaton.recognised]
    have hg0 : g 0 = f := by
      dsimp [g]
      rw [extTuple_zero]
    have hX0 : A.sem (MvPolynomial.X 0) = g 0 := by
      funext w
      simpa [shuffleEval_X] using hsem w (MvPolynomial.X 0)
    rw [hX0]
    exact hg0
  exact ⟨A, hrec⟩

/--
conclusion: Lax619925.Shuffle.ShuffleCoincidence
---
The shuffle coincidence theorem (paper §6): a series is shuffle-finite (a shuffle
polynomial in a finite tuple of series closed under the left derivatives) if and only
if it is recognised by a shuffle automaton.  The "finite implies recognisable"
direction extends the witnessing tuple by the series itself and builds the automaton
from the closure under left derivatives; the "recognisable implies finite" direction
reads off the generator tuple `A.sem (X_i)`, closed under left derivatives by the
derivation property. -/
theorem ShuffleCoincidence (f : Series α) :
    IsShuffleFinite α f ↔ IsShuffleRecognisable α f := by
  constructor
  · intro hfin
    exact shuffleRecognisable_of_finite f hfin
  · intro hrec
    exact shuffleFinite_of_recognisable f hrec

/-! ### The closure: combining witnessing tuples -/

/-- The witnessing tuple of `f` (size `k`) and `g` (size `k'`) concatenated: the first
    `k` slots are `fs`, the remaining `k'` slots are `fs'`. -/
noncomputable def combineTuple (k k' : ℕ) (fs : Fin k → Series α) (fs' : Fin k' → Series α) :
    Fin (k + k') → Series α :=
  fun i => if h : i.val < k then fs ⟨i.val, h⟩ else fs' ⟨i.val - k, by omega⟩

/-- Embedding a polynomial in `Fin k` into `Fin (k + k')`, keeping the variables
    `X_0, …, X_{k-1}` in place (the trailing slots are unused): `X_i ↦ X_i`. -/
noncomputable def embedFront (k k' : ℕ) (p : MvPolynomial (Fin k) ℚ) : MvPolynomial (Fin (k + k')) ℚ :=
  aeval (fun i : Fin k => MvPolynomial.X ⟨i.val, by omega⟩) p

/-- Embedding a polynomial in `Fin k'` into `Fin (k + k')`, shifted past the first `k`
    slots: `X_i ↦ X_{k + i}`. -/
noncomputable def embedBack (k k' : ℕ) (p : MvPolynomial (Fin k') ℚ) : MvPolynomial (Fin (k + k')) ℚ :=
  aeval (fun i : Fin k' => MvPolynomial.X ⟨k + i.val, by omega⟩) p

/-- A shuffle polynomial in `fs` is unchanged when the tuple is extended with `fs'` and
    the polynomial is embedded at the front: `shuffleEval α k fs p =
    shuffleEval α (k + k') (combineTuple k k' fs fs') (embedFront k k' p)`.  Both sides are
    shuffle-algebra homomorphisms sending `X_i` to `fs i`; the trailing slots of the extended
    tuple are unused by the embedded polynomial, so their values (`fs'`) are irrelevant. -/
private theorem shuffleEval_embedFront (k k' : ℕ) (fs : Fin k → Series α)
    (fs' : Fin k' → Series α) (p : MvPolynomial (Fin k) ℚ) :
    shuffleEval α k fs p = shuffleEval α (k + k') (combineTuple k k' fs fs') (embedFront k k' p) := by
  let aev : MvPolynomial (Fin k) ℚ →ₐ[ℚ] MvPolynomial (Fin (k + k')) ℚ :=
    MvPolynomial.aeval (fun i : Fin k => MvPolynomial.X ⟨i.val, by omega⟩)
  have hadd2 : ∀ p q, shuffleEval α (k + k') (combineTuple k k' fs fs') (embedFront k k' (p + q)) =
      shuffleEval α (k + k') (combineTuple k k' fs fs') (embedFront k k' p) +
        shuffleEval α (k + k') (combineTuple k k' fs fs') (embedFront k k' q) := by
    intro p q
    rw [embedFront, embedFront, embedFront]
    rw [map_add aev p q, shuffleEval_add]
  have hsmul2 : ∀ (c : ℚ) p, shuffleEval α (k + k') (combineTuple k k' fs fs') (embedFront k k' (c • p)) =
      c • shuffleEval α (k + k') (combineTuple k k' fs fs') (embedFront k k' p) := by
    intro c p
    rw [embedFront, embedFront]
    rw [map_smul aev c p, shuffleEval_smul]
  have hmul2 : ∀ p q, shuffleEval α (k + k') (combineTuple k k' fs fs') (embedFront k k' (p * q)) =
      shuffle α (shuffleEval α (k + k') (combineTuple k k' fs fs') (embedFront k k' p))
        (shuffleEval α (k + k') (combineTuple k k' fs fs') (embedFront k k' q)) := by
    intro p q
    rw [embedFront, embedFront, embedFront]
    rw [map_mul aev p q, shuffleEval_mul]
  have hone : shuffleEval α k fs 1 = shuffleEval α (k + k') (combineTuple k k' fs fs') (embedFront k k' 1) := by
    rw [shuffleEval_one, embedFront, map_one aev, shuffleEval_one]
  have hgen : ∀ i, shuffleEval α k fs (MvPolynomial.X i) =
      shuffleEval α (k + k') (combineTuple k k' fs fs') (embedFront k k' (MvPolynomial.X i)) := by
    intro i
    rw [shuffleEval_X, embedFront, MvPolynomial.aeval_X, shuffleEval_X]
    simp [combineTuple]
  exact shuffleHom_ext k
    (fun p => shuffleEval α k fs p)
    (fun p => shuffleEval α (k + k') (combineTuple k k' fs fs') (embedFront k k' p))
    (shuffleEval_add k fs) hadd2
    (shuffleEval_smul k fs) hsmul2
    (shuffleEval_mul k fs) hmul2
    hone hgen p

/-- The back-embedding analogue: `shuffleEval α k' fs' p =
    shuffleEval α (k + k') (combineTuple k k' fs fs') (embedBack k k' p)`. -/
private theorem shuffleEval_embedBack (k k' : ℕ) (fs : Fin k → Series α)
    (fs' : Fin k' → Series α) (p : MvPolynomial (Fin k') ℚ) :
    shuffleEval α k' fs' p = shuffleEval α (k + k') (combineTuple k k' fs fs') (embedBack k k' p) := by
  let aev : MvPolynomial (Fin k') ℚ →ₐ[ℚ] MvPolynomial (Fin (k + k')) ℚ :=
    MvPolynomial.aeval (fun i : Fin k' => MvPolynomial.X ⟨k + i.val, by omega⟩)
  have hadd2 : ∀ p q, shuffleEval α (k + k') (combineTuple k k' fs fs') (embedBack k k' (p + q)) =
      shuffleEval α (k + k') (combineTuple k k' fs fs') (embedBack k k' p) +
        shuffleEval α (k + k') (combineTuple k k' fs fs') (embedBack k k' q) := by
    intro p q
    rw [embedBack, embedBack, embedBack]
    rw [map_add aev p q, shuffleEval_add]
  have hsmul2 : ∀ (c : ℚ) p, shuffleEval α (k + k') (combineTuple k k' fs fs') (embedBack k k' (c • p)) =
      c • shuffleEval α (k + k') (combineTuple k k' fs fs') (embedBack k k' p) := by
    intro c p
    rw [embedBack, embedBack]
    rw [map_smul aev c p, shuffleEval_smul]
  have hmul2 : ∀ p q, shuffleEval α (k + k') (combineTuple k k' fs fs') (embedBack k k' (p * q)) =
      shuffle α (shuffleEval α (k + k') (combineTuple k k' fs fs') (embedBack k k' p))
        (shuffleEval α (k + k') (combineTuple k k' fs fs') (embedBack k k' q)) := by
    intro p q
    rw [embedBack, embedBack, embedBack]
    rw [map_mul aev p q, shuffleEval_mul]
  have hone : shuffleEval α k' fs' 1 = shuffleEval α (k + k') (combineTuple k k' fs fs') (embedBack k k' 1) := by
    rw [shuffleEval_one, embedBack, map_one aev, shuffleEval_one]
  have hgen : ∀ i, shuffleEval α k' fs' (MvPolynomial.X i) =
      shuffleEval α (k + k') (combineTuple k k' fs fs') (embedBack k k' (MvPolynomial.X i)) := by
    intro i
    rw [shuffleEval_X, embedBack, MvPolynomial.aeval_X, shuffleEval_X]
    simp [combineTuple]
  exact shuffleHom_ext k'
    (fun p => shuffleEval α k' fs' p)
    (fun p => shuffleEval α (k + k') (combineTuple k k' fs fs') (embedBack k k' p))
    (shuffleEval_add k' fs') hadd2
    (shuffleEval_smul k' fs') hsmul2
    (shuffleEval_mul k' fs') hmul2
    hone hgen p

/-- The concatenated tuple is closed under left derivatives, given that both summands are:
    the left derivative of a slot is the embedded left derivative of the corresponding
    summand slot. -/
private theorem combineTuple_closed (k k' : ℕ) (fs : Fin k → Series α) (fs' : Fin k' → Series α)
    (hfs : ∀ a (i : Fin k), ∃ q, leftDeriv α a (fs i) = shuffleEval α k fs q)
    (hfs' : ∀ a (i : Fin k'), ∃ q, leftDeriv α a (fs' i) = shuffleEval α k' fs' q) :
    ∀ a (i : Fin (k + k')), ∃ q,
      leftDeriv α a (combineTuple k k' fs fs' i) =
        shuffleEval α (k + k') (combineTuple k k' fs fs') q := by
  intro a i
  by_cases hlt : i.val < k
  · let j : Fin k := ⟨i.val, hlt⟩
    obtain ⟨q, hq⟩ := hfs a j
    refine ⟨embedFront k k' q, ?_⟩
    have hci : combineTuple k k' fs fs' i = fs j := by
      simp [combineTuple, j, hlt]
    rw [hci, hq, shuffleEval_embedFront]
  · let j : Fin k' := ⟨i.val - k, by omega⟩
    obtain ⟨q, hq⟩ := hfs' a j
    refine ⟨embedBack k k' q, ?_⟩
    have hci : combineTuple k k' fs fs' i = fs' j := by
      simp [combineTuple, j, hlt]
    rw [hci, hq, shuffleEval_embedBack]

/-! ### The right derivative of a shuffle polynomial -/

/-- The polynomial whose shuffle-evaluation in the extended tuple
    `combineTuple k k fs (fun i => rightDeriv a (fs i))` is the right derivative of
    `shuffleEval α k fs p`: for each monomial `m` of `p` and each index `i`, the summand is
    `p.coeff m • (m i) • (embedFront (monomial (m - e_i) 1) * embedBack (X i))`, which
    evaluates to `p.coeff m • (m i) • (shuffleProd (m - e_i) ⧢ rightDeriv a (fs i))`. -/
noncomputable def rightDerivPoly (k : ℕ) (fs : Fin k → Series α) (a : α)
    (p : MvPolynomial (Fin k) ℚ) : MvPolynomial (Fin (k + k)) ℚ :=
  p.support.sum fun m => p.coeff m • (∑ i : Fin k, (m i : ℚ) •
    (embedFront k k (MvPolynomial.monomial (m - Finsupp.single i 1) 1) * embedBack k k (MvPolynomial.X i)))

/-- The right derivative of a shuffle polynomial is a shuffle polynomial in the extended
    tuple `fs' = (fs, rightDeriv a fs)`: `rightDeriv α a (shuffleEval α k fs p) =
    shuffleEval α (k + k) fs' (rightDerivPoly k fs a p)`.  Both sides equal the sum
    `∑ m ∈ p.support, p.coeff m • rightDeriv a (shuffleProd k fs m)`: the LHS by `ℚ`-linearity
    of the right derivative, and the RHS by the product rule (`rightDeriv_shuffleProd`)
    together with the embedding lemmas. -/
private theorem rightDeriv_shuffleEval (k : ℕ) (fs : Fin k → Series α) (a : α)
    (p : MvPolynomial (Fin k) ℚ) :
    rightDeriv α a (shuffleEval α k fs p) =
      shuffleEval α (k + k) (combineTuple k k fs (fun i => rightDeriv α a (fs i)))
        (rightDerivPoly k fs a p) := by
  let fs' := combineTuple k k fs (fun i => rightDeriv α a (fs i))
  -- LHS: `rightDeriv a (shuffleEval k fs p) = ∑ m ∈ p.support, p.coeff m • rightDeriv a (shuffleProd k fs m)`
  have hLHS : rightDeriv α a (shuffleEval α k fs p) =
      ∑ m ∈ p.support, p.coeff m • rightDeriv α a (shuffleProd α k fs m) := by
    have hsum : rightDeriv α a (shuffleEval α k fs p) =
        rightDeriv α a (p.support.sum fun m => p.coeff m • shuffleProd α k fs m) := by
      rw [shuffleEval]
    rw [hsum]
    have hsum2 : rightDeriv α a (p.support.sum fun m => p.coeff m • shuffleProd α k fs m) =
        ∑ m ∈ p.support, p.coeff m • rightDeriv α a (shuffleProd α k fs m) := by
      have : ∀ (t : Finset (Fin k →₀ ℕ)) (g : (Fin k →₀ ℕ) → Series α),
          rightDeriv α a (∑ j ∈ t, g j) = ∑ j ∈ t, rightDeriv α a (g j) := by
        intro t g
        induction t using Finset.induction_on with
        | empty => simp [rightDeriv_zero]
        | insert x t hx ih' =>
            simp [Finset.sum_insert hx, ih', rightDeriv_add a]
      have hlin := this p.support (fun m => p.coeff m • shuffleProd α k fs m)
      rw [hlin]
      apply Finset.sum_congr rfl
      intro m _
      rw [rightDeriv_smul a]
    rw [hsum2]
  -- RHS: `shuffleEval (2k) fs' (rightDerivPoly k fs a p)`
  have hRHS : shuffleEval α (k + k) fs' (rightDerivPoly k fs a p) =
      ∑ m ∈ p.support, p.coeff m • rightDeriv α a (shuffleProd α k fs m) := by
    dsimp [rightDerivPoly]
    have hsum : shuffleEval α (k + k) fs' (p.support.sum fun m =>
        p.coeff m • (∑ i : Fin k, (m i : ℚ) •
          (embedFront k k (MvPolynomial.monomial (m - Finsupp.single i 1) 1) *
            embedBack k k (MvPolynomial.X i)))) =
        ∑ m ∈ p.support, p.coeff m • shuffleEval α (k + k) fs'
          (∑ i : Fin k, (m i : ℚ) •
            (embedFront k k (MvPolynomial.monomial (m - Finsupp.single i 1) 1) *
              embedBack k k (MvPolynomial.X i))) := by
      have : ∀ (t : Finset (Fin k →₀ ℕ)) (g : (Fin k →₀ ℕ) → MvPolynomial (Fin (k + k)) ℚ),
          shuffleEval α (k + k) fs' (∑ j ∈ t, g j) = ∑ j ∈ t, shuffleEval α (k + k) fs' (g j) := by
        intro t g
        induction t using Finset.induction_on with
        | empty => simp [shuffleEval_zero]
        | insert x t hx ih' =>
            simp [Finset.sum_insert hx, ih', shuffleEval_add]
      have hlin := this p.support (fun m =>
          p.coeff m • (∑ i : Fin k, (m i : ℚ) •
            (embedFront k k (MvPolynomial.monomial (m - Finsupp.single i 1) 1) *
              embedBack k k (MvPolynomial.X i))))
      rw [hlin]
      apply Finset.sum_congr rfl
      intro m _
      rw [shuffleEval_smul]
    rw [hsum]
    apply Finset.sum_congr rfl
    intro m _
    congr
    have hsum2 : shuffleEval α (k + k) fs'
        (∑ i : Fin k, (m i : ℚ) •
          (embedFront k k (MvPolynomial.monomial (m - Finsupp.single i 1) 1) *
            embedBack k k (MvPolynomial.X i))) =
        ∑ i : Fin k, (m i : ℚ) • shuffleEval α (k + k) fs'
          (embedFront k k (MvPolynomial.monomial (m - Finsupp.single i 1) 1) *
            embedBack k k (MvPolynomial.X i)) := by
      have : ∀ (t : Finset (Fin k)) (g : Fin k → MvPolynomial (Fin (k + k)) ℚ),
          shuffleEval α (k + k) fs' (∑ j ∈ t, g j) = ∑ j ∈ t, shuffleEval α (k + k) fs' (g j) := by
        intro t g
        induction t using Finset.induction_on with
        | empty => simp [shuffleEval_zero]
        | insert x t hx ih' =>
            simp [Finset.sum_insert hx, ih', shuffleEval_add]
      have hlin := this (Finset.univ : Finset (Fin k))
          (fun i => (m i : ℚ) •
            (embedFront k k (MvPolynomial.monomial (m - Finsupp.single i 1) 1) *
              embedBack k k (MvPolynomial.X i)))
      rw [hlin]
      apply Finset.sum_congr rfl
      intro i _
      rw [shuffleEval_smul]
    rw [hsum2, rightDeriv_shuffleProd]
    apply Finset.sum_congr rfl
    intro i _
    rw [shuffleEval_mul]
    have hfront : shuffleEval α (k + k) fs'
        (embedFront k k (MvPolynomial.monomial (m - Finsupp.single i 1) 1)) =
        shuffleEval α k fs (MvPolynomial.monomial (m - Finsupp.single i 1) 1) :=
      (shuffleEval_embedFront k k fs (fun i => rightDeriv α a (fs i))
        (MvPolynomial.monomial (m - Finsupp.single i 1) 1)).symm
    have hback : shuffleEval α (k + k) fs' (embedBack k k (MvPolynomial.X i)) =
        rightDeriv α a (fs i) := by
      rw [← shuffleEval_embedBack k k fs (fun i => rightDeriv α a (fs i)) (MvPolynomial.X i),
          shuffleEval_X]
    have hmono : shuffleEval α k fs (MvPolynomial.monomial (m - Finsupp.single i 1) 1) =
        shuffleProd α k fs (m - Finsupp.single i 1) := by
      rw [shuffleEval_monomial]
      simp
    rw [hfront, hback, hmono]
  rw [hLHS, hRHS]

/-! ### The semantic closure and the closure theorem -/

/-- The semantic class `IsShuffleFinite` is closed under addition, scalar multiplication,
    the shuffle product, and right derivatives.  The first three parts follow by concatenating
    the witnessing tuples (`combineTuple`/`embedFront`/`embedBack`); the right derivative is
    the extended tuple `(fs, rightDeriv a fs)` (the `rightDerivPoly` polynomial), which is
    closed under left derivatives by the commutativity of the left and right derivatives. -/
private theorem shuffleFiniteClosure :
    (∀ (f g : Series α), IsShuffleFinite α f → IsShuffleFinite α g → IsShuffleFinite α (f + g)) ∧
    (∀ (c : ℚ) (f : Series α), IsShuffleFinite α f → IsShuffleFinite α (c • f)) ∧
    (∀ (f g : Series α), IsShuffleFinite α f → IsShuffleFinite α g → IsShuffleFinite α (shuffle α f g)) ∧
    (∀ (a : α) (f : Series α), IsShuffleFinite α f → IsShuffleFinite α (rightDeriv α a f)) := by
  constructor
  · -- Addition
    intro f g hf hg
    obtain ⟨k, fs, p, hfp, hfc⟩ := hf
    obtain ⟨k', fs', p', hgp', hfc'⟩ := hg
    refine ⟨k + k', combineTuple k k' fs fs', embedFront k k' p + embedBack k k' p', ?_,
        combineTuple_closed k k' fs fs' hfc hfc'⟩
    calc
      f + g = shuffleEval α k fs p + shuffleEval α k' fs' p' := by rw [← hfp, ← hgp']
      _ = shuffleEval α (k + k') (combineTuple k k' fs fs') (embedFront k k' p) +
          shuffleEval α k' fs' p' := by
        rw [shuffleEval_embedFront k k' fs fs' p]
      _ = shuffleEval α (k + k') (combineTuple k k' fs fs') (embedFront k k' p) +
          shuffleEval α (k + k') (combineTuple k k' fs fs') (embedBack k k' p') := by
        rw [shuffleEval_embedBack k k' fs fs' p']
      _ = shuffleEval α (k + k') (combineTuple k k' fs fs')
          (embedFront k k' p + embedBack k k' p') := by
        simp [shuffleEval_add]
  · constructor
    · -- Scalar multiplication
      intro c f hf
      obtain ⟨k, fs, p, hfp, hfc⟩ := hf
      refine ⟨k, fs, c • p, ?_, hfc⟩
      calc
        c • f = c • shuffleEval α k fs p := by rw [← hfp]
        _ = shuffleEval α k fs (c • p) := by rw [shuffleEval_smul]
    · constructor
      · -- Shuffle product
        intro f g hf hg
        obtain ⟨k, fs, p, hfp, hfc⟩ := hf
        obtain ⟨k', fs', p', hgp', hfc'⟩ := hg
        refine ⟨k + k', combineTuple k k' fs fs', embedFront k k' p * embedBack k k' p', ?_,
            combineTuple_closed k k' fs fs' hfc hfc'⟩
        calc
          shuffle α f g = shuffle α (shuffleEval α k fs p) (shuffleEval α k' fs' p') := by
            rw [← hfp, ← hgp']
          _ = shuffle α (shuffleEval α (k + k') (combineTuple k k' fs fs') (embedFront k k' p))
              (shuffleEval α k' fs' p') := by
            rw [shuffleEval_embedFront k k' fs fs' p]
          _ = shuffle α (shuffleEval α (k + k') (combineTuple k k' fs fs') (embedFront k k' p))
              (shuffleEval α (k + k') (combineTuple k k' fs fs') (embedBack k k' p')) := by
            rw [shuffleEval_embedBack k k' fs fs' p']
          _ = shuffleEval α (k + k') (combineTuple k k' fs fs')
              (embedFront k k' p * embedBack k k' p') := by
            rw [shuffleEval_mul]
      · -- Right derivative
        intro a f hf
        obtain ⟨k, fs, p, hfp, hfc⟩ := hf
        let fs' := combineTuple k k fs (fun i => rightDeriv α a (fs i))
        refine ⟨k + k, fs', rightDerivPoly k fs a p, ?_, ?_⟩
        · -- `f = shuffleEval k fs p`, so `rightDeriv a f = rightDeriv a (shuffleEval k fs p)`
          calc
            rightDeriv α a f = rightDeriv α a (shuffleEval α k fs p) := by rw [← hfp]
            _ = shuffleEval α (k + k) fs' (rightDerivPoly k fs a p) :=
              rightDeriv_shuffleEval k fs a p
        · -- `fs'` is closed under left derivatives
          intro b j
          by_cases hlt : j.val < k
          · -- `j < k`: `fs' j = fs j`, and `leftDeriv b (fs j) = shuffleEval k fs q` (closure of `fs`)
            let i : Fin k := ⟨j.val, hlt⟩
            obtain ⟨q, hq⟩ := hfc b i
            refine ⟨embedFront k k q, ?_⟩
            have hci : fs' j = fs i := by
              simp [fs', combineTuple, hlt]
              congr
            rw [hci, hq, shuffleEval_embedFront]
          · -- `j ≥ k`: `fs' j = rightDeriv a (fs i)` for `i = j - k`.  The left derivative of a
            -- right derivative is the right derivative of the left derivative (commutativity),
            -- which is a shuffle polynomial by `rightDeriv_shuffleEval`.
            let i : Fin k := ⟨j.val - k, by omega⟩
            obtain ⟨q, hq⟩ := hfc b i
            refine ⟨rightDerivPoly k fs a q, ?_⟩
            have hci : fs' j = rightDeriv α a (fs i) := by
              simp [fs', combineTuple, hlt]
              congr
            rw [hci]
            have hcomm : leftDeriv α b (rightDeriv α a (fs i)) =
                rightDeriv α a (leftDeriv α b (fs i)) := by
              have := congrArg (fun h => h (fs i)) (LeftRightDerivativesCommute α b a)
              simp [Function.comp_apply] at this
              exact this
            rw [hcomm, hq, rightDeriv_shuffleEval]

/--
conclusion: Lax619925.Shuffle.ShuffleClosure
---
The shuffle closure theorem (paper §6): the shuffle-finite series are closed under
addition, scalar multiplication, the shuffle product, and right derivatives.  The proof
proceeds at the semantic level (shuffle polynomials in a tuple closed under left
derivatives), where the shuffle-algebra evaluation makes the first three parts immediate
and the right derivative is the extended tuple `(fs, rightDeriv a fs)`.
-/
theorem ShuffleClosure :
    (∀ (f g : Series α), IsShuffleFinite α f → IsShuffleFinite α g → IsShuffleFinite α (f + g)) ∧
    (∀ (c : ℚ) (f : Series α), IsShuffleFinite α f → IsShuffleFinite α (c • f)) ∧
    (∀ (f g : Series α), IsShuffleFinite α f → IsShuffleFinite α g → IsShuffleFinite α (shuffle α f g)) ∧
    (∀ (a : α) (f : Series α), IsShuffleFinite α f → IsShuffleFinite α (rightDeriv α a f)) :=
  @shuffleFiniteClosure α

/-! ### The anti-derivative closure -/

/-- Lifting a polynomial from a sub-index-set along a general index map `assign`:
    `liftPoly k k' assign p` is the polynomial in `Fin k` obtained by substituting
    `X_i ↦ X_{assign i}`.  (The generalisation of `embedFront`/`embedBack` to an arbitrary
    index map; used to express a shuffle polynomial in a sub-tuple as one in a larger tuple.) -/
noncomputable def liftPoly (k k' : ℕ) (assign : Fin k' → Fin k) (p : MvPolynomial (Fin k') ℚ) :
    MvPolynomial (Fin k) ℚ :=
  aeval (fun i : Fin k' => MvPolynomial.X (assign i)) p

/-- A shuffle polynomial in a sub-tuple `fs` is unchanged when the tuple is extended to `FS`
    (with `FS (assign i) = fs i`) and the polynomial is lifted by `assign`: `shuffleEval α k'
    fs p = shuffleEval α k FS (liftPoly k k' assign p)`.  Both sides are shuffle-algebra
    homomorphisms sending `X_i` to `fs i`, so they coincide by `shuffleHom_ext`.  (The shuffle
    analogue of the Hadamard `aeval`-based lifting: `shuffleEval` is a shuffle-algebra hom, not
    a pointwise `aeval`, so the equality is established by the homomorphism-extension lemma.) -/
private theorem shuffleEval_lift (k k' : ℕ) (FS : Fin k → Series α) (fs : Fin k' → Series α)
    (assign : Fin k' → Fin k) (hassign : ∀ i, FS (assign i) = fs i)
    (p : MvPolynomial (Fin k') ℚ) :
    shuffleEval α k' fs p = shuffleEval α k FS (liftPoly k k' assign p) := by
  let aev : MvPolynomial (Fin k') ℚ →ₐ[ℚ] MvPolynomial (Fin k) ℚ :=
    MvPolynomial.aeval (fun i : Fin k' => MvPolynomial.X (assign i))
  have hadd2 : ∀ p q, shuffleEval α k FS (liftPoly k k' assign (p + q)) =
      shuffleEval α k FS (liftPoly k k' assign p) + shuffleEval α k FS (liftPoly k k' assign q) := by
    intro p q
    rw [liftPoly, liftPoly, liftPoly]
    rw [map_add aev p q, shuffleEval_add]
  have hsmul2 : ∀ (c : ℚ) p, shuffleEval α k FS (liftPoly k k' assign (c • p)) =
      c • shuffleEval α k FS (liftPoly k k' assign p) := by
    intro c p
    rw [liftPoly, liftPoly]
    rw [map_smul aev c p, shuffleEval_smul]
  have hmul2 : ∀ p q, shuffleEval α k FS (liftPoly k k' assign (p * q)) =
      shuffle α (shuffleEval α k FS (liftPoly k k' assign p))
        (shuffleEval α k FS (liftPoly k k' assign q)) := by
    intro p q
    rw [liftPoly, liftPoly, liftPoly]
    rw [map_mul aev p q, shuffleEval_mul]
  have hone : shuffleEval α k' fs 1 = shuffleEval α k FS (liftPoly k k' assign 1) := by
    rw [shuffleEval_one, liftPoly, map_one aev, shuffleEval_one]
  have hgen : ∀ i, shuffleEval α k' fs (MvPolynomial.X i) =
      shuffleEval α k FS (liftPoly k k' assign (MvPolynomial.X i)) := by
    intro i
    rw [shuffleEval_X, liftPoly, MvPolynomial.aeval_X, shuffleEval_X]
    rw [hassign i]
  exact shuffleHom_ext k'
    (fun p => shuffleEval α k' fs p)
    (fun p => shuffleEval α k FS (liftPoly k k' assign p))
    (shuffleEval_add k' fs) hadd2
    (shuffleEval_smul k' fs) hsmul2
    (shuffleEval_mul k' fs) hmul2
    hone hgen p

/-- A package of the witnessing data for a shuffle-finite (semantic) series: the dimension
    `k`, the generator tuple `fs`, the polynomial `p`, and the proofs that
    `f = shuffleEval k fs p` and that `fs` is closed under left derivatives.  Packaged as a
    `Type` (not a `Prop`) so that `Classical.choose` can produce one witness per letter from a
    `∀ a, IsShuffleFinite …`. -/
structure ShuffleWitnessData (α : Type*) (f : Series α) where
  k : ℕ
  fs : Fin k → Series α
  p : MvPolynomial (Fin k) ℚ
  hfin : f = shuffleEval α k fs p
  hclose : ∀ a i, ∃ q, leftDeriv α a (fs i) = shuffleEval α k fs q

/-- `IsShuffleFinite α f` is the same as the existence of a `ShuffleWitnessData`. -/
private theorem ShuffleWitnessData_iff (f : Series α) :
    IsShuffleFinite α f ↔ ∃ _ : ShuffleWitnessData α f, True := by
  constructor
  · intro h
    obtain ⟨k, fs, p, hfp, hfc⟩ := h
    exact ⟨⟨k, fs, p, hfp, hfc⟩, by trivial⟩
  · intro h
    obtain ⟨⟨k, fs, p, hfp, hfc⟩, -⟩ := h
    exact ⟨k, fs, p, hfp, hfc⟩

/--
---
conclusion: Lax619925.Shuffle.ShuffleAntiDerivativeClosure
---
The shuffle anti-derivative closure (paper §6): over a finite alphabet, if `g` is a left
anti-derivative of a tuple `f` of shuffle-finite series (`leftDeriv a g = f a` for all `a`),
then `g` is shuffle-finite.  The witnessing tuple for `g` is `g` itself followed by the
concatenation of the witnessing tuples of the `f a`'s: `g` is trivially a shuffle polynomial
in a tuple containing it (its own variable), and the tuple is closed under left derivatives
because `leftDeriv a g = f a` is a shuffle polynomial in the (closed) witnessing tuple for
`f a`, and each `f a`'s witnessing tuple is itself closed.  The finiteness of the alphabet is
what makes the combined tuple finite.  The proof proceeds entirely at the semantic level
(shuffle polynomials in a tuple closed under left derivatives).
-/
theorem ShuffleAntiDerivativeClosure [Fintype α]
    (g : Series α) (f : α → Series α) (hantideriv : IsLeftAntiDerivative α g f)
    (hf : ∀ a, IsShuffleFinite α (f a)) : IsShuffleFinite α g := by
  have hsem_g : IsShuffleFinite α g := by
    let W : (a : α) → ShuffleWitnessData α (f a) :=
      fun a => Classical.choose ((ShuffleWitnessData_iff (f a)).mp (hf a))
    -- The non-`g` slots: one per element of each `W a .fs`, indexed by the pair `(a, j)`.
    let nonGslots : Finset (α × ℕ) :=
      Finset.biUnion Finset.univ (fun a => (Finset.range ((W a).k)).image (fun j => (a, j)))
    let M : ℕ := nonGslots.card
    let e : Fin M ≃ nonGslots := (Finset.equivFin nonGslots).symm
    -- The `Fin M` index of the non-`g` slot for a slot `i` is `i.val - 1`.  The `i.val ≠ 0`
    -- argument is required for totality: when `M = 0`, `i : Fin (1 + M) = Fin 1` forces
    -- `i.val = 0`, so the `i.val ≠ 0` premise is false and the function is vacuously defined.
    let idx : (i : Fin (1 + M)) → i.val ≠ 0 → Fin M :=
      fun i hne => ⟨i.val - 1, by
        by_cases hM : M = 0
        · exfalso
          have : i.val = 0 := by
            have : i.val < 1 := by simpa [hM] using i.isLt
            omega
          exact hne this
        · have hsub : i.val - 1 < i.val := by omega
          have hle : i.val ≤ M := by omega
          exact Nat.lt_of_lt_of_le hsub hle⟩
    -- The bound on the second component of `e j` (from its membership in `nonGslots`).
    let hj_of (j : Fin M) : (e j).1.2 < (W ((e j).1.1)).k := by
      let hmem := (e j).2
      dsimp [nonGslots] at hmem
      obtain ⟨b', hb', himg⟩ := Finset.mem_biUnion.mp hmem
      obtain ⟨j', hj', hpair⟩ := Finset.mem_image.mp himg
      have hb' : b' = (e j).1.1 := (Prod.ext_iff.mp hpair).1
      have hj'eq : j' = (e j).1.2 := (Prod.ext_iff.mp hpair).2
      rw [hb', hj'eq] at hj'
      exact Finset.mem_range.mp hj'
    -- The series held at the non-`g` slot for `Fin M` index `j`: the `((e j).1.2)`-th element
    -- of the witnessing tuple of `W ((e j).1.1)`.  The bound proof is inlined so that it
    -- elaborates to a concrete proof term that `rw`/`simp` can adjust via `Eq.ndrec`.
    let FSofJ (j : Fin M) : Series α :=
      (W ((e j).1.1)).fs ⟨(e j).1.2, by
        let hmem := (e j).2
        dsimp [nonGslots] at hmem
        obtain ⟨b', hb', himg⟩ := Finset.mem_biUnion.mp hmem
        obtain ⟨j', hj', hpair⟩ := Finset.mem_image.mp himg
        have hb' : b' = (e j).1.1 := (Prod.ext_iff.mp hpair).1
        have hj'eq : j' = (e j).1.2 := (Prod.ext_iff.mp hpair).2
        rw [hb', hj'eq] at hj'
        exact Finset.mem_range.mp hj'
      ⟩
    -- The combined tuple: slot 0 is `g`; slot `i` (`i.val ≥ 1`) is the non-`g` slot for
    -- `Fin M` index `idx i` (i.e. `i.val - 1`), an element of some `W b .fs`.
    let FS : Fin (1 + M) → Series α := fun i =>
      if h : i.val = 0 then g
      else FSofJ (idx i (by omega))
    -- `g` is a shuffle polynomial in `FS`: the variable of slot 0.
    have hfin_g : g = shuffleEval α (1 + M) FS (MvPolynomial.X ⟨0, by omega⟩) := by
      rw [shuffleEval_X]
      simp [FS]
    -- Membership of `(a, j)` in `nonGslots` (for `j < (W a).k`), as a named constant so that
    -- `slot_of` and the lemmas about it share the *same* term.
    have hmem_pair : (a : α) → (j : ℕ) → j < (W a).k → (a, j) ∈ nonGslots := by
      intro a j hj
      dsimp [nonGslots]
      exact Finset.mem_biUnion.mpr ⟨a, Finset.mem_univ a,
        Finset.mem_image_of_mem (fun j' => (a, j')) (Finset.mem_range.mpr hj)⟩
    -- The slot of `FS` holding `(W a).fs j` (for `j < (W a).k`): `1 +` the index of `(a, j)`.
    let slot_of (a : α) (j : ℕ) (hj : j < (W a).k) : Fin (1 + M) :=
      ⟨1 + (e.symm ⟨(a, j), hmem_pair a j hj⟩).val,
        by omega⟩
    -- A slot of `FS` holds the corresponding element of the witnessing tuple.
    have hFS_slot : ∀ (a : α) (j : ℕ) (hj : j < (W a).k), FS (slot_of a j hj) = (W a).fs ⟨j, hj⟩ := by
      intro a j hj
      by_cases hM : M = 0
      · exfalso
        have hmem : (a, j) ∈ nonGslots := hmem_pair a j hj
        have hpos : 0 < nonGslots.card := Finset.card_pos.mpr ⟨(a, j), hmem⟩
        have hzero : nonGslots.card = 0 := hM
        rw [hzero] at hpos
        omega
      · let x : nonGslots := ⟨(a, j), hmem_pair a j hj⟩
        let i := slot_of a j hj
        let hne : i.val ≠ 0 := by
          dsimp [i, slot_of, x]
          omega
        have he : e (idx i hne) = x := by
          have hval : (idx i hne).val = (e.symm x).val := by
            dsimp [idx, i, slot_of, x]
            omega
          rw [Fin.ext hval]
          exact Equiv.apply_symm_apply e x
        dsimp [FS]
        dsimp [i, slot_of, x] at he
        split_ifs with h
        · exfalso
          omega
        · dsimp [FSofJ]
          have he' : e (idx (slot_of a j hj) h) = x := by
            have hidx_eq : idx (slot_of a j hj) h = idx (slot_of a j hj) hne := by
              apply Fin.ext
              rfl
            dsimp [slot_of, x] at hidx_eq
            dsimp [slot_of, x]
            rw [← hidx_eq]
            exact he
          rw [he']
    -- `FS` is closed under left derivatives.
    have hclose_FS : ∀ (a : α) (i : Fin (1 + M)),
        ∃ q, leftDeriv α a (FS i) = shuffleEval α (1 + M) FS q := by
      intro a i
      by_cases h0 : i = 0
      · -- `i` is the `g` slot: `leftDeriv a g = f a`, a shuffle polynomial in `W a .fs`.
        let q : MvPolynomial (Fin (1 + M)) ℚ :=
          liftPoly (1 + M) (W a).k (fun j : Fin (W a).k => slot_of a j.val j.isLt) (W a).p
        refine ⟨q, ?_⟩
        have hFSg : FS i = g := by simp [FS, h0]
        rw [hFSg, hantideriv a, (W a).hfin]
        have hassign : ∀ (j : Fin (W a).k),
            FS ((fun j : Fin (W a).k => slot_of a j.val j.isLt) j) = (W a).fs j := by
          intro j
          dsimp
          rw [hFS_slot]
        dsimp only [q]
        exact shuffleEval_lift (1 + M) (W a).k FS (W a).fs
          (fun j : Fin (W a).k => slot_of a j.val j.isLt) hassign (W a).p
      · -- `i` is a non-`g` slot: `FS i = (W b).fs ⟨jnat, hj⟩`; its left derivative is a shuffle
        -- polynomial in `W b .fs` (closure of that witnessing tuple).
        have hval : i.val ≥ 1 := by
          have hne : i.val ≠ 0 := by
            intro h
            exact h0 (Fin.ext h)
          omega
        let j : Fin M := ⟨i.val - 1, by
          have hbound : i.val ≤ M := by omega
          omega⟩
        let b := (e j).1.1
        let jnat := (e j).1.2
        let hj : jnat < (W b).k := hj_of j
        have hi : i = slot_of b jnat hj := by
          apply Fin.ext
          dsimp [slot_of]
          have hsub : (⟨(b, jnat), by
              dsimp [nonGslots]
              exact Finset.mem_biUnion.mpr ⟨b, Finset.mem_univ b,
                Finset.mem_image_of_mem (fun j' => (b, j')) (Finset.mem_range.mpr hj)⟩⟩ : nonGslots) = e j := by
            apply Subtype.ext
            rfl
          rw [hsub, Equiv.symm_apply_apply]
          dsimp only [j]
          omega
        have hFSi : FS i = (W b).fs ⟨jnat, hj⟩ := by
          rw [hi]
          exact hFS_slot b jnat hj
        obtain ⟨q', hq'⟩ := (W b).hclose a ⟨jnat, hj⟩
        let q : MvPolynomial (Fin (1 + M)) ℚ :=
          liftPoly (1 + M) (W b).k (fun j' : Fin (W b).k => slot_of b j'.val j'.isLt) q'
        refine ⟨q, ?_⟩
        rw [hFSi, hq']
        have hassign : ∀ (j' : Fin (W b).k),
            FS ((fun j' : Fin (W b).k => slot_of b j'.val j'.isLt) j') = (W b).fs j' := by
          intro j'
          dsimp
          rw [hFS_slot]
        dsimp only [q]
        exact shuffleEval_lift (1 + M) (W b).k FS (W b).fs
          (fun j' : Fin (W b).k => slot_of b j'.val j'.isLt) hassign q'
    exact ⟨1 + M, FS, MvPolynomial.X ⟨0, by omega⟩, hfin_g, hclose_FS⟩
  exact hsem_g

/-! ### The orbit ideal chain (zeroness via Hilbert's basis theorem) -/

/-- The initial configuration `X_1` (the first nonterminal). -/
private noncomputable def X0 (A : ShuffleAutomaton α) : MvPolynomial (Fin A.dim) ℚ :=
  X (Fin.mk 0 A.hdim)

/-- The *cumulative orbit*: the configurations reachable from `X_1` by words of length `≤ n`.
    `orbitSet A 0 = {X_1}` and `orbitSet A (n+1) = orbitSet A n ∪ ⋃ₐ δₐ(orbitSet A n)`
    (append one letter to every reachable configuration).  Finite because the alphabet is.
    (As in the Hadamard case, the letter map is now the *derivation* `derivationExt (Δ a)`.) -/
noncomputable def orbitSet (A : ShuffleAutomaton α) [Fintype α] :
    ℕ → Finset (MvPolynomial (Fin A.dim) ℚ)
  | 0 => {X0 A}
  | n + 1 => orbitSet A n ∪ Finset.biUnion Finset.univ
      (fun a => (orbitSet A n).image (derivationExt (A.Δ a)))

/-- The *orbit ideal* `I_n`: the ideal generated by the configurations reachable from `X_1`
    by words of length `≤ n`. -/
noncomputable def orbitIdeal (A : ShuffleAutomaton α) [Fintype α] (n : ℕ) :
    Ideal (MvPolynomial (Fin A.dim) ℚ) :=
  Ideal.span (orbitSet A n)

/-- The orbit is cumulative: `orbitSet A n ⊆ orbitSet A (n+1)`. -/
private theorem orbitSet_mono (A : ShuffleAutomaton α) [Fintype α] (n : ℕ) :
    orbitSet A n ⊆ orbitSet A (n+1) := by
  dsimp [orbitSet]
  exact Finset.subset_union_left

/-- Appending a letter stays within the next orbit level:
    `δₐ(orbitSet A n) ⊆ orbitSet A (n+1)`. -/
private theorem orbitSet_image (A : ShuffleAutomaton α) [Fintype α] (a : α) (n : ℕ) :
    (orbitSet A n).image (derivationExt (A.Δ a)) ⊆ orbitSet A (n+1) := by
  dsimp [orbitSet]
  intro x hx
  apply Finset.mem_union_right
  rw [Finset.mem_biUnion]
  exact ⟨a, Finset.mem_univ a, hx⟩

/-- The orbit ideals form an ascending chain: `I_n ≤ I_{n+1}`. -/
private theorem orbitIdeal_mono (A : ShuffleAutomaton α) [Fintype α] (n : ℕ) :
    orbitIdeal A n ≤ orbitIdeal A (n+1) := by
  rw [orbitIdeal, orbitIdeal]
  exact Ideal.span_mono (orbitSet_mono A n)

/-- `derivationExt φ` is additive, hence commutes with a finite sum. -/
private theorem derivationExt_finset_sum {σ : Type*} [Fintype σ] {R : Type*} [CommRing R]
    (φ : σ → MvPolynomial σ R) (s : Finset (MvPolynomial σ R))
    (g : MvPolynomial σ R → MvPolynomial σ R) :
    derivationExt φ (∑ i ∈ s, g i) = ∑ i ∈ s, derivationExt φ (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [derivationExt_eq_mkDerivation]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, derivationExt_add, ih, Finset.sum_insert ha]

set_option maxHeartbeats 0

/-- The transition invariance: applying a letter-derivation to a configuration in the
    depth-`≤ n` orbit ideal lands in the depth-`≤ (n+1)` orbit ideal, `δₐ(I_n) ⊆ I_{n+1}`.
    Unlike the Hadamard case (a ring hom, so `Ideal.map_span`), a derivation is only `ℚ`-linear,
    not a ring hom.  So decompose `p` as a finite `R`-linear combination of orbit-set elements
    (`Submodule.mem_span_finset`; `Ideal R` is definitionally `Submodule R R`), apply the
    Leibniz rule termwise, and note that the two resulting sums lie in `I_n` and in the ideal
    generated by the derived orbit set, both of which are contained in `I_{n+1}`. -/
private theorem orbitIdeal_image (A : ShuffleAutomaton α) [Fintype α] (a : α) (n : ℕ)
    (p : MvPolynomial (Fin A.dim) ℚ) (hp : p ∈ orbitIdeal A n) :
    derivationExt (A.Δ a) p ∈ orbitIdeal A (n+1) := by
  let R := MvPolynomial (Fin A.dim) ℚ
  -- Decompose `p` as a finite `R`-linear combination of orbit-set elements.  (`Ideal R` is
  -- definitionally `Submodule R R`, so `orbitIdeal A n = Ideal.span … = Submodule.span R …`.)
  have hp' : p ∈ Submodule.span R (orbitSet A n) := by
    simpa [orbitIdeal] using hp
  obtain ⟨f, _, hf_sum⟩ := Submodule.mem_span_finset.mp hp'
  -- `p = ∑ z ∈ orbitSet A n, f z * z` (reindex to `z`, then the self-module `•` is `*`).
  have hf_sum' : p = ∑ z ∈ orbitSet A n, f z * z := by
    have hre : p = ∑ z ∈ orbitSet A n, f z • z := by
      rw [← hf_sum]
    rw [hre]
    simp [smul_eq_mul]
  -- The derivation commutes with the finite sum (additivity).
  have hsum : derivationExt (A.Δ a) p =
      ∑ z ∈ orbitSet A n, derivationExt (A.Δ a) (f z * z) := by
    rw [hf_sum', derivationExt_finset_sum (A.Δ a) (orbitSet A n) (fun z => f z * z)]
  -- Leibniz: `δ (f z * z) = δ (f z) * z + f z * δ z`.
  have hleib : ∀ z, derivationExt (A.Δ a) (f z * z) =
      derivationExt (A.Δ a) (f z) * z + f z * derivationExt (A.Δ a) z := by
    intro z
    rw [derivationExt_mul (A.Δ a) (f z) z]
  -- So `δ p` is the sum of two pieces.
  have hsplit : derivationExt (A.Δ a) p =
      (∑ z ∈ orbitSet A n, derivationExt (A.Δ a) (f z) * z) +
      (∑ z ∈ orbitSet A n, f z * derivationExt (A.Δ a) z) := by
    calc
      derivationExt (A.Δ a) p = ∑ z ∈ orbitSet A n, derivationExt (A.Δ a) (f z * z) := hsum
      _ = ∑ z ∈ orbitSet A n,
          (derivationExt (A.Δ a) (f z) * z + f z * derivationExt (A.Δ a) z) := by
        simp [hleib]
      _ = (∑ z ∈ orbitSet A n, derivationExt (A.Δ a) (f z) * z) +
          (∑ z ∈ orbitSet A n, f z * derivationExt (A.Δ a) z) :=
        Finset.sum_add_distrib
  -- First piece: `∑ δ (f z) * z` lies in `I_n` (an `R`-combination of orbit-set elements).
  have h1 : (∑ z ∈ orbitSet A n, derivationExt (A.Δ a) (f z) * z) ∈ orbitIdeal A n := by
    apply Submodule.sum_mem
    intro z hz
    have hz' : z ∈ ↑(Ideal.span ↑(orbitSet A n)) := Ideal.subset_span (Finset.mem_coe.mpr hz)
    exact Ideal.mul_mem_left (Ideal.span ↑(orbitSet A n)) (derivationExt (A.Δ a) (f z)) hz'
  -- Second piece: `∑ f z * δ z` lies in the ideal generated by the derived orbit set.
  have h2 : (∑ z ∈ orbitSet A n, f z * derivationExt (A.Δ a) z) ∈
      Ideal.span (derivationExt (A.Δ a) '' ↑(orbitSet A n)) := by
    apply Submodule.sum_mem
    intro z hz
    have himg : derivationExt (A.Δ a) z ∈ derivationExt (A.Δ a) '' ↑(orbitSet A n) :=
      Set.mem_image_of_mem (derivationExt (A.Δ a)) (Finset.mem_coe.mpr hz)
    have hspan : derivationExt (A.Δ a) z ∈
        ↑(Ideal.span (derivationExt (A.Δ a) '' ↑(orbitSet A n))) := Ideal.subset_span himg
    exact Ideal.mul_mem_left (Ideal.span (derivationExt (A.Δ a) '' ↑(orbitSet A n))) (f z) hspan
  -- Both are contained in `I_{n+1}`: `I_n ≤ I_{n+1}`, and
  -- `span (δ '' orbitSet A n) ≤ I_{n+1}` (the derived orbit set lands one level up).
  have hnext1 : orbitIdeal A n ≤ orbitIdeal A (n+1) := orbitIdeal_mono A n
  have hnext2 : Ideal.span (derivationExt (A.Δ a) '' ↑(orbitSet A n)) ≤ orbitIdeal A (n+1) := by
    rw [orbitIdeal]
    apply Ideal.span_mono
    rw [← Finset.coe_image]
    exact orbitSet_image A a n
  -- Hence `δ p ∈ I_{n+1}`.
  rw [hsplit]
  exact (orbitIdeal A (n+1)).add_mem (mem_of_le_of_mem hnext1 h1)
      (mem_of_le_of_mem hnext2 h2)

/-! ### The kernel of the final-weight functional -/

/-- The final-weight functional as a `ℚ`-algebra homomorphism:
    `F_hom A p = aeval (A.F) p = eval (A.F) p`, the evaluation of the configuration
    `p` at the point `(A.F 0, …, A.F (dim-1))`.  (Unchanged from the Hadamard case:
    the final-weight evaluation is a point evaluation, independent of the automaton class.) -/
noncomputable def F_hom (A : ShuffleAutomaton α) :
    MvPolynomial (Fin A.dim) ℚ →ₐ[ℚ] ℚ :=
  aeval (A.F)

/-- The kernel of the final-weight functional: the ideal of configurations that
    evaluate to `0` under `F`. -/
noncomputable def K (A : ShuffleAutomaton α) : Ideal (MvPolynomial (Fin A.dim) ℚ) :=
  RingHom.ker (F_hom A)

/-- A configuration lies in the kernel iff it evaluates to `0`:
    `p ∈ K A ↔ eval (A.F) p = 0`. -/
private theorem kerMem_eval (A : ShuffleAutomaton α) (p : MvPolynomial (Fin A.dim) ℚ) :
    p ∈ K A ↔ eval (A.F) p = 0 := by
  rw [K, F_hom, RingHom.mem_ker]
  simp [aeval_eq_eval]

/-! ### Stabilisation of the orbit-ideal chain (Hilbert's basis theorem) -/

/-- The configuration ring is Noetherian: a polynomial ring over a Noetherian ring in
    finitely many variables is Noetherian (`isNoetherianRing_fin`), and `ℚ` is a field,
    hence Noetherian. -/
private theorem noetherian (A : ShuffleAutomaton α) :
    IsNoetherianRing (MvPolynomial (Fin A.dim) ℚ) :=
  isNoetherianRing_fin

/-- The orbit ideals form a monotone (ascending) chain. -/
private theorem orbitIdeal_monotone (A : ShuffleAutomaton α) [Fintype α] :
    Monotone (fun n => orbitIdeal A n) := by
  intro a b hab
  exact Nat.le_induction (le_rfl) (fun n _ hn => le_trans hn (orbitIdeal_mono A n)) b hab

/-- The orbit-ideal chain stabilises (Noetherianity): there is an `N` such that
    `I_N = I_m` for all `m ≥ N`. -/
private theorem orbitIdeal_stabilises (A : ShuffleAutomaton α) [Fintype α] :
    ∃ N, ∀ m, N ≤ m → orbitIdeal A N = orbitIdeal A m := by
  let R := MvPolynomial (Fin A.dim) ℚ
  obtain ⟨N, hN⟩ :=
    monotone_stabilizes_iff_noetherian.mpr (isNoetherianRing_iff.mp (noetherian A))
      (⟨fun n => orbitIdeal A n, orbitIdeal_monotone A⟩)
  exact ⟨N, fun m hm => hN m hm⟩

/-- A stabilisation point of the orbit-ideal chain. -/
noncomputable def orbitIdeal_stab (A : ShuffleAutomaton α) [Fintype α] : ℕ :=
  Classical.choose (orbitIdeal_stabilises A)

/-- At the stabilisation point the chain is constant: `I_N = I_m` for all `m ≥ N`. -/
private theorem orbitIdeal_stab_spec (A : ShuffleAutomaton α) [Fintype α] :
    ∀ m, orbitIdeal_stab A ≤ m → orbitIdeal A (orbitIdeal_stab A) = orbitIdeal A m :=
  Classical.choose_spec (orbitIdeal_stabilises A)

/-! ### The stabilised orbit ideal is a bi-ideal -/

/-- The initial configuration lies in the orbit ideal at every level. -/
private theorem X0_in_orbitSet (A : ShuffleAutomaton α) [Fintype α] (n : ℕ) :
    X0 A ∈ orbitSet A n := by
  induction n with
  | zero =>
      dsimp [orbitSet]
      simp
  | succ n ih =>
      dsimp [orbitSet]
      exact Finset.mem_union_left _ ih

/-- The initial configuration lies in the stabilised orbit ideal. -/
private theorem X0_in_orbitIdeal (A : ShuffleAutomaton α) [Fintype α] :
    X0 A ∈ orbitIdeal A (orbitIdeal_stab A) := by
  rw [orbitIdeal]
  have h : X0 A ∈ ↑(orbitSet A (orbitIdeal_stab A)) := by
    simpa using X0_in_orbitSet A (orbitIdeal_stab A)
  exact Submodule.subset_span h

/-- The stabilised orbit ideal is invariant under every letter transition
    (`δₐ(I_N) ⊆ I_N`): the image lands one level up (`orbitIdeal_image`), which
    equals `I_N` at the stabilisation point. -/
private theorem orbitIdeal_stab_invariant (A : ShuffleAutomaton α) [Fintype α]
    (a : α) (p : MvPolynomial (Fin A.dim) ℚ) (hp : p ∈ orbitIdeal A (orbitIdeal_stab A)) :
    derivationExt (A.Δ a) p ∈ orbitIdeal A (orbitIdeal_stab A) := by
  have h1 : derivationExt (A.Δ a) p ∈ orbitIdeal A (orbitIdeal_stab A + 1) :=
    orbitIdeal_image A a (orbitIdeal_stab A) p hp
  have h2 : orbitIdeal A (orbitIdeal_stab A + 1) = orbitIdeal A (orbitIdeal_stab A) :=
    (orbitIdeal_stab_spec A (orbitIdeal_stab A + 1) (Nat.le_succ (orbitIdeal_stab A))).symm
  rw [← h2]
  exact h1

/-- `Mword [a] = derivationExt (Δ a)`: a single letter applies its derivation. -/
private theorem Mword_singleton (A : ShuffleAutomaton α) (a : α) :
    A.Mword [a] = derivationExt (A.Δ a) := by
  rw [Mword_cons, Mword_nil]
  simp

/-- The word endomorphism preserves the stabilised orbit ideal: if `p` is in the
    ideal, so is `Δ_w p`.  Each letter derivation preserves the ideal
    (`orbitIdeal_stab_invariant`), and the word map composes them. -/
private theorem Mword_preserves_orbitIdeal (A : ShuffleAutomaton α) [Fintype α] (w : List α) :
    ∀ p, p ∈ orbitIdeal A (orbitIdeal_stab A) → A.Mword w p ∈ orbitIdeal A (orbitIdeal_stab A) := by
  induction w with
  | nil =>
      intro p hp
      rw [Mword_nil]
      exact hp
  | cons a w ih =>
      intro p hp
      rw [Mword_cons, Function.comp_apply]
      have h1 : derivationExt (A.Δ a) p ∈ orbitIdeal A (orbitIdeal_stab A) :=
        orbitIdeal_stab_invariant A a p hp
      exact ih (derivationExt (A.Δ a) p) h1

/-- Every reachable configuration lies in the stabilised orbit ideal: the word map
    preserves the ideal and `X_1` is in it. -/
private theorem Mword_mem_orbitIdeal (A : ShuffleAutomaton α) [Fintype α] (w : List α) :
    A.Mword w (X0 A) ∈ orbitIdeal A (orbitIdeal_stab A) :=
  Mword_preserves_orbitIdeal A w (X0 A) (X0_in_orbitIdeal A)

/-! ### The orbit set is reachable, and the zeroness characterisation -/

/-- Every configuration in the depth-`≤ n` orbit set is reachable from `X_1` by some
    word: `p ∈ orbitSet A n → ∃ w, p = Δ_w X_1`. -/
private theorem orbitSet_reachable (A : ShuffleAutomaton α) [Fintype α] (n : ℕ) :
    ∀ p, p ∈ orbitSet A n → ∃ w : List α, p = A.Mword w (X0 A) := by
  induction n with
  | zero =>
      intro p hp
      dsimp [orbitSet] at hp
      have hp' : p = X0 A := by simpa using hp
      exact ⟨[], by rw [hp', Mword_nil]; rfl⟩
  | succ n ih =>
      intro p hp
      dsimp [orbitSet] at hp
      rw [Finset.mem_union] at hp
      rcases hp with hleft | hright
      · obtain ⟨w, hw⟩ := ih p hleft
        exact ⟨w, hw⟩
      · simp only [Finset.mem_biUnion] at hright
        obtain ⟨a, _, himg⟩ := hright
        simp only [Finset.mem_image] at himg
        obtain ⟨q, hq, hqimg⟩ := himg
        obtain ⟨w, hw⟩ := ih q hq
        exact ⟨w ++ [a], by
          rw [← hqimg, hw, Mword_append, Mword_singleton, Function.comp_apply]⟩

/-- The recognised series is zero iff every reachable configuration lies in the kernel:
    `A.recognised = 0 ↔ ∀ w, Δ_w X_1 ∈ K A`.  The coefficient of `w` in the recognised
    series is `F(Δ_w X_1)`, which is `0` exactly when `Δ_w X_1` is in the kernel. -/
private theorem recognised_zero_iff_allInK (A : ShuffleAutomaton α) :
    A.recognised = 0 ↔ ∀ w, A.Mword w (X0 A) ∈ K A := by
  constructor
  · intro h w
    have hw : A.recognised w = 0 := by
      rw [h]
      simp
    have hsem : A.recognised w = eval (A.F) (A.Mword w (X0 A)) := by
      simp [ShuffleAutomaton.recognised, ShuffleAutomaton.sem, X0]
    rw [hsem] at hw
    rw [kerMem_eval A (A.Mword w (X0 A))]
    exact hw
  · intro h
    funext w
    change eval (A.F) (A.Mword w (X0 A)) = 0
    rw [← kerMem_eval A (A.Mword w (X0 A))]
    exact h w

/-- The zeroness characterisation at the stabilisation point:
    `A.recognised = 0 ↔ ∀ p ∈ orbitSet A N, p ∈ K A`, where `N` is a stabilisation
    point.  (→) Every orbit-set configuration is reachable, hence in the kernel.
    (←) Every reachable configuration is in the stabilised orbit ideal (the bi-ideal
    property), which is contained in the kernel once the orbit-set configurations are. -/
private theorem zeroness_iff_orbitSet (A : ShuffleAutomaton α) [Fintype α] :
    A.recognised = 0 ↔ ∀ p ∈ orbitSet A (orbitIdeal_stab A), p ∈ K A := by
  let N := orbitIdeal_stab A
  have hchar : A.recognised = 0 ↔ ∀ w, A.Mword w (X0 A) ∈ K A := recognised_zero_iff_allInK A
  constructor
  · intro h
    have hall := hchar.mp h
    intro p hp
    obtain ⟨w, hw⟩ := orbitSet_reachable A N p hp
    rw [hw]
    exact hall w
  · intro h
    apply hchar.mpr
    intro w
    have hmem : A.Mword w (X0 A) ∈ orbitIdeal A N := Mword_mem_orbitIdeal A w
    have hsub : orbitIdeal A N ≤ K A := by
      rw [orbitIdeal]
      exact Ideal.span_le.mpr h
    exact mem_of_le_of_mem hsub hmem

/-! ### The equality (zeroness) decision, reduced to the open leaf -/

/-- A finite generating set of the kernel `K A` (exists by Noetherianity). -/
noncomputable def gensKer (A : ShuffleAutomaton α) : Finset (MvPolynomial (Fin A.dim) ℚ) :=
  letI _ : IsNoetherianRing (MvPolynomial (Fin A.dim) ℚ) := noetherian A
  Classical.choose (Ideal.fg_of_isNoetherianRing (K A))

/-- The kernel is exactly the ideal generated by `gensKer A`. -/
private theorem gensKer_spec (A : ShuffleAutomaton α) :
    Ideal.span ↑(gensKer A) = K A := by
  letI _ : IsNoetherianRing (MvPolynomial (Fin A.dim) ℚ) := noetherian A
  exact Classical.choose_spec (Ideal.fg_of_isNoetherianRing (K A))

/-- A `Finset`-fold with `&&` (the Boolean "and") starting from `true` is `true`
    exactly when every element satisfies the predicate:
    `s.fold (· && ·) true p = true ↔ ∀ x ∈ s, p x = true`. -/
private theorem fold_and_true {β : Type*} (s : Finset β) (p : β → Bool) :
    s.fold (· && ·) true p = true ↔ ∀ x ∈ s, p x = true := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.fold_insert ha, Bool.and_eq_true_iff, ih]
      simp [Finset.mem_insert]

/-- The per-configuration decision procedure, extracted from the open leaf
    `IdealMembershipDecidable` (which asserts that a correct `Bool`-valued
    decision exists for the ideal `span ↑(gensKer A)`): `orbitDec A p` is
    `true` exactly when `p` lies in the ideal generated by `gensKer A`. -/
private noncomputable def orbitDec (A : ShuffleAutomaton α) : MvPolynomial (Fin A.dim) ℚ → Bool :=
  Classical.choose (IdealMembershipDecidable A.dim (gensKer A))

/-- `orbitDec A p = true ↔ p ∈ K A`: the leaf's decision procedure is correct
    (`Classical.choose_spec`), so `orbitDec A p = true ↔ p ∈ span ↑(gensKer A)`,
    which is exactly the kernel `K A` (`gensKer_spec`). -/
private theorem orbitDec_iff (A : ShuffleAutomaton α) (p : MvPolynomial (Fin A.dim) ℚ) :
    orbitDec A p = true ↔ p ∈ K A := by
  dsimp [orbitDec]
  rw [Classical.choose_spec (IdealMembershipDecidable A.dim (gensKer A)) p, ← gensKer_spec A]

/--
---
conclusion: Lax619925.Shuffle.ShuffleEqualityDecidable
---
The equality (zeroness) problem is decidable for shuffle automata over a finite
alphabet (paper §6).  As in the Hadamard case, the orbit-ideal chain `I_n`
stabilises by Hilbert's basis theorem (`orbitIdeal_stabilises`), and the stabilised
ideal is a bi-ideal, so the zeroness of the recognised series is characterised by
the finite statement `∀ p ∈ orbitSet A N, p ∈ K A` (`zeroness_iff_orbitSet`).  The
only difference from the Hadamard case is the transition invariance
(`orbitIdeal_image`): the letter map is a *derivation* (ℚ-linear, not a ring hom),
so instead of `Ideal.map_span` one decomposes `p` as a finite `R`-linear combination
of orbit-set elements and applies the Leibniz rule termwise.  The kernel `K A` is
finitely generated (`gensKer`, by Noetherianity), so this finite statement is a
batch of ideal-membership queries `p ∈ span ↑(gensKer A)`, each decided by the open
leaf `IdealMembershipDecidable`; the decision `d` is the Boolean "and" of these
queries over the (finite) orbit set.
-/
theorem ShuffleEqualityDecidable [Fintype α] :
    ∃ d : ShuffleAutomaton α → Bool, ∀ A, d A = true ↔ A.recognised = 0 := by
  let d : ShuffleAutomaton α → Bool := fun A =>
    (orbitSet A (orbitIdeal_stab A)).fold (· && ·) true (orbitDec A)
  refine ⟨d, ?_⟩
  intro A
  let N := orbitIdeal_stab A
  have hfor : d A = true ↔ ∀ p ∈ orbitSet A N, p ∈ K A := by
    dsimp [d]
    rw [fold_and_true]
    constructor
    · intro h p hp
      have this := h p hp
      rw [orbitDec_iff A p] at this
      exact this
    · intro h p hp
      have this := h p hp
      rw [orbitDec_iff A p]
      exact this
  have hzer : (∀ p ∈ orbitSet A N, p ∈ K A) ↔ A.recognised = 0 :=
    (zeroness_iff_orbitSet A).symm
  calc
    d A = true ↔ ∀ p ∈ orbitSet A N, p ∈ K A := hfor
    _ ↔ A.recognised = 0 := hzer

/-! ### The effective prevariety of shuffle-finite series -/

/-- The derivation of the constant `0` is `0`: `derivationExt φ 0 = 0` (it is
    `MvPolynomial.mkDerivation`, a linear map, hence it preserves `0`). -/
private theorem derivationExt_zero {σ : Type*} [Fintype σ] {R : Type*} [CommRing R]
    (φ : σ → MvPolynomial σ R) : derivationExt φ 0 = 0 := by
  rw [derivationExt_eq_mkDerivation]
  exact (MvPolynomial.mkDerivation R φ).map_zero

/-- The word map sends `0` to `0`: `A.Mword w 0 = 0` for every word `w` (each letter
    map is a derivation, hence preserves `0`, and a composition of such maps does too). -/
private theorem Mword_zero (A : ShuffleAutomaton α) (w : List α) : A.Mword w 0 = 0 := by
  induction w with
  | nil => simp [Mword_nil]
  | cons a w' ih => rw [Mword_cons, Function.comp_apply, derivationExt_zero, ih]

/-- The left derivative of a shuffle-finite (semantic) series is shuffle-finite (semantic):
    the witnessing tuple is unchanged, and the polynomial is pre-composed with the
    left-derivative polynomials of the generators (`leftDeriv_shuffleEval_deriv`, with the
    letter map a *derivation* — the shuffle analogue of `leftDeriv_hadamardFinite`). -/
private theorem leftDeriv_shuffleFiniteSem (f : Series α) (hfsem : IsShuffleFinite α f) (a : α) :
    IsShuffleFinite α (leftDeriv α a f) := by
  obtain ⟨k, fs, p, hfp, hfc⟩ := hfsem
  let q : Fin k → MvPolynomial (Fin k) ℚ := fun i => Classical.choose (hfc a i)
  have hq : ∀ i, leftDeriv α a (fs i) = shuffleEval α k fs (q i) := by
    intro i
    dsimp [q]
    exact Classical.choose_spec (hfc a i)
  refine ⟨k, fs, derivationExt q p, ?_, hfc⟩
  calc
    leftDeriv α a f = leftDeriv α a (shuffleEval α k fs p) := by rw [← hfp]
    _ = shuffleEval α k fs (derivationExt q p) := by rw [leftDeriv_shuffleEval_deriv k fs a q hq p]

/-- `A.recognised` is shuffle-finite (by the coincidence, from recognisability). -/
private theorem recognised_shuffleFinite (A : ShuffleAutomaton α) :
    IsShuffleFinite α A.recognised :=
  shuffleFinite_of_recognisable _ ⟨A, rfl⟩

/-- The top prevariety: the whole space of series, trivially closed under the
    derivatives.  Serves as the `prevariety` field of the shuffle effective
    prevariety (the image of the semantics is a prevariety; the top space is the
    coarsest such). -/
private def topPrevariety (α : Type*) : Prevariety α :=
  { carrier := ⊤,
    closedLeftDeriv := fun _ _ => Submodule.mem_top,
    closedRightDeriv := fun _ _ => Submodule.mem_top }

/-- A shuffle automaton recognising the zero series: one nonterminal, zero final
    weight, and zero transitions (the configuration is `0` after any non-empty word,
    and the empty word evaluates to `F 0 = 0`).  Takes `α` explicitly so that the
    projection `zeroAutomaton α .recognised` elaborates. -/
noncomputable def zeroAutomaton (α : Type*) : ShuffleAutomaton α :=
  { dim := 1,
    hdim := by decide,
    F := fun _ => 0,
    Δ := fun _ _ => 0 }

/-- `zeroAutomaton` recognises the zero series. -/
private theorem zeroAutomaton_recognised :
    (zeroAutomaton α).recognised = 0 := by
  funext w
  induction w with
  | nil =>
      dsimp [ShuffleAutomaton.recognised, ShuffleAutomaton.sem, zeroAutomaton]
      rw [Mword_nil]
      simp
  | cons a w' =>
      dsimp [ShuffleAutomaton.recognised, ShuffleAutomaton.sem]
      rw [Mword_cons]
      simp only [Function.comp_apply]
      have h : derivationExt ((zeroAutomaton α).Δ a) (MvPolynomial.X (Fin.mk 0 (zeroAutomaton α).hdim)) = 0 := by
        rw [derivationExt_X]
        dsimp [zeroAutomaton]
        rfl
      rw [h, Mword_zero (zeroAutomaton α) w']
      simp

/-- The sum of two recognised series is shuffle-recognisable. -/
private theorem addRecognisable (A B : ShuffleAutomaton α) :
    IsShuffleRecognisable α (A.recognised + B.recognised) :=
  (ShuffleCoincidence _).mp
    (ShuffleClosure.1 _ _ (recognised_shuffleFinite A) (recognised_shuffleFinite B))

/-- The scalar multiple of a recognised series is shuffle-recognisable. -/
private theorem smulRecognisable (c : ℚ) (A : ShuffleAutomaton α) :
    IsShuffleRecognisable α (c • A.recognised) :=
  (ShuffleCoincidence _).mp
    (ShuffleClosure.2.1 _ _ (recognised_shuffleFinite A))

/-- The left derivative of a recognised series is shuffle-recognisable. -/
private theorem derivLRecognisable (a : α) (A : ShuffleAutomaton α) :
    IsShuffleRecognisable α (leftDeriv α a A.recognised) :=
  (ShuffleCoincidence _).mp
    (leftDeriv_shuffleFiniteSem _ (recognised_shuffleFinite A) a)

/-- The right derivative of a recognised series is shuffle-recognisable. -/
private theorem derivRRecognisable (a : α) (A : ShuffleAutomaton α) :
    IsShuffleRecognisable α (rightDeriv α a A.recognised) :=
  (ShuffleCoincidence _).mp
    (ShuffleClosure.2.2.2 _ _ (recognised_shuffleFinite A))

/-- The sum automaton: recognises `A.recognised + B.recognised`. -/
noncomputable def addAutomaton (A B : ShuffleAutomaton α) : ShuffleAutomaton α :=
  Classical.choose (addRecognisable A B)

/-- The scalar-multiple automaton: recognises `c • A.recognised`. -/
noncomputable def smulAutomaton (c : ℚ) (A : ShuffleAutomaton α) : ShuffleAutomaton α :=
  Classical.choose (smulRecognisable c A)

/-- The left-derivative automaton: recognises `leftDeriv a (A.recognised)`. -/
noncomputable def derivLAutomaton (a : α) (A : ShuffleAutomaton α) : ShuffleAutomaton α :=
  Classical.choose (derivLRecognisable a A)

/-- The right-derivative automaton: recognises `rightDeriv a (A.recognised)`. -/
noncomputable def derivRAutomaton (a : α) (A : ShuffleAutomaton α) : ShuffleAutomaton α :=
  Classical.choose (derivRRecognisable a A)

private theorem addAutomaton_spec (A B : ShuffleAutomaton α) :
    (addAutomaton A B).recognised = A.recognised + B.recognised := by
  dsimp [addAutomaton]
  exact Classical.choose_spec (addRecognisable A B)

private theorem smulAutomaton_spec (c : ℚ) (A : ShuffleAutomaton α) :
    (smulAutomaton c A).recognised = c • A.recognised := by
  dsimp [smulAutomaton]
  exact Classical.choose_spec (smulRecognisable c A)

private theorem derivLAutomaton_spec (a : α) (A : ShuffleAutomaton α) :
    (derivLAutomaton a A).recognised = leftDeriv α a A.recognised := by
  dsimp [derivLAutomaton]
  exact Classical.choose_spec (derivLRecognisable a A)

private theorem derivRAutomaton_spec (a : α) (A : ShuffleAutomaton α) :
    (derivRAutomaton a A).recognised = rightDeriv α a A.recognised := by
  dsimp [derivRAutomaton]
  exact Classical.choose_spec (derivRRecognisable a A)

/-- The effective prevariety of shuffle-finite series: presentations are shuffle
    automata, the semantics is the recognised series, and the operations are carried
    out by the (classically chosen) closure automata.  Equality is decided by the
    zeroness decision applied to `A - B` (`ShuffleEqualityDecidable`). -/
noncomputable def shuffleEffectivePrevariety [Fintype α] : EffectivePrevariety α :=
  { Rep := ShuffleAutomaton α,
    sem := fun A => A.recognised,
    prevariety := topPrevariety α,
    mem := fun A => by
      change A.recognised ∈ (⊤ : Submodule ℚ (Series α))
      exact Submodule.mem_top
    zero := zeroAutomaton α,
    add := addAutomaton,
    smul := smulAutomaton,
    derivL := derivLAutomaton,
    derivR := derivRAutomaton,
    sem_zero := by
      change (zeroAutomaton α).recognised = 0
      exact zeroAutomaton_recognised
    sem_add := fun A B => by
      change (addAutomaton A B).recognised = A.recognised + B.recognised
      exact addAutomaton_spec A B
    sem_smul := fun c A => by
      change (smulAutomaton c A).recognised = c • A.recognised
      exact smulAutomaton_spec c A
    sem_derivL := fun a A => by
      change (derivLAutomaton a A).recognised = leftDeriv α a (A.recognised)
      exact derivLAutomaton_spec a A
    sem_derivR := fun a A => by
      change (derivRAutomaton a A).recognised = rightDeriv α a (A.recognised)
      exact derivRAutomaton_spec a A
    decEq := fun A B => by
      let d := Classical.choose (ShuffleEqualityDecidable (α := α))
      let hd := Classical.choose_spec (ShuffleEqualityDecidable (α := α))
      let C := addAutomaton A (smulAutomaton (-1) B)
      have hc : C.recognised = A.recognised - B.recognised := by
        dsimp [C]
        rw [addAutomaton_spec, smulAutomaton_spec]
        simp [sub_eq_add_neg]
      have hdC : d C = true ↔ C.recognised = 0 := hd C
      have hsub : C.recognised = 0 ↔ A.recognised = B.recognised := by
        rw [hc, sub_eq_zero]
      have h : d C = true ↔ A.recognised = B.recognised := hdC.trans hsub
      let decP : Decidable (d C = true) := inferInstance
      exact match decP with
        | .isTrue ht => .isTrue (h.mp ht)
        | .isFalse hf => .isFalse fun x => hf (h.mpr x) }

/--
---
conclusion: Lax619925.Shuffle.ShuffleEffectivePrevariety
---
The shuffle-finite series form an effective prevariety over a finite alphabet
(paper §6, theorem): the effective prevariety `shuffleEffectivePrevariety` has
presentations given by shuffle automata, and its image is exactly the
shuffle-finite series (by the coincidence, `ShuffleCoincidence`).
-/
theorem ShuffleEffectivePrevariety [Fintype α] :
    ∃ P : EffectivePrevariety α, ∀ f, IsShuffleFinite α f ↔ ∃ r : P.Rep, P.sem r = f := by
  refine ⟨shuffleEffectivePrevariety, ?_⟩
  intro f
  dsimp [shuffleEffectivePrevariety, IsShuffleRecognisable]
  exact ShuffleCoincidence f

/--
---
conclusion: Lax619925.Shuffle.ShuffleCommutativityDecidable
---
The commutativity problem is decidable for shuffle-finite series over a finite
alphabet (paper §6).  This is the meta-theorem
(`EffectivePrevarietyCommutativityDecidable`) applied to
`shuffleEffectivePrevariety`, the effective prevariety of shuffle-finite
series: its boolean decider on a presentation `A` decides
`IsCommutative (shuffleEffectivePrevariety.sem A)`, and since
`shuffleEffectivePrevariety.sem A = A.recognised`, it decides
`IsCommutative (A.recognised)`.
-/
theorem ShuffleCommutativityDecidable [Fintype α] :
    ∃ d : ShuffleAutomaton α → Bool, ∀ A, d A = true ↔ IsCommutative α (A.recognised) := by
  obtain ⟨d, hd⟩ := EffectivePrevarietyCommutativityDecidable (α := α) shuffleEffectivePrevariety
  refine ⟨fun (A : ShuffleAutomaton α) => d A, fun A => ?_⟩
  have hsem : shuffleEffectivePrevariety.sem A = A.recognised := by
    dsimp only [shuffleEffectivePrevariety]
  simpa [hsem] using hd A

end Lax619925Proofs.Shuffle
