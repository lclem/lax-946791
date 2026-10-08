import Lax619925.Hadamard
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
import Mathlib.Data.Bool.Basic
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Algebra.Basic
import Mathlib.RingTheory.Ideal.Basic
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.Tactic

-- `letI` is used to register the `IsNoetherianRing` instance required by
-- `Ideal.fg_of_isNoetherianRing`; the `haveILetI` linter's suggestion to use
-- `let` would drop that instance, so the linter is disabled here.
set_option linter.style.haveILetI false

namespace Lax619925Proofs.Hadamard

open Lax619925.Series Lax619925.Prevariety Lax619925.Commutativity Lax619925.Hadamard
open Lax619925.IdealMembership
open MvPolynomial
open Classical

variable {α : Type*}

/-! ### The word extension is a `ℚ`-algebra endomorphism -/

/-- `Mword [] = id`. -/
theorem Mword_nil (A : HadamardAutomaton α) : A.Mword [] = id := by
  rfl

/-- `Mword (a :: w) = Mword w ∘ aeval (Δ a)`: reading `a` then `w` applies the letter
    endomorphism `Δ_a` first, then the word endomorphism for `w`. -/
private theorem Mword_cons (A : HadamardAutomaton α) (a : α) (w : List α) :
    A.Mword (a :: w) = A.Mword w ∘ aeval (A.Δ a) := by
  dsimp [HadamardAutomaton.Mword]
  funext β
  simp

/-- `Mword (u ++ v) = Mword v ∘ Mword u` (the letters of `u` are applied after those of
    `v`, right-to-left). -/
private theorem Mword_append (A : HadamardAutomaton α) (u v : List α) :
    A.Mword (u ++ v) = A.Mword v ∘ A.Mword u := by
  induction u with
  | nil =>
      funext β
      simp [Mword_nil]
  | cons a u ih =>
      funext β
      simp [Mword_cons, List.cons_append, ih, Function.comp_apply]

/-- The `ℚ`-algebra endomorphism version of `Mword`: the composition of the letter
    algebra homomorphisms `aeval (Δ a)` along the word, right-to-left. -/
noncomputable def MwordAlg (A : HadamardAutomaton α) (w : List α) :
    MvPolynomial (Fin A.dim) ℚ →ₐ[ℚ] MvPolynomial (Fin A.dim) ℚ :=
  w.foldr (fun a φ => φ.comp (aeval (A.Δ a))) (AlgHom.id ℚ (MvPolynomial (Fin A.dim) ℚ))

/-- `MwordAlg A (a :: w) = (MwordAlg A w).comp (aeval (Δ a))`. -/
private theorem MwordAlg_cons (A : HadamardAutomaton α) (a : α) (w : List α) :
    MwordAlg A (a :: w) = (MwordAlg A w).comp (aeval (A.Δ a)) := by
  dsimp [MwordAlg]

/-- `MwordAlg A w` applied to a configuration is `Mword A w` applied to it: the algebra
    endomorphism and the raw word map agree pointwise. -/
private theorem MwordAlg_apply (A : HadamardAutomaton α) (w : List α)
    (p : MvPolynomial (Fin A.dim) ℚ) : (MwordAlg A w) p = A.Mword w p := by
  have : ∀ (w : List α) (p : MvPolynomial (Fin A.dim) ℚ), (MwordAlg A w) p = A.Mword w p := by
    intro w
    induction w with
    | nil =>
        intro p
        rfl
    | cons a w ih =>
        intro p
        rw [MwordAlg_cons, AlgHom.comp_apply, ih (aeval (A.Δ a) p), Mword_cons, Function.comp_apply]
  exact this w p

/-- `Mword A w` preserves addition: it is the underlying map of the algebra endomorphism
    `MwordAlg A w`. -/
private theorem Mword_add (A : HadamardAutomaton α) (w : List α)
    (p q : MvPolynomial (Fin A.dim) ℚ) : A.Mword w (p + q) = A.Mword w p + A.Mword w q := by
  rw [← MwordAlg_apply A w p, ← MwordAlg_apply A w q, ← MwordAlg_apply A w (p + q)]
  exact (MwordAlg A w).map_add p q

/-- `Mword A w` preserves multiplication. -/
private theorem Mword_mul (A : HadamardAutomaton α) (w : List α)
    (p q : MvPolynomial (Fin A.dim) ℚ) : A.Mword w (p * q) = A.Mword w p * A.Mword w q := by
  rw [← MwordAlg_apply A w p, ← MwordAlg_apply A w q, ← MwordAlg_apply A w (p * q)]
  exact (MwordAlg A w).map_mul p q

/-! ### Semantics properties -/

/-- The semantics is `ℚ`-linear: `A.sem (p + q) = A.sem p + A.sem q`. -/
private theorem sem_add (A : HadamardAutomaton α) (p q : MvPolynomial (Fin A.dim) ℚ) :
    A.sem (p + q) = A.sem p + A.sem q := by
  funext w
  dsimp [HadamardAutomaton.sem]
  rw [Mword_add, eval_add]

/-- The semantics is a ring homomorphism on the configuration space:
    `A.sem (p * q) = A.sem p * A.sem q` (the Hadamard product of the two recognised
    series). -/
private theorem sem_mul (A : HadamardAutomaton α) (p q : MvPolynomial (Fin A.dim) ℚ) :
    A.sem (p * q) = A.sem p * A.sem q := by
  funext w
  dsimp [HadamardAutomaton.sem]
  rw [Mword_mul, eval_mul]

/-- The derivation property: `leftDeriv a (A.sem p) = A.sem (Δ_a p)`.  Reading the word
    `a :: w` applies `Δ_a` first (`Mword_cons`), so the left derivative of the semantics
    at `p` is the semantics at `Δ_a p`. -/
theorem sem_deriv (A : HadamardAutomaton α) (a : α) (p : MvPolynomial (Fin A.dim) ℚ) :
    leftDeriv α a (A.sem p) = A.sem (aeval (A.Δ a) p) := by
  funext w
  dsimp [HadamardAutomaton.sem, leftDeriv]
  rw [Mword_cons]
  rfl

/-! ### The semantics is a `ℚ`-algebra homomorphism -/

/-- The semantics is a `ℚ`-algebra homomorphism that agrees with the `aeval` of the
    generator series: `A.sem p = aeval (fun i => A.sem (X i)) p`, the evaluation of `p`
    in the pointwise ring of series sending `X_i` to the generator series `A.sem (X_i)`.
    The map `p ↦ A.sem p` is a `ℚ`-algebra homomorphism (built from `sem_add`/`sem_mul`
    and the unit / scalar laws) and is identified with the `aeval` of its values on the
    generators by `aeval_unique`. -/
theorem sem_aeval (A : HadamardAutomaton α) (p : MvPolynomial (Fin A.dim) ℚ) :
    A.sem p = aeval (fun i => A.sem (MvPolynomial.X i)) p := by
  let semAlg : MvPolynomial (Fin A.dim) ℚ →ₐ[ℚ] Series α :=
    { toFun := A.sem,
      map_zero' := by
        funext w
        dsimp [HadamardAutomaton.sem]
        rw [← MwordAlg_apply A w 0]
        simp
      map_one' := by
        funext w
        dsimp [HadamardAutomaton.sem]
        rw [← MwordAlg_apply A w 1]
        simp
      map_mul' := fun p q => sem_mul A p q,
      map_add' := fun p q => sem_add A p q,
      commutes' := fun r => by
        funext w
        dsimp [HadamardAutomaton.sem]
        rw [← MwordAlg_apply A w _]
        simp }
  have h : semAlg = aeval (fun i => A.sem (MvPolynomial.X i)) := by
    rw [aeval_unique semAlg]
    congr
  rw [← h]
  rfl

/-! ### `hadamardEval` is `aeval` in the pointwise ring of series -/

/-- `hadamardEval α k fs p` is the `aeval` of the assignment `X_i ↦ fs i` in the pointwise
    ring of series: the two differ only in the (commutative) order of the coefficient and
    the monomial product. -/
theorem hadamardEval_aeval (k : ℕ) (fs : Fin k → Series α) (p : MvPolynomial (Fin k) ℚ) :
    hadamardEval α k fs p = aeval (fun i => fs i) p := by
  funext w
  simp [hadamardEval, MvPolynomial.aeval_def, MvPolynomial.eval₂_eq']

/-! ### Left derivatives commute with `aeval` -/

/-- The left derivative of the `aeval` of a polynomial is the `aeval` of the polynomial
    in the left derivatives of the assigned series: `leftDeriv a (aeval φ p) =
    aeval (fun i => leftDeriv a (φ i)) p`.  The left derivative is the pointwise map
    `f ↦ f ∘ (a · -)`, a ring homomorphism on the pointwise ring of series, so it
    commutes with the evaluation. -/
private theorem leftDeriv_aeval (k : ℕ) (φ : Fin k → Series α) (p : MvPolynomial (Fin k) ℚ)
    (a : α) : leftDeriv α a (aeval φ p) = aeval (fun i => leftDeriv α a (φ i)) p := by
  funext w
  simp [leftDeriv, MvPolynomial.aeval_def, MvPolynomial.eval₂_eq']

/-- The left derivative of a Hadamard polynomial is the Hadamard polynomial in the left
    derivatives of the assigned series: `leftDeriv a (hadamardEval α k fs p) =
    hadamardEval α k (fun i => leftDeriv a (fs i)) p`. -/
private theorem leftDeriv_hadamardEval (k : ℕ) (fs : Fin k → Series α)
    (p : MvPolynomial (Fin k) ℚ) (a : α) :
    leftDeriv α a (hadamardEval α k fs p) = hadamardEval α k (fun i => leftDeriv α a (fs i)) p := by
  rw [hadamardEval_aeval, leftDeriv_aeval, hadamardEval_aeval]

/-! ### Extending the witnessing tuple -/

/-- The witnessing tuple extended by `f` at index `0`: `extTuple f k fs 0 = f` and
    `extTuple f k fs (Fin.succ i) = fs i`.  This lets a Hadamard polynomial in `fs` be
    viewed as a Hadamard polynomial in the extended tuple, with `f` as a generator. -/
noncomputable def extTuple (f : Series α) (k : ℕ) (fs : Fin k → Series α) : Fin (k+1) → Series α :=
  fun j => if h : j = 0 then f else fs ⟨j.val - 1, by
    have hlt : j.val < k + 1 := j.isLt
    have hne : j.val ≠ 0 := by
      intro hj
      exact h (Fin.ext hj)
    omega⟩

/-- `extTuple f k fs 0 = f`. -/
private theorem extTuple_zero (f : Series α) (k : ℕ) (fs : Fin k → Series α) :
    extTuple f k fs 0 = f := by
  simp [extTuple]

/-- `extTuple f k fs (Fin.succ i) = fs i`. -/
private theorem extTuple_succ (f : Series α) (k : ℕ) (fs : Fin k → Series α) (i : Fin k) :
    extTuple f k fs (Fin.succ i) = fs i := by
  simp [extTuple]

/-- The embedding of a polynomial in `Fin k` into `Fin (k+1)`, shifting each variable
    `X_i` to `X_{i+1}` (leaving `X_0` unused): `embedPoly k p = aeval (X ∘ Fin.succ) p`. -/
noncomputable def embedPoly (k : ℕ) (p : MvPolynomial (Fin k) ℚ) : MvPolynomial (Fin (k+1)) ℚ :=
  aeval (fun i => MvPolynomial.X (Fin.succ i)) p

/-! ### Substitution and embedding for `hadamardEval` -/

/-- Substituting Hadamard polynomials: evaluating `p` in the Hadamard algebra where
    `X_i` is the Hadamard polynomial `q_i` equals evaluating the composed polynomial
    `aeval (q) p` in the original Hadamard algebra.  This is the `aeval` composition law
    (`comp_aeval_apply`) expressed in terms of `hadamardEval`. -/
private theorem hadamardEval_subst (k : ℕ) (fs : Fin k → Series α)
    (q : α → Fin k → MvPolynomial (Fin k) ℚ) (a : α) (p : MvPolynomial (Fin k) ℚ) :
    hadamardEval α k (fun i => hadamardEval α k fs (q a i)) p =
        hadamardEval α k fs (aeval (fun i => q a i) p) := by
  have h1 : hadamardEval α k (fun i => hadamardEval α k fs (q a i)) p =
      aeval (fun i => aeval (fun j => fs j) (q a i)) p := by
    rw [hadamardEval_aeval]
    congr
    funext i
    rw [hadamardEval_aeval]
  have h2 : hadamardEval α k fs (aeval (fun i => q a i) p) =
      aeval (fun j => fs j) (aeval (fun i => q a i) p) := by
    rw [hadamardEval_aeval]
  calc
    hadamardEval α k (fun i => hadamardEval α k fs (q a i)) p =
        aeval (fun i => aeval (fun j => fs j) (q a i)) p := h1
    _ = aeval (fun j => fs j) (aeval (fun i => q a i) p) := by
      rw [← MvPolynomial.comp_aeval_apply]
    _ = hadamardEval α k fs (aeval (fun i => q a i) p) := h2.symm

/-- A Hadamard polynomial in `fs` is the same series as the embedded Hadamard polynomial
    in the extended tuple: `hadamardEval α k fs r = hadamardEval α (k+1) (extTuple f k fs)
    (embedPoly k r)`.  The `X_0` slot of the extended tuple is unused by the embedded
    polynomial, so the value of `f` there is irrelevant. -/
private theorem hadamardEval_embed (f : Series α) (k : ℕ) (fs : Fin k → Series α)
    (r : MvPolynomial (Fin k) ℚ) :
    hadamardEval α k fs r = hadamardEval α (k+1) (extTuple f k fs) (embedPoly k r) := by
  rw [hadamardEval_aeval, hadamardEval_aeval, embedPoly, MvPolynomial.comp_aeval_apply]
  have hfun : (fun i => fs i) =
      (fun i => (aeval (fun j => extTuple f k fs j)
          (MvPolynomial.X (Fin.succ i) : MvPolynomial (Fin (k+1)) ℚ) : Series α)) := by
    funext i
    rw [aeval_X, extTuple_succ]
  rw [hfun]

/-! ### The coincidence: finite ↔ recognisable -/

/-- Every Hadamard-recognisable series is Hadamard-finite (the "recognisable implies
    finite" direction of the coincidence).  The witnessing tuple is the generator series
    `A.sem (X_i)`, closed under left derivatives by the derivation property `sem_deriv`;
    `f` is the Hadamard polynomial `X_0` in that tuple. -/
private theorem finite_of_recognisable (f : Series α)
    (hrec : IsHadamardRecognisable α f) : IsHadamardFinite α f := by
  obtain ⟨A, hA⟩ := hrec
  let X0 : MvPolynomial (Fin A.dim) ℚ := MvPolynomial.X (Fin.mk 0 A.hdim)
  let fs := fun i => A.sem (MvPolynomial.X i)
  have hf : f = A.sem X0 := by
    rw [← hA, HadamardAutomaton.recognised]
  have h1 : f = hadamardEval α A.dim fs X0 := by
    rw [hf, sem_aeval, hadamardEval_aeval]
  refine ⟨A.dim, fs, X0, h1, ?_⟩
  intro a i
  refine ⟨A.Δ a i, ?_⟩
  have hlhs : leftDeriv α a (fs i) = A.sem (A.Δ a i) := by
    dsimp [fs]
    rw [sem_deriv, aeval_X]
  rw [hlhs, sem_aeval, hadamardEval_aeval]

/-- Every Hadamard-finite series is Hadamard-recognisable (the "finite implies
    recognisable" direction of the coincidence).  Given `f = hadamardEval α k fs p` with
    `fs` closed under left derivatives, extend the tuple to `g = extTuple f k fs` (so
    `g 0 = f` and `g (Fin.succ i) = fs i`), show `g` is closed under left derivatives,
    build an automaton `A` with `dim = k+1`, `F i = (g i) []`, and `Δ a i` the polynomial
    witnessing the closure of `g i`, and prove `A.sem p = hadamardEval α (k+1) g p` for
    all `p` by a word-length induction.  Then `A.recognised = A.sem (X_0) = g 0 = f`. -/
private theorem recognisable_of_finite (f : Series α)
    (hfin : IsHadamardFinite α f) : IsHadamardRecognisable α f := by
  obtain ⟨k, fs, p, hf, hclose⟩ := hfin
  let g := extTuple f k fs
  -- `g` is closed under left derivatives
  have hclose_g : ∀ (a : α) (j : Fin (k+1)),
      ∃ q, leftDeriv α a (g j) = hadamardEval α (k+1) g q := by
    intro a j
    by_cases h0 : j = 0
    · -- `j = 0`: `g 0 = f = hadamardEval α k fs p`
      let qf : Fin k → MvPolynomial (Fin k) ℚ := fun i => Classical.choose (hclose a i)
      have hqf : ∀ i, leftDeriv α a (fs i) = hadamardEval α k fs (qf i) := by
        intro i
        dsimp [qf]
        exact Classical.choose_spec (hclose a i)
      have hg0 : g 0 = f := by
        dsimp [g]
        rw [extTuple_zero]
      refine ⟨embedPoly k (aeval qf p), ?_⟩
      calc
        leftDeriv α a (g j) = leftDeriv α a (g 0) := by rw [h0]
        _ = leftDeriv α a f := by rw [hg0]
        _ = leftDeriv α a (hadamardEval α k fs p) := by rw [← hf]
        _ = hadamardEval α k (fun i => leftDeriv α a (fs i)) p := by rw [leftDeriv_hadamardEval]
        _ = hadamardEval α k (fun i => hadamardEval α k fs (qf i)) p := by
          congr; funext i; exact hqf i
        _ = hadamardEval α k fs (aeval qf p) := by
          rw [hadamardEval_subst _ _ (fun _ => qf) a p]
        _ = hadamardEval α (k+1) g (embedPoly k (aeval qf p)) := by rw [hadamardEval_embed]
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
      have hqi : leftDeriv α a (fs i) = hadamardEval α k fs qi := by
        rw [show qi = Classical.choose (hclose a i) from rfl]
        exact Classical.choose_spec (hclose a i)
      have hgs : g (Fin.succ i) = fs i := by
        dsimp [g]
        rw [extTuple_succ]
      refine ⟨embedPoly k qi, ?_⟩
      calc
        leftDeriv α a (g j) = leftDeriv α a (g (Fin.succ i)) := by rw [← hi]
        _ = leftDeriv α a (fs i) := by rw [hgs]
        _ = hadamardEval α k fs qi := hqi
        _ = hadamardEval α (k+1) g (embedPoly k qi) := by rw [hadamardEval_embed]
  -- Choose the polynomials for the transition
  let Δ : α → Fin (k+1) → MvPolynomial (Fin (k+1)) ℚ :=
      fun a j => Classical.choose (hclose_g a j)
  have hΔ : ∀ (a : α) (j : Fin (k+1)),
      leftDeriv α a (g j) = hadamardEval α (k+1) g (Δ a j) := by
    intro a j
    rw [show Δ a j = Classical.choose (hclose_g a j) from rfl]
    exact Classical.choose_spec (hclose_g a j)
  -- Build the automaton
  let A : HadamardAutomaton α :=
    { dim := k + 1,
      hdim := by omega,
      F := fun i => (g i) [],
      Δ := Δ }
  -- The semantics agrees with the Hadamard evaluation in `g`, by a word-length induction
  have hsem : ∀ (w : List α) (p : MvPolynomial (Fin (k+1)) ℚ),
      A.sem p w = hadamardEval α (k+1) g p w := by
    intro w
    induction w with
    | nil =>
      intro p
      dsimp [HadamardAutomaton.sem]
      rw [Mword_nil]
      simp only [id]
      dsimp [A]
      simp [hadamardEval, MvPolynomial.eval_eq']
    | cons a w' ih =>
      intro p
      dsimp [HadamardAutomaton.sem]
      rw [Mword_cons]
      change A.sem (aeval (A.Δ a) p) w' = _
      have h1 : A.sem (aeval (A.Δ a) p) w' =
          hadamardEval α (k+1) g (aeval (A.Δ a) p) w' := ih (aeval (A.Δ a) p)
      rw [h1]
      have haeval : aeval (A.Δ a) p = aeval (fun i => A.Δ a i) p := rfl
      rw [haeval, ← hadamardEval_subst]
      have h2 : (fun i : Fin (k+1) => hadamardEval α (k+1) g (A.Δ a i)) =
          (fun i => leftDeriv α a (g i)) := by
        funext i
        dsimp [A]
        rw [← hΔ a i]
      rw [h2, ← leftDeriv_hadamardEval (k+1) g p a]
      rfl
  -- `A.sem (X i) = g i` for all `i`
  have hgen : ∀ (i : Fin (k+1)), A.sem (MvPolynomial.X i) = g i := by
    intro i
    funext w
    simpa [hadamardEval_aeval, aeval_X] using hsem w (MvPolynomial.X i)
  -- `A.recognised = f`
  have hrec : A.recognised = f := by
    dsimp [HadamardAutomaton.recognised]
    rw [hgen 0]
    have hg0 : g 0 = f := by
      dsimp [g]
      rw [extTuple_zero]
    rw [hg0]
  exact ⟨A, hrec⟩

/-! ### The coincidence theorem -/

/--
---
conclusion: Lax619925.Hadamard.HadamardCoincidence
---
The Hadamard coincidence theorem (paper §5): a series is Hadamard-finite if and
only if it is Hadamard-recognisable.  The "recognisable implies finite" direction
reads off the generator tuple `A.sem (X_i)`; the "finite implies recognisable"
direction extends the witnessing tuple by the series itself and builds the
automaton from the closure under left derivatives.
-/
theorem HadamardCoincidence (f : Series α) :
    IsHadamardFinite α f ↔ IsHadamardRecognisable α f := by
  constructor
  · intro hfin
    exact recognisable_of_finite f hfin
  · intro hrec
    exact finite_of_recognisable f hrec

/-! ### Closure of the Hadamard-finite series -/

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

/-- A Hadamard polynomial in `fs` is unchanged when the tuple is extended with `fs'` and
    the polynomial is embedded at the front: `hadamardEval α k fs p =
    hadamardEval α (k + k') (combineTuple k k' fs fs') (embedFront k k' p)`.  The trailing
    slots of the extended tuple are unused by the embedded polynomial, so their values
    (`fs'`) are irrelevant. -/
private theorem hadamardEval_embedFront (k k' : ℕ) (fs : Fin k → Series α)
    (fs' : Fin k' → Series α) (p : MvPolynomial (Fin k) ℚ) :
    hadamardEval α k fs p = hadamardEval α (k + k') (combineTuple k k' fs fs') (embedFront k k' p) := by
  rw [hadamardEval_aeval, hadamardEval_aeval, embedFront, MvPolynomial.comp_aeval_apply]
  congr
  funext i
  rw [aeval_X]
  simp [combineTuple]

/-- The back-embedding analogue: `hadamardEval α k' fs' p =
    hadamardEval α (k + k') (combineTuple k k' fs fs') (embedBack k k' p)`. -/
private theorem hadamardEval_embedBack (k k' : ℕ) (fs : Fin k → Series α)
    (fs' : Fin k' → Series α) (p : MvPolynomial (Fin k') ℚ) :
    hadamardEval α k' fs' p = hadamardEval α (k + k') (combineTuple k k' fs fs') (embedBack k k' p) := by
  rw [hadamardEval_aeval, hadamardEval_aeval, embedBack, MvPolynomial.comp_aeval_apply]
  congr
  funext i
  rw [aeval_X]
  simp [combineTuple]

/-- The concatenated tuple is closed under left derivatives, given that both summands are:
    the left derivative of a slot is the embedded left derivative of the corresponding
    summand slot. -/
private theorem combineTuple_closed (k k' : ℕ) (fs : Fin k → Series α) (fs' : Fin k' → Series α)
    (hfs : ∀ a (i : Fin k), ∃ q, leftDeriv α a (fs i) = hadamardEval α k fs q)
    (hfs' : ∀ a (i : Fin k'), ∃ q, leftDeriv α a (fs' i) = hadamardEval α k' fs' q) :
    ∀ a (i : Fin (k + k')), ∃ q,
      leftDeriv α a (combineTuple k k' fs fs' i) =
        hadamardEval α (k + k') (combineTuple k k' fs fs') q := by
  intro a i
  by_cases hlt : i.val < k
  · let j : Fin k := ⟨i.val, hlt⟩
    obtain ⟨q, hq⟩ := hfs a j
    refine ⟨embedFront k k' q, ?_⟩
    have hci : combineTuple k k' fs fs' i = fs j := by
      simp [combineTuple, j, hlt]
    rw [hci, hq, hadamardEval_embedFront]
  · let j : Fin k' := ⟨i.val - k, by omega⟩
    obtain ⟨q, hq⟩ := hfs' a j
    refine ⟨embedBack k k' q, ?_⟩
    have hci : combineTuple k k' fs fs' i = fs' j := by
      simp [combineTuple, j, hlt]
    rw [hci, hq, hadamardEval_embedBack]

/-- The right-derivative automaton: the same dimension and transitions as `A`, but with
    the final-weight functional pre-composed with the letter endomorphism `Δ_a`,
    `F' i = eval (A.F) (A.Δ a i)`.  Reading a word `w` and then the trailing letter `a`
    applies `Δ_a` to the configuration reached by `w`, so the right derivative of the
    recognised series is recognised by this automaton. -/
noncomputable def rightDerivAutomaton (A : HadamardAutomaton α) (a : α) : HadamardAutomaton α :=
  { dim := A.dim,
    hdim := A.hdim,
    F := fun i => eval (A.F) (A.Δ a i),
    Δ := A.Δ }

/-- `A.Mword [a] = aeval (A.Δ a)`: a single-letter word applies just that letter's
    endomorphism. -/
private theorem Mword_singleton (A : HadamardAutomaton α) (a : α) :
    A.Mword [a] = aeval (A.Δ a) := by
  rw [Mword_cons, Mword_nil]
  simp

/-- Composing the final-weight evaluation with a letter endomorphism is the evaluation at
    the pre-composed weights: `eval (A.F) (aeval (A.Δ a) p) =
    eval (fun i => eval (A.F) (A.Δ a i)) p`.  Both sides are the evaluation of `p` in `ℚ`
    sending `X_i` to `eval (A.F) (A.Δ a i)`. -/
private theorem eval_aeval (A : HadamardAutomaton α) (a : α) (p : MvPolynomial (Fin A.dim) ℚ) :
    eval (A.F) (aeval (A.Δ a) p) = eval (fun i => eval (A.F) (A.Δ a i)) p := by
  rw [MvPolynomial.map_aeval]
  have h : (eval (A.F) : MvPolynomial (Fin A.dim) ℚ →+* ℚ).comp
      (algebraMap ℚ (MvPolynomial (Fin A.dim) ℚ)) = RingHom.id ℚ := by
    apply RingHom.ext
    intro c
    simp
  rw [h]
  rfl

/-- The right derivative of the series recognised by `A` is recognised by the
    right-derivative automaton: `rightDeriv a (A.recognised) = (rightDerivAutomaton A a)
    .recognised`.  Reading `w ++ [a]` applies `Δ_a` to the configuration reached by `w`
    (`Mword_append`), and `eval (A.F) ∘ aeval (Δ_a)` is the evaluation at the modified
    final weights `F' i = eval (A.F) (A.Δ a i)`. -/
private theorem rightDeriv_recognised (A : HadamardAutomaton α) (a : α) :
    (rightDerivAutomaton A a).recognised = rightDeriv α a (A.recognised) := by
  funext w
  dsimp [HadamardAutomaton.recognised, HadamardAutomaton.sem, rightDeriv, rightDerivAutomaton]
  have h_rhs : eval (A.F) (A.Mword (w ++ [a]) (MvPolynomial.X (Fin.mk 0 A.hdim))) =
      eval (A.F) (aeval (A.Δ a) (A.Mword w (MvPolynomial.X (Fin.mk 0 A.hdim)))) := by
    rw [Mword_append, Function.comp_apply, Mword_singleton]
  rw [h_rhs]
  exact (eval_aeval A a (A.Mword w (MvPolynomial.X (Fin.mk 0 A.hdim)))).symm

/-! ### The closure theorem -/

/--
---
conclusion: Lax619925.Hadamard.HadamardClosure
---
The Hadamard closure theorem (paper §5): the Hadamard-finite series are closed under
addition, scalar multiplication, the Hadamard product, and right derivatives.  Addition,
scalar multiplication, and the Hadamard product follow by concatenating the witnessing
tuples (the Hadamard algebra is the pointwise ring, so the evaluation is a `ℚ`-algebra
homomorphism); the right derivative is handled by the coincidence together with the
right-derivative automaton (the final weights pre-composed with the letter endomorphism).
-/
theorem HadamardClosure :
    (∀ (f g : Series α), IsHadamardFinite α f → IsHadamardFinite α g → IsHadamardFinite α (f + g)) ∧
    (∀ (c : ℚ) (f : Series α), IsHadamardFinite α f → IsHadamardFinite α (c • f)) ∧
    (∀ (f g : Series α), IsHadamardFinite α f → IsHadamardFinite α g → IsHadamardFinite α (hadamard α f g)) ∧
    (∀ (a : α) (f : Series α), IsHadamardFinite α f → IsHadamardFinite α (rightDeriv α a f)) := by
  constructor
  · -- Addition
    intro f g hf hg
    obtain ⟨k, fs, p, hfp, hfc⟩ := hf
    obtain ⟨k', fs', p', hgp', hfc'⟩ := hg
    refine ⟨k + k', combineTuple k k' fs fs', embedFront k k' p + embedBack k k' p', ?_,
        combineTuple_closed k k' fs fs' hfc hfc'⟩
    calc
      f + g = hadamardEval α k fs p + hadamardEval α k' fs' p' := by rw [← hfp, ← hgp']
      _ = hadamardEval α (k + k') (combineTuple k k' fs fs') (embedFront k k' p) +
          hadamardEval α k' fs' p' := by
        rw [hadamardEval_embedFront k k' fs fs' p]
      _ = hadamardEval α (k + k') (combineTuple k k' fs fs') (embedFront k k' p) +
          hadamardEval α (k + k') (combineTuple k k' fs fs') (embedBack k k' p') := by
        rw [hadamardEval_embedBack k k' fs fs' p']
      _ = hadamardEval α (k + k') (combineTuple k k' fs fs')
          (embedFront k k' p + embedBack k k' p') := by
        simp [hadamardEval_aeval]
  · constructor
    · -- Scalar multiplication
      intro c f hf
      obtain ⟨k, fs, p, hfp, hfc⟩ := hf
      refine ⟨k, fs, c • p, ?_, hfc⟩
      calc
        c • f = c • hadamardEval α k fs p := by rw [← hfp]
        _ = c • aeval (fun i => fs i) p := by rw [hadamardEval_aeval]
        _ = aeval (fun i => fs i) (c • p) := by simp
        _ = hadamardEval α k fs (c • p) := by rw [hadamardEval_aeval]
    · constructor
      · -- Hadamard product
        intro f g hf hg
        obtain ⟨k, fs, p, hfp, hfc⟩ := hf
        obtain ⟨k', fs', p', hgp', hfc'⟩ := hg
        refine ⟨k + k', combineTuple k k' fs fs', embedFront k k' p * embedBack k k' p', ?_,
            combineTuple_closed k k' fs fs' hfc hfc'⟩
        calc
          hadamard α f g = f * g := rfl
          _ = hadamardEval α k fs p * hadamardEval α k' fs' p' := by rw [← hfp, ← hgp']
          _ = hadamardEval α (k + k') (combineTuple k k' fs fs') (embedFront k k' p) *
              hadamardEval α k' fs' p' := by
            rw [hadamardEval_embedFront k k' fs fs' p]
          _ = hadamardEval α (k + k') (combineTuple k k' fs fs') (embedFront k k' p) *
              hadamardEval α (k + k') (combineTuple k k' fs fs') (embedBack k k' p') := by
            rw [hadamardEval_embedBack k k' fs fs' p']
          _ = hadamardEval α (k + k') (combineTuple k k' fs fs')
              (embedFront k k' p * embedBack k k' p') := by
            simp [hadamardEval_aeval]
      · -- Right derivative (via the coincidence and the right-derivative automaton)
        intro a f hf
        have hrec : IsHadamardRecognisable α f := (HadamardCoincidence f).mp hf
        obtain ⟨A, hA⟩ := hrec
        let A' := rightDerivAutomaton A a
        have hA' : A'.recognised = rightDeriv α a f := by
          rw [rightDeriv_recognised, ← hA]
        exact (HadamardCoincidence (rightDeriv α a f)).mpr ⟨A', hA'⟩

/-! ### The anti-derivative closure -/

/-- A package of the witnessing data for a Hadamard-finite series: the dimension `k`, the
    generator tuple `fs`, the polynomial `p`, and the proofs that `f = p(fs)` and that `fs`
    is closed under left derivatives.  Packaged as a `Type` (not a `Prop`) so that
    `Classical.choose` can produce one witness per letter from a `∀ a, IsHadamardFinite …`. -/
structure HadamardWitnessData (α : Type*) (f : Series α) where
  k : ℕ
  fs : Fin k → Series α
  p : MvPolynomial (Fin k) ℚ
  hfin : f = hadamardEval α k fs p
  hclose : ∀ a i, ∃ q, leftDeriv α a (fs i) = hadamardEval α k fs q

/-- `IsHadamardFinite α f` is the same as the existence of a `HadamardWitnessData`. -/
private theorem HadamardWitnessData_iff (f : Series α) :
    IsHadamardFinite α f ↔ ∃ _ : HadamardWitnessData α f, True := by
  constructor
  · intro h
    obtain ⟨k, fs, p, hfp, hfc⟩ := h
    exact ⟨⟨k, fs, p, hfp, hfc⟩, by trivial⟩
  · intro h
    obtain ⟨⟨k, fs, p, hfp, hfc⟩, -⟩ := h
    exact ⟨k, fs, p, hfp, hfc⟩

/--
---
conclusion: Lax619925.Hadamard.HadamardAntiDerivativeClosure
---
The Hadamard anti-derivative closure (paper §5): over a finite alphabet, if `g` is a left
anti-derivative of a tuple `f` of Hadamard-finite series (`leftDeriv a g = f a` for all `a`),
then `g` is Hadamard-finite.  The witnessing tuple for `g` is `g` itself followed by the
concatenation of the witnessing tuples of the `f a`'s: `g` is trivially a Hadamard polynomial
in a tuple containing it (its own variable), and the tuple is closed under left derivatives
because `leftDeriv a g = f a` is a Hadamard polynomial in the (closed) witnessing tuple for
`f a`, and each `f a`'s witnessing tuple is itself closed.  The finiteness of the alphabet is
what makes the combined tuple finite.
-/
theorem HadamardAntiDerivativeClosure [Fintype α]
    (g : Series α) (f : α → Series α) (hantideriv : IsLeftAntiDerivative α g f)
    (hf : ∀ a, IsHadamardFinite α (f a)) : IsHadamardFinite α g := by
  let W : (a : α) → HadamardWitnessData α (f a) :=
    fun a => Classical.choose ((HadamardWitnessData_iff (f a)).mp (hf a))
  -- The non-`g` slots: one per element of each `W a .fs`, indexed by the pair `(a, j)`.
  let nonGslots : Finset (α × ℕ) :=
    Finset.biUnion Finset.univ (fun a => (Finset.range ((W a).k)).image (fun j => (a, j)))
  let M : ℕ := nonGslots.card
  let e : Fin M ≃ nonGslots := (Finset.equivFin nonGslots).symm
  -- The `Fin M` index of the non-`g` slot for a slot `i` is `i.val - 1`.  The `i.val ≠ 0`
  -- argument is required for totality: when `M = 0`, `i : Fin (1 + M) = Fin 1` forces
  -- `i.val = 0`, so the `i.val ≠ 0` premise is false and the function is vacuously defined.
  -- Callers (`FS`'s `else` branch, `hFS_slot`) supply the premise, which holds there.
  let idx : (i : Fin (1 + M)) → i.val ≠ 0 → Fin M :=
    fun i hne => ⟨i.val - 1, by
      by_cases hM : M = 0
      · -- `M = 0` forces `i.val = 0` (since `i : Fin (1 + M) = Fin 1`), contradicting `hne`.
        exfalso
        have : i.val = 0 := by
          have : i.val < 1 := by simpa [hM] using i.isLt
          omega
        exact hne this
      · -- `M ≠ 0`: `i.val - 1 < i.val ≤ M` (the `hne` premise gives `i.val ≥ 1`;
        -- `i.isLt : i.val < 1 + M` gives `i.val ≤ M`).
        have hsub : i.val - 1 < i.val := by omega
        have hle : i.val ≤ M := by omega
        exact Nat.lt_of_lt_of_le hsub hle⟩
  -- The bound on the second component of `e j` (from its membership in `nonGslots`), hoisted
  -- out of `FS`'s `else` branch: a `have`/`let` binding of a `Prop`-typed value is opaque to
  -- `dsimp`, which would keep the `if` from reducing to a flat `ite` that `rw [ite_false]`
  -- can match.  As a top-level `let` function it is transparent at the call site.
  let hj_of (j : Fin M) : (e j).1.2 < (W ((e j).1.1)).k := by
    let hmem := (e j).2
    dsimp [nonGslots] at hmem
    obtain ⟨b', hb', himg⟩ := Finset.mem_biUnion.mp hmem
    obtain ⟨j', hj', hpair⟩ := Finset.mem_image.mp himg
    -- `hpair : (b', j') = (e j).1`, so `b' = (e j).1.1` and `j' = (e j).1.2`; `hj'` is a
    -- `Finset.range` membership, converted to `<` via `Finset.mem_range`.
    have hb' : b' = (e j).1.1 := (Prod.ext_iff.mp hpair).1
    have hj'eq : j' = (e j).1.2 := (Prod.ext_iff.mp hpair).2
    rw [hb', hj'eq] at hj'
    exact Finset.mem_range.mp hj'
  -- The series held at the non-`g` slot for `Fin M` index `j`: the `((e j).1.2)`-th element
  -- of the witnessing tuple of `W ((e j).1.1)`.  The bound proof is inlined (rather than
  -- referencing the `hj_of` let-binding) so that it elaborates to a concrete proof term:
  -- `rw`/`simp` can then adjust it via `Eq.ndrec` when rewriting `e (idx ·)` in `hFS_slot`.
  -- (A `let`-bound function is opaque to `rw`/`simp` — its type is not rewritten.)
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
  -- `Fin M` index `idx i` (i.e. `i.val - 1`), an element of some `W b .fs`.  The `else`
  -- branch is the bare application `FSofJ (idx i)`, so the `if` reduces to a flat `ite`,
  -- and the index `idx i` is shared with the lemmas about `FS`.
  let FS : Fin (1 + M) → Series α := fun i =>
    if h : i.val = 0 then g
    else FSofJ (idx i (by omega))
  -- `g` is a Hadamard polynomial in `FS`: the variable of slot 0.
  have hfin_g : g = hadamardEval α (1 + M) FS (MvPolynomial.X ⟨0, by omega⟩) := by
    rw [hadamardEval_aeval, MvPolynomial.aeval_X]
    simp [FS]
  -- Membership of `(a, j)` in `nonGslots` (for `j < (W a).k`), as a named constant so that
  -- `slot_of` and the lemmas about it share the *same* term (a `let` would be inlined by
  -- `dsimp`, leaving two definitionally-distinct but propositionally-equal proofs).
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
    · -- `M = 0` makes `nonGslots` empty, so no `(a, j)` with `j < (W a).k` exists: vacuous.
      exfalso
      have hmem : (a, j) ∈ nonGslots := hmem_pair a j hj
      have hpos : 0 < nonGslots.card := Finset.card_pos.mpr ⟨(a, j), hmem⟩
      have hzero : nonGslots.card = 0 := hM
      rw [hzero] at hpos
      omega
    · -- `M ≠ 0`.  `i = slot_of a j hj` has `i.val = 1 + ↑(e.symm x).val ≥ 1`, so `FS i` takes
      -- the else branch: the non-`g` slot for `Fin M` index `idx i` (= `i.val - 1`), whose
      -- `e`-image is `x = (a, j)`.  We reduce the `if` with `split_ifs` (the `i.val = 0` case
      -- is impossible) and then use `he : e (idx i) = x`.
      let x : nonGslots := ⟨(a, j), hmem_pair a j hj⟩
      let i := slot_of a j hj
      -- `i.val = 1 + ↑(e.symm x).val ≥ 1`, so the `idx` premise `i.val ≠ 0` holds.
      let hne : i.val ≠ 0 := by
        dsimp [i, slot_of, x]
        omega
      have he : e (idx i hne) = x := by
        have hval : (idx i hne).val = (e.symm x).val := by
          dsimp [idx, i, slot_of, x]
          omega
        rw [Fin.ext hval]
        exact Equiv.apply_symm_apply e x
      -- Unfold only `FS` (to expose the `ite` for `split_ifs`); keep `i` as a `let` so the
      -- component equalities `h1`/`h2` below (which also carry `i` as a `let`) match the goal
      -- syntactically.  `he` gets `i`/`slot_of`/`x` unfolded separately, for `h1`/`h2`'s proofs.
      dsimp [FS]
      dsimp [i, slot_of, x] at he
      split_ifs with h
      · -- `i.val = 0`: impossible, since `i.val = 1 + ↑(e.symm x).val ≥ 1`.  `by_contra`
        -- turns the goal into `False`; `omega` then sees `i.val = 1 + ↑(e.symm x).val`
        -- (unfolded by the earlier `dsimp … at he`) and contradicts `i.val = 0`.
        exfalso
        omega
      · -- `i.val ≠ 0`: the else branch.  `he : e (idx i hne) = x` gives the component
        -- equalities `(e (idx i hne)).1.1 = a` and `(e (idx i hne)).1.2 = j`.  The bound
        -- proof in `FSofJ` is inlined (a concrete term, not the `hj_of` let-binding), so
        -- `rw [he']` rewrites `e (idx ·)` to `x = ⟨(a, j), ·⟩` and adjusts the bound proof
        -- via `Eq.ndrec`, reducing the goal to `rfl` (the two `Fin (W a).k` witnesses agree
        -- on `.1 = j`).
        dsimp [FSofJ]
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
      ∃ q, leftDeriv α a (FS i) = hadamardEval α (1 + M) FS q := by
    intro a i
    by_cases h0 : i = 0
    · -- `i` is the `g` slot: `leftDeriv a g = f a`, a Hadamard polynomial in `W a .fs`.
      let q : MvPolynomial (Fin (1 + M)) ℚ :=
        aeval (fun j : Fin (W a).k => MvPolynomial.X (slot_of a j.val j.isLt)) (W a).p
      refine ⟨q, ?_⟩
      have hFSg : FS i = g := by simp [FS, h0]
      rw [hFSg, hantideriv a, (W a).hfin, hadamardEval_aeval, hadamardEval_aeval]
      dsimp only [q]
      rw [MvPolynomial.comp_aeval_apply]
      have hassign : (fun j : Fin (W a).k => FS (slot_of a j.val j.isLt)) = fun i => (W a).fs i := by
        funext j
        rw [hFS_slot]
      simp [MvPolynomial.aeval_X, hassign]
    · -- `i` is a non-`g` slot: `FS i = (W b).fs ⟨j, hj⟩`; its left derivative is a Hadamard
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
      -- `i` is the non-`g` slot for `(b, jnat)`, i.e. `i = slot_of b jnat hj`.
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
        aeval (fun j' : Fin (W b).k => MvPolynomial.X (slot_of b j'.val j'.isLt)) q'
      refine ⟨q, ?_⟩
      rw [hFSi, hq', hadamardEval_aeval, hadamardEval_aeval]
      dsimp only [q]
      rw [MvPolynomial.comp_aeval_apply]
      have hassign : (fun j' : Fin (W b).k => FS (slot_of b j'.val j'.isLt)) = fun i => (W b).fs i := by
        funext j'
        rw [hFS_slot]
      simp [MvPolynomial.aeval_X, hassign]
  exact ⟨1 + M, FS, MvPolynomial.X ⟨0, by omega⟩, hfin_g, hclose_FS⟩

/-! ### The orbit ideal chain (zeroness via Hilbert's basis theorem) -/

/-- The initial configuration `X_1` (the first nonterminal). -/
private noncomputable def X0 (A : HadamardAutomaton α) : MvPolynomial (Fin A.dim) ℚ :=
  X (Fin.mk 0 A.hdim)

/-- The *cumulative orbit*: the configurations reachable from `X_1` by words of length `≤ n`.
    `orbitSet A 0 = {X_1}` and `orbitSet A (n+1) = orbitSet A n ∪ ⋃ₐ Δₐ(orbitSet A n)`
    (append one letter to every reachable configuration).  Finite because the alphabet is. -/
noncomputable def orbitSet (A : HadamardAutomaton α) [Fintype α] :
    ℕ → Finset (MvPolynomial (Fin A.dim) ℚ)
  | 0 => {X0 A}
  | n + 1 => orbitSet A n ∪ Finset.biUnion Finset.univ (fun a => (orbitSet A n).image (aeval (A.Δ a)))

/-- The *orbit ideal* `I_n`: the ideal generated by the configurations reachable from `X_1`
    by words of length `≤ n`. -/
noncomputable def orbitIdeal (A : HadamardAutomaton α) [Fintype α] (n : ℕ) :
    Ideal (MvPolynomial (Fin A.dim) ℚ) :=
  Ideal.span (orbitSet A n)

/-- The orbit is cumulative: `orbitSet A n ⊆ orbitSet A (n+1)`. -/
private theorem orbitSet_mono (A : HadamardAutomaton α) [Fintype α] (n : ℕ) :
    orbitSet A n ⊆ orbitSet A (n+1) := by
  dsimp [orbitSet]
  exact Finset.subset_union_left

/-- Appending a letter stays within the next orbit level:
    `Δₐ(orbitSet A n) ⊆ orbitSet A (n+1)`. -/
private theorem orbitSet_image (A : HadamardAutomaton α) [Fintype α] (a : α) (n : ℕ) :
    (orbitSet A n).image (aeval (A.Δ a)) ⊆ orbitSet A (n+1) := by
  dsimp [orbitSet]
  intro x hx
  apply Finset.mem_union_right
  rw [Finset.mem_biUnion]
  exact ⟨a, Finset.mem_univ a, hx⟩

/-- The orbit ideals form an ascending chain: `I_n ≤ I_{n+1}`. -/
private theorem orbitIdeal_mono (A : HadamardAutomaton α) [Fintype α] (n : ℕ) :
    orbitIdeal A n ≤ orbitIdeal A (n+1) := by
  rw [orbitIdeal, orbitIdeal]
  exact Ideal.span_mono (orbitSet_mono A n)

/-- The transition invariance: applying a letter to a configuration in the depth-`≤ n` orbit
    ideal lands in the depth-`≤ (n+1)` orbit ideal, `Δₐ(I_n) ⊆ I_{n+1}`.  The image of a
    generated ideal under a ring hom is contained in the ideal generated by the image
    (`Ideal.map_span`, no surjectivity needed); the image of the orbit set lands one level up
    (`orbitSet_image`). -/
private theorem orbitIdeal_image (A : HadamardAutomaton α) [Fintype α] (a : α) (n : ℕ)
    (p : MvPolynomial (Fin A.dim) ℚ) (hp : p ∈ orbitIdeal A n) :
    aeval (A.Δ a) p ∈ orbitIdeal A (n+1) := by
  let f := (aeval (A.Δ a) : MvPolynomial (Fin A.dim) ℚ →ₐ[ℚ] MvPolynomial (Fin A.dim) ℚ)
  -- `f p` lies in the image-ideal `(orbitIdeal A n).map f`.
  have himap : f p ∈ (orbitIdeal A n).map f := Ideal.mem_map_of_mem f hp
  -- `map f (span s) = span (f '' s)` (no surjectivity needed).
  have hmap : (orbitIdeal A n).map f = Ideal.span (f '' ↑(orbitSet A n)) := by
    rw [orbitIdeal, Ideal.map_span]
  -- `f '' orbitSet A n ⊆ orbitSet A (n+1)` (appending a letter stays in the next level).
  have hsub : f '' ↑(orbitSet A n) ⊆ ↑(orbitSet A (n+1)) := by
    rw [← Finset.coe_image]
    exact orbitSet_image A a n
  -- Hence `f p ∈ Ideal.span (f '' orbitSet A n) ≤ Ideal.span (orbitSet A (n+1))`.
  have hspan : f p ∈ Ideal.span (f '' ↑(orbitSet A n)) := by
    rw [← hmap]
    exact himap
  have hnext : Ideal.span (f '' ↑(orbitSet A n)) ≤ Ideal.span (↑(orbitSet A (n+1))) :=
    Ideal.span_mono hsub
  exact mem_of_le_of_mem hnext hspan

/-! ### The kernel of the final-weight functional -/

/-- The final-weight functional as a `ℚ`-algebra homomorphism:
    `F_hom A p = aeval (A.F) p = eval (A.F) p`, the evaluation of the configuration
    `p` at the point `(A.F 0, …, A.F (dim-1))`. -/
noncomputable def F_hom (A : HadamardAutomaton α) :
    MvPolynomial (Fin A.dim) ℚ →ₐ[ℚ] ℚ :=
  aeval (A.F)

/-- The kernel of the final-weight functional: the ideal of configurations that
    evaluate to `0` under `F`. -/
noncomputable def K (A : HadamardAutomaton α) : Ideal (MvPolynomial (Fin A.dim) ℚ) :=
  RingHom.ker (F_hom A)

/-- A configuration lies in the kernel iff it evaluates to `0`:
    `p ∈ K A ↔ eval (A.F) p = 0`. -/
private theorem kerMem_eval (A : HadamardAutomaton α) (p : MvPolynomial (Fin A.dim) ℚ) :
    p ∈ K A ↔ eval (A.F) p = 0 := by
  rw [K, F_hom, RingHom.mem_ker]
  simp [aeval_eq_eval]

/-! ### Stabilisation of the orbit-ideal chain (Hilbert's basis theorem) -/

/-- The configuration ring is Noetherian: a polynomial ring over a Noetherian ring in
    finitely many variables is Noetherian (`isNoetherianRing_fin`), and `ℚ` is a field,
    hence Noetherian. -/
private theorem noetherian (A : HadamardAutomaton α) :
    IsNoetherianRing (MvPolynomial (Fin A.dim) ℚ) :=
  isNoetherianRing_fin

/-- The orbit ideals form a monotone (ascending) chain. -/
private theorem orbitIdeal_monotone (A : HadamardAutomaton α) [Fintype α] :
    Monotone (fun n => orbitIdeal A n) := by
  intro a b hab
  exact Nat.le_induction (le_rfl) (fun n _ hn => le_trans hn (orbitIdeal_mono A n)) b hab

/-- The orbit-ideal chain stabilises (Noetherianity): there is an `N` such that
    `I_N = I_m` for all `m ≥ N`. -/
private theorem orbitIdeal_stabilises (A : HadamardAutomaton α) [Fintype α] :
    ∃ N, ∀ m, N ≤ m → orbitIdeal A N = orbitIdeal A m := by
  let R := MvPolynomial (Fin A.dim) ℚ
  obtain ⟨N, hN⟩ :=
    monotone_stabilizes_iff_noetherian.mpr (isNoetherianRing_iff.mp (noetherian A))
      (⟨fun n => orbitIdeal A n, orbitIdeal_monotone A⟩)
  exact ⟨N, fun m hm => hN m hm⟩

/-- A stabilisation point of the orbit-ideal chain. -/
noncomputable def orbitIdeal_stab (A : HadamardAutomaton α) [Fintype α] : ℕ :=
  Classical.choose (orbitIdeal_stabilises A)

/-- At the stabilisation point the chain is constant: `I_N = I_m` for all `m ≥ N`. -/
private theorem orbitIdeal_stab_spec (A : HadamardAutomaton α) [Fintype α] :
    ∀ m, orbitIdeal_stab A ≤ m → orbitIdeal A (orbitIdeal_stab A) = orbitIdeal A m :=
  Classical.choose_spec (orbitIdeal_stabilises A)

/-! ### The stabilised orbit ideal is a bi-ideal -/

/-- The initial configuration lies in the orbit ideal at every level. -/
private theorem X0_in_orbitSet (A : HadamardAutomaton α) [Fintype α] (n : ℕ) :
    X0 A ∈ orbitSet A n := by
  induction n with
  | zero =>
      dsimp [orbitSet]
      simp
  | succ n ih =>
      dsimp [orbitSet]
      exact Finset.mem_union_left _ ih

/-- The initial configuration lies in the stabilised orbit ideal. -/
private theorem X0_in_orbitIdeal (A : HadamardAutomaton α) [Fintype α] :
    X0 A ∈ orbitIdeal A (orbitIdeal_stab A) := by
  rw [orbitIdeal]
  have h : X0 A ∈ ↑(orbitSet A (orbitIdeal_stab A)) := by
    simpa using X0_in_orbitSet A (orbitIdeal_stab A)
  exact Submodule.subset_span h

/-- The stabilised orbit ideal is invariant under every letter transition
    (`Δₐ(I_N) ⊆ I_N`): the image lands one level up (`orbitIdeal_image`), which
    equals `I_N` at the stabilisation point. -/
private theorem orbitIdeal_stab_invariant (A : HadamardAutomaton α) [Fintype α]
    (a : α) (p : MvPolynomial (Fin A.dim) ℚ) (hp : p ∈ orbitIdeal A (orbitIdeal_stab A)) :
    aeval (A.Δ a) p ∈ orbitIdeal A (orbitIdeal_stab A) := by
  have h1 : aeval (A.Δ a) p ∈ orbitIdeal A (orbitIdeal_stab A + 1) :=
    orbitIdeal_image A a (orbitIdeal_stab A) p hp
  have h2 : orbitIdeal A (orbitIdeal_stab A + 1) = orbitIdeal A (orbitIdeal_stab A) :=
    (orbitIdeal_stab_spec A (orbitIdeal_stab A + 1) (Nat.le_succ (orbitIdeal_stab A))).symm
  rw [← h2]
  exact h1

/-- The word endomorphism preserves the stabilised orbit ideal: if `p` is in the
    ideal, so is `Δ_w p`.  Each letter endomorphism preserves the ideal
    (`orbitIdeal_stab_invariant`), and the word map composes them. -/
private theorem Mword_preserves_orbitIdeal (A : HadamardAutomaton α) [Fintype α] (w : List α) :
    ∀ p, p ∈ orbitIdeal A (orbitIdeal_stab A) → A.Mword w p ∈ orbitIdeal A (orbitIdeal_stab A) := by
  induction w with
  | nil =>
      intro p hp
      rw [Mword_nil]
      exact hp
  | cons a w ih =>
      intro p hp
      rw [Mword_cons, Function.comp_apply]
      have h1 : aeval (A.Δ a) p ∈ orbitIdeal A (orbitIdeal_stab A) :=
        orbitIdeal_stab_invariant A a p hp
      exact ih (aeval (A.Δ a) p) h1

/-- Every reachable configuration lies in the stabilised orbit ideal: the word map
    preserves the ideal and `X_1` is in it. -/
private theorem Mword_mem_orbitIdeal (A : HadamardAutomaton α) [Fintype α] (w : List α) :
    A.Mword w (X0 A) ∈ orbitIdeal A (orbitIdeal_stab A) :=
  Mword_preserves_orbitIdeal A w (X0 A) (X0_in_orbitIdeal A)

/-! ### The orbit set is reachable, and the zeroness characterisation -/

/-- Every configuration in the depth-`≤ n` orbit set is reachable from `X_1` by some
    word: `p ∈ orbitSet A n → ∃ w, p = Δ_w X_1`. -/
private theorem orbitSet_reachable (A : HadamardAutomaton α) [Fintype α] (n : ℕ) :
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
          rw [← hqimg, hw, Mword_append, Mword_singleton, Function.comp_apply]
          rfl⟩

/-- The recognised series is zero iff every reachable configuration lies in the kernel:
    `A.recognised = 0 ↔ ∀ w, Δ_w X_1 ∈ K A`.  The coefficient of `w` in the recognised
    series is `F(Δ_w X_1)`, which is `0` exactly when `Δ_w X_1` is in the kernel. -/
private theorem recognised_zero_iff_allInK (A : HadamardAutomaton α) :
    A.recognised = 0 ↔ ∀ w, A.Mword w (X0 A) ∈ K A := by
  constructor
  · intro h w
    have hw : A.recognised w = 0 := by
      rw [h]
      simp
    have hsem : A.recognised w = eval (A.F) (A.Mword w (X0 A)) := by
      simp [HadamardAutomaton.recognised, HadamardAutomaton.sem, X0]
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
private theorem zeroness_iff_orbitSet (A : HadamardAutomaton α) [Fintype α] :
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
noncomputable def gensKer (A : HadamardAutomaton α) : Finset (MvPolynomial (Fin A.dim) ℚ) :=
  letI _ : IsNoetherianRing (MvPolynomial (Fin A.dim) ℚ) := noetherian A
  Classical.choose (Ideal.fg_of_isNoetherianRing (K A))

/-- The kernel is exactly the ideal generated by `gensKer A`. -/
private theorem gensKer_spec (A : HadamardAutomaton α) :
    Ideal.span ↑(gensKer A) = K A := by
  letI _ : IsNoetherianRing (MvPolynomial (Fin A.dim) ℚ) := noetherian A
  exact Classical.choose_spec (Ideal.fg_of_isNoetherianRing (K A))

/-- A `Decidable` cast to a `Bool` that is `true` exactly when the proposition holds:
    the Boolean value `d.casesOn (· => false) (· => true)` is `true` iff `P`. -/
private theorem decBool_true {P : Prop} (d : Decidable P) :
    d.casesOn (fun _ => false) (fun _ => true) = true ↔ P := by
  cases d with
  | isTrue h =>
      simp
      exact h
  | isFalse h =>
      simp
      exact h

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

/-- The per-configuration decision: `orbitDec A p` is `true` exactly when `p` lies in
    the ideal generated by `gensKer A` — the open leaf `IdealMembershipDecidable`. -/
private noncomputable def orbitDec (A : HadamardAutomaton α) (p : MvPolynomial (Fin A.dim) ℚ) : Bool :=
  (IdealMembershipDecidable A.dim (gensKer A) p).casesOn (fun _ => false) (fun _ => true)

/-- `orbitDec A p = true ↔ p ∈ K A`: the leaf decides `p ∈ span ↑(gensKer A)`, which
    is exactly the kernel `K A` (`gensKer_spec`). -/
private theorem orbitDec_iff (A : HadamardAutomaton α) (p : MvPolynomial (Fin A.dim) ℚ) :
    orbitDec A p = true ↔ p ∈ K A := by
  dsimp [orbitDec]
  rw [decBool_true (IdealMembershipDecidable A.dim (gensKer A) p), ← gensKer_spec A]

/--
---
conclusion: Lax619925.Hadamard.HadamardEqualityDecidable
---
The equality (zeroness) problem is decidable for Hadamard automata over a finite
alphabet (paper §5).  The orbit-ideal chain `I_n` stabilises by Hilbert's basis
theorem (`orbitIdeal_stabilises`), and the stabilised ideal is a bi-ideal, so the
zeroness of the recognised series is characterised by the finite statement
`∀ p ∈ orbitSet A N, p ∈ K A` (`zeroness_iff_orbitSet`).  The kernel `K A` is
finitely generated (`gensKer`, by Noetherianity), so this finite statement is a
batch of ideal-membership queries `p ∈ span ↑(gensKer A)`, each decided by the
open leaf `IdealMembershipDecidable`; the decision `d` is the Boolean "and" of
these queries over the (finite) orbit set.
-/
theorem HadamardEqualityDecidable [Fintype α] :
    ∃ d : HadamardAutomaton α → Bool, ∀ A, d A = true ↔ A.recognised = 0 := by
  let d : HadamardAutomaton α → Bool := fun A =>
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

/-! ### The effective prevariety of Hadamard-finite series -/

/-- The top prevariety: the whole space of series, trivially closed under the
    derivatives.  Serves as the `prevariety` field of the Hadamard effective
    prevariety (the image of the semantics is a prevariety; the top space is the
    coarsest such). -/
private def topPrevariety (α : Type*) : Prevariety α :=
  { carrier := ⊤,
    closedLeftDeriv := fun _ _ => Submodule.mem_top,
    closedRightDeriv := fun _ _ => Submodule.mem_top }

/-- The left derivative of a Hadamard-finite series is Hadamard-finite: the
    witnessing tuple is unchanged, and the polynomial is pre-composed with the
    left-derivative polynomials of the generators (`leftDeriv_hadamardEval` and
    `hadamardEval_subst`). -/
private theorem leftDeriv_hadamardFinite (f : Series α) (hf : IsHadamardFinite α f) (a : α) :
    IsHadamardFinite α (leftDeriv α a f) := by
  obtain ⟨k, fs, p, hfp, hfc⟩ := hf
  let q : Fin k → MvPolynomial (Fin k) ℚ := fun i => Classical.choose (hfc a i)
  have hq : ∀ i, leftDeriv α a (fs i) = hadamardEval α k fs (q i) := by
    intro i
    dsimp [q]
    exact Classical.choose_spec (hfc a i)
  refine ⟨k, fs, aeval q p, ?_, hfc⟩
  calc
    leftDeriv α a f = leftDeriv α a (hadamardEval α k fs p) := by rw [← hfp]
    _ = hadamardEval α k (fun i => leftDeriv α a (fs i)) p := by rw [leftDeriv_hadamardEval]
    _ = hadamardEval α k (fun i => hadamardEval α k fs (q i)) p := by
      congr; funext i; exact hq i
    _ = hadamardEval α k fs (aeval q p) := by rw [hadamardEval_subst _ _ (fun _ => q) a p]

/-- A Hadamard automaton recognising the zero series: one nonterminal, zero final
    weight, and zero transitions (the configuration is `0` after any non-empty word,
    and the empty word evaluates to `F 0 = 0`).  Takes `α` explicitly so that the
    projection `zeroAutomaton α .recognised` elaborates (a top-level `def` bound to
    the implicit `α` would not). -/
noncomputable def zeroAutomaton (α : Type*) : HadamardAutomaton α :=
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
      dsimp [HadamardAutomaton.recognised, HadamardAutomaton.sem, zeroAutomaton]
      rw [Mword_nil]
      simp
  | cons a w' =>
      dsimp [HadamardAutomaton.recognised, HadamardAutomaton.sem]
      rw [Mword_cons]
      simp only [Function.comp_apply]
      have h : (aeval ((zeroAutomaton α).Δ a) : MvPolynomial (Fin (zeroAutomaton α).dim) ℚ → MvPolynomial (Fin (zeroAutomaton α).dim) ℚ)
          (MvPolynomial.X (Fin.mk 0 (zeroAutomaton α).hdim)) = 0 := by
        change (aeval (fun (i : Fin 1) => (0 : MvPolynomial (Fin 1) ℚ)) : MvPolynomial (Fin 1) ℚ → MvPolynomial (Fin 1) ℚ)
            (MvPolynomial.X (0 : Fin 1)) = 0
        rw [aeval_X]
      rw [h]
      have h0 : (zeroAutomaton α).Mword w' 0 = 0 := by
        rw [← MwordAlg_apply (zeroAutomaton α) w' 0]
        simp
      rw [h0]
      simp

/-- `A.recognised` is Hadamard-finite (by the coincidence, from recognisability). -/
private theorem recognised_hadamardFinite (A : HadamardAutomaton α) :
    IsHadamardFinite α A.recognised :=
  finite_of_recognisable _ ⟨A, rfl⟩

/-- The sum of two recognised series is Hadamard-recognisable. -/
private theorem addRecognisable (A B : HadamardAutomaton α) :
    IsHadamardRecognisable α (A.recognised + B.recognised) :=
  (HadamardCoincidence _).mp
    (HadamardClosure.1 _ _ (recognised_hadamardFinite A) (recognised_hadamardFinite B))

/-- The scalar multiple of a recognised series is Hadamard-recognisable. -/
private theorem smulRecognisable (c : ℚ) (A : HadamardAutomaton α) :
    IsHadamardRecognisable α (c • A.recognised) :=
  (HadamardCoincidence _).mp
    (HadamardClosure.2.1 _ _ (recognised_hadamardFinite A))

/-- The left derivative of a recognised series is Hadamard-recognisable. -/
private theorem derivLRecognisable (a : α) (A : HadamardAutomaton α) :
    IsHadamardRecognisable α (leftDeriv α a A.recognised) :=
  (HadamardCoincidence _).mp
    (leftDeriv_hadamardFinite _ (recognised_hadamardFinite A) a)

/-- The sum automaton: recognises `A.recognised + B.recognised`. -/
noncomputable def addAutomaton (A B : HadamardAutomaton α) : HadamardAutomaton α :=
  Classical.choose (addRecognisable A B)

/-- The scalar-multiple automaton: recognises `c • A.recognised`. -/
noncomputable def smulAutomaton (c : ℚ) (A : HadamardAutomaton α) : HadamardAutomaton α :=
  Classical.choose (smulRecognisable c A)

/-- The left-derivative automaton: recognises `leftDeriv a (A.recognised)`. -/
noncomputable def derivLAutomaton (a : α) (A : HadamardAutomaton α) : HadamardAutomaton α :=
  Classical.choose (derivLRecognisable a A)

private theorem addAutomaton_spec (A B : HadamardAutomaton α) :
    (addAutomaton A B).recognised = A.recognised + B.recognised := by
  dsimp [addAutomaton]
  exact Classical.choose_spec (addRecognisable A B)

private theorem smulAutomaton_spec (c : ℚ) (A : HadamardAutomaton α) :
    (smulAutomaton c A).recognised = c • A.recognised := by
  dsimp [smulAutomaton]
  exact Classical.choose_spec (smulRecognisable c A)

private theorem derivLAutomaton_spec (a : α) (A : HadamardAutomaton α) :
    (derivLAutomaton a A).recognised = leftDeriv α a A.recognised := by
  dsimp [derivLAutomaton]
  exact Classical.choose_spec (derivLRecognisable a A)

/-- The effective prevariety of Hadamard-finite series: presentations are Hadamard
    automata, the semantics is the recognised series, and the operations are carried
    out by the (classically chosen) closure automata.  Equality is decided by the
    zeroness decision applied to `A - B` (`HadamardEqualityDecidable`). -/
noncomputable def hadamardEffectivePrevariety [Fintype α] : EffectivePrevariety α :=
  { Rep := HadamardAutomaton α,
    sem := fun A => A.recognised,
    prevariety := topPrevariety α,
    mem := fun A => by
      change A.recognised ∈ (⊤ : Submodule ℚ (Series α))
      exact Submodule.mem_top
    zero := zeroAutomaton α,
    add := addAutomaton,
    smul := smulAutomaton,
    derivL := derivLAutomaton,
    derivR := fun a A => rightDerivAutomaton A a,
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
      change (rightDerivAutomaton A a).recognised = rightDeriv α a (A.recognised)
      exact rightDeriv_recognised A a
    decEq := fun A B => by
      let d := Classical.choose (HadamardEqualityDecidable (α := α))
      let hd := Classical.choose_spec (HadamardEqualityDecidable (α := α))
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
conclusion: Lax619925.Hadamard.HadamardEffectivePrevariety
---
The Hadamard-finite series form an effective prevariety over a finite alphabet
(paper §5, theorem): the effective prevariety `hadamardEffectivePrevariety` has
presentations given by Hadamard automata, and its image is exactly the
Hadamard-finite series (by the coincidence, `HadamardCoincidence`).
-/
theorem HadamardEffectivePrevariety [Fintype α] :
    ∃ P : EffectivePrevariety α, ∀ f, IsHadamardFinite α f ↔ ∃ r : P.Rep, P.sem r = f := by
  refine ⟨hadamardEffectivePrevariety, ?_⟩
  intro f
  change IsHadamardFinite α f ↔ ∃ A : HadamardAutomaton α, A.recognised = f
  exact HadamardCoincidence f

/--
---
conclusion: Lax619925.Hadamard.HadamardCommutativityDecidable
---
The commutativity problem is decidable for Hadamard-finite series over a finite
alphabet (paper §5).  This is the meta-theorem
(`EffectivePrevarietyCommutativityDecidable`) applied to
`hadamardEffectivePrevariety`, the effective prevariety of Hadamard-finite
series: its boolean decider on a presentation `A` decides
`IsCommutative (hadamardEffectivePrevariety.sem A)`, and since
`hadamardEffectivePrevariety.sem A = A.recognised`, it decides
`IsCommutative (A.recognised)`.
-/
theorem HadamardCommutativityDecidable [Fintype α] :
    ∃ d : HadamardAutomaton α → Bool, ∀ A, d A = true ↔ IsCommutative α (A.recognised) := by
  obtain ⟨d, hd⟩ := EffectivePrevarietyCommutativityDecidable (α := α) hadamardEffectivePrevariety
  refine ⟨fun (A : HadamardAutomaton α) => d A, fun A => ?_⟩
  have hsem : hadamardEffectivePrevariety.sem A = A.recognised := by
    dsimp only [hadamardEffectivePrevariety]
  simpa [hsem] using hd A

end Lax619925Proofs.Hadamard
