import Lax619925.Polyrec
import Lax619925.Hadamard
import Lax619925.Series
import Lax619925Proofs.Hadamard
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Finsupp.Basic
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Data.Bool.Basic
import Mathlib.Tactic

/-!
Polyrec consistency (paper §5.4, theorem `polyrec consistency`): a multivariate
polynomial recursive sequence system is isomorphic to a Hadamard system over the
`d`-letter alphabet, so a solution exists exactly when the companion Hadamard
series are commutative, which is decidable.

The isomorphism is the Parikh image: a sequence `f : ℕ^d → ℚ` and a commutative
series `g : (Fin d)^* → ℚ` carry the same information (`f n = g` on the word with
Parikh image `n`), and the isomorphism sends the shift `shift_j` to the left
derivative `leftDeriv a_j` and the pointwise product to the Hadamard product.

The companion Hadamard automaton of a polyrec system `(p, c)` has nonterminals
`X_1, …, X_k`, output `F X_i = c_i`, and transitions `Δ_{a_j} X_i = p^{(j)}_i`.
Its semantics `g_i = ⟦A⟧_{X_i}` is the unique solution of the companion system;
the initial condition extends to a polyrec solution iff all `g_i` are commutative.
-/

namespace Lax619925Proofs.Polyrec

open Lax619925.Polyrec Lax619925.Hadamard Lax619925.Series
open Lax619925Proofs.Hadamard
open MvPolynomial

/-! ### The Parikh-image isomorphism -/

/-- A word whose multiset of letters is `∑_i n_i · {i}` (hence whose Parikh image is
    `n`).  The list order is immaterial: only the multiset, i.e. the Parikh image,
    matters for commutative series. -/
noncomputable def wordFromParikh (d : ℕ) (n : Fin d → ℕ) : List (Fin d) :=
  ((Finset.univ : Finset (Fin d)).sum (fun i => Multiset.replicate (n i) i)).toList

/-- Lift a sequence to a (necessarily commutative) series: the coefficient of the
    word `w` is the sequence value at the Parikh image of `w`. -/
def toSeries (d : ℕ) (f : Lax619925.Polyrec.Seq d) : Series (Fin d) := fun w => f (parikh (Fin d) w)

/-- Project a (commutative) series to a sequence: the value at the multi-index `n`
    is the series value at a word with Parikh image `n`. -/
noncomputable def toSeq (d : ℕ) (g : Series (Fin d)) : Lax619925.Polyrec.Seq d := fun n => g (wordFromParikh d n)

/-- `wordFromParikh` has the intended Parikh image: `parikh (wordFromParikh n) = n`. -/
private theorem wordFromParikh_parikh (d : ℕ) (n : Fin d → ℕ) :
    parikh (Fin d) (wordFromParikh d n) = n := by
  funext j
  simp [wordFromParikh, parikh]
  rw [← Multiset.coe_count, Multiset.coe_toList]
  have : ∀ (s : Finset (Fin d)) (f : Fin d → Multiset (Fin d)),
      (s.sum f).count j = s.sum (fun i => (f i).count j) := by
    intro s f
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih => rw [Finset.sum_insert ha, Multiset.count_add, ih, Finset.sum_insert ha]
  rw [this]
  simp [Multiset.count_replicate]

/-- The Parikh image of a cons is the Parikh image of the tail plus one at the head:
    `parikh (a · w) = parikh w + e_a`. -/
private theorem parikh_cons (d : ℕ) (j : Fin d) (w : List (Fin d)) :
    parikh (Fin d) (j :: w) = parikh (Fin d) w + (fun i => if i = j then 1 else 0) := by
  funext i
  simp [parikh, List.count_cons]
  by_cases h : i = j
  · simp [h]
  · simp [h, Ne.symm h]

/-- Lifting then projecting is the identity on sequences. -/
private theorem toSeq_toSeries (d : ℕ) (f : Lax619925.Polyrec.Seq d) : toSeq d (toSeries d f) = f := by
  funext n
  dsimp [toSeq, toSeries]
  rw [wordFromParikh_parikh]

/-- Projecting then lifting is the identity on commutative series. -/
private theorem toSeries_toSeq (d : ℕ) (g : Series (Fin d)) (hg : IsCommutative (Fin d) g) :
    toSeries d (toSeq d g) = g := by
  funext w
  dsimp [toSeries, toSeq]
  have hce : CommutativelyEquivalent (Fin d) (wordFromParikh d (parikh (Fin d) w)) w := by
    rw [CommutativelyEquivalent, Multiset.ext]
    intro a
    rw [Multiset.coe_count, Multiset.coe_count]
    have hpar : parikh (Fin d) (wordFromParikh d (parikh (Fin d) w)) = parikh (Fin d) w := by
      rw [wordFromParikh_parikh]
    simpa [parikh] using congrArg (fun f : Fin d → ℕ => f a) hpar
  simpa [hce] using hg _ _ hce

/-- The lift of a shift is the left derivative of the lift:
    `toSeries (shift_j f) = leftDeriv a_j (toSeries f)`. -/
private theorem toSeries_shift (d : ℕ) (j : Fin d) (f : Lax619925.Polyrec.Seq d) :
    toSeries d (shift d j f) = leftDeriv (Fin d) j (toSeries d f) := by
  funext w
  dsimp [toSeries, shift, leftDeriv]
  rw [parikh_cons]
  congr

/-- The lift of the pointwise (Hadamard-algebra) evaluation is the Hadamard-algebra
    evaluation of the lifts. -/
private theorem toSeries_evalSeq (d k : ℕ) (fs : Fin k → Lax619925.Polyrec.Seq d) (p : MvPolynomial (Fin k) ℚ) :
    toSeries d (evalSeq d k fs p) = hadamardEval (Fin d) k (fun i => toSeries d (fs i)) p := by
  funext w
  simp [toSeries, evalSeq, hadamardEval]

/-- The lift of a sequence is a commutative series (it is constant on words with the
    same Parikh image). -/
private theorem toSeries_commutative (d : ℕ) (f : Lax619925.Polyrec.Seq d) : IsCommutative (Fin d) (toSeries d f) := by
  intro u v hce
  dsimp [IsCommutative, toSeries]
  have hpar : parikh (Fin d) u = parikh (Fin d) v := by
    funext a
    rw [parikh, parikh, ← Multiset.coe_count, ← Multiset.coe_count, hce]
  rw [hpar]

/-! ### The companion Hadamard automaton -/

/-- The companion Hadamard automaton of a polyrec system `(p, c)`: `k` nonterminals,
    output `F X_i = c_i`, transitions `Δ_{a_j} X_i = p^{(j)}_i`. -/
abbrev companionAutomaton (d k : ℕ) (_hd : 0 < d) (hk : 0 < k)
    (p : Fin k → Fin d → MvPolynomial (Fin k) ℚ) (c : Fin k → ℚ) :
    HadamardAutomaton (Fin d) :=
  { dim := k, hdim := hk, F := c, Δ := fun j i => p i j }

/-- A tuple `g` of series *solves the companion system* of `(p, c)`: it satisfies the
    initial condition `g_i(ε) = c_i` and the Hadamard equations
    `leftDeriv a_j g_i = p^{(j)}_i(g_1, …, g_k)` (the Hadamard-algebra evaluation). -/
def SolvesCompanion (d k : ℕ) (g : Fin k → Series (Fin d))
    (p : Fin k → Fin d → MvPolynomial (Fin k) ℚ) (c : Fin k → ℚ) : Prop :=
  (∀ i, g i [] = c i) ∧ ∀ i j, leftDeriv (Fin d) j (g i) = hadamardEval (Fin d) k g (p i j)

/-- The semantics of the companion automaton at `X_i` solves the companion system. -/
private theorem companion_solves (d k : ℕ) (hd : 0 < d) (hk : 0 < k)
    (p : Fin k → Fin d → MvPolynomial (Fin k) ℚ) (c : Fin k → ℚ) :
    SolvesCompanion d k (fun i => (companionAutomaton d k hd hk p c).sem (X i)) p c := by
  let A := companionAutomaton d k hd hk p c
  constructor
  · intro i
    dsimp [SolvesCompanion]
    have h : A.sem (X i) [] = MvPolynomial.eval (fun j => A.F j) (A.Mword [] (X i)) := rfl
    rw [h, Mword_nil]
    simp only [id]
    dsimp [A, companionAutomaton]
    change MvPolynomial.eval (fun j => c j) (X i) = c i
    rw [MvPolynomial.eval_X]
  · intro i j
    dsimp [SolvesCompanion]
    have h1 : leftDeriv (Fin d) j (A.sem (X i)) = A.sem (aeval (A.Δ j) (X i)) := sem_deriv A j (X i)
    have h3 : A.sem (A.Δ j i) = hadamardEval (Fin d) A.dim (fun j' => A.sem (X j')) (A.Δ j i) := by
      rw [sem_aeval, ← hadamardEval_aeval]
    calc
      leftDeriv (Fin d) j (A.sem (X i)) = A.sem (aeval (A.Δ j) (X i)) := h1
      _ = A.sem (A.Δ j i) := by rw [MvPolynomial.aeval_X]
      _ = hadamardEval (Fin d) A.dim (fun j' => A.sem (X j')) (A.Δ j i) := h3
      _ = hadamardEval (Fin d) k (fun j' => A.sem (X j')) (p i j) := by
        dsimp [A]

/-- The companion system has a unique solution: two solutions agree on every word, by
    induction on the word length (the value at `a·w` is determined by the values at `w`). -/
private theorem companion_unique (d k : ℕ)
    (p : Fin k → Fin d → MvPolynomial (Fin k) ℚ) (c : Fin k → ℚ)
    (g h : Fin k → Series (Fin d)) (hg : SolvesCompanion d k g p c) (hh : SolvesCompanion d k h p c) :
    g = h := by
  have hmain : ∀ w i, g i w = h i w := by
    intro w
    induction w with
    | nil =>
        intro i
        rw [hg.1 i, hh.1 i]
    | cons a v ih =>
        intro i
        have hgi : g i (a :: v) = (leftDeriv (Fin d) a (g i)) v := by dsimp [leftDeriv]
        have hhi : h i (a :: v) = (leftDeriv (Fin d) a (h i)) v := by dsimp [leftDeriv]
        rw [hgi, hhi, hg.2 i a, hh.2 i a]
        have hsum : hadamardEval (Fin d) k g (p i a) v = hadamardEval (Fin d) k h (p i a) v := by
          dsimp [hadamardEval]
          apply Finset.sum_congr rfl
          intro m _
          have hprod : (∏ j : Fin k, (g j) v ^ m j) = (∏ j : Fin k, (h j) v ^ m j) := by
            apply Finset.prod_congr rfl
            intro j _
            rw [ih j]
          rw [hprod]
        simpa using hsum
  ext i w
  exact hmain w i

/-! ### The bridge: solvability ↔ all companion components commutative -/

/-- The initial condition `c` extends to a polyrec solution iff the companion
    automaton's component series are all commutative. -/
private theorem bridge (d k : ℕ) (hd : 0 < d) (hk : 0 < k)
    (p : Fin k → Fin d → MvPolynomial (Fin k) ℚ) (c : Fin k → ℚ) :
    (∃ f : Fin k → Lax619925.Polyrec.Seq d, SolvesPolyrec d k f p c) ↔
      ∀ i, IsCommutative (Fin d) ((companionAutomaton d k hd hk p c).sem (X i)) := by
  let A := companionAutomaton d k hd hk p c
  constructor
  · -- (→) a polyrec solution lifts to a commutative companion solution, hence equals the
    -- unique companion solution
    rintro ⟨f, hf⟩
    let gs := fun i => toSeries d (f i)
    have hgs : SolvesCompanion d k gs p c := by
      constructor
      · intro i
        dsimp [SolvesCompanion, gs, toSeries]
        have hpar : parikh (Fin d) [] = (0 : Fin d → ℕ) := by
          funext j; simp [parikh, List.count_nil]
        rw [hpar]
        simpa using hf.1 i
      · intro i j
        dsimp [SolvesCompanion, gs]
        calc
          leftDeriv (Fin d) j (toSeries d (f i)) = toSeries d (shift d j (f i)) :=
            (toSeries_shift d j (f i)).symm
          _ = toSeries d (evalSeq d k f (p i j)) := by
            rw [hf.2 i j]
          _ = hadamardEval (Fin d) k (fun i' => toSeries d (f i')) (p i j) :=
            toSeries_evalSeq d k f (p i j)
          _ = hadamardEval (Fin d) k gs (p i j) := by dsimp [gs]
    have hcomm : ∀ i, IsCommutative (Fin d) (gs i) := fun i => toSeries_commutative d (f i)
    have hgs_unique : gs = fun i => A.sem (X i) :=
      companion_unique d k p c gs (fun i => A.sem (X i)) hgs (companion_solves d k hd hk p c)
    intro i
    have h : gs i = A.sem (X i) := by rw [hgs_unique]
    simpa [h] using hcomm i
  · -- (←) commutative companion components project to a polyrec solution
    intro hcomm
    let f := fun i => toSeq d (A.sem (X i))
    have hf : SolvesPolyrec d k f p c := by
      constructor
      · intro i
        dsimp [SolvesPolyrec, f, toSeq]
        have hword : wordFromParikh d 0 = [] := by
          dsimp [wordFromParikh]
          simp
        calc
          (A.sem (X i)) (wordFromParikh d 0) = (A.sem (X i)) [] := by rw [hword]
          _ = c i := (companion_solves d k hd hk p c).1 i
      · intro i j
        dsimp [SolvesPolyrec, f]
        calc
          shift d j (toSeq d (A.sem (X i))) = toSeq d (toSeries d (shift d j (toSeq d (A.sem (X i))))) := by
            rw [toSeq_toSeries]
          _ = toSeq d (leftDeriv (Fin d) j (toSeries d (toSeq d (A.sem (X i))))) := by
            rw [← toSeries_shift d j (toSeq d (A.sem (X i)))]
          _ = toSeq d (leftDeriv (Fin d) j (A.sem (X i))) := by
            rw [toSeries_toSeq d (A.sem (X i)) (hcomm i)]
          _ = toSeq d (hadamardEval (Fin d) k (fun i' => A.sem (X i')) (p i j)) := by
            rw [← (companion_solves d k hd hk p c).2 i j]
          _ = toSeq d (toSeries d (evalSeq d k (fun i' => toSeq d (A.sem (X i'))) (p i j))) := by
            rw [toSeries_evalSeq d k (fun i' => toSeq d (A.sem (X i'))) (p i j)]
            congr 2
            funext i'
            rw [toSeries_toSeq d (A.sem (X i')) (hcomm i')]
          _ = evalSeq d k f (p i j) := by
            dsimp [f]
            rw [toSeq_toSeries]
    exact ⟨f, hf⟩

/-! ### Decidability of the commutative components -/

/-- `A.sem (X_i)` is Hadamard-finite: it is the Hadamard polynomial `X_i` in the
    left-derivative-closed tuple `(A.sem (X_0), …, A.sem (X_{k-1}))`. -/
private theorem hadamardFinite_sem (α : Type*) (A : HadamardAutomaton α) (i : Fin A.dim) :
    IsHadamardFinite α (A.sem (X i)) := by
  refine ⟨A.dim, fun j => A.sem (X j), X i, ?_, ?_⟩
  · rw [sem_aeval, hadamardEval_aeval]
  · intro a j
    refine ⟨A.Δ a j, ?_⟩
    calc
      leftDeriv α a (A.sem (X j)) = A.sem (aeval (A.Δ a) (X j)) := sem_deriv A a (X j)
      _ = A.sem (A.Δ a j) := by rw [MvPolynomial.aeval_X]
      _ = hadamardEval α A.dim (fun j' => A.sem (X j')) (A.Δ a j) := by
        rw [sem_aeval, ← hadamardEval_aeval]

/-- `A.sem (X_i)` is Hadamard-recognisable (by the coincidence, from Hadamard-finiteness). -/
private theorem recognisable_sem (α : Type*) (A : HadamardAutomaton α) (i : Fin A.dim) :
    IsHadamardRecognisable α (A.sem (X i)) :=
  (HadamardCoincidence α (A.sem (X i))).mp (hadamardFinite_sem α A i)

/-- An automaton whose recognised series is `A.sem (X_i)` (chosen by the axiom of choice). -/
noncomputable def companionComponent (α : Type*) (A : HadamardAutomaton α) (i : Fin A.dim) :
    HadamardAutomaton α := Classical.choose (recognisable_sem α A i)

private theorem companionComponent_spec (α : Type*) (A : HadamardAutomaton α) (i : Fin A.dim) :
    (companionComponent α A i).recognised = A.sem (X i) :=
  Classical.choose_spec (recognisable_sem α A i)

/-! ### The main theorem -/

/--
---
conclusion: Lax619925.Polyrec.PolyrecConsistency
assumptions:
  - Lax619925.Hadamard.HadamardCommutativityDecidable
  - Lax619925.Hadamard.HadamardCoincidence
---
The polyrec consistency problem is decidable (paper §5.4): the decision reduces to
checking that all components of the companion Hadamard automaton's recognised series
are commutative, each decided by `HadamardCommutativityDecidable` (the meta-theorem
applied to the effective prevariety of Hadamard-finite series).
-/
theorem PolyrecConsistency (d k : ℕ) (hd : 0 < d) (hk : 0 < k) :
    ∃ dec : (Fin k → Fin d → MvPolynomial (Fin k) ℚ) → (Fin k → ℚ) → Bool,
      ∀ p c, dec p c = true ↔ ∃ f : Fin k → Lax619925.Polyrec.Seq d, SolvesPolyrec d k f p c := by
  obtain ⟨dcomm, hdcomm⟩ := HadamardCommutativityDecidable (Fin d)
  let dec : (Fin k → Fin d → MvPolynomial (Fin k) ℚ) → (Fin k → ℚ) → Bool :=
    fun p c => decide (∀ i, dcomm (companionComponent (Fin d) (companionAutomaton d k hd hk p c) i) = true)
  refine ⟨dec, ?_⟩
  intro p c
  let A := companionAutomaton d k hd hk p c
  have hdec : dec p c = true ↔ ∀ i, IsCommutative (Fin d) (A.sem (X i)) := by
    dsimp [dec]
    rw [Bool.decide_iff]
    constructor
    · intro h i
      have := hdcomm (companionComponent (Fin d) A i)
      rw [companionComponent_spec (Fin d) A i] at this
      exact this.mp (h i)
    · intro h i
      have := hdcomm (companionComponent (Fin d) A i)
      rw [companionComponent_spec (Fin d) A i] at this
      exact this.mpr (h i)
  have hbridge : (∀ i, IsCommutative (Fin d) (A.sem (X i))) ↔
      ∃ f : Fin k → Lax619925.Polyrec.Seq d, SolvesPolyrec d k f p c :=
    (bridge d k hd hk p c).symm
  calc
    dec p c = true ↔ ∀ i, IsCommutative (Fin d) (A.sem (X i)) := hdec
    _ ↔ ∃ f : Fin k → Lax619925.Polyrec.Seq d, SolvesPolyrec d k f p c := hbridge

end Lax619925Proofs.Polyrec
