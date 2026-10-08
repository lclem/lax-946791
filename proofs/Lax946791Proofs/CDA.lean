import Lax946791.CDA
import Lax946791.Shuffle
import Lax946791.Series
import Lax946791Proofs.Shuffle
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Data.Bool.Basic
import Mathlib.Tactic

/-!
CDA solvability (paper §6.4, theorem `decidability of CDA solvability`): a
multivariate constructible differentially algebraic (CDA) power series system is
isomorphic to a shuffle system over the `d`-letter alphabet, so a solution exists
exactly when the companion shuffle series are commutative, which is decidable.

The isomorphism is the Parikh image: an exponential power series `f : ℕ^d → ℚ` and a
commutative series `g : (Fin d)^* → ℚ` carry the same information (`f n = g` on the
word with Parikh image `n`), and the isomorphism sends the partial derivative
`expDeriv_j` to the left derivative `leftDeriv a_j` and the binomial-convolution
product to the shuffle product.

The companion shuffle automaton of a CDA system `(p, c)` has nonterminals
`X_1, …, X_k`, output `F X_i = c_i`, and transitions `Δ_{a_j} X_i = p^{(j)}_i`.
Its semantics `g_i = ⟦A⟧_{X_i}` is the unique solution of the companion system;
the initial condition extends to a CDA solution iff all `g_i` are commutative.
-/

namespace Lax946791Proofs.CDA

open Lax946791.CDA Lax946791.Shuffle Lax946791.Series
open Lax946791Proofs.Shuffle
open MvPolynomial

/-! ### The Parikh-image isomorphism -/

/-- A word whose multiset of letters is `∑_i n_i · {i}` (hence whose Parikh image is
    `n`).  The list order is immaterial: only the multiset, i.e. the Parikh image,
    matters for commutative series. -/
noncomputable def wordFromParikh (d : ℕ) (n : Fin d → ℕ) : List (Fin d) :=
  ((Finset.univ : Finset (Fin d)).sum (fun i => Multiset.replicate (n i) i)).toList

/-- Lift an exponential power series to a (necessarily commutative) series: the
    coefficient of the word `w` is the series value at the Parikh image of `w`. -/
def toSeries (d : ℕ) (f : Lax946791.CDA.ExpPowerSeries d) : Series (Fin d) :=
  fun w => f (parikh (Fin d) w)

/-- Project a (commutative) series to an exponential power series: the value at the
    multi-index `n` is the series value at a word with Parikh image `n`. -/
noncomputable def toSeq (d : ℕ) (g : Series (Fin d)) : Lax946791.CDA.ExpPowerSeries d :=
  fun n => g (wordFromParikh d n)

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

/-- Lifting then projecting is the identity on exponential power series. -/
private theorem toSeq_toSeries (d : ℕ) (f : Lax946791.CDA.ExpPowerSeries d) :
    toSeq d (toSeries d f) = f := by
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

/-- The lift of a partial derivative is the left derivative of the lift:
    `toSeries (expDeriv_j f) = leftDeriv a_j (toSeries f)`.  Here `expDeriv` is
    definitionally the shift, so this is the same identity as the polyrec
    `toSeries_shift`. -/
private theorem toSeries_expDeriv (d : ℕ) (j : Fin d) (f : Lax946791.CDA.ExpPowerSeries d) :
    toSeries d (expDeriv d j f) = leftDeriv (Fin d) j (toSeries d f) := by
  funext w
  dsimp [toSeries, expDeriv, leftDeriv]
  rw [parikh_cons]
  congr

/-- The lift of a sum is the sum of the lifts (the Parikh lift is linear). -/
private theorem toSeries_add (d : ℕ) (f g : Lax946791.CDA.ExpPowerSeries d) :
    toSeries d (f + g) = toSeries d f + toSeries d g := by
  funext w
  dsimp [toSeries]

/-- The lift of a scalar multiple is the scalar multiple of the lift. -/
private theorem toSeries_smul (d : ℕ) (c : ℚ) (f : Lax946791.CDA.ExpPowerSeries d) :
    toSeries d (c • f) = c • toSeries d f := by
  funext w
  dsimp [toSeries]

/-- The lift of a sequence is a commutative series (it is constant on words with the
    same Parikh image). -/
private theorem toSeries_commutative (d : ℕ) (f : Lax946791.CDA.ExpPowerSeries d) :
    IsCommutative (Fin d) (toSeries d f) := by
  intro u v hce
  dsimp [IsCommutative, toSeries]
  have hpar : parikh (Fin d) u = parikh (Fin d) v := by
    funext a
    rw [parikh, parikh, ← Multiset.coe_count, ← Multiset.coe_count, hce]
  rw [hpar]

/-- The lift of the constant-1 exponential series is the shuffle unit: the constant-1
    series is `1` at the zero multi-index and `0` elsewhere, so its lift is `1` on the
    empty word and `0` elsewhere (the shuffle unit). -/
private theorem toSeries_unit (d : ℕ) :
    toSeries d (fun idx => if idx = 0 then 1 else 0) = shuffleUnit (Fin d) := by
  funext w
  dsimp [toSeries, shuffleUnit]
  have hpar : parikh (Fin d) w = 0 ↔ w = [] := by
    constructor
    · intro h
      by_contra hw
      have hmem : ∃ a, a ∈ w := by
        by_contra h
        push Not at h
        have hnil : w = [] := by
          induction w with
          | nil => rfl
          | cons a _ => exact (h a List.mem_cons_self).elim
        contradiction
      obtain ⟨a, ha⟩ := hmem
      have hcount : 0 < w.count a := List.count_pos_iff.mpr ha
      have hzero : w.count a = 0 := by
        have := congrFun h a
        simpa [parikh] using this
      linarith
    · intro h
      rw [h]
      ext a
      simp [parikh]
  by_cases hw : w = []
  · have h1 : parikh (Fin d) w = 0 := hpar.mpr hw
    subst hw
    simp [h1]
  · have hpar_ne : parikh (Fin d) w ≠ 0 := fun h => hw (hpar.mp h)
    simp [hw, hpar_ne]

/-! ### The binomial-convolution product is the shuffle product under the lift -/

private def cleanIdx (d : ℕ) (m : (a : Fin d) → a ∈ Finset.univ → ℕ) : Fin d → ℕ :=
  fun i => m i (Finset.mem_univ i)

private def weirdBox (d : ℕ) (n : Fin d → ℕ) : Finset ((a : Fin d) → a ∈ Finset.univ → ℕ) :=
  Finset.univ.pi (fun i => Finset.range (n i + 1))

private def cleanBox (d : ℕ) (n : Fin d → ℕ) : Finset (Fin d → ℕ) :=
  (weirdBox d n).image (cleanIdx d)

private def ej (d : ℕ) (j : Fin d) : Fin d → ℕ := fun i => if i = j then 1 else 0
private def sub_ej (d : ℕ) (j : Fin d) (m : Fin d → ℕ) : Fin d → ℕ := fun i => m i - if i = j then 1 else 0

private def cleanExpMul (d : ℕ) (f g : ExpPowerSeries d) (n : Fin d → ℕ) : ℚ :=
  (cleanBox d n).sum (fun m => (Finset.univ : Finset (Fin d)).prod (fun i => Nat.choose (n i) (m i)) * f m * g (fun i => n i - m i))

private def prodN (d : ℕ) (n : Fin d → ℕ) (m : Fin d → ℕ) : ℕ :=
  (Finset.univ : Finset (Fin d)).prod (fun i => Nat.choose (n i) (m i))

private def prodNp (d : ℕ) (j : Fin d) (n : Fin d → ℕ) (m : Fin d → ℕ) : ℕ :=
  (Finset.univ : Finset (Fin d)).prod (fun i => Nat.choose (n i + (if i = j then 1 else 0)) (m i))

private def prodRest (d : ℕ) (j : Fin d) (n : Fin d → ℕ) (m : Fin d → ℕ) : ℕ :=
  (Finset.univ.erase j : Finset (Fin d)).prod (fun i => Nat.choose (n i) (m i))

private theorem expMul_clean (d : ℕ) (f g : ExpPowerSeries d) (n : Fin d → ℕ) :
    expMul d f g n = cleanExpMul d f g n := by
  dsimp [expMul, cleanBox, cleanExpMul, weirdBox]
  let clean := cleanIdx d
  have hinj : Set.InjOn clean (↑(weirdBox d n)) := by
    classical
    intro m _ m' _ h
    funext i p
    have h1 : m i (Finset.mem_univ i) = m' i (Finset.mem_univ i) := by
      simpa [clean, cleanIdx] using congrFun h i
    have h2 : m i p = m i (Finset.mem_univ i) := by
      apply congrArg (fun q => m i q)
      exact Subsingleton.elim p (Finset.mem_univ i)
    have h4 : m' i (Finset.mem_univ i) = m' i p := by
      apply congrArg (fun q => m' i q)
      exact Subsingleton.elim (Finset.mem_univ i) p
    simpa [h2, h4] using h1
  exact (Finset.sum_image (M := ℚ)
      (f := fun m => (Finset.univ : Finset (Fin d)).prod (fun i => Nat.choose (n i) (m i)) * f m * g (fun i => n i - m i))
      hinj).symm

private theorem cleanBox_mem (d : ℕ) (n : Fin d → ℕ) (m : Fin d → ℕ) :
    m ∈ cleanBox d n ↔ ∀ i, m i ≤ n i := by
  dsimp [cleanBox]
  constructor
  · rw [Finset.mem_image]
    rintro ⟨w, hw, rfl⟩
    intro i
    have hw' : ∀ a, w a (Finset.mem_univ a) < n a + 1 := by simpa [weirdBox] using hw
    exact Nat.le_of_lt_succ (hw' i)
  · intro h
    rw [Finset.mem_image]
    use fun i _ => m i
    constructor
    · dsimp [weirdBox]
      simp [Finset.mem_pi, Finset.mem_range]
      intro i
      simpa using Nat.lt_succ_of_le (h i)
    · rfl

private theorem choose_succ_left' (n k : ℕ) :
    Nat.choose (n + 1) k = Nat.choose n k + (if k = 0 then 0 else Nat.choose n (k - 1)) := by
  by_cases hk : k = 0
  · simp [hk]
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
    have := Nat.choose_succ_left n k hkpos
    simpa [hk, Nat.add_comm] using this

private theorem n'_j (d : ℕ) (j : Fin d) (n : Fin d → ℕ) : (n + ej d j) j = n j + 1 := by
  dsimp [ej]
  simp

private theorem n'_ij (d : ℕ) (j : Fin d) (n : Fin d → ℕ) (i : Fin d) (hij : i ≠ j) :
    (n + ej d j) i = n i := by
  dsimp [ej]
  split_ifs <;> simp_all

private theorem n'_coord (d : ℕ) (j : Fin d) (n : Fin d → ℕ) (i : Fin d) :
    (n + ej d j) i = n i + (if i = j then 1 else 0) := by
  dsimp [ej]

private theorem univ_insert_erase (d : ℕ) (j : Fin d) :
    (Finset.univ : Finset (Fin d)) = insert j (Finset.univ.erase j) := by
  ext x
  simp [Finset.mem_insert, Finset.mem_erase]
  <;> tauto

private theorem j_notin_erase (d : ℕ) (j : Fin d) : j ∉ (Finset.univ : Finset (Fin d)).erase j := by
  simp [Finset.mem_erase]

private theorem prodN_split (d : ℕ) (j : Fin d) (n : Fin d → ℕ) (m : Fin d → ℕ) :
    prodN d n m = Nat.choose (n j) (m j) * prodRest d j n m := by
  dsimp [prodN, prodRest]
  rw [univ_insert_erase, Finset.prod_insert (j_notin_erase d j)]
  <;> simp

private theorem prodNp_split (d : ℕ) (j : Fin d) (n : Fin d → ℕ) (m : Fin d → ℕ) :
    prodNp d j n m = Nat.choose (n j + 1) (m j) * prodRest d j n m := by
  dsimp [prodNp, prodRest]
  rw [univ_insert_erase, Finset.prod_insert (j_notin_erase d j)]
  have h1 : (n j + if j = j then 1 else 0).choose (m j) = (n j + 1).choose (m j) := by
    simp
  have h2 : (Finset.univ.erase j).prod (fun i => Nat.choose (n i + (if i = j then 1 else 0)) (m i)) =
      (Finset.univ.erase j).prod (fun i => Nat.choose (n i) (m i)) := by
    apply Finset.prod_congr rfl
    intro i hi
    obtain ⟨hij, _⟩ := Finset.mem_erase.mp hi
    simp [hij]
  rw [h1, h2]
  simp [univ_insert_erase]

private theorem prodN_subej (d : ℕ) (j : Fin d) (n : Fin d → ℕ) (m : Fin d → ℕ) :
    prodN d n (sub_ej d j m) = Nat.choose (n j) (m j - 1) * prodRest d j n m := by
  dsimp [prodN, prodRest, sub_ej]
  rw [univ_insert_erase, Finset.prod_insert (j_notin_erase d j)]
  have h1 : (n j).choose (m j - (if j = j then 1 else 0)) = (n j).choose (m j - 1) := by
    simp
  have h2 : (Finset.univ.erase j).prod (fun i => Nat.choose (n i) (m i - (if i = j then 1 else 0))) =
      (Finset.univ.erase j).prod (fun i => Nat.choose (n i) (m i)) := by
    apply Finset.prod_congr rfl
    intro i hi
    obtain ⟨hij, _⟩ := Finset.mem_erase.mp hi
    simp [hij]
  rw [h1, h2]
  simp [univ_insert_erase]

private theorem prodNp_eq (d : ℕ) (j : Fin d) (n : Fin d → ℕ) (m : Fin d → ℕ) :
    prodNp d j n m = prodN d n m + (if m j = 0 then 0 else prodN d n (sub_ej d j m)) := by
  rw [prodNp_split, prodN_split, prodN_subej, choose_succ_left' (n j) (m j)]
  split_ifs <;> ring

private theorem prodNp_of_nprime (d : ℕ) (j : Fin d) (n : Fin d → ℕ) (m : Fin d → ℕ) :
    (Finset.univ : Finset (Fin d)).prod (fun i => Nat.choose ((n + ej d j) i) (m i)) = prodNp d j n m := by
  apply Finset.prod_congr rfl
  intro i _
  rw [n'_coord d j n i]

/-- The product rule for the binomial-convolution product: the partial derivative of a
    binomial-convolution product is the sum of the two one-sided products
    (`expDeriv_j (f * g) = (expDeriv_j f) * g + f * (expDeriv_j g)`).  This is the
    Leibniz rule, and it is what makes the binomial-convolution algebra a differential
    algebra (the exponential algebra). -/
private theorem expDeriv_expMul (d : ℕ) (j : Fin d) (f g : Lax946791.CDA.ExpPowerSeries d) :
    expDeriv d j (expMul d f g) = expMul d (expDeriv d j f) g + expMul d f (expDeriv d j g) := by
  funext n
  have hshift : expDeriv d j (expMul d f g) n = (expMul d f g) (n + ej d j) := by
    dsimp [expDeriv, ej]
    rfl
  rw [hshift, expMul_clean, Pi.add_apply]
  rw [expMul_clean (f := expDeriv d j f), expMul_clean (g := expDeriv d j g)]
  dsimp [cleanExpMul]
  let n' := n + ej d j
  let boxN := cleanBox d n
  let boxN' := cleanBox d n'
  let layer := boxN'.filter (fun m => m j = n j + 1)
  let faceBot := boxN.filter (fun m => m j < n j)
  let faceTop := boxN.filter (fun m => m j = n j)
  let faceZero := boxN.filter (fun m => m j = 0)
  let facePos := boxN.filter (fun m => 0 < m j)
  let φ (m : Fin d → ℕ) := prodNp d j n m * f m * g (fun i => n' i - m i)
  let ψ1 (m : Fin d → ℕ) := prodN d n m * f m * expDeriv d j g (fun i => n i - m i)
  let ψ2 (m : Fin d → ℕ) := prodN d n m * expDeriv d j f m * g (fun i => n i - m i)
  have hgoal :
      (boxN' : Finset (Fin d → ℕ)).sum (fun m => prodNp d j n m * f m * g (fun i => n' i - m i)) =
        boxN.sum ψ2 + boxN.sum ψ1 := by
    dsimp only [φ, ψ1, ψ2]
    -- ---- box decompositions ----
    have hsub : boxN ⊆ boxN' := by
      intro m hm
      rw [cleanBox_mem] at hm ⊢
      intro i
      have hnj : n i ≤ n' i := by
        dsimp [n']
        exact Nat.le_add_right _ _
      exact Nat.le_trans (hm i) hnj
    have hdisj : Disjoint boxN layer := by
      rw [Finset.disjoint_left]
      intro m hm
      dsimp only [layer]
      intro hm'
      simp only [Finset.mem_filter] at hm'
      have h1 : m j ≤ n j := by rw [cleanBox_mem] at hm; exact hm j
      omega
    have hunion : boxN' = boxN ∪ layer := by
      dsimp [layer]
      classical
      ext m
      simp [Finset.mem_union, Finset.mem_filter]
      constructor
      · intro hm'
        have hcoord : m j ≤ n j + 1 := by
          have hm'box : m ∈ boxN' := hm'
          rw [cleanBox_mem] at hm'box
          have hnj : m j ≤ n' j := hm'box j
          dsimp only [n'] at hnj
          rw [n'_j] at hnj
          exact hnj
        by_cases hj : m j ≤ n j
        · have hboxN : m ∈ boxN := by
            rw [cleanBox_mem]
            intro i
            by_cases hij : i = j
            · simpa [hij] using hj
            · have hnj : n' i = n i := by dsimp [n']; exact n'_ij d j n i hij
              have hmi : m i ≤ n' i := by rw [cleanBox_mem] at hm'; exact hm' i
              simpa [hnj] using hmi
          exact Or.inl hboxN
        · have hmj : m j = n j + 1 := by
            have : m j > n j := Nat.not_le.mp hj
            omega
          exact Or.inr ⟨hm', hmj⟩
      · intro hm
        cases hm with
        | inl h => exact hsub h
        | inr h => exact h.1
    have hface_union : boxN = faceBot ∪ faceTop := by
      classical
      ext m
      dsimp only [faceBot, faceTop]
      simp [Finset.mem_union, Finset.mem_filter]
      constructor
      · intro hm
        by_cases h : m j < n j
        · exact Or.inl ⟨hm, h⟩
        · have h' : m j = n j := by
            have hmj : m j ≤ n j := by rw [cleanBox_mem] at hm; exact hm j
            omega
          exact Or.inr ⟨hm, h'⟩
      · intro hm
        cases hm with
        | inl h => exact h.1
        | inr h => exact h.1
    have hface_disj : Disjoint faceBot faceTop := by
      rw [Finset.disjoint_left]
      intro m hm
      dsimp only [faceBot] at hm
      dsimp only [faceTop]
      intro hm'
      simp only [Finset.mem_filter] at hm hm'
      omega
    have hpos_union : boxN = faceZero ∪ facePos := by
      classical
      ext m
      dsimp only [faceZero, facePos]
      simp [Finset.mem_union, Finset.mem_filter]
      constructor
      · intro hm
        by_cases h : 0 < m j
        · exact Or.inr ⟨hm, h⟩
        · have h' : m j = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_not_lt h)
          exact Or.inl ⟨hm, h'⟩
      · intro hm
        cases hm with
        | inl h => exact h.1
        | inr h => exact h.1
    have hpos_disj : Disjoint faceZero facePos := by
      rw [Finset.disjoint_left]
      intro m hm
      dsimp only [faceZero] at hm
      dsimp only [facePos]
      intro hm'
      simp only [Finset.mem_filter] at hm hm'
      omega
    -- ---- vector shift lemmas ----
    have hnm_eq (m : Fin d → ℕ) (hm : m ∈ boxN) : (fun i => n' i - m i) = (fun i => n i - m i) + ej d j := by
      funext i
      by_cases hij : i = j
      · rw [hij]
        have hmj : m j ≤ n j := by rw [cleanBox_mem] at hm; exact hm j
        dsimp [n', ej]
        omega
      · rw [show n' i = n i from by dsimp [n']; exact n'_ij d j n i hij]
        dsimp [ej]
        simp [hij]
    have hsub_add (m : Fin d → ℕ) (hm : m ∈ boxN) (hpos : 0 < m j) : (sub_ej d j m) + ej d j = m := by
      funext i
      by_cases hij : i = j
      · rw [hij]
        dsimp [sub_ej, ej]
        simp [Nat.sub_add_cancel hpos]
      · dsimp [sub_ej, ej]
        simp [hij]
    have hnm_sub (m : Fin d → ℕ) (hm : m ∈ boxN) (hpos : 0 < m j) : (fun i => n i - m i) + ej d j = fun i => n i - (sub_ej d j m) i := by
      funext i
      by_cases hij : i = j
      · rw [hij]
        simp [sub_ej, ej]
        have hmj : m j ≤ n j := by rw [cleanBox_mem] at hm; exact hm j
        omega
      · dsimp [sub_ej, ej]
        simp [hij]
    -- ---- pointwise identities ----
    have hphi_boxN (m : Fin d → ℕ) (hm : m ∈ boxN) :
        prodNp d j n m * f m * g (fun i => n' i - m i) =
          prodN d n m * f m * expDeriv d j g (fun i => n i - m i) +
          (if m j = 0 then 0 else prodN d n (sub_ej d j m) * expDeriv d j f (sub_ej d j m) * g (fun i => n i - (sub_ej d j m) i)) := by
      rw [prodNp_eq d j n m]
      have hg : g (fun i => n' i - m i) = expDeriv d j g (fun i => n i - m i) := by
        rw [hnm_eq m hm]
        dsimp [expDeriv]
        congr
      rw [hg]
      by_cases h0 : m j = 0
      · simp [h0]
      · have hpos : 0 < m j := Nat.pos_of_ne_zero h0
        have hf : f m = expDeriv d j f (sub_ej d j m) := by
          dsimp [expDeriv, sub_ej]
          congr
          funext i
          by_cases hij : i = j
          · rw [hij]
            simp [hpos, Nat.sub_add_cancel hpos]
          · simp [hij]
        have hg2 : expDeriv d j g (fun i => n i - m i) = g (fun i => n i - (sub_ej d j m) i) := by
          dsimp [expDeriv]
          congr
          funext i
          by_cases hij : i = j
          · rw [hij]
            simp [sub_ej, ej]
            have hmj : m j ≤ n j := by rw [cleanBox_mem] at hm; exact hm j
            omega
          · dsimp [sub_ej]
            simp [hij]
        simp [h0, hf, hg2]
        <;> ring
    have hphi_layer (m : Fin d → ℕ) (hm : m ∈ layer) :
        prodNp d j n m * f m * g (fun i => n' i - m i) =
          prodN d n (sub_ej d j m) * expDeriv d j f (sub_ej d j m) * g (fun i => n i - (sub_ej d j m) i) := by
      dsimp only [layer] at hm
      simp only [Finset.mem_filter] at hm
      have hmj : m j = n j + 1 := hm.2
      have hpos : 0 < m j := by omega
      have hf : f m = expDeriv d j f (sub_ej d j m) := by
        dsimp [expDeriv, sub_ej]
        congr
        funext i
        by_cases hij : i = j
        · rw [hij]
          simp [hpos, Nat.sub_add_cancel hpos]
        · simp [hij]
      have hg : g (fun i => n' i - m i) = g (fun i => n i - (sub_ej d j m) i) := by
        have hnm : (fun i => n' i - m i) = fun i => n i - (sub_ej d j m) i := by
          funext i
          by_cases hij : i = j
          · rw [hij]
            dsimp [n', sub_ej, ej]
            rw [hmj]
            simp [Nat.sub_self, Nat.add_sub_cancel, Nat.add_comm]
          · have hnj : n' i = n i := by dsimp [n']; exact n'_ij d j n i hij
            rw [hnj]
            dsimp [sub_ej]
            simp [hij]
        rw [hnm]
      rw [hf, hg]
      have hprod : prodNp d j n m = prodN d n (sub_ej d j m) := by
        rw [prodNp_split, prodN_subej]
        have h1 : Nat.choose (n j + 1) (m j) = 1 := by
          rw [hmj, Nat.choose_self]
        have h2 : Nat.choose (n j) (m j - 1) = 1 := by
          rw [show m j - 1 = n j from by omega, Nat.choose_self]
        simp [h1, h2]
        <;> ring
      rw [hprod]
    -- ---- reindexing bijections ----
    have hsub_inj_facePos : Set.InjOn (sub_ej d j) (↑facePos) := by
      intro m hm m' hm' h
      funext i
      by_cases hij : i = j
      · rw [hij]
        have hj : (sub_ej d j m) j = (sub_ej d j m') j := congrFun h j
        simp [sub_ej] at hj
        have hpos : 0 < m j := by
          have this : m ∈ facePos := by simpa [facePos] using hm
          simp [facePos, Finset.mem_filter] at this
          exact this.2
        have hpos' : 0 < m' j := by
          have this : m' ∈ facePos := by simpa [facePos] using hm'
          simp [facePos, Finset.mem_filter] at this
          exact this.2
        omega
      · have hi : (sub_ej d j m) i = (sub_ej d j m') i := congrFun h i
        dsimp [sub_ej] at hi
        simpa [hij] using hi
    have himg_facePos : facePos.image (sub_ej d j) = faceBot := by
      dsimp [facePos, faceBot]
      ext m
      constructor
      · rw [Finset.mem_image]
        rintro ⟨x, hx, rfl⟩
        simp only [Finset.mem_filter] at hx
        have hxbox : x ∈ boxN := hx.1
        have hxpos : 0 < x j := hx.2
        have hxbox' : ∀ i, x i ≤ n i := by rw [cleanBox_mem] at hxbox; exact hxbox
        have hxj : x j ≤ n j := hxbox' j
        rw [Finset.mem_filter]
        constructor
        · rw [cleanBox_mem]
          intro i
          by_cases hij : i = j
          · rw [hij]
            simp [sub_ej]
            omega
          · dsimp [sub_ej]
            simp [hij]
            exact hxbox' i
        · simp [sub_ej]
          by_cases h : x j = n j
          · rw [h]
            have : 0 < n j := by rw [← h]; exact hxpos
            omega
          · have hlt : x j < n j := Nat.lt_of_le_of_ne hxj h
            exact Nat.lt_of_le_of_lt (Nat.sub_le (x j) 1) hlt
      · intro hm
        simp only [Finset.mem_filter] at hm
        have hmbox : m ∈ boxN := hm.1
        have hmj : m j < n j := hm.2
        rw [Finset.mem_image]
        use m + ej d j
        constructor
        · rw [Finset.mem_filter]
          constructor
          · rw [cleanBox_mem]
            intro i
            by_cases hij : i = j
            · rw [hij]
              simp [ej]
              exact Nat.succ_le_of_lt hmj
            · have : m i ≤ n i := by rw [cleanBox_mem] at hmbox; exact hmbox i
              simp [hij, ej]
              exact this
          · simp [ej]
        · ext i
          by_cases hij : i = j
          · rw [hij]
            simp [sub_ej, ej]
          · simp [hij, sub_ej, ej]
    have hsub_inj_layer : Set.InjOn (sub_ej d j) (↑layer) := by
      intro m hm m' hm' h
      funext i
      by_cases hij : i = j
      · rw [hij]
        have hj : (sub_ej d j m) j = (sub_ej d j m') j := congrFun h j
        simp [sub_ej] at hj
        have hpos : 0 < m j := by
          have this : m ∈ layer := by simpa [layer] using hm
          simp [layer, Finset.mem_filter] at this
          omega
        have hpos' : 0 < m' j := by
          have this : m' ∈ layer := by simpa [layer] using hm'
          simp [layer, Finset.mem_filter] at this
          omega
        omega
      · have hi : (sub_ej d j m) i = (sub_ej d j m') i := congrFun h i
        dsimp [sub_ej] at hi
        simpa [hij] using hi
    have himg_layer : layer.image (sub_ej d j) = faceTop := by
      dsimp [layer, faceTop]
      ext m
      constructor
      · rw [Finset.mem_image]
        rintro ⟨x, hx, rfl⟩
        simp only [Finset.mem_filter] at hx
        have hxbox : x ∈ boxN' := hx.1
        have hxj : x j = n j + 1 := hx.2
        rw [Finset.mem_filter]
        constructor
        · rw [cleanBox_mem]
          intro i
          by_cases hij : i = j
          · rw [hij]
            dsimp [sub_ej]
            rw [hxj]
            simp [Nat.add_sub_cancel, Nat.add_comm]
          · dsimp [sub_ej]
            simp [hij]
            have hnj : n' i = n i := by dsimp [n']; exact n'_ij d j n i hij
            have : x i ≤ n' i := by rw [cleanBox_mem] at hxbox; exact hxbox i
            simpa [hnj] using this
        · dsimp [sub_ej]
          rw [hxj]
          simp [Nat.add_sub_cancel, Nat.add_comm]
      · intro hm
        simp only [Finset.mem_filter] at hm
        have hmbox : m ∈ boxN := hm.1
        have hmj : m j = n j := hm.2
        rw [Finset.mem_image]
        use m + ej d j
        constructor
        · rw [Finset.mem_filter]
          constructor
          · rw [cleanBox_mem]
            intro i
            by_cases hij : i = j
            · rw [hij]
              simp [ej, n']
              omega
            · dsimp [ej]
              simp [hij]
              have hnj : n' i = n i := by dsimp [n']; exact n'_ij d j n i hij
              have : m i ≤ n i := by rw [cleanBox_mem] at hmbox; exact hmbox i
              simpa [hnj] using this
          · simp [ej, hmj]
        · ext i
          by_cases hij : i = j
          · rw [hij]
            simp [sub_ej, ej]
          · simp [hij, sub_ej, ej]
    -- ---- sum identities ----
    have hsum1 : boxN'.sum (fun m => prodNp d j n m * f m * g (fun i => n' i - m i)) =
        boxN.sum (fun m => prodNp d j n m * f m * g (fun i => n' i - m i)) +
        layer.sum (fun m => prodNp d j n m * f m * g (fun i => n' i - m i)) := by
      rw [hunion, Finset.sum_union hdisj]
    have hboxN : boxN.sum (fun m => prodNp d j n m * f m * g (fun i => n' i - m i)) =
        boxN.sum (fun m => prodN d n m * f m * expDeriv d j g (fun i => n i - m i)) +
        faceBot.sum (fun m => prodN d n m * expDeriv d j f m * g (fun i => n i - m i)) := by
      have h1 : boxN.sum (fun m => prodNp d j n m * f m * g (fun i => n' i - m i)) =
          boxN.sum (fun m => prodN d n m * f m * expDeriv d j g (fun i => n i - m i) +
            (if m j = 0 then 0 else prodN d n (sub_ej d j m) * expDeriv d j f (sub_ej d j m) * g (fun i => n i - (sub_ej d j m) i))) := by
        apply Finset.sum_congr rfl
        intro m hm
        exact hphi_boxN m hm
      rw [h1]
      have h2 : boxN.sum (fun m => prodN d n m * f m * expDeriv d j g (fun i => n i - m i) +
          (if m j = 0 then 0 else prodN d n (sub_ej d j m) * expDeriv d j f (sub_ej d j m) * g (fun i => n i - (sub_ej d j m) i))) =
          boxN.sum (fun m => prodN d n m * f m * expDeriv d j g (fun i => n i - m i)) +
          boxN.sum (fun m => if m j = 0 then 0 else prodN d n (sub_ej d j m) * expDeriv d j f (sub_ej d j m) * g (fun i => n i - (sub_ej d j m) i)) := by
        simp [Finset.sum_add_distrib]
      rw [h2]
      have h3 : boxN.sum (fun m => if m j = 0 then 0 else prodN d n (sub_ej d j m) * expDeriv d j f (sub_ej d j m) * g (fun i => n i - (sub_ej d j m) i)) =
          facePos.sum (fun m => prodN d n (sub_ej d j m) * expDeriv d j f (sub_ej d j m) * g (fun i => n i - (sub_ej d j m) i)) := by
        rw [show boxN = faceZero ∪ facePos from hpos_union, Finset.sum_union hpos_disj]
        have hz : faceZero.sum (fun m => if m j = 0 then 0 else prodN d n (sub_ej d j m) * expDeriv d j f (sub_ej d j m) * g (fun i => n i - (sub_ej d j m) i)) = 0 := by
          apply Finset.sum_eq_zero
          intro m hm
          dsimp only [faceZero] at hm
          simp only [Finset.mem_filter] at hm
          simp [hm.2]
        have hp : facePos.sum (fun m => if m j = 0 then 0 else prodN d n (sub_ej d j m) * expDeriv d j f (sub_ej d j m) * g (fun i => n i - (sub_ej d j m) i)) =
            facePos.sum (fun m => prodN d n (sub_ej d j m) * expDeriv d j f (sub_ej d j m) * g (fun i => n i - (sub_ej d j m) i)) := by
          apply Finset.sum_congr rfl
          intro m hm
          dsimp only [facePos] at hm
          simp only [Finset.mem_filter] at hm
          have : 0 < m j := hm.2
          simp [show m j ≠ 0 from Nat.pos_iff_ne_zero.mp this]
        rw [hz, hp]
        <;> simp
      rw [h3]
      have h4 : facePos.sum (fun m => prodN d n (sub_ej d j m) * expDeriv d j f (sub_ej d j m) * g (fun i => n i - (sub_ej d j m) i)) =
          faceBot.sum (fun m => prodN d n m * expDeriv d j f m * g (fun i => n i - m i)) := by
        have := Finset.sum_image (s := facePos) (g := sub_ej d j)
            (f := fun m => prodN d n m * expDeriv d j f m * g (fun i => n i - m i)) hsub_inj_facePos
        rw [himg_facePos] at this
        simpa using this.symm
      rw [h4]
    have hlayer : layer.sum (fun m => prodNp d j n m * f m * g (fun i => n' i - m i)) =
        faceTop.sum (fun m => prodN d n m * expDeriv d j f m * g (fun i => n i - m i)) := by
      have h1 : layer.sum (fun m => prodNp d j n m * f m * g (fun i => n' i - m i)) =
          layer.sum (fun m => prodN d n (sub_ej d j m) * expDeriv d j f (sub_ej d j m) * g (fun i => n i - (sub_ej d j m) i)) := by
        apply Finset.sum_congr rfl
        intro m hm
        exact hphi_layer m hm
      rw [h1]
      have := Finset.sum_image (s := layer) (g := sub_ej d j)
          (f := fun m => prodN d n m * expDeriv d j f m * g (fun i => n i - m i)) hsub_inj_layer
      rw [himg_layer] at this
      simpa using this.symm
    have hface : faceBot.sum (fun m => prodN d n m * expDeriv d j f m * g (fun i => n i - m i)) +
        faceTop.sum (fun m => prodN d n m * expDeriv d j f m * g (fun i => n i - m i)) =
        boxN.sum (fun m => prodN d n m * expDeriv d j f m * g (fun i => n i - m i)) := by
      rw [hface_union, Finset.sum_union hface_disj]
    -- ---- assemble ----
    rw [hsum1, hboxN, hlayer, ← hface]
    ring
  have hlhs :
      (boxN' : Finset (Fin d → ℕ)).sum (fun m => (Finset.univ : Finset (Fin d)).prod (fun i => Nat.choose (n' i) (m i)) * f m * g (fun i => n' i - m i)) =
        boxN'.sum φ := by
    apply Finset.sum_congr rfl
    intro m _
    dsimp [φ]
    rw [show (Finset.univ : Finset (Fin d)).prod (fun i => Nat.choose (n' i) (m i)) = prodNp d j n m from by
      dsimp [n']
      exact prodNp_of_nprime d j n m]
  have hrhs1 :
      boxN.sum (fun m => (Finset.univ : Finset (Fin d)).prod (fun i => Nat.choose (n i) (m i)) * expDeriv d j f m * g (fun i => n i - m i)) =
        boxN.sum ψ2 := by
    apply Finset.sum_congr rfl
    intro m _
    dsimp [ψ2, prodN]
  have hrhs2 :
      boxN.sum (fun m => (Finset.univ : Finset (Fin d)).prod (fun i => Nat.choose (n i) (m i)) * f m * expDeriv d j g (fun i => n i - m i)) =
        boxN.sum ψ1 := by
    apply Finset.sum_congr rfl
    intro m _
    dsimp [ψ1, prodN]
  change (boxN' : Finset (Fin d → ℕ)).sum (fun m => (Finset.univ : Finset (Fin d)).prod (fun i => Nat.choose (n' i) (m i)) * f m * g (fun i => n' i - m i)) =
      boxN.sum (fun m => (Finset.univ : Finset (Fin d)).prod (fun i => Nat.choose (n i) (m i)) * expDeriv d j f m * g (fun i => n i - m i)) +
      boxN.sum (fun m => (Finset.univ : Finset (Fin d)).prod (fun i => Nat.choose (n i) (m i)) * f m * expDeriv d j g (fun i => n i - m i))
  rw [hlhs, hrhs1, hrhs2]
  exact hgoal

/-- The Leibniz rule for the shuffle product: `∂_a (f ⧢ g) = (∂_a f) ⧢ g + f ⧢ (∂_a g)`,
    the step case of the shuffle recursion. -/
private theorem shuffleLeibniz {α : Type*} (f g : Series α) (a : α) :
    leftDeriv α a (shuffle α f g) =
      shuffle α (leftDeriv α a f) g + shuffle α f (leftDeriv α a g) := by
  funext w
  dsimp [leftDeriv, shuffle]
  simp [shuffleRec_cons]

/-- The shuffle product is commutative: `f ⧢ g = g ⧢ f`.  (Re-proved here: the lemma is
    private in the `Shuffle` module.)  Both sides satisfy the same recursion (the Leibniz
    rule and the symmetric initial condition), proved by induction on the word. -/
private theorem shuffle_comm {α : Type*} (f g : Series α) : shuffle α f g = shuffle α g f := by
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

/-- The binomial-convolution product at the zero multi-index is the pointwise product. -/
private theorem expMul_zero (d : ℕ) (f g : Lax946791.CDA.ExpPowerSeries d) :
    expMul d f g 0 = f 0 * g 0 := by
  rw [expMul_clean, cleanExpMul]
  have hbox : cleanBox d 0 = {0} := by
    ext m
    simp [cleanBox_mem]
    constructor
    · intro h
      funext i
      exact h i
    · intro h
      intro i
      rw [h]
      rfl
  rw [hbox, Finset.sum_singleton]
  simp only [Nat.choose_self, Finset.prod_const, one_pow, Nat.cast_one, one_mul, Pi.zero_apply, Nat.zero_sub]
  rfl

/-- The lift of the binomial-convolution product is the shuffle product of the lifts:
    `toSeries (expMul f g) = shuffle (toSeries f) (toSeries g)`.  Both sides satisfy
    the same initial condition and the same Leibniz recursion (the shuffle
    characterisation), so they are equal; the Leibniz step uses the product rule. -/
private theorem toSeries_expMul (d : ℕ) (f g : Lax946791.CDA.ExpPowerSeries d) :
    toSeries d (expMul d f g) = shuffle (Fin d) (toSeries d f) (toSeries d g) := by
  funext w
  induction w generalizing f g with
  | nil =>
    have hpar : parikh (Fin d) [] = 0 := by
      funext a
      simp [parikh]
    have hL : toSeries d (expMul d f g) [] = f 0 * g 0 := by
      dsimp [toSeries]
      rw [hpar, expMul_zero]
    have hR : shuffle (Fin d) (toSeries d f) (toSeries d g) [] = f 0 * g 0 := by
      dsimp [shuffle]
      rw [shuffleRec_nil]
      dsimp [toSeries]
      simp [hpar]
    rw [hL, hR]
  | cons a w' ih =>
    let T := shuffle (Fin d) (toSeries d (expDeriv d a f)) (toSeries d g) w' +
             shuffle (Fin d) (toSeries d f) (toSeries d (expDeriv d a g)) w'
    have hL : toSeries d (expMul d f g) (a :: w') = T := by
      have h1 : toSeries d (expMul d f g) (a :: w') =
          leftDeriv (Fin d) a (toSeries d (expMul d f g)) w' := by
        dsimp [toSeries, leftDeriv]
      rw [h1, ← toSeries_expDeriv, expDeriv_expMul, toSeries_add, Pi.add_apply]
      rw [ih (expDeriv d a f) g, ih f (expDeriv d a g)]
    have hR : shuffle (Fin d) (toSeries d f) (toSeries d g) (a :: w') = T := by
      have h1 : shuffle (Fin d) (toSeries d f) (toSeries d g) (a :: w') =
          leftDeriv (Fin d) a (shuffle (Fin d) (toSeries d f) (toSeries d g)) w' := by
        dsimp [leftDeriv, shuffle]
      rw [h1, shuffleLeibniz, Pi.add_apply]
      simp [← toSeries_expDeriv]
      rfl
    rw [hL, hR]

/-- The lift of the `n`-fold binomial-convolution power is the `n`-fold shuffle power
    of the lift. -/
private theorem toSeries_expPow (d : ℕ) (f : Lax946791.CDA.ExpPowerSeries d) (n : ℕ) :
    toSeries d (expPow d f n) = shufflePow (Fin d) (toSeries d f) n := by
  induction n with
  | zero =>
      dsimp [expPow, shufflePow]
      exact toSeries_unit d
  | succ n ih =>
      dsimp [expPow, shufflePow]
      rw [toSeries_expMul, ih, shuffle_comm (shufflePow (Fin d) (toSeries d f) n) (toSeries d f)]

/-- Lifting commutes with the `foldr` of binomial-convolution powers: the lift of
    `L.foldr (fun i acc => expMul d acc (expPow d (fs i) (m i))) (1)` is the `foldr` of
    the shuffle powers of the lifts, starting from the lifted unit. -/
private theorem toSeries_foldr (d k : ℕ) (fs : Fin k → Lax946791.CDA.ExpPowerSeries d)
    (m : Fin k →₀ ℕ) (L : List (Fin k)) :
    toSeries d (L.foldr (fun i acc => expMul d acc (expPow d (fs i) (m i)))
        (fun idx => if idx = 0 then 1 else 0)) =
      L.foldr (fun i acc => shuffle (Fin d) acc (shufflePow (Fin d) (toSeries d (fs i)) (m i)))
        (toSeries d (fun idx => if idx = 0 then 1 else 0)) := by
  induction L with
  | nil =>
      rfl
  | cons i L ih =>
      dsimp [List.foldr]
      rw [toSeries_expMul, ih, toSeries_expPow]

/-- A `Finset.fold` of the (commutative, associative) shuffle product over `univ` equals
    the `foldr` of the same step over `univ.toList`: the `Finset.fold` unfolds to a
    `Multiset.fold` (i.e. a `foldr`) over the multiset of the set, and the commutativity
    of the shuffle product lets the fold commute across the `map` (so that the new factor
    is applied on the right, as in the `foldr`). -/
private theorem foldr_eq_univfold {α : Type*} (k : ℕ) (b : Series α) (H : Fin k → Series α) :
    (Finset.univ : Finset (Fin k)).fold (shuffle α) b H =
      (Finset.univ : Finset (Fin k)).toList.foldr (fun i acc => shuffle α acc (H i)) b := by
  let s : Finset (Fin k) := Finset.univ
  have : ∀ (l : List (Fin k)), (l.map H).foldr (shuffle α) b =
      l.foldr (fun i acc => shuffle α acc (H i)) b := by
    intro l
    induction l with
    | nil => rfl
    | cons i l ih =>
        dsimp [List.foldr, List.map]
        rw [ih, shuffle_comm (H i) _]
  have hmap : s.val.map H = ((s.toList.map H) : Multiset (Series α)) := by
    rw [← Finset.coe_toList]
    rfl
  have h1 : (s.val.map H).fold (shuffle α) b = (s.toList.map H).foldr (shuffle α) b := by
    rw [hmap]
    simp [Multiset.coe_fold_r]
  calc
    s.fold (shuffle α) b H = (s.val.map H).fold (shuffle α) b := by dsimp [Finset.fold]
    _ = (s.toList.map H).foldr (shuffle α) b := h1
    _ = s.toList.foldr (fun i acc => shuffle α acc (H i)) b := this s.toList

/-- The lift of the binomial-convolution-algebra evaluation is the shuffle-algebra
    evaluation of the lifts: `toSeries (evalCDA d k fs p) =
    shuffleEval (Fin d) k (fun i => toSeries (fs i)) p`.  The lift is `ℚ`-linear, so it
    commutes with the sum over the support; on each monomial it turns the `foldr` of
    binomial-convolution powers into the `foldr` of shuffle powers (`toSeries_foldr`), and
    the latter is the `Finset.fold` over `univ` that defines `shuffleProd`
    (`foldr_eq_univfold`). -/
private theorem toSeries_evalCDA (d k : ℕ) (fs : Fin k → Lax946791.CDA.ExpPowerSeries d)
    (p : MvPolynomial (Fin k) ℚ) :
    toSeries d (evalCDA d k fs p) = shuffleEval (Fin d) k (fun i => toSeries d (fs i)) p := by
  dsimp [evalCDA, shuffleEval]
  let E (m : Fin k →₀ ℕ) :=
    (Finset.univ : Finset (Fin k)).toList.foldr
      (fun i acc => expMul d acc (expPow d (fs i) (m i))) (fun idx => if idx = 0 then 1 else 0)
  let S (m : Fin k →₀ ℕ) :=
    (Finset.univ : Finset (Fin k)).fold (shuffle (Fin d)) (shuffleUnit (Fin d))
      (fun i => shufflePow (Fin d) (toSeries d (fs i)) (m i))
  have hE : ∀ (m : Fin k →₀ ℕ), toSeries d (E m) = S m := by
    intro m
    rw [toSeries_foldr d k fs m (Finset.univ : Finset (Fin k)).toList, toSeries_unit d]
    exact (foldr_eq_univfold (α := Fin d) k (shuffleUnit (Fin d))
        (fun i => shufflePow (Fin d) (toSeries d (fs i)) (m i))).symm
  have hsum : toSeries d (p.support.sum (fun m => p.coeff m • E m)) =
      p.support.sum (fun m => p.coeff m • toSeries d (E m)) := by
    funext w
    simp [toSeries, Pi.smul_apply]
  rw [hsum]
  apply Finset.sum_congr rfl
  intro m hm
  rw [hE m]
  rw [shuffleProd_eq_fold]

/-! ### The companion shuffle automaton -/

/-- The companion shuffle automaton of a CDA system `(p, c)`: `k` nonterminals,
    output `F X_i = c_i`, transitions `Δ_{a_j} X_i = p^{(j)}_i`. -/
abbrev companionAutomaton (d k : ℕ) (_hd : 0 < d) (hk : 0 < k)
    (p : Fin k → Fin d → MvPolynomial (Fin k) ℚ) (c : Fin k → ℚ) :
    ShuffleAutomaton (Fin d) :=
  { dim := k, hdim := hk, F := c, Δ := fun j i => p i j }

/-- A tuple `g` of series *solves the companion system* of `(p, c)`: it satisfies the
    initial condition `g_i(ε) = c_i` and the shuffle equations
    `leftDeriv a_j g_i = p^{(j)}_i(g_1, …, g_k)` (the shuffle-algebra evaluation). -/
def SolvesCompanion (d k : ℕ) (g : Fin k → Series (Fin d))
    (p : Fin k → Fin d → MvPolynomial (Fin k) ℚ) (c : Fin k → ℚ) : Prop :=
  (∀ i, g i [] = c i) ∧ ∀ i j, leftDeriv (Fin d) j (g i) = shuffleEval (Fin d) k g (p i j)

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
    have h1 : leftDeriv (Fin d) j (A.sem (X i)) = A.sem (derivationExt (A.Δ j) (X i)) :=
      sem_deriv A j (X i)
    have h3 : A.sem (A.Δ j i) = shuffleEval (Fin d) A.dim (fun j' => A.sem (X j')) (A.Δ j i) :=
      sem_eq_shuffleEval A (A.Δ j i)
    calc
      leftDeriv (Fin d) j (A.sem (X i)) = A.sem (derivationExt (A.Δ j) (X i)) := h1
      _ = A.sem (A.Δ j i) := by rw [derivationExt_X]
      _ = shuffleEval (Fin d) A.dim (fun j' => A.sem (X j')) (A.Δ j i) := h3
      _ = shuffleEval (Fin d) k (fun j' => A.sem (X j')) (p i j) := by
        dsimp [A]

/-! ### Locality of the shuffle product and evaluation -/

/-- The shuffle product is *local*: `(f ⧢ g) v` depends only on the values of `f` and
    `g` at words of length at most `|v|`.  Proven by induction on `|v|` using the
    recursion equations of `shuffleRec` (the `cons` step reduces to the two sub-words
    of length `|v|-1`, and the `leftDeriv` of a local pair is local). -/
private theorem shuffle_local {α : Type*} (v : List α) :
    ∀ (f g f' g' : Series α),
      (∀ w, w.length ≤ v.length → f w = f' w) →
      (∀ w, w.length ≤ v.length → g w = g' w) →
      shuffle α f g v = shuffle α f' g' v := by
  induction v with
  | nil =>
      intro f g f' g' hf hg
      dsimp [shuffle]
      simp [shuffleRec_nil]
      rw [hf [] (by simp), hg [] (by simp)]
  | cons a w' ih =>
      intro f g f' g' hf hg
      dsimp [shuffle]
      simp [shuffleRec_cons]
      have hlf : ∀ w, w.length ≤ w'.length → leftDeriv α a f w = leftDeriv α a f' w := by
        intro w hw
        dsimp [leftDeriv]
        have : (a :: w).length ≤ (a :: w').length := by simp [List.length_cons]; exact hw
        rw [hf _ this]
      have hlg : ∀ w, w.length ≤ w'.length → leftDeriv α a g w = leftDeriv α a g' w := by
        intro w hw
        dsimp [leftDeriv]
        have : (a :: w).length ≤ (a :: w').length := by simp [List.length_cons]; exact hw
        rw [hg _ this]
      have h1 : shuffleRec α (leftDeriv α a f) g w' = shuffleRec α (leftDeriv α a f') g' w' := by
        have := ih (leftDeriv α a f) g (leftDeriv α a f') g'
          (fun w hw => hlf w hw) (fun w hw => hg w (by simp [List.length_cons]; omega))
        dsimp [shuffle] at this
        exact this
      have h2 : shuffleRec α f (leftDeriv α a g) w' = shuffleRec α f' (leftDeriv α a g') w' := by
        have := ih f (leftDeriv α a g) f' (leftDeriv α a g')
          (fun w hw => hf w (by simp [List.length_cons]; omega)) (fun w hw => hlg w hw)
        dsimp [shuffle] at this
        exact this
      rw [h1, h2]

/-- The iterated shuffle power is local: for all words `w` of length at most `|v|`,
    `shufflePow f n w` depends only on the values of `f` at words of length at most
    `|w|`.  Proven by induction on `n` (the `succ` step uses the locality of the
    shuffle product). -/
private theorem shufflePow_local {α : Type*} (v : List α) (n : ℕ) (f f' : Series α)
    (hf : ∀ w, w.length ≤ v.length → f w = f' w) :
    ∀ w, w.length ≤ v.length → shufflePow α f n w = shufflePow α f' n w := by
  induction n with
  | zero =>
      intro w hw
      rfl
  | succ n ih =>
      intro w hw
      dsimp [shufflePow]
      have hih : ∀ w', w'.length ≤ w.length → shufflePow α f n w' = shufflePow α f' n w' := by
        intro w' hw'
        exact ih w' (by omega)
      have hf' : ∀ w', w'.length ≤ w.length → f w' = f' w' := by
        intro w' hw'
        exact hf w' (by omega)
      rw [shuffle_local w f (shufflePow α f n) f' (shufflePow α f' n) hf' hih]

/-- The shuffle product of a family (indexed by a `Finsupp` exponent) is local:
    `shuffleProd k fs m v` depends only on the values of `fs i` at words of length
    at most `|v|`, for all `i`. -/
private theorem shuffleProd_local {α : Type*} (k : ℕ) (v : List α) (m : Fin k →₀ ℕ)
    (fs fs' : Fin k → Series α)
    (h : ∀ w, w.length ≤ v.length → ∀ i, fs i w = fs' i w) :
    shuffleProd α k fs m v = shuffleProd α k fs' m v := by
  rw [shuffleProd_eq_fold, foldr_eq_univfold (α := α) k (shuffleUnit α) (fun i => shufflePow α (fs i) (m i))]
  rw [shuffleProd_eq_fold, foldr_eq_univfold (α := α) k (shuffleUnit α) (fun i => shufflePow α (fs' i) (m i))]
  have hpow : ∀ (i : Fin k) (w : List α), w.length ≤ v.length →
      shufflePow α (fs i) (m i) w = shufflePow α (fs' i) (m i) w := by
    intro i w hw
    exact shufflePow_local v (m i) (fs i) (fs' i) (fun w' hw' => h w' hw' i) w hw
  -- The foldr of a local step is local: prove by induction on the list, for all words
  -- of length at most `|v|`
  have : ∀ (l : List (Fin k)), ∀ w, w.length ≤ v.length →
      l.foldr (fun i acc => shuffle α acc (shufflePow α (fs i) (m i))) (shuffleUnit α) w =
        l.foldr (fun i acc => shuffle α acc (shufflePow α (fs' i) (m i))) (shuffleUnit α) w := by
    intro l
    induction l with
    | nil =>
        intro w hw
        rfl
    | cons i l ih =>
        intro w hw
        dsimp [List.foldr]
        have hsh : shuffle α (l.foldr (fun j acc => shuffle α acc (shufflePow α (fs j) (m j))) (shuffleUnit α))
            (shufflePow α (fs i) (m i)) w =
            shuffle α (l.foldr (fun j acc => shuffle α acc (shufflePow α (fs' j) (m j))) (shuffleUnit α))
              (shufflePow α (fs' i) (m i)) w := by
          have h1 : ∀ w', w'.length ≤ w.length →
              l.foldr (fun j acc => shuffle α acc (shufflePow α (fs j) (m j))) (shuffleUnit α) w' =
                l.foldr (fun j acc => shuffle α acc (shufflePow α (fs' j) (m j))) (shuffleUnit α) w' :=
            fun w' hw' => ih w' (by omega)
          have h2 : ∀ w', w'.length ≤ w.length →
              shufflePow α (fs i) (m i) w' = shufflePow α (fs' i) (m i) w' :=
            fun w' hw' => hpow i w' (Nat.le_trans hw' hw)
          exact shuffle_local w
            (l.foldr (fun j acc => shuffle α acc (shufflePow α (fs j) (m j))) (shuffleUnit α))
            (shufflePow α (fs i) (m i))
            (l.foldr (fun j acc => shuffle α acc (shufflePow α (fs' j) (m j))) (shuffleUnit α))
            (shufflePow α (fs' i) (m i)) h1 h2
        rw [hsh]
  exact this (Finset.univ.toList) v (by simp)

/-- The shuffle evaluation is local: `shuffleEval k fs p v` depends only on the values
    of `fs i` at words of length at most `|v|`, for all `i`. -/
private theorem shuffleEval_local {α : Type*} (k : ℕ) (v : List α)
    (fs fs' : Fin k → Series α) (p : MvPolynomial (Fin k) ℚ)
    (h : ∀ w, w.length ≤ v.length → ∀ i, fs i w = fs' i w) :
    shuffleEval α k fs p v = shuffleEval α k fs' p v := by
  dsimp [shuffleEval]
  simp [Pi.smul_apply]
  apply Finset.sum_congr rfl
  intro m _
  rw [shuffleProd_local k v m fs fs' h]

/-! ### Uniqueness of the companion system solution -/

/-- The companion system has a unique solution: two solutions agree on every word.
    Because the shuffle evaluation is not pointwise (it depends on the values at all
    shorter words), the induction is on the word length with the hypothesis that the
    two solutions agree on all words of length at most the current one. -/
private theorem companion_unique (d k : ℕ)
    (p : Fin k → Fin d → MvPolynomial (Fin k) ℚ) (c : Fin k → ℚ)
    (g h : Fin k → Series (Fin d)) (hg : SolvesCompanion d k g p c) (hh : SolvesCompanion d k h p c) :
    g = h := by
  -- Strong induction on the word length: the hypothesis covers all words of length
  -- at most `n` and all components, which is what the locality of the shuffle
  -- evaluation requires.
  have : ∀ (n : ℕ), ∀ (w : List (Fin d)), w.length ≤ n → ∀ i, g i w = h i w := by
    intro n
    induction n with
    | zero =>
        intro w hw i
        have : w = [] := by
          simpa [List.length_eq_zero_iff] using Nat.le_antisymm hw (Nat.zero_le _)
        subst this
        dsimp [SolvesCompanion] at hg hh
        rw [hg.1 i, hh.1 i]
    | succ n ih =>
        intro w hw i
        cases w with
        | nil =>
            dsimp [SolvesCompanion] at hg hh
            rw [hg.1 i, hh.1 i]
        | cons a w' =>
            have hw' : w'.length ≤ n := by
              simp [List.length_cons] at hw
              omega
            have hloc : shuffleEval (Fin d) k g (p i a) w' = shuffleEval (Fin d) k h (p i a) w' :=
              shuffleEval_local (α := Fin d) k w' g h (p i a)
                (fun v hv => fun j => ih v (Nat.le_trans hv hw') j)
            calc
              g i (a :: w') = leftDeriv (Fin d) a (g i) w' := by dsimp [leftDeriv]
              _ = shuffleEval (Fin d) k g (p i a) w' := by rw [← hg.2 i a]
              _ = shuffleEval (Fin d) k h (p i a) w' := hloc
              _ = leftDeriv (Fin d) a (h i) w' := by rw [← hh.2 i a]
              _ = h i (a :: w') := by dsimp [leftDeriv]
  funext i w
  exact this w.length w (Nat.le_refl _) i

/-! ### The bridge: solvability ↔ all companion components commutative -/

/-- The initial condition `c` extends to a CDA solution iff the companion automaton's
    component series are all commutative. -/
private theorem bridge (d k : ℕ) (hd : 0 < d) (hk : 0 < k)
    (p : Fin k → Fin d → MvPolynomial (Fin k) ℚ) (c : Fin k → ℚ) :
    (∃ f : Fin k → Lax946791.CDA.ExpPowerSeries d, SolvesCDA d k f p c) ↔
      ∀ i, IsCommutative (Fin d) ((companionAutomaton d k hd hk p c).sem (X i)) := by
  let A := companionAutomaton d k hd hk p c
  constructor
  · -- (→) A CDA solution lifts to a shuffle solution of the companion system; by
      -- uniqueness the companion components coincide with the (commutative) lifts.
    intro ⟨f, hf⟩
    have hlift : SolvesCompanion d k (fun i => toSeries d (f i)) p c := by
      constructor
      · intro i
        have hpar : parikh (Fin d) [] = 0 := by
          funext a
          simp [parikh]
        dsimp [toSeries]
        rw [hpar]
        exact hf.1 i
      · intro i j
        calc
          leftDeriv (Fin d) j (toSeries d (f i)) = toSeries d (expDeriv d j (f i)) :=
            (toSeries_expDeriv d j (f i)).symm
          _ = toSeries d (evalCDA d k f (p i j)) := by rw [hf.2 i j]
          _ = shuffleEval (Fin d) k (fun i => toSeries d (f i)) (p i j) :=
            toSeries_evalCDA d k f (p i j)
    have hcomp : SolvesCompanion d k (fun i => A.sem (X i)) p c := companion_solves d k hd hk p c
    have heq : (fun i => A.sem (X i)) = (fun i => toSeries d (f i)) :=
      companion_unique d k p c (fun i => A.sem (X i)) (fun i => toSeries d (f i)) hcomp hlift
    intro i
    rw [congrFun heq i]
    exact toSeries_commutative d (f i)
  · -- (←) The companion components solve the companion system and are commutative, so
      -- their Parikh projections `f_i = toSeq (A.sem (X_i))` solve the CDA system.
    intro hcomm
    let f : Fin k → Lax946791.CDA.ExpPowerSeries d := fun i => toSeq d (A.sem (X i))
    have hlift_all : ∀ i, toSeries d (f i) = A.sem (X i) := by
      intro i
      dsimp [f]
      exact toSeries_toSeq d (A.sem (X i)) (hcomm i)
    have hcomp : SolvesCompanion d k (fun i => A.sem (X i)) p c := companion_solves d k hd hk p c
    have hf : SolvesCDA d k f p c := by
      constructor
      · intro i
        dsimp [f, toSeq]
        have hce : CommutativelyEquivalent (Fin d) (wordFromParikh d 0) [] := by
          rw [CommutativelyEquivalent, Multiset.ext]
          intro a
          rw [Multiset.coe_count, Multiset.coe_count]
          have hpar : parikh (Fin d) (wordFromParikh d 0) = parikh (Fin d) [] := by
            rw [wordFromParikh_parikh]
            funext a
            simp [parikh]
          simpa [parikh] using congrArg (fun q : Fin d → ℕ => q a) hpar
        rw [(hcomm i) (wordFromParikh d 0) [] hce]
        exact hcomp.1 i
      · intro i j
        have h1 : toSeries d (expDeriv d j (f i)) = leftDeriv (Fin d) j (toSeries d (f i)) :=
          toSeries_expDeriv d j (f i)
        have h2 : leftDeriv (Fin d) j (toSeries d (f i)) = leftDeriv (Fin d) j (A.sem (X i)) := by
          rw [hlift_all i]
        have h3 : leftDeriv (Fin d) j (A.sem (X i)) =
            shuffleEval (Fin d) k (fun i => A.sem (X i)) (p i j) := hcomp.2 i j
        have h4 : toSeries d (evalCDA d k f (p i j)) =
            shuffleEval (Fin d) k (fun i => toSeries d (f i)) (p i j) := toSeries_evalCDA d k f (p i j)
        have hfs : (fun i => toSeries d (f i)) = (fun i => A.sem (X i)) := by
          funext i'
          exact hlift_all i'
        have h5 : shuffleEval (Fin d) k (fun i => toSeries d (f i)) (p i j) =
            shuffleEval (Fin d) k (fun i => A.sem (X i)) (p i j) :=
          congrArg (fun fs => shuffleEval (Fin d) k fs (p i j)) hfs
        have hleft : toSeries d (expDeriv d j (f i)) =
            shuffleEval (Fin d) k (fun i => A.sem (X i)) (p i j) := by
          calc
            toSeries d (expDeriv d j (f i)) = leftDeriv (Fin d) j (toSeries d (f i)) := h1
            _ = leftDeriv (Fin d) j (A.sem (X i)) := h2
            _ = shuffleEval (Fin d) k (fun i => A.sem (X i)) (p i j) := h3
        have hright : toSeries d (evalCDA d k f (p i j)) =
            shuffleEval (Fin d) k (fun i => A.sem (X i)) (p i j) := by
          calc
            toSeries d (evalCDA d k f (p i j)) =
                shuffleEval (Fin d) k (fun i => toSeries d (f i)) (p i j) := h4
            _ = shuffleEval (Fin d) k (fun i => A.sem (X i)) (p i j) := h5
        have h6 : toSeries d (expDeriv d j (f i)) = toSeries d (evalCDA d k f (p i j)) := by
          rw [hleft, hright]
        have h7 : toSeq d (toSeries d (expDeriv d j (f i))) =
            toSeq d (toSeries d (evalCDA d k f (p i j))) := by rw [h6]
        rw [toSeq_toSeries d _, toSeq_toSeries d _] at h7
        exact h7
    exact ⟨f, hf⟩

/-! ### Decidability of the commutative components -/

/-- `A.sem (X_i)` is shuffle-finite in the semantic sense: it is the shuffle polynomial
    `X_i` in the left-derivative-closed tuple `(A.sem (X_0), …, A.sem (X_{k-1}))`. -/
private theorem shuffleFiniteSem_sem (α : Type*) (A : ShuffleAutomaton α) (i : Fin A.dim) :
    IsShuffleFinite α (A.sem (X i)) := by
  refine ⟨A.dim, fun j => A.sem (X j), X i, ?_, ?_⟩
  · exact sem_eq_shuffleEval A (X i)
  · intro a j
    refine ⟨A.Δ a j, ?_⟩
    calc
      leftDeriv α a (A.sem (X j)) = A.sem (derivationExt (A.Δ a) (X j)) := sem_deriv A a (X j)
      _ = A.sem (A.Δ a j) := by rw [derivationExt_X]
      _ = shuffleEval α A.dim (fun j' => A.sem (X j')) (A.Δ a j) :=
        sem_eq_shuffleEval A (A.Δ a j)

/-- `A.sem (X_i)` is shuffle-recognisable (by the coincidence, from shuffle-finite). -/
private theorem recognisable_sem (α : Type*) (A : ShuffleAutomaton α) (i : Fin A.dim) :
    IsShuffleRecognisable α (A.sem (X i)) :=
  (ShuffleCoincidence (A.sem (X i))).mp (shuffleFiniteSem_sem α A i)

/-- An automaton whose recognised series is `A.sem (X_i)` (chosen by the axiom of
    choice). -/
noncomputable def companionComponent (α : Type*) (A : ShuffleAutomaton α) (i : Fin A.dim) :
    ShuffleAutomaton α := Classical.choose (recognisable_sem α A i)

private theorem companionComponent_spec (α : Type*) (A : ShuffleAutomaton α) (i : Fin A.dim) :
    (companionComponent α A i).recognised = A.sem (X i) :=
  Classical.choose_spec (recognisable_sem α A i)

/-! ### The main theorem -/

/--
---
conclusion: Lax946791.CDA.CDASolvability
assumptions:
  - Lax946791.Shuffle.ShuffleCommutativityDecidable
---
The CDA solvability problem is decidable (paper §6.4): the decision reduces to
checking that all components of the companion shuffle automaton's recognised series
are commutative, each decided by `ShuffleCommutativityDecidable` (the meta-theorem
applied to the effective prevariety of shuffle-finite series).
-/
theorem CDASolvability (d k : ℕ) (hd : 0 < d) (hk : 0 < k) :
    ∃ dec : (Fin k → Fin d → MvPolynomial (Fin k) ℚ) → (Fin k → ℚ) → Bool,
      ∀ p c, dec p c = true ↔ ∃ f : Fin k → Lax946791.CDA.ExpPowerSeries d, SolvesCDA d k f p c := by
  obtain ⟨dcomm, hdcomm⟩ := ShuffleCommutativityDecidable (Fin d)
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
      ∃ f : Fin k → Lax946791.CDA.ExpPowerSeries d, SolvesCDA d k f p c :=
    (bridge d k hd hk p c).symm
  calc
    dec p c = true ↔ ∀ i, IsCommutative (Fin d) (A.sem (X i)) := hdec
    _ ↔ ∃ f : Fin k → Lax946791.CDA.ExpPowerSeries d, SolvesCDA d k f p c := hbridge

end Lax946791Proofs.CDA
