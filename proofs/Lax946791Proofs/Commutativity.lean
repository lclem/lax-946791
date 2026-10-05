import Lax946791.Commutativity
import Lax946791.Series
import Lax946791.Prevariety
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Rotate
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Multiset.AddSub
import Mathlib.Data.Multiset.ZeroCons
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Lax946791Proofs.Commutativity

open Lax946791.Commutativity Lax946791.Series Lax946791.Prevariety
open List

variable (α : Type*)

/-- Swap the first two letters of a word, leaving shorter words unchanged. -/
def swapFirst2 (w : List α) : List α :=
  match w with
  | b :: a :: rest => a :: b :: rest
  | _ => w

/-- Swap the two letters at positions `i` and `i + 1` (0-indexed), leaving the word
    unchanged when there are not two letters there. -/
def swapAdjacent (w : List α) (i : ℕ) : List α :=
  let pre := w.take i
  let mid := w.drop i
  match mid with
  | x :: y :: tail => pre ++ y :: x :: tail
  | _ => w

/-- The reflexive-transitive closure of "differ by a single adjacent transposition." -/
inductive AdjacentReach : List α → List α → Prop where
  | refl (u : List α) : AdjacentReach u u
  | step (u v w : List α) (i : ℕ) (hv : v = swapAdjacent α u i)
      (rest : AdjacentReach v w) : AdjacentReach u w

/-- Transitivity of adjacent reachability. -/
private theorem AdjacentReach.trans {u v w : List α}
    (h1 : AdjacentReach α u v) (h2 : AdjacentReach α v w) : AdjacentReach α u w := by
  induction h1 with
  | refl => exact h2
  | step u₁ v₁ v₂ i hv rest ih =>
    exact .step _ _ _ i hv (ih h2)

/-- The coercion of a cons to a multiset is the singleton plus the coercion of the tail. -/
private theorem ofList_cons' (a : α) (l : List α) :
    (a :: l : Multiset α) = {a} + (l : Multiset α) := by
  rw [← Multiset.coe_singleton, Multiset.coe_add]
  rfl

/-- A series satisfying the rotate equation is invariant under a one-step rotation:
    `f (w.rotate 1) = f w`.  For `w = a :: w'` this is exactly
    `f (a :: w') = f (w' ++ [a])`; the empty word is fixed by rotation. -/
private theorem fRotate1Inv (f : Series α) (hrot : SatisfiesRotate α f) (w : List α) :
    f (w.rotate 1) = f w := by
  cases w with
  | nil => simp [rotate]
  | cons a w' =>
    rw [List.rotate_cons_succ w' a 0, List.rotate_zero]
    have := congrArg (fun g => g w') (hrot a)
    simpa [leftDeriv, rightDeriv] using this.symm

/-- A series satisfying the rotate equation is invariant under rotation by any amount. -/
private theorem fRotateInv (f : Series α) (hrot : SatisfiesRotate α f) (w : List α) (k : ℕ) :
    f (w.rotate k) = f w := by
  induction k with
  | zero => simp [rotate]
  | succ k ih =>
    rw [← List.rotate_rotate w k 1]
    trans f (w.rotate k)
    · exact fRotate1Inv α f hrot (w.rotate k)
    · exact ih

/-- A series satisfying the swap equation is invariant under swapping the first two
    letters: `f (swapFirst2 w) = f w`. -/
private theorem fSwap2Inv (f : Series α) (hswap : SatisfiesSwap α f) (w : List α) :
    f (swapFirst2 α w) = f w := by
  cases w with
  | nil => simp [swapFirst2]
  | cons b w' =>
    cases w' with
    | nil => simp [swapFirst2]
    | cons a rest =>
      simp [swapFirst2]
      have := congr_arg (fun g => g rest) (hswap a b)
      simpa [leftDeriv] using this.symm

/-- A series satisfying the rotate equation is invariant under cyclically permuting an
    append: `f (p ++ r) = f (r ++ p)`, since `r ++ p` is a rotation of `p ++ r`. -/
private theorem fAppendRotate (f : Series α) (hrot : SatisfiesRotate α f) (p r : List α) :
    f (p ++ r) = f (r ++ p) := by
  trans f ((p ++ r).rotate p.length)
  · exact (fRotateInv α f hrot (p ++ r) p.length).symm
  · rw [List.rotate_append_length_eq]

/-- An adjacent transposition in the tail lifts to the cons-extended word:
    `swapAdjacent (a :: u) (i + 1) = a :: swapAdjacent u i`. -/
private theorem swapAdjacent_cons (a : α) (u : List α) (i : ℕ) :
    swapAdjacent α (a :: u) (i + 1) = a :: swapAdjacent α u i := by
  simp [swapAdjacent]
  cases u.drop i with
  | nil => simp_all
  | cons x d =>
    cases d with
    | nil => simp_all
    | cons y d2 => simp_all

/-- Swapping the first two letters is the identity on words of length < 2. -/
private theorem swapFirst2_id_short (q : List α) (h : q.length < 2) :
    swapFirst2 α q = q := by
  cases q with
  | nil => simp [swapFirst2]
  | cons x d =>
    cases d with
    | nil => simp [swapFirst2]
    | cons y d2 =>
      exfalso
      simp at h

/-- When the left part has at least two letters, swapping its first two and then
    appending the right part equals swapping the first two of the whole append. -/
private theorem swapFirst2_append (q p : List α) (h : 2 ≤ q.length) :
    swapFirst2 α q ++ p = swapFirst2 α (q ++ p) := by
  cases q with
  | nil => exfalso; simp at h
  | cons x d =>
    cases d with
    | nil => exfalso; simp at h
    | cons y d2 => simp [swapFirst2]

/-- `swapAdjacent w i` is the prefix of length `i` followed by the first-two-swapped
    tail: `swapAdjacent w i = w.take i ++ swapFirst2 (w.drop i)`.  Both sides match on
    `w.drop i`: when it has two or more letters the transposition swaps its first two,
    and when it is shorter both sides reduce to `w`. -/
private theorem swapAdjacent_take_swapFirst2 (w : List α) (i : ℕ) :
    swapAdjacent α w i = w.take i ++ swapFirst2 α (w.drop i) := by
  have : ∀ (i : ℕ) (w : List α), swapAdjacent α w i = w.take i ++ swapFirst2 α (w.drop i) := by
    intro i
    induction i with
    | zero =>
      intro w
      simp [swapAdjacent, swapFirst2, List.take_zero, List.drop_zero]
    | succ i ih =>
      intro w
      cases w with
      | nil =>
        simp [swapAdjacent, swapFirst2, List.take_nil, List.drop_nil]
      | cons a w' =>
        rw [swapAdjacent_cons α a w' i, List.take_succ_cons, List.drop_succ_cons, List.cons_append, ← ih w']
  exact this i w

/-- A series satisfying both the swap and the rotate equations is invariant under an
    adjacent transposition at any position: `f (swapAdjacent w i) = f w`.  Writing
    `w = p ++ q` with `p = w.take i` and `q = w.drop i`, the transposition swaps the
    first two letters of `q`; when `q` has at least two letters this is a first-two swap
    of `q ++ p` (conjugated by the invariance under cyclic permutation of an append), and
    when `q` is shorter the transposition is a no-op. -/
private theorem fSwapInv (f : Series α) (hswap : SatisfiesSwap α f)
    (hrot : SatisfiesRotate α f) (w : List α) (i : ℕ) : f (swapAdjacent α w i) = f w := by
  rw [swapAdjacent_take_swapFirst2 α w i]
  by_cases hq : 2 ≤ (w.drop i).length
  · trans f (w.take i ++ w.drop i)
    · calc f (w.take i ++ swapFirst2 α (w.drop i))
        _ = f (swapFirst2 α (w.drop i) ++ w.take i) :=
          fAppendRotate α f hrot (w.take i) (swapFirst2 α (w.drop i))
        _ = f (w.drop i ++ w.take i) := by
          rw [swapFirst2_append α (w.drop i) (w.take i) hq]
          exact fSwap2Inv α f hswap (w.drop i ++ w.take i)
        _ = f (w.take i ++ w.drop i) :=
          (fAppendRotate α f hrot (w.take i) (w.drop i)).symm
    · rw [List.take_append_drop]
  · have hq' : swapFirst2 α (w.drop i) = w.drop i :=
      swapFirst2_id_short α (w.drop i) (by omega)
    rw [hq', List.take_append_drop]

/-- A series satisfying both equations is invariant under any sequence of adjacent
    transpositions. -/
private theorem fReachInv (f : Series α) (hswap : SatisfiesSwap α f)
    (hrot : SatisfiesRotate α f) {u v : List α} (r : AdjacentReach α u v) : f u = f v := by
  induction r with
  | refl => rfl
  | step u v w i hv rest ih =>
    have := fSwapInv α f hswap hrot u i
    trans f v
    · rw [hv]
      exact this.symm
    · exact ih

/-- If the tails are connected by adjacent transpositions, so are the cons-extended
    words: `u' ~adj v'` implies `a :: u' ~adj a :: v'`. -/
private theorem tailReachable (a : α) {u' v' : List α} (r : AdjacentReach α u' v') :
    AdjacentReach α (a :: u') (a :: v') := by
  induction r with
  | refl => exact .refl _
  | step u v w i hv rest ih =>
    have : a :: v = swapAdjacent α (a :: u) (i + 1) := by
      simp only [hv, swapAdjacent_cons]
    exact .step _ _ _ (i + 1) this ih

/-- If a letter `b` occurs in `u`, then `u` can be transformed by adjacent
    transpositions into a word beginning with `b`, whose multiset of letters is the
    multiset of `u` (one `b` moved to the front). -/
private theorem bubbleToFront (b : α) {u : List α} (hb : b ∈ u) :
    ∃ u', AdjacentReach α u (b :: u') ∧ (b :: u' : Multiset α) = (u : Multiset α) := by
  induction u with
  | nil =>
    cases hb
  | cons a u' ih =>
    by_cases h : a = b
    · subst a
      exact ⟨u', .refl _, rfl⟩
    · have hmem : b ∈ u' := by
        rcases List.mem_cons.mp hb with hab' | hu'
        · exfalso; exact h hab'.symm
        · exact hu'
      obtain ⟨u'', r, hu''⟩ := ih hmem
      have rcons : AdjacentReach α (a :: u') (a :: b :: u'') := tailReachable α a r
      have rstep : AdjacentReach α (a :: b :: u'') (b :: a :: u'') := by
        have : swapAdjacent α (a :: b :: u'') 0 = b :: a :: u'' := by
          simp [swapAdjacent]
        exact .step _ _ _ 0 this.symm (.refl _)
      have hu''s : {b} + (u'' : Multiset α) = (u' : Multiset α) := by
        simp only [ofList_cons'] at hu''
        exact hu''
      refine ⟨a :: u'', AdjacentReach.trans α rcons rstep, ?_⟩
      · simp only [ofList_cons']
        rw [hu''s.symm]
        ac_rfl

/-- Two words with the same multiset of letters are connected by adjacent
    transpositions.  Induct on the length (strongly): match the leading letters, and
    when they differ, bubble the leading letter of one word to the front of the other,
    reducing to a strictly shorter pair. -/
private theorem sameMultisetReachable {u v : List α}
    (h : (u : Multiset α) = (v : Multiset α)) : AdjacentReach α u v := by
  have recFn : ∀ n,
      (∀ m < n, ∀ (l₁ l₂ : List α), l₁.length = m → (l₁ : Multiset α) = (l₂ : Multiset α) → AdjacentReach α l₁ l₂) →
      ∀ (l₁ l₂ : List α), l₁.length = n → (l₁ : Multiset α) = (l₂ : Multiset α) → AdjacentReach α l₁ l₂ := by
    intro n ih l₁ l₂ hl₁ hl₂
    cases l₁ with
    | nil =>
      have : l₂ = [] := by
        rw [← List.length_eq_zero_iff, ← Multiset.coe_card, ← hl₂]
        simp
      subst l₂
      exact .refl _
    | cons a u' =>
      have hu' : u'.length = n - 1 := by
        rw [List.length_cons] at hl₁
        omega
      cases l₂ with
      | nil =>
        exfalso
        have ha : a ∈ (a :: u' : Multiset α) := by
          rw [ofList_cons']
          simp
        simp [hl₂] at ha
      | cons b v' =>
        have hmult : {a} + (u' : Multiset α) = {b} + (v' : Multiset α) := by
          rw [ofList_cons', ofList_cons'] at hl₂
          exact hl₂
        have hn : 0 < n := by
          rw [← hl₁]
          simp
        by_cases hab : a = b
        · subst b
          have hu'v' : (u' : Multiset α) = (v' : Multiset α) := by
            apply Multiset.add_right_inj.mp
            exact hmult
          have ih' : AdjacentReach α u' v' := ih (n - 1) (by omega) u' v' hu' hu'v'
          exact tailReachable α a ih'
        · have hmem : b ∈ u' := by
            have hbu : b ∈ (a :: u' : Multiset α) := by
              rw [hl₂]
              simp
            rw [ofList_cons'] at hbu
            rcases Multiset.mem_add.mp hbu with hab' | hu'
            · exfalso
              have := Multiset.mem_singleton.mp hab'
              exact hab this.symm
            · exact Multiset.mem_coe.mp hu'
          obtain ⟨u'', r, hu''⟩ := bubbleToFront α b hmem
          have hu''orig : (b :: u'' : Multiset α) = (u' : Multiset α) := hu''
          have rcons : AdjacentReach α (a :: u') (a :: b :: u'') := tailReachable α a r
          have rstep : AdjacentReach α (a :: b :: u'') (b :: a :: u'') := by
            have : swapAdjacent α (a :: b :: u'') 0 = b :: a :: u'' := by
              simp [swapAdjacent]
            exact .step _ _ _ 0 this.symm (.refl _)
          have r1 : AdjacentReach α (a :: u') (b :: a :: u'') := AdjacentReach.trans α rcons rstep
          have hu''s : {b} + (u'' : Multiset α) = (u' : Multiset α) := by
            simp only [ofList_cons'] at hu''
            exact hu''
          have hu''v' : (a :: u'' : Multiset α) = (v' : Multiset α) := by
            have h1 : (u' : Multiset α) = {b} + (u'' : Multiset α) := hu''s.symm
            have h2 : {a} + (u' : Multiset α) = {b} + (v' : Multiset α) := hmult
            rw [h1] at h2
            have h3 : {a} + ({b} + (u'' : Multiset α)) =
                {b} + ({a} + (u'' : Multiset α)) := by ac_rfl
            rw [h3] at h2
            have h4 : {a} + (u'' : Multiset α) = (v' : Multiset α) :=
              Multiset.add_right_inj.mp h2
            simpa using h4
          have ha'' : (a :: u'').length = n - 1 := by
            have hcard : (b :: u'').length = u'.length := by
              have hc : Multiset.card (b :: u'' : Multiset α) =
                  Multiset.card (u' : Multiset α) :=
                congrArg Multiset.card hu''orig
              rw [Multiset.coe_card, Multiset.coe_card] at hc
              exact hc
            calc (a :: u'').length
              _ = u''.length + 1 := by simp [List.length_cons]
              _ = (b :: u'').length := by simp [List.length_cons]
              _ = u'.length := hcard
              _ = n - 1 := hu'
          have ih' : AdjacentReach α (a :: u'') v' :=
            ih (n - 1) (by omega) (a :: u'') v' ha'' hu''v'
          have rcons2 : AdjacentReach α (b :: a :: u'') (b :: v') := tailReachable α b ih'
          exact AdjacentReach.trans α r1 rcons2
  exact (Nat.strongRecOn u.length recFn
      (motive := fun n => ∀ (l₁ l₂ : List α), l₁.length = n → (l₁ : Multiset α) = (l₂ : Multiset α) → AdjacentReach α l₁ l₂)) u v (by rfl) h

/--
---
conclusion: Lax946791.Commutativity.FiniteAxiomatisation
---
The characterisation of commutativity (paper §3, lemma `commutativity`): a series is
commutative if and only if it satisfies the swap and the rotate equations.  The forward
direction is immediate — the swap and rotate equations are exactly the commutative
equivalence of words differing by a transposition or a rotation.  The backward direction
uses that swaps and rotations connect any two words with the same multiset of letters, so
satisfying the two finite families of equations forces the series to be constant on
commutatively equivalent words.
-/
theorem FiniteAxiomatisation (f : Series α) :
    IsCommutative α f ↔ SatisfiesSwap α f ∧ SatisfiesRotate α f := by
  constructor
  · intro hcomm
    constructor
    · intro a b
      funext w
      have heq : CommutativelyEquivalent α (b :: a :: w) (a :: b :: w) := by
        simp only [CommutativelyEquivalent, ofList_cons']
        ac_rfl
      exact hcomm _ _ heq
    · intro a
      funext w
      have heq : CommutativelyEquivalent α (a :: w) (w ++ [a]) := by
        simp only [CommutativelyEquivalent, ofList_cons']
        ac_rfl
      exact hcomm _ _ heq
  · rintro ⟨hswap, hrot⟩ u v h
    have hms : (u : Multiset α) = (v : Multiset α) := by
      dsimp only [CommutativelyEquivalent] at h
      simpa using h
    have r := sameMultisetReachable α hms
    exact fReachInv α f hswap hrot r

/-- A `Decidable` instance, read as a `Bool` through its two branches, is `true` exactly
    when the proposition holds. -/
private theorem decCasesOnTrueIff {q : Prop} (d : Decidable q) :
    d.casesOn (fun _ => false) (fun _ => true) = true ↔ q := by
  cases d with
  | isTrue hq =>
    simp
    exact hq
  | isFalse hq =>
    simp
    exact hq

/-- `x && y = true` iff both `x` and `y` are `true`. -/
private theorem andTrueIff (x y : Bool) : Bool.and x y = true ↔ x = true ∧ y = true := by
  by_cases hx : x = true <;> by_cases hy : y = true <;> simp [hx, hy]

/-- Folding `and` over a finset (starting from `true`) is `true` exactly when every
    element's value is `true`. -/
private theorem foldAndTrueIff (s : Finset α) (f : α → Bool) :
    Finset.fold Bool.and true f s = true ↔ ∀ x ∈ s, f x = true := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp
  | insert a s ha ih =>
    rw [Finset.fold_insert ha, andTrueIff, ih, Finset.forall_mem_insert]

/--
---
conclusion: Lax946791.Commutativity.EffectivePrevarietyCommutativityDecidable
---
The commutativity problem is decidable for effective prevarieties (paper §3, the
meta-theorem).  By the finite axiomatisation, `sem r` is commutative exactly when it
satisfies the swap and the rotate equations.  Each of those is a finite family of
equalities between presentations (the alphabet is finite), and each equality is decided
by the prevariety's `decEq`.  A single boolean procedure therefore decides commutativity.
-/
theorem EffectivePrevarietyCommutativityDecidable [Fintype α] (P : EffectivePrevariety α) :
    ∃ d : P.Rep → Bool, ∀ r, d r = true ↔ IsCommutative α (P.sem r) := by
  let swapHolds (r : P.Rep) : Bool :=
    Finset.fold Bool.and true (fun a =>
      Finset.fold Bool.and true (fun b =>
        (P.decEq (P.derivL a (P.derivL b r)) (P.derivL b (P.derivL a r))).casesOn (fun _ => false) (fun _ => true))
      Finset.univ)
    Finset.univ
  let rotateHolds (r : P.Rep) : Bool :=
    Finset.fold Bool.and true (fun a =>
      (P.decEq (P.derivL a r) (P.derivR a r)).casesOn (fun _ => false) (fun _ => true))
    Finset.univ
  let d (r : P.Rep) : Bool := Bool.and (swapHolds r) (rotateHolds r)
  refine ⟨d, fun r => ?_⟩
  have swapSem (a b : α) : P.sem (P.derivL a (P.derivL b r)) = leftDeriv α a (leftDeriv α b (P.sem r)) := by
    rw [P.sem_derivL a (P.derivL b r), P.sem_derivL b r]
  have hswap : swapHolds r = true ↔ SatisfiesSwap α (P.sem r) := by
    have h1 : swapHolds r = true ↔
        (∀ a ∈ (Finset.univ : Finset α), ∀ b ∈ (Finset.univ : Finset α),
          (P.decEq (P.derivL a (P.derivL b r)) (P.derivL b (P.derivL a r))).casesOn (fun _ => false) (fun _ => true) = true) := by
      simp [swapHolds, foldAndTrueIff]
    have h2 : (∀ a ∈ (Finset.univ : Finset α), ∀ b ∈ (Finset.univ : Finset α),
          (P.decEq (P.derivL a (P.derivL b r)) (P.derivL b (P.derivL a r))).casesOn (fun _ => false) (fun _ => true) = true) ↔
        (∀ a b, P.sem (P.derivL a (P.derivL b r)) = P.sem (P.derivL b (P.derivL a r))) := by
      simp [Finset.mem_univ, decCasesOnTrueIff]
    have h3 : (∀ a b, P.sem (P.derivL a (P.derivL b r)) = P.sem (P.derivL b (P.derivL a r))) ↔
        SatisfiesSwap α (P.sem r) := by
      simp only [SatisfiesSwap]
      constructor
      · intro h a b
        have := h a b
        rw [swapSem a b, swapSem b a] at this
        exact this
      · intro h a b
        have := h a b
        rw [← swapSem a b, ← swapSem b a] at this
        exact this
    exact (h1.trans h2).trans h3
  have rotSemL (a : α) : P.sem (P.derivL a r) = leftDeriv α a (P.sem r) := P.sem_derivL a r
  have rotSemR (a : α) : P.sem (P.derivR a r) = rightDeriv α a (P.sem r) := P.sem_derivR a r
  have hrot : rotateHolds r = true ↔ SatisfiesRotate α (P.sem r) := by
    have h1 : rotateHolds r = true ↔
        (∀ a ∈ (Finset.univ : Finset α),
          (P.decEq (P.derivL a r) (P.derivR a r)).casesOn (fun _ => false) (fun _ => true) = true) := by
      simp [rotateHolds, foldAndTrueIff]
    have h2 : (∀ a ∈ (Finset.univ : Finset α),
          (P.decEq (P.derivL a r) (P.derivR a r)).casesOn (fun _ => false) (fun _ => true) = true) ↔
        (∀ a, P.sem (P.derivL a r) = P.sem (P.derivR a r)) := by
      simp [Finset.mem_univ, decCasesOnTrueIff]
    have h3 : (∀ a, P.sem (P.derivL a r) = P.sem (P.derivR a r)) ↔
        SatisfiesRotate α (P.sem r) := by
      simp only [SatisfiesRotate]
      constructor
      · intro h a
        have := h a
        rw [rotSemL a, rotSemR a] at this
        exact this
      · intro h a
        have := h a
        rw [← rotSemL a, ← rotSemR a] at this
        exact this
    exact (h1.trans h2).trans h3
  have hd : d r = true ↔ swapHolds r = true ∧ rotateHolds r = true := by
    simp [d]
  rw [hd, hswap, hrot]
  exact (FiniteAxiomatisation α (P.sem r)).symm

/-- `liftWordOpt` of the letter-lift of a word is `some` of the word. -/
private theorem liftWordOpt_mapLetter (w : List α) :
    liftWordOpt α (List.map Fresh2.letter w) = some w := by
  induction w with
  | nil => simp [liftWordOpt]
  | cons a w ih =>
    simp [liftWordOpt, List.map_cons, ih]

/-- Extending the zero series gives the zero series. -/
private theorem extendZero (w : List (Fresh2 α)) : extendSeries α 0 w = 0 := by
  simp [extendSeries]
  cases liftWordOpt α w with
  | some rest => simp
  | none => rfl

/-- The anti-derivative series of the zero series is the zero series. -/
private theorem antiDerivZero (w : List (Fresh2 α)) :
    antiDerivativeSeries α 0 w = 0 := by
  induction w with
  | nil => simp [antiDerivativeSeries]
  | cons a w ih =>
    cases a with
    | letter _ => simp [antiDerivativeSeries]
    | fresh0 =>
      cases w with
      | nil => simp [antiDerivativeSeries]
      | cons b w' =>
        cases b with
        | fresh1 => simp [antiDerivativeSeries, extendZero]
        | _ => simp [antiDerivativeSeries]
    | fresh1 => simp [antiDerivativeSeries]

/--
---
conclusion: Lax946791.Commutativity.AntiDerivativeCommutativeIffZero
---
The paper's reduction of the equality problem to commutativity.  `g` is supported only
on words beginning `fresh0 · fresh1`, where `g (fresh0 · fresh1 · w) = f w`.  If `g` is
commutative, then `f w = g (fresh0 · fresh1 · w) = g (fresh1 · fresh0 · w) = 0` (the two
words are commutatively equivalent), so `f = 0`.  Conversely `f = 0` forces `g = 0`, which
is commutative.
-/
theorem AntiDerivativeCommutativeIffZero (f : Series α) :
    IsCommutative (Fresh2 α) (antiDerivativeSeries α f) ↔ f = 0 := by
  constructor
  · intro hComm
    funext w
    have hEq : antiDerivativeSeries α f (Fresh2.fresh0 :: Fresh2.fresh1 :: List.map Fresh2.letter w) =
        antiDerivativeSeries α f (Fresh2.fresh1 :: Fresh2.fresh0 :: List.map Fresh2.letter w) :=
      hComm _ _ (by
        dsimp only [CommutativelyEquivalent]
        rw [Multiset.coe_eq_coe]
        exact List.Perm.swap Fresh2.fresh1 Fresh2.fresh0 (List.map Fresh2.letter w))
    simp [antiDerivativeSeries, extendSeries, liftWordOpt_mapLetter] at hEq
    exact hEq
  · intro hf u v _
    subst hf
    simp [antiDerivZero]
