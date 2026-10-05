import Lax946791.PolynomialAutomata
import Lax946791.Hadamard
import Lax946791.Series
import Mathlib.Data.Real.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Eval

/-!
Polynomial-vs-Hadamard duality (paper appendix, `app:polynomial automata`):
a series is recognisable by a polynomial automaton iff its reversal is
Hadamard-finite.  The "only if" direction reads the polynomial automaton's
states backwards (the `g_i` are the component series `w ↦ π_i(q_I · w^R)`),
which land in the Hadamard algebra they generate and are closed under left
derivatives; the "if" direction rebuilds a polynomial automaton from a
left-derivative-closed Hadamard algebra, by induction on the word.
-/

namespace Lax946791Proofs.PolynomialAutomata

open Lax946791.PolynomialAutomata Lax946791.Hadamard Lax946791.Series

variable {α : Type*}

/-- Point evaluation of a polynomial at the pointwise values of a family of
    series equals the Hadamard-algebra evaluation at the same word: both sides
    are `∑ m ∈ p.support, p.coeff m * ∏ i, (fs i w) ^ m i`. -/
private theorem eval_hadamardEval (k : ℕ) (fs : Fin k → Series α) (p : MvPolynomial (Fin k) ℚ)
    (w : List α) :
    MvPolynomial.eval (fun i => fs i w) p = hadamardEval α k fs p w := by
  simp [hadamardEval, MvPolynomial.eval_eq']

/-- The word action of a polynomial automaton is a (left) action:
    `q · (u ++ v) = (q · u) · v`, and `q · [] = q`. -/
private theorem wordAction_append (A : PolynomialAutomaton α) (q : Fin A.dim → ℚ) (u v : List α) :
    A.wordAction q (u ++ v) = A.wordAction (A.wordAction q u) v := by
  simp [PolynomialAutomaton.wordAction, List.foldl_append]

private theorem wordAction_nil (A : PolynomialAutomaton α) (q : Fin A.dim → ℚ) :
    A.wordAction q [] = q := by
  simp [PolynomialAutomaton.wordAction]

/-- Acting with a single letter `[a]` is the one-step action: `q · [a] = q · a`. -/
private theorem wordAction_singleton (A : PolynomialAutomaton α) (q : Fin A.dim → ℚ) (a : α) :
    A.wordAction q [a] = A.action q a := by
  simp [PolynomialAutomaton.wordAction, List.foldl_cons, List.foldl_nil]

/-- The `i`-th component of the one-step action is the `i`-th transition
    polynomial evaluated at the point `q`. -/
private theorem action_i (A : PolynomialAutomaton α) (q : Fin A.dim → ℚ) (a : α) (i : Fin A.dim) :
    (A.action q a) i = MvPolynomial.eval q (A.Δ a i) := by
  simp [PolynomialAutomaton.action]

/-- Reversing a cons gives a snoc: `(a :: w).reverse = w.reverse ++ [a]`. -/
private theorem reverse_cons (a : α) (w : List α) : (a :: w).reverse = w.reverse ++ [a] := by
  simp [List.reverse_cons]

/-- A constant series is polynomial-recognisable: a one-dimensional automaton
    with identity transitions and output the first coordinate. -/
private theorem constPolynomialRecognisable (c : ℚ) :
    IsPolynomialRecognisable α (fun _ => c) := by
  let B : PolynomialAutomaton α := {
    dim := 1, hdim := by decide,
    qI := fun _ => c,
    F := (MvPolynomial.X (Fin.mk 0 (by decide)) : MvPolynomial (Fin 1) ℚ),
    Δ := fun _ i => (MvPolynomial.X i : MvPolynomial (Fin 1) ℚ) }
  have hact : ∀ q a, B.action q a = q := by
    intro q a
    change (fun i => MvPolynomial.eval q (B.Δ a i)) = q
    funext i
    dsimp [B]
    rw [MvPolynomial.eval_X]
  have hword : ∀ q w, B.wordAction q w = q := by
    intro q w
    induction w with
    | nil => simp [PolynomialAutomaton.wordAction]
    | cons a v ih =>
      simp [PolynomialAutomaton.wordAction, List.foldl_cons]
      rw [hact q a, ← PolynomialAutomaton.wordAction, ih]
  refine ⟨B, ?_⟩
  funext w
  dsimp [PolynomialAutomaton.recognised, PolynomialAutomaton.sem]
  rw [hword B.qI w]
  dsimp [B]
  rw [MvPolynomial.eval_X]

/--
---
conclusion: Lax946791.PolynomialAutomata.PolynomialHadamardEquivalence
assumptions:
  - Lax946791.Hadamard.HadamardCoincidence
  - Lax946791.Series.ReversalInvolution
---
A series is recognisable by a polynomial automaton iff its reversal is
Hadamard-finite (paper appendix).  Only-if: the component series
`g_i(w) = π_i(q_I · w^R)` generate a Hadamard algebra closed under left
derivatives containing `f^R = F(g_1, …, g_k)`.  If: from a left-derivative-
closed Hadamard algebra `ℚ{g_1, …, g_k}` containing `f^R = F(g_1, …, g_k)`,
rebuild the polynomial automaton with initial state `(g_1(ε), …, g_k(ε))`
and transitions given by the left-derivative polynomials; an induction on the
word shows `g_i(w) = π_i(q_I · w^R)`, hence `f = ⟦B⟧`.
-/
theorem PolynomialHadamardEquivalence (f : Series α) :
    IsPolynomialRecognisable α f ↔ IsHadamardRecognisable α (reversal α f) := by
  constructor
  · -- (→) polynomial-recognisable ⇒ reversal is Hadamard-recognisable
    rintro ⟨A, hA⟩
    rw [← HadamardCoincidence]
    let g : Fin A.dim → Series α := fun i w => (A.wordAction A.qI w.reverse) i
    refine ⟨A.dim, g, A.F, ?_, ?_⟩
    · -- f^R = F(g_1, …, g_k)
      funext w
      have hL : (reversal α f) w = f w.reverse := by dsimp [reversal]
      rw [hL, ← hA]
      have hsem : (A.recognised) w.reverse = MvPolynomial.eval (A.wordAction A.qI w.reverse) A.F := by
        dsimp [PolynomialAutomaton.recognised, PolynomialAutomaton.sem]
      rw [hsem]
      have hR : (hadamardEval α A.dim g A.F) w = MvPolynomial.eval (fun i => g i w) A.F := by
        rw [eval_hadamardEval]
      rw [hR]
    · -- leftDeriv a (g_i) = Δ^a_i(g_1, …, g_k)
      intro a i
      refine ⟨A.Δ a i, ?_⟩
      funext w
      have hL : (leftDeriv α a (g i)) w = (A.wordAction A.qI (a :: w).reverse) i := by
        dsimp [leftDeriv, g]
      rw [hL, reverse_cons, wordAction_append, wordAction_singleton, action_i]
      have hR : (hadamardEval α A.dim g (A.Δ a i)) w = MvPolynomial.eval (fun j => g j w) (A.Δ a i) := by
        rw [eval_hadamardEval]
      rw [hR]
  · -- (←) reversal is Hadamard-recognisable ⇒ polynomial-recognisable
    intro hrec
    have hfin : IsHadamardFinite α (reversal α f) := (HadamardCoincidence α (reversal α f)).mpr hrec
    obtain ⟨k, fs, p, hrep, hclosed⟩ := hfin
    by_cases hk0 : k = 0
    · -- k = 0: reversal f is a constant series, so f is constant
      have hconst : reversal α f = fun _ => (reversal α f) [] := by
        subst k
        rw [hrep]
        funext w
        simp [hadamardEval]
      let c : ℚ := (reversal α f) []
      have hconst' : reversal α f = fun _ => c := by simpa [c] using hconst
      have hf : f = fun _ => c := by
        rw [← ReversalInvolution α f, hconst']
        funext w
        dsimp [reversal]
      rw [hf]
      exact constPolynomialRecognisable c
    · -- k > 0: rebuild the polynomial automaton
      have hk : 0 < k := Nat.pos_of_ne_zero hk0
      let Δ : α → Fin k → MvPolynomial (Fin k) ℚ := fun a i => Classical.choose (hclosed a i)
      have hΔ : ∀ a i, leftDeriv α a (fs i) = hadamardEval α k fs (Δ a i) := fun a i =>
        Classical.choose_spec (hclosed a i)
      let qI : Fin k → ℚ := fun i => fs i []
      let B : PolynomialAutomaton α := { dim := k, hdim := hk, qI := qI, F := p, Δ := Δ }
      -- Claim 1: fs i w = π_i(q_I · w^R)  (induction on w, `i` in the hypothesis)
      have hgen : ∀ w i, fs i w = (B.wordAction qI w.reverse) i := by
        intro w
        induction w with
        | nil =>
          intro i
          dsimp [qI, B]
          rw [wordAction_nil]
        | cons a v ih =>
          intro i
          dsimp [qI, B]
          have hstep : fs i (a :: v) = (leftDeriv α a (fs i)) v := by dsimp [leftDeriv]
          rw [hstep, hΔ a i]
          have hR : (hadamardEval α k fs (Δ a i)) v = MvPolynomial.eval (fun j => fs j v) (Δ a i) := by
            rw [eval_hadamardEval]
          rw [hR]
          have hIH : (fun j => fs j v) = B.wordAction qI v.reverse := by
            funext j
            rw [ih j]
          rw [hIH]
          have hact : MvPolynomial.eval (B.wordAction qI v.reverse) (Δ a i) =
              (B.action (B.wordAction qI v.reverse) a) i := by
            dsimp [B]
            rw [action_i]
          rw [hact]
          have hsnoc : B.wordAction qI (a :: v).reverse =
              B.wordAction (B.wordAction qI v.reverse) [a] := by
            rw [reverse_cons, wordAction_append]
          have hsingle : (B.action (B.wordAction qI v.reverse) a) i =
              (B.wordAction (B.wordAction qI v.reverse) [a]) i := by
            rw [wordAction_singleton]
          rw [hsnoc, hsingle]
      -- Claim 2: f = ⟦B⟧
      have hsem : f = B.recognised := by
        funext w
        have h1 : f w = (reversal α f) w.reverse := by
          dsimp [reversal]
          rw [List.reverse_reverse]
        have h2 : (reversal α f) w.reverse = (hadamardEval α k fs p) w.reverse := by
          rw [hrep]
        have h3 : (hadamardEval α k fs p) w.reverse = MvPolynomial.eval (fun i => fs i w.reverse) p := by
          rw [eval_hadamardEval]
        rw [h1, h2, h3]
        have hIH : (fun i => fs i w.reverse) = B.wordAction qI w := by
          funext i
          rw [hgen (w.reverse) i]
          rw [List.reverse_reverse]
        rw [hIH]
        dsimp [B, PolynomialAutomaton.recognised, PolynomialAutomaton.sem]
      exact ⟨B, hsem.symm⟩

end Lax946791Proofs.PolynomialAutomata
