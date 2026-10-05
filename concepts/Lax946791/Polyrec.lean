import Lax946791.Series
import Lax946791.Hadamard
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.MvPolynomial.Basic

/-!
---
title: Multivariate polynomial recursive sequences
type: theorem
---
A *multivariate polynomial recursive sequence* (polyrec sequence) in `d` variables
is a `k`-tuple of sequences `f : ℕ^d → ℚ` satisfying polynomial equations
`shift_j f_i = p^{(j)}_i(f_1, …, f_k)` (paper §5.4), where `shift_j` is the shift
in the `j`-th coordinate and `p^{(j)}_i` are polynomials evaluated pointwise in the
sequences.  The *consistency problem* asks whether, given the equations and an
initial condition `f_i(0) = c_i`, a solution exists.  This is decidable (paper
§5.4, theorem `polyrec consistency`): the polyrec system is isomorphic to a
Hadamard system over the `d`-letter alphabet, so a solution exists exactly when
the companion Hadamard series are commutative, which is decidable.
-/

namespace Lax946791.Polyrec

open Lax946791.Series Lax946791.Hadamard

/-- A multivariate sequence in `d` variables: a function `ℕ^d → ℚ`, represented
    as a function on the multi-index type `Fin d → ℕ`. -/
abbrev Seq (d : ℕ) := (Fin d → ℕ) → ℚ

/-- The shift of a multivariate sequence in the `j`-th coordinate:
    `(shift d j f) n = f (n + e_j)`, where `e_j` is the `j`-th unit vector.
    The shifts in different coordinates commute. -/
def shift (d : ℕ) (j : Fin d) (f : Seq d) : Seq d :=
  fun n => f (fun i => n i + if i = j then 1 else 0)

/-- The pointwise (Hadamard-algebra) evaluation of the polynomial `p` at the tuple
    of sequences `fs`: `evalSeq d k fs p n = Σ_m p.coeff m · ∏_i (fs i n)^{m i}`,
    the interpretation of `p` in the pointwise ring of sequences, where the
    variable `X_i` is mapped to `fs i` and the multiplication is pointwise. -/
def evalSeq (d k : ℕ) (fs : Fin k → Seq d) (p : MvPolynomial (Fin k) ℚ) : Seq d :=
  fun n => p.support.sum fun m => p.coeff m * ∏ i : Fin k, (fs i) n ^ (m i)

/-- A `k`-tuple of multivariate sequences `f` *solves* the polyrec system
    `(p, c)` if it satisfies the initial condition `f_i(0) = c_i` and the
    polynomial equations `shift_j f_i = p^{(j)}_i(f_1, …, f_k)` for all `i, j`,
    where `p^{(j)}_i` is evaluated pointwise in the sequences (the Hadamard
    algebra).  Here `0` is the zero multi-index, the origin of `ℕ^d`. -/
def SolvesPolyrec (d k : ℕ) (f : Fin k → Seq d)
    (p : Fin k → Fin d → MvPolynomial (Fin k) ℚ) (c : Fin k → ℚ) : Prop :=
  (∀ i, f i 0 = c i) ∧ ∀ i j, shift d j (f i) = evalSeq d k f (p i j)

/-- The polyrec consistency problem is decidable (paper §5.4, theorem
    `polyrec consistency`): there is a procedure that, given the polynomial
    equations `p` and the initial condition `c`, decides whether a solution
    exists.  The decision reduces to the commutativity of the companion Hadamard
    series, which is decidable. -/
axiom PolyrecConsistency (d k : ℕ) (hd : 0 < d) (hk : 0 < k) :
  ∃ dec : (Fin k → Fin d → MvPolynomial (Fin k) ℚ) → (Fin k → ℚ) → Bool,
    ∀ p c, dec p c = true ↔ ∃ f : Fin k → Seq d, SolvesPolyrec d k f p c

end Lax946791.Polyrec
