import Lax619925.Series
import Lax619925.Shuffle
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.MvPolynomial.Basic

/-!
---
title: Multivariate constructible differentially algebraic power series
type: theorem
---
An *exponential multivariate power series* in `d` variables is a series
`f = Σ_n f_n x^n / n!` (paper §6.4), identified with its coefficient sequence
`f : ℕ^d → ℚ`.  It carries a binomial-convolution product and commuting partial
derivatives `∂_{x_j} f = Σ_n f_{n+e_j} x^n / n!` (the shift in the `j`-th
coordinate).  A *CDA system* is a `k`-tuple of such series satisfying
`∂_{x_j} f_i = p^{(j)}_i(f_1, …, f_k)`, the right-hand side a polynomial in the
binomial-convolution algebra.  The *solvability problem* asks whether, given the
equations and an initial condition `f_i(0) = c_i`, a solution exists.  This is
decidable (paper §6.4): the CDA system is isomorphic to a shuffle system over
the `d`-letter alphabet, so a solution exists exactly when the companion shuffle
series are commutative, which is decidable.
-/

namespace Lax619925.CDA

open Lax619925.Series Lax619925.Shuffle

/-- An exponential multivariate power series in `d` variables, identified with
    its coefficient sequence (the series is `Σ_n f_n x^n / n!`). -/
abbrev ExpPowerSeries (d : ℕ) := (Fin d → ℕ) → ℚ

/-- The binomial-convolution product of two exponential power series:
    `(expMul d f g) n = Σ_{m ≤ n} binom(n, m) f m · g (n - m)`, the product in the
    exponential (binomial) algebra, where the sum is over the multi-indices
    `m ≤ n` (coordinate-wise) and `binom(n, m) = ∏_i binom(n_i, m_i)` is the
    multinomial coefficient. -/
noncomputable def expMul (d : ℕ) (f g : ExpPowerSeries d) : ExpPowerSeries d :=
  fun n =>
    (Finset.univ.pi (fun i => Finset.range (n i + 1))).sum fun m =>
      let m' : Fin d → ℕ := fun i => m i (Finset.mem_univ i)
      (Finset.univ : Finset (Fin d)).prod (fun i => Nat.choose (n i) (m' i)) * f m' * g (fun i => n i - m' i)

/-- The partial derivative in the `j`-th coordinate:
    `(expDeriv d j f) n = f (n + e_j)`.  In the exponential normalisation this is
    the shift in the `j`-th coordinate; the partial derivatives commute. -/
def expDeriv (d : ℕ) (j : Fin d) (f : ExpPowerSeries d) : ExpPowerSeries d :=
  fun n => f (fun i => n i + if i = j then 1 else 0)

/-- The `n`-fold binomial-convolution power of an exponential power series:
    `expPow d f 0` is the constant-1 series and `expPow d f (n+1) = expMul d (expPow d f n) f`. -/
noncomputable def expPow (d : ℕ) (f : ExpPowerSeries d) (n : ℕ) : ExpPowerSeries d :=
  match n with
  | 0 => fun idx => if idx = 0 then 1 else 0
  | n + 1 => expMul d (expPow d f n) f

/-- The evaluation of the polynomial `p` at the tuple of exponential power series
    `fs`, in the binomial-convolution algebra: the variable `X_i` is mapped to
    `fs i` and the multiplication is the binomial-convolution product. -/
noncomputable def evalCDA (d k : ℕ) (fs : Fin k → ExpPowerSeries d) (p : MvPolynomial (Fin k) ℚ) :
    ExpPowerSeries d :=
  p.support.sum fun m =>
    p.coeff m • (Finset.univ : Finset (Fin k)).toList.foldr
      (fun i acc => expMul d acc (expPow d (fs i) (m i)))
      (fun idx => if idx = 0 then 1 else 0)

/-- A `k`-tuple of exponential power series `f` *solves* the CDA system `(p, c)`
    if it satisfies the initial condition `f_i(0) = c_i` and the differential
    equations `∂_{x_j} f_i = p^{(j)}_i(f_1, …, f_k)` for all `i, j`, the
    right-hand side a polynomial in the binomial-convolution algebra.  Here `0`
    is the zero multi-index. -/
def SolvesCDA (d k : ℕ) (f : Fin k → ExpPowerSeries d)
    (p : Fin k → Fin d → MvPolynomial (Fin k) ℚ) (c : Fin k → ℚ) : Prop :=
  (∀ i, f i 0 = c i) ∧ ∀ i j, expDeriv d j (f i) = evalCDA d k f (p i j)

/-- The CDA solvability problem is decidable (paper §6.4, theorem `decidability
    of CDA solvability`): there is a procedure that, given the polynomial
    equations `p` and the initial condition `c`, decides whether a power series
    solution exists.  The decision reduces to the commutativity of the companion
    shuffle series, which is decidable. -/
axiom CDASolvability (d k : ℕ) (hd : 0 < d) (hk : 0 < k) :
  ∃ dec : (Fin k → Fin d → MvPolynomial (Fin k) ℚ) → (Fin k → ℚ) → Bool,
    ∀ p c, dec p c = true ↔ ∃ f : Fin k → ExpPowerSeries d, SolvesCDA d k f p c

end Lax619925.CDA
