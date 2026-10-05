import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.Ideal.Basic

/-!
---
title: Ideal membership in multivariate polynomials
type: theorem
---
The single open leaf of this submission.  Deciding whether a polynomial lies in a
given ideal of `MvPolynomial (Fin k) ℚ` (the ideal-membership problem) is the
Gröbner-basis fact that mathlib does not yet provide: its `MvPolynomial.Groebner`
file implements reduction only, with no decision procedure.  The paper's unified
ideal-chain argument (the chain `I_n` of ideals stabilising by Hilbert's basis
theorem) reduces the equality problem for the Hadamard, shuffle, and infiltration
automata to exactly this leaf.
-/

namespace Lax946791.IdealMembership

/-- Ideal membership in the multivariate polynomial ring over `ℚ` is decidable:
    given a finite set of generators and a polynomial, one can decide whether the
    polynomial lies in the ideal they generate.  This is the Gröbner-basis fact
    absent from mathlib, and the single open leaf of the submission. -/
axiom IdealMembershipDecidable (k : ℕ)
    (gens : Finset (MvPolynomial (Fin k) ℚ)) (p : MvPolynomial (Fin k) ℚ) :
  Decidable (p ∈ Ideal.span ↑gens)

end Lax946791.IdealMembership
