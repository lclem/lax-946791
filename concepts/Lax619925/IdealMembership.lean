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
The single open leaf of this submission.  The leaf states that ideal membership
in `MvPolynomial (Fin k) ℚ` is decidable: for every finite set of generators
`gens`, there exists a decision procedure `dec` such that `dec p = true` exactly
when `p` lies in the ideal `gens` generates.  This is the Gröbner-basis fact
that mathlib does not yet provide (its `MvPolynomial.Groebner` file implements
reduction only, with no decision procedure), stated propositionally as an
existential over a `Bool`-valued function — the same shape as the other
`*EqualityDecidable` axioms.  The paper's unified ideal-chain argument (the
chain `I_n` of ideals stabilising by Hilbert's basis theorem) reduces the
equality problem for the Hadamard, shuffle, and infiltration automata to exactly
this leaf.
-/

namespace Lax619925.IdealMembership

/-- Ideal membership in the multivariate polynomial ring over `ℚ` is decidable:
    given a finite set of generators, there is a decision procedure `dec` such
    that `dec p = true` iff `p` lies in the ideal the generators span.  This is
    the Gröbner-basis fact absent from mathlib, stated propositionally (as an
    existential over a `Bool`-valued function), and is the single open leaf of
    the submission. -/
axiom IdealMembershipDecidable (k : ℕ) (gens : Finset (MvPolynomial (Fin k) ℚ)) :
  ∃ dec : MvPolynomial (Fin k) ℚ → Bool, ∀ p, dec p = true ↔ p ∈ Ideal.span ↑gens

end Lax619925.IdealMembership
