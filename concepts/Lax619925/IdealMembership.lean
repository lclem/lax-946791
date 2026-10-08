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
The ideal-membership statement on which the paper's unified ideal-chain
argument rests.  It says that ideal membership in `MvPolynomial (Fin k) ℚ`
is decidable in the propositional sense: for every finite set of generators
`gens`, there exists a `Bool`-valued function `dec` such that `dec p = true`
exactly when `p` lies in the ideal `gens` generates — the same shape as the
other `*EqualityDecidable` statements.  It is proven in the proofs package by
a classical argument: excluded middle supplies the characteristic function of
the ideal.  The constructive Gröbner-basis decision procedure (Buchberger's
algorithm) — the Gröbner-basis fact mathlib does not yet provide, its
`MvPolynomial.Groebner` file implementing division only — is the algorithmic
content of the paper's decidability claims and is out of scope for this
submission.  The paper's unified ideal-chain argument (the chain `I_n` of
ideals stabilising by Hilbert's basis theorem) reduces the equality problem
for the Hadamard, shuffle, and infiltration automata to this statement.
-/

namespace Lax619925.IdealMembership

/-- Ideal membership in the multivariate polynomial ring over `ℚ` is decidable:
    given a finite set of generators, there is a decision procedure `dec` such
    that `dec p = true` iff `p` lies in the ideal the generators span.  Proven
    in the proofs package by a classical argument (excluded middle supplies the
    characteristic function); the constructive Gröbner-basis procedure is out
    of scope. -/
axiom IdealMembershipDecidable (k : ℕ) (gens : Finset (MvPolynomial (Fin k) ℚ)) :
  ∃ dec : MvPolynomial (Fin k) ℚ → Bool, ∀ p, dec p = true ↔ p ∈ Ideal.span ↑gens

end Lax619925.IdealMembership
