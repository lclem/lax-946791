import Lax946791.Series
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Module.Submodule.Basic

universe u

/-!
---
title: Prevarieties and effective prevarieties of series
type: definition
---
A *prevariety* of series over an alphabet `α` is a `ℚ`-subspace of the series
closed under the left and right derivatives (paper §2.3, conditions (V.1) and
(V.2)).  An *effective prevariety* is a prevariety whose elements admit finite
presentations (a type `Rep` with a semantics map) such that the closure
operations are carried out algorithmically on presentations and the equality
problem is decidable (paper §2.3, conditions (1)–(3)).  These are definitions
only; the decidability results built on them live in the `Commutativity` module.
-/

namespace Lax946791.Prevariety

open Lax946791.Series

-- the type and the module carrying it have the same name on purpose
set_option linter.dupNamespace false in
/-- A prevariety of series over `α`: a `ℚ`-subspace of `Series α` (the field
    `carrier`) that is closed under the left and right derivatives. -/
structure Prevariety (α : Type*) where
  carrier : Submodule ℚ (Series α)
  closedLeftDeriv : ∀ {f : Series α} (_hf : f ∈ carrier), ∀ a, leftDeriv α a f ∈ carrier
  closedRightDeriv : ∀ {f : Series α} (_hf : f ∈ carrier), ∀ a, rightDeriv α a f ∈ carrier

/-- Coercion from a prevariety to its underlying `ℚ`-submodule. -/
instance (α : Type*) : Coe (Prevariety α) (Submodule ℚ (Series α)) where
  coe P := P.carrier

/-- Membership in a prevariety: `f ∈ P` means that `f` belongs to the underlying
    `ℚ`-subspace of `P`. -/
instance (α : Type*) : Membership (Series α) (Prevariety α) where
  mem P f := f ∈ P.carrier

/-- An effective prevariety of series over `α`: a prevariety given by a type `Rep`
    of finite presentations with a semantics map `sem`, in which the vector-space
    operations and the left and right derivatives are computed by operations on
    presentations (the `sem_*` fields record their correctness), and on which the
    equality problem is decidable.  The fields `prevariety` and `mem` record that
    the image of the semantics is a prevariety. -/
structure EffectivePrevariety (α : Type u) where
  Rep : Type u
  sem : Rep → Series α
  prevariety : Prevariety α
  mem : ∀ r, sem r ∈ prevariety
  zero : Rep
  add : Rep → Rep → Rep
  smul : ℚ → Rep → Rep
  derivL : α → Rep → Rep
  derivR : α → Rep → Rep
  sem_zero : sem zero = 0
  sem_add : ∀ r s, sem (add r s) = sem r + sem s
  sem_smul : ∀ c r, sem (smul c r) = c • sem r
  sem_derivL : ∀ a r, sem (derivL a r) = leftDeriv α a (sem r)
  sem_derivR : ∀ a r, sem (derivR a r) = rightDeriv α a (sem r)
  decEq : ∀ r s, Decidable (sem r = sem s)

end Lax946791.Prevariety
