import Lax946791.Series
import Mathlib.Data.List.Basic
import Mathlib.Data.Real.Basic

namespace Lax946791Proofs.Series

open Lax946791.Series

/--
---
conclusion: Lax946791.Series.LeftRightDerivativesCommute
---
Both compositions send a series `f` to the series `w ↦ f (a :: w ++ [b])`:
the left derivative reads the coefficient of `a · w`, and the right derivative
appends `b`, so the order in which the two letters are applied is irrelevant.
-/
theorem LeftRightDerivativesCommute (α : Type*) (a b : α) :
    leftDeriv α a ∘ rightDeriv α b = rightDeriv α b ∘ leftDeriv α a := by
  funext f w
  simp [leftDeriv, rightDeriv]

/--
---
conclusion: Lax946791.Series.ReversalInvolution
---
Reversing a word twice gives the word back, so reversing a series twice is the
identity.
-/
theorem ReversalInvolution (α : Type*) (f : Series α) : reversal α (reversal α f) = f := by
  funext w
  simp [reversal, List.reverse_reverse]

/--
---
conclusion: Lax946791.Series.ReversalSwapsDerivatives
---
Reversal interchanges the left and right derivatives: the coefficient of
`a · w` in `f`, read off `reversal f`, is the coefficient of `w · a`, and
`(w ++ [a]).reverse = a :: w.reverse`.
-/
theorem ReversalSwapsDerivatives (α : Type*) (a : α) (f : Series α) :
    reversal α (leftDeriv α a f) = rightDeriv α a (reversal α f) := by
  funext w
  simp [reversal, leftDeriv, rightDeriv, List.reverse_append]

end Lax946791Proofs.Series
