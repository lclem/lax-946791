import Lax946791.Infiltration
import Lax946791.Series
import Lax946791.Prevariety
import Lax946791.Commutativity
import Lax946791.IdealMembership
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.Finset.Fold
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Bool.Basic
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Algebra.Basic
import Mathlib.RingTheory.Ideal.Basic
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Span
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.Tactic

-- `letI` is used to register the `IsNoetherianRing` instance required by
-- `Ideal.fg_of_isNoetherianRing`; the `haveILetI` linter's suggestion to use
-- `let` would drop that instance, so the linter is disabled here.
set_option linter.style.haveILetI false

/-!
---
title: Infiltration automata: closure, equality, and commutativity decidability
type: theorem
---
Proves the five statements of the `Lax946791.Infiltration` concept: the
infiltration-finite series are closed under addition, scalar multiplication, the
infiltration product, and right derivatives (the closure lemma); over a finite
alphabet they are closed under left anti-derivatives; they form an effective
prevariety; the equality (zeroness) problem is decidable for infiltration
automata, reducing to ideal membership in the configuration polynomial ring (the
open leaf) via the ideal-chain argument; and the commutativity problem is
decidable (the meta-theorem applied to the effective prevariety).

The key structural difference from the shuffle case is that an infiltration
transition `Δ_a` extends to an *infiltration* of the configuration space rather
than a derivation.  By the fundamental relationship, an infiltration is `S − id`
for the endomorphism `S = id + Δ`; here `S_a` is the ring homomorphism
substituting `X_i ↦ X_i + Δ_a X_i`, so the letter map is `S_a − id`.  Its product
rule is `Δ_a (p · q) = Δ_a p · q + S_a p · Δ_a q` (the paper's "infiltration
ideals" lemma), which is the synchronising-interleaving analogue of the Leibniz
rule (the extra `S_a p · Δ_a q` term allows the two factors to consume a letter
jointly).  Consequently the word map `Mword` is `ℚ`-linear but not multiplicative,
the stabilised orbit ideal is a bi-ideal by *linearity* (the infiltration product
rule) rather than by `Ideal.map_span`, and the semantics `sem A` is a homomorphism
for the *infiltration* product (not the pointwise product), which is what makes the
infiltration-finite series closed under the infiltration product.
-/

namespace Lax946791Proofs.Infiltration

open Lax946791.Series Lax946791.Prevariety Lax946791.Commutativity Lax946791.Infiltration
open Lax946791.IdealMembership
open MvPolynomial
open Classical

variable {α : Type*}

/-! ### The infiltration product is a commutative ring multiplication -/

/-- The left derivative is `ℚ`-linear: it preserves addition. -/
private theorem leftDeriv_add (a : α) (f g : Series α) :
    leftDeriv α a (f + g) = leftDeriv α a f + leftDeriv α a g := by
  funext w; dsimp [leftDeriv]

/-- The left derivative is `ℚ`-linear: it preserves scalar multiplication. -/
private theorem leftDeriv_smul (a : α) (c : ℚ) (f : Series α) :
    leftDeriv α a (c • f) = c • leftDeriv α a f := by
  funext w; dsimp [leftDeriv]

/-- The left derivative of the zero series is zero. -/
private theorem leftDeriv_zero (a : α) : leftDeriv α a 0 = 0 := by
  funext w; dsimp [leftDeriv]

/-- The left derivative of the infiltration unit is zero: a non-empty word is never the
    empty word, so `leftDeriv a infiltrationUnit = 0`. -/
private theorem infiltrationUnit_leftDeriv (a : α) : leftDeriv α a (infiltrationUnit α) = 0 := by
  funext w
  dsimp [leftDeriv, infiltrationUnit]

/-- The infiltration product rule: `leftDeriv a (f ↑ g) = (leftDeriv a f) ↑ g +
    f ↑ (leftDeriv a g) + (leftDeriv a f) ↑ (leftDeriv a g)`.  This holds by definition:
    the infiltration recursion's step case is exactly this rule (the extra last term
    allows the two series to consume the letter jointly), and the left derivative is the
    map `f ↦ f ∘ (a · -)`. -/
private theorem infiltrationLeibniz (f g : Series α) (a : α) :
    leftDeriv α a (infiltration α f g) =
      infiltration α (leftDeriv α a f) g + infiltration α f (leftDeriv α a g) +
      infiltration α (leftDeriv α a f) (leftDeriv α a g) := by
  funext w
  dsimp [leftDeriv, infiltration]
  simp [infiltrationRec]

/-- The two recursion equations for `infiltrationRec`, as simp lemmas (the `match` is
    defined with `termination_by`, so it does not unfold definitionally; `simp
    [infiltrationRec]` does).  These are used in the ring-axiom proofs below. -/
private theorem infiltrationRec_nil (f g : Series α) : infiltrationRec α f g [] = f [] * g [] := by
  simp [infiltrationRec]
private theorem infiltrationRec_cons (f g : Series α) (a : α) (w : List α) :
    infiltrationRec α f g (a :: w) =
      infiltrationRec α (leftDeriv α a f) g w + infiltrationRec α f (leftDeriv α a g) w +
      infiltrationRec α (leftDeriv α a f) (leftDeriv α a g) w := by
  simp [infiltrationRec]

/-! ### `infiltrationRec` is bilinear -/

/-- `infiltrationRec` is additive in the first argument:
    `infiltrationRec (f + f') g w = infiltrationRec f g w + infiltrationRec f' g w`.
    The induction hypothesis is quantified over all `f f' g` so it applies to the three
    derived pairs in the step case. -/
private theorem infiltrationRec_add_left (f f' g : Series α) (w : List α) :
    infiltrationRec α (f + f') g w = infiltrationRec α f g w + infiltrationRec α f' g w := by
  have : ∀ (f f' g : Series α),
      infiltrationRec α (f + f') g w = infiltrationRec α f g w + infiltrationRec α f' g w := by
    induction w with
    | nil =>
        intro f f' g
        simp [infiltrationRec_nil]
        ring
    | cons a w' ih =>
        intro f f' g
        simp [infiltrationRec_cons]
        rw [leftDeriv_add a f f',
            ih (leftDeriv α a f) (leftDeriv α a f') g,
            ih f f' (leftDeriv α a g),
            ih (leftDeriv α a f) (leftDeriv α a f') (leftDeriv α a g)]
        simp [add_assoc, add_comm, add_left_comm]
  exact this f f' g

/-- `infiltrationRec` is additive in the second argument:
    `infiltrationRec f (g + g') w = infiltrationRec f g w + infiltrationRec f g' w`. -/
private theorem infiltrationRec_add_right (f g g' : Series α) (w : List α) :
    infiltrationRec α f (g + g') w = infiltrationRec α f g w + infiltrationRec α f g' w := by
  have : ∀ (f g g' : Series α),
      infiltrationRec α f (g + g') w = infiltrationRec α f g w + infiltrationRec α f g' w := by
    induction w with
    | nil =>
        intro f g g'
        simp [infiltrationRec_nil]
        ring
    | cons a w' ih =>
        intro f g g'
        simp [infiltrationRec_cons]
        rw [leftDeriv_add a g g',
            ih f (leftDeriv α a g) (leftDeriv α a g'),
            ih (leftDeriv α a f) g g',
            ih (leftDeriv α a f) (leftDeriv α a g) (leftDeriv α a g')]
        simp [add_assoc, add_comm, add_left_comm]
  exact this f g g'

/-- `infiltrationRec` is `ℚ`-linear in the first argument:
    `infiltrationRec (c • f) g w = c • infiltrationRec f g w`. -/
private theorem infiltrationRec_smul_left (c : ℚ) (f g : Series α) (w : List α) :
    infiltrationRec α (c • f) g w = c • infiltrationRec α f g w := by
  have : ∀ (f g : Series α), infiltrationRec α (c • f) g w = c • infiltrationRec α f g w := by
    induction w with
    | nil =>
        intro f g
        simp [infiltrationRec_nil]
        ring
    | cons a w' ih =>
        intro f g
        simp [infiltrationRec_cons, leftDeriv_smul, ih, mul_add, smul_smul]
  exact this f g

/-- `infiltrationRec` is `ℚ`-linear in the second argument:
    `infiltrationRec f (c • g) w = c • infiltrationRec f g w`. -/
private theorem infiltrationRec_smul_right (c : ℚ) (f g : Series α) (w : List α) :
    infiltrationRec α f (c • g) w = c • infiltrationRec α f g w := by
  have : ∀ (f g : Series α), infiltrationRec α f (c • g) w = c • infiltrationRec α f g w := by
    induction w with
    | nil =>
        intro f g
        simp [infiltrationRec_nil]
        ring
    | cons a w' ih =>
        intro f g
        simp [infiltrationRec_cons, leftDeriv_smul, ih, mul_add, smul_smul]
  exact this f g

/-! ### The ring axioms -/

/-- The infiltration product with the zero series is zero. -/
private theorem infiltration_zero_right (f : Series α) : infiltration α f 0 = 0 := by
  funext w
  have : ∀ (f : Series α), infiltrationRec α f 0 w = 0 := by
    induction w with
    | nil =>
        intro f
        simp [infiltrationRec_nil]
    | cons a w' ih =>
        intro f
        simp [infiltrationRec_cons]
        rw [leftDeriv_zero a, ih f, ih (leftDeriv α a f)]
        simp
  exact this f

/-- The infiltration product is commutative: `f ↑ g = g ↑ f`.  Both sides satisfy the same
    recursion (the infiltration product rule and the symmetric initial condition), proved
    by induction on the word. -/
private theorem infiltration_comm (f g : Series α) : infiltration α f g = infiltration α g f := by
  funext w
  have : ∀ (f g : Series α), infiltrationRec α f g w = infiltrationRec α g f w := by
    induction w with
    | nil =>
        intro f g
        simp [infiltrationRec_nil]
        ring
    | cons a w' ih =>
        intro f g
        simp [infiltrationRec_cons]
        rw [ih (leftDeriv α a f) g, ih f (leftDeriv α a g),
            ih (leftDeriv α a f) (leftDeriv α a g)]
        simp [add_comm, add_left_comm]
  exact this f g

/-- The infiltration product with the zero series is zero, in the first argument. -/
private theorem infiltration_zero_left (f : Series α) : infiltration α 0 f = 0 := by
  rw [infiltration_comm, infiltration_zero_right]

/-- Pointwise form of `infiltration_zero_left`: `infiltrationRec α 0 f w = 0`. -/
private theorem infiltrationRec_zero_left (f : Series α) (w : List α) :
    infiltrationRec α 0 f w = 0 := by
  have := infiltration_zero_left f
  simpa [infiltration] using congrArg (fun s => s w) this

/-- The infiltration product is left-distributive over addition:
    `(f + g) ↑ h = f ↑ h + g ↑ h`. -/
private theorem infiltration_add_left (f g h : Series α) :
    infiltration α (f + g) h = infiltration α f h + infiltration α g h := by
  funext w
  have : ∀ (f g h : Series α),
      infiltrationRec α (f + g) h w = infiltrationRec α f h w + infiltrationRec α g h w := by
    induction w with
    | nil =>
        intro f g h
        simp [infiltrationRec_nil]
        ring
    | cons a w' ih =>
        intro f g h
        simp [infiltrationRec_cons]
        rw [leftDeriv_add a f g,
            ih (leftDeriv α a f) (leftDeriv α a g) h,
            ih f g (leftDeriv α a h),
            ih (leftDeriv α a f) (leftDeriv α a g) (leftDeriv α a h)]
        simp [add_assoc, add_comm, add_left_comm]
  exact this f g h

/-- The infiltration product is right-distributive over addition:
    `f ↑ (g + h) = f ↑ g + f ↑ h`. -/
private theorem infiltration_add_right (f g h : Series α) :
    infiltration α f (g + h) = infiltration α f g + infiltration α f h := by
  have := infiltration_add_left g h f
  simpa [infiltration_comm] using this

/-- The infiltration product is associative: `(f ↑ g) ↑ h = f ↑ (g ↑ h)`.  The induction
    step uses the infiltration product rule (three terms), the bilinearity of
    `infiltrationRec` (to distribute the sums), and the induction hypothesis (to match
    the seven resulting terms). -/
private theorem infiltration_assoc (f g h : Series α) :
    infiltration α (infiltration α f g) h = infiltration α f (infiltration α g h) := by
  funext w
  have : ∀ (f g h : Series α),
      infiltrationRec α (infiltrationRec α f g) h w =
      infiltrationRec α f (infiltrationRec α g h) w := by
    induction w with
    | nil =>
        intro f g h
        simp [infiltrationRec_nil]
        ring
    | cons a w' ih =>
        intro f g h
        -- Expand `leftDeriv a (infiltrationRec f g)` and `leftDeriv a (infiltrationRec g h)`
        -- using the infiltration product rule.
        have hLeib_fg : leftDeriv α a (infiltrationRec α f g) =
            infiltrationRec α (leftDeriv α a f) g + infiltrationRec α f (leftDeriv α a g) +
            infiltrationRec α (leftDeriv α a f) (leftDeriv α a g) :=
          infiltrationLeibniz f g a
        have hLeib_gh : leftDeriv α a (infiltrationRec α g h) =
            infiltrationRec α (leftDeriv α a g) h + infiltrationRec α g (leftDeriv α a h) +
            infiltrationRec α (leftDeriv α a g) (leftDeriv α a h) :=
          infiltrationLeibniz g h a
        -- Expand the cons rule and the product rule on both sides (the `hLeib_*` lemmas
        -- make the expansion symmetric; a bare `simp [infiltrationRec_cons]` would expand
        -- only one side).
        simp [infiltrationRec_cons, hLeib_fg, hLeib_gh]
        -- Distribute `infiltrationRec` over the added terms (bilinearity).
        have hdistL1 : infiltrationRec α
            (infiltrationRec α (leftDeriv α a f) g + infiltrationRec α f (leftDeriv α a g) +
              infiltrationRec α (leftDeriv α a f) (leftDeriv α a g)) h w' =
            infiltrationRec α (infiltrationRec α (leftDeriv α a f) g) h w' +
            infiltrationRec α (infiltrationRec α f (leftDeriv α a g)) h w' +
            infiltrationRec α (infiltrationRec α (leftDeriv α a f) (leftDeriv α a g)) h w' := by
          simp [infiltrationRec_add_left]
        have hdistL3 : infiltrationRec α
            (infiltrationRec α (leftDeriv α a f) g + infiltrationRec α f (leftDeriv α a g) +
              infiltrationRec α (leftDeriv α a f) (leftDeriv α a g)) (leftDeriv α a h) w' =
            infiltrationRec α (infiltrationRec α (leftDeriv α a f) g) (leftDeriv α a h) w' +
            infiltrationRec α (infiltrationRec α f (leftDeriv α a g)) (leftDeriv α a h) w' +
            infiltrationRec α (infiltrationRec α (leftDeriv α a f) (leftDeriv α a g))
              (leftDeriv α a h) w' := by
          simp [infiltrationRec_add_left]
        have hdistR1 : infiltrationRec α (leftDeriv α a f)
            (infiltrationRec α (leftDeriv α a g) h + infiltrationRec α g (leftDeriv α a h) +
              infiltrationRec α (leftDeriv α a g) (leftDeriv α a h)) w' =
            infiltrationRec α (leftDeriv α a f) (infiltrationRec α (leftDeriv α a g) h) w' +
            infiltrationRec α (leftDeriv α a f) (infiltrationRec α g (leftDeriv α a h)) w' +
            infiltrationRec α (leftDeriv α a f)
              (infiltrationRec α (leftDeriv α a g) (leftDeriv α a h)) w' := by
          simp [infiltrationRec_add_right]
        have hdistR2 : infiltrationRec α f
            (infiltrationRec α (leftDeriv α a g) h + infiltrationRec α g (leftDeriv α a h) +
              infiltrationRec α (leftDeriv α a g) (leftDeriv α a h)) w' =
            infiltrationRec α f (infiltrationRec α (leftDeriv α a g) h) w' +
            infiltrationRec α f (infiltrationRec α g (leftDeriv α a h)) w' +
            infiltrationRec α f (infiltrationRec α (leftDeriv α a g) (leftDeriv α a h)) w' := by
          simp [infiltrationRec_add_right]
        rw [hdistL1, hdistL3, hdistR1, hdistR2]
        -- Apply the induction hypothesis to match the seven terms.
        rw [ih (leftDeriv α a f) g h, ih f (leftDeriv α a g) h,
            ih (leftDeriv α a f) (leftDeriv α a g) h,
            ih f g (leftDeriv α a h),
            ih (leftDeriv α a f) g (leftDeriv α a h),
            ih f (leftDeriv α a g) (leftDeriv α a h),
            ih (leftDeriv α a f) (leftDeriv α a g) (leftDeriv α a h)]
        simp [add_assoc, add_comm, add_left_comm]
  exact this f g h

/-- The delta series is the left unit of the infiltration product: `infiltrationUnit ↑ f = f`. -/
private theorem infiltration_unit_left (f : Series α) : infiltration α (infiltrationUnit α) f = f := by
  funext w
  have : ∀ (f : Series α), infiltrationRec α (infiltrationUnit α) f w = f w := by
    induction w with
    | nil =>
        intro f
        simp [infiltrationRec_nil, infiltrationUnit]
    | cons a w' ih =>
        intro f
        simp [infiltrationRec_cons]
        rw [infiltrationUnit_leftDeriv a, infiltrationRec_zero_left f w', ih (leftDeriv α a f),
            infiltrationRec_zero_left (leftDeriv α a f) w']
        simp [leftDeriv]
  exact this f

/-- The delta series is the right unit of the infiltration product: `f ↑ infiltrationUnit = f`. -/
private theorem infiltration_unit_right (f : Series α) : infiltration α f (infiltrationUnit α) = f := by
  rw [infiltration_comm]
  exact infiltration_unit_left f

/-- The infiltration product is `ℚ`-bilinear: it preserves scalar multiplication in each
    argument, `(c • f) ↑ g = c • (f ↑ g)`. -/
private theorem infiltration_smul_left (c : ℚ) (f g : Series α) :
    infiltration α (c • f) g = c • infiltration α f g := by
  funext w
  exact infiltrationRec_smul_left c f g w

/-- The infiltration product is `ℚ`-bilinear in the second argument:
    `f ↑ (c • g) = c • (f ↑ g)`. -/
private theorem infiltration_smul_right (c : ℚ) (f g : Series α) :
    infiltration α f (c • g) = c • infiltration α f g := by
  funext w
  exact infiltrationRec_smul_right c f g w

/-! ### The letter map: `infiltrationExt` is `S_map − id` -/

/-- The endomorphism `S_a` of the configuration space: the `ℚ`-algebra homomorphism
    substituting `X_i ↦ X_i + Δ_a X_i` (an `aeval`).  By the fundamental relationship, the
    letter infiltration is `Δ_a = S_a − id`.  It is declared as an algebra homomorphism so
    that the ring-hom lemmas (`map_add`, `map_mul`, …) apply to it directly. -/
noncomputable def S_map (A : InfiltrationAutomaton α) (a : α) :
    MvPolynomial (Fin A.dim) ℚ →ₐ[ℚ] MvPolynomial (Fin A.dim) ℚ :=
  aeval (fun i => MvPolynomial.X i + A.Δ a i)

/-- The letter infiltration `Δ_a`: the map `S_a − id`, an infiltration of the configuration
    space (the paper's infiltration-algebra structure, §7).  It is `ℚ`-linear (the
    difference of two `ℚ`-linear maps) and satisfies the infiltration product rule
    `Δ_a (p · q) = Δ_a p · q + S_a p · Δ_a q`. -/
noncomputable def infiltrationExt (A : InfiltrationAutomaton α) (a : α) :
    MvPolynomial (Fin A.dim) ℚ → MvPolynomial (Fin A.dim) ℚ :=
  fun p => S_map A a p - p

/-- `S_map A a` preserves addition. -/
private theorem S_map_add (A : InfiltrationAutomaton α) (a : α)
    (p q : MvPolynomial (Fin A.dim) ℚ) :
    S_map A a (p + q) = S_map A a p + S_map A a q := by
  rw [map_add (S_map A a) p q]

/-- `S_map A a` preserves scalar multiplication. -/
private theorem S_map_smul (A : InfiltrationAutomaton α) (a : α) (c : ℚ)
    (p : MvPolynomial (Fin A.dim) ℚ) :
    S_map A a (c • p) = c • S_map A a p := by
  rw [map_smul (S_map A a) c p]

/-- `S_map A a` preserves multiplication. -/
private theorem S_map_mul (A : InfiltrationAutomaton α) (a : α)
    (p q : MvPolynomial (Fin A.dim) ℚ) :
    S_map A a (p * q) = S_map A a p * S_map A a q := by
  rw [map_mul (S_map A a) p q]

/-- `S_map A a` sends `1` to `1`. -/
private theorem S_map_one (A : InfiltrationAutomaton α) (a : α) :
    S_map A a 1 = 1 := by
  rw [map_one (S_map A a)]

/-- `S_map A a` sends `0` to `0`. -/
private theorem S_map_zero (A : InfiltrationAutomaton α) (a : α) :
    S_map A a 0 = 0 := by
  rw [map_zero (S_map A a)]

/-- `S_map A a` sends the variable `X i` to `X i + Δ_a X_i`. -/
private theorem S_map_X (A : InfiltrationAutomaton α) (a : α) (i : Fin A.dim) :
    S_map A a (MvPolynomial.X i) = MvPolynomial.X i + A.Δ a i := by
  change MvPolynomial.aeval (fun i => MvPolynomial.X i + A.Δ a i) (MvPolynomial.X i) =
      MvPolynomial.X i + A.Δ a i
  rw [MvPolynomial.aeval_X]

/-- `S_map A a p = p + infiltrationExt A a p`: the endomorphism is the identity plus the
    infiltration (the fundamental relationship `S = id + Δ`). -/
private theorem S_map_eq_add (A : InfiltrationAutomaton α) (a : α)
    (p : MvPolynomial (Fin A.dim) ℚ) :
    S_map A a p = p + infiltrationExt A a p := by
  dsimp [infiltrationExt]
  simp [add_sub_cancel]

/-- `infiltrationExt A a` is `ℚ`-linear: it preserves addition. -/
private theorem infiltrationExt_add (A : InfiltrationAutomaton α) (a : α)
    (p q : MvPolynomial (Fin A.dim) ℚ) :
    infiltrationExt A a (p + q) = infiltrationExt A a p + infiltrationExt A a q := by
  dsimp [infiltrationExt]
  rw [S_map_add]
  ring

/-- `infiltrationExt A a` is `ℚ`-linear: it preserves scalar multiplication. -/
private theorem infiltrationExt_smul (A : InfiltrationAutomaton α) (a : α) (c : ℚ)
    (p : MvPolynomial (Fin A.dim) ℚ) :
    infiltrationExt A a (c • p) = c • infiltrationExt A a p := by
  dsimp [infiltrationExt]
  rw [S_map_smul]
  simp [smul_sub]

/-- `infiltrationExt A a` sends `0` to `0`. -/
private theorem infiltrationExt_zero (A : InfiltrationAutomaton α) (a : α) :
    infiltrationExt A a 0 = 0 := by
  dsimp [infiltrationExt]
  rw [S_map_zero]
  simp

/-- `infiltrationExt A a` sends `1` to `0`: `S_a 1 = 1`, so `Δ_a 1 = 1 − 1 = 0`. -/
private theorem infiltrationExt_one (A : InfiltrationAutomaton α) (a : α) :
    infiltrationExt A a 1 = 0 := by
  dsimp [infiltrationExt]
  rw [S_map_one]
  simp

/-- `infiltrationExt A a` sends the variable `X i` to `Δ_a X_i`: `S_a (X i) = X i + Δ_a X_i`,
    so `Δ_a (X i) = (X i + Δ_a X_i) − X i = Δ_a X_i`. -/
private theorem infiltrationExt_X (A : InfiltrationAutomaton α) (a : α) (i : Fin A.dim) :
    infiltrationExt A a (MvPolynomial.X i) = A.Δ a i := by
  dsimp [infiltrationExt]
  rw [S_map_X]
  simp

/-- The infiltration product rule: `infiltrationExt A a (p * q) =
    infiltrationExt A a p * q + S_map A a p * infiltrationExt A a q` (the paper's
    "infiltration ideals" lemma, point 2).  The LHS is `S_a (p · q) − p · q =
    S_a p · S_a q − p · q` (since `S_a` is a ring hom), and the RHS is
    `(S_a p − p) · q + S_a p · (S_a q − q) = S_a p · S_a q − p · q`. -/
private theorem infiltrationExt_mul (A : InfiltrationAutomaton α) (a : α)
    (p q : MvPolynomial (Fin A.dim) ℚ) :
    infiltrationExt A a (p * q) =
      infiltrationExt A a p * q + S_map A a p * infiltrationExt A a q := by
  dsimp [infiltrationExt]
  rw [S_map_mul]
  ring

/-! ### The word extension: a `ℚ`-linear map built from infiltrations -/

/-- `Mword [] = id`. -/
private theorem Mword_nil (A : InfiltrationAutomaton α) : A.Mword [] = id := by
  rfl

/-- `Mword (a :: w) = Mword w ∘ infiltrationExt (Δ a)`: reading `a` then `w` applies the
    letter infiltration `Δ_a` first, then the word map for `w`. -/
private theorem Mword_cons (A : InfiltrationAutomaton α) (a : α) (w : List α) :
    A.Mword (a :: w) = A.Mword w ∘ infiltrationExt A a := by
  dsimp [InfiltrationAutomaton.Mword]
  funext β
  simp [infiltrationExt, S_map]

/-- `Mword (u ++ v) = Mword v ∘ Mword u` (the letters of `u` are applied after those of
    `v`, right-to-left). -/
private theorem Mword_append (A : InfiltrationAutomaton α) (u v : List α) :
    A.Mword (u ++ v) = A.Mword v ∘ A.Mword u := by
  induction u with
  | nil =>
      funext β
      simp [Mword_nil]
  | cons a u ih =>
      funext β
      simp [Mword_cons, List.cons_append, ih, Function.comp_apply]

/-! ### Semantics properties -/

/-- The word map is `ℚ`-linear: `A.Mword w (p + q) = A.Mword w p + A.Mword w q`.  Each letter
    map `infiltrationExt (Δ a)` is `ℚ`-linear, and a composition of `ℚ`-linear maps is
    `ℚ`-linear.  The induction hypothesis is stated for all `p q` so it can be applied to
    the derived terms. -/
private theorem Mword_add (A : InfiltrationAutomaton α) (w : List α)
    (p q : MvPolynomial (Fin A.dim) ℚ) :
    A.Mword w (p + q) = A.Mword w p + A.Mword w q := by
  have : ∀ (w : List α) (p q : MvPolynomial (Fin A.dim) ℚ),
      A.Mword w (p + q) = A.Mword w p + A.Mword w q := by
    intro w
    induction w with
    | nil =>
        intro p q
        simp [Mword_nil]
    | cons a w' ih =>
        intro p q
        simp [Mword_cons, Function.comp_apply]
        rw [infiltrationExt_add A a, ih (infiltrationExt A a p) (infiltrationExt A a q)]
  exact this w p q

/-- The word map commutes with scalar multiplication: `A.Mword w (c • p) = c • A.Mword w p`. -/
private theorem Mword_smul (A : InfiltrationAutomaton α) (w : List α) (c : ℚ)
    (p : MvPolynomial (Fin A.dim) ℚ) :
    A.Mword w (c • p) = c • A.Mword w p := by
  have : ∀ (w : List α) (c : ℚ) (p : MvPolynomial (Fin A.dim) ℚ),
      A.Mword w (c • p) = c • A.Mword w p := by
    intro w
    induction w with
    | nil =>
        intro c p
        simp [Mword_nil]
    | cons a w' ih =>
        intro c p
        simp [Mword_cons, Function.comp_apply]
        rw [infiltrationExt_smul A a c, ih c (infiltrationExt A a p)]
  exact this w c p

/-- The semantics is `ℚ`-linear: `A.sem (p + q) = A.sem p + A.sem q`.  The word map is
    `ℚ`-linear and `eval` is a ring homomorphism. -/
private theorem sem_add (A : InfiltrationAutomaton α) (p q : MvPolynomial (Fin A.dim) ℚ) :
    A.sem (p + q) = A.sem p + A.sem q := by
  funext w
  dsimp [InfiltrationAutomaton.sem]
  rw [Mword_add A w p q, eval_add]

/-- The semantics commutes with scalar multiplication: `A.sem (c • p) = c • A.sem p`. -/
private theorem sem_smul (A : InfiltrationAutomaton α) (c : ℚ) (p : MvPolynomial (Fin A.dim) ℚ) :
    A.sem (c • p) = c • A.sem p := by
  funext w
  dsimp [InfiltrationAutomaton.sem]
  rw [Mword_smul A w c p]
  simp

/-- The derivation property: `leftDeriv a (A.sem p) = A.sem (infiltrationExt (Δ a) p)`.
    Reading the word `a :: w` applies `Δ_a` first (`Mword_cons`), so the left derivative of
    the semantics at `p` is the semantics at `infiltrationExt (Δ a) p`. -/
private theorem sem_deriv (A : InfiltrationAutomaton α) (a : α) (p : MvPolynomial (Fin A.dim) ℚ) :
    leftDeriv α a (A.sem p) = A.sem (infiltrationExt A a p) := by
  funext w
  dsimp [InfiltrationAutomaton.sem, leftDeriv]
  rw [Mword_cons]
  rfl

/-- The endomorphism property: `A.sem (S_a p) = A.sem p + leftDeriv a (A.sem p)`.  The
    endomorphism `S_a` is the identity plus the infiltration (`S_map_eq_add`), so its
    semantics is the semantics of `p` plus the semantics of `infiltrationExt (Δ a) p`
    (`sem_add`), which is the left derivative of the semantics of `p` (`sem_deriv`). -/
private theorem sem_endomorphism (A : InfiltrationAutomaton α) (a : α)
    (p : MvPolynomial (Fin A.dim) ℚ) :
    A.sem (S_map A a p) = A.sem p + leftDeriv α a (A.sem p) := by
  rw [S_map_eq_add, sem_add, sem_deriv]

/-! ### The semantics is a homomorphism for the infiltration product -/

/-- The key homomorphism property (paper §7, Lemma "Properties of the semantics"):
    `sem A (p * q) = infiltration (sem A p) (sem A q)`.  The ring product of the
    configuration space maps to the *infiltration* product of the series.

    The proof is by induction on the word `w`, with the induction hypothesis quantified
    over all `p q` (so it applies to the derived polynomials).  It does NOT use the
    infiltration-product characterisation (whose product rule would be circular); instead
    it reduces both sides to the word-level recursion, using `Mword_cons`, the infiltration
    product rule for `infiltrationExt`, the endomorphism property `sem_endomorphism`, and
    `sem_deriv`. -/
private theorem sem_infiltration (A : InfiltrationAutomaton α)
    (p q : MvPolynomial (Fin A.dim) ℚ) :
    A.sem (p * q) = infiltration α (A.sem p) (A.sem q) := by
  funext w
  dsimp [InfiltrationAutomaton.sem, infiltration]
  have : ∀ (p q : MvPolynomial (Fin A.dim) ℚ),
      eval (fun i => A.F i) (A.Mword w (p * q)) = infiltrationRec α (A.sem p) (A.sem q) w := by
    induction w with
    | nil =>
        intro p q
        simp [Mword_nil, infiltrationRec_nil, InfiltrationAutomaton.sem, eval_mul]
    | cons a w' ih =>
        intro p q
        have hLHS : eval (fun i => A.F i) (A.Mword (a :: w') (p * q)) =
            eval (fun i => A.F i) (A.Mword w' (infiltrationExt A a p * q)) +
            eval (fun i => A.F i) (A.Mword w' (S_map A a p * infiltrationExt A a q)) := by
          rw [Mword_cons, Function.comp_apply, infiltrationExt_mul, Mword_add, eval_add]
        rw [hLHS]
        have hRHS : infiltrationRec α (A.sem p) (A.sem q) (a :: w') =
            infiltrationRec α (leftDeriv α a (A.sem p)) (A.sem q) w' +
            infiltrationRec α (A.sem p) (leftDeriv α a (A.sem q)) w' +
            infiltrationRec α (leftDeriv α a (A.sem p)) (leftDeriv α a (A.sem q)) w' := by
          simp [infiltrationRec_cons]
        rw [hRHS]
        -- Apply the induction hypothesis to the derived polynomials.
        have hih1 : eval (fun i => A.F i) (A.Mword w' (infiltrationExt A a p * q)) =
            infiltrationRec α (A.sem (infiltrationExt A a p)) (A.sem q) w' :=
          ih (infiltrationExt A a p) q
        have hih2 : eval (fun i => A.F i) (A.Mword w' (S_map A a p * infiltrationExt A a q)) =
            infiltrationRec α (A.sem (S_map A a p)) (A.sem (infiltrationExt A a q)) w' :=
          ih (S_map A a p) (infiltrationExt A a q)
        rw [hih1, hih2]
        -- `sem A (infiltrationExt (Δ a) p) = leftDeriv a (sem A p)` (via `sem_deriv`).
        have hsem1 : A.sem (infiltrationExt A a p) = leftDeriv α a (A.sem p) :=
          sem_deriv A a p
        have hsem2 : A.sem (infiltrationExt A a q) = leftDeriv α a (A.sem q) :=
          sem_deriv A a q
        -- `sem A (S_a p) = sem A p + leftDeriv a (sem A p)` (via `sem_endomorphism`).
        have hsemS : A.sem (S_map A a p) = A.sem p + leftDeriv α a (A.sem p) :=
          sem_endomorphism A a p
        rw [hsem1, hsem2, hsemS]
        -- The LHS second term is `infiltrationRec (sem p + leftDeriv a (sem p)) (leftDeriv a (sem q)) w'`,
        -- which by bilinearity (additivity in the first argument) is the sum of the RHS second and
        -- third terms.
        have hdist : infiltrationRec α (A.sem p + leftDeriv α a (A.sem p))
            (leftDeriv α a (A.sem q)) w' =
            infiltrationRec α (A.sem p) (leftDeriv α a (A.sem q)) w' +
            infiltrationRec α (leftDeriv α a (A.sem p)) (leftDeriv α a (A.sem q)) w' :=
          infiltrationRec_add_left (A.sem p) (leftDeriv α a (A.sem p)) (leftDeriv α a (A.sem q)) w'
        simp [hdist, add_assoc, add_comm, add_left_comm]
  exact this p q

/-! ### The infiltration-algebra evaluation (the semantic working definition) -/

/-- `infiltrationPow α f 0 = infiltrationUnit α`. -/
private theorem infiltrationPow_zero (f : Series α) : infiltrationPow α f 0 = infiltrationUnit α := rfl

/-- `infiltrationPow α f (n+1) = f ↑ infiltrationPow α f n`. -/
private theorem infiltrationPow_succ (f : Series α) (n : ℕ) :
    infiltrationPow α f (n + 1) = infiltration α f (infiltrationPow α f n) := rfl

/-- `infiltrationPow α f (m + n) = infiltrationPow α f m ↑ infiltrationPow α f n`. -/
private theorem infiltrationPow_add (f : Series α) (m n : ℕ) :
    infiltrationPow α f (m + n) = infiltration α (infiltrationPow α f m) (infiltrationPow α f n) := by
  induction m with
  | zero =>
      rw [Nat.zero_add, infiltrationPow_zero, infiltration_unit_left]
  | succ m ih =>
      rw [Nat.succ_add, infiltrationPow_succ, ih, infiltrationPow_succ]
      simp [infiltration_assoc]

/-- `infiltrationPow α f 1 = f`. -/
private theorem infiltrationPow_one (f : Series α) : infiltrationPow α f 1 = f := by
  rw [infiltrationPow_succ, infiltrationPow_zero, infiltration_unit_right]

/-- The infiltration product is a commutative and associative operation on series, hence a
    commutative-associative operation in the sense of `Std`.  These instances let `Finset.fold`
    take the infiltration product of a finite family of series (see `infiltrationProd` below). -/
instance : Std.Commutative (infiltration α) := ⟨infiltration_comm⟩
instance : Std.Associative (infiltration α) := ⟨infiltration_assoc⟩

/-- The concept package's `infiltrationProd` (a typeclass-free right-fold over the index list)
    equals the `Finset.fold` of the infiltration product over all indices: both compute the
    infiltration product of the iterated powers `fs i ↑^[d i]`, and the infiltration product is
    commutative and associative, so the result is independent of the order of the factors. -/
theorem infiltrationProd_eq_fold (k : ℕ) (fs : Fin k → Series α) (d : Fin k →₀ ℕ) :
    infiltrationProd α k fs d =
      (Finset.univ : Finset (Fin k)).fold (infiltration α) (infiltrationUnit α) (fun i => infiltrationPow α (fs i) (d i)) := by
  unfold infiltrationProd
  -- The LHS folds with `fun x acc => infiltration α x acc`, eta-equivalent to `infiltration α`
  -- (the latter is the term carrying the `Std.Commutative`/`Std.Associative` instances, which
  -- `Multiset.coe_fold_r` requires).
  change List.foldr (infiltration α) (infiltrationUnit α) (List.map (fun i => infiltrationPow α (fs i) (d i)) Finset.univ.toList) =
      (Finset.univ : Finset (Fin k)).fold (infiltration α) (infiltrationUnit α) (fun i => infiltrationPow α (fs i) (d i))
  -- Both sides fold the infiltration product over the image of `Finset.univ` under
  -- `i ↦ infiltrationPow (fs i) (d i)`: the LHS is the `List.foldr` over the list representative
  -- (`Multiset.coe_fold_r`), the RHS the `Finset.fold`; the multiset being folded is the same in
  -- both (`Finset.coe_toList`, `Multiset.map_coe`).  The rewrite brings the LHS to a `Multiset.fold`;
  -- unfolding the RHS `Finset.fold` (whose definition is a `Multiset.fold`) makes the two sides
  -- identical, closing the goal.
  rw [← Multiset.coe_fold_r, ← Multiset.map_coe, Finset.coe_toList]
  dsimp only [Finset.fold]

/-- `infiltrationProd α k fs 0 = infiltrationUnit α`. -/
private theorem infiltrationProd_zero (k : ℕ) (fs : Fin k → Series α) :
    infiltrationProd α k fs 0 = infiltrationUnit α := by
  have : ∀ (s : Finset (Fin k)),
      s.fold (infiltration α) (infiltrationUnit α) (fun _ => infiltrationUnit α) = infiltrationUnit α := by
    intro s
    apply Finset.induction_on
      (motive := fun s => s.fold (infiltration α) (infiltrationUnit α) (fun _ => infiltrationUnit α) = infiltrationUnit α)
    · simp [Finset.fold_empty]
    · intro a s h ih
      rw [Finset.fold_insert h, ih]
      simp [infiltration_unit_left]
  rw [infiltrationProd_eq_fold]
  have hLHS : (Finset.univ : Finset (Fin k)).fold (infiltration α) (infiltrationUnit α)
      (fun i => infiltrationPow α (fs i) ((0 : Fin k →₀ ℕ) i)) =
      (Finset.univ : Finset (Fin k)).fold (infiltration α) (infiltrationUnit α) (fun _ => infiltrationUnit α) := by
    apply Finset.fold_congr
    intro i _
    simp [Finsupp.zero_apply, infiltrationPow_zero]
  rw [hLHS]
  exact this Finset.univ

/-- `infiltrationProd α k fs (X i) = fs i`. -/
private theorem infiltrationProd_X (k : ℕ) (fs : Fin k → Series α) (i : Fin k) :
    infiltrationProd α k fs (Finsupp.single i 1) = fs i := by
  have : ∀ (s : Finset (Fin k)),
      s.fold (infiltration α) (infiltrationUnit α) (fun j => infiltrationPow α (fs j) ((Finsupp.single i 1) j)) =
      if i ∈ s then fs i else infiltrationUnit α := by
    intro s
    apply Finset.induction_on
      (motive := fun s => s.fold (infiltration α) (infiltrationUnit α)
        (fun j => infiltrationPow α (fs j) ((Finsupp.single i 1) j)) =
        if i ∈ s then fs i else infiltrationUnit α)
    · simp [Finset.fold_empty]
    · intro a s h ih
      rw [Finset.fold_insert h, ih]
      have hfac : infiltrationPow α (fs a) ((Finsupp.single i 1) a) = if a = i then fs a else infiltrationUnit α := by
        by_cases ha : a = i
        · rw [ha]
          simp [Finsupp.single_apply, infiltrationPow_one]
        · have hne : i ≠ a := by
            intro h; exact ha h.symm
          rw [Finsupp.single_apply]
          simp [ha, hne, infiltrationPow_zero]
      rw [hfac]
      by_cases ha : a = i
      · have hnot : i ∉ s := by
          intro hi
          exact h (by rwa [ha])
        simp [ha, hnot, Finset.mem_insert_self, infiltration_unit_right]
      · have hne : i ≠ a := by
          intro h; exact ha h.symm
        simp [ha, hne, infiltration_unit_left, Finset.mem_insert]
  rw [infiltrationProd_eq_fold]
  simp [this, Finset.mem_univ]

/-- `infiltrationProd α k fs (m + n) = infiltrationProd α k fs m ↑ infiltrationProd α k fs n`. -/
private theorem infiltrationProd_add (k : ℕ) (fs : Fin k → Series α) (m n : Fin k →₀ ℕ) :
    infiltrationProd α k fs (m + n) = infiltration α (infiltrationProd α k fs m) (infiltrationProd α k fs n) := by
  rw [infiltrationProd_eq_fold, infiltrationProd_eq_fold, infiltrationProd_eq_fold]
  have hsplit : ∀ i, infiltrationPow α (fs i) (m i + n i) =
      infiltration α (infiltrationPow α (fs i) (m i)) (infiltrationPow α (fs i) (n i)) := by
    intro i; rw [infiltrationPow_add]
  have hLHS : (Finset.univ : Finset (Fin k)).fold (infiltration α) (infiltrationUnit α)
      (fun i => infiltrationPow α (fs i) ((m + n) i)) =
      (Finset.univ : Finset (Fin k)).fold (infiltration α) (infiltrationUnit α)
        (fun i => infiltration α (infiltrationPow α (fs i) (m i)) (infiltrationPow α (fs i) (n i))) := by
    apply Finset.fold_congr
    intro i _
    rw [Finsupp.add_apply, hsplit i]
  -- The infiltration product of a multiset of factors is independent of the grouping
  -- (infiltration is commutative and associative).
  have hkey : ∀ (A B U V : Series α),
      infiltration α (infiltration α A U) (infiltration α B V) = infiltration α (infiltration α A B) (infiltration α U V) := by
    intro A B U V
    calc
      infiltration α (infiltration α A U) (infiltration α B V)
          = infiltration α A (infiltration α U (infiltration α B V)) := by rw [infiltration_assoc]
        _ = infiltration α A (infiltration α (infiltration α U B) V) := by
            conv =>
              lhs
              arg 3
              rw [← infiltration_assoc]
        _ = infiltration α A (infiltration α (infiltration α B U) V) := by
            conv =>
              lhs
              arg 3
              arg 2
              rw [infiltration_comm]
        _ = infiltration α A (infiltration α B (infiltration α U V)) := by
            conv =>
              lhs
              arg 3
              rw [infiltration_assoc]
        _ = infiltration α (infiltration α A B) (infiltration α U V) := by rw [← infiltration_assoc]
  have hdist : ∀ (s : Finset (Fin k)),
      infiltration α (s.fold (infiltration α) (infiltrationUnit α) (fun i => infiltrationPow α (fs i) (m i)))
        (s.fold (infiltration α) (infiltrationUnit α) (fun i => infiltrationPow α (fs i) (n i))) =
      s.fold (infiltration α) (infiltrationUnit α)
        (fun i => infiltration α (infiltrationPow α (fs i) (m i)) (infiltrationPow α (fs i) (n i))) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        simp [Finset.fold_empty, infiltration_unit_left, infiltration_unit_right]
    | insert a s h ih =>
        rw [Finset.fold_insert h, Finset.fold_insert h, Finset.fold_insert h, ← ih]
        exact hkey _ _ _ _
  rw [hLHS, hdist Finset.univ]

/-! ### `infiltrationEval` is a homomorphism for the infiltration algebra -/

/-- `infiltrationEval α k fs 0 = 0`. -/
private theorem infiltrationEval_zero (k : ℕ) (fs : Fin k → Series α) :
    infiltrationEval α k fs 0 = 0 := by
  simp [infiltrationEval, MvPolynomial.support_zero]

/-- `infiltrationEval α k fs 1 = infiltrationUnit α`. -/
private theorem infiltrationEval_one (k : ℕ) (fs : Fin k → Series α) :
    infiltrationEval α k fs 1 = infiltrationUnit α := by
  simp [infiltrationEval, MvPolynomial.support_one, MvPolynomial.coeff_one, one_smul, infiltrationProd_zero]

/-- `infiltrationEval α k fs (X i) = fs i`. -/
private theorem infiltrationEval_X (k : ℕ) (fs : Fin k → Series α) (i : Fin k) :
    infiltrationEval α k fs (MvPolynomial.X i) = fs i := by
  simp [infiltrationEval, MvPolynomial.support_X, MvPolynomial.coeff_X, one_smul, infiltrationProd_X]

/-- `infiltrationEval` is additive: `infiltrationEval α k fs (p + q) = infiltrationEval α k fs p +
    infiltrationEval α k fs q`. -/
private theorem infiltrationEval_add (k : ℕ) (fs : Fin k → Series α)
    (p q : MvPolynomial (Fin k) ℚ) :
    infiltrationEval α k fs (p + q) = infiltrationEval α k fs p + infiltrationEval α k fs q := by
  rw [infiltrationEval, infiltrationEval, infiltrationEval]
  have hsup : (p + q).support ⊆ p.support ∪ q.support := MvPolynomial.support_add
  have hcoeff : ∀ m, (p + q).coeff m = p.coeff m + q.coeff m := by
    intro m; rw [MvPolynomial.coeff_add]
  have hext1 : (p + q).support.sum (fun m => (p + q).coeff m • infiltrationProd α k fs m) =
      (p.support ∪ q.support).sum (fun m => (p + q).coeff m • infiltrationProd α k fs m) := by
    have h' : ∀ x ∈ p.support ∪ q.support, x ∉ (p + q).support →
        (p + q).coeff x • infiltrationProd α k fs x = 0 := by
      intro x _ hx
      have hcoeff0 : (p + q).coeff x = 0 := by
        simpa using (MvPolynomial.notMem_support_iff (p := p + q) (m := x)).mp hx
      simp [hcoeff0, zero_smul]
    exact Finset.sum_subset hsup h'
  have hext2 : (p.support ∪ q.support).sum (fun m => p.coeff m • infiltrationProd α k fs m) =
      p.support.sum (fun m => p.coeff m • infiltrationProd α k fs m) := by
    have h' : ∀ x ∈ p.support ∪ q.support, x ∉ p.support →
        p.coeff x • infiltrationProd α k fs x = 0 := by
      intro x _ hx
      have hcoeff0 : p.coeff x = 0 := by
        simpa using (MvPolynomial.notMem_support_iff (p := p) (m := x)).mp hx
      simp [hcoeff0, zero_smul]
    exact (Finset.sum_subset Finset.subset_union_left h').symm
  have hext3 : (p.support ∪ q.support).sum (fun m => q.coeff m • infiltrationProd α k fs m) =
      q.support.sum (fun m => q.coeff m • infiltrationProd α k fs m) := by
    have h' : ∀ x ∈ p.support ∪ q.support, x ∉ q.support →
        q.coeff x • infiltrationProd α k fs x = 0 := by
      intro x _ hx
      have hcoeff0 : q.coeff x = 0 := by
        simpa using (MvPolynomial.notMem_support_iff (p := q) (m := x)).mp hx
      simp [hcoeff0, zero_smul]
    exact (Finset.sum_subset Finset.subset_union_right h').symm
  calc
    (p + q).support.sum (fun m => (p + q).coeff m • infiltrationProd α k fs m)
        = (p.support ∪ q.support).sum (fun m => (p + q).coeff m • infiltrationProd α k fs m) := hext1
    _ = (p.support ∪ q.support).sum (fun m => (p.coeff m + q.coeff m) • infiltrationProd α k fs m) := by
      simp [hcoeff]
    _ = (p.support ∪ q.support).sum (fun m => p.coeff m • infiltrationProd α k fs m +
          q.coeff m • infiltrationProd α k fs m) := by
      simp [add_smul]
    _ = (p.support ∪ q.support).sum (fun m => p.coeff m • infiltrationProd α k fs m) +
        (p.support ∪ q.support).sum (fun m => q.coeff m • infiltrationProd α k fs m) := by
      rw [Finset.sum_add_distrib]
    _ = p.support.sum (fun m => p.coeff m • infiltrationProd α k fs m) +
        q.support.sum (fun m => q.coeff m • infiltrationProd α k fs m) := by
      rw [hext2, hext3]

/-- `infiltrationEval` commutes with scalar multiplication. -/
private theorem infiltrationEval_smul (k : ℕ) (fs : Fin k → Series α) (c : ℚ)
    (p : MvPolynomial (Fin k) ℚ) :
    infiltrationEval α k fs (c • p) = c • infiltrationEval α k fs p := by
  rw [infiltrationEval, infiltrationEval]
  have hsup : (c • p).support ⊆ p.support := MvPolynomial.support_smul
  have hcoeff : ∀ m, (c • p).coeff m = c • p.coeff m := by
    intro m; rw [MvPolynomial.coeff_smul]
  have hext : (c • p).support.sum (fun m => (c • p).coeff m • infiltrationProd α k fs m) =
      p.support.sum (fun m => (c • p).coeff m • infiltrationProd α k fs m) := by
    have h' : ∀ x ∈ p.support, x ∉ (c • p).support →
        (c • p).coeff x • infiltrationProd α k fs x = 0 := by
      intro x _ hx
      have hcoeff0 : (c • p).coeff x = 0 := by
        simpa using (MvPolynomial.notMem_support_iff (p := c • p) (m := x)).mp hx
      simp [hcoeff0, zero_smul]
    exact Finset.sum_subset hsup h'
  calc
    (c • p).support.sum (fun m => (c • p).coeff m • infiltrationProd α k fs m)
        = p.support.sum (fun m => (c • p).coeff m • infiltrationProd α k fs m) := hext
    _ = p.support.sum (fun m => c • (p.coeff m • infiltrationProd α k fs m)) := by
      simp [hcoeff, mul_smul]
    _ = c • p.support.sum (fun m => p.coeff m • infiltrationProd α k fs m) := by
      rw [← Finset.smul_sum]

/-- `infiltrationEval` is multiplicative for the infiltration product:
    `infiltrationEval α k fs (p * q) = infiltration α (infiltrationEval α k fs p) (infiltrationEval α k fs q)`. -/
private theorem infiltrationEval_mul (k : ℕ) (fs : Fin k → Series α)
    (p q : MvPolynomial (Fin k) ℚ) :
    infiltrationEval α k fs (p * q) = infiltration α (infiltrationEval α k fs p) (infiltrationEval α k fs q) := by
  have haddL : ∀ (s : Finset (Fin k →₀ ℕ)) (f : (Fin k →₀ ℕ) → Series α) (g : Series α),
      infiltration α (s.sum f) g = s.sum (fun x => infiltration α (f x) g) := by
    intro s f g
    induction s using Finset.induction_on with
    | empty => simp [Finset.sum_empty, infiltration_zero_left]
    | insert a s h ih =>
        rw [Finset.sum_insert h, infiltration_add_left, ih, Finset.sum_insert h]
  have haddR : ∀ (f : Series α) (s : Finset (Fin k →₀ ℕ)) (g : (Fin k →₀ ℕ) → Series α),
      infiltration α f (s.sum g) = s.sum (fun x => infiltration α f (g x)) := by
    intro f s g
    induction s using Finset.induction_on with
    | empty => simp [Finset.sum_empty, infiltration_zero_right]
    | insert a s h ih =>
        rw [Finset.sum_insert h, infiltration_add_right, ih, Finset.sum_insert h]
  have hsum : ∀ (s : Finset ((Fin k →₀ ℕ) × (Fin k →₀ ℕ)))
      (f : ((Fin k →₀ ℕ) × (Fin k →₀ ℕ)) → MvPolynomial (Fin k) ℚ),
      infiltrationEval α k fs (s.sum f) = s.sum (fun x => infiltrationEval α k fs (f x)) := by
    intro s f
    induction s using Finset.induction_on with
    | empty => simp [infiltrationEval, MvPolynomial.support_zero]
    | insert a s h ih =>
        rw [Finset.sum_insert h, infiltrationEval_add, ih, Finset.sum_insert h]
  have hmono : ∀ (m : Fin k →₀ ℕ) (a : ℚ),
      infiltrationEval α k fs (MvPolynomial.monomial m a) = a • infiltrationProd α k fs m := by
    intro m a
    by_cases ha : a = 0
    · simp [ha, MvPolynomial.monomial_zero, infiltrationEval_zero, zero_smul]
    · simp [infiltrationEval, ha, MvPolynomial.support_monomial, MvPolynomial.coeff_monomial,
        Finset.sum_singleton]
  have hRHS : infiltration α (infiltrationEval α k fs p) (infiltrationEval α k fs q) =
      ∑ n ∈ p.support, ∑ o ∈ q.support, (p.coeff n * q.coeff o) • infiltrationProd α k fs (n + o) := by
    rw [infiltrationEval, infiltrationEval]
    calc
      infiltration α (p.support.sum (fun n => p.coeff n • infiltrationProd α k fs n))
          (q.support.sum (fun o => q.coeff o • infiltrationProd α k fs o))
          = ∑ n ∈ p.support, infiltration α (p.coeff n • infiltrationProd α k fs n)
              (q.support.sum (fun o => q.coeff o • infiltrationProd α k fs o)) := by
        rw [haddL (s := p.support) (f := fun n => p.coeff n • infiltrationProd α k fs n)
          (g := q.support.sum (fun o => q.coeff o • infiltrationProd α k fs o))]
      _ = ∑ n ∈ p.support, ∑ o ∈ q.support,
          infiltration α (p.coeff n • infiltrationProd α k fs n) (q.coeff o • infiltrationProd α k fs o) := by
        apply Finset.sum_congr rfl
        intro n _
        exact haddR (f := p.coeff n • infiltrationProd α k fs n) (s := q.support)
          (g := fun o => q.coeff o • infiltrationProd α k fs o)
      _ = ∑ n ∈ p.support, ∑ o ∈ q.support,
          (p.coeff n * q.coeff o) • infiltrationProd α k fs (n + o) := by
        apply Finset.sum_congr rfl
        intro n _
        apply Finset.sum_congr rfl
        intro o _
        rw [infiltration_smul_left, infiltration_smul_right, smul_smul, infiltrationProd_add]
  have hLHS : infiltrationEval α k fs (p * q) =
      ∑ n ∈ p.support, ∑ o ∈ q.support, (p.coeff n * q.coeff o) • infiltrationProd α k fs (n + o) := by
    have hdecomp : p * q = ∑ w ∈ p.support ×ˢ q.support,
        MvPolynomial.monomial (w.1 + w.2) (p.coeff w.1 * q.coeff w.2) := by
      calc
        p * q = (∑ n ∈ p.support, MvPolynomial.monomial n (p.coeff n)) *
            (∑ o ∈ q.support, MvPolynomial.monomial o (q.coeff o)) := by
          conv_lhs =>
            rw [MvPolynomial.as_sum p, MvPolynomial.as_sum q]
        _ = ∑ n ∈ p.support, ∑ o ∈ q.support,
            MvPolynomial.monomial n (p.coeff n) * MvPolynomial.monomial o (q.coeff o) := by
          rw [Finset.sum_mul_sum]
        _ = ∑ n ∈ p.support, ∑ o ∈ q.support,
            MvPolynomial.monomial (n + o) (p.coeff n * q.coeff o) := by
          simp [MvPolynomial.monomial_mul]
        _ = ∑ w ∈ p.support ×ˢ q.support,
            MvPolynomial.monomial (w.1 + w.2) (p.coeff w.1 * q.coeff w.2) := by
          simp [Finset.sum_product]
    calc
      infiltrationEval α k fs (p * q)
          = infiltrationEval α k fs (∑ w ∈ p.support ×ˢ q.support,
              MvPolynomial.monomial (w.1 + w.2) (p.coeff w.1 * q.coeff w.2)) := by rw [hdecomp]
        _ = ∑ w ∈ p.support ×ˢ q.support,
            infiltrationEval α k fs (MvPolynomial.monomial (w.1 + w.2) (p.coeff w.1 * q.coeff w.2)) := by
          rw [hsum (s := p.support ×ˢ q.support)
            (f := fun (w : (Fin k →₀ ℕ) × (Fin k →₀ ℕ)) =>
              MvPolynomial.monomial (w.1 + w.2) (p.coeff w.1 * q.coeff w.2))]
        _ = ∑ w ∈ p.support ×ˢ q.support,
            (p.coeff w.1 * q.coeff w.2) • infiltrationProd α k fs (w.1 + w.2) := by
          simp [hmono]
        _ = ∑ n ∈ p.support, ∑ o ∈ q.support,
            (p.coeff n * q.coeff o) • infiltrationProd α k fs (n + o) := by
          simp [Finset.sum_product]
  rw [hLHS, hRHS]

/-! ### The coincidence: infiltration-finite ↔ infiltration-recognisable -/

/-! The semantics agrees with the infiltration-algebra evaluation: `A.sem p =
    infiltrationEval α A.dim (fun i => A.sem (X i)) p` for all `p`.  Both sides are
    infiltration-algebra homomorphisms sending `X_i` to `A.sem (X_i)`, so they coincide. -/

/-- The semantics of the zero configuration is the zero series: `A.sem 0 = 0`. -/
private theorem sem_zero (A : InfiltrationAutomaton α) : A.sem 0 = 0 := by
  funext w
  dsimp [InfiltrationAutomaton.sem]
  have : A.Mword w 0 = 0 := by
    simpa using Mword_smul A w 0 0
  rw [this]
  simp

/-- The word map sends `1` to `1` at the empty word and `0` otherwise: an infiltration kills
    `1`, so a non-empty word sends `1` to `0`. -/
private theorem Mword_one (A : InfiltrationAutomaton α) (w : List α) :
    A.Mword w 1 = if w = [] then 1 else 0 := by
  induction w with
  | nil => simp [Mword_nil]
  | cons a w' ih =>
      rw [Mword_cons, Function.comp_apply, infiltrationExt_one]
      have : A.Mword w' 0 = 0 := by
        simpa using Mword_smul A w' 0 0
      rw [this]
      simp

/-- The semantics of the constant `1` configuration is the infiltration unit: `A.sem 1 =
    infiltrationUnit α`. -/
private theorem sem_one (A : InfiltrationAutomaton α) : A.sem 1 = infiltrationUnit α := by
  funext w
  dsimp [InfiltrationAutomaton.sem, infiltrationUnit]
  rw [Mword_one]
  split_ifs with h
  · simp
  · simp

/-- The semantics of a variable power is the iterated infiltration power of the generator:
    `A.sem (X i ^ n) = infiltrationPow α (A.sem (X i)) n` (by the infiltration-hom property
    `sem_infiltration` and induction on `n`). -/
private theorem sem_pow (A : InfiltrationAutomaton α) (i : Fin A.dim) (n : ℕ) :
    A.sem ((MvPolynomial.X i) ^ n) = infiltrationPow α (A.sem (MvPolynomial.X i)) n := by
  induction n with
  | zero =>
      rw [pow_zero, sem_one, infiltrationPow_zero]
  | succ n ih =>
      rw [pow_succ, sem_infiltration, ih, infiltrationPow_succ, infiltration_comm]

/-- The infiltration product of a finite product of variable powers is the infiltration fold of
    the iterated powers: `A.sem (∏_{i ∈ s} X_i ^ (m i)) = s.fold (↑) (infiltrationUnit)
    (fun i => infiltrationPow α (A.sem (X i)) (m i))`, by induction on `s` using
    `sem_infiltration` and `sem_pow`. -/
private theorem sem_prod (A : InfiltrationAutomaton α) (m : Fin A.dim →₀ ℕ) (s : Finset (Fin A.dim)) :
    A.sem (s.prod (fun i => (MvPolynomial.X i) ^ m i)) =
      s.fold (infiltration α) (infiltrationUnit α) (fun i => infiltrationPow α (A.sem (MvPolynomial.X i)) (m i)) := by
  induction s using Finset.induction_on with
  | empty =>
      rw [Finset.prod_empty, sem_one]
      simp [Finset.fold_empty, infiltrationUnit]
  | insert a s h ih =>
      rw [Finset.prod_insert h, sem_infiltration, ih, Finset.fold_insert h, sem_pow A a (m a)]

/-- `infiltrationProd` is unchanged when the fold is taken over the support of the exponent
    `m` rather than over all indices: the zero-exponent terms contribute the infiltration unit
    (the identity), so `infiltrationProd α k fs m = (m.support).fold (↑) (infiltrationUnit)
    (fun i => infiltrationPow α (fs i) (m i))`. -/
private theorem infiltrationProd_support (k : ℕ) (fs : Fin k → Series α) (m : Fin k →₀ ℕ) :
    infiltrationProd α k fs m =
      (m.support).fold (infiltration α) (infiltrationUnit α) (fun i => infiltrationPow α (fs i) (m i)) := by
  rw [infiltrationProd_eq_fold]
  have hfold : ∀ (s : Finset (Fin k)),
      s.fold (infiltration α) (infiltrationUnit α) (fun i => infiltrationPow α (fs i) (m i)) =
        (m.support ∩ s).fold (infiltration α) (infiltrationUnit α) (fun i => infiltrationPow α (fs i) (m i)) := by
    intro s
    apply Finset.induction_on
      (motive := fun s => s.fold (infiltration α) (infiltrationUnit α) (fun i => infiltrationPow α (fs i) (m i)) =
        (m.support ∩ s).fold (infiltration α) (infiltrationUnit α) (fun i => infiltrationPow α (fs i) (m i)))
    · simp [Finset.fold_empty, Finset.inter_empty]
    · intro a s h ih
      rw [Finset.fold_insert h, ih]
      by_cases ha : a ∈ m.support
      · have hnot : a ∉ m.support ∩ s := by
          intro h'
          exact h (Finset.mem_inter.mp h' |>.2)
        rw [Finset.inter_insert_of_mem ha, Finset.fold_insert hnot]
      · have hne : ¬(m a ≠ 0) := by
          intro h
          exact ha (Finsupp.mem_support_iff.mpr h)
        have hm0 : m a = 0 := by simpa using hne
        rw [Finset.inter_insert_of_notMem ha, hm0, infiltrationPow_zero]
        simp [infiltration_unit_left]
  rw [hfold Finset.univ]
  simp [Finset.inter_univ]

/-- The semantics of a monomial is the infiltration product of the iterated powers of the
    generators: `A.sem (monomial m 1) = infiltrationProd α A.dim (fun i => A.sem (X i)) m`. -/
private theorem sem_monomial (A : InfiltrationAutomaton α) (m : Fin A.dim →₀ ℕ) :
    A.sem (MvPolynomial.monomial m 1) =
      infiltrationProd α A.dim (fun i => A.sem (MvPolynomial.X i)) m := by
  have hmono : MvPolynomial.monomial m (1 : ℚ) = (m.support).prod (fun i => (MvPolynomial.X i) ^ m i) := by
    rw [MvPolynomial.prod_X_pow_eq_monomial]
  have hstep : A.sem (MvPolynomial.monomial m 1) =
      A.sem ((m.support).prod (fun i => (MvPolynomial.X i) ^ m i)) :=
    congrArg (fun x => A.sem x) hmono
  rw [hstep, sem_prod A m m.support]
  exact (infiltrationProd_support A.dim (fun i => A.sem (MvPolynomial.X i)) m).symm

/-- `infiltrationEval` of a monomial is the scalar times the infiltration product:
    `infiltrationEval α k fs (monomial m c) = c • infiltrationProd α k fs m`. -/
private theorem infiltrationEval_monomial (k : ℕ) (fs : Fin k → Series α) (m : Fin k →₀ ℕ) (c : ℚ) :
    infiltrationEval α k fs (MvPolynomial.monomial m c) = c • infiltrationProd α k fs m := by
  by_cases hc : c = 0
  · simp [hc, MvPolynomial.monomial_zero, infiltrationEval_zero, zero_smul]
  · rw [infiltrationEval]
    have hsup : (MvPolynomial.monomial m c).support = {m} := by
      rw [MvPolynomial.support_monomial]
      simp [hc]
    rw [hsup, Finset.sum_singleton]
    have hcoeff : (MvPolynomial.monomial m c).coeff m = c := by
      rw [MvPolynomial.coeff_monomial]
      simp [hc]
    rw [hcoeff]

/-- The semantics agrees with the infiltration-algebra evaluation: `A.sem p =
    infiltrationEval α A.dim (fun i => A.sem (X i)) p`.  Both sides are infiltration-algebra
    homomorphisms sending `X_i` to `A.sem (X_i)`; they agree on monomials (`sem_monomial`
    and `infiltrationEval_monomial`) and are `ℚ`-linear, so they agree on the sum of monomials
    that is `p`. -/
private theorem sem_eq_infiltrationEval (A : InfiltrationAutomaton α) (p : MvPolynomial (Fin A.dim) ℚ) :
    A.sem p = infiltrationEval α A.dim (fun i => A.sem (MvPolynomial.X i)) p := by
  let fs := fun i => A.sem (MvPolynomial.X i)
  have hsum : ∀ (s : Finset (Fin A.dim →₀ ℕ)) (f : (Fin A.dim →₀ ℕ) → MvPolynomial (Fin A.dim) ℚ),
      A.sem (s.sum f) = s.sum (fun x => A.sem (f x)) := by
    intro s f
    induction s using Finset.induction_on with
    | empty => simp [Finset.sum_empty, sem_zero]
    | insert a s h ih =>
        rw [Finset.sum_insert h, sem_add, ih, Finset.sum_insert h]
  have hdecomp : p = ∑ v ∈ p.support, p.coeff v • MvPolynomial.monomial v 1 := by
    simp [MvPolynomial.smul_monomial]
  calc
    A.sem p = A.sem (∑ v ∈ p.support, p.coeff v • MvPolynomial.monomial v 1) := by conv_lhs => rw [hdecomp]
    _ = ∑ v ∈ p.support, A.sem (p.coeff v • MvPolynomial.monomial v 1) := by
      rw [hsum (s := p.support) (f := fun v => p.coeff v • MvPolynomial.monomial v 1)]
    _ = ∑ v ∈ p.support, p.coeff v • A.sem (MvPolynomial.monomial v 1) := by
      apply Finset.sum_congr rfl
      intro v _
      rw [sem_smul]
    _ = ∑ v ∈ p.support, p.coeff v • infiltrationProd α A.dim fs v := by
      apply Finset.sum_congr rfl
      intro v _
      rw [sem_monomial]
    _ = infiltrationEval α A.dim fs p := by
      dsimp [infiltrationEval]

/-! ### Extending the witnessing tuple -/

/-- The witnessing tuple extended by `f` at index `0`: `extTuple f k fs 0 = f` and
    `extTuple f k fs (Fin.succ i) = fs i`.  This lets an infiltration polynomial in `fs` be
    viewed as an infiltration polynomial in the extended tuple, with `f` as a generator. -/
noncomputable def extTuple (f : Series α) (k : ℕ) (fs : Fin k → Series α) : Fin (k+1) → Series α :=
  fun j => if h : j = 0 then f else fs ⟨j.val - 1, by
    have hlt : j.val < k + 1 := j.isLt
    have hne : j.val ≠ 0 := by
      intro hj
      exact h (Fin.ext hj)
    omega⟩

private theorem extTuple_zero (f : Series α) (k : ℕ) (fs : Fin k → Series α) :
    extTuple f k fs 0 = f := by
  simp [extTuple]

private theorem extTuple_succ (f : Series α) (k : ℕ) (fs : Fin k → Series α) (i : Fin k) :
    extTuple f k fs (Fin.succ i) = fs i := by
  simp [extTuple]

/-- The embedding of a polynomial in `Fin k` into `Fin (k+1)`, shifting each variable
    `X_i` to `X_{i+1}` (leaving `X_0` unused): `embedPoly k p = aeval (X ∘ Fin.succ) p`. -/
noncomputable def embedPoly (k : ℕ) (p : MvPolynomial (Fin k) ℚ) : MvPolynomial (Fin (k+1)) ℚ :=
  aeval (fun i => MvPolynomial.X (Fin.succ i)) p

/-! ### Two infiltration-algebra homomorphisms agreeing on the generators are equal -/

/-- Two `ℚ`-algebra homomorphisms (for the *infiltration* product) `h1 h2 :
    MvPolynomial (Fin k) ℚ → Series α` that agree on the unit `1` and on the generators
    `X i` are equal.  The polynomial ring is generated (as a ring) by `1` and the `X i`,
    and an infiltration-algebra hom is determined by those values: it commutes with the powers
    `X i ^ n` (induction on `n`, using multiplicativity), with the monomials
    `monomial m 1` (induction on the support, peeling off one generator at a time), and
    with all polynomials (additivity + scalar-linearity + the monomial case). -/
private theorem infiltrationHom_ext (k : ℕ)
    (h1 h2 : MvPolynomial (Fin k) ℚ → Series α)
    (hadd1 : ∀ p q, h1 (p + q) = h1 p + h1 q)
    (hadd2 : ∀ p q, h2 (p + q) = h2 p + h2 q)
    (hsmul1 : ∀ (c : ℚ) p, h1 (c • p) = c • h1 p)
    (hsmul2 : ∀ (c : ℚ) p, h2 (c • p) = c • h2 p)
    (hmul1 : ∀ p q, h1 (p * q) = infiltration α (h1 p) (h1 q))
    (hmul2 : ∀ p q, h2 (p * q) = infiltration α (h2 p) (h2 q))
    (hone : h1 1 = h2 1)
    (hgen : ∀ i, h1 (MvPolynomial.X i) = h2 (MvPolynomial.X i)) :
    ∀ p, h1 p = h2 p := by
  have hpow : ∀ (i : Fin k) (n : ℕ), h1 ((MvPolynomial.X i) ^ n) = h2 ((MvPolynomial.X i) ^ n) := by
    intro i n
    induction n with
    | zero =>
        rw [pow_zero, hone]
    | succ n ih =>
        rw [pow_succ, hmul1, ih, hmul2, hgen i]
  have hmono : ∀ (m : Fin k →₀ ℕ),
      h1 (MvPolynomial.monomial m (1 : ℚ)) = h2 (MvPolynomial.monomial m (1 : ℚ)) := by
    have : ∀ (s : Finset (Fin k)) (m : Fin k →₀ ℕ), m.support ⊆ s →
        h1 (MvPolynomial.monomial m (1 : ℚ)) = h2 (MvPolynomial.monomial m (1 : ℚ)) := by
      intro s
      induction s using Finset.induction_on with
      | empty =>
          intro m hm
          have hm0 : m = 0 := by
            rw [Finsupp.ext_iff]
            intro j
            by_contra hj
            have : j ∈ m.support := Finsupp.mem_support_iff.mpr hj
            exact Finset.notMem_empty j (Finset.mem_of_subset hm this)
          rw [hm0, ← MvPolynomial.one_def, hone]
      | insert i s h ih =>
          intro m hm
          by_cases him : i ∈ m.support
          · have hmi : m i ≠ 0 := Finsupp.mem_support_iff.mp him
            have hsplit : MvPolynomial.monomial m (1 : ℚ) =
                (MvPolynomial.X i) ^ m i * MvPolynomial.monomial (m - Finsupp.single i (m i)) (1 : ℚ) := by
              have hx : (MvPolynomial.X i) ^ m i =
                  MvPolynomial.monomial (Finsupp.single i (m i)) (1 : ℚ) :=
                MvPolynomial.X_pow_eq_monomial
              rw [hx, MvPolynomial.monomial_mul]
              have hsum : Finsupp.single i (m i) + (m - Finsupp.single i (m i)) = m := by
                rw [Finsupp.ext_iff]
                intro j
                by_cases hj : j = i
                · subst hj
                  simp [Finsupp.tsub_apply, Finsupp.single_apply]
                · simp [hj, Finsupp.single_apply, Finsupp.tsub_apply]
              simp [hsum]
            have hsub : (m - Finsupp.single i (m i)).support ⊆ s := by
              intro j hjj
              have hjne : j ≠ i := by
                intro hj
                have : (m - Finsupp.single i (m i)) j = 0 := by
                  subst hj
                  simp [Finsupp.tsub_apply, Finsupp.single_apply]
                exact (Finsupp.mem_support_iff.mp hjj) this
              have hjm : j ∈ m.support := by
                rw [Finsupp.mem_support_iff]
                have hsubj : (m - Finsupp.single i (m i)) j = m j := by
                  rw [Finsupp.tsub_apply]
                  simp [hjne, Finsupp.single_apply]
                rw [← hsubj]
                exact Finsupp.mem_support_iff.mp hjj
              have hjin : j ∈ insert i s := Finset.mem_of_subset hm hjm
              have hjin' : j ∈ s := by
                rw [Finset.mem_insert] at hjin
                exact hjin.resolve_left hjne
              exact hjin'
            rw [hsplit, hmul1, hmul2, hpow i (m i), ih _ hsub]
          · have hsup : m.support ⊆ s := by
              intro j hjj
              have hjne : j ≠ i := by
                intro hj
                have : j ∉ m.support := by
                  subst hj
                  simpa [Finsupp.mem_support_iff] using him
                exact this hjj
              have hjin : j ∈ insert i s := Finset.mem_of_subset hm hjj
              have hjin' : j ∈ s := by
                rw [Finset.mem_insert] at hjin
                exact hjin.resolve_left hjne
              exact hjin'
            exact ih m hsup
    intro m
    exact this Finset.univ m (Finset.subset_univ m.support)
  intro p
  have hsum : ∀ (s : Finset (Fin k →₀ ℕ)) (f : (Fin k →₀ ℕ) → MvPolynomial (Fin k) ℚ),
      h1 (s.sum f) = s.sum (fun x => h1 (f x)) := by
    intro s f
    induction s using Finset.induction_on with
    | empty => simp [Finset.sum_empty, show h1 0 = 0 from by simpa using hsmul1 0 0]
    | insert a s h ih =>
        rw [Finset.sum_insert h, hadd1, ih, Finset.sum_insert h]
  have hsum2 : ∀ (s : Finset (Fin k →₀ ℕ)) (f : (Fin k →₀ ℕ) → MvPolynomial (Fin k) ℚ),
      h2 (s.sum f) = s.sum (fun x => h2 (f x)) := by
    intro s f
    induction s using Finset.induction_on with
    | empty => simp [Finset.sum_empty, show h2 0 = 0 from by simpa using hsmul2 0 0]
    | insert a s h ih =>
        rw [Finset.sum_insert h, hadd2, ih, Finset.sum_insert h]
  have hdecomp : p = ∑ v ∈ p.support, p.coeff v • MvPolynomial.monomial v (1 : ℚ) := by
    simp [MvPolynomial.smul_monomial]
  calc
    h1 p = h1 (∑ v ∈ p.support, p.coeff v • MvPolynomial.monomial v (1 : ℚ)) := by
      conv_lhs => rw [hdecomp]
    _ = ∑ v ∈ p.support, h1 (p.coeff v • MvPolynomial.monomial v (1 : ℚ)) := by
      rw [hsum (s := p.support) (f := fun v => p.coeff v • MvPolynomial.monomial v (1 : ℚ))]
    _ = ∑ v ∈ p.support, p.coeff v • h1 (MvPolynomial.monomial v (1 : ℚ)) := by
      apply Finset.sum_congr rfl
      intro v _
      rw [hsmul1]
    _ = ∑ v ∈ p.support, p.coeff v • h2 (MvPolynomial.monomial v (1 : ℚ)) := by
      apply Finset.sum_congr rfl
      intro v _
      rw [hmono v]
    _ = ∑ v ∈ p.support, h2 (p.coeff v • MvPolynomial.monomial v (1 : ℚ)) := by
      apply Finset.sum_congr rfl
      intro v _
      rw [hsmul2]
    _ = h2 (∑ v ∈ p.support, p.coeff v • MvPolynomial.monomial v (1 : ℚ)) := by
      rw [hsum2 (s := p.support) (f := fun v => p.coeff v • MvPolynomial.monomial v (1 : ℚ))]
    _ = h2 p := by
      conv_rhs => rw [hdecomp]

/-- An infiltration polynomial in `fs` is the same series as the embedded infiltration polynomial
    in the extended tuple: `infiltrationEval α k fs r = infiltrationEval α (k+1) (extTuple f k fs)
    (embedPoly k r)`.  Both sides are infiltration-algebra homomorphisms sending `X_i` to
    `fs i` (the `X_0` slot of the extended tuple is unused by the embedded polynomial, so
    the value of `f` there is irrelevant), so they coincide by `infiltrationHom_ext`. -/
private theorem infiltrationEval_embed (f : Series α) (k : ℕ) (fs : Fin k → Series α)
    (r : MvPolynomial (Fin k) ℚ) :
    infiltrationEval α k fs r = infiltrationEval α (k+1) (extTuple f k fs) (embedPoly k r) := by
  let g := extTuple f k fs
  let aev : MvPolynomial (Fin k) ℚ →ₐ[ℚ] MvPolynomial (Fin (k+1)) ℚ :=
    MvPolynomial.aeval (fun i => MvPolynomial.X (Fin.succ i))
  have hadd2 : ∀ p q, infiltrationEval α (k+1) g (embedPoly k (p + q)) =
      infiltrationEval α (k+1) g (embedPoly k p) + infiltrationEval α (k+1) g (embedPoly k q) := by
    intro p q
    rw [embedPoly, embedPoly, embedPoly]
    rw [map_add aev p q, infiltrationEval_add]
  have hsmul2 : ∀ (c : ℚ) p, infiltrationEval α (k+1) g (embedPoly k (c • p)) =
      c • infiltrationEval α (k+1) g (embedPoly k p) := by
    intro c p
    rw [embedPoly, embedPoly]
    rw [map_smul aev c p, infiltrationEval_smul]
  have hmul2 : ∀ p q, infiltrationEval α (k+1) g (embedPoly k (p * q)) =
      infiltration α (infiltrationEval α (k+1) g (embedPoly k p)) (infiltrationEval α (k+1) g (embedPoly k q)) := by
    intro p q
    rw [embedPoly, embedPoly, embedPoly]
    rw [map_mul aev p q, infiltrationEval_mul]
  have hone : infiltrationEval α k fs 1 = infiltrationEval α (k+1) g (embedPoly k 1) := by
    rw [embedPoly]
    rw [map_one aev, infiltrationEval_one, infiltrationEval_one]
  have hgen : ∀ i, infiltrationEval α k fs (MvPolynomial.X i) =
      infiltrationEval α (k+1) g (embedPoly k (MvPolynomial.X i)) := by
    intro i
    rw [infiltrationEval_X, embedPoly, MvPolynomial.aeval_X, infiltrationEval_X]
    dsimp [g]
    rw [extTuple_succ]
  exact infiltrationHom_ext k
    (fun p => infiltrationEval α k fs p)
    (fun p => infiltrationEval α (k+1) g (embedPoly k p))
    (infiltrationEval_add k fs) hadd2
    (infiltrationEval_smul k fs) hsmul2
    (infiltrationEval_mul k fs) hmul2
    hone hgen r

/-! ### The left derivative commutes with the infiltration evaluation -/

/-- Infiltration is ℚ-bilinear, so it commutes with negation on the right:
    `infiltration α f (-g) = -infiltration α f g`.  Since `-g = -1 • g`, this is the
    case `c = -1` of the pointwise `ℚ`-linearity `infiltrationRec α f (c • g) w = c • infiltrationRec α f g w`. -/
@[simp] private theorem infiltration_neg_right (f g : Series α) :
    infiltration α f (-g) = -infiltration α f g := by
  funext w
  simp [infiltration]
  simpa using infiltrationRec_smul_right (-1 : ℚ) f g w

/-- Infiltration is ℚ-bilinear, so it commutes with negation on the left:
    `infiltration α (-f) g = -infiltration α f g`.  Symmetric to the right version
    (`-f = -1 • f`, the case `c = -1` of `infiltrationRec α (c • f) g w = c • infiltrationRec α f g w`). -/
@[simp] private theorem infiltration_neg_left (f g : Series α) :
    infiltration α (-f) g = -infiltration α f g := by
  funext w
  simp [infiltration]
  simpa using infiltrationRec_smul_left (-1 : ℚ) f g w

/-- The left derivative of an iterated infiltration power, in terms of the *extended*
    generator: if `leftDeriv a (fs i) = infiltrationEval α k fs (q i)`, then
    `leftDeriv a (infiltrationPow α (fs i) n) =
    infiltrationPow α (fs i + infiltrationEval α k fs (q i)) n − infiltrationPow α (fs i) n`.
    The extended generator is `fs i + leftDeriv a (fs i)`; the left derivative (an infiltration,
    3-term rule) of `f ↑^[n]` is the difference of the extended and ordinary iterated powers. -/
private theorem leftDeriv_infiltrationPow (k : ℕ) (fs : Fin k → Series α) (a : α)
    (q : Fin k → MvPolynomial (Fin k) ℚ)
    (hq : ∀ i, leftDeriv α a (fs i) = infiltrationEval α k fs (q i))
    (i : Fin k) (n : ℕ) :
    leftDeriv α a (infiltrationPow α (fs i) n) =
      infiltrationPow α (fs i + infiltrationEval α k fs (q i)) n - infiltrationPow α (fs i) n := by
  induction n with
  | zero =>
      simp [infiltrationPow_zero, infiltrationUnit_leftDeriv a, sub_self]
  | succ n ih =>
      let f := fs i
      let e := infiltrationEval α k fs (q i)
      have hL : leftDeriv α a (infiltration α f (infiltrationPow α f n)) =
          infiltration α (leftDeriv α a f) (infiltrationPow α f n) +
          infiltration α f (leftDeriv α a (infiltrationPow α f n)) +
          infiltration α (leftDeriv α a f) (leftDeriv α a (infiltrationPow α f n)) :=
        infiltrationLeibniz f (infiltrationPow α f n) a
      rw [infiltrationPow_succ, hL, ih, hq i, infiltrationPow_succ]
      -- LHS: `e ↑ P_n + f ↑ (Q_n - P_n) + e ↑ (Q_n - P_n)` where `P_n = f ↑^[n]`, `Q_n = (f+e) ↑^[n]`.
      -- The `e ↑ P_n` terms cancel, leaving `f ↑ Q_n + e ↑ Q_n - f ↑ P_n = (f + e) ↑ Q_n - f ↑ P_n`.
      have hPn : infiltrationPow α f n = infiltrationPow α f n := rfl
      have hQn : infiltrationPow α (f + e) n = infiltrationPow α (f + e) n := rfl
      simp [infiltration_add_left, infiltration_add_right, infiltration_smul_left,
          infiltration_smul_right, neg_smul, sub_eq_add_neg, add_sub, sub_add,
          add_assoc, add_comm, add_left_comm]
      ring

/-- Folding the infiltration with a constant unit integrand yields the unit: each step
    `infiltration α acc (infiltrationUnit α) = acc` (by `infiltration_unit_right`). -/
private theorem fold_infiltration_unit_const (k : ℕ) (s : Finset (Fin k)) :
    s.fold (infiltration α) (infiltrationUnit α) (fun _ => infiltrationUnit α) = infiltrationUnit α := by
  induction s using Finset.induction_on with
  | empty => simp [Finset.fold_empty]
  | insert x s hx ih =>
      rw [Finset.fold_insert hx, ih]
      simp [infiltration_unit_left]

/-- `infiltrationProd α k fs (Finsupp.single i n) = infiltrationPow α (fs i) n`: the only
    non-unit factor of the product is the `i`-th one (all other exponents are zero). -/
private theorem infiltrationProd_single (k : ℕ) (fs : Fin k → Series α) (i : Fin k) (n : ℕ) :
    infiltrationProd α k fs (Finsupp.single i n) = infiltrationPow α (fs i) n := by
  rw [infiltrationProd_eq_fold]
  have hsplit : (Finset.univ : Finset (Fin k)) = insert i ((Finset.univ : Finset (Fin k)) \ {i}) := by
    ext j
    simp [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert]
  rw [hsplit, Finset.fold_insert (by simp [Finset.mem_sdiff])]
  have hrest : ((Finset.univ : Finset (Fin k)) \ {i}).fold (infiltration α) (infiltrationUnit α)
      (fun j => infiltrationPow α (fs j) ((Finsupp.single i n) j)) = infiltrationUnit α := by
    have hconst : ∀ j ∈ (Finset.univ : Finset (Fin k)) \ {i},
        infiltrationPow α (fs j) ((Finsupp.single i n) j) = infiltrationUnit α := by
      intro j hj
      have hjne : j ≠ i := by
        intro heq
        have : j ∈ ({i} : Finset (Fin k)) := Finset.mem_singleton.mpr heq
        exact (Finset.mem_sdiff.mp hj).2 this
      rw [show (Finsupp.single i n) j = 0 by simp [Finsupp.single_apply, hjne], infiltrationPow_zero]
    have h1 : ((Finset.univ : Finset (Fin k)) \ {i}).fold (infiltration α) (infiltrationUnit α)
        (fun j => infiltrationPow α (fs j) ((Finsupp.single i n) j)) =
        ((Finset.univ : Finset (Fin k)) \ {i}).fold (infiltration α) (infiltrationUnit α)
          (fun _ => infiltrationUnit α) := by
      apply Finset.fold_congr
      intro j hj
      exact hconst j hj
    rw [h1, fold_infiltration_unit_const k (Finset.univ \ {i})]
  rw [hrest]
  simp [infiltration_unit_right]

/-- The left derivative of an infiltration product (monomial case): if
    `leftDeriv a (fs i) = infiltrationEval α k fs (q i)` for all `i`, then
    `leftDeriv a (infiltrationProd α k fs m) =
    infiltrationProd α k (fun i => fs i + infiltrationEval α k fs (q i)) m − infiltrationProd α k fs m`.
    The right-hand side is the infiltration product of the *extended* generators
    `fs i + leftDeriv a (fs i)`, minus the ordinary product.  Proven by induction on the
    support of `m`, peeling off one generator at a time: the 3-term Leibniz rule for
    `leftDeriv a` (an infiltration) plus `leftDeriv_infiltrationPow` make the cross terms
    telescope. -/
private theorem leftDeriv_infiltrationProd_monomial (k : ℕ) (fs : Fin k → Series α) (a : α)
    (q : Fin k → MvPolynomial (Fin k) ℚ)
    (hq : ∀ i, leftDeriv α a (fs i) = infiltrationEval α k fs (q i))
    (m : Fin k →₀ ℕ) :
    leftDeriv α a (infiltrationProd α k fs m) =
      infiltrationProd α k (fun i => fs i + infiltrationEval α k fs (q i)) m -
      infiltrationProd α k fs m := by
  let fs' : Fin k → Series α := fun i => fs i + infiltrationEval α k fs (q i)
  have hmain : ∀ (s : Finset (Fin k)) (m : Fin k →₀ ℕ), m.support ⊆ s →
      leftDeriv α a (infiltrationProd α k fs m) =
        infiltrationProd α k fs' m - infiltrationProd α k fs m := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        intro m hm
        have hm0 : m = 0 := by
          rw [Finsupp.ext_iff]
          intro j
          by_contra hj
          have : j ∈ m.support := Finsupp.mem_support_iff.mpr hj
          exact Finset.notMem_empty j (Finset.mem_of_subset hm this)
        rw [hm0, infiltrationProd_zero, infiltrationProd_zero, infiltrationUnit_leftDeriv a, sub_self]
    | insert i s h ih =>
        intro m hm
        by_cases him : i ∈ m.support
        · have hmi : m i ≠ 0 := Finsupp.mem_support_iff.mp him
          let m' := m - Finsupp.single i (m i)
          have hsub : m'.support ⊆ s := by
            intro j hjj
            have hjne : j ≠ i := by
              intro hj
              have : m' j = 0 := by
                rw [hj]
                dsimp only [m']
                simp [Finsupp.tsub_apply, Finsupp.single_apply]
              exact (Finsupp.mem_support_iff.mp hjj) this
            have hjm : j ∈ m.support := by
              rw [Finsupp.mem_support_iff]
              have hsubj : m' j = m j := by
                dsimp only [m']
                rw [Finsupp.tsub_apply]
                simp [hjne, Finsupp.single_apply]
              rw [← hsubj]
              exact Finsupp.mem_support_iff.mp hjj
            have hjin : j ∈ insert i s := Finset.mem_of_subset hm hjm
            have hjin' : j ∈ s := by
              rw [Finset.mem_insert] at hjin
              exact hjin.resolve_left hjne
            exact hjin'
          have hsplit : m = m' + Finsupp.single i (m i) := by
            rw [Finsupp.ext_iff]
            intro j
            by_cases hj : j = i
            · rw [hj]
              dsimp only [m']
              simp [Finsupp.tsub_apply, Finsupp.single_apply]
            · dsimp only [m']
              simp [hj, Finsupp.tsub_apply, Finsupp.single_apply]
          have hprod : infiltrationProd α k fs m =
              infiltration α (infiltrationProd α k fs m') (infiltrationPow α (fs i) (m i)) := by
            have h1 : infiltrationProd α k fs m =
                infiltrationProd α k fs (m' + Finsupp.single i (m i)) :=
              congrArg (infiltrationProd α k fs) hsplit
            have h2 : infiltrationProd α k fs (m' + Finsupp.single i (m i)) =
                infiltration α (infiltrationProd α k fs m')
                  (infiltrationProd α k fs (Finsupp.single i (m i))) :=
              infiltrationProd_add k fs m' (Finsupp.single i (m i))
            have h3 : infiltrationProd α k fs (Finsupp.single i (m i)) =
                infiltrationPow α (fs i) (m i) :=
              infiltrationProd_single k fs i (m i)
            calc
              infiltrationProd α k fs m = infiltrationProd α k fs (m' + Finsupp.single i (m i)) := h1
              _ = infiltration α (infiltrationProd α k fs m')
                    (infiltrationProd α k fs (Finsupp.single i (m i))) := h2
              _ = infiltration α (infiltrationProd α k fs m') (infiltrationPow α (fs i) (m i)) := by
                rw [h3]
          have hprod' : infiltrationProd α k fs' m =
              infiltration α (infiltrationProd α k fs' m') (infiltrationPow α (fs' i) (m i)) := by
            have h1 : infiltrationProd α k fs' m =
                infiltrationProd α k fs' (m' + Finsupp.single i (m i)) :=
              congrArg (infiltrationProd α k fs') hsplit
            have h2 : infiltrationProd α k fs' (m' + Finsupp.single i (m i)) =
                infiltration α (infiltrationProd α k fs' m')
                  (infiltrationProd α k fs' (Finsupp.single i (m i))) :=
              infiltrationProd_add k fs' m' (Finsupp.single i (m i))
            have h3 : infiltrationProd α k fs' (Finsupp.single i (m i)) =
                infiltrationPow α (fs' i) (m i) :=
              infiltrationProd_single k fs' i (m i)
            calc
              infiltrationProd α k fs' m = infiltrationProd α k fs' (m' + Finsupp.single i (m i)) := h1
              _ = infiltration α (infiltrationProd α k fs' m')
                    (infiltrationProd α k fs' (Finsupp.single i (m i))) := h2
              _ = infiltration α (infiltrationProd α k fs' m') (infiltrationPow α (fs' i) (m i)) := by
                rw [h3]
          rw [hprod, hprod']
          let R := infiltrationProd α k fs m'
          let R' := infiltrationProd α k fs' m'
          let P := infiltrationPow α (fs i) (m i)
          let P' := infiltrationPow α (fs' i) (m i)
          have hIH : leftDeriv α a R = R' - R := by
            dsimp only [R, R']
            exact ih m' hsub
          have hP : leftDeriv α a P = P' - P := by
            dsimp only [P, P']
            simpa [show fs' i = fs i + infiltrationEval α k fs (q i) by rfl] using
              leftDeriv_infiltrationPow k fs a q hq i (m i)
          rw [infiltrationLeibniz R P a, hIH, hP]
          have hgoal : infiltration α (R' - R) P + infiltration α R (P' - P) +
              infiltration α (R' - R) (P' - P) = infiltration α R' P' - infiltration α R P := by
            simp [infiltration_add_left, infiltration_add_right, infiltration_smul_left,
                infiltration_smul_right, neg_smul, sub_eq_add_neg, add_sub, sub_add,
                add_assoc, add_comm, add_left_comm]
          rw [hgoal]
        · have hsup : m.support ⊆ s := by
            intro j hjj
            have hjne : j ≠ i := by
              intro hj
              have : j ∉ m.support := by
                rw [hj]
                exact him
              exact this hjj
            have hjin : j ∈ insert i s := Finset.mem_of_subset hm hjj
            have hjin' : j ∈ s := by
              rw [Finset.mem_insert] at hjin
              exact hjin.resolve_left hjne
            exact hjin'
          exact ih m hsup
  exact hmain Finset.univ m (Finset.subset_univ m.support)

/-- The iterated infiltration power at the empty word is the pointwise power:
    `infiltrationPow α f n [] = f [] ^ n`.  The base case is the unit (`1 = f [] ^ 0`);
    the step uses `(f ↑ g) [] = f [] · g []` (`infiltrationRec_nil`). -/
private theorem infiltrationPow_nil (f : Series α) (n : ℕ) :
    infiltrationPow α f n [] = f [] ^ n := by
  induction n with
  | zero =>
      simp [infiltrationPow_zero, infiltrationUnit]
  | succ n ih =>
      rw [infiltrationPow_succ, infiltration, infiltrationRec_nil, ih]
      ring

/-- The infiltration monomial at the empty word is the pointwise monomial:
    `infiltrationProd α k fs m [] = ∏ i, (fs i) [] ^ (m i)`.  The infiltration product at the
    empty word is the pointwise product (`infiltrationRec_nil`), so the fold over the iterated
    powers becomes the pointwise product of the powers at the empty word. -/
private theorem infiltrationProd_nil (k : ℕ) (fs : Fin k → Series α) (m : Fin k →₀ ℕ) :
    infiltrationProd α k fs m [] = ∏ i : Fin k, (fs i) [] ^ (m i) := by
  have : ∀ (s : Finset (Fin k)),
      s.fold (infiltration α) (infiltrationUnit α) (fun i => infiltrationPow α (fs i) (m i)) [] =
        ∏ i ∈ s, (fs i) [] ^ (m i) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        simp [Finset.fold_empty, infiltrationUnit, Finset.prod_empty]
    | insert x s hx ih =>
        simp [infiltration, Finset.fold_insert hx, infiltrationRec_nil, infiltrationPow_nil, ih,
            Finset.prod_insert hx]
  rw [infiltrationProd_eq_fold]
  simpa using this Finset.univ

/-! ### `infiltrationEval` and the general infiltration `Δ_q = S_q − id` -/

/-- `infiltrationEval` commutes with subtraction: `infiltrationEval α k fs (p − q) =
    infiltrationEval α k fs p − infiltrationEval α k fs q`. -/
private theorem infiltrationEval_sub (k : ℕ) (fs : Fin k → Series α)
    (p q : MvPolynomial (Fin k) ℚ) :
    infiltrationEval α k fs (p - q) = infiltrationEval α k fs p - infiltrationEval α k fs q := by
  rw [show p - q = p + -q by simp [sub_eq_add_neg]]
  rw [infiltrationEval_add]
  have hneg : infiltrationEval α k fs (-q) = -(infiltrationEval α k fs q) := by
    rw [show -q = (-1 : ℚ) • q by simp, infiltrationEval_smul]
    simp
  rw [hneg]
  simp [sub_eq_add_neg]

/-- The general substitution endomorphism `S_q`: `S_map_gen k q` is the algebra endomorphism
    of `MvPolynomial (Fin k) ℚ` substituting `X_i ↦ X_i + q i`.  This is the polynomial-level
    analogue of the letter map `S_map A a` (which is `S_map_gen A.dim (fun i => A.Δ a i)`). -/
noncomputable def S_map_gen (k : ℕ) (q : Fin k → MvPolynomial (Fin k) ℚ) :
    MvPolynomial (Fin k) ℚ →ₐ[ℚ] MvPolynomial (Fin k) ℚ :=
  aeval (fun i => MvPolynomial.X i + q i)

/-- `S_map_gen k q` sends the variable `X i` to `X i + q i`. -/
private theorem S_map_gen_X (k : ℕ) (q : Fin k → MvPolynomial (Fin k) ℚ) (i : Fin k) :
    S_map_gen k q (MvPolynomial.X i) = MvPolynomial.X i + q i := by
  change MvPolynomial.aeval (fun i => MvPolynomial.X i + q i) (MvPolynomial.X i) =
      MvPolynomial.X i + q i
  rw [MvPolynomial.aeval_X]

/-- Substituting `X_i ↦ X_i + r i` before evaluating in the infiltration algebra is the same
    as evaluating in the algebra with the generators shifted to `fs i + infiltrationEval (r i)`:
    `infiltrationEval α k fs (S_map_gen k r p) =
    infiltrationEval α k (fun i => fs i + infiltrationEval α k fs (r i)) p`.
    Both sides are infiltration-algebra homomorphisms sending `X_i` to
    `fs i + infiltrationEval α k fs (r i)`, so they coincide (`infiltrationHom_ext`). -/
private theorem infiltrationEval_aeval (k : ℕ) (fs : Fin k → Series α)
    (r : Fin k → MvPolynomial (Fin k) ℚ) (p : MvPolynomial (Fin k) ℚ) :
    infiltrationEval α k fs (S_map_gen k r p) =
      infiltrationEval α k (fun i => fs i + infiltrationEval α k fs (r i)) p := by
  let h1 := fun (p : MvPolynomial (Fin k) ℚ) => infiltrationEval α k fs (S_map_gen k r p)
  let h2 := fun (p : MvPolynomial (Fin k) ℚ) =>
      infiltrationEval α k (fun i => fs i + infiltrationEval α k fs (r i)) p
  have hadd1 : ∀ p q, h1 (p + q) = h1 p + h1 q := by
    intro p q
    dsimp [h1]
    rw [map_add (S_map_gen k r) p q, infiltrationEval_add]
  have hsmul1 : ∀ (c : ℚ) p, h1 (c • p) = c • h1 p := by
    intro c p
    dsimp [h1]
    rw [map_smul (S_map_gen k r) c p, infiltrationEval_smul]
  have hmul1 : ∀ p q, h1 (p * q) = infiltration α (h1 p) (h1 q) := by
    intro p q
    dsimp [h1]
    rw [map_mul (S_map_gen k r) p q, infiltrationEval_mul]
  have hadd2 : ∀ p q, h2 (p + q) = h2 p + h2 q := by
    intro p q
    dsimp [h2]
    rw [infiltrationEval_add]
  have hsmul2 : ∀ (c : ℚ) p, h2 (c • p) = c • h2 p := by
    intro c p
    dsimp [h2]
    rw [infiltrationEval_smul]
  have hmul2 : ∀ p q, h2 (p * q) = infiltration α (h2 p) (h2 q) := by
    intro p q
    dsimp [h2]
    rw [infiltrationEval_mul]
  have hone : h1 1 = h2 1 := by
    dsimp [h1, h2]
    rw [map_one (S_map_gen k r), infiltrationEval_one, infiltrationEval_one]
  have hgen : ∀ i, h1 (MvPolynomial.X i) = h2 (MvPolynomial.X i) := by
    intro i
    dsimp [h1, h2]
    rw [S_map_gen_X, infiltrationEval_add, infiltrationEval_X]
    simp [infiltrationEval_X]
  exact (infiltrationHom_ext k h1 h2 hadd1 hadd2 hsmul1 hsmul2 hmul1 hmul2 hone hgen) p

/-- The general polynomial infiltration `Δ_q = S_q − id`: `infiltrationExtGen k q p =
    S_map_gen k q p − p`.  This is the polynomial-level analogue of the letter infiltration
    `infiltrationExt A a` (which is `Δ_q` with `q i = A.Δ a i`). -/
noncomputable def infiltrationExtGen (k : ℕ) (q : Fin k → MvPolynomial (Fin k) ℚ)
    (p : MvPolynomial (Fin k) ℚ) : MvPolynomial (Fin k) ℚ :=
  S_map_gen k q p - p

/-- `infiltrationExtGen k q` is `ℚ`-linear: it sends `0` to `0`. -/
private theorem infiltrationExtGen_zero (k : ℕ) (q : Fin k → MvPolynomial (Fin k) ℚ) :
    infiltrationExtGen k q 0 = 0 := by
  dsimp [infiltrationExtGen]
  rw [map_zero (S_map_gen k q)]
  ring

/-- `infiltrationExtGen k q` is `ℚ`-linear: it preserves addition. -/
private theorem infiltrationExtGen_add (k : ℕ) (q : Fin k → MvPolynomial (Fin k) ℚ)
    (p r : MvPolynomial (Fin k) ℚ) :
    infiltrationExtGen k q (p + r) = infiltrationExtGen k q p + infiltrationExtGen k q r := by
  dsimp [infiltrationExtGen]
  rw [map_add (S_map_gen k q) p r]
  ring

/-- `infiltrationExtGen k q` is `ℚ`-linear: it preserves scalar multiplication. -/
private theorem infiltrationExtGen_smul (k : ℕ) (q : Fin k → MvPolynomial (Fin k) ℚ) (c : ℚ)
    (p : MvPolynomial (Fin k) ℚ) :
    infiltrationExtGen k q (c • p) = c • infiltrationExtGen k q p := by
  dsimp [infiltrationExtGen]
  rw [map_smul (S_map_gen k q) c p]
  simp [smul_sub]

/-- The letter infiltration `infiltrationExt A a` is the general infiltration `Δ_q` with
    `q i = A.Δ a i`: `infiltrationExt A a p = infiltrationExtGen A.dim (fun i => A.Δ a i) p`. -/
private theorem infiltrationExt_eq_infiltrationExtGen (A : InfiltrationAutomaton α) (a : α)
    (p : MvPolynomial (Fin A.dim) ℚ) :
    infiltrationExt A a p = infiltrationExtGen A.dim (fun i => A.Δ a i) p := by
  dsimp [infiltrationExt, infiltrationExtGen, S_map, S_map_gen]

/-- Evaluating the general infiltration of a monomial in the infiltration algebra gives the
    difference of the extended and ordinary infiltration products:
    `infiltrationEval α k fs (infiltrationExtGen k q (monomial m 1)) =
    infiltrationProd α k (fun i => fs i + infiltrationEval α k fs (q i)) m − infiltrationProd α k fs m`.
    The LHS is `infiltrationEval (S_q (X^m) − X^m)`; by `infiltrationEval_aeval`, evaluating
    `S_q (X^m)` shifts the generators to `fs i + infiltrationEval (q i)`, and the monomial
    evaluation is the infiltration product. -/
private theorem infiltrationEval_infiltrationExtGen_monomial (k : ℕ) (fs : Fin k → Series α)
    (q : Fin k → MvPolynomial (Fin k) ℚ) (m : Fin k →₀ ℕ) :
    infiltrationEval α k fs (infiltrationExtGen k q (MvPolynomial.monomial m 1)) =
      infiltrationProd α k (fun i => fs i + infiltrationEval α k fs (q i)) m -
      infiltrationProd α k fs m := by
  dsimp [infiltrationExtGen]
  rw [infiltrationEval_sub]
  have hS : infiltrationEval α k fs (S_map_gen k q (MvPolynomial.monomial m 1)) =
      infiltrationProd α k (fun i => fs i + infiltrationEval α k fs (q i)) m := by
    rw [infiltrationEval_aeval, infiltrationEval_monomial]
    simp
  have hmono : infiltrationEval α k fs (MvPolynomial.monomial m 1) = infiltrationProd α k fs m := by
    rw [infiltrationEval_monomial]
    simp
  rw [hS, hmono]

/-- The left derivative commutes with the infiltration evaluation: if `leftDeriv a (fs i) =
    infiltrationEval α k fs (q i)` for all `i`, then `leftDeriv a (infiltrationEval α k fs p) =
    infiltrationEval α k fs (infiltrationExtGen k q p)`.  Both sides are `ℚ`-linear in `p`;
    on a monomial `X^m` both are `leftDeriv a (infiltrationProd α k fs m)` (the LHS by
    linearity of `leftDeriv`, the RHS by the key monomial identity plus
    `leftDeriv_infiltrationProd_monomial`), so they agree on all of `p`. -/
private theorem leftDeriv_infiltrationEval_infiltration (k : ℕ) (fs : Fin k → Series α) (a : α)
    (q : Fin k → MvPolynomial (Fin k) ℚ)
    (hq : ∀ i, leftDeriv α a (fs i) = infiltrationEval α k fs (q i))
    (p : MvPolynomial (Fin k) ℚ) :
    leftDeriv α a (infiltrationEval α k fs p) = infiltrationEval α k fs (infiltrationExtGen k q p) := by
  have hLHS : leftDeriv α a (infiltrationEval α k fs p) =
      ∑ m ∈ p.support, p.coeff m • leftDeriv α a (infiltrationProd α k fs m) := by
    rw [infiltrationEval]
    have hsum : leftDeriv α a (p.support.sum fun m => p.coeff m • infiltrationProd α k fs m) =
        ∑ m ∈ p.support, p.coeff m • leftDeriv α a (infiltrationProd α k fs m) := by
      have : ∀ (t : Finset (Fin k →₀ ℕ)) (g : (Fin k →₀ ℕ) → Series α),
          leftDeriv α a (∑ j ∈ t, g j) = ∑ j ∈ t, leftDeriv α a (g j) := by
        intro t g
        induction t using Finset.induction_on with
        | empty => simp [leftDeriv_zero]
        | insert x t hx ih' =>
            simp [Finset.sum_insert hx, ih', leftDeriv_add a]
      have hlin := this p.support (fun m => p.coeff m • infiltrationProd α k fs m)
      rw [hlin]
      apply Finset.sum_congr rfl
      intro m _
      rw [leftDeriv_smul a]
    rw [hsum]
  have hRHS : infiltrationEval α k fs (infiltrationExtGen k q p) =
      ∑ m ∈ p.support, p.coeff m • leftDeriv α a (infiltrationProd α k fs m) := by
    have hdecomp : p = ∑ m ∈ p.support, p.coeff m • MvPolynomial.monomial m 1 := by
      simp [MvPolynomial.smul_monomial]
    have hext : infiltrationExtGen k q p =
        ∑ m ∈ p.support, p.coeff m • infiltrationExtGen k q (MvPolynomial.monomial m 1) := by
      conv =>
        lhs
        rw [hdecomp]
      have hlin : ∀ (t : Finset (Fin k →₀ ℕ)) (g : (Fin k →₀ ℕ) → MvPolynomial (Fin k) ℚ),
          infiltrationExtGen k q (∑ j ∈ t, g j) = ∑ j ∈ t, infiltrationExtGen k q (g j) := by
        intro t g
        induction t using Finset.induction_on with
        | empty => simp [infiltrationExtGen_zero]
        | insert x t hx ih' =>
            simp [Finset.sum_insert hx, ih', infiltrationExtGen_add]
      rw [hlin (t := p.support) (g := fun m => p.coeff m • MvPolynomial.monomial m 1)]
      apply Finset.sum_congr rfl
      intro m _
      rw [infiltrationExtGen_smul]
    rw [hext]
    have hsum : infiltrationEval α k fs (∑ m ∈ p.support,
        p.coeff m • infiltrationExtGen k q (MvPolynomial.monomial m 1)) =
        ∑ m ∈ p.support, p.coeff m •
          infiltrationEval α k fs (infiltrationExtGen k q (MvPolynomial.monomial m 1)) := by
      have hlin : ∀ (t : Finset (Fin k →₀ ℕ)) (g : (Fin k →₀ ℕ) → MvPolynomial (Fin k) ℚ),
          infiltrationEval α k fs (∑ j ∈ t, g j) = ∑ j ∈ t, infiltrationEval α k fs (g j) := by
        intro t g
        induction t using Finset.induction_on with
        | empty => simp [infiltrationEval_zero]
        | insert x t hx ih' =>
            simp [Finset.sum_insert hx, ih', infiltrationEval_add]
      have hlin2 := hlin p.support
          (fun m => p.coeff m • infiltrationExtGen k q (MvPolynomial.monomial m 1))
      rw [hlin2]
      apply Finset.sum_congr rfl
      intro m _
      rw [infiltrationEval_smul]
    rw [hsum]
    apply Finset.sum_congr rfl
    intro m _
    have hmono : infiltrationEval α k fs (infiltrationExtGen k q (MvPolynomial.monomial m 1)) =
        infiltrationProd α k (fun i => fs i + infiltrationEval α k fs (q i)) m -
        infiltrationProd α k fs m :=
      infiltrationEval_infiltrationExtGen_monomial k fs q m
    have hlp : leftDeriv α a (infiltrationProd α k fs m) =
        infiltrationProd α k (fun i => fs i + infiltrationEval α k fs (q i)) m -
        infiltrationProd α k fs m :=
      leftDeriv_infiltrationProd_monomial k fs a q hq m
    rw [hmono, ← hlp]
  rw [hLHS, hRHS]

/-- Every infiltration-finite series is infiltration-finite in the semantic sense (the
    "finite implies finite-sem" direction of the coincidence).  The witnessing tuple is the
    generator series `A.sem (X_i)`, closed under left derivatives by the derivation property
    `sem_deriv`; `f` is the infiltration polynomial `X_0` in that tuple. -/
private theorem infiltrationFinite_of_recognisable (f : Series α)
    (hfin : IsInfiltrationRecognisable α f) : IsInfiltrationFinite α f := by
  obtain ⟨A, hA⟩ := hfin
  let X0 : MvPolynomial (Fin A.dim) ℚ := MvPolynomial.X (Fin.mk 0 A.hdim)
  let fs := fun i => A.sem (MvPolynomial.X i)
  have hf : f = A.sem X0 := by
    rw [← hA, InfiltrationAutomaton.recognised]
  have h1 : f = infiltrationEval α A.dim fs X0 := by
    rw [hf, sem_eq_infiltrationEval]
  refine ⟨A.dim, fs, X0, h1, ?_⟩
  intro a i
  refine ⟨A.Δ a i, ?_⟩
  have hlhs : leftDeriv α a (fs i) = A.sem (A.Δ a i) := by
    dsimp [fs]
    rw [sem_deriv, infiltrationExt_X]
  rw [hlhs, sem_eq_infiltrationEval]

/-- Every infiltration-finite series in the semantic sense is infiltration-finite (the
    "finite-sem implies finite" direction of the coincidence).  Given
    `f = infiltrationEval α k fs p` with `fs` closed under left derivatives, extend the tuple
    to `g = extTuple f k fs` (so `g 0 = f` and `g (Fin.succ i) = fs i`), show `g` is closed
    under left derivatives (the `g 0` slot via `leftDeriv_infiltrationEval_infiltration`, the
    `fs i` slots by the closure of `fs`), and build the automaton from the closure. -/
private theorem infiltrationRecognisable_of_finite (f : Series α)
    (hsem : IsInfiltrationFinite α f) : IsInfiltrationRecognisable α f := by
  obtain ⟨k, fs, p, hf, hclose⟩ := hsem
  let g := extTuple f k fs
  have hclose_g : ∀ (a : α) (j : Fin (k+1)),
      ∃ q, leftDeriv α a (g j) = infiltrationEval α (k+1) g q := by
    intro a j
    by_cases h0 : j = 0
    · let qf : Fin k → MvPolynomial (Fin k) ℚ := fun i => Classical.choose (hclose a i)
      have hqf : ∀ i, leftDeriv α a (fs i) = infiltrationEval α k fs (qf i) := by
        intro i
        dsimp [qf]
        exact Classical.choose_spec (hclose a i)
      have hg0 : g 0 = f := by
        dsimp [g]
        rw [extTuple_zero]
      refine ⟨embedPoly k (infiltrationExtGen k qf p), ?_⟩
      calc
        leftDeriv α a (g j) = leftDeriv α a (g 0) := by rw [h0]
        _ = leftDeriv α a f := by rw [hg0]
        _ = leftDeriv α a (infiltrationEval α k fs p) := by rw [← hf]
        _ = infiltrationEval α k fs (infiltrationExtGen k qf p) := by
          rw [leftDeriv_infiltrationEval_infiltration k fs a qf hqf p]
        _ = infiltrationEval α (k+1) g (embedPoly k (infiltrationExtGen k qf p)) := by
          rw [infiltrationEval_embed]
    · have hj : j.val ≠ 0 := by
        intro hj0
        exact h0 (Fin.ext hj0)
      let i : Fin k := ⟨j.val - 1, by
        have := j.isLt
        omega⟩
      have hi : Fin.succ i = j := by
        apply Fin.ext
        simp [i]
        omega
      let qi := Classical.choose (hclose a i)
      have hqi : leftDeriv α a (fs i) = infiltrationEval α k fs qi := by
        rw [show qi = Classical.choose (hclose a i) from rfl]
        exact Classical.choose_spec (hclose a i)
      have hgs : g (Fin.succ i) = fs i := by
        dsimp [g]
        rw [extTuple_succ]
      refine ⟨embedPoly k qi, ?_⟩
      calc
        leftDeriv α a (g j) = leftDeriv α a (g (Fin.succ i)) := by rw [← hi]
        _ = leftDeriv α a (fs i) := by rw [hgs]
        _ = infiltrationEval α k fs qi := hqi
        _ = infiltrationEval α (k+1) g (embedPoly k qi) := by rw [infiltrationEval_embed]
  let Δ : α → Fin (k+1) → MvPolynomial (Fin (k+1)) ℚ :=
      fun a j => Classical.choose (hclose_g a j)
  have hΔ : ∀ (a : α) (j : Fin (k+1)),
      leftDeriv α a (g j) = infiltrationEval α (k+1) g (Δ a j) := by
    intro a j
    rw [show Δ a j = Classical.choose (hclose_g a j) from rfl]
    exact Classical.choose_spec (hclose_g a j)
  let A : InfiltrationAutomaton α :=
    { dim := k + 1,
      hdim := by omega,
      F := fun i => (g i) [],
      Δ := Δ }
  have hsem : ∀ (w : List α) (p : MvPolynomial (Fin (k+1)) ℚ),
      A.sem p w = infiltrationEval α (k+1) g p w := by
    intro w
    induction w with
    | nil =>
      intro p
      dsimp [InfiltrationAutomaton.sem]
      rw [Mword_nil]
      simp only [id]
      dsimp [A]
      have hLHS : eval (fun i => (g i) []) p =
          ∑ m ∈ p.support, p.coeff m * ∏ i : Fin (k+1), (g i) [] ^ (m i) := by
        rw [MvPolynomial.eval_eq']
      have hRHS : infiltrationEval α (k+1) g p [] =
          ∑ m ∈ p.support, p.coeff m * ∏ i : Fin (k+1), (g i) [] ^ (m i) := by
        rw [infiltrationEval]
        have hsum : (∑ m ∈ p.support, p.coeff m • infiltrationProd α (k+1) g m) [] =
            ∑ m ∈ p.support, p.coeff m * infiltrationProd α (k+1) g m [] := by
          simp
        rw [hsum]
        apply Finset.sum_congr rfl
        intro m _
        rw [infiltrationProd_nil]
      rw [hLHS, hRHS]
    | cons a w' ih =>
      intro p
      dsimp [InfiltrationAutomaton.sem]
      rw [Mword_cons]
      change A.sem (infiltrationExt A a p) w' = _
      have h1 : A.sem (infiltrationExt A a p) w' =
          infiltrationEval α (k+1) g (infiltrationExt A a p) w' := ih (infiltrationExt A a p)
      rw [h1]
      have h2 : infiltrationEval α (k+1) g (infiltrationExt A a p) =
          leftDeriv α a (infiltrationEval α (k+1) g p) := by
        rw [infiltrationExt_eq_infiltrationExtGen]
        rw [← leftDeriv_infiltrationEval_infiltration (k+1) g a (fun i => A.Δ a i)
          (by intro i; exact hΔ a i) p]
      rw [h2]
      rfl
  have hrec : A.recognised = f := by
    dsimp [InfiltrationAutomaton.recognised]
    have hg0 : g 0 = f := by
      dsimp [g]
      rw [extTuple_zero]
    have hX0 : A.sem (MvPolynomial.X 0) = g 0 := by
      funext w
      simpa [infiltrationEval_X] using hsem w (MvPolynomial.X 0)
    rw [hX0]
    exact hg0
  exact ⟨A, hrec⟩

/--
conclusion: Lax946791.Infiltration.InfiltrationCoincidence
---
The infiltration coincidence theorem (paper §7): a series is infiltration-finite (an
infiltration polynomial in a finite tuple of series closed under the left derivatives) if
and only if it is recognised by an infiltration automaton.  The "finite implies recognisable"
direction extends the witnessing tuple by the series itself and builds the automaton from the
closure under left derivatives; the "recognisable implies finite" direction reads off the
generator tuple `A.sem (X_i)`, closed under left derivatives by the derivation property. -/
theorem InfiltrationCoincidence (f : Series α) :
    IsInfiltrationFinite α f ↔ IsInfiltrationRecognisable α f := by
  constructor
  · intro hfin
    exact infiltrationRecognisable_of_finite f hfin
  · intro hrec
    exact infiltrationFinite_of_recognisable f hrec

/-! ### The closure: combining witnessing tuples -/

/-- The witnessing tuple of `f` (size `k`) and `g` (size `k'`) concatenated: the first
    `k` slots are `fs`, the remaining `k'` slots are `fs'`. -/
noncomputable def combineTuple (k k' : ℕ) (fs : Fin k → Series α) (fs' : Fin k' → Series α) :
    Fin (k + k') → Series α :=
  fun i => if h : i.val < k then fs ⟨i.val, h⟩ else fs' ⟨i.val - k, by omega⟩

/-- Embedding a polynomial in `Fin k` into `Fin (k + k')`, keeping the variables
    `X_0, …, X_{k-1}` in place (the trailing slots are unused): `X_i ↦ X_i`. -/
noncomputable def embedFront (k k' : ℕ) (p : MvPolynomial (Fin k) ℚ) : MvPolynomial (Fin (k + k')) ℚ :=
  aeval (fun i : Fin k => MvPolynomial.X ⟨i.val, by omega⟩) p

/-- Embedding a polynomial in `Fin k'` into `Fin (k + k')`, shifted past the first `k`
    slots: `X_i ↦ X_{k + i}`. -/
noncomputable def embedBack (k k' : ℕ) (p : MvPolynomial (Fin k') ℚ) : MvPolynomial (Fin (k + k')) ℚ :=
  aeval (fun i : Fin k' => MvPolynomial.X ⟨k + i.val, by omega⟩) p

/-- An infiltration polynomial in `fs` is unchanged when the tuple is extended with `fs'` and
    the polynomial is embedded at the front: `infiltrationEval α k fs p =
    infiltrationEval α (k + k') (combineTuple k k' fs fs') (embedFront k k' p)`.  Both sides are
    infiltration-algebra homomorphisms sending `X_i` to `fs i`; the trailing slots of the extended
    tuple are unused by the embedded polynomial, so their values (`fs'`) are irrelevant. -/
private theorem infiltrationEval_embedFront (k k' : ℕ) (fs : Fin k → Series α)
    (fs' : Fin k' → Series α) (p : MvPolynomial (Fin k) ℚ) :
    infiltrationEval α k fs p = infiltrationEval α (k + k') (combineTuple k k' fs fs') (embedFront k k' p) := by
  let aev : MvPolynomial (Fin k) ℚ →ₐ[ℚ] MvPolynomial (Fin (k + k')) ℚ :=
    MvPolynomial.aeval (fun i : Fin k => MvPolynomial.X ⟨i.val, by omega⟩)
  have hadd2 : ∀ p q, infiltrationEval α (k + k') (combineTuple k k' fs fs') (embedFront k k' (p + q)) =
      infiltrationEval α (k + k') (combineTuple k k' fs fs') (embedFront k k' p) +
        infiltrationEval α (k + k') (combineTuple k k' fs fs') (embedFront k k' q) := by
    intro p q
    rw [embedFront, embedFront, embedFront]
    rw [map_add aev p q, infiltrationEval_add]
  have hsmul2 : ∀ (c : ℚ) p, infiltrationEval α (k + k') (combineTuple k k' fs fs') (embedFront k k' (c • p)) =
      c • infiltrationEval α (k + k') (combineTuple k k' fs fs') (embedFront k k' p) := by
    intro c p
    rw [embedFront, embedFront]
    rw [map_smul aev c p, infiltrationEval_smul]
  have hmul2 : ∀ p q, infiltrationEval α (k + k') (combineTuple k k' fs fs') (embedFront k k' (p * q)) =
      infiltration α (infiltrationEval α (k + k') (combineTuple k k' fs fs') (embedFront k k' p))
        (infiltrationEval α (k + k') (combineTuple k k' fs fs') (embedFront k k' q)) := by
    intro p q
    rw [embedFront, embedFront, embedFront]
    rw [map_mul aev p q, infiltrationEval_mul]
  have hone : infiltrationEval α k fs 1 = infiltrationEval α (k + k') (combineTuple k k' fs fs') (embedFront k k' 1) := by
    rw [infiltrationEval_one, embedFront, map_one aev, infiltrationEval_one]
  have hgen : ∀ i, infiltrationEval α k fs (MvPolynomial.X i) =
      infiltrationEval α (k + k') (combineTuple k k' fs fs') (embedFront k k' (MvPolynomial.X i)) := by
    intro i
    rw [infiltrationEval_X, embedFront, MvPolynomial.aeval_X, infiltrationEval_X]
    simp [combineTuple]
  exact infiltrationHom_ext k
    (fun p => infiltrationEval α k fs p)
    (fun p => infiltrationEval α (k + k') (combineTuple k k' fs fs') (embedFront k k' p))
    (infiltrationEval_add k fs) hadd2
    (infiltrationEval_smul k fs) hsmul2
    (infiltrationEval_mul k fs) hmul2
    hone hgen p

/-- The back-embedding analogue: `infiltrationEval α k' fs' p =
    infiltrationEval α (k + k') (combineTuple k k' fs fs') (embedBack k k' p)`. -/
private theorem infiltrationEval_embedBack (k k' : ℕ) (fs : Fin k → Series α)
    (fs' : Fin k' → Series α) (p : MvPolynomial (Fin k') ℚ) :
    infiltrationEval α k' fs' p = infiltrationEval α (k + k') (combineTuple k k' fs fs') (embedBack k k' p) := by
  let aev : MvPolynomial (Fin k') ℚ →ₐ[ℚ] MvPolynomial (Fin (k + k')) ℚ :=
    MvPolynomial.aeval (fun i : Fin k' => MvPolynomial.X ⟨k + i.val, by omega⟩)
  have hadd2 : ∀ p q, infiltrationEval α (k + k') (combineTuple k k' fs fs') (embedBack k k' (p + q)) =
      infiltrationEval α (k + k') (combineTuple k k' fs fs') (embedBack k k' p) +
        infiltrationEval α (k + k') (combineTuple k k' fs fs') (embedBack k k' q) := by
    intro p q
    rw [embedBack, embedBack, embedBack]
    rw [map_add aev p q, infiltrationEval_add]
  have hsmul2 : ∀ (c : ℚ) p, infiltrationEval α (k + k') (combineTuple k k' fs fs') (embedBack k k' (c • p)) =
      c • infiltrationEval α (k + k') (combineTuple k k' fs fs') (embedBack k k' p) := by
    intro c p
    rw [embedBack, embedBack]
    rw [map_smul aev c p, infiltrationEval_smul]
  have hmul2 : ∀ p q, infiltrationEval α (k + k') (combineTuple k k' fs fs') (embedBack k k' (p * q)) =
      infiltration α (infiltrationEval α (k + k') (combineTuple k k' fs fs') (embedBack k k' p))
        (infiltrationEval α (k + k') (combineTuple k k' fs fs') (embedBack k k' q)) := by
    intro p q
    rw [embedBack, embedBack, embedBack]
    rw [map_mul aev p q, infiltrationEval_mul]
  have hone : infiltrationEval α k' fs' 1 = infiltrationEval α (k + k') (combineTuple k k' fs fs') (embedBack k k' 1) := by
    rw [infiltrationEval_one, embedBack, map_one aev, infiltrationEval_one]
  have hgen : ∀ i, infiltrationEval α k' fs' (MvPolynomial.X i) =
      infiltrationEval α (k + k') (combineTuple k k' fs fs') (embedBack k k' (MvPolynomial.X i)) := by
    intro i
    rw [infiltrationEval_X, embedBack, MvPolynomial.aeval_X, infiltrationEval_X]
    simp [combineTuple]
  exact infiltrationHom_ext k'
    (fun p => infiltrationEval α k' fs' p)
    (fun p => infiltrationEval α (k + k') (combineTuple k k' fs fs') (embedBack k k' p))
    (infiltrationEval_add k' fs') hadd2
    (infiltrationEval_smul k' fs') hsmul2
    (infiltrationEval_mul k' fs') hmul2
    hone hgen p

/-- The concatenated tuple is closed under left derivatives, given that both summands are:
    the left derivative of a slot is the embedded left derivative of the corresponding
    summand slot. -/
private theorem combineTuple_closed (k k' : ℕ) (fs : Fin k → Series α) (fs' : Fin k' → Series α)
    (hfs : ∀ a (i : Fin k), ∃ q, leftDeriv α a (fs i) = infiltrationEval α k fs q)
    (hfs' : ∀ a (i : Fin k'), ∃ q, leftDeriv α a (fs' i) = infiltrationEval α k' fs' q) :
    ∀ a (i : Fin (k + k')), ∃ q,
      leftDeriv α a (combineTuple k k' fs fs' i) =
        infiltrationEval α (k + k') (combineTuple k k' fs fs') q := by
  intro a i
  by_cases hlt : i.val < k
  · let j : Fin k := ⟨i.val, hlt⟩
    obtain ⟨q, hq⟩ := hfs a j
    refine ⟨embedFront k k' q, ?_⟩
    have hci : combineTuple k k' fs fs' i = fs j := by
      simp [combineTuple, j, hlt]
    rw [hci, hq, infiltrationEval_embedFront]
  · let j : Fin k' := ⟨i.val - k, by omega⟩
    obtain ⟨q, hq⟩ := hfs' a j
    refine ⟨embedBack k k' q, ?_⟩
    have hci : combineTuple k k' fs fs' i = fs' j := by
      simp [combineTuple, j, hlt]
    rw [hci, hq, infiltrationEval_embedBack]

/-! ### The right derivative of an infiltration polynomial -/

/-- The right derivative of the infiltration unit is zero: appending a letter to a word makes
    it non-empty, so the unit (which is `1` only on the empty word) vanishes. -/
private theorem infiltrationUnit_rightDeriv (a : α) :
    rightDeriv α a (infiltrationUnit α) = 0 := by
  funext w
  have hne : w ++ [a] ≠ [] := by
    intro h
    have : (w ++ [a]).length = 0 := by rw [h]; simp
    have : (w ++ [a]).length = w.length + 1 := by simp [List.length_append, List.length_cons]
    omega
  simp [rightDeriv, infiltrationUnit, hne]

/-- Left and right derivatives commute: `leftDeriv a (rightDeriv b f) =
    rightDeriv b (leftDeriv a f)`.  Both sides are `f (a :: (w ++ [b]))`. -/
private theorem leftDeriv_rightDeriv_commute (f : Series α) (a b : α) :
    leftDeriv α a (rightDeriv α b f) = rightDeriv α b (leftDeriv α a f) := by
  funext w
  simp [leftDeriv, rightDeriv, List.cons_append]

/-- The right derivative of the infiltration product, in terms of the recurrence:
    `infiltrationRec f g (w ++ [a]) = infiltrationRec (rightDeriv a f) g w +
    infiltrationRec f (rightDeriv a g) w + infiltrationRec (rightDeriv a f) (rightDeriv a g) w`.
    Proven by induction on `w`, using the commutation of left and right derivatives at the
    step. -/
private theorem infiltrationRec_rightDeriv (a : α) (w : List α) :
    ∀ (f g : Series α),
    infiltrationRec α f g (w ++ [a]) =
      infiltrationRec α (rightDeriv α a f) g w +
        infiltrationRec α f (rightDeriv α a g) w +
        infiltrationRec α (rightDeriv α a f) (rightDeriv α a g) w := by
  induction w with
  | nil =>
      intro f g
      simp [infiltrationRec_cons, infiltrationRec_nil, leftDeriv, rightDeriv]
  | cons b w' ih =>
      intro f g
      have ihf := ih (leftDeriv α b f) g
      have ihg := ih f (leftDeriv α b g)
      have ihfg := ih (leftDeriv α b f) (leftDeriv α b g)
      have hc1 : rightDeriv α a (leftDeriv α b f) = leftDeriv α b (rightDeriv α a f) :=
        leftDeriv_rightDeriv_commute f b a
      have hc2 : rightDeriv α a (leftDeriv α b g) = leftDeriv α b (rightDeriv α a g) :=
        leftDeriv_rightDeriv_commute g b a
      simp [infiltrationRec_cons, List.cons_append, hc1, hc2, ihf, ihg, ihfg]
      ring

/-- The right derivative of the infiltration product of two series is the "Leibniz rule with a
    correction term": `rightDeriv a (f ↑ g) = (f + rightDeriv a f) ↑ (g + rightDeriv a g) −
    f ↑ g`.  Expanding the RHS by bilinearity gives the three-term rule
    `(rightDeriv a f) ↑ g + f ↑ (rightDeriv a g) + (rightDeriv a f) ↑ (rightDeriv a g)` (the
    extra last term accounts for the two series consuming the letter jointly). -/
private theorem infiltrationRightDerivProd (f g : Series α) (a : α) :
    rightDeriv α a (infiltration α f g) =
      infiltration α (f + rightDeriv α a f) (g + rightDeriv α a g) - infiltration α f g := by
  funext w
  have hLHS : rightDeriv α a (infiltration α f g) w = infiltrationRec α f g (w ++ [a]) := by
    simp [rightDeriv, infiltration]
  have hRHS : (infiltration α (f + rightDeriv α a f) (g + rightDeriv α a g) -
      infiltration α f g) w =
      infiltrationRec α (f + rightDeriv α a f) (g + rightDeriv α a g) w -
        infiltrationRec α f g w := by
    simp [infiltration]
  rw [hLHS, hRHS]
  have hbilin : infiltrationRec α (f + rightDeriv α a f) (g + rightDeriv α a g) w =
      infiltrationRec α f g w + infiltrationRec α f (rightDeriv α a g) w +
        infiltrationRec α (rightDeriv α a f) g w +
        infiltrationRec α (rightDeriv α a f) (rightDeriv α a g) w := by
    simp [infiltrationRec_add_left, infiltrationRec_add_right]
    abel
  rw [hbilin]
  rw [infiltrationRec_rightDeriv a w f g]
  ring

/-- The right derivative of an infiltration power: `rightDeriv a (f^n) =
    (f + rightDeriv a f)^n − f^n`, where `f^n` is the `n`-fold infiltration product `f ↑ … ↑ f`.
    Follows by induction on `n` from the two-factor rule. -/
private theorem infiltrationPow_rightDeriv (f : Series α) (n : ℕ) (a : α) :
    rightDeriv α a (infiltrationPow α f n) =
      infiltrationPow α (f + rightDeriv α a f) n - infiltrationPow α f n := by
  induction n with
  | zero =>
      simp [infiltrationPow_zero, infiltrationUnit_rightDeriv]
  | succ n' ih =>
      have hpow : infiltrationPow α f (n' + 1) = infiltration α (infiltrationPow α f n') f := by
        rw [infiltrationPow_succ]
        simp [infiltration_comm]
      have hpow' : infiltrationPow α (f + rightDeriv α a f) (n' + 1) =
          infiltration α (infiltrationPow α (f + rightDeriv α a f) n') (f + rightDeriv α a f) := by
        rw [infiltrationPow_succ]
        simp [infiltration_comm]
      rw [hpow, hpow']
      have hprod := infiltrationRightDerivProd (infiltrationPow α f n') f a
      simp [ih, hprod]

/-- The right derivative of an infiltration product (a monomial in the tuple):
    `rightDeriv a (∏ i, (fs i)^{m i}) = ∏ i, (fs i + rightDeriv a (fs i))^{m i} −
    ∏ i, (fs i)^{m i}`.  Each factor `fs i` is replaced by `fs i + rightDeriv a (fs i)` (the
    power rule), and the two-factor rule accumulates over the factors. -/
private theorem infiltrationProd_rightDeriv (k : ℕ) (fs : Fin k → Series α) (m : Fin k →₀ ℕ)
    (a : α) :
    rightDeriv α a (infiltrationProd α k fs m) =
      infiltrationProd α k (fun i => fs i + rightDeriv α a (fs i)) m -
        infiltrationProd α k fs m := by
  -- `infiltrationProd k fs m` is the fold of `infiltration` over the factors
  -- `infiltrationPow (fs i) (m i)`; prove the formula by induction on the index set.
  have hfold : ∀ (s : Finset (Fin k)),
      rightDeriv α a (s.fold (infiltration α) (infiltrationUnit α) (fun i => infiltrationPow α (fs i) (m i))) =
        s.fold (infiltration α) (infiltrationUnit α)
            (fun i => infiltrationPow α (fs i + rightDeriv α a (fs i)) (m i)) -
          s.fold (infiltration α) (infiltrationUnit α) (fun i => infiltrationPow α (fs i) (m i)) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        simp [infiltrationUnit_rightDeriv, Finset.fold_empty, sub_self]
    | insert x s hx ih =>
        -- `P`, `P'` are the original/augmented partial products over `s`;
        -- `q`, `q'` the original/augmented factor at index `x`.
        let P := s.fold (infiltration α) (infiltrationUnit α) (fun i => infiltrationPow α (fs i) (m i))
        let P' := s.fold (infiltration α) (infiltrationUnit α)
            (fun i => infiltrationPow α (fs i + rightDeriv α a (fs i)) (m i))
        let q := infiltrationPow α (fs x) (m x)
        let q' := infiltrationPow α (fs x + rightDeriv α a (fs x)) (m x)
        -- The augmented factor is `q + rightDeriv a q` (power rule); the augmented
        -- partial product is `P + rightDeriv a P` (induction hypothesis).
        have hpow := infiltrationPow_rightDeriv (fs x) (m x) a
        have hqaug : q + rightDeriv α a q = q' := by
          rw [hpow]
          ring
        have hPaug : P + rightDeriv α a P = P' := by
          rw [ih]
          ring
        -- Two-factor rule on `infiltration q P`; the augmented side is `infiltration q' P'`.
        have hprod := infiltrationRightDerivProd q P a
        simp [Finset.fold_insert hx]
        rw [hprod, hqaug, hPaug]
  simp only [infiltrationProd_eq_fold]
  exact hfold (Finset.univ : Finset (Fin k))

/-! ### Right derivative of the evaluation (semantic level) -/

/-- The right derivative is `ℚ`-linear (additive). -/
private theorem rightDeriv_add (a : α) (f g : Series α) :
    rightDeriv α a (f + g) = rightDeriv α a f + rightDeriv α a g := by
  funext w; dsimp [rightDeriv]

/-- The right derivative is `ℚ`-linear (scalar multiplication). -/
private theorem rightDeriv_smul (a : α) (c : ℚ) (f : Series α) :
    rightDeriv α a (c • f) = c • rightDeriv α a f := by
  funext w; dsimp [rightDeriv]

/-- The right derivative of the zero series is zero. -/
private theorem rightDeriv_zero (a : α) : rightDeriv α a 0 = 0 := by
  funext w; dsimp [rightDeriv]

/-- The right derivative of the infiltration evaluation is the evaluation in the "augmented"
    tuple (each slot replaced by `fs i + rightDeriv a (fs i)`) minus the original evaluation:
    `rightDeriv a (infiltrationEval k fs p) =
    infiltrationEval k (fun i => fs i + rightDeriv a (fs i)) p − infiltrationEval k fs p`.
    Both sides equal `∑ m ∈ p.support, p.coeff m • rightDeriv a (infiltrationProd k fs m)`:
    the LHS by `ℚ`-linearity of the right derivative (the evaluation is a finite sum of scalar
    multiples of products), and the RHS by the product rule (`infiltrationProd_rightDeriv`). -/
private theorem infiltrationRightDerivEval (k : ℕ) (fs : Fin k → Series α) (a : α)
    (p : MvPolynomial (Fin k) ℚ) :
    rightDeriv α a (infiltrationEval α k fs p) =
      infiltrationEval α k (fun i => fs i + rightDeriv α a (fs i)) p - infiltrationEval α k fs p := by
  let fs' := fun i : Fin k => fs i + rightDeriv α a (fs i)
  have hLHS : rightDeriv α a (infiltrationEval α k fs p) =
      ∑ m ∈ p.support, p.coeff m • rightDeriv α a (infiltrationProd α k fs m) := by
    have hsum : rightDeriv α a (infiltrationEval α k fs p) =
        rightDeriv α a (p.support.sum fun m => p.coeff m • infiltrationProd α k fs m) := by
      rw [infiltrationEval]
    rw [hsum]
    have hsum2 : rightDeriv α a (p.support.sum fun m => p.coeff m • infiltrationProd α k fs m) =
        ∑ m ∈ p.support, p.coeff m • rightDeriv α a (infiltrationProd α k fs m) := by
      have : ∀ (t : Finset (Fin k →₀ ℕ)) (g : (Fin k →₀ ℕ) → Series α),
          rightDeriv α a (∑ j ∈ t, g j) = ∑ j ∈ t, rightDeriv α a (g j) := by
        intro t g
        induction t using Finset.induction_on with
        | empty => simp [rightDeriv_zero]
        | insert x t hx ih' =>
            simp [Finset.sum_insert hx, ih', rightDeriv_add a]
      have hlin := this p.support (fun m => p.coeff m • infiltrationProd α k fs m)
      rw [hlin]
      apply Finset.sum_congr rfl
      intro m _
      rw [rightDeriv_smul a]
    rw [hsum2]
  have hRHS : infiltrationEval α k fs' p - infiltrationEval α k fs p =
      ∑ m ∈ p.support, p.coeff m • rightDeriv α a (infiltrationProd α k fs m) := by
    rw [infiltrationEval, infiltrationEval]
    have hsumsub : (∑ m ∈ p.support, p.coeff m • infiltrationProd α k fs' m) -
        (∑ m ∈ p.support, p.coeff m • infiltrationProd α k fs m) =
        ∑ m ∈ p.support,
          (p.coeff m • infiltrationProd α k fs' m - p.coeff m • infiltrationProd α k fs m) := by
      induction p.support using Finset.induction_on with
      | empty => simp
      | insert x s hx ih =>
          rw [Finset.sum_insert hx, Finset.sum_insert hx, Finset.sum_insert hx]
          rw [ih.symm]
          abel
    rw [hsumsub]
    apply Finset.sum_congr rfl
    intro m _
    rw [← smul_sub, (infiltrationProd_rightDeriv k fs m a).symm]
  rw [hLHS, hRHS]

/-- The polynomial whose infiltration-evaluation in the extended tuple
    `combineTuple k k fs (fun i => fs i + rightDeriv a (fs i))` is the right derivative of
    `infiltrationEval α k fs p`: `embedBack k k p − embedFront k k p`.  The back embedding
    evaluates in the augmented tuple (giving the "augmented" evaluation), and the front
    embedding evaluates in the original tuple; their difference is the right derivative. -/
noncomputable def infiltrationRightDerivPoly (k : ℕ) (fs : Fin k → Series α) (a : α)
    (p : MvPolynomial (Fin k) ℚ) : MvPolynomial (Fin (k + k)) ℚ :=
  embedBack k k p - embedFront k k p

/-- The right derivative of the infiltration evaluation is an infiltration evaluation in the
    extended tuple `combineTuple k k fs (fun i => fs i + rightDeriv a (fs i))`:
    `rightDeriv a (infiltrationEval k fs p) =
    infiltrationEval (k + k) (combineTuple k k fs (fun i => fs i + rightDeriv a (fs i)))
    (infiltrationRightDerivPoly k fs a p)`.  Follows from `infiltrationRightDerivEval` and the
    front/back embedding lemmas. -/
private theorem infiltrationRightDerivEval_ext (k : ℕ) (fs : Fin k → Series α) (a : α)
    (p : MvPolynomial (Fin k) ℚ) :
    rightDeriv α a (infiltrationEval α k fs p) =
      infiltrationEval α (k + k) (combineTuple k k fs (fun i => fs i + rightDeriv α a (fs i)))
          (infiltrationRightDerivPoly k fs a p) := by
  let fs' := fun i : Fin k => fs i + rightDeriv α a (fs i)
  have h := infiltrationRightDerivEval k fs a p
  rw [h]
  have h1 : infiltrationEval α k fs' p =
      infiltrationEval α (k + k) (combineTuple k k fs fs') (embedBack k k p) :=
    infiltrationEval_embedBack k k fs fs' p
  have h2 : infiltrationEval α k fs p =
      infiltrationEval α (k + k) (combineTuple k k fs fs') (embedFront k k p) :=
    infiltrationEval_embedFront k k fs fs' p
  rw [h1, h2]
  dsimp [infiltrationRightDerivPoly]
  exact (infiltrationEval_sub (k + k) (combineTuple k k fs fs') (embedBack k k p) (embedFront k k p)).symm

/-- The "augmented" concatenated tuple `combineTuple k k fs (fun i => fs i + rightDeriv a (fs i))`
    is closed under left derivatives, given that `fs` is: a front slot's left derivative is the
    embedded left derivative of the corresponding `fs` slot; a back slot `fs j + rightDeriv a (fs j)`
    differentiates to `leftDeriv a' (fs j) + rightDeriv a (leftDeriv a' (fs j))` (the left/right
    commutation), which reduces to the back-embedded left derivative. -/
private theorem combineTuple_add_rightDeriv_closed (k : ℕ) (fs : Fin k → Series α) (a : α)
    (hfc : ∀ a (i : Fin k), ∃ q, leftDeriv α a (fs i) = infiltrationEval α k fs q) :
    ∀ a' (i : Fin (k + k)), ∃ q,
      leftDeriv α a' (combineTuple k k fs (fun i => fs i + rightDeriv α a (fs i)) i) =
        infiltrationEval α (k + k) (combineTuple k k fs (fun i => fs i + rightDeriv α a (fs i))) q := by
  let fs' := fun i : Fin k => fs i + rightDeriv α a (fs i)
  intro a' i
  by_cases hlt : i.val < k
  · let j : Fin k := ⟨i.val, hlt⟩
    obtain ⟨q, hq⟩ := hfc a' j
    refine ⟨embedFront k k q, ?_⟩
    have hci : combineTuple k k fs fs' i = fs j := by
      simp [combineTuple, j, hlt]
    rw [hci, hq, infiltrationEval_embedFront k k fs fs' q]
  · let j : Fin k := ⟨i.val - k, by omega⟩
    obtain ⟨q, hq⟩ := hfc a' j
    refine ⟨embedBack k k q, ?_⟩
    have hci : combineTuple k k fs fs' i = fs j + rightDeriv α a (fs j) := by
      simp [combineTuple, fs', j, hlt]
    rw [hci]
    have hadd : leftDeriv α a' (fs j + rightDeriv α a (fs j)) =
        leftDeriv α a' (fs j) + leftDeriv α a' (rightDeriv α a (fs j)) := by
      exact leftDeriv_add a' (fs j) (rightDeriv α a (fs j))
    rw [hadd]
    have hcomm : leftDeriv α a' (rightDeriv α a (fs j)) = rightDeriv α a (leftDeriv α a' (fs j)) :=
      leftDeriv_rightDeriv_commute (fs j) a' a
    simp [hcomm, hq]
    have hrd := infiltrationRightDerivEval k fs a q
    rw [hrd]
    abel
    rw [← infiltrationEval_embedBack k k fs fs' q]

/-! ### The closure theorem -/

/--
---
conclusion: Lax946791.Infiltration.InfiltrationClosure
---
The infiltration closure theorem (paper §7): the infiltration-finite series are closed
under addition, scalar multiplication, the infiltration product, and right derivatives.
Addition, scalar multiplication, and the infiltration product follow by concatenating the
witnessing tuples (the infiltration algebra is not the pointwise ring, so the evaluation is
an infiltration-algebra homomorphism; the tuple is extended and the polynomial embedded at
the front or back, and the closure under left derivatives is preserved by the concatenation).
The right derivative is handled at the semantic level: the letter endomorphism `S_a = id + Δ_a`
is `ℚ`-linear but not a ring homomorphism, so the right derivative cannot be read off an
automaton with the same transitions (unlike the Hadamard case); instead the witnessing tuple is
extended to the "augmented" tuple `(fs, fun i => fs i + rightDeriv a (fs i))`, and the right
derivative of the evaluation is the evaluation of `embedBack p − embedFront p` in the extended
tuple.  The class is stated in terms of the semantic definition `IsInfiltrationFinite`; the proof
proceeds at the semantic level, working directly with the witnessing tuples.
-/
theorem InfiltrationClosure :
    (∀ (f g : Series α), IsInfiltrationFinite α f → IsInfiltrationFinite α g → IsInfiltrationFinite α (f + g)) ∧
    (∀ (c : ℚ) (f : Series α), IsInfiltrationFinite α f → IsInfiltrationFinite α (c • f)) ∧
    (∀ (f g : Series α), IsInfiltrationFinite α f → IsInfiltrationFinite α g → IsInfiltrationFinite α (infiltration α f g)) ∧
    (∀ (a : α) (f : Series α), IsInfiltrationFinite α f → IsInfiltrationFinite α (rightDeriv α a f)) := by
  constructor
  · -- Addition
    intro f g hf hg
    obtain ⟨k, fs, p, hfp, hfc⟩ := hf
    obtain ⟨k', fs', p', hgp', hfc'⟩ := hg
    have hsum : IsInfiltrationFinite α (f + g) :=
      ⟨k + k', combineTuple k k' fs fs', embedFront k k' p + embedBack k k' p',
        by calc
          f + g = infiltrationEval α k fs p + infiltrationEval α k' fs' p' := by rw [← hfp, ← hgp']
          _ = infiltrationEval α (k + k') (combineTuple k k' fs fs') (embedFront k k' p) +
              infiltrationEval α k' fs' p' := by
            rw [infiltrationEval_embedFront k k' fs fs' p]
          _ = infiltrationEval α (k + k') (combineTuple k k' fs fs') (embedFront k k' p) +
              infiltrationEval α (k + k') (combineTuple k k' fs fs') (embedBack k k' p') := by
            rw [infiltrationEval_embedBack k k' fs fs' p']
          _ = infiltrationEval α (k + k') (combineTuple k k' fs fs')
              (embedFront k k' p + embedBack k k' p') := by
            rw [← infiltrationEval_add]
        , combineTuple_closed k k' fs fs' hfc hfc'⟩
    exact hsum
  · constructor
    · -- Scalar multiplication
      intro c f hf
      obtain ⟨k, fs, p, hfp, hfc⟩ := hf
      have hsmul : IsInfiltrationFinite α (c • f) :=
        ⟨k, fs, c • p,
          by calc
            c • f = c • infiltrationEval α k fs p := by rw [← hfp]
            _ = infiltrationEval α k fs (c • p) := by rw [← infiltrationEval_smul]
          , hfc⟩
      exact hsmul
    · constructor
      · -- Infiltration product
        intro f g hf hg
        obtain ⟨k, fs, p, hfp, hfc⟩ := hf
        obtain ⟨k', fs', p', hgp', hfc'⟩ := hg
        have hmul : IsInfiltrationFinite α (infiltration α f g) :=
          ⟨k + k', combineTuple k k' fs fs', embedFront k k' p * embedBack k k' p',
            by calc
              infiltration α f g =
                  infiltration α (infiltrationEval α k fs p) (infiltrationEval α k' fs' p') := by
                rw [← hfp, ← hgp']
              _ = infiltration α
                  (infiltrationEval α (k + k') (combineTuple k k' fs fs') (embedFront k k' p))
                  (infiltrationEval α k' fs' p') := by
                rw [infiltrationEval_embedFront k k' fs fs' p]
              _ = infiltration α
                  (infiltrationEval α (k + k') (combineTuple k k' fs fs') (embedFront k k' p))
                  (infiltrationEval α (k + k') (combineTuple k k' fs fs') (embedBack k k' p')) := by
                rw [infiltrationEval_embedBack k k' fs fs' p']
              _ = infiltrationEval α (k + k') (combineTuple k k' fs fs')
                  (embedFront k k' p * embedBack k k' p') := by
                rw [← infiltrationEval_mul]
            , combineTuple_closed k k' fs fs' hfc hfc'⟩
        exact hmul
      · -- Right derivative (semantic level, via the extended "augmented" tuple)
        intro a f hf
        obtain ⟨k, fs, p, hfp, hfc⟩ := hf
        let fs' := fun i : Fin k => fs i + rightDeriv α a (fs i)
        let FS := combineTuple k k fs fs'
        have hrd : IsInfiltrationFinite α (rightDeriv α a f) :=
          ⟨k + k, FS, infiltrationRightDerivPoly k fs a p,
            by calc
              rightDeriv α a f = rightDeriv α a (infiltrationEval α k fs p) := by rw [← hfp]
              _ = infiltrationEval α (k + k) FS (infiltrationRightDerivPoly k fs a p) := by
                rw [infiltrationRightDerivEval_ext k fs a p]
            , combineTuple_add_rightDeriv_closed k fs a hfc⟩
        exact hrd

/-! ### The ideal chain: orbit ideals and their stabilisation -/

/-- The initial configuration `X_0` (the first nonterminal). -/
private noncomputable def X0 (A : InfiltrationAutomaton α) : MvPolynomial (Fin A.dim) ℚ :=
  X (Fin.mk 0 A.hdim)

/-- The *cumulative orbit*: the configurations reachable from `X_0` by words of length `≤ n`.
    `orbitSet A 0 = {X_0}` and `orbitSet A (n+1) = orbitSet A n ∪ ⋃ₐ Δₐ(orbitSet A n)`
    (append one letter to every reachable configuration).  Finite because the alphabet is.
    (Unlike the Hadamard case (a ring hom) and the shuffle case (a derivation), the letter
    map here is the *infiltration* `infiltrationExt A a`.) -/
noncomputable def orbitSet (A : InfiltrationAutomaton α) [Fintype α] :
    ℕ → Finset (MvPolynomial (Fin A.dim) ℚ)
  | 0 => {X0 A}
  | n + 1 => orbitSet A n ∪ Finset.biUnion Finset.univ
      (fun a => (orbitSet A n).image (infiltrationExt A a))

/-- The *orbit ideal* `I_n`: the ideal generated by the configurations reachable from `X_0`
    by words of length `≤ n`. -/
noncomputable def orbitIdeal (A : InfiltrationAutomaton α) [Fintype α] (n : ℕ) :
    Ideal (MvPolynomial (Fin A.dim) ℚ) :=
  Ideal.span (orbitSet A n)

/-- The orbit is cumulative: `orbitSet A n ⊆ orbitSet A (n+1)`. -/
private theorem orbitSet_mono (A : InfiltrationAutomaton α) [Fintype α] (n : ℕ) :
    orbitSet A n ⊆ orbitSet A (n+1) := by
  dsimp [orbitSet]
  exact Finset.subset_union_left

/-- Appending a letter stays within the next orbit level:
    `Δₐ(orbitSet A n) ⊆ orbitSet A (n+1)`. -/
private theorem orbitSet_image (A : InfiltrationAutomaton α) [Fintype α] (a : α) (n : ℕ) :
    (orbitSet A n).image (infiltrationExt A a) ⊆ orbitSet A (n+1) := by
  dsimp [orbitSet]
  intro x hx
  apply Finset.mem_union_right
  rw [Finset.mem_biUnion]
  exact ⟨a, Finset.mem_univ a, hx⟩

/-- The orbit ideals form an ascending chain: `I_n ≤ I_{n+1}`. -/
private theorem orbitIdeal_mono (A : InfiltrationAutomaton α) [Fintype α] (n : ℕ) :
    orbitIdeal A n ≤ orbitIdeal A (n+1) := by
  rw [orbitIdeal, orbitIdeal]
  exact Ideal.span_mono (orbitSet_mono A n)

/-- The letter infiltration `infiltrationExt A a` is `ℚ`-linear, hence commutes with a
    finite sum. -/
private theorem infiltrationExt_finset_sum (A : InfiltrationAutomaton α) (a : α)
    (s : Finset (MvPolynomial (Fin A.dim) ℚ))
    (g : MvPolynomial (Fin A.dim) ℚ → MvPolynomial (Fin A.dim) ℚ) :
    infiltrationExt A a (∑ i ∈ s, g i) = ∑ i ∈ s, infiltrationExt A a (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [infiltrationExt_zero A a]
  | insert x s ha ih =>
      rw [Finset.sum_insert ha, infiltrationExt_add A a, ih, Finset.sum_insert ha]

set_option maxHeartbeats 0

/-- The transition invariance: applying a letter infiltration to a configuration in the
    depth-`≤ n` orbit ideal lands in the depth-`≤ (n+1)` orbit ideal, `Δₐ(I_n) ⊆ I_{n+1}`.
    Unlike the Hadamard case (a ring hom, so `Ideal.map_span`) and the shuffle case (a
    derivation, so the Leibniz rule), the infiltration letter map is `ℚ`-linear but neither
    a ring hom nor a derivation.  So decompose `p` as a finite `R`-linear combination of
    orbit-set elements (`Submodule.mem_span_finset`), apply the infiltration product rule
    `Δₐ(p·q) = Δₐ p·q + Sₐ p·Δₐ q` termwise, and note that the two resulting sums lie in
    `I_n` and in the ideal generated by the infiltrated orbit set, both contained in
    `I_{n+1}`. -/
private theorem orbitIdeal_image (A : InfiltrationAutomaton α) [Fintype α] (a : α) (n : ℕ)
    (p : MvPolynomial (Fin A.dim) ℚ) (hp : p ∈ orbitIdeal A n) :
    infiltrationExt A a p ∈ orbitIdeal A (n+1) := by
  let R := MvPolynomial (Fin A.dim) ℚ
  have hp' : p ∈ Submodule.span R (orbitSet A n) := by
    simpa [orbitIdeal] using hp
  obtain ⟨f, _, hf_sum⟩ := Submodule.mem_span_finset.mp hp'
  have hf_sum' : p = ∑ z ∈ orbitSet A n, f z * z := by
    have hre : p = ∑ z ∈ orbitSet A n, f z • z := by
      rw [← hf_sum]
    rw [hre]
    simp [smul_eq_mul]
  have hsum : infiltrationExt A a p =
      ∑ z ∈ orbitSet A n, infiltrationExt A a (f z * z) := by
    rw [hf_sum', infiltrationExt_finset_sum A a (orbitSet A n) (fun z => f z * z)]
  have hrule : ∀ z, infiltrationExt A a (f z * z) =
      infiltrationExt A a (f z) * z + S_map A a (f z) * infiltrationExt A a z := by
    intro z
    rw [infiltrationExt_mul A a (f z) z]
  have hsplit : infiltrationExt A a p =
      (∑ z ∈ orbitSet A n, infiltrationExt A a (f z) * z) +
      (∑ z ∈ orbitSet A n, S_map A a (f z) * infiltrationExt A a z) := by
    calc
      infiltrationExt A a p = ∑ z ∈ orbitSet A n, infiltrationExt A a (f z * z) := hsum
      _ = ∑ z ∈ orbitSet A n,
          (infiltrationExt A a (f z) * z + S_map A a (f z) * infiltrationExt A a z) := by
        simp [hrule]
      _ = (∑ z ∈ orbitSet A n, infiltrationExt A a (f z) * z) +
          (∑ z ∈ orbitSet A n, S_map A a (f z) * infiltrationExt A a z) :=
        Finset.sum_add_distrib
  have h1 : (∑ z ∈ orbitSet A n, infiltrationExt A a (f z) * z) ∈ orbitIdeal A n := by
    apply Submodule.sum_mem
    intro z hz
    have hz' : z ∈ ↑(Ideal.span ↑(orbitSet A n)) := Ideal.subset_span (Finset.mem_coe.mpr hz)
    exact Ideal.mul_mem_left (Ideal.span ↑(orbitSet A n)) (infiltrationExt A a (f z)) hz'
  have h2 : (∑ z ∈ orbitSet A n, S_map A a (f z) * infiltrationExt A a z) ∈
      Ideal.span (infiltrationExt A a '' ↑(orbitSet A n)) := by
    apply Submodule.sum_mem
    intro z hz
    have himg : infiltrationExt A a z ∈ infiltrationExt A a '' ↑(orbitSet A n) :=
      Set.mem_image_of_mem (infiltrationExt A a) (Finset.mem_coe.mpr hz)
    have hspan : infiltrationExt A a z ∈
        ↑(Ideal.span (infiltrationExt A a '' ↑(orbitSet A n))) := Ideal.subset_span himg
    exact Ideal.mul_mem_left (Ideal.span (infiltrationExt A a '' ↑(orbitSet A n))) (S_map A a (f z)) hspan
  have hnext1 : orbitIdeal A n ≤ orbitIdeal A (n+1) := orbitIdeal_mono A n
  have hnext2 : Ideal.span (infiltrationExt A a '' ↑(orbitSet A n)) ≤ orbitIdeal A (n+1) := by
    rw [orbitIdeal]
    apply Ideal.span_mono
    rw [← Finset.coe_image]
    exact orbitSet_image A a n
  rw [hsplit]
  exact (orbitIdeal A (n+1)).add_mem (mem_of_le_of_mem hnext1 h1)
      (mem_of_le_of_mem hnext2 h2)

/-! ### The kernel of the final-weight functional -/

/-- The final-weight functional as a `ℚ`-algebra homomorphism:
    `F_hom A p = aeval (A.F) p = eval (A.F) p`, the evaluation of the configuration
    `p` at the point `(A.F 0, …, A.F (dim-1))`.  (Unchanged from the Hadamard case:
    the final-weight evaluation is a point evaluation, independent of the automaton class.) -/
noncomputable def F_hom (A : InfiltrationAutomaton α) :
    MvPolynomial (Fin A.dim) ℚ →ₐ[ℚ] ℚ :=
  aeval (A.F)

/-- The kernel of the final-weight functional: the ideal of configurations that
    evaluate to `0` under `F`. -/
noncomputable def K (A : InfiltrationAutomaton α) : Ideal (MvPolynomial (Fin A.dim) ℚ) :=
  RingHom.ker (F_hom A)

/-- A configuration lies in the kernel iff it evaluates to `0`:
    `p ∈ K A ↔ eval (A.F) p = 0`. -/
private theorem kerMem_eval (A : InfiltrationAutomaton α) (p : MvPolynomial (Fin A.dim) ℚ) :
    p ∈ K A ↔ eval (A.F) p = 0 := by
  rw [K, F_hom, RingHom.mem_ker]
  simp [aeval_eq_eval]

/-! ### Stabilisation of the orbit-ideal chain (Hilbert's basis theorem) -/

/-- The configuration ring is Noetherian: a polynomial ring over a Noetherian ring in
    finitely many variables is Noetherian (`isNoetherianRing_fin`), and `ℚ` is a field,
    hence Noetherian. -/
private theorem noetherian (A : InfiltrationAutomaton α) :
    IsNoetherianRing (MvPolynomial (Fin A.dim) ℚ) :=
  isNoetherianRing_fin

/-- The orbit ideals form a monotone (ascending) chain. -/
private theorem orbitIdeal_monotone (A : InfiltrationAutomaton α) [Fintype α] :
    Monotone (fun n => orbitIdeal A n) := by
  intro a b hab
  exact Nat.le_induction (le_rfl) (fun n _ hn => le_trans hn (orbitIdeal_mono A n)) b hab

/-- The orbit-ideal chain stabilises (Noetherianity): there is an `N` such that
    `I_N = I_m` for all `m ≥ N`. -/
private theorem orbitIdeal_stabilises (A : InfiltrationAutomaton α) [Fintype α] :
    ∃ N, ∀ m, N ≤ m → orbitIdeal A N = orbitIdeal A m := by
  let R := MvPolynomial (Fin A.dim) ℚ
  obtain ⟨N, hN⟩ :=
    monotone_stabilizes_iff_noetherian.mpr (isNoetherianRing_iff.mp (noetherian A))
      (⟨fun n => orbitIdeal A n, orbitIdeal_monotone A⟩)
  exact ⟨N, fun m hm => hN m hm⟩

/-- A stabilisation point of the orbit-ideal chain. -/
noncomputable def orbitIdeal_stab (A : InfiltrationAutomaton α) [Fintype α] : ℕ :=
  Classical.choose (orbitIdeal_stabilises A)

/-- At the stabilisation point the chain is constant: `I_N = I_m` for all `m ≥ N`. -/
private theorem orbitIdeal_stab_spec (A : InfiltrationAutomaton α) [Fintype α] :
    ∀ m, orbitIdeal_stab A ≤ m → orbitIdeal A (orbitIdeal_stab A) = orbitIdeal A m :=
  Classical.choose_spec (orbitIdeal_stabilises A)

/-! ### The stabilised orbit ideal is a bi-ideal -/

/-- The initial configuration lies in the orbit ideal at every level. -/
private theorem X0_in_orbitSet (A : InfiltrationAutomaton α) [Fintype α] (n : ℕ) :
    X0 A ∈ orbitSet A n := by
  induction n with
  | zero =>
      dsimp [orbitSet]
      simp
  | succ n ih =>
      dsimp [orbitSet]
      exact Finset.mem_union_left _ ih

/-- The initial configuration lies in the stabilised orbit ideal. -/
private theorem X0_in_orbitIdeal (A : InfiltrationAutomaton α) [Fintype α] :
    X0 A ∈ orbitIdeal A (orbitIdeal_stab A) := by
  rw [orbitIdeal]
  have h : X0 A ∈ ↑(orbitSet A (orbitIdeal_stab A)) := by
    simpa using X0_in_orbitSet A (orbitIdeal_stab A)
  exact Submodule.subset_span h

/-- The stabilised orbit ideal is invariant under every letter infiltration
    (`Δₐ(I_N) ⊆ I_N`): the image lands one level up (`orbitIdeal_image`), which
    equals `I_N` at the stabilisation point. -/
private theorem orbitIdeal_stab_invariant (A : InfiltrationAutomaton α) [Fintype α]
    (a : α) (p : MvPolynomial (Fin A.dim) ℚ) (hp : p ∈ orbitIdeal A (orbitIdeal_stab A)) :
    infiltrationExt A a p ∈ orbitIdeal A (orbitIdeal_stab A) := by
  have h1 : infiltrationExt A a p ∈ orbitIdeal A (orbitIdeal_stab A + 1) :=
    orbitIdeal_image A a (orbitIdeal_stab A) p hp
  have h2 : orbitIdeal A (orbitIdeal_stab A + 1) = orbitIdeal A (orbitIdeal_stab A) :=
    (orbitIdeal_stab_spec A (orbitIdeal_stab A + 1) (Nat.le_succ (orbitIdeal_stab A))).symm
  rw [← h2]
  exact h1

/-- `Mword [a] = infiltrationExt A a`: a single letter applies its infiltration. -/
private theorem Mword_singleton (A : InfiltrationAutomaton α) (a : α) :
    A.Mword [a] = infiltrationExt A a := by
  rw [Mword_cons, Mword_nil]
  simp

/-- The word endomorphism preserves the stabilised orbit ideal: if `p` is in the
    ideal, so is `Δ_w p`.  Each letter infiltration preserves the ideal
    (`orbitIdeal_stab_invariant`), and the word map composes them. -/
private theorem Mword_preserves_orbitIdeal (A : InfiltrationAutomaton α) [Fintype α] (w : List α) :
    ∀ p, p ∈ orbitIdeal A (orbitIdeal_stab A) → A.Mword w p ∈ orbitIdeal A (orbitIdeal_stab A) := by
  induction w with
  | nil =>
      intro p hp
      rw [Mword_nil]
      exact hp
  | cons a w ih =>
      intro p hp
      rw [Mword_cons, Function.comp_apply]
      have h1 : infiltrationExt A a p ∈ orbitIdeal A (orbitIdeal_stab A) :=
        orbitIdeal_stab_invariant A a p hp
      exact ih (infiltrationExt A a p) h1

/-- Every reachable configuration lies in the stabilised orbit ideal: the word map
    preserves the ideal and `X_0` is in it. -/
private theorem Mword_mem_orbitIdeal (A : InfiltrationAutomaton α) [Fintype α] (w : List α) :
    A.Mword w (X0 A) ∈ orbitIdeal A (orbitIdeal_stab A) :=
  Mword_preserves_orbitIdeal A w (X0 A) (X0_in_orbitIdeal A)

/-! ### The orbit set is reachable, and the zeroness characterisation -/

/-- Every configuration in the depth-`≤ n` orbit set is reachable from `X_0` by some
    word: `p ∈ orbitSet A n → ∃ w, p = Δ_w X_0`. -/
private theorem orbitSet_reachable (A : InfiltrationAutomaton α) [Fintype α] (n : ℕ) :
    ∀ p, p ∈ orbitSet A n → ∃ w : List α, p = A.Mword w (X0 A) := by
  induction n with
  | zero =>
      intro p hp
      dsimp [orbitSet] at hp
      have hp' : p = X0 A := by simpa using hp
      exact ⟨[], by rw [hp', Mword_nil]; rfl⟩
  | succ n ih =>
      intro p hp
      dsimp [orbitSet] at hp
      rw [Finset.mem_union] at hp
      rcases hp with hleft | hright
      · obtain ⟨w, hw⟩ := ih p hleft
        exact ⟨w, hw⟩
      · simp only [Finset.mem_biUnion] at hright
        obtain ⟨a, _, himg⟩ := hright
        simp only [Finset.mem_image] at himg
        obtain ⟨q, hq, hqimg⟩ := himg
        obtain ⟨w, hw⟩ := ih q hq
        exact ⟨w ++ [a], by
          rw [← hqimg, hw, Mword_append, Mword_singleton, Function.comp_apply]⟩

/-- The recognised series is zero iff every reachable configuration lies in the kernel:
    `A.recognised = 0 ↔ ∀ w, Δ_w X_0 ∈ K A`.  The coefficient of `w` in the recognised
    series is `F(Δ_w X_0)`, which is `0` exactly when `Δ_w X_0` is in the kernel. -/
private theorem recognised_zero_iff_allInK (A : InfiltrationAutomaton α) :
    A.recognised = 0 ↔ ∀ w, A.Mword w (X0 A) ∈ K A := by
  constructor
  · intro h w
    have hw : A.recognised w = 0 := by
      rw [h]
      simp
    have hsem : A.recognised w = eval (A.F) (A.Mword w (X0 A)) := by
      simp [InfiltrationAutomaton.recognised, InfiltrationAutomaton.sem, X0]
    rw [hsem] at hw
    rw [kerMem_eval A (A.Mword w (X0 A))]
    exact hw
  · intro h
    funext w
    change eval (A.F) (A.Mword w (X0 A)) = 0
    rw [← kerMem_eval A (A.Mword w (X0 A))]
    exact h w

/-- The zeroness characterisation at the stabilisation point:
    `A.recognised = 0 ↔ ∀ p ∈ orbitSet A N, p ∈ K A`, where `N` is a stabilisation
    point.  (→) Every orbit-set configuration is reachable, hence in the kernel.
    (←) Every reachable configuration is in the stabilised orbit ideal (the bi-ideal
    property), which is contained in the kernel once the orbit-set configurations are. -/
private theorem zeroness_iff_orbitSet (A : InfiltrationAutomaton α) [Fintype α] :
    A.recognised = 0 ↔ ∀ p ∈ orbitSet A (orbitIdeal_stab A), p ∈ K A := by
  let N := orbitIdeal_stab A
  have hchar : A.recognised = 0 ↔ ∀ w, A.Mword w (X0 A) ∈ K A := recognised_zero_iff_allInK A
  constructor
  · intro h
    have hall := hchar.mp h
    intro p hp
    obtain ⟨w, hw⟩ := orbitSet_reachable A N p hp
    rw [hw]
    exact hall w
  · intro h
    apply hchar.mpr
    intro w
    have hmem : A.Mword w (X0 A) ∈ orbitIdeal A N := Mword_mem_orbitIdeal A w
    have hsub : orbitIdeal A N ≤ K A := by
      rw [orbitIdeal]
      exact Ideal.span_le.mpr h
    exact mem_of_le_of_mem hsub hmem

/-! ### The equality (zeroness) decision, reduced to the open leaf -/

/-- A finite generating set of the kernel `K A` (exists by Noetherianity). -/
noncomputable def gensKer (A : InfiltrationAutomaton α) : Finset (MvPolynomial (Fin A.dim) ℚ) :=
  letI _ : IsNoetherianRing (MvPolynomial (Fin A.dim) ℚ) := noetherian A
  Classical.choose (Ideal.fg_of_isNoetherianRing (K A))

/-- The kernel is exactly the ideal generated by `gensKer A`. -/
private theorem gensKer_spec (A : InfiltrationAutomaton α) :
    Ideal.span ↑(gensKer A) = K A := by
  letI _ : IsNoetherianRing (MvPolynomial (Fin A.dim) ℚ) := noetherian A
  exact Classical.choose_spec (Ideal.fg_of_isNoetherianRing (K A))

/-- A `Decidable` cast to a `Bool` that is `true` exactly when the proposition holds:
    the Boolean value `d.casesOn (· => false) (· => true)` is `true` iff `P`. -/
private theorem decBool_true {P : Prop} (d : Decidable P) :
    d.casesOn (fun _ => false) (fun _ => true) = true ↔ P := by
  cases d with
  | isTrue h =>
      simp
      exact h
  | isFalse h =>
      simp
      exact h

/-- A `Finset`-fold with `&&` (the Boolean "and") starting from `true` is `true`
    exactly when every element satisfies the predicate:
    `s.fold (· && ·) true p = true ↔ ∀ x ∈ s, p x = true`. -/
private theorem fold_and_true {β : Type*} (s : Finset β) (p : β → Bool) :
    s.fold (· && ·) true p = true ↔ ∀ x ∈ s, p x = true := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.fold_insert ha, Bool.and_eq_true_iff, ih]
      simp [Finset.mem_insert]

/-- The per-configuration decision: `orbitDec A p` is `true` exactly when `p` lies in
    the ideal generated by `gensKer A` — the open leaf `IdealMembershipDecidable`. -/
private noncomputable def orbitDec (A : InfiltrationAutomaton α) (p : MvPolynomial (Fin A.dim) ℚ) : Bool :=
  (IdealMembershipDecidable A.dim (gensKer A) p).casesOn (fun _ => false) (fun _ => true)

/-- `orbitDec A p = true ↔ p ∈ K A`: the leaf decides `p ∈ span ↑(gensKer A)`, which
    is exactly the kernel `K A` (`gensKer_spec`). -/
private theorem orbitDec_iff (A : InfiltrationAutomaton α) (p : MvPolynomial (Fin A.dim) ℚ) :
    orbitDec A p = true ↔ p ∈ K A := by
  dsimp [orbitDec]
  rw [decBool_true (IdealMembershipDecidable A.dim (gensKer A) p), ← gensKer_spec A]

/--
---
conclusion: Lax946791.Infiltration.InfiltrationEqualityDecidable
---
The equality (zeroness) problem is decidable for infiltration automata over a finite
alphabet (paper §7).  As in the Hadamard and shuffle cases, the orbit-ideal chain `I_n`
stabilises by Hilbert's basis theorem (`orbitIdeal_stabilises`), and the stabilised
ideal is a bi-ideal, so the zeroness of the recognised series is characterised by the
finite statement `∀ p ∈ orbitSet A N, p ∈ K A` (`zeroness_iff_orbitSet`).  The only
difference from the other two classes is the transition invariance
(`orbitIdeal_image`): the letter map is an *infiltration* `Δₐ = Sₐ − id` (ℚ-linear,
neither a ring hom nor a derivation), so instead of `Ideal.map_span` (Hadamard) or the
Leibniz rule (shuffle) one decomposes `p` as a finite `R`-linear combination of
orbit-set elements and applies the infiltration product rule
`Δₐ(p·q) = Δₐ p·q + Sₐ p·Δₐ q` termwise.  The kernel `K A` is finitely generated
(`gensKer`, by Noetherianity), so this finite statement is a batch of ideal-membership
queries `p ∈ span ↑(gensKer A)`, each decided by the open leaf
`IdealMembershipDecidable`; the decision `d` is the Boolean "and" of these queries over
the (finite) orbit set.
-/
theorem InfiltrationEqualityDecidable [Fintype α] :
    ∃ d : InfiltrationAutomaton α → Bool, ∀ A, d A = true ↔ A.recognised = 0 := by
  let d : InfiltrationAutomaton α → Bool := fun A =>
    (orbitSet A (orbitIdeal_stab A)).fold (· && ·) true (orbitDec A)
  refine ⟨d, ?_⟩
  intro A
  let N := orbitIdeal_stab A
  have hfor : d A = true ↔ ∀ p ∈ orbitSet A N, p ∈ K A := by
    dsimp [d]
    rw [fold_and_true]
    constructor
    · intro h p hp
      have this := h p hp
      rw [orbitDec_iff A p] at this
      exact this
    · intro h p hp
      have this := h p hp
      rw [orbitDec_iff A p]
      exact this
  have hzer : (∀ p ∈ orbitSet A N, p ∈ K A) ↔ A.recognised = 0 :=
    (zeroness_iff_orbitSet A).symm
  calc
    d A = true ↔ ∀ p ∈ orbitSet A N, p ∈ K A := hfor
    _ ↔ A.recognised = 0 := hzer

/-! ### The anti-derivative closure -/

/-- Lifting a polynomial from a sub-index-set along a general index map `assign`:
    `liftPoly k k' assign p` is the polynomial in `Fin k` obtained by substituting
    `X_i ↦ X_{assign i}`.  (The generalisation of `embedFront`/`embedBack` to an arbitrary
    index map; used to express an infiltration polynomial in a sub-tuple as one in a larger
    tuple.) -/
noncomputable def liftPoly (k k' : ℕ) (assign : Fin k' → Fin k) (p : MvPolynomial (Fin k') ℚ) :
    MvPolynomial (Fin k) ℚ :=
  aeval (fun i : Fin k' => MvPolynomial.X (assign i)) p

/-- An infiltration polynomial in a sub-tuple `fs` is unchanged when the tuple is extended to
    `FS` (with `FS (assign i) = fs i`) and the polynomial is lifted by `assign`:
    `infiltrationEval α k' fs p = infiltrationEval α k FS (liftPoly k k' assign p)`.  Both sides
    are infiltration-algebra homomorphisms sending `X_i` to `fs i`, so they coincide by
    `infiltrationHom_ext`.  (The infiltration analogue of the Hadamard `aeval`-based lifting:
    `infiltrationEval` is an infiltration-algebra hom, not a pointwise `aeval`, so the equality
    is established by the homomorphism-extension lemma.) -/
private theorem infiltrationEval_lift (k k' : ℕ) (FS : Fin k → Series α) (fs : Fin k' → Series α)
    (assign : Fin k' → Fin k) (hassign : ∀ i, FS (assign i) = fs i)
    (p : MvPolynomial (Fin k') ℚ) :
    infiltrationEval α k' fs p = infiltrationEval α k FS (liftPoly k k' assign p) := by
  let aev : MvPolynomial (Fin k') ℚ →ₐ[ℚ] MvPolynomial (Fin k) ℚ :=
    MvPolynomial.aeval (fun i : Fin k' => MvPolynomial.X (assign i))
  have hadd2 : ∀ p q, infiltrationEval α k FS (liftPoly k k' assign (p + q)) =
      infiltrationEval α k FS (liftPoly k k' assign p) + infiltrationEval α k FS (liftPoly k k' assign q) := by
    intro p q
    rw [liftPoly, liftPoly, liftPoly]
    rw [map_add aev p q, infiltrationEval_add]
  have hsmul2 : ∀ (c : ℚ) p, infiltrationEval α k FS (liftPoly k k' assign (c • p)) =
      c • infiltrationEval α k FS (liftPoly k k' assign p) := by
    intro c p
    rw [liftPoly, liftPoly]
    rw [map_smul aev c p, infiltrationEval_smul]
  have hmul2 : ∀ p q, infiltrationEval α k FS (liftPoly k k' assign (p * q)) =
      infiltration α (infiltrationEval α k FS (liftPoly k k' assign p))
        (infiltrationEval α k FS (liftPoly k k' assign q)) := by
    intro p q
    rw [liftPoly, liftPoly, liftPoly]
    rw [map_mul aev p q, infiltrationEval_mul]
  have hone : infiltrationEval α k' fs 1 = infiltrationEval α k FS (liftPoly k k' assign 1) := by
    rw [infiltrationEval_one, liftPoly, map_one aev, infiltrationEval_one]
  have hgen : ∀ i, infiltrationEval α k' fs (MvPolynomial.X i) =
      infiltrationEval α k FS (liftPoly k k' assign (MvPolynomial.X i)) := by
    intro i
    rw [infiltrationEval_X, liftPoly, MvPolynomial.aeval_X, infiltrationEval_X]
    rw [hassign i]
  exact infiltrationHom_ext k'
    (fun p => infiltrationEval α k' fs p)
    (fun p => infiltrationEval α k FS (liftPoly k k' assign p))
    (infiltrationEval_add k' fs) hadd2
    (infiltrationEval_smul k' fs) hsmul2
    (infiltrationEval_mul k' fs) hmul2
    hone hgen p

/-- A package of the witnessing data for an infiltration-finite (semantic) series: the dimension
    `k`, the generator tuple `fs`, the polynomial `p`, and the proofs that
    `f = infiltrationEval k fs p` and that `fs` is closed under left derivatives.  Packaged as a
    `Type` (not a `Prop`) so that `Classical.choose` can produce one witness per letter from a
    `∀ a, IsInfiltrationFinite …`. -/
structure InfiltrationWitnessData (α : Type*) (f : Series α) where
  k : ℕ
  fs : Fin k → Series α
  p : MvPolynomial (Fin k) ℚ
  hfin : f = infiltrationEval α k fs p
  hclose : ∀ a i, ∃ q, leftDeriv α a (fs i) = infiltrationEval α k fs q

/-- `IsInfiltrationFinite α f` is the same as the existence of an `InfiltrationWitnessData`. -/
private theorem InfiltrationWitnessData_iff (f : Series α) :
    IsInfiltrationFinite α f ↔ ∃ _ : InfiltrationWitnessData α f, True := by
  constructor
  · intro h
    obtain ⟨k, fs, p, hfp, hfc⟩ := h
    exact ⟨⟨k, fs, p, hfp, hfc⟩, by trivial⟩
  · intro h
    obtain ⟨⟨k, fs, p, hfp, hfc⟩, -⟩ := h
    exact ⟨k, fs, p, hfp, hfc⟩

/--
---
conclusion: Lax946791.Infiltration.InfiltrationAntiDerivativeClosure
---
The infiltration anti-derivative closure (paper §7): over a finite alphabet, if `g` is a left
anti-derivative of a tuple `f` of infiltration-finite series (`leftDeriv a g = f a` for all
`a`), then `g` is infiltration-finite.  The witnessing tuple for `g` is `g` itself followed by
the concatenation of the witnessing tuples of the `f a`'s: `g` is trivially an infiltration
polynomial in a tuple containing it (its own variable), and the tuple is closed under left
derivatives because `leftDeriv a g = f a` is an infiltration polynomial in the (closed)
witnessing tuple for `f a`, and each `f a`'s witnessing tuple is itself closed.  The finiteness
of the alphabet is what makes the combined tuple finite.  The proof proceeds entirely at the
semantic level (infiltration polynomials in a tuple closed under left derivatives).
-/
theorem InfiltrationAntiDerivativeClosure [Fintype α]
    (g : Series α) (f : α → Series α) (hantideriv : IsLeftAntiDerivative α g f)
    (hf : ∀ a, IsInfiltrationFinite α (f a)) : IsInfiltrationFinite α g := by
  have hsem_g : IsInfiltrationFinite α g := by
    let W : (a : α) → InfiltrationWitnessData α (f a) :=
      fun a => Classical.choose ((InfiltrationWitnessData_iff (f a)).mp (hf a))
    -- The non-`g` slots: one per element of each `W a .fs`, indexed by the pair `(a, j)`.
    let nonGslots : Finset (α × ℕ) :=
      Finset.biUnion Finset.univ (fun a => (Finset.range ((W a).k)).image (fun j => (a, j)))
    let M : ℕ := nonGslots.card
    let e : Fin M ≃ nonGslots := (Finset.equivFin nonGslots).symm
    -- The `Fin M` index of the non-`g` slot for a slot `i` is `i.val - 1`.  The `i.val ≠ 0`
    -- argument is required for totality: when `M = 0`, `i : Fin (1 + M) = Fin 1` forces
    -- `i.val = 0`, so the `i.val ≠ 0` premise is false and the function is vacuously defined.
    let idx : (i : Fin (1 + M)) → i.val ≠ 0 → Fin M :=
      fun i hne => ⟨i.val - 1, by
        by_cases hM : M = 0
        · exfalso
          have : i.val = 0 := by
            have : i.val < 1 := by simpa [hM] using i.isLt
            omega
          exact hne this
        · have hsub : i.val - 1 < i.val := by omega
          have hle : i.val ≤ M := by omega
          exact Nat.lt_of_lt_of_le hsub hle⟩
    -- The bound on the second component of `e j` (from its membership in `nonGslots`).
    let hj_of (j : Fin M) : (e j).1.2 < (W ((e j).1.1)).k := by
      let hmem := (e j).2
      dsimp [nonGslots] at hmem
      obtain ⟨b', hb', himg⟩ := Finset.mem_biUnion.mp hmem
      obtain ⟨j', hj', hpair⟩ := Finset.mem_image.mp himg
      have hb' : b' = (e j).1.1 := (Prod.ext_iff.mp hpair).1
      have hj'eq : j' = (e j).1.2 := (Prod.ext_iff.mp hpair).2
      rw [hb', hj'eq] at hj'
      exact Finset.mem_range.mp hj'
    -- The series held at the non-`g` slot for `Fin M` index `j`: the `((e j).1.2)`-th element
    -- of the witnessing tuple of `W ((e j).1.1)`.  The bound proof is inlined so that it
    -- elaborates to a concrete proof term that `rw`/`simp` can adjust via `Eq.ndrec`.
    let FSofJ (j : Fin M) : Series α :=
      (W ((e j).1.1)).fs ⟨(e j).1.2, by
        let hmem := (e j).2
        dsimp [nonGslots] at hmem
        obtain ⟨b', hb', himg⟩ := Finset.mem_biUnion.mp hmem
        obtain ⟨j', hj', hpair⟩ := Finset.mem_image.mp himg
        have hb' : b' = (e j).1.1 := (Prod.ext_iff.mp hpair).1
        have hj'eq : j' = (e j).1.2 := (Prod.ext_iff.mp hpair).2
        rw [hb', hj'eq] at hj'
        exact Finset.mem_range.mp hj'
      ⟩
    -- The combined tuple: slot 0 is `g`; slot `i` (`i.val ≥ 1`) is the non-`g` slot for
    -- `Fin M` index `idx i` (i.e. `i.val - 1`), an element of some `W b .fs`.
    let FS : Fin (1 + M) → Series α := fun i =>
      if h : i.val = 0 then g
      else FSofJ (idx i (by omega))
    -- `g` is an infiltration polynomial in `FS`: the variable of slot 0.
    have hfin_g : g = infiltrationEval α (1 + M) FS (MvPolynomial.X ⟨0, by omega⟩) := by
      rw [infiltrationEval_X]
      simp [FS]
    -- Membership of `(a, j)` in `nonGslots` (for `j < (W a).k`), as a named constant so that
    -- `slot_of` and the lemmas about it share the *same* term.
    have hmem_pair : (a : α) → (j : ℕ) → j < (W a).k → (a, j) ∈ nonGslots := by
      intro a j hj
      dsimp [nonGslots]
      exact Finset.mem_biUnion.mpr ⟨a, Finset.mem_univ a,
        Finset.mem_image_of_mem (fun j' => (a, j')) (Finset.mem_range.mpr hj)⟩
    -- The slot of `FS` holding `(W a).fs j` (for `j < (W a).k`): `1 +` the index of `(a, j)`.
    let slot_of (a : α) (j : ℕ) (hj : j < (W a).k) : Fin (1 + M) :=
      ⟨1 + (e.symm ⟨(a, j), hmem_pair a j hj⟩).val,
        by omega⟩
    -- A slot of `FS` holds the corresponding element of the witnessing tuple.
    have hFS_slot : ∀ (a : α) (j : ℕ) (hj : j < (W a).k), FS (slot_of a j hj) = (W a).fs ⟨j, hj⟩ := by
      intro a j hj
      by_cases hM : M = 0
      · exfalso
        have hmem : (a, j) ∈ nonGslots := hmem_pair a j hj
        have hpos : 0 < nonGslots.card := Finset.card_pos.mpr ⟨(a, j), hmem⟩
        have hzero : nonGslots.card = 0 := hM
        rw [hzero] at hpos
        omega
      · let x : nonGslots := ⟨(a, j), hmem_pair a j hj⟩
        let i := slot_of a j hj
        let hne : i.val ≠ 0 := by
          dsimp [i, slot_of, x]
          omega
        have he : e (idx i hne) = x := by
          have hval : (idx i hne).val = (e.symm x).val := by
            dsimp [idx, i, slot_of, x]
            omega
          rw [Fin.ext hval]
          exact Equiv.apply_symm_apply e x
        dsimp [FS]
        dsimp [i, slot_of, x] at he
        split_ifs with h
        · exfalso
          omega
        · dsimp [FSofJ]
          have he' : e (idx (slot_of a j hj) h) = x := by
            have hidx_eq : idx (slot_of a j hj) h = idx (slot_of a j hj) hne := by
              apply Fin.ext
              rfl
            dsimp [slot_of, x] at hidx_eq
            dsimp [slot_of, x]
            rw [← hidx_eq]
            exact he
          rw [he']
    -- `FS` is closed under left derivatives.
    have hclose_FS : ∀ (a : α) (i : Fin (1 + M)),
        ∃ q, leftDeriv α a (FS i) = infiltrationEval α (1 + M) FS q := by
      intro a i
      by_cases h0 : i = 0
      · -- `i` is the `g` slot: `leftDeriv a g = f a`, an infiltration polynomial in `W a .fs`.
        let q : MvPolynomial (Fin (1 + M)) ℚ :=
          liftPoly (1 + M) (W a).k (fun j : Fin (W a).k => slot_of a j.val j.isLt) (W a).p
        refine ⟨q, ?_⟩
        have hFSg : FS i = g := by simp [FS, h0]
        rw [hFSg, hantideriv a, (W a).hfin]
        have hassign : ∀ (j : Fin (W a).k),
            FS ((fun j : Fin (W a).k => slot_of a j.val j.isLt) j) = (W a).fs j := by
          intro j
          dsimp
          rw [hFS_slot]
        dsimp only [q]
        exact infiltrationEval_lift (1 + M) (W a).k FS (W a).fs
          (fun j : Fin (W a).k => slot_of a j.val j.isLt) hassign (W a).p
      · -- `i` is a non-`g` slot: `FS i = (W b).fs ⟨jnat, hj⟩`; its left derivative is an infiltration
        -- polynomial in `W b .fs` (closure of that witnessing tuple).
        have hval : i.val ≥ 1 := by
          have hne : i.val ≠ 0 := by
            intro h
            exact h0 (Fin.ext h)
          omega
        let j : Fin M := ⟨i.val - 1, by
          have hbound : i.val ≤ M := by omega
          omega⟩
        let b := (e j).1.1
        let jnat := (e j).1.2
        let hj : jnat < (W b).k := hj_of j
        have hi : i = slot_of b jnat hj := by
          apply Fin.ext
          dsimp [slot_of]
          have hsub : (⟨(b, jnat), by
              dsimp [nonGslots]
              exact Finset.mem_biUnion.mpr ⟨b, Finset.mem_univ b,
                Finset.mem_image_of_mem (fun j' => (b, j')) (Finset.mem_range.mpr hj)⟩⟩ : nonGslots) = e j := by
            apply Subtype.ext
            rfl
          rw [hsub, Equiv.symm_apply_apply]
          dsimp only [j]
          omega
        have hFSi : FS i = (W b).fs ⟨jnat, hj⟩ := by
          rw [hi]
          exact hFS_slot b jnat hj
        obtain ⟨q', hq'⟩ := (W b).hclose a ⟨jnat, hj⟩
        let q : MvPolynomial (Fin (1 + M)) ℚ :=
          liftPoly (1 + M) (W b).k (fun j' : Fin (W b).k => slot_of b j'.val j'.isLt) q'
        refine ⟨q, ?_⟩
        rw [hFSi, hq']
        have hassign : ∀ (j' : Fin (W b).k),
            FS ((fun j' : Fin (W b).k => slot_of b j'.val j'.isLt) j') = (W b).fs j' := by
          intro j'
          dsimp
          rw [hFS_slot]
        dsimp only [q]
        exact infiltrationEval_lift (1 + M) (W b).k FS (W b).fs
          (fun j' : Fin (W b).k => slot_of b j'.val j'.isLt) hassign q'
    exact ⟨1 + M, FS, MvPolynomial.X ⟨0, by omega⟩, hfin_g, hclose_FS⟩
  exact hsem_g

/-! ### The effective prevariety of infiltration-finite series -/

/-- The word map sends `0` to `0`: `A.Mword w 0 = 0` for every word `w` (each letter
    infiltration `infiltrationExt A a` is `ℚ`-linear, hence preserves `0`, and a composition
    of such maps does too). -/
private theorem Mword_zero (A : InfiltrationAutomaton α) (w : List α) : A.Mword w 0 = 0 := by
  induction w with
  | nil => simp [Mword_nil]
  | cons a w' ih => rw [Mword_cons, Function.comp_apply, infiltrationExt_zero, ih]

/-- The left derivative of an infiltration-finite (semantic) series is infiltration-finite
    (semantic): the witnessing tuple is unchanged, and the polynomial is replaced by the
    general infiltration `infiltrationExtGen k q p` with `q i` the left-derivative polynomial
    of `fs i` (`leftDeriv_infiltrationEval_infiltration`).  (The infiltration analogue of
    `leftDeriv_shuffleFiniteSem`, where the letter map is a *derivation*; here the letter
    endomorphism `S_a` is only `ℚ`-linear, so the left derivative is read off by the general
    infiltration `Δ_q = S_q − id`.) -/
private theorem leftDeriv_infiltrationFiniteSem (f : Series α) (hfsem : IsInfiltrationFinite α f) (a : α) :
    IsInfiltrationFinite α (leftDeriv α a f) := by
  obtain ⟨k, fs, p, hfp, hfc⟩ := hfsem
  let q : Fin k → MvPolynomial (Fin k) ℚ := fun i => Classical.choose (hfc a i)
  have hq : ∀ i, leftDeriv α a (fs i) = infiltrationEval α k fs (q i) := by
    intro i
    dsimp [q]
    exact Classical.choose_spec (hfc a i)
  refine ⟨k, fs, infiltrationExtGen k q p, ?_, hfc⟩
  calc
    leftDeriv α a f = leftDeriv α a (infiltrationEval α k fs p) := by rw [← hfp]
    _ = infiltrationEval α k fs (infiltrationExtGen k q p) := by rw [leftDeriv_infiltrationEval_infiltration k fs a q hq p]

/-- `A.recognised` is infiltration-finite (by the coincidence, from recognisability). -/
private theorem recognised_infiltrationFinite (A : InfiltrationAutomaton α) :
    IsInfiltrationFinite α A.recognised :=
  infiltrationFinite_of_recognisable _ ⟨A, rfl⟩

/-- The top prevariety: the whole space of series, trivially closed under the
    derivatives.  Serves as the `prevariety` field of the infiltration effective
    prevariety (the image of the semantics is a prevariety; the top space is the
    coarsest such). -/
private def topPrevariety (α : Type*) : Prevariety α :=
  { carrier := ⊤,
    closedLeftDeriv := fun _ _ => Submodule.mem_top,
    closedRightDeriv := fun _ _ => Submodule.mem_top }

/-- An infiltration automaton recognising the zero series: one nonterminal, zero final
    weight, and zero transitions (the configuration is `0` after any non-empty word,
    and the empty word evaluates to `F 0 = 0`).  Takes `α` explicitly so that the
    projection `zeroAutomaton α .recognised` elaborates. -/
noncomputable def zeroAutomaton (α : Type*) : InfiltrationAutomaton α :=
  { dim := 1,
    hdim := by decide,
    F := fun _ => 0,
    Δ := fun _ _ => 0 }

/-- `zeroAutomaton` recognises the zero series. -/
private theorem zeroAutomaton_recognised :
    (zeroAutomaton α).recognised = 0 := by
  funext w
  induction w with
  | nil =>
      dsimp [InfiltrationAutomaton.recognised, InfiltrationAutomaton.sem, zeroAutomaton]
      rw [Mword_nil]
      simp
  | cons a w' =>
      dsimp [InfiltrationAutomaton.recognised, InfiltrationAutomaton.sem]
      rw [Mword_cons]
      simp only [Function.comp_apply]
      have h : infiltrationExt (zeroAutomaton α) a (MvPolynomial.X (Fin.mk 0 (zeroAutomaton α).hdim)) = 0 := by
        rw [infiltrationExt_X]
        dsimp [zeroAutomaton]
        rfl
      rw [h, Mword_zero (zeroAutomaton α) w']
      simp

/-- The sum of two recognised series is infiltration-recognisable. -/
private theorem addRecognisable (A B : InfiltrationAutomaton α) :
    IsInfiltrationRecognisable α (A.recognised + B.recognised) :=
  (InfiltrationCoincidence _).mp
    (InfiltrationClosure.1 _ _ (recognised_infiltrationFinite A) (recognised_infiltrationFinite B))

/-- The scalar multiple of a recognised series is infiltration-recognisable. -/
private theorem smulRecognisable (c : ℚ) (A : InfiltrationAutomaton α) :
    IsInfiltrationRecognisable α (c • A.recognised) :=
  (InfiltrationCoincidence _).mp
    (InfiltrationClosure.2.1 _ _ (recognised_infiltrationFinite A))

/-- The left derivative of a recognised series is infiltration-recognisable. -/
private theorem derivLRecognisable (a : α) (A : InfiltrationAutomaton α) :
    IsInfiltrationRecognisable α (leftDeriv α a A.recognised) :=
  (InfiltrationCoincidence _).mp
    (leftDeriv_infiltrationFiniteSem _ (recognised_infiltrationFinite A) a)

/-- The right derivative of a recognised series is infiltration-recognisable. -/
private theorem derivRRecognisable (a : α) (A : InfiltrationAutomaton α) :
    IsInfiltrationRecognisable α (rightDeriv α a A.recognised) :=
  (InfiltrationCoincidence _).mp
    (InfiltrationClosure.2.2.2 _ _ (recognised_infiltrationFinite A))

/-- The sum automaton: recognises `A.recognised + B.recognised`. -/
noncomputable def addAutomaton (A B : InfiltrationAutomaton α) : InfiltrationAutomaton α :=
  Classical.choose (addRecognisable A B)

/-- The scalar-multiple automaton: recognises `c • A.recognised`. -/
noncomputable def smulAutomaton (c : ℚ) (A : InfiltrationAutomaton α) : InfiltrationAutomaton α :=
  Classical.choose (smulRecognisable c A)

/-- The left-derivative automaton: recognises `leftDeriv a (A.recognised)`. -/
noncomputable def derivLAutomaton (a : α) (A : InfiltrationAutomaton α) : InfiltrationAutomaton α :=
  Classical.choose (derivLRecognisable a A)

/-- The right-derivative automaton: recognises `rightDeriv a (A.recognised)`. -/
noncomputable def derivRAutomaton (a : α) (A : InfiltrationAutomaton α) : InfiltrationAutomaton α :=
  Classical.choose (derivRRecognisable a A)

private theorem addAutomaton_spec (A B : InfiltrationAutomaton α) :
    (addAutomaton A B).recognised = A.recognised + B.recognised := by
  dsimp [addAutomaton]
  exact Classical.choose_spec (addRecognisable A B)

private theorem smulAutomaton_spec (c : ℚ) (A : InfiltrationAutomaton α) :
    (smulAutomaton c A).recognised = c • A.recognised := by
  dsimp [smulAutomaton]
  exact Classical.choose_spec (smulRecognisable c A)

private theorem derivLAutomaton_spec (a : α) (A : InfiltrationAutomaton α) :
    (derivLAutomaton a A).recognised = leftDeriv α a A.recognised := by
  dsimp [derivLAutomaton]
  exact Classical.choose_spec (derivLRecognisable a A)

private theorem derivRAutomaton_spec (a : α) (A : InfiltrationAutomaton α) :
    (derivRAutomaton a A).recognised = rightDeriv α a A.recognised := by
  dsimp [derivRAutomaton]
  exact Classical.choose_spec (derivRRecognisable a A)

/-- The effective prevariety of infiltration-finite series: presentations are infiltration
    automata, the semantics is the recognised series, and the operations are carried out by
    the (classically chosen) closure automata.  Equality is decided by the zeroness decision
    applied to `A - B` (`InfiltrationEqualityDecidable`). -/
noncomputable def infiltrationEffectivePrevariety [Fintype α] : EffectivePrevariety α :=
  { Rep := InfiltrationAutomaton α,
    sem := fun A => A.recognised,
    prevariety := topPrevariety α,
    mem := fun A => by
      change A.recognised ∈ (⊤ : Submodule ℚ (Series α))
      exact Submodule.mem_top
    zero := zeroAutomaton α,
    add := addAutomaton,
    smul := smulAutomaton,
    derivL := derivLAutomaton,
    derivR := derivRAutomaton,
    sem_zero := by
      change (zeroAutomaton α).recognised = 0
      exact zeroAutomaton_recognised
    sem_add := fun A B => by
      change (addAutomaton A B).recognised = A.recognised + B.recognised
      exact addAutomaton_spec A B
    sem_smul := fun c A => by
      change (smulAutomaton c A).recognised = c • A.recognised
      exact smulAutomaton_spec c A
    sem_derivL := fun a A => by
      change (derivLAutomaton a A).recognised = leftDeriv α a (A.recognised)
      exact derivLAutomaton_spec a A
    sem_derivR := fun a A => by
      change (derivRAutomaton a A).recognised = rightDeriv α a (A.recognised)
      exact derivRAutomaton_spec a A
    decEq := fun A B => by
      let d := Classical.choose (InfiltrationEqualityDecidable (α := α))
      let hd := Classical.choose_spec (InfiltrationEqualityDecidable (α := α))
      let C := addAutomaton A (smulAutomaton (-1) B)
      have hc : C.recognised = A.recognised - B.recognised := by
        dsimp [C]
        rw [addAutomaton_spec, smulAutomaton_spec]
        simp [sub_eq_add_neg]
      have hdC : d C = true ↔ C.recognised = 0 := hd C
      have hsub : C.recognised = 0 ↔ A.recognised = B.recognised := by
        rw [hc, sub_eq_zero]
      have h : d C = true ↔ A.recognised = B.recognised := hdC.trans hsub
      let decP : Decidable (d C = true) := inferInstance
      exact match decP with
        | .isTrue ht => .isTrue (h.mp ht)
        | .isFalse hf => .isFalse fun x => hf (h.mpr x) }

/--
---
conclusion: Lax946791.Infiltration.InfiltrationEffectivePrevariety
---
The infiltration-finite series form an effective prevariety over a finite alphabet
(paper §7, theorem): the effective prevariety `infiltrationEffectivePrevariety` has
presentations given by infiltration automata, and its image is exactly the
infiltration-finite series (by the coincidence, `InfiltrationCoincidence`).
-/
theorem InfiltrationEffectivePrevariety [Fintype α] :
    ∃ P : EffectivePrevariety α, ∀ f, IsInfiltrationFinite α f ↔ ∃ r : P.Rep, P.sem r = f := by
  refine ⟨infiltrationEffectivePrevariety, ?_⟩
  intro f
  dsimp [infiltrationEffectivePrevariety, IsInfiltrationRecognisable]
  exact InfiltrationCoincidence f

/--
---
conclusion: Lax946791.Infiltration.InfiltrationCommutativityDecidable
---
The commutativity problem is decidable for infiltration-finite series over a finite
alphabet (paper §7).  This is the meta-theorem
(`EffectivePrevarietyCommutativityDecidable`) applied to
`infiltrationEffectivePrevariety`, the effective prevariety of infiltration-finite
series: its boolean decider on a presentation `A` decides
`IsCommutative (infiltrationEffectivePrevariety.sem A)`, and since
`infiltrationEffectivePrevariety.sem A = A.recognised`, it decides
`IsCommutative (A.recognised)`.
-/
theorem InfiltrationCommutativityDecidable [Fintype α] :
    ∃ d : InfiltrationAutomaton α → Bool, ∀ A, d A = true ↔ IsCommutative α (A.recognised) := by
  obtain ⟨d, hd⟩ := EffectivePrevarietyCommutativityDecidable (α := α) infiltrationEffectivePrevariety
  refine ⟨fun (A : InfiltrationAutomaton α) => d A, fun A => ?_⟩
  have hsem : infiltrationEffectivePrevariety.sem A = A.recognised := by
    dsimp only [infiltrationEffectivePrevariety]
  simpa [hsem] using hd A

end Lax946791Proofs.Infiltration

