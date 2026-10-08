import Lax619925.Recognisable
import Lax619925.Series
import Lax619925.Prevariety
import Lax619925.Commutativity
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Matrix.Basis
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Algebra.Module.Submodule.Range
import Mathlib.Algebra.Module.Submodule.Map
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Algebra.Module.Submodule.Ker
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Finsupp.Supported
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Lax619925Proofs.Recognisable

open Lax619925.Series Lax619925.Prevariety Lax619925.Commutativity Lax619925.Recognisable
open Matrix Submodule
open Classical

variable {α : Type*}

/-- `Mword [] = 1`. -/
private theorem Mword_nil (r : LinearRepresentation α) : r.Mword [] = 1 := by
  dsimp [LinearRepresentation.Mword]

/-- `Mword (a :: w) = M a * Mword w`. -/
private theorem Mword_cons (r : LinearRepresentation α) (a : α) (w : List α) :
    r.Mword (a :: w) = r.M a * r.Mword w := by
  dsimp [LinearRepresentation.Mword]

/-- The word product is a monoid homomorphism: `Mword (u ++ v) = Mword u * Mword v`. -/
private theorem Mword_append (r : LinearRepresentation α) (u v : List α) :
    r.Mword (u ++ v) = r.Mword u * r.Mword v := by
  induction u with
  | nil => simp [Mword_nil]
  | cons a u ih => simp [Mword_cons, ih, List.cons_append, Matrix.mul_assoc]

/-- The product of the transposed letter matrices over `w` is the transpose of the
    word product over `w.reverse`. -/
private theorem Mword_reverse_transpose (r : LinearRepresentation α) (w : List α) :
    w.foldr (fun a A => (r.M a).transpose * A) 1 = (r.Mword (w.reverse)).transpose := by
  induction w with
  | nil => simp [Mword_nil]
  | cons a w ih =>
    simp [List.foldr_cons, ih, List.reverse_cons, Mword_append, Mword_cons, Mword_nil,
         Matrix.transpose_mul]

/--
---
conclusion: Lax619925.Recognisable.RecognisableReversal
---
The transposed representation `(k, y, x, Mᵀ)` recognises `reversal f`: on a word
`w` it computes `y · (M(w.reverse))ᵀ · x`, which equals `x · M(w.reverse) · y = f (w.reverse)`
by the bilinear-form identity.
-/
theorem RecognisableReversal (f : Series α) (hf : IsRecognisable α f) :
    IsRecognisable α (reversal α f) := by
  obtain ⟨r, rfl⟩ := hf
  use { dim := r.dim, init := r.final, final := r.init, M := fun a => (r.M a).transpose }
  ext w
  dsimp [LinearRepresentation.sem, LinearRepresentation.Mword, reversal]
  rw [Mword_reverse_transpose r w]
  dsimp [LinearRepresentation.Mword]
  rw [dotProduct_transpose_mulVec]

/-- The left derivative of a recognisable series is recognisable: prepend the
    letter matrix to the initial vector. -/
private theorem RecognisableLeftDeriv (a : α) (f : Series α) (hf : IsRecognisable α f) :
    IsRecognisable α (leftDeriv α a f) := by
  obtain ⟨r, rfl⟩ := hf
  use { dim := r.dim, init := r.init ᵥ* r.M a, final := r.final, M := r.M }
  ext w
  simp [LinearRepresentation.sem, LinearRepresentation.Mword, leftDeriv, dotProduct_mulVec]

/--
---
conclusion: Lax619925.Recognisable.RecognisableRightDeriv
---
By the paper's double-reversal identity `rightDeriv a f = reversal (leftDeriv a (reversal f))`:
`reversal f` is recognisable (transposition), so is `leftDeriv a (reversal f)` (left-derivative
closure), so is its reversal — hence `rightDeriv a f` is recognisable.
-/
theorem RecognisableRightDeriv (a : α) (f : Series α) (hf : IsRecognisable α f) :
    IsRecognisable α (rightDeriv α a f) := by
  have h1 : IsRecognisable α (reversal α f) := RecognisableReversal f hf
  have h2 : IsRecognisable α (leftDeriv α a (reversal α f)) :=
    RecognisableLeftDeriv a (reversal α f) h1
  obtain ⟨r, hr⟩ := RecognisableReversal (leftDeriv α a (reversal α f)) h2
  use r
  rw [hr, ReversalSwapsDerivatives, ReversalInvolution]

/-- `leftDeriv a` is `ℚ`-linear: it preserves addition. -/
private theorem leftDeriv_add (a : α) (f g : Series α) :
    leftDeriv α a (f + g) = leftDeriv α a f + leftDeriv α a g := by
  funext w
  simp [leftDeriv]

/-- `leftDeriv a` is `ℚ`-linear: it commutes with scalar multiplication. -/
private theorem leftDeriv_smul (a : α) (c : ℚ) (f : Series α) :
    leftDeriv α a (c • f) = c • leftDeriv α a f := by
  funext w
  simp [leftDeriv]

/-- The left derivative `leftDeriv a`, as a `ℚ`-linear map on series. -/
private def leftDerivLin (a : α) : (Series α) →ₗ[ℚ] Series α :=
  { toFun := fun f => leftDeriv α a f
    map_add' := fun f g => leftDeriv_add a f g
    map_smul' := fun c f => leftDeriv_smul a c f }

/-- Applying the linear map `leftDerivLin a` is definitionally `leftDeriv a`. -/
private theorem leftDerivLin_apply (a : α) (f : Series α) :
    (leftDerivLin a) f = leftDeriv α a f := rfl

/-- Left-derivative closure: if `f` is linearly finite with generators `G`, then
    `leftDeriv a f` is linearly finite with the *same* generators `G`.  The image of
    `span G` under the linear map `leftDeriv a` is contained in `span G` because every
    generator maps into `span G`.  The submodule is held in a `let`-binding so it stays
    opaque to the elaborator (an explicit submodule of a function-type module triggers a
    `whnf` timeout). -/
private theorem LF_leftDeriv (f : Series α) (hf : IsLinearlyFinite α f) (a : α) :
    IsLinearlyFinite α (leftDeriv α a f) := by
  obtain ⟨G, hspan, hclose⟩ := hf
  let p := Submodule.span ℚ (G : Set (Series α))
  refine ⟨G, ?_, hclose⟩
  have h : map (leftDerivLin a) p ≤ p :=
    (map_span_le (leftDerivLin a) (↑G) p).2
      (fun g hg => by
        rw [leftDerivLin_apply]
        exact hclose a g hg)
  rw [← leftDerivLin_apply]
  exact h (Submodule.mem_map_of_mem hspan)

/-- Scalar closure: if `f` is linearly finite with generators `G`, then `c • f` is
    linearly finite with the same generators (a submodule is closed under scalars). -/
private theorem LF_smul (c : ℚ) (f : Series α) (hf : IsLinearlyFinite α f) :
    IsLinearlyFinite α (c • f) := by
  obtain ⟨G, hspan, hclose⟩ := hf
  let p := Submodule.span ℚ (G : Set (Series α))
  refine ⟨G, ?_, hclose⟩
  exact Submodule.smul_mem p c hspan

/-- Addition closure: if `f` is linearly finite with generators `G` and `g` with
    generators `H`, then `f + g` is linearly finite with generators `G ∪ H`.  Proven via
    the `mem_span` characterization (`x ∈ span R s ↔ ∀ p, s ⊆ p → x ∈ p`), which avoids
    unfolding the target submodule (a `whnf` on a function-type module times out). -/
private theorem LF_add (f g : Series α) (hf : IsLinearlyFinite α f) (hg : IsLinearlyFinite α g) :
    IsLinearlyFinite α (f + g) := by
  obtain ⟨G, hspan_f, hclose_f⟩ := hf
  obtain ⟨H, hspan_g, hclose_g⟩ := hg
  have hGsub : ↑G ⊆ ↑(G ∪ H) := fun x hx => Finset.mem_union.mpr (Or.inl hx)
  have hHsub : ↑H ⊆ ↑(G ∪ H) := fun x hx => Finset.mem_union.mpr (Or.inr hx)
  refine ⟨G ∪ H, ?_, ?_⟩
  · rw [Submodule.mem_span]
    intro p hsub
    have hf : f ∈ ↑p := (Submodule.mem_span.mp hspan_f) p (Set.Subset.trans hGsub hsub)
    have hg : g ∈ ↑p := (Submodule.mem_span.mp hspan_g) p (Set.Subset.trans hHsub hsub)
    exact AddMemClass.add_mem hf hg
  · intro a h hmem
    rw [Submodule.mem_span]
    intro p hsub
    rcases Finset.mem_union.mp hmem with hG' | hH'
    · exact (Submodule.mem_span.mp (hclose_f a h hG')) p (Set.Subset.trans hGsub hsub)
    · exact (Submodule.mem_span.mp (hclose_g a h hH')) p (Set.Subset.trans hHsub hsub)

/--
---
conclusion: Lax619925.Recognisable.LinearlyFiniteClosure
---
The class of linearly finite series is closed under addition, scalar multiplication, and
left derivatives (paper §4).  Each operation is witnessed by an explicit finite generator
set: addition uses `G ∪ H`, while scalar multiplication and left derivatives reuse the
original generators.
-/
theorem LinearlyFiniteClosure :
    (∀ (f g : Series α), IsLinearlyFinite α f → IsLinearlyFinite α g → IsLinearlyFinite α (f + g)) ∧
    (∀ (c : ℚ) (f : Series α), IsLinearlyFinite α f → IsLinearlyFinite α (c • f)) ∧
    (∀ (a : α) (f : Series α), IsLinearlyFinite α f → IsLinearlyFinite α (leftDeriv α a f)) := by
  exact ⟨fun f g hf hg => LF_add f g hf hg,
        fun c f hf => LF_smul c f hf,
        fun a f hf => LF_leftDeriv f hf a⟩

/--
---
conclusion: Lax619925.Recognisable.LinearlyFiniteAntiDerivativeClosure
---
If `g` is a left anti-derivative of the tuple `f` (`leftDeriv a g = f a` for every letter
`a`) and each `f a` is linearly finite, then `g` is linearly finite.  The witness is
`{g} ∪ ⋃ₐ Gₐ`, where `Gₐ` is a finite generator set for `f a`; the union is finite because
`α` is a `Fintype`.  Every generator of the witness maps under a left derivative either to
`f a` (if it is `g`) or into the span of its own `Gₐ` (if it comes from some `G_b`), and
both of those lie in the span of the whole witness.
-/
theorem LinearlyFiniteAntiDerivativeClosure [Fintype α]
    (g : Series α) (f : α → Series α) (hantideriv : IsLeftAntiDerivative α g f)
    (hf : ∀ a, IsLinearlyFinite α (f a)) : IsLinearlyFinite α g := by
  let Gfun : α → Finset (Series α) := fun a => Classical.choose (hf a)
  have hspan_a : ∀ a, f a ∈ Submodule.span ℚ (Gfun a) :=
    fun a => (Classical.choose_spec (hf a)).1
  have hclose_a : ∀ (i a : α), ∀ h ∈ Gfun i, leftDeriv α a h ∈ Submodule.span ℚ (Gfun i) :=
    fun i a h hh => (Classical.choose_spec (hf i)).2 a h hh
  let G' : Finset (Series α) := {g} ∪ Finset.biUnion Finset.univ Gfun
  refine ⟨G', ?_, ?_⟩
  · rw [Submodule.mem_span]
    intro p hsub
    have hgm : g ∈ ↑G' := Finset.mem_union.mpr (Or.inl (Finset.mem_singleton.mpr rfl))
    exact hsub hgm
  · intro a h hmem
    rw [Submodule.mem_span]
    intro p hsub
    rcases Finset.mem_union.mp hmem with hgs | hb
    · have h_eq : h = g := Finset.mem_singleton.mp hgs
      have hspanAsub : ↑(Gfun a) ⊆ ↑G' :=
        fun x hx => Finset.mem_union.mpr
          (Or.inr (Finset.mem_biUnion.mpr ⟨a, Finset.mem_univ a, hx⟩))
      have hfa_sub_p : f a ∈ ↑p :=
        (Submodule.mem_span.mp (hspan_a a)) p (Set.Subset.trans hspanAsub hsub)
      rw [h_eq, hantideriv a]
      exact hfa_sub_p
    · rcases Finset.mem_biUnion.mp hb with ⟨b, _, hbmem⟩
      have hspanBsub : ↑(Gfun b) ⊆ ↑G' :=
        fun x hx => Finset.mem_union.mpr
          (Or.inr (Finset.mem_biUnion.mpr ⟨b, Finset.mem_univ b, hx⟩))
      have hclose_b : leftDeriv α a h ∈ Submodule.span ℚ (Gfun b) :=
        hclose_a b a h hbmem
      exact (Submodule.mem_span.mp hclose_b) p (Set.Subset.trans hspanBsub hsub)

/-! ### The coincidence lemma: `IsRecognisable ↔ IsLinearlyFinite` -/

/-- The `ℚ`-linear map sending an initial vector `v` to the series
    `w ↦ v ⬝ᵥ M(w) · final`.  Its range is the set of series recognised by
    representations sharing `r`'s `M` and `final`, and it is closed under left
    derivatives (`semLin_leftDeriv`). -/
@[reducible]
private def semLin (r : LinearRepresentation α) : (Fin r.dim → ℚ) →ₗ[ℚ] Series α :=
  { toFun := fun v w => dotProduct v (Matrix.mulVec (r.Mword w) r.final)
    map_add' := fun v w => by funext u; simp [add_dotProduct]
    map_smul' := fun c v => by funext u; simp [smul_dotProduct] }

/-- The range of `semLin r` is closed under left derivatives:
    `leftDeriv a (semLin r v) = semLin r (v ᵥ* M a)`. -/
private theorem semLin_leftDeriv (r : LinearRepresentation α) (a : α) (v : Fin r.dim → ℚ) :
    leftDeriv α a (semLin r v) = semLin r (v ᵥ* r.M a) := by
  funext w
  simp [leftDeriv]
  rw [Mword_cons, ← mulVec_mulVec, dotProduct_mulVec]

/--
---
The *forward* direction of the coincidence lemma: a recognisable series is linearly
finite.  The `ℚ`-space `V` recognised by the fixed transition matrices `r.M` and final
vector `r.final` (the range of `semLin r`) is finite-dimensional — its domain
`Fin r.dim → ℚ` is — hence finitely generated, so `V = span G` for a finite set `G`.
The series `f = semLin r r.init` lies in `V`, and `V` is closed under left derivatives
(`semLin_leftDeriv`), so `span G` is a left-derivative-invariant finite generator space
containing `f`.
-/
private theorem LF_of_recognisable (f : Series α) (hf : IsRecognisable α f) :
    IsLinearlyFinite α f := by
  obtain ⟨r, rfl⟩ := hf
  let V := LinearMap.range (semLin r)
  have hfg : V.FG := by
    rw [Submodule.fg_iff_finiteDimensional]
    exact LinearMap.finiteDimensional_range (f := semLin r)
  obtain ⟨G, hspan⟩ := hfg
  refine ⟨G, ?_, ?_⟩
  · -- f ∈ span G  (f = semLin r r.init ∈ range = span G)
    rw [hspan]
    exact LinearMap.mem_range_self (semLin r) r.init
  · -- ∀ a, ∀ g ∈ G, leftDeriv a g ∈ span G  (range is left-derivative-closed)
    intro a g hmem
    rw [hspan]
    have hgV : g ∈ V := by
      rw [← hspan, Submodule.mem_span]
      intro p hsub
      exact hsub (Finset.mem_coe.mpr hmem)
    obtain ⟨v, hv⟩ := LinearMap.mem_range.mp hgV
    rw [← hv, semLin_leftDeriv]
    exact LinearMap.mem_range_self (semLin r) (v ᵥ* r.M a)

/-! ### The reverse direction: `IsLinearlyFinite → IsRecognisable` -/

/--
The *reverse* direction of the coincidence lemma: a linearly finite series is
recognisable.  Let `V = span G` be the finite-dimensional, left-derivative-closed
space from the hypothesis and let `B` be a basis of `V`.  The representation
`(k, init, final, M)` is read off from `B`: `init` is the coordinate vector of `f`,
`final i` is the value of the `i`-th basis vector at the empty word, and `M a` is the
matrix of the left derivative `leftDeriv a` on `V` in the basis `B` (row `i` is the
image of the `i`-th basis vector).  The key identity
`dotProduct v (M(w) · final) = (∑ᵢ vᵢ · Bᵢ) w`, proven by induction on `w`, then gives
`f = r.sem` because `f = ∑ᵢ initᵢ · Bᵢ`.
-/
private theorem recognisable_of_linearly_finite (f : Series α) (hf : IsLinearlyFinite α f) :
    IsRecognisable α f := by
  obtain ⟨G, hspan, hclose⟩ := hf
  let V := Submodule.span ℚ (G : Set (Series α))
  -- `V` is finitely generated (hence finite-dimensional over the field `ℚ`): it is the
  -- span of the finite set `G`.  Registered as an instance so `Module.finBasis` can use it.
  haveI : Module.Finite ℚ V := Module.Finite.span_finset ℚ G
  -- `V` is closed under left derivatives: the closure of the generators extends to all of `V`.
  have hcloseV : ∀ a, map (leftDerivLin a) V ≤ V :=
    fun a => (map_span_le (leftDerivLin a) (↑G) V).2
      (fun g hg => by rw [leftDerivLin_apply]; exact hclose a g hg)
  -- A basis of `V`, indexed by `Fin (finrank ℚ V)`.
  let k := Module.finrank ℚ V
  let B : Module.Basis (Fin k) ℚ V := Module.finBasis (R := ℚ) (M := V)
  -- `leftDeriv a (B i)` stays in `V`, so its `B`-coordinates are defined.
  have hmem (a : α) (i : Fin k) : leftDeriv α a ((B i : Series α)) ∈ V := by
    rw [← leftDerivLin_apply]
    exact (hcloseV a) (Submodule.mem_map_of_mem (B i).property)
  -- The representation.
  let r : LinearRepresentation α := {
    dim := k
    init := fun i => B.repr ⟨f, hspan⟩ i
    final := fun i => ((B i : Series α) [])
    M := fun a i j => B.repr ⟨leftDeriv α a ((B i : Series α)), hmem a i⟩ j }
  -- The series corresponding to a coordinate vector `v`.
  let s (v : Fin k → ℚ) : Series α := ∑ i, v i • (B i : Series α)
  -- Basis expansion: an element of `V` is the linear combination of the basis vectors
  -- (`Module.Basis.sum_repr`), and the coercion to `Series α` commutes with the sum.
  have hbasisExp (x : V) : (↑x : Series α) = ∑ i, (B.repr x) i • (B i : Series α) := by
    have h : ∑ i, (B.repr x) i • B i = (x : V) := Module.Basis.sum_repr B x
    calc
      (↑x : Series α) = ↑(∑ i, (B.repr x) i • B i) := by
        rw [h]
      _ = ∑ i, (B.repr x) i • (B i : Series α) := by
        rw [Submodule.coe_sum]
        simp
  -- The basis expansion of `leftDeriv a (B i)`, in terms of the matrix `M a`.
  have hBasis (a : α) (i : Fin k) :
      leftDeriv α a ((B i : Series α)) = ∑ j, (r.M a i j) • (B j : Series α) := by
    let y : V := ⟨leftDeriv α a ((B i : Series α)), hmem a i⟩
    calc
      leftDeriv α a ((B i : Series α)) = (↑y : Series α) := by
        simp [y]
      _ = ∑ j, (B.repr y) j • (B j : Series α) := by
        rw [hbasisExp y]
      _ = ∑ j, (r.M a i j) • (B j : Series α) := by
        rfl
  -- `leftDeriv a` commutes with `s`: `leftDeriv a (s v) = s (v ᵥ* M a)`.
  have hD (a : α) (v : Fin k → ℚ) : leftDeriv α a (s v) = s (v ᵥ* r.M a) := by
    calc
      leftDeriv α a (s v) = leftDeriv α a (∑ i, v i • (B i : Series α)) := by simp [s]
      _ = ∑ i, v i • leftDeriv α a ((B i : Series α)) := by
        rw [← leftDerivLin_apply]
        simp [leftDerivLin_apply]
      _ = ∑ i, v i • ∑ j, (r.M a i j) • (B j : Series α) := by
        congr 1; funext i; rw [hBasis a i]
      _ = ∑ i, ∑ j, (v i * r.M a i j) • (B j : Series α) := by
        simp [Finset.smul_sum, smul_smul]
      _ = ∑ j, ∑ i, (v i * r.M a i j) • (B j : Series α) := by rw [Finset.sum_comm]
      _ = ∑ j, (∑ i, v i * r.M a i j) • (B j : Series α) := by
        simp [Finset.sum_smul]
      _ = ∑ j, (v ᵥ* r.M a) j • (B j : Series α) := by
        simp [← Matrix.vecMul_apply_eq_sum]
      _ = s (v ᵥ* r.M a) := by rfl
  -- Key identity: `dotProduct v (M(w) · final) = s v w`, by induction on `w`.
  have hkey (w : List α) : ∀ (v : Fin k → ℚ),
      dotProduct v (r.Mword w *ᵥ r.final) = s v w := by
    induction w with
    | nil =>
      intro v
      rw [Mword_nil r, Matrix.one_mulVec]
      have h : s v [] = ∑ i, v i * ((B i : Series α) []) := by
        simp [s, Finset.sum_apply, Pi.smul_apply]
      rw [h, show r.final = fun i => ((B i : Series α) []) from rfl]
      simp [dotProduct]
    | cons a w ih =>
      intro v
      rw [Mword_cons r a w, ← mulVec_mulVec, dotProduct_mulVec, ih (v ᵥ* r.M a)]
      have h1 : s v (a :: w) = leftDeriv α a (s v) w := by simp [leftDeriv]
      rw [h1, ← hD a v]
  -- `f = s (r.init)`, so `r.sem = f`.
  use r
  ext w
  dsimp [LinearRepresentation.sem]
  rw [hkey w r.init]
  have hs : s r.init = f := by
    let z : V := ⟨f, hspan⟩
    calc
      s r.init = ∑ i, r.init i • (B i : Series α) := by simp [s]; rfl
      _ = ∑ i, (B.repr z) i • (B i : Series α) := by
        rfl
      _ = (↑z : Series α) := by rw [← hbasisExp z]
      _ = f := by simp [z]
  rw [hs]

/--
---
conclusion: Lax619925.Recognisable.RecognisableLinearlyFinite
---
The classical coincidence lemma (paper §4): a series is recognisable if and only if it
is linearly finite.  The forward direction (`LF_of_recognisable`) takes the
finite-dimensional range of the representation's `semLin` map as the finite generator
space; the reverse direction (`recognisable_of_linearly_finite`) builds a representation
from a left-derivative-closed finite generator space, reading off the matrices, initial
vector, and final vector from a basis of that space.
-/
theorem RecognisableLinearlyFinite (f : Series α) :
    IsRecognisable α f ↔ IsLinearlyFinite α f := by
  constructor
  · intro hf
    exact LF_of_recognisable f hf
  · intro hf
    exact recognisable_of_linearly_finite f hf

/-! ### Zeroness: the reachable subspace and the annihilation characterisation -/

/-- The subspace of `ℚ^k` reachable from the final vector: the span of the word-orbits
    `M(w) · final` as `w` ranges over all words.  It is the smallest subspace containing
    `final` and closed under all the letter matrices. -/
private def reachableSubspace (r : LinearRepresentation α) : Submodule ℚ (Fin r.dim → ℚ) :=
  Submodule.span ℚ {v | ∃ w : List α, v = r.Mword w *ᵥ r.final}

/-- The `ℚ`-linear functional `v ↦ init · v` (the dot product with the initial vector,
    which is linear in the second argument). -/
private def initDot (r : LinearRepresentation α) : (Fin r.dim → ℚ) →ₗ[ℚ] ℚ :=
  { toFun := fun v => dotProduct r.init v
    map_add' := fun u v => by simp [dotProduct_add]
    map_smul' := fun c v => by simp [dotProduct_smul] }

/-- Applying `initDot r` is definitionally the dot product with `r.init`. -/
private theorem initDot_apply (r : LinearRepresentation α) (v : Fin r.dim → ℚ) :
    (initDot r) v = dotProduct r.init v := rfl

/--
Zeroness characterisation (paper §4): `r.sem = 0` iff the initial vector annihilates
the reachable subspace, i.e. `∀ v ∈ reachableSubspace r, dotProduct r.init v = 0`.
The reachable subspace is the span of the word-orbits `M(w) · final`; the initial vector
annihilates it exactly when it annihilates every word-orbit (linearity of the dot product
in the second argument), which is exactly `r.sem = 0`.
-/
private theorem semZero_iff_annihilatesReachable (r : LinearRepresentation α) :
    r.sem = 0 ↔ ∀ v ∈ reachableSubspace r, dotProduct r.init v = 0 := by
  constructor
  · intro hsem v hv
    -- `r.sem = 0` forces every word-orbit to be annihilated by `r.init`.
    have hS : ∀ w, dotProduct r.init (r.Mword w *ᵥ r.final) = 0 := by
      intro w
      have := congrArg (fun f => f w) hsem
      simpa [LinearRepresentation.sem] using this
    -- hence the word-orbit set lies in the kernel of `initDot r`.
    have hker : ∀ v, (∃ w : List α, v = r.Mword w *ᵥ r.final) → v ∈ LinearMap.ker (initDot r) := by
      intro v ⟨w, hw⟩
      subst hw
      rw [LinearMap.mem_ker, initDot_apply]
      exact hS w
    -- so the reachable subspace (the span of the word-orbit set) lies in the kernel.
    have hsub : reachableSubspace r ≤ LinearMap.ker (initDot r) := by
      rw [show reachableSubspace r =
            Submodule.span ℚ {v | ∃ w : List α, v = r.Mword w *ᵥ r.final} from rfl, span_le]
      exact hker
    -- and `v` (in the reachable subspace) is therefore annihilated.
    rw [← initDot_apply, ← LinearMap.mem_ker]
    exact hsub hv
  · intro h
    ext w
    -- `r.sem w = dotProduct r.init (M(w) · final)`, and `M(w) · final` is in the reachable subspace.
    have hmem : r.Mword w *ᵥ r.final ∈ reachableSubspace r := by
      rw [show reachableSubspace r =
            Submodule.span ℚ {v | ∃ w : List α, v = r.Mword w *ᵥ r.final} from rfl]
      exact Submodule.mem_span_of_mem ⟨w, rfl⟩
    rw [LinearRepresentation.sem]
    exact h (r.Mword w *ᵥ r.final) hmem

/-- A `Decidable` instance, read as a `Bool` through its two branches, is `true` exactly
    when the proposition holds. -/
private theorem decCasesOnTrueIff {q : Prop} (d : Decidable q) :
    d.casesOn (fun _ => false) (fun _ => true) = true ↔ q := by
  cases d with
  | isTrue hq => simp; exact hq
  | isFalse hq => simp; exact hq

/--
---
conclusion: Lax619925.Recognisable.RecognisableEqualityDecidable
---
The equality (zeroness) problem is decidable for recognisable series over a finite
alphabet (paper §4).  The decider `decZero` reads, as a `Bool`, the linear-algebra
condition that the initial vector annihilates the subspace reachable from the final
vector: `r.sem = 0` iff that annihilation holds (`semZero_iff_annihilatesReachable`),
and the annihilation condition is decidable (it lives in the finite-dimensional space
`Fin r.dim → ℚ`), so `r.sem = 0` is.
-/
theorem RecognisableEqualityDecidable [Fintype α] :
    ∃ d : LinearRepresentation α → Bool, ∀ r, d r = true ↔ r.sem = 0 := by
  let decZero (r : LinearRepresentation α) : Bool :=
    (Classical.dec (∀ v ∈ reachableSubspace r, dotProduct r.init v = 0)).casesOn
      (fun _ => false) (fun _ => true)
  refine ⟨decZero, fun r => ?_⟩
  have hdec : decZero r = true ↔ ∀ v ∈ reachableSubspace r, dotProduct r.init v = 0 := by
    dsimp only [decZero]
    exact decCasesOnTrueIff (Classical.dec (∀ v ∈ reachableSubspace r, dotProduct r.init v = 0))
  have hchar : r.sem = 0 ↔ ∀ v ∈ reachableSubspace r, dotProduct r.init v = 0 :=
    semZero_iff_annihilatesReachable r
  exact hdec.trans hchar.symm

/-! ### The effective prevariety of recognisable series -/

/-- `rightDeriv a` is `ℚ`-linear: it preserves addition. -/
private theorem rightDeriv_add (a : α) (f g : Series α) :
    rightDeriv α a (f + g) = rightDeriv α a f + rightDeriv α a g := by
  funext w
  simp [rightDeriv]

/-- `rightDeriv a` is `ℚ`-linear: it commutes with scalar multiplication. -/
private theorem rightDeriv_smul (a : α) (c : ℚ) (f : Series α) :
    rightDeriv α a (c • f) = c • rightDeriv α a f := by
  funext w
  simp [rightDeriv]

/-- The right derivative `rightDeriv a`, as a `ℚ`-linear map on series. -/
private def rightDerivLin (a : α) : (Series α) →ₗ[ℚ] Series α :=
  { toFun := fun f => rightDeriv α a f
    map_add' := fun f g => rightDeriv_add a f g
    map_smul' := fun c f => rightDeriv_smul a c f }

/-- Applying the linear map `rightDerivLin a` is definitionally `rightDeriv a`. -/
private theorem rightDerivLin_apply (a : α) (f : Series α) :
    (rightDerivLin a) f = rightDeriv α a f := rfl

/-- The sum of two recognisable series is recognisable (via the coincidence lemma and
    the linearly-finite closure). -/
private theorem recognisableAdd (f g : Series α) (hf : IsRecognisable α f) (hg : IsRecognisable α g) :
    IsRecognisable α (f + g) := by
  have h1 : IsLinearlyFinite α f := (RecognisableLinearlyFinite f).mp hf
  have h2 : IsLinearlyFinite α g := (RecognisableLinearlyFinite g).mp hg
  exact (RecognisableLinearlyFinite (f + g)).mpr (LinearlyFiniteClosure.1 f g h1 h2)

/-- A scalar multiple of a recognisable series is recognisable. -/
private theorem recognisableSMul (c : ℚ) (f : Series α) (hf : IsRecognisable α f) :
    IsRecognisable α (c • f) := by
  have h1 : IsLinearlyFinite α f := (RecognisableLinearlyFinite f).mp hf
  exact (RecognisableLinearlyFinite (c • f)).mpr (LinearlyFiniteClosure.2.1 c f h1)

/-- The semantic of a representation is recognisable (witnessed by the representation
    itself). -/
private theorem semRecognisable (r : LinearRepresentation α) : IsRecognisable α (r.sem) :=
  ⟨r, rfl⟩

/-- There is a representation whose semantic is `r.sem + s.sem`. -/
private theorem existsRepAdd (r s : LinearRepresentation α) :
    ∃ t : LinearRepresentation α, t.sem = r.sem + s.sem :=
  recognisableAdd (r.sem) (s.sem) (semRecognisable r) (semRecognisable s)

/-- There is a representation whose semantic is `c • r.sem`. -/
private theorem existsRepSMul (c : ℚ) (r : LinearRepresentation α) :
    ∃ t : LinearRepresentation α, t.sem = c • r.sem :=
  recognisableSMul c (r.sem) (semRecognisable r)

/-- There is a representation whose semantic is `rightDeriv a (r.sem)`. -/
private theorem existsRepDerivR (a : α) (r : LinearRepresentation α) :
    ∃ t : LinearRepresentation α, t.sem = rightDeriv α a (r.sem) :=
  RecognisableRightDeriv a (r.sem) (semRecognisable r)

/-- Prepending the letter matrix to the initial vector gives a representation of
    `leftDeriv a (r.sem)`. -/
private theorem semDerivL (a : α) (r : LinearRepresentation α) :
    ({ dim := r.dim, init := r.init ᵥ* r.M a, final := r.final, M := r.M } : LinearRepresentation α).sem =
      leftDeriv α a (r.sem) := by
  ext w
  simp [LinearRepresentation.sem, LinearRepresentation.Mword, leftDeriv, dotProduct_mulVec]

/-- The effective prevariety of recognisable series: the presentations are linear
    representations, the carrier is the `ℚ`-span of the recognisable series (closed
    under the left and right derivatives), the vector-space operations and the
    derivatives are carried out on presentations (the left derivative explicitly, the
    rest by the closure properties), and equality is decidable by the zeroness decider
    (`RecognisableEqualityDecidable`): `sem r = sem s` reduces to `sem r - sem s = 0`,
    a zeroness question for the representation of the difference.  Named (rather than a
    local `let`) so that both theorems below can unfold it and see that `Rep` is
    `LinearRepresentation α` and `sem` is `LinearRepresentation.sem`. -/
noncomputable def recPrevariety [Fintype α] : EffectivePrevariety α := by
  let carrier : Submodule ℚ (Series α) := Submodule.span ℚ {f | IsRecognisable α f}
  have hcloseL : ∀ a, map (leftDerivLin a) carrier ≤ carrier := by
    intro a
    rw [show carrier = Submodule.span ℚ {f | IsRecognisable α f} from rfl]
    exact (map_span_le (leftDerivLin a) {f | IsRecognisable α f}
        (Submodule.span ℚ {f | IsRecognisable α f})).2
      (fun f hf => by
        rw [leftDerivLin_apply]
        exact Submodule.mem_span_of_mem (Set.mem_ofPred.mpr (RecognisableLeftDeriv a f hf)))
  have hcloseR : ∀ a, map (rightDerivLin a) carrier ≤ carrier := by
    intro a
    rw [show carrier = Submodule.span ℚ {f | IsRecognisable α f} from rfl]
    exact (map_span_le (rightDerivLin a) {f | IsRecognisable α f}
        (Submodule.span ℚ {f | IsRecognisable α f})).2
      (fun f hf => by
        rw [rightDerivLin_apply]
        exact Submodule.mem_span_of_mem (Set.mem_ofPred.mpr (RecognisableRightDeriv a f hf)))
  let prevariety : Prevariety α :=
    { carrier := carrier
      closedLeftDeriv := by
        intro f hf a
        rw [← leftDerivLin_apply]
        exact (hcloseL a) (Submodule.mem_map_of_mem hf)
      closedRightDeriv := by
        intro f hf a
        rw [← rightDerivLin_apply]
        exact (hcloseR a) (Submodule.mem_map_of_mem hf) }
  exact
    { Rep := LinearRepresentation α
      sem := LinearRepresentation.sem
      prevariety := prevariety
      mem := fun r => by
        have h : r.sem ∈ carrier := by
          rw [show carrier = Submodule.span ℚ {f | IsRecognisable α f} from rfl]
          exact Submodule.mem_span_of_mem (Set.mem_ofPred.mpr (semRecognisable r))
        simpa [prevariety, Membership.mem] using h
      zero := { dim := 0, init := 0, final := 0, M := fun _ => 0 }
      add := fun r s => Classical.choose (existsRepAdd r s)
      smul := fun c r => Classical.choose (existsRepSMul c r)
      derivL := fun a r => { dim := r.dim, init := r.init ᵥ* r.M a, final := r.final, M := r.M }
      derivR := fun a r => Classical.choose (existsRepDerivR a r)
      sem_zero := by
        ext w
        simp [LinearRepresentation.sem, LinearRepresentation.Mword]
      sem_add := fun r s => Classical.choose_spec (existsRepAdd r s)
      sem_smul := fun c r => Classical.choose_spec (existsRepSMul c r)
      sem_derivL := fun a r => semDerivL a r
      sem_derivR := fun a r => Classical.choose_spec (existsRepDerivR a r)
      decEq := fun r s => by
        let d := Classical.choose (RecognisableEqualityDecidable (α := α))
        have hd : ∀ r, d r = true ↔ r.sem = 0 :=
          Classical.choose_spec (RecognisableEqualityDecidable (α := α))
        have hsub : IsRecognisable α (r.sem - s.sem) := by
          have hneg : IsRecognisable α (-1 • s.sem) := recognisableSMul (-1) (s.sem) (semRecognisable s)
          simpa [sub_eq_add_neg] using recognisableAdd (r.sem) (-1 • s.sem) (semRecognisable r) hneg
        let t := Classical.choose hsub
        have ht : t.sem = r.sem - s.sem := Classical.choose_spec hsub
        have hiff : d t = true ↔ r.sem = s.sem := by
          constructor
          · intro h
            have ht0 : t.sem = 0 := (hd t).mp h
            have h0 : r.sem - s.sem = 0 := by rw [ht] at ht0; exact ht0
            rw [← sub_eq_zero]
            exact h0
          · intro h
            have h0 : r.sem - s.sem = 0 := by rw [h, sub_self]
            have ht0 : t.sem = 0 := by rw [ht]; exact h0
            exact (hd t).mpr ht0
        exact decidable_of_decidable_of_iff hiff }

/--
---
conclusion: Lax619925.Recognisable.RecognisableEffectivePrevariety
---
The class of recognisable (= linearly finite) series is an effective prevariety
(paper §4, theorem).  The presentations are linear representations, so the image of the
semantics of `recPrevariety` is exactly the recognisable series; the closure and
decidability content is carried by the construction of `recPrevariety`.
-/
theorem RecognisableEffectivePrevariety [Fintype α] :
    ∃ P : EffectivePrevariety α, ∀ f, IsRecognisable α f ↔ ∃ r : P.Rep, P.sem r = f := by
  use recPrevariety
  intro f
  dsimp only [recPrevariety, IsRecognisable]
  exact Iff.rfl

/--
---
conclusion: Lax619925.Recognisable.RecognisableCommutativityDecidable
---
The commutativity problem is decidable for recognisable series over a finite alphabet
(paper §4).  This is the meta-theorem (`EffectivePrevarietyCommutativityDecidable`)
applied to `recPrevariety`, the effective prevariety of recognisable series: its boolean
decider on a presentation `r` decides `IsCommutative (recPrevariety.sem r)`, and since
`recPrevariety.sem r = r.sem`, it decides `IsCommutative (r.sem)`.
-/
theorem RecognisableCommutativityDecidable [Fintype α] :
    ∃ d : LinearRepresentation α → Bool, ∀ r, d r = true ↔ IsCommutative α (r.sem) := by
  obtain ⟨d, hd⟩ := EffectivePrevarietyCommutativityDecidable (α := α) recPrevariety
  refine ⟨fun (r : LinearRepresentation α) => d r, fun r => ?_⟩
  -- `hd r` states `d r = true ↔ IsCommutative (recPrevariety.sem r)`; `recPrevariety.sem`
  -- unfolds to `LinearRepresentation.sem` (= `r.sem`), so `hd r` is the goal.
  have hsem : recPrevariety.sem r = r.sem := by dsimp only [recPrevariety]
  simpa [hsem] using hd r

end Lax619925Proofs.Recognisable
