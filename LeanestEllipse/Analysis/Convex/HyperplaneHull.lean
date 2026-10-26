import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

/-!
# Hyperplanes meeting a set and its convex hull

This file collects the convex-geometric facts behind [Hägg, Remark 2] (*connected data sets*):
the ellipse criterion extends from open convex data sets `D₀` to connected sets `D₀` that are
not contained in a line, because

* a preconnected set `S` and its convex hull meet exactly the same hyperplanes
  (`IsPreconnected.exists_inner_eq_iff_convexHull`): the values of a continuous linear functional
  on a preconnected set form an interval;
* in finite dimension, a set not contained in any affine hyperplane has a convex hull with
  nonempty interior (`interior_convexHull_nonempty_iff_forall_not_subset_hyperplane`, a
  reformulation of Mathlib's `interior_convexHull_nonempty_iff_affineSpan_eq_top`; in the plane,
  `interior_convexHull_nonempty_of_not_collinear`);
* for such sets `closure (interior (convexHull ℝ S)) = closure (convexHull ℝ S)`
  (`closure_interior_convexHull`), so that `closure S ⊆ closure (interior (convexHull ℝ S))`;
* `interior (convexHull ℝ S)` is open and convex (`isOpen_interior`,
  `convex_interior_convexHull`), and bounded if `S` is (`Bornology.IsBounded.interior_convexHull`).

The convex hull of an open set is open: this is Mathlib's `IsOpen.convexHull`.

## References

* C. Hägg, *An ellipse criterion for exact nonuniqueness in the planar interior Radon problem*.
-/

open Set Bornology
open scoped RealInnerProductSpace

/-! ### Preconnected sets and their convex hulls meet the same hyperplanes -/

section TopologicalVectorSpace

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] {S : Set E}

/-- A linear functional which is continuous on a preconnected set `S` takes the same values on
`S` and on its convex hull: its image of `S` is a preconnected, hence convex, subset of `ℝ`. -/
theorem IsPreconnected.image_convexHull (hS : IsPreconnected S) (f : E →ₗ[ℝ] ℝ)
    (hf : ContinuousOn f S) : f '' convexHull ℝ S = f '' S := by
  rw [f.image_convexHull, (hS.image f hf).convex.convexHull_eq]

end TopologicalVectorSpace

section InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {S : Set E}

/-- The linear functional `x ↦ ⟪x, ω⟫`. -/
private def innerLeft (ω : E) : E →ₗ[ℝ] ℝ where
  toFun x := ⟪x, ω⟫
  map_add' x y := inner_add_left x y ω
  map_smul' c x := real_inner_smul_left x ω c

/-- A preconnected set and its convex hull have the same projections onto every line. -/
theorem IsPreconnected.image_inner_convexHull (hS : IsPreconnected S) (ω : E) :
    (fun x ↦ ⟪x, ω⟫) '' convexHull ℝ S = (fun x ↦ ⟪x, ω⟫) '' S :=
  hS.image_convexHull (innerLeft ω) (continuous_id.inner continuous_const).continuousOn

/-- **Connected data sets** [Hägg, Remark 2]: a preconnected set and its convex hull meet exactly
the same hyperplanes `{x | ⟪x, ω⟫ = p}`. -/
theorem IsPreconnected.exists_inner_eq_iff_convexHull (hS : IsPreconnected S) (ω : E) (p : ℝ) :
    (∃ x ∈ S, ⟪x, ω⟫ = p) ↔ ∃ x ∈ convexHull ℝ S, ⟪x, ω⟫ = p := by
  have h := congrArg (p ∈ ·) (hS.image_inner_convexHull ω)
  simp only [mem_image, eq_iff_iff] at h
  exact h.symm

/-! ### Sets not contained in a hyperplane -/

/-- A set spans the whole space affinely iff it is nonempty and not contained in any affine
hyperplane `{x | ⟪x, ω⟫ = p}` (`ω ≠ 0`).  (Finite dimension is used for `←`: a proper subspace
has a nonzero normal vector.) -/
theorem affineSpan_eq_top_iff_forall_not_subset_hyperplane [FiniteDimensional ℝ E] :
    affineSpan ℝ S = ⊤ ↔
      S.Nonempty ∧ ∀ ω : E, ω ≠ 0 → ∀ p : ℝ, ¬ S ⊆ {x | ⟪x, ω⟫ = p} := by
  constructor
  · intro h
    refine ⟨AffineSubspace.nonempty_of_affineSpan_eq_top ℝ E E h, fun ω hω p hSp ↦ hω ?_⟩
    have hspan : vectorSpan ℝ S ≤ LinearMap.ker (innerLeft ω) := by
      rw [vectorSpan_def, Submodule.span_le]
      rintro _ ⟨x, hx, y, hy, rfl⟩
      change ⟪x -ᵥ y, ω⟫ = 0
      rw [vsub_eq_sub, inner_sub_left, hSp hx, hSp hy, sub_self]
    rw [AffineSubspace.vectorSpan_eq_top_of_affineSpan_eq_top ℝ E E h, top_le_iff] at hspan
    have hω' : ω ∈ LinearMap.ker (innerLeft ω) := hspan ▸ Submodule.mem_top
    rw [LinearMap.mem_ker] at hω'
    exact inner_self_eq_zero.mp hω'
  · rintro ⟨⟨x₀, hx₀⟩, hS⟩
    by_contra htop
    rw [AffineSubspace.affineSpan_eq_top_iff_vectorSpan_eq_top_of_nonempty ℝ E E ⟨x₀, hx₀⟩,
      ← Submodule.orthogonal_eq_bot_iff] at htop
    obtain ⟨ω, hωV, hω⟩ := Submodule.exists_mem_ne_zero_of_ne_bot htop
    refine hS ω hω ⟪x₀, ω⟫ fun x hx ↦ ?_
    have h := (Submodule.mem_orthogonal _ ω).mp hωV (x -ᵥ x₀) (vsub_mem_vectorSpan ℝ hx hx₀)
    rw [vsub_eq_sub, inner_sub_left, sub_eq_zero] at h
    exact h

/-- In finite dimension, the convex hull of a set has nonempty interior iff the set is nonempty
and not contained in any affine hyperplane `{x | ⟪x, ω⟫ = p}` (`ω ≠ 0`)
[Hägg, Remark 2]. -/
theorem interior_convexHull_nonempty_iff_forall_not_subset_hyperplane [FiniteDimensional ℝ E] :
    (interior (convexHull ℝ S)).Nonempty ↔
      S.Nonempty ∧ ∀ ω : E, ω ≠ 0 → ∀ p : ℝ, ¬ S ⊆ {x | ⟪x, ω⟫ = p} := by
  rw [interior_convexHull_nonempty_iff_affineSpan_eq_top,
    affineSpan_eq_top_iff_forall_not_subset_hyperplane]

/-- In a nontrivial finite dimensional space, a set which is not contained in any affine
hyperplane `{x | ⟪x, ω⟫ = p}` (`ω ≠ 0`) has a convex hull with nonempty interior
[Hägg, Remark 2].  (Nontriviality only excludes `S = ∅` in the zero space.) -/
theorem interior_convexHull_nonempty_of_forall_not_subset_hyperplane [FiniteDimensional ℝ E]
    [Nontrivial E] (h : ∀ ω : E, ω ≠ 0 → ∀ p : ℝ, ¬ S ⊆ {x | ⟪x, ω⟫ = p}) :
    (interior (convexHull ℝ S)).Nonempty := by
  refine interior_convexHull_nonempty_iff_forall_not_subset_hyperplane.mpr ⟨?_, h⟩
  rw [nonempty_iff_ne_empty]
  rintro rfl
  obtain ⟨ω, hω⟩ := exists_ne (0 : E)
  exact h ω hω 0 (empty_subset _)

end InnerProductSpace

/-- In a two-dimensional real normed space, a set which is not contained in a line (i.e. is not
collinear) has a convex hull with nonempty interior [Hägg, Remark 2]. -/
theorem interior_convexHull_nonempty_of_not_collinear {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (hE : Module.finrank ℝ E = 2) {S : Set E}
    (hS : ¬ Collinear ℝ S) : (interior (convexHull ℝ S)).Nonempty := by
  rw [interior_convexHull_nonempty_iff_affineSpan_eq_top]
  have hne : S.Nonempty := by
    rw [nonempty_iff_ne_empty]
    rintro rfl
    exact hS (collinear_empty ℝ E)
  have hdim : 1 < Module.finrank ℝ (vectorSpan ℝ S) :=
    lt_of_not_ge fun h ↦ hS (collinear_iff_finrank_le_one.mpr h)
  have htop : vectorSpan ℝ S = ⊤ := by
    by_contra h
    have := Submodule.finrank_lt h
    omega
  rw [← direction_affineSpan] at htop
  exact (AffineSubspace.direction_eq_top_iff_of_nonempty (hne.mono (subset_affineSpan ℝ S))).mp
    htop

/-! ### The interior of the convex hull -/

section Interior

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] {S : Set E}

/-- The interior of a convex hull is convex. -/
theorem convex_interior_convexHull (S : Set E) : Convex ℝ (interior (convexHull ℝ S)) :=
  (convex_convexHull ℝ S).interior

/-- If the convex hull of `S` has nonempty interior, then the closure of this interior is the
closure of the convex hull [Hägg, Remark 2]. -/
theorem closure_interior_convexHull (h : (interior (convexHull ℝ S)).Nonempty) :
    closure (interior (convexHull ℝ S)) = closure (convexHull ℝ S) :=
  (convex_convexHull ℝ S).closure_interior_eq_closure_of_nonempty_interior h

/-- If the convex hull of `S` has nonempty interior, then `S` lies in the closure of this
interior. -/
theorem closure_subset_closure_interior_convexHull (h : (interior (convexHull ℝ S)).Nonempty) :
    closure S ⊆ closure (interior (convexHull ℝ S)) := by
  rw [closure_interior_convexHull h]
  exact closure_mono (subset_convexHull ℝ S)

end Interior

/-- The interior of the convex hull of a bounded set is bounded. -/
theorem Bornology.IsBounded.interior_convexHull {E : Type*} [SeminormedAddCommGroup E]
    [NormedSpace ℝ E] {S : Set E} (hS : IsBounded S) : IsBounded (interior (convexHull ℝ S)) :=
  (isBounded_convexHull.mpr hS).subset interior_subset
