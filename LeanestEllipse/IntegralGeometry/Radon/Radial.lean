import LeanestEllipse.IntegralGeometry.Radon.Plane
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection

/-!
# Radon transforms of radial functions

For a unit vector `ω` of a finite dimensional real inner product space `E`, the points
`p • ω + y`, `y ∈ (ℝ ∙ ω)ᗮ`, of the hyperplane `{x | ⟪x, ω⟫ = p}` have squared norm
`p ^ 2 + ‖y‖ ^ 2`.  Hence the Radon transform of a radial function `x ↦ Ψ (‖x‖ ^ 2)` is

`radonTransform (fun x ↦ Ψ (‖x‖ ^ 2)) ω p = ∫ y : (ℝ ∙ ω)ᗮ, Ψ (p ^ 2 + ‖y‖ ^ 2)`,

and in the plane it is the one-dimensional integral `∫ t, Ψ (p ^ 2 + t ^ 2)` (a profile
integral of Abel type, see `LeanestEllipse.IntegralGeometry.Radon.Abel`).  The Radon transform of a
radial function does not depend on the direction.

## Main results

* `radonTransform_comp_norm_sq`: the Radon transform of `x ↦ Ψ (‖x‖ ^ 2)` as an integral over
  the hyperplane `(ℝ ∙ ω)ᗮ`;
* `radonTransform_eq_of_norm_eq`: for a radial function (`‖x‖ = ‖y‖ → f x = f y`), the Radon
  transform in direction `ω` only depends on `‖ω‖`;
* `exists_norm_eq_one_inner_eq_zero_of_finrank_eq_two`: in the plane, every nonzero vector has a
  unit normal;
* `radonTransform_comp_norm_sq_eq_integral`: in the plane,
  `radonTransform (fun x ↦ Ψ (‖x‖ ^ 2)) ω p = ∫ t, Ψ (p ^ 2 + t ^ 2)`.
-/

open MeasureTheory Set Submodule
open scoped RealInnerProductSpace

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

section General

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

namespace RadonTransform

/-- **Pythagoras on a hyperplane**: for a unit vector `ω` and `y ∈ (ℝ ∙ ω)ᗮ`,
`‖p • ω + y‖ ^ 2 = p ^ 2 + ‖y‖ ^ 2`. -/
theorem norm_smul_add_sq {ω : E} (hω : ‖ω‖ = 1) (p : ℝ) (y : (ℝ ∙ ω)ᗮ) :
    ‖p • ω + (y : E)‖ ^ 2 = p ^ 2 + ‖y‖ ^ 2 := by
  have h : ⟪p • ω, (y : E)⟫ = 0 := by
    rw [real_inner_smul_left, real_inner_comm, inner_orthogonal_eq_zero, mul_zero]
  have := norm_add_sq_eq_norm_sq_add_norm_sq_real h
  rw [norm_smul, hω, mul_one, Real.norm_eq_abs] at this
  have hy : ‖y‖ = ‖(y : E)‖ := rfl
  rw [hy]
  nlinarith [sq_abs p]

end RadonTransform

open RadonTransform

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- **Radon transform of a radial function**: for a unit vector `ω`,
`radonTransform (fun x ↦ Ψ (‖x‖ ^ 2)) ω p = ∫ y : (ℝ ∙ ω)ᗮ, Ψ (p ^ 2 + ‖y‖ ^ 2)`. -/
theorem radonTransform_comp_norm_sq (Ψ : ℝ → F) {ω : E} (hω : ‖ω‖ = 1) (p : ℝ) :
    radonTransform (fun x ↦ Ψ (‖x‖ ^ 2)) ω p = ∫ y : (ℝ ∙ ω)ᗮ, Ψ (p ^ 2 + ‖y‖ ^ 2) := by
  simp only [radonTransform, norm_smul_add_sq hω]

/-- **The Radon transform of a radial function does not depend on the direction**: if
`f x = f y` whenever `‖x‖ = ‖y‖`, then `radonTransform f ω p = radonTransform f ω' p` for
`‖ω‖ = ‖ω'‖` (the reflection in `(ℝ ∙ (ω - ω'))ᗮ` maps `ω` to `ω'` and preserves `f`). -/
theorem radonTransform_eq_of_norm_eq {f : E → F} (hf : ∀ x y, ‖x‖ = ‖y‖ → f x = f y)
    {ω ω' : E} (h : ‖ω‖ = ‖ω'‖) (p : ℝ) : radonTransform f ω p = radonTransform f ω' p := by
  set L : E ≃ₗᵢ[ℝ] E := (ℝ ∙ (ω - ω'))ᗮ.reflection
  have hL : L ω = ω' := Submodule.reflection_sub h
  have hfL : f ∘ L = f := funext fun x ↦ hf _ _ (L.norm_map x)
  rw [← hL, ← radonTransform_comp_linearIsometryEquiv L f ω p, hfL]

/-- The Radon transform of `x ↦ Ψ (‖x‖ ^ 2)` does not depend on the (unit) direction. -/
theorem radonTransform_comp_norm_sq_eq (Ψ : ℝ → F) {ω ω' : E} (h : ‖ω‖ = ‖ω'‖) (p : ℝ) :
    radonTransform (fun x ↦ Ψ (‖x‖ ^ 2)) ω p = radonTransform (fun x ↦ Ψ (‖x‖ ^ 2)) ω' p :=
  radonTransform_eq_of_norm_eq (fun x y hxy ↦ by simp only [hxy]) h p

end General

section TwoDim

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fact (Module.finrank ℝ E = 2)] [MeasurableSpace E] [BorelSpace E]

attribute [local instance] FiniteDimensional.of_fact_finrank_eq_two

omit [MeasurableSpace E] [BorelSpace E] in
/-- In the plane, every nonzero vector `ω` has a unit normal `τ`: `‖τ‖ = 1` and `⟪ω, τ⟫ = 0`. -/
theorem exists_norm_eq_one_inner_eq_zero_of_finrank_eq_two {ω : E} (hω : ω ≠ 0) :
    ∃ τ : E, ‖τ‖ = 1 ∧ ⟪ω, τ⟫ = 0 := by
  have : Fact (Module.finrank ℝ E = 1 + 1) := ⟨(Fact.out : Module.finrank ℝ E = 2)⟩
  have hK : Module.finrank ℝ (ℝ ∙ ω)ᗮ = 1 := Submodule.finrank_orthogonal_span_singleton hω
  have hne : (ℝ ∙ ω)ᗮ ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hK
    exact zero_ne_one hK
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  refine ⟨‖v‖⁻¹ • v, ?_, ?_⟩
  · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 hv0)]
  · rw [real_inner_smul_right, (Submodule.mem_orthogonal_singleton_iff_inner_right).1 hv,
      mul_zero]

/-- **Radon transform of a radial function in the plane**: for a unit vector `ω`,
`radonTransform (fun x ↦ Ψ (‖x‖ ^ 2)) ω p = ∫ t, Ψ (p ^ 2 + t ^ 2)`. -/
theorem radonTransform_comp_norm_sq_eq_integral (Ψ : ℝ → F) {ω : E} (hω : ‖ω‖ = 1) (p : ℝ) :
    radonTransform (fun x ↦ Ψ (‖x‖ ^ 2)) ω p = ∫ t : ℝ, Ψ (p ^ 2 + t ^ 2) := by
  obtain ⟨τ, hτ, hωτ⟩ := exists_norm_eq_one_inner_eq_zero_of_finrank_eq_two
    (norm_ne_zero_iff.1 (by rw [hω]; exact one_ne_zero))
  rw [radonTransform_eq_integral_line hω hτ hωτ]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t ↦ ?_)
  have h : ⟪p • ω, t • τ⟫ = 0 := by
    rw [real_inner_smul_left, real_inner_smul_right, hωτ, mul_zero, mul_zero]
  have := norm_add_sq_eq_norm_sq_add_norm_sq_real h
  rw [norm_smul, norm_smul, hω, hτ, mul_one, mul_one, Real.norm_eq_abs, Real.norm_eq_abs] at this
  have hsq : ‖p • ω + t • τ‖ ^ 2 = p ^ 2 + t ^ 2 := by nlinarith [sq_abs p, sq_abs t]
  simp only [hsq]

end TwoDim

end
