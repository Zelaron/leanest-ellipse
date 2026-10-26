import LeanestEllipse.IntegralGeometry.Radon.Plane
import LeanestEllipse.IntegralGeometry.Radon.Injective

/-!
# Injectivity of the planar Radon transform in angle coordinates

* `ae_of_ae_restrict_Ico_of_periodic`: a `2π`-periodic property holding for almost every angle
  in one period holds for almost every angle.
* `Complex.ae_eq_zero_of_ae_radonTransform_exp_ae_eq_zero`: if `𝓡 f (e^{iθ}) = 0` almost
  everywhere in the offset for almost every angle `θ`, then `f = 0` almost everywhere
  ([Hägg, proof of Proposition 11]).
-/

open MeasureTheory Set Filter Complex
open scoped Real RealInnerProductSpace

noncomputable section

/-- A `2π`-periodic property holding for almost every angle of `[0, 2π)` holds for almost every
real angle. -/
theorem ae_of_ae_restrict_Ico_of_periodic {P : ℝ → Prop}
    (hP : ∀ (θ : ℝ) (k : ℤ), P (θ + k * (2 * π)) ↔ P θ)
    (h : ∀ᵐ θ ∂(volume.restrict (Ico 0 (2 * π))), P θ) : ∀ᵐ θ : ℝ, P θ := by
  rw [ae_restrict_iff' measurableSet_Ico] at h
  have hk : ∀ k : ℤ, ∀ᵐ θ : ℝ, θ - k * (2 * π) ∈ Ico 0 (2 * π) → P θ := by
    intro k
    have hmp := measurePreserving_sub_right (volume : Measure ℝ) (k * (2 * π))
    filter_upwards [hmp.quasiMeasurePreserving.ae h] with θ hθ hmem
    have := hθ hmem
    rwa [show θ - k * (2 * π) = θ + (-k : ℤ) * (2 * π) by push_cast; ring, hP] at this
  rw [← ae_all_iff] at hk
  filter_upwards [hk] with θ hθ
  obtain ⟨k, hk', -⟩ := existsUnique_sub_zsmul_mem_Ico Real.two_pi_pos θ 0
  refine hθ k ?_
  rw [zsmul_eq_mul, zero_add] at hk'
  exact hk'

namespace Complex

/-- **Injectivity of the planar Radon transform in angle coordinates.**  If for almost every
angle `θ` the Radon transform `p ↦ 𝓡 f (e^{iθ}) p` vanishes almost everywhere, then `f = 0`
almost everywhere. -/
theorem ae_eq_zero_of_ae_radonTransform_exp_ae_eq_zero {f : ℂ → ℂ} (hf : Integrable f)
    (h : ∀ᵐ θ : ℝ, radonTransform f (exp (θ * I)) =ᵐ[volume] 0) : f =ᵐ[volume] 0 := by
  set F : ℂ → ℂ := fun ξ ↦ ∫ x, Complex.exp (-(⟪x, ξ⟫ : ℝ) * Complex.I) * f x
  have hFcont : Continuous F := by
    simpa only [F, smul_eq_mul] using continuous_integral_exp_inner_smul hf
  have hdense : Dense {θ : ℝ | radonTransform f (exp (θ * I)) =ᵐ[volume] 0} :=
    Measure.dense_of_ae h
  have hgood : ∀ θ : ℝ, radonTransform f (exp (θ * I)) =ᵐ[volume] 0 →
      ∀ s : ℝ, F ((s : ℂ) * exp (θ * I)) = 0 := by
    intro θ hθ s
    have := integral_exp_inner_mul_eq_zero_of_radonTransform_ae_eq_zero hf
      (norm_exp_ofReal_mul_I θ) hθ s
    simpa only [F, Complex.real_smul] using this
  have hall : ∀ (θ s : ℝ), F ((s : ℂ) * exp (θ * I)) = 0 := by
    intro θ s
    have hclosed : IsClosed {θ : ℝ | F ((s : ℂ) * exp (θ * I)) = 0} :=
      isClosed_eq (hFcont.comp (by fun_prop)) continuous_const
    exact (hclosed.closure_subset_iff.mpr fun θ hθ ↦ hgood θ hθ s)
      (hdense.closure_eq ▸ mem_univ θ)
  refine ae_eq_zero_of_integral_exp_inner_mul_eq_zero hf fun ξ ↦ ?_
  have := hall (arg ξ) ‖ξ‖
  rwa [Complex.norm_mul_exp_arg_mul_I] at this

end Complex

end
