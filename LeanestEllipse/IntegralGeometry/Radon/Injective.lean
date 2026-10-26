import LeanestEllipse.IntegralGeometry.Radon.Basic
import LeanestEllipse.Analysis.Fourier.L1Injective
import Mathlib.MeasureTheory.Constructions.HaarToSphere

/-!
# Injectivity of the Radon transform on `L¹`

If the Radon transform of an integrable function vanishes (almost everywhere in the offset) for
almost every direction — with respect to the surface measure `volume.toSphere` on the unit
sphere — then the function vanishes almost everywhere.

The proof follows [Hägg, proof of Proposition 11]: the Fourier slice identity shows that the
Fourier transform of `f` vanishes on every radial line through a direction in a set of full, hence
dense, measure; continuity of the Fourier transform and uniqueness on `L¹` conclude.
-/

open MeasureTheory Set Filter Metric
open scoped RealInnerProductSpace

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- If `p ↦ 𝓡 f ω p` vanishes almost everywhere, the Fourier transform of `f` vanishes on the
line `ℝ ω`. -/
theorem integral_exp_inner_mul_eq_zero_of_radonTransform_ae_eq_zero {f : E → ℂ}
    (hf : Integrable f) {ω : E} (hω : ‖ω‖ = 1) (h : radonTransform f ω =ᵐ[volume] 0) (s : ℝ) :
    ∫ x, Complex.exp (-(⟪x, s • ω⟫ : ℝ) * Complex.I) * f x = 0 := by
  have hslice := integral_exp_smul_radonTransform hf hω s
  simp only [smul_eq_mul] at hslice
  simp_rw [real_inner_smul_right]
  rw [← hslice]
  refine integral_eq_zero_of_ae ?_
  filter_upwards [h] with p hp
  simp [hp]

/-- **Injectivity of the Radon transform on `L¹`.**  If for almost every unit vector `ω`
(with respect to the surface measure of the sphere) the Radon transform `p ↦ 𝓡 f ω p` vanishes
almost everywhere, then `f = 0` almost everywhere. -/
theorem ae_eq_zero_of_ae_radonTransform_ae_eq_zero [Nontrivial E] {f : E → ℂ}
    (hf : Integrable f)
    (h : ∀ᵐ ω : sphere (0 : E) 1 ∂(volume : Measure E).toSphere,
      radonTransform f (ω : E) =ᵐ[volume] 0) :
    f =ᵐ[volume] 0 := by
  set F : E → ℂ := fun ξ ↦ ∫ x, Complex.exp (-(⟪x, ξ⟫ : ℝ) * Complex.I) * f x
  have hFcont : Continuous F := by
    simpa only [F, smul_eq_mul] using continuous_integral_exp_inner_smul hf
  -- the good directions are dense in the sphere
  have hdense : Dense {ω : sphere (0 : E) 1 | radonTransform f (ω : E) =ᵐ[volume] 0} :=
    Measure.dense_of_ae h
  have hgood : ∀ ω : sphere (0 : E) 1, radonTransform f (ω : E) =ᵐ[volume] 0 →
      ∀ s : ℝ, F (s • (ω : E)) = 0 := fun ω hω s ↦
    integral_exp_inner_mul_eq_zero_of_radonTransform_ae_eq_zero hf
      (by simp) hω s
  -- hence `F` vanishes on every ray
  have hray : ∀ (ω : sphere (0 : E) 1) (s : ℝ), F (s • (ω : E)) = 0 := by
    intro ω s
    have hclosed : IsClosed {ω : sphere (0 : E) 1 | F (s • (ω : E)) = 0} :=
      isClosed_eq (hFcont.comp (continuous_const.smul continuous_subtype_val)) continuous_const
    have hsub : {ω : sphere (0 : E) 1 | radonTransform f (ω : E) =ᵐ[volume] 0} ⊆
        {ω : sphere (0 : E) 1 | F (s • (ω : E)) = 0} := fun ω hω ↦ hgood ω hω s
    exact (hclosed.closure_subset_iff.mpr hsub) (hdense.closure_eq ▸ Set.mem_univ ω)
  refine ae_eq_zero_of_integral_exp_inner_mul_eq_zero hf fun ξ ↦ ?_
  rcases eq_or_ne ξ 0 with rfl | hξ
  · obtain ⟨v, hv⟩ := exists_ne (0 : E)
    have := hray ⟨‖v‖⁻¹ • v, by simp [norm_smul, hv]⟩ 0
    simpa [F] using this
  · have hmem : ‖ξ‖⁻¹ • ξ ∈ sphere (0 : E) 1 := by
      simp [norm_smul, norm_ne_zero_iff.mpr hξ]
    have := hray ⟨_, hmem⟩ ‖ξ‖
    simpa [F, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hξ)] using this

end
