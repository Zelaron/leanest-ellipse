import LeanestEllipse.IntegralGeometry.Radon.FourierSlice
import LeanestEllipse.IntegralGeometry.Radon.Backprojection
import LeanestEllipse.MeasureTheory.Constructions.SignedRadial
import LeanestEllipse.Analysis.Fourier.Laplacian

/-!
# Odd-dimensional Radon inversion

For a smooth compactly supported function on a real inner product space of dimension
`2k + 1`, every power of the negative Laplacian can be moved through the Fourier integral
for backprojection. Signed polar coordinates then give

`f = (2 * (2π)^(2k))⁻¹ • (-Δ)^k (radonBackprojection (radonTransform f))`.

Hyperplanes carry the Euclidean volume induced by orthonormal coordinates, and the full
unit sphere carries `volume.toSphere`. The factor two accounts for both orientations of
one hyperplane. The result applies to arbitrary complex Banach-valued functions. All
integrability and regularity requirements are derived from smooth compact support.
-/

open MeasureTheory Set Metric Real
open scoped RealInnerProductSpace FourierTransform SchwartzMap

noncomputable section

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

omit [CompleteSpace F] in
/-- Every norm-power weighted Schwartz function is integrable against a temperate measure. -/
theorem SchwartzMap.integrable_norm_pow_smul (g : 𝓢(E, F)) (μ : Measure E)
    [μ.HasTemperateGrowth] (n : ℕ) : Integrable (fun ξ ↦ ‖ξ‖ ^ n • g ξ) μ := by
  refine (g.integrable_pow_mul μ n).mono'
    ((continuous_norm.pow n).aestronglyMeasurable.smul g.continuous.aestronglyMeasurable) ?_
  filter_upwards [] with ξ
  simp [norm_smul]

/-- Backprojection of smooth compactly supported Radon data is an inverse Fourier integral
with the signed radial frequency measure. -/
theorem radonBackprojection_radonTransform_eq_inverseFourierIntegral {f : E → F}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f) :
    radonBackprojection (radonTransform f) = VectorFourier.inverseFourierIntegral
      (Measure.signedRadial (volume : Measure E).toSphere) (𝓕 f) := by
  let σ := (volume : Measure E).toSphere
  let ν := Measure.signedRadial σ
  let g := hc.toSchwartzMap hf
  have hν : Integrable (𝓕 f) ν := (𝓕 g).integrable
  ext x
  have hmod : Integrable (fun ξ ↦ 𝐞 (-(-innerSL ℝ) ξ x) • 𝓕 f ξ) ν :=
    (Real.fourierIntegral_convergent_iff' (-innerSL ℝ) x).2 hν
  have hcomp := hmod.comp_measurable Measure.continuous_signedRadialPoint.measurable
  change Integrable (fun z : sphere (0 : E) 1 × ℝ ↦
    𝐞 (-(-innerSL ℝ) (Measure.signedRadialPoint z) x) •
      𝓕 f (Measure.signedRadialPoint z)) (σ.prod volume) at hcomp
  change radonBackprojection (radonTransform f) x =
    ∫ ξ, 𝐞 (-(-innerSL ℝ) ξ x) • 𝓕 f ξ ∂ν
  rw [show ν = Measure.map Measure.signedRadialPoint (σ.prod volume) from rfl,
    integral_map Measure.continuous_signedRadialPoint.measurable.aemeasurable
      hmod.aestronglyMeasurable,
    integral_prod _ hcomp]
  unfold radonBackprojection
  apply integral_congr_ae
  filter_upwards [] with ω
  rw [← fourierInv_slice_eq_radonTransform_of_contDiff hf hc (by simp) ⟪x, (ω : E)⟫,
    Real.fourierInv_eq]
  apply integral_congr_ae
  filter_upwards [] with s
  congr 1
  congr 1
  change ⟪s, ⟪x, (ω : E)⟫⟫ = -(-innerSL ℝ) (s • (ω : E)) x
  simp [real_inner_comm, innerSL_apply_apply, mul_comm]

/-- Backprojection of the Radon data of a smooth compactly supported function is smooth. -/
theorem contDiff_radonBackprojection_radonTransform {f : E → F}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f) :
    ContDiff ℝ (⊤ : ℕ∞) (radonBackprojection (radonTransform f)) := by
  rw [radonBackprojection_radonTransform_eq_inverseFourierIntegral hf hc]
  let g := hc.toSchwartzMap hf
  let ν := Measure.signedRadial (volume : Measure E).toSphere
  exact VectorFourier.contDiff_inverseFourierIntegral (μ := ν)
    (fun n _ ↦ (𝓕 g).integrable_pow_mul ν n)

/-- **Odd-dimensional Radon inversion**, with the full oriented-sphere normalization.
The dimension condition also includes dimension one (`k = 0`). -/
theorem radon_inversion_odd {f : E → F}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f)
    (k : ℕ) (hdim : Module.finrank ℝ E = 2 * k + 1) (x : E) :
    f x = (2 * (2 * Real.pi) ^ (2 * k))⁻¹ •
      ((fun g : E → F ↦ -Laplacian.laplacian g)^[k]
        (radonBackprojection (radonTransform f))) x := by
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (M := E) (by omega)
  let σ := (volume : Measure E).toSphere
  let ν := Measure.signedRadial σ
  let g := hc.toSchwartzMap hf
  have hnorm (n : ℕ) : Integrable (fun ξ ↦ ‖ξ‖ ^ n * ‖𝓕 f ξ‖) ν :=
    (𝓕 g).integrable_pow_mul ν n
  have hm : AEStronglyMeasurable (𝓕 f) ν := (𝓕 g).continuous.aestronglyMeasurable
  have hinv : 𝓕⁻ (𝓕 f) = f :=
    hf.continuous.fourierInv_fourier_eq g.integrable (𝓕 g).integrable
  have hpolar (x : E) :
      VectorFourier.inverseFourierIntegral ν (fun ξ ↦ ‖ξ‖ ^ (2 * k) • 𝓕 f ξ) x =
        (2 : ℝ) • 𝓕⁻ (𝓕 f) x := by
    let q : E → F := fun ξ ↦ 𝐞 ⟪ξ, x⟫ • 𝓕 f ξ
    have hw : Integrable (fun ξ ↦ ‖ξ‖ ^ (2 * k) • 𝓕 f ξ) ν :=
      (𝓕 g).integrable_norm_pow_smul ν (2 * k)
    have hwm := (Real.fourierIntegral_convergent_iff' (-innerSL ℝ) x).2 hw
    have heq (ξ : E) : 𝐞 (-(-innerSL ℝ) ξ x) • (‖ξ‖ ^ (2 * k) • 𝓕 f ξ) =
        ‖ξ‖ ^ (Module.finrank ℝ E - 1) • q ξ := by
      simp only [hdim, Nat.add_sub_cancel, q, neg_apply, innerSL_apply_apply, neg_neg]
      exact smul_comm _ _ _
    have hwm' : Integrable (fun ξ ↦ ‖ξ‖ ^ (Module.finrank ℝ E - 1) • q ξ) ν :=
      hwm.congr (Filter.Eventually.of_forall heq)
    change (∫ ξ, 𝐞 (-(-innerSL ℝ) ξ x) • (‖ξ‖ ^ (2 * k) • 𝓕 f ξ) ∂ν) = _
    rw [integral_congr_ae (Filter.Eventually.of_forall heq)]
    rw [Measure.integral_signedRadial q hwm']
    rw [Real.fourierInv_eq]
  have hidentity :
      ((fun g : E → F ↦ -Laplacian.laplacian g)^[k]
        (radonBackprojection (radonTransform f))) =
          (2 * (2 * Real.pi) ^ (2 * k)) • f := by
    rw [radonBackprojection_radonTransform_eq_inverseFourierIntegral hf hc,
      VectorFourier.iterate_neg_laplacian_inverseFourierIntegral hnorm hm k]
    ext y
    change (2 * Real.pi) ^ (2 * k) •
      VectorFourier.inverseFourierIntegral ν (fun ξ ↦ ‖ξ‖ ^ (2 * k) • 𝓕 f ξ) y = _
    rw [hpolar, hinv]
    simp [smul_smul, mul_comm]
  rw [hidentity, Pi.smul_apply, smul_smul, inv_mul_cancel₀ (by positivity), one_smul]

