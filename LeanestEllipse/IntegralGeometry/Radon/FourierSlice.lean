import LeanestEllipse.IntegralGeometry.Radon.Continuous
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

/-!
# Fourier slices in Mathlib's normalization

The basic Radon API uses the article's exponential `exp (-i s p)`. Here the slice identity
is expressed using Mathlib's Fourier transform, with exponential `exp (-2π i s p)`, and
combined with one-dimensional Fourier inversion.

These are dimension-independent prerequisites for the odd-dimensional inversion formula.
The general inverse-slice identity records its integrability and continuity assumptions;
for smooth compactly supported functions those assumptions are proved here.
-/

open MeasureTheory
open scoped FourierTransform RealInnerProductSpace SchwartzMap

noncomputable section

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- **Fourier-slice identity**, in Mathlib's `2π` normalization. -/
theorem fourier_radonTransform {f : E → F} (hf : Integrable f) {ω : E} (hω : ‖ω‖ = 1)
    (s : ℝ) : 𝓕 (radonTransform f ω) s = 𝓕 f (s • ω) := by
  rw [Real.fourier_real_eq_integral_exp_smul, Real.fourier_eq']
  convert integral_exp_smul_radonTransform hf hω (2 * Real.pi * s) using 1
  · apply integral_congr_ae
    filter_upwards [] with p
    congr 2
    push_cast
    ring
  · apply integral_congr_ae
    filter_upwards [] with x
    rw [real_inner_smul_right]
    congr 2
    push_cast
    ring

/-- Inverting a Fourier slice reconstructs the Radon profile at its continuity points.
The two integrability requirements are explicit; integrability of `f` alone does not imply
integrability of the Fourier slice. -/
theorem fourierInv_slice_eq_radonTransform {f : E → F}
    (hf : Integrable f) {ω : E} (hω : ‖ω‖ = 1)
    (hslice : Integrable (fun s : ℝ ↦ 𝓕 f (s • ω))) {p : ℝ}
    (hp : ContinuousAt (radonTransform f ω) p) :
    𝓕⁻ (fun s : ℝ ↦ 𝓕 f (s • ω)) p = radonTransform f ω p := by
  have heq : (fun s : ℝ ↦ 𝓕 f (s • ω)) = 𝓕 (radonTransform f ω) :=
    funext fun s ↦ (fourier_radonTransform hf hω s).symm
  rw [heq] at hslice ⊢
  exact (integrable_radonTransform hf hω).fourierInv_fourier_eq hslice hp

omit [CompleteSpace F] in
/-- Every Fourier slice of a Schwartz function is integrable. -/
theorem SchwartzMap.integrable_fourier_slice (f : 𝓢(E, F)) {ω : E} (hω : ‖ω‖ = 1) :
    Integrable (fun s : ℝ ↦ 𝓕 (f : E → F) (s • ω)) := by
  let L := LinearIsometry.toSpanSingleton ℝ E hω
  let g : 𝓢(ℝ, F) := SchwartzMap.compCLMOfAntilipschitz ℂ
    L.toContinuousLinearMap.hasTemperateGrowth L.isometry.antilipschitzWith (𝓕 f)
  exact g.integrable

/-- Fourier inversion along every unit normal reconstructs the complete Radon profile of
a smooth compactly supported function. -/
theorem fourierInv_slice_eq_radonTransform_of_contDiff {f : E → F}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f)
    {ω : E} (hω : ‖ω‖ = 1) (p : ℝ) :
    𝓕⁻ (fun s : ℝ ↦ 𝓕 f (s • ω)) p = radonTransform f ω p := by
  let g := hc.toSchwartzMap hf
  exact fourierInv_slice_eq_radonTransform (hf.continuous.integrable_of_hasCompactSupport hc)
    hω (g.integrable_fourier_slice hω) (hf.continuous.radonTransform hc ω).continuousAt
