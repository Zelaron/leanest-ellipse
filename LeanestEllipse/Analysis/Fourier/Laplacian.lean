import LeanestEllipse.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Laplacians of inverse Fourier integrals

These formulas hold for an arbitrary frequency measure. Integrability of the required norm
moments allows differentiation under the integral; each negative Laplacian multiplies the integrand
by `(2π)² ‖ξ‖²`. In particular, the result applies to the signed radial measure used in
odd-dimensional Radon inversion, as well as to ordinary Lebesgue measure.

The range is an arbitrary complex normed space, with its real scalar structure obtained by
restriction of scalars.
-/

open MeasureTheory Real
open scoped RealInnerProductSpace FourierTransform

noncomputable section

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

namespace VectorFourier

/-- The inverse Fourier integral with an arbitrary frequency measure and the `2π` convention. -/
def inverseFourierIntegral (μ : Measure E) (f : E → F) : E → F :=
  fourierIntegral 𝐞 μ (-innerSL ℝ).toLinearMap₁₂ f

/-- Integrable norm moments up to order `N` make the inverse Fourier integral `C^N`. -/
theorem contDiff_inverseFourierIntegral {μ : Measure E} {f : E → F} {N : ℕ∞}
    (hf : ∀ n : ℕ, n ≤ N → Integrable (fun ξ ↦ ‖ξ‖ ^ n * ‖f ξ‖) μ) :
    ContDiff ℝ N (inverseFourierIntegral μ f) :=
  contDiff_fourierIntegral (-innerSL ℝ) hf

set_option maxHeartbeats 800000 in
-- Tracing the multilinear Fourier derivative requires reducing several nested scalar actions.
/-- The negative Laplacian of an inverse Fourier integral is the inverse Fourier integral
with the multiplier `(2π)² ‖ξ‖²`. -/
theorem neg_laplacian_inverseFourierIntegral {μ : Measure E} {f : E → F}
    (hf : ∀ n : ℕ, n ≤ 2 → Integrable (fun ξ ↦ ‖ξ‖ ^ n * ‖f ξ‖) μ)
    (hm : AEStronglyMeasurable f μ) :
    -Laplacian.laplacian (inverseFourierIntegral μ f) =
      (2 * Real.pi) ^ 2 • inverseFourierIntegral μ (fun ξ ↦ ‖ξ‖ ^ 2 • f ξ) := by
  let b := stdOrthonormalBasis ℝ E
  have h₂ : Integrable (fun ξ ↦ fourierPowSMulRight (-innerSL ℝ) f ξ 2) μ :=
    integrable_fourierPowSMulRight (-innerSL ℝ) (hf 2 le_rfl) hm
  have hd : iteratedFDeriv ℝ 2 (inverseFourierIntegral μ f) =
      fourierIntegral 𝐞 μ (-innerSL ℝ).toLinearMap₁₂
        (fun ξ ↦ fourierPowSMulRight (-innerSL ℝ) f ξ 2) :=
    iteratedFDeriv_fourierIntegral (N := (2 : ℕ∞)) (-innerSL ℝ)
      (fun n hn ↦ hf n (by exact_mod_cast hn)) hm (by simp)
  have hc : - (2 * (Real.pi : ℂ) * Complex.I) ^ 2 =
      (((2 * Real.pi) ^ 2 : ℝ) : ℂ) := by
    push_cast
    simp [mul_pow, Complex.I_sq]
  have htrace (ξ : E) :
      -(∑ i, fourierPowSMulRight (-innerSL ℝ) f ξ 2 ![b i, b i]) =
        (2 * Real.pi) ^ 2 • (‖ξ‖ ^ 2 • f ξ) := by
    simp only [fourierPowSMulRight_apply, Fin.prod_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    change -(∑ i, (-(2 * (Real.pi : ℂ) * Complex.I)) ^ 2 •
      ((-⟪ξ, b i⟫) * (-⟪ξ, b i⟫)) • f ξ) = _
    simp only [← pow_two, neg_sq]
    rw [← Finset.smul_sum, ← Finset.sum_smul, b.sum_sq_inner_left, ← neg_smul, hc]
    rfl
  ext x
  change -(Laplacian.laplacian (inverseFourierIntegral μ f) x) =
    (2 * Real.pi) ^ 2 • inverseFourierIntegral μ (fun ξ ↦ ‖ξ‖ ^ 2 • f ξ) x
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis _ b]
  simp_rw [hd, Real.fourierIntegral_continuousMultilinearMap_apply' h₂]
  have hint (i) : Integrable (fun ξ ↦
      𝐞 (-(-innerSL ℝ) ξ x) • fourierPowSMulRight (-innerSL ℝ) f ξ 2 ![b i, b i]) μ := by
    apply (Real.fourierIntegral_convergent_iff' (-innerSL ℝ) x).2
    exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 ↦ E) F ![b i, b i]).integrable_comp h₂
  change -(∑ i, ∫ ξ, 𝐞 (-(-innerSL ℝ) ξ x) •
      fourierPowSMulRight (-innerSL ℝ) f ξ 2 ![b i, b i] ∂μ) =
        (2 * Real.pi) ^ 2 •
          (∫ ξ, 𝐞 (-(-innerSL ℝ) ξ x) • (‖ξ‖ ^ 2 • f ξ) ∂μ)
  rw [← integral_finsetSum _ (fun i _ ↦ hint i), ← integral_neg, ← integral_smul]
  apply integral_congr_ae
  filter_upwards [] with ξ
  rw [← Finset.smul_sum, ← smul_neg, htrace]
  exact smul_comm _ _ _

set_option maxHeartbeats 800000 in
-- The induction combines the real scalar action with the complex Fourier integral.
/-- Every iterate of the negative Laplacian can be computed by multiplying the frequency
integrand by the corresponding even power of the norm. -/
theorem iterate_neg_laplacian_inverseFourierIntegral {μ : Measure E} {f : E → F}
    (hf : ∀ n : ℕ, Integrable (fun ξ ↦ ‖ξ‖ ^ n * ‖f ξ‖) μ)
    (hm : AEStronglyMeasurable f μ) (k : ℕ) :
    ((fun g : E → F ↦ -Laplacian.laplacian g)^[k] (inverseFourierIntegral μ f)) =
      (2 * Real.pi) ^ (2 * k) •
        inverseFourierIntegral μ (fun ξ ↦ ‖ξ‖ ^ (2 * k) • f ξ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    let g : E → F := fun ξ ↦ ‖ξ‖ ^ (2 * k) • f ξ
    have hg : ∀ n : ℕ, Integrable (fun ξ ↦ ‖ξ‖ ^ n * ‖g ξ‖) μ := by
      intro n
      simpa only [g, norm_smul, Real.norm_eq_abs, abs_pow, abs_norm,
        ← mul_assoc, ← pow_add] using hf (n + 2 * k)
    have hgm : AEStronglyMeasurable g μ :=
      (continuous_norm.pow (2 * k)).aestronglyMeasurable.smul hm
    have hcont : ContDiff ℝ 2 (inverseFourierIntegral μ g) :=
      contDiff_inverseFourierIntegral (fun n _ ↦ hg n)
    have hscale :
        -Laplacian.laplacian ((2 * Real.pi) ^ (2 * k) • inverseFourierIntegral μ g) =
          (2 * Real.pi) ^ (2 * k) • (-Laplacian.laplacian (inverseFourierIntegral μ g)) := by
      ext x
      change -(Laplacian.laplacian ((2 * Real.pi) ^ (2 * k) •
        inverseFourierIntegral μ g) x) =
          (2 * Real.pi) ^ (2 * k) • (-(Laplacian.laplacian
            (inverseFourierIntegral μ g) x))
      rw [InnerProductSpace.laplacian_smul _ hcont.contDiffAt, smul_neg]
    rw [Function.iterate_succ_apply', ih]
    change -Laplacian.laplacian ((2 * Real.pi) ^ (2 * k) •
      inverseFourierIntegral μ g) = _
    rw [hscale, neg_laplacian_inverseFourierIntegral (fun n _ ↦ hg n) hgm, smul_smul]
    have hexp : 2 * k + 2 = 2 * (k + 1) := by omega
    rw [← pow_add, hexp]
    congr 1
    apply congrArg (inverseFourierIntegral μ)
    funext ξ
    dsimp [g]
    rw [smul_smul, ← pow_add, show 2 + 2 * k = 2 * (k + 1) by omega]

end VectorFourier
