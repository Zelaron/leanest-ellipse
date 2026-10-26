import LeanestEllipse.IntegralGeometry.Radon.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Radon transforms of continuous compactly supported functions

A continuous compactly supported function is integrable on each affine hyperplane.
Consequently its Radon transform is pointwise linear, with no exceptional offsets.
For every fixed normal vector its Radon profile is continuous in the offset.
-/

open MeasureTheory Set Metric
open scoped RealInnerProductSpace

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [NormedSpace ℝ F] in
/-- A continuous compactly supported function is integrable on every affine hyperplane. -/
theorem Continuous.integrable_radonTransform_fiber {f : E → F} (hf : Continuous f)
    (hc : HasCompactSupport f) (ω : E) (p : ℝ) :
    Integrable (fun y : (ℝ ∙ ω)ᗮ ↦ f (p • ω + y)) := by
  have he : Topology.IsClosedEmbedding (fun y : (ℝ ∙ ω)ᗮ ↦ p • ω + (y : E)) :=
    (Homeomorph.addLeft (p • ω)).isClosedEmbedding.comp
      (Submodule.isClosed_orthogonal (ℝ ∙ ω)).isClosedEmbedding_subtypeVal
  exact (hf.comp he.continuous).integrable_of_hasCompactSupport
    (hc.comp_isClosedEmbedding he)

/-- The Radon transform is additive at every offset for continuous functions of compact support. -/
theorem radonTransform_add_of_continuous {f g : E → F} (hf : Continuous f)
    (hfc : HasCompactSupport f) (hg : Continuous g) (hgc : HasCompactSupport g)
    (ω : E) (p : ℝ) :
    radonTransform (f + g) ω p = radonTransform f ω p + radonTransform g ω p :=
  radonTransform_add (hf.integrable_radonTransform_fiber hfc ω p)
    (hg.integrable_radonTransform_fiber hgc ω p)

/-- The Radon profile of a continuous compactly supported function is continuous in its
offset. The normal vector need not be a unit vector. -/
theorem Continuous.radonTransform {f : E → F} (hf : Continuous f)
    (hc : HasCompactSupport f) (ω : E) : Continuous (_root_.radonTransform f ω) := by
  obtain ⟨R, hR⟩ := (show IsCompact (tsupport f) from hc).isBounded.exists_norm_le
  have hrestrict (p : ℝ) : _root_.radonTransform f ω p =
      ∫ y in closedBall (0 : (ℝ ∙ ω)ᗮ) R, f (p • ω + (y : E)) := by
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro y hy
    by_contra hfy
    have hsupport := hR _ (subset_tsupport f hfy)
    have horth : ⟪p • ω, (y : E)⟫ = 0 := by
      rw [real_inner_smul_left, real_inner_comm (y : E) ω,
        RadonTransform.inner_orthogonal_eq_zero y, mul_zero]
    have hnorm : ‖(y : E)‖ ≤ ‖p • ω + (y : E)‖ := by
      have hsq := norm_add_sq_real (p • ω) (y : E)
      rw [horth] at hsq
      nlinarith [norm_nonneg (p • ω + (y : E)), norm_nonneg (y : E), sq_nonneg ‖p • ω‖]
    exact hy (by simpa using hnorm.trans hsupport)
  have hcontinuous : Continuous (fun z : ℝ × (ℝ ∙ ω)ᗮ ↦ f (z.1 • ω + (z.2 : E))) := by
    fun_prop
  have hint := continuous_parametric_integral_of_continuous
    (f := fun (p : ℝ) (y : (ℝ ∙ ω)ᗮ) ↦ f (p • ω + (y : E))) (μ := volume)
    hcontinuous (isCompact_closedBall (0 : (ℝ ∙ ω)ᗮ) R)
  exact hint.congr fun p ↦ (hrestrict p).symm
