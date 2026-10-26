import LeanestEllipse.IntegralGeometry.Radon.Basic
import LeanestEllipse.MeasureTheory.Constructions.SphereMeasure
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Analysis.Complex.Isometry

/-!
# The Radon transform in the plane

In a two-dimensional real inner product space the hyperplanes are lines, and the Radon transform
is the line integral with respect to arc length:

* `radonTransform_eq_integral_line`: for unit vectors `ω ⊥ τ`,
  `𝓡 f ω p = ∫ t, f (p • ω + t • τ)`;
* `Complex.radonTransform_eq_integral`: on `ℂ` (the model of `ℝ²` used in [Hägg]), for a unit
  complex number `ω`, `𝓡 f ω p = ∫ t, f (ω * (p + t i))`; in particular
  `𝓡 f (e^{iθ}) p = ∫ t, f (e^{iθ} (p + t i))`;
* `Complex.stronglyMeasurable_radonTransform_angle`,
  `Complex.stronglyMeasurable_radonTransform_sphere`: joint measurability of the Radon transform
  in the angle/direction and the offset;
* `Complex.ae_angle_of_ae_sphere`: an almost-everywhere statement on the space of oriented lines
  `𝕊¹ × ℝ` (with the product of arc length and Lebesgue measure) holds for almost every
  `(θ, p) ∈ ℝ × ℝ` in angle coordinates.
-/

open MeasureTheory Set Submodule Metric
open scoped RealInnerProductSpace Real

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

section TwoDim

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fact (Module.finrank ℝ E = 2)] [MeasurableSpace E] [BorelSpace E]

attribute [local instance] FiniteDimensional.of_fact_finrank_eq_two

omit [MeasurableSpace E] [BorelSpace E] in
/-- In the plane, the orthogonal complement of a unit vector `ω` is spanned by any unit vector
orthogonal to `ω`. -/
theorem span_singleton_eq_orthogonal_of_two {ω τ : E} (hω : ω ≠ 0) (hτ : τ ≠ 0)
    (hωτ : ⟪ω, τ⟫ = 0) : (ℝ ∙ τ) = (ℝ ∙ ω)ᗮ := by
  have : Fact (Module.finrank ℝ E = 1 + 1) := ⟨(Fact.out : Module.finrank ℝ E = 2)⟩
  refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
  · rw [Submodule.span_singleton_le_iff_mem, mem_orthogonal_singleton_iff_inner_right (𝕜 := ℝ)]
    exact hωτ
  · rw [finrank_span_singleton hτ, finrank_orthogonal_span_singleton (𝕜 := ℝ) (n := 1) hω]

/-- **The planar Radon transform as a line integral**: for unit vectors `ω ⊥ τ`,
`𝓡 f ω p = ∫ t, f (p • ω + t • τ)` (arc length along the line `L(ω, p)`). -/
theorem radonTransform_eq_integral_line {ω τ : E} (hω : ‖ω‖ = 1) (hτ : ‖τ‖ = 1)
    (hωτ : ⟪ω, τ⟫ = 0) (f : E → F) (p : ℝ) :
    radonTransform f ω p = ∫ t : ℝ, f (p • ω + t • τ) := by
  have hspan := span_singleton_eq_orthogonal_of_two (norm_ne_zero_iff.mp (by rw [hω]; norm_num))
    (norm_ne_zero_iff.mp (by rw [hτ]; norm_num)) hωτ
  let e : ℝ ≃ₗᵢ[ℝ] (ℝ ∙ ω)ᗮ :=
    (LinearIsometryEquiv.toSpanUnitSingleton τ hτ).trans (LinearIsometryEquiv.ofEq _ _ hspan)
  have he : ∀ t, (e t : E) = t • τ := fun t ↦ rfl
  rw [radonTransform, ← e.measurePreserving.integral_comp' (f := e.toHomeomorph.toMeasurableEquiv)]
  simp [he]

end TwoDim

namespace Complex

attribute [local instance] Complex.finrank_real_complex_fact

theorem inner_mul_I_self (ω : ℂ) : ⟪ω, ω * I⟫ = 0 := by
  rw [Complex.inner]
  simp [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im]
  ring

/-- **The Radon transform on `ℂ`**: for a unit complex number `ω`,
`𝓡 f ω p = ∫ t, f (ω * (p + t i))`. -/
theorem radonTransform_eq_integral {ω : ℂ} (hω : ‖ω‖ = 1) (f : ℂ → F) (p : ℝ) :
    radonTransform f ω p = ∫ t : ℝ, f (ω * (p + t * I)) := by
  rw [radonTransform_eq_integral_line hω (by rw [norm_mul, hω, norm_I, one_mul])
    (inner_mul_I_self ω)]
  congr 1
  ext t
  congr 1
  simp only [Complex.real_smul]
  ring

/-- The Radon transform on `ℂ` in angle coordinates:
`𝓡 f (e^{iθ}) p = ∫ t, f (e^{iθ} (p + t i))`. -/
theorem radonTransform_exp_eq_integral (f : ℂ → F) (θ p : ℝ) :
    radonTransform f (exp (θ * I)) p = ∫ t : ℝ, f (exp (θ * I) * (p + t * I)) :=
  radonTransform_eq_integral (by simp) f p

/-- Joint measurability of the Radon transform in angle coordinates. -/
theorem stronglyMeasurable_radonTransform_angle {f : ℂ → F} (hf : StronglyMeasurable f) :
    StronglyMeasurable fun w : ℝ × ℝ ↦ radonTransform f (exp (w.1 * I)) w.2 := by
  simp_rw [radonTransform_exp_eq_integral]
  refine StronglyMeasurable.integral_prod_right'
    (f := fun z : (ℝ × ℝ) × ℝ ↦ f (exp (z.1.1 * I) * (z.1.2 + z.2 * I))) ?_
  exact hf.comp_measurable (by fun_prop)

/-- Joint measurability of the Radon transform on `𝕊¹ × ℝ`. -/
theorem stronglyMeasurable_radonTransform_sphere {f : ℂ → F} (hf : StronglyMeasurable f) :
    StronglyMeasurable fun z : sphere (0 : ℂ) 1 × ℝ ↦ radonTransform f (z.1 : ℂ) z.2 := by
  have : (fun z : sphere (0 : ℂ) 1 × ℝ ↦ radonTransform f (z.1 : ℂ) z.2) =
      fun z ↦ ∫ t : ℝ, f ((z.1 : ℂ) * (z.2 + t * I)) := by
    ext z
    exact radonTransform_eq_integral (by simp) f z.2
  rw [this]
  refine StronglyMeasurable.integral_prod_right'
    (f := fun z : (sphere (0 : ℂ) 1 × ℝ) × ℝ ↦ f ((z.1.1 : ℂ) * (z.1.2 + z.2 * I))) ?_
  exact hf.comp_measurable (by fun_prop)

/-- The map `((θ, p), t) ↦ e^{iθ} (p + t i)`, parametrizing the points of all oriented lines. -/
def linePoint (z : (ℝ × ℝ) × ℝ) : ℂ := exp (z.1.1 * I) * (z.1.2 + z.2 * I)

theorem measurable_linePoint : Measurable linePoint := by
  unfold linePoint
  fun_prop

/-- For a fixed angle, `(p, t) ↦ e^{iθ} (p + t i)` preserves Lebesgue measure. -/
theorem measurePreserving_rotate_equivRealProd_symm (θ : ℝ) :
    MeasurePreserving (fun z : ℝ × ℝ ↦ exp (θ * I) * (z.1 + z.2 * I)) := by
  have h1 := Complex.volume_preserving_equiv_real_prod.symm
  have h2 := (rotation (Circle.exp θ)).measurePreserving
  convert h2.comp h1 using 1
  ext z
  simp [Complex.measurableEquivRealProd, mul_comm, Complex.ext_iff]

/-- `((θ, p), t) ↦ e^{iθ} (p + t i)` does not charge Lebesgue null sets. -/
theorem quasiMeasurePreserving_linePoint :
    Measure.QuasiMeasurePreserving linePoint ((volume.prod volume).prod volume) volume := by
  refine ⟨measurable_linePoint, Measure.AbsolutelyContinuous.mk fun s hs h0 ↦ ?_⟩
  rw [Measure.map_apply measurable_linePoint hs]
  set A : Set (ℝ × ℝ × ℝ) := {z | exp (z.1 * I) * (z.2.1 + z.2.2 * I) ∈ s}
  have hA : MeasurableSet A := hs.preimage (by fun_prop)
  have hpre : linePoint ⁻¹' s = MeasurableEquiv.prodAssoc ⁻¹' A := by
    ext z; rfl
  rw [hpre, (measurePreserving_prodAssoc volume volume volume).measure_preimage
    hA.nullMeasurableSet, Measure.prod_apply hA]
  have hθ : ∀ θ : ℝ, (volume.prod volume) (Prod.mk θ ⁻¹' A) = 0 := by
    intro θ
    have := (measurePreserving_rotate_equivRealProd_symm θ).measure_preimage hs.nullMeasurableSet
    rw [← Measure.volume_eq_prod,
      show Prod.mk θ ⁻¹' A = (fun z : ℝ × ℝ ↦ exp (θ * I) * (z.1 + z.2 * I)) ⁻¹' s from rfl,
      this, h0]
  simp [hθ]

/-- **The planar Radon transform only depends on the a.e.-class, jointly in the line.**  If
`f = g` almost everywhere, then `𝓡 f (e^{iθ}) p = 𝓡 g (e^{iθ}) p` for almost every
`(θ, p) ∈ ℝ × ℝ`. -/
theorem radonTransform_exp_ae_eq_of_ae_eq {f g : ℂ → F} (hfg : f =ᵐ[volume] g) :
    ∀ᵐ w : ℝ × ℝ, radonTransform f (exp (w.1 * I)) w.2 =
      radonTransform g (exp (w.1 * I)) w.2 := by
  have h1 : f ∘ linePoint =ᵐ[(volume.prod volume).prod volume] g ∘ linePoint :=
    quasiMeasurePreserving_linePoint.ae_eq_comp hfg
  have h2 := Measure.ae_ae_eq_curry_of_prod h1
  rw [← Measure.volume_eq_prod] at h2
  filter_upwards [h2] with w hw
  rw [radonTransform_exp_eq_integral, radonTransform_exp_eq_integral]
  exact integral_congr_ae hw

/-- **From oriented-line space to angle coordinates.**  A property of oriented lines
`(ω, p) ∈ 𝕊¹ × ℝ` holding almost everywhere for the product of arc length and Lebesgue measure
holds for almost every `(θ, p) ∈ ℝ × ℝ` at `(e^{iθ}, p)`. -/
theorem ae_angle_of_ae_sphere {P : sphere (0 : ℂ) 1 → ℝ → Prop}
    (h : ∀ᵐ z ∂((volume : Measure ℂ).toSphere.prod volume), P z.1 z.2) :
    ∀ᵐ w : ℝ × ℝ, P (expMapSphere w.1) w.2 := by
  -- one period
  have hmap : (volume : Measure ℂ).toSphere.prod (volume : Measure ℝ) =
      (((volume : Measure ℝ).restrict (Ioc (-π) π)).prod volume).map
        (Prod.map expMapSphere id) := by
    rw [← Measure.map_prod_map _ _ measurable_expMapSphere measurable_id, Measure.map_id,
      toSphere_eq_map_expMapSphere]
  have hprod : ((volume : Measure ℝ).restrict (Ioc (-π) π)).prod (volume : Measure ℝ) =
      (volume : Measure (ℝ × ℝ)).restrict (Ioc (-π) π ×ˢ univ) := by
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]
  rw [hmap] at h
  have h1 := ae_of_ae_map (measurable_expMapSphere.prodMap measurable_id).aemeasurable h
  rw [hprod, ae_restrict_iff' (measurableSet_Ioc.prod MeasurableSet.univ)] at h1
  -- all periods, by translation invariance
  have hk : ∀ k : ℤ, ∀ᵐ w : ℝ × ℝ, w.1 - k * (2 * π) ∈ Ioc (-π) π →
      P (expMapSphere w.1) w.2 := by
    intro k
    have hmp : MeasurePreserving (fun w : ℝ × ℝ ↦ (w.1 - k * (2 * π), w.2)) := by
      have := (measurePreserving_sub_right (volume : Measure ℝ) (k * (2 * π))).prod
        (MeasurePreserving.id (volume : Measure ℝ))
      rw [← Measure.volume_eq_prod] at this
      exact this
    filter_upwards [hmp.quasiMeasurePreserving.ae h1] with w hw hmem
    have := hw ⟨hmem, mem_univ _⟩
    have hexp : expMapSphere (w.1 - k * (2 * π)) = expMapSphere w.1 := by
      apply Subtype.ext
      simp only [coe_expMapSphere]
      rw [show ((w.1 - k * (2 * π) : ℝ) : ℂ) * I = w.1 * I - k * (2 * π * I) by push_cast; ring,
        Complex.exp_sub, Complex.exp_int_mul_two_pi_mul_I, div_one]
    simpa [hexp] using this
  rw [← ae_all_iff] at hk
  filter_upwards [hk] with w hw
  obtain ⟨k, hk', -⟩ := existsUnique_sub_zsmul_mem_Ioc Real.two_pi_pos w.1 (-π)
  refine hw k ?_
  rw [zsmul_eq_mul] at hk'
  convert hk' using 2
  ring

end Complex

end
