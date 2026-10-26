import LeanestEllipse.MeasureTheory.Constructions.SphereMeasure
import Mathlib.Analysis.Distribution.TemperateGrowth
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

/-!
# Polar coordinates with a signed radius

`Measure.signedRadial μ` is the push-forward of `μ.prod volume` under `(ω, r) ↦ r • ω`,
where `ω` is a unit vector and `r` ranges over all of `ℝ`. A finite angular measure gives a
measure of temperate growth.

For the Euclidean surface measure `volume.toSphere`, weighting by
`‖x‖ ^ (finrank ℝ E - 1)` gives twice the Euclidean volume integral. The factor two comes
from the two representations `(ω, r)` and `(-ω, -r)` of every nonzero point.
-/

open MeasureTheory Set Metric

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

namespace MeasureTheory.Measure

/-- The point with unit direction `z.1` and signed radius `z.2`. -/
def signedRadialPoint (z : sphere (0 : E) 1 × ℝ) : E := z.2 • (z.1 : E)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
@[fun_prop]
theorem continuous_signedRadialPoint : Continuous (signedRadialPoint (E := E)) := by
  fun_prop [signedRadialPoint]

omit [FiniteDimensional ℝ E] in
@[fun_prop]
theorem measurable_signedRadialPoint : Measurable (signedRadialPoint (E := E)) :=
  continuous_signedRadialPoint.measurable

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
@[simp]
theorem norm_signedRadialPoint (z : sphere (0 : E) 1 × ℝ) :
    ‖signedRadialPoint z‖ = |z.2| := by
  simp [signedRadialPoint, norm_smul]

/-- The push-forward of an angular measure times Lebesgue measure in a signed radius. -/
def signedRadial (μ : Measure (sphere (0 : E) 1)) : Measure E :=
  Measure.map signedRadialPoint (μ.prod volume)

instance signedRadial_hasTemperateGrowth (μ : Measure (sphere (0 : E) 1)) [IsFiniteMeasure μ] :
    (signedRadial μ).HasTemperateGrowth := by
  have hreal : Integrable (fun s : ℝ ↦ (1 + ‖s‖) ^ (-(2 : ℝ))) :=
    integrable_one_add_norm (by norm_num)
  have hcont : Continuous (fun x : E ↦ (1 + ‖x‖) ^ (-(2 : ℝ))) := by
    apply Continuous.rpow_const (by fun_prop)
    intro x
    exact Or.inl (ne_of_gt (by positivity))
  refine ⟨2, (integrable_map_measure hcont.aestronglyMeasurable
    continuous_signedRadialPoint.measurable.aemeasurable).2 ?_⟩
  simpa [Function.comp_def, signedRadialPoint, norm_smul] using hreal.comp_snd μ

/-- Positive-radius polar coordinates preserve Euclidean volume with the usual radial weight. -/
theorem measurePreserving_positiveRadial [Nontrivial E] :
    MeasurePreserving
      (fun z : sphere (0 : E) 1 × Ioi (0 : ℝ) ↦ (z.2 : ℝ) • (z.1 : E))
      ((volume : Measure E).toSphere.prod (volumeIoiPow (Module.finrank ℝ E - 1)))
      volume := by
  have hpolar := (volume : Measure E).measurePreserving_homeomorphUnitSphereProd
  have hinv := hpolar.symm (homeomorphUnitSphereProd E).toMeasurableEquiv
  have hsub := measurePreserving_subtype_coe (μa := (volume : Measure E))
    (measurableSet_singleton (0 : E)).compl
  rw [restrict_compl_singleton] at hsub
  convert hsub.comp hinv using 1
  funext z
  simp

/-- Positive-radius polar coordinates give a measurable embedding into the ambient space. -/
theorem measurableEmbedding_positiveRadial :
    MeasurableEmbedding
      (fun z : sphere (0 : E) 1 × Ioi (0 : ℝ) ↦ (z.2 : ℝ) • (z.1 : E)) := by
  convert (MeasurableEmbedding.subtype_coe (measurableSet_singleton (0 : E)).compl).comp
    (homeomorphUnitSphereProd E).symm.measurableEmbedding using 1
  funext z
  simp

/-- The positive-radius half of the signed polar-coordinate integral. -/
theorem integral_positiveRadial [Nontrivial E] {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (f : E → F) :
    ∫ z in univ ×ˢ Ioi (0 : ℝ),
      ‖signedRadialPoint z‖ ^ (Module.finrank ℝ E - 1) • f (signedRadialPoint z)
        ∂(volume : Measure E).toSphere.prod volume = ∫ x, f x := by
  have : SigmaFinite (volume.comap (Subtype.val : Ioi (0 : ℝ) → ℝ)) := by
    simpa [volumeIoiPow] using (inferInstance : SigmaFinite (volumeIoiPow 0))
  let σ := (volume : Measure E).toSphere
  let m := Module.finrank ℝ E - 1
  have hpolar := (measurePreserving_positiveRadial (E := E)).integral_comp
    measurableEmbedding_positiveRadial f
  simp only [volumeIoiPow, ENNReal.ofReal] at hpolar
  rw [prod_withDensity_right (by fun_prop), integral_withDensity_eq_integral_smul
    (by fun_prop)] at hpolar
  have hweight :
      (fun z : sphere (0 : E) 1 × Ioi (0 : ℝ) ↦
        Real.toNNReal ((z.2 : ℝ) ^ m) • f ((z.2 : ℝ) • (z.1 : E))) =
      (fun z ↦ ‖signedRadialPoint (z.1, (z.2 : ℝ))‖ ^ m •
        f (signedRadialPoint (z.1, (z.2 : ℝ)))) := by
    funext z
    have hz : 0 < (z.2 : ℝ) := z.2.2
    simp [signedRadialPoint, norm_smul, abs_of_pos hz, NNReal.smul_def,
      Real.coe_toNNReal _ (pow_nonneg hz.le _)]
  change (∫ z, Real.toNNReal ((z.2 : ℝ) ^ m) •
    f ((z.2 : ℝ) • (z.1 : E)) ∂σ.prod (volume.comap (Subtype.val : Ioi (0 : ℝ) → ℝ))) = _
    at hpolar
  rw [hweight] at hpolar
  have hi := (MeasurePreserving.id σ).prod
    (measurePreserving_subtype_coe (μa := (volume : Measure ℝ))
      (s := Ioi (0 : ℝ)) measurableSet_Ioi)
  have hemb : MeasurableEmbedding (Prod.map (id : sphere (0 : E) 1 → sphere (0 : E) 1)
      (Subtype.val : Ioi (0 : ℝ) → ℝ)) := MeasurableEmbedding.id.prodMap
    (MeasurableEmbedding.subtype_coe (s := Ioi (0 : ℝ)) measurableSet_Ioi)
  have hchange := hi.integral_comp hemb (fun z : sphere (0 : E) 1 × ℝ ↦
    ‖signedRadialPoint z‖ ^ m • f (signedRadialPoint z))
  change (∫ z, ‖signedRadialPoint (z.1, (z.2 : ℝ))‖ ^ m •
    f (signedRadialPoint (z.1, (z.2 : ℝ)))
      ∂σ.prod (volume.comap (Subtype.val : Ioi (0 : ℝ) → ℝ))) = _ at hchange
  change (∫ z, ‖signedRadialPoint z‖ ^ m • f (signedRadialPoint z)
    ∂(σ.prod volume).restrict (univ ×ˢ Ioi (0 : ℝ))) = _
  rw [← Measure.prod_restrict, Measure.restrict_univ, ← hchange]
  exact hpolar

private def sphereAntipode : sphere (0 : E) 1 ≃ᵐ sphere (0 : E) 1 where
  toEquiv :=
    { toFun := (LinearIsometryEquiv.neg ℝ : E ≃ₗᵢ[ℝ] E).sphereMap
      invFun := (LinearIsometryEquiv.neg ℝ : E ≃ₗᵢ[ℝ] E).sphereMap
      left_inv := by intro x; apply Subtype.ext; simp
      right_inv := by intro x; apply Subtype.ext; simp }
  measurable_toFun := (LinearIsometryEquiv.neg ℝ : E ≃ₗᵢ[ℝ] E).continuous_sphereMap.measurable
  measurable_invFun := (LinearIsometryEquiv.neg ℝ : E ≃ₗᵢ[ℝ] E).continuous_sphereMap.measurable

private def radialFlip : sphere (0 : E) 1 × ℝ ≃ᵐ sphere (0 : E) 1 × ℝ :=
  (sphereAntipode (E := E)).prodCongr (Homeomorph.neg ℝ).toMeasurableEquiv

private theorem measurePreserving_radialFlip :
    MeasurePreserving (radialFlip (E := E))
      ((volume : Measure E).toSphere.prod volume)
      ((volume : Measure E).toSphere.prod volume) := by
  have hs : MeasurePreserving (sphereAntipode (E := E))
      (volume : Measure E).toSphere (volume : Measure E).toSphere :=
    ⟨(sphereAntipode (E := E)).measurable,
      (LinearIsometryEquiv.neg ℝ : E ≃ₗᵢ[ℝ] E).toSphere_map⟩
  exact hs.prod (LinearIsometryEquiv.neg ℝ : ℝ ≃ₗᵢ[ℝ] ℝ).measurePreserving

omit [FiniteDimensional ℝ E] in
@[simp] private theorem signedRadialPoint_radialFlip (z : sphere (0 : E) 1 × ℝ) :
    signedRadialPoint (radialFlip z) = signedRadialPoint z := by
  change (-z.2) • (-(z.1 : E)) = z.2 • (z.1 : E)
  simp

/-- The negative-radius half equals the positive half by antipodal symmetry. -/
theorem integral_negativeRadial [Nontrivial E] {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (f : E → F) :
    ∫ z in univ ×ˢ Iio (0 : ℝ),
      ‖signedRadialPoint z‖ ^ (Module.finrank ℝ E - 1) • f (signedRadialPoint z)
        ∂(volume : Measure E).toSphere.prod volume = ∫ x, f x := by
  have hpre : (radialFlip (E := E)) ⁻¹' (univ ×ˢ Ioi (0 : ℝ)) = univ ×ˢ Iio (0 : ℝ) := by
    ext z
    change (True ∧ 0 < -z.2) ↔ (True ∧ z.2 < 0)
    simp
  have hchange := (measurePreserving_radialFlip (E := E)).setIntegral_preimage_emb
    (radialFlip (E := E)).measurableEmbedding
    (fun z : sphere (0 : E) 1 × ℝ ↦
      ‖signedRadialPoint z‖ ^ (Module.finrank ℝ E - 1) • f (signedRadialPoint z))
    (univ ×ˢ Ioi (0 : ℝ))
  rw [hpre] at hchange
  simpa only [signedRadialPoint_radialFlip] using
    hchange.trans (integral_positiveRadial f)

/-- The weighted signed polar-coordinate integral is twice the Euclidean volume integral. -/
theorem integral_signedRadial [Nontrivial E] {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (f : E → F)
    (hw : Integrable (fun x ↦ ‖x‖ ^ (Module.finrank ℝ E - 1) • f x)
      (signedRadial (volume : Measure E).toSphere)) :
    ∫ x, ‖x‖ ^ (Module.finrank ℝ E - 1) • f x
      ∂signedRadial (volume : Measure E).toSphere = (2 : ℝ) • ∫ x, f x := by
  have hgi := hw.comp_measurable continuous_signedRadialPoint.measurable
  change Integrable (fun z : sphere (0 : E) 1 × ℝ ↦
    ‖signedRadialPoint z‖ ^ (Module.finrank ℝ E - 1) • f (signedRadialPoint z))
    ((volume : Measure E).toSphere.prod volume) at hgi
  rw [signedRadial, integral_map continuous_signedRadialPoint.measurable.aemeasurable
    hw.aestronglyMeasurable]
  have hcomp : (univ ×ˢ Ioi (0 : ℝ) : Set (sphere (0 : E) 1 × ℝ))ᶜ = univ ×ˢ Iic (0 : ℝ) := by
    ext z
    simp
  have hae : (univ ×ˢ Iic (0 : ℝ) : Set (sphere (0 : E) 1 × ℝ))
      =ᵐ[(volume : Measure E).toSphere.prod volume] univ ×ˢ Iio (0 : ℝ) :=
    set_prod_ae_eq Filter.EventuallyEq.rfl Iio_ae_eq_Iic.symm
  have hsplit := integral_add_compl (s := univ ×ˢ Ioi (0 : ℝ))
    (MeasurableSet.univ.prod measurableSet_Ioi) hgi
  rw [hcomp, setIntegral_congr_set hae, integral_positiveRadial, integral_negativeRadial] at hsplit
  rw [← hsplit, two_smul ℝ]

end MeasureTheory.Measure
