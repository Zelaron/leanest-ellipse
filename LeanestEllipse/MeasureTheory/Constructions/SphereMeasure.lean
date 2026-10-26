import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# The surface measure of the unit sphere

Mathlib's `MeasureTheory.Measure.toSphere` equips the unit sphere of a normed space with the
surface measure induced by a Haar measure (`μ.toSphere s = dim E * μ (Ioo 0 1 • s)`).  We prove:

* `LinearIsometryEquiv.toSphere_map`: it is invariant under linear isometry equivalences;
* `Complex.toSphere_eq_map_expMapSphere`: on `ℂ` it is arc length, i.e. the push-forward of
  Lebesgue measure on `(-π, π]` under `θ ↦ exp (θ i)`.

Consequently, on a two-dimensional real inner product space `(volume).toSphere` is the arc-length
measure `dω` on the unit circle `𝕊¹` used in [Hägg].
-/

open MeasureTheory Set Metric
open scoped ENNReal Real Pointwise

noncomputable section

/-! ### Cones over sets of unit vectors -/

section Cone

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The cone `Ioo 0 1 • s` over a measurable set of unit vectors is measurable. -/
theorem measurableSet_Ioo_smul_image {s : Set (sphere (0 : E) 1)} (hs : MeasurableSet s) :
    MeasurableSet (Ioo (0 : ℝ) 1 • ((↑) '' s : Set E)) := by
  have : PolishSpace (sphere (0 : E) 1) := isClosed_sphere.polishSpace
  have heq : Ioo (0 : ℝ) 1 • ((↑) '' s : Set E) =
      (fun p : ℝ × sphere (0 : E) 1 ↦ p.1 • (p.2 : E)) '' (Ioo (0 : ℝ) 1 ×ˢ s) := by
    ext x
    simp only [Set.mem_smul, mem_image, mem_prod, Prod.exists]
    constructor
    · rintro ⟨a, ha, _, ⟨y, hy, rfl⟩, rfl⟩
      exact ⟨a, y, ⟨ha, hy⟩, rfl⟩
    · rintro ⟨a, y, ⟨ha, hy⟩, rfl⟩
      exact ⟨a, ha, y, ⟨y, hy, rfl⟩, rfl⟩
  rw [heq]
  refine (measurableSet_Ioo.prod hs).image_of_continuousOn_injOn (by fun_prop) ?_
  rintro ⟨a, y⟩ ⟨ha, -⟩ ⟨b, z⟩ ⟨hb, -⟩ hab
  have hy : ‖(y : E)‖ = 1 := by simp
  have hz : ‖(z : E)‖ = 1 := by simp
  simp only at hab
  have hnorm : a = b := by
    have := congrArg norm hab
    rwa [norm_smul, norm_smul, hy, hz, mul_one, mul_one, Real.norm_of_nonneg ha.1.le,
      Real.norm_of_nonneg hb.1.le] at this
  subst hnorm
  have : (y : E) = z := smul_right_injective E ha.1.ne' hab
  simp [Subtype.ext this]

end Cone

/-! ### Invariance under linear isometries -/

section Isometry

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]

/-- The map between unit spheres induced by a linear isometry equivalence. -/
def LinearIsometryEquiv.sphereMap (L : E ≃ₗᵢ[ℝ] F) (x : sphere (0 : E) 1) : sphere (0 : F) 1 :=
  ⟨L x, by simp⟩

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F] in
@[simp] theorem LinearIsometryEquiv.coe_sphereMap (L : E ≃ₗᵢ[ℝ] F) (x : sphere (0 : E) 1) :
    (L.sphereMap x : F) = L x := rfl

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F] in
theorem LinearIsometryEquiv.continuous_sphereMap (L : E ≃ₗᵢ[ℝ] F) : Continuous L.sphereMap :=
  (L.continuous.comp continuous_subtype_val).subtype_mk _

/-- The surface measure of the unit sphere is invariant under linear isometry equivalences. -/
theorem LinearIsometryEquiv.toSphere_map (L : E ≃ₗᵢ[ℝ] F) :
    (volume : Measure E).toSphere.map L.sphereMap = (volume : Measure F).toSphere := by
  ext s hs
  have hmeas : Measurable L.sphereMap := L.continuous_sphereMap.measurable
  rw [Measure.map_apply hmeas hs, Measure.toSphere_apply' _ (hmeas hs),
    Measure.toSphere_apply' _ hs, L.toLinearEquiv.finrank_eq]
  congr 1
  have himage : Ioo (0 : ℝ) 1 • ((↑) '' (L.sphereMap ⁻¹' s) : Set E) =
      L ⁻¹' (Ioo (0 : ℝ) 1 • ((↑) '' s : Set F)) := by
    ext x
    simp only [Set.mem_smul, mem_image, mem_preimage, Subtype.exists, exists_and_right,
      exists_eq_right]
    constructor
    · rintro ⟨a, ha, y, ⟨hy, hys⟩, rfl⟩
      exact ⟨a, ha, L y, ⟨by simpa using hy, hys⟩, by simp⟩
    · rintro ⟨a, ha, y, ⟨hy, hys⟩, hxy⟩
      refine ⟨a, ha, L.symm y, ⟨by simpa using hy, ?_⟩, ?_⟩
      · convert hys using 2
        simp [LinearIsometryEquiv.sphereMap]
      · apply L.injective
        simp [hxy]
  have hL : MeasurePreserving L.toHomeomorph.toMeasurableEquiv volume volume := L.measurePreserving
  rw [himage]
  exact hL.measure_preimage_equiv _

end Isometry

/-! ### Arc length on the unit circle of `ℂ` -/

namespace Complex

/-- The angle parametrization `θ ↦ exp (θ i)` of the unit circle of `ℂ`. -/
def expMapSphere (θ : ℝ) : sphere (0 : ℂ) 1 :=
  ⟨Complex.exp (θ * Complex.I), by simp⟩

@[simp] theorem coe_expMapSphere (θ : ℝ) :
    (expMapSphere θ : ℂ) = Complex.exp (θ * Complex.I) := rfl

theorem continuous_expMapSphere : Continuous expMapSphere :=
  (by fun_prop : Continuous fun θ : ℝ ↦ Complex.exp (θ * Complex.I)).subtype_mk _

theorem measurable_expMapSphere : Measurable expMapSphere :=
  continuous_expMapSphere.measurable

/-- A point `r • u` (`r > 0`, `‖u‖ = 1`) lies in `Ioo 0 1 • S` (`S` a set of unit vectors) iff
`r < 1` and `u ∈ S`. -/
theorem smul_mem_Ioo_smul_iff {S : Set ℂ} (hS : S ⊆ sphere 0 1) {r : ℝ} (hr : 0 < r) {u : ℂ}
    (hu : ‖u‖ = 1) : (r : ℂ) * u ∈ Ioo (0 : ℝ) 1 • S ↔ r < 1 ∧ u ∈ S := by
  constructor
  · rintro ⟨a, ha, v, hv, hav⟩
    have hvn : ‖v‖ = 1 := by simpa using hS hv
    have hnorm : a = r := by
      have := congrArg norm hav
      rw [norm_smul, hvn, mul_one, norm_mul, hu, mul_one, Complex.norm_real,
        Real.norm_of_nonneg ha.1.le, Real.norm_of_nonneg hr.le] at this
      exact this
    subst hnorm
    refine ⟨ha.2, ?_⟩
    have : v = u := by
      have hav' : (a : ℂ) * v = (a : ℂ) * u := by simpa [Complex.real_smul] using hav
      exact mul_left_cancel₀ (by exact_mod_cast ha.1.ne') hav'
    rwa [← this]
  · rintro ⟨hr1, huS⟩
    exact ⟨r, ⟨hr, hr1⟩, u, huS, by simp [Complex.real_smul]⟩

/-- The volume of the "cone" `Ioo 0 1 • S` over a set `S` of unit vectors, in polar coordinates:
half the length of the set of angles in `(-π, π)` pointing into `S`. -/
theorem volume_Ioo_smul_eq {s : Set (sphere (0 : ℂ) 1)} (hs : MeasurableSet s) :
    volume (Ioo (0 : ℝ) 1 • ((↑) '' s : Set ℂ)) =
      ENNReal.ofReal (1 / 2) * volume (expMapSphere ⁻¹' s ∩ Ioo (-π) π) := by
  set X : Set ℂ := Ioo (0 : ℝ) 1 • ((↑) '' s : Set ℂ)
  have hS : ((↑) '' s : Set ℂ) ⊆ sphere 0 1 := by rintro _ ⟨x, -, rfl⟩; exact x.2
  -- the indicator of `X` in polar coordinates
  have hind : ∀ p ∈ Complex.polarCoord.target,
      X.indicator (1 : ℂ → ℝ≥0∞) (Complex.polarCoord.symm p) =
        (Iio (1 : ℝ)).indicator 1 p.1 * (expMapSphere ⁻¹' s).indicator 1 p.2 := by
    rintro ⟨r, θ⟩ ⟨hr, -⟩
    have hr : 0 < r := hr
    have hpt : Complex.polarCoord.symm (r, θ) = (r : ℂ) * Complex.exp (θ * Complex.I) := by
      rw [Complex.polarCoord_symm_apply, Complex.exp_mul_I, ← Complex.ofReal_cos,
        ← Complex.ofReal_sin]
    have hmem : (r : ℂ) * Complex.exp (θ * Complex.I) ∈ X ↔ r < 1 ∧ θ ∈ expMapSphere ⁻¹' s := by
      rw [smul_mem_Ioo_smul_iff hS hr (by simp)]
      simp only [mem_preimage, mem_image]
      refine and_congr_right fun _ ↦ ⟨?_, fun h ↦ ⟨_, h, rfl⟩⟩
      rintro ⟨x, hx, hxe⟩
      have : x = expMapSphere θ := Subtype.ext hxe
      rwa [← this]
    rw [hpt]
    by_cases h1 : r < 1 <;> by_cases h2 : θ ∈ expMapSphere ⁻¹' s <;>
      simp [indicator, hmem, h1, h2]
  calc volume X = ∫⁻ z, X.indicator 1 z :=
        (lintegral_indicator_one (measurableSet_Ioo_smul_image hs)).symm
    _ = ∫⁻ p in Complex.polarCoord.target, ENNReal.ofReal p.1 •
          X.indicator (1 : ℂ → ℝ≥0∞) (Complex.polarCoord.symm p) :=
        (Complex.lintegral_comp_polarCoord_symm _).symm
    _ = ∫⁻ p in Ioi (0 : ℝ) ×ˢ Ioo (-π) π,
          (ENNReal.ofReal p.1 * (Iio (1 : ℝ)).indicator 1 p.1) *
            (expMapSphere ⁻¹' s).indicator 1 p.2 := by
        rw [Complex.polarCoord_target]
        refine setLIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo) fun p hp ↦ ?_
        rw [smul_eq_mul, hind p (by rwa [Complex.polarCoord_target]), mul_assoc]
    _ = (∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal r * (Iio (1 : ℝ)).indicator 1 r) *
          ∫⁻ θ in Ioo (-π) π, (expMapSphere ⁻¹' s).indicator 1 θ := by
        rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
        exact lintegral_prod_mul
          ((ENNReal.measurable_ofReal.mul
            (measurable_one.indicator measurableSet_Iio)).aemeasurable)
          ((measurable_one.indicator (measurable_expMapSphere hs)).aemeasurable)
    _ = ENNReal.ofReal (1 / 2) * volume (expMapSphere ⁻¹' s ∩ Ioo (-π) π) := by
        congr 1
        · have h1 : ∀ r : ℝ, ENNReal.ofReal r * (Iio (1 : ℝ)).indicator 1 r =
              (Iio (1 : ℝ)).indicator (fun r ↦ ENNReal.ofReal r) r := by
            intro r
            by_cases hr : r < 1 <;> simp [indicator, hr]
          simp_rw [h1]
          rw [lintegral_indicator measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio,
            Iio_inter_Ioi, ← ofReal_integral_eq_lintegral_ofReal]
          · congr 1
            rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one,
              integral_id]
            norm_num
          · exact (continuous_id.integrableOn_Icc (a := 0) (b := 1)).mono_set Ioo_subset_Icc_self
          · filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
            exact hr.1.le
        · rw [lintegral_indicator_one (measurable_expMapSphere hs), Measure.restrict_apply
            (measurable_expMapSphere hs)]

/-- **Arc length on the unit circle.**  The surface measure `volume.toSphere` of the unit circle
of `ℂ` is the push-forward of Lebesgue measure on `(-π, π]` under `θ ↦ exp (θ i)`. -/
theorem toSphere_eq_map_expMapSphere :
    (volume : Measure ℂ).toSphere = (volume.restrict (Ioc (-π) π)).map expMapSphere := by
  ext s hs
  rw [Measure.map_apply measurable_expMapSphere hs, Measure.restrict_apply
    (measurable_expMapSphere hs), Measure.toSphere_apply' _ hs, Complex.finrank_real_complex,
    volume_Ioo_smul_eq hs]
  have hIoc : volume (expMapSphere ⁻¹' s ∩ Ioc (-π) π) =
      volume (expMapSphere ⁻¹' s ∩ Ioo (-π) π) := by
    apply le_antisymm
    · calc volume (expMapSphere ⁻¹' s ∩ Ioc (-π) π)
          ≤ volume (expMapSphere ⁻¹' s ∩ Ioo (-π) π ∪ {π}) := by
            refine measure_mono fun x ⟨hxA, hx1, hx2⟩ ↦ ?_
            rcases hx2.lt_or_eq with h | h
            · exact Or.inl ⟨hxA, hx1, h⟩
            · exact Or.inr h
        _ ≤ volume (expMapSphere ⁻¹' s ∩ Ioo (-π) π) + volume ({π} : Set ℝ) :=
            measure_union_le _ _
        _ = volume (expMapSphere ⁻¹' s ∩ Ioo (-π) π) := by rw [Real.volume_singleton, add_zero]
    · exact measure_mono (inter_subset_inter_right _ Ioo_subset_Ioc_self)
  have h2 : (2 : ℝ≥0∞) * ENNReal.ofReal (1 / 2) = 1 := by
    rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num)]
    norm_num
  rw [hIoc, ← mul_assoc]
  push_cast
  rw [h2, one_mul]

/-- The unit circle has total arc length `2π`, in the surface-measure normalization. -/
@[simp]
theorem toSphere_real_univ : (volume : Measure ℂ).toSphere.real univ = 2 * π := by
  rw [Measure.real, toSphere_eq_map_expMapSphere,
    Measure.map_apply measurable_expMapSphere MeasurableSet.univ]
  simp only [preimage_univ, Measure.restrict_apply MeasurableSet.univ, univ_inter,
    Real.volume_Ioc]
  rw [ENNReal.toReal_ofReal (show 0 ≤ π - -π by linarith [Real.pi_pos])]
  ring

end Complex

end
