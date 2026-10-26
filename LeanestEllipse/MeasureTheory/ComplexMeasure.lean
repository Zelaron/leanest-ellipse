import Mathlib.MeasureTheory.VectorMeasure.WithDensityVec
import Mathlib.MeasureTheory.VectorMeasure.Variation.SignedMeasure
import Mathlib.MeasureTheory.Measure.Complex
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.Topology.ContinuousMap.Compact

/-!
# Integration against complex measures

We complement Mathlib's vector-measure integral `∫ᵛ x, f x ∂[B; μ]`
(`Mathlib/MeasureTheory/VectorMeasure/Integral.lean`) with the facts needed to work with
complex measures `η : ComplexMeasure X`, integrated through the pairing
`ContinuousLinearMap.mul ℝ ℂ`, i.e. `∫ᵛ x, f x ∂[ContinuousLinearMap.mul ℝ ℂ; η] = ∫ f dη`.

## Main results

* `MeasureTheory.ComplexMeasure.isFiniteMeasure_variation`: the variation `|η|` of a complex
  measure is a finite measure (and similarly for signed measures).
* `MeasureTheory.Measure.integral_withDensityᵥ`: for an integrable density `h : X → F`, a
  continuous bilinear pairing `B` and `g` integrable against `|μ.withDensityᵥ h| = ‖h‖ μ`,
  `∫ᵛ x, g x ∂[B; μ.withDensityᵥ h] = ∫ x, B (g x) (h x) ∂μ`.
* `MeasureTheory.ComplexMeasure.integral_withDensityᵥ_of_integrable_mul`,
  `MeasureTheory.ComplexMeasure.integral_withDensityᵥ_of_bounded`,
  `MeasureTheory.ComplexMeasure.integral_withDensityᵥ_continuousMap`: the complex versions
  `∫ᵛ x, g x ∂[mul ℝ ℂ; μ.withDensityᵥ h] = ∫ x, g x * h x ∂μ`.
* `MeasurableEmbedding.vectorMeasure_map_eq_zero_iff`,
  `MeasureTheory.ComplexMeasure.integral_map_withDensityᵥ_of_bounded`: pushforwards along
  measurable embeddings (the integral itself is Mathlib's
  `MeasurableEmbedding.integral_map_vectorMeasure`).
* `MeasureTheory.ComplexMeasure.integral_const_mul`, `MeasureTheory.ComplexMeasure.integralCLM`:
  `ℂ`-linearity, and integration as a continuous `ℂ`-linear functional on `C(X, ℂ)`.
* `MeasureTheory.ComplexMeasure.eq_zero_of_forall_integral_eq_zero`,
  `MeasureTheory.ComplexMeasure.ext_of_forall_integral_eq`,
  `MeasureTheory.ComplexMeasure.eq_zero_of_forall_continuousMap_integral_eq_zero`: a complex
  Borel measure on a space with `HasOuterApproxClosed` (e.g. any pseudo-metrizable space) is
  determined by the integrals of bounded continuous functions.
* `MeasureTheory.Measure.withDensityᵥ_eq_zero_iff`, `MeasureTheory.Measure.withDensityᵥ_ne_zero`:
  the vector measure with an integrable density vanishes iff the density vanishes a.e.
-/

open Set Filter Topology
open scoped ENNReal NNReal BoundedContinuousFunction

noncomputable section

namespace MeasureTheory

variable {X : Type*} {mX : MeasurableSpace X}

/-! ### Finiteness of the variation -/

namespace SignedMeasure

/-- The variation of a signed measure is a finite measure. -/
instance isFiniteMeasure_variation (s : SignedMeasure X) :
    IsFiniteMeasure (VectorMeasure.variation s) := by
  rw [← s.totalVariation_eq_variation]
  unfold totalVariation
  infer_instance

end SignedMeasure

namespace ComplexMeasure

/-- The variation of a complex measure is dominated by the sum of the total variations of its
real and imaginary parts. -/
theorem variation_le_totalVariation_re_add_im (η : ComplexMeasure X) :
    η.variation ≤ (ComplexMeasure.re η).totalVariation + (ComplexMeasure.im η).totalVariation := by
  refine VectorMeasure.variation_le_of_forall_enorm_le fun s _ ↦ ?_
  have hre : ‖(ComplexMeasure.re η) s‖ₑ = ENNReal.ofReal |(η s).re| := by
    rw [Real.enorm_eq_ofReal_abs]; rfl
  have him : ‖(ComplexMeasure.im η) s‖ₑ = ENNReal.ofReal |(η s).im| := by
    rw [Real.enorm_eq_ofReal_abs]; rfl
  calc ‖η s‖ₑ = ENNReal.ofReal ‖η s‖ := (ofReal_norm _).symm
    _ ≤ ENNReal.ofReal (|(η s).re| + |(η s).im|) :=
        ENNReal.ofReal_le_ofReal (Complex.norm_le_abs_re_add_abs_im _)
    _ = ‖(ComplexMeasure.re η) s‖ₑ + ‖(ComplexMeasure.im η) s‖ₑ := by
        rw [hre, him, ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
    _ ≤ _ := add_le_add (SignedMeasure.enorm_le_totalVariation _ _)
        (SignedMeasure.enorm_le_totalVariation _ _)

/-- The variation `|η|` of a complex measure is a finite measure. -/
instance isFiniteMeasure_variation (η : ComplexMeasure X) : IsFiniteMeasure η.variation := by
  have : IsFiniteMeasure
      ((ComplexMeasure.re η).totalVariation + (ComplexMeasure.im η).totalVariation) := by
    unfold SignedMeasure.totalVariation
    infer_instance
  exact isFiniteMeasure_of_le _ (variation_le_totalVariation_re_add_im η)

end ComplexMeasure

/-- A nonzero vector measure lives on a nonempty type. -/
theorem VectorMeasure.nonempty_of_ne_zero {M : Type*} [AddCommMonoid M] [TopologicalSpace M]
    {v : VectorMeasure X M} (hv : v ≠ 0) : Nonempty X := by
  by_contra hX
  rw [not_nonempty_iff] at hX
  exact hv (Subsingleton.elim _ _)

/-! ### Densities -/

section WithDensity

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
  {μ : Measure X} {h : X → F} {g : X → E}

namespace Measure

omit [NormedSpace ℝ E] in
/-- A function is integrable against the vector measure `μ.withDensityᵥ h` iff it is integrable
against the positive measure with density `‖h‖`. -/
theorem integrable_withDensityᵥ_iff (hh : Integrable h μ) :
    (μ.withDensityᵥ h).Integrable g ↔ Integrable g (μ.withDensity fun x ↦ ‖h x‖ₑ) := by
  rw [VectorMeasure.Integrable, variation_withDensityᵥ hh]

/-- A sufficient condition for integrability against `μ.withDensityᵥ h`. -/
theorem integrable_withDensityᵥ_of_integrable_norm_mul (hh : Integrable h μ)
    (hg : AEStronglyMeasurable g μ) (hgh : Integrable (fun x ↦ ‖g x‖ * ‖h x‖) μ) :
    (μ.withDensityᵥ h).Integrable g := by
  rw [integrable_withDensityᵥ_iff hh, integrable_withDensity_iff_integrable_smul₀' hh.1.enorm
    (ae_of_all _ fun _ ↦ enorm_lt_top)]
  simp only [toReal_enorm]
  refine hgh.mono' (hh.1.norm.smul hg) (ae_of_all _ fun x ↦ ?_)
  rw [norm_smul, norm_norm, mul_comm]

/-- Bounded a.e.-strongly measurable functions are integrable against `μ.withDensityᵥ h`. -/
theorem integrable_withDensityᵥ_of_bounded (hh : Integrable h μ)
    (hg : AEStronglyMeasurable g μ) {C : ℝ} (hC : ∀ᵐ x ∂μ, ‖g x‖ ≤ C) :
    (μ.withDensityᵥ h).Integrable g := by
  refine integrable_withDensityᵥ_of_integrable_norm_mul hh hg
    ((hh.norm.const_mul C).mono' (hg.norm.mul hh.1.norm) ?_)
  filter_upwards [hC] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact mul_le_mul_of_nonneg_right hx (norm_nonneg _)

/-- **Integration against a vector measure with density.**  For an integrable density
`h : X → F`, a continuous bilinear pairing `B : E →L[ℝ] F →L[ℝ] G` and a function `g`
integrable against `μ.withDensityᵥ h` (equivalently, against the measure `‖h‖ μ`),
`∫ᵛ x, g x ∂[B; μ.withDensityᵥ h] = ∫ x, B (g x) (h x) ∂μ`. -/
theorem integral_withDensityᵥ (hh : Integrable h μ) (B : E →L[ℝ] F →L[ℝ] G)
    (hg : (μ.withDensityᵥ h).Integrable g) :
    ∫ᵛ x, g x ∂[B; μ.withDensityᵥ h] = ∫ x, B (g x) (h x) ∂μ := by
  set ν := μ.withDensityᵥ h with hν
  set ρ := ν.variation with hρ_def
  have hρ : ρ = μ.withDensity fun x ↦ ‖h x‖ₑ := variation_withDensityᵥ hh
  -- the normalized density `u = h / ‖h‖`
  set u : X → F := fun x ↦ ‖h x‖⁻¹ • h x with hu_def
  have hu_norm : ∀ x, ‖u x‖ ≤ 1 := fun x ↦ by
    rcases eq_or_ne (h x) 0 with hx | hx
    · simp [u, hx]
    · rw [hu_def, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 hx)]
  have hu_meas : AEStronglyMeasurable u ρ := by
    rw [hρ]
    exact (hh.1.norm.inv₀.smul hh.1).mono_ac (withDensity_absolutelyContinuous _ _)
  have hBu : ∀ {f : X → E}, Integrable f ρ → Integrable (fun x ↦ B (f x) (u x)) ρ := by
    intro f hf
    refine (hf.norm.const_mul ‖B‖).mono' (B.aestronglyMeasurable_comp₂ hf.1 hu_meas)
      (ae_of_all _ fun x ↦ ?_)
    calc ‖B (f x) (u x)‖ ≤ ‖B‖ * ‖f x‖ * ‖u x‖ := B.le_opNorm₂ _ _
      _ ≤ ‖B‖ * ‖f x‖ * 1 := by gcongr; exact hu_norm x
      _ = ‖B‖ * ‖f x‖ := mul_one _
  -- change of measure from `ρ = ‖h‖ μ` back to `μ`
  have hchange : ∀ f : X → E, ∫ x, B (f x) (u x) ∂ρ = ∫ x, B (f x) (h x) ∂μ := by
    intro f
    rw [hρ, integral_withDensity_eq_integral_toReal_smul₀ hh.1.enorm
      (ae_of_all _ fun _ ↦ enorm_lt_top)]
    congr 1
    ext x
    rw [toReal_enorm, ← _root_.map_smul]
    congr 1
    rcases eq_or_ne (h x) 0 with hx | hx
    · simp [u, hx]
    · rw [hu_def, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.2 hx), one_smul]
  rw [← hchange]
  refine Integrable.induction (μ := ρ)
    (fun f ↦ ∫ᵛ x, f x ∂[B; ν] = ∫ x, B (f x) (u x) ∂ρ) ?_ ?_ ?_ ?_ hg
  · -- indicator functions
    intro c s hs hsρ
    have : IsFiniteMeasure (ρ.restrict s) := isFiniteMeasure_restrict.2 hsρ.ne
    rw [VectorMeasure.integral_indicator_const c hs, hchange]
    have : (fun x ↦ B (s.indicator (fun _ ↦ c) x) (h x)) = s.indicator (fun x ↦ B c (h x)) := by
      ext x
      by_cases hx : x ∈ s <;> simp [hx]
    rw [this, integral_indicator hs, (B c).integral_comp_comm hh.integrableOn,
      withDensityᵥ_apply hh hs]
  · -- sums
    intro f f' _ hf hf' hfP hf'P
    have hadd : (fun x ↦ B ((f + f') x) (u x)) =
        fun x ↦ B (f x) (u x) + B (f' x) (u x) := by
      ext x
      simp
    rw [VectorMeasure.integral_add hf hf', hfP, hf'P, hadd, integral_add (hBu hf) (hBu hf')]
  · -- closedness in `L¹`
    refine isClosed_eq VectorMeasure.continuous_integral ?_
    refine (LipschitzWith.of_dist_le_mul (K := ‖B‖₊) fun f f' ↦ ?_).continuous
    rw [dist_eq_norm, ← integral_sub (hBu (L1.integrable_coeFn f)) (hBu (L1.integrable_coeFn f')),
      L1.dist_eq_integral_dist, coe_nnnorm, ← integral_const_mul]
    refine norm_integral_le_of_norm_le
      ((((L1.integrable_coeFn f).sub (L1.integrable_coeFn f')).norm.const_mul ‖B‖).congr
        (ae_of_all _ fun x ↦ by simp [dist_eq_norm])) (ae_of_all _ fun x ↦ ?_)
    rw [← ContinuousLinearMap.map_sub₂, dist_eq_norm]
    calc ‖B (f x - f' x) (u x)‖ ≤ ‖B‖ * ‖f x - f' x‖ * ‖u x‖ := B.le_opNorm₂ _ _
      _ ≤ ‖B‖ * ‖f x - f' x‖ * 1 := by gcongr; exact hu_norm x
      _ = ‖B‖ * ‖f x - f' x‖ := mul_one _
  · -- almost everywhere equal functions
    intro f f' hff' _ hfP
    rw [← VectorMeasure.integral_congr_ae hff', hfP]
    exact integral_congr_ae (hff'.mono fun x hx ↦ by simp [hx])

/-- The vector measure with an integrable density vanishes iff the density vanishes a.e. -/
theorem withDensityᵥ_eq_zero_iff (hh : Integrable h μ) :
    μ.withDensityᵥ h = 0 ↔ h =ᵐ[μ] 0 := by
  refine ⟨fun H ↦ hh.ae_eq_of_withDensityᵥ_eq (integrable_zero _ _ _)
    (H.trans withDensityᵥ_zero.symm), fun H ↦ ?_⟩
  rw [WithDensityᵥEq.congr_ae H, withDensityᵥ_zero]

/-- The vector measure with an integrable density which is not a.e. zero is nonzero. -/
theorem withDensityᵥ_ne_zero (hh : Integrable h μ) (h0 : ¬ h =ᵐ[μ] 0) :
    μ.withDensityᵥ h ≠ 0 :=
  fun H ↦ h0 ((withDensityᵥ_eq_zero_iff hh).1 H)

end Measure

end WithDensity

/-! ### Pushforwards -/

/-- The pushforward of a vector measure along a measurable embedding vanishes iff the vector
measure vanishes. -/
theorem _root_.MeasurableEmbedding.vectorMeasure_map_eq_zero_iff {Y : Type*} [MeasurableSpace Y]
    {M : Type*} [AddCommMonoid M] [TopologicalSpace M] {f : X → Y} (hf : MeasurableEmbedding f)
    {v : VectorMeasure X M} : v.map f = 0 ↔ v = 0 := by
  refine ⟨fun H ↦ VectorMeasure.ext fun s hs ↦ ?_, fun H ↦ by rw [H, VectorMeasure.map_zero]⟩
  have := congrArg (fun w : VectorMeasure Y M ↦ w (f '' s)) H
  simp only [VectorMeasure.map_apply _ hf.measurable (hf.measurableSet_image' hs),
    hf.injective.preimage_image, zero_apply] at this
  simpa using this

/-! ### Pullbacks along measurable embeddings -/

namespace VectorMeasure

section Comap

variable {α β M : Type*} [MeasurableSpace α] [MeasurableSpace β] [AddCommMonoid M]
  [TopologicalSpace M]

open Classical in
/-- The pullback of a vector measure along a measurable embedding `f`:
`(v.comap f) s = v (f '' s)` for measurable `s` (and `0` if `f` is not a measurable
embedding).  For `f = Subtype.val` this is the restriction of a vector measure to a measurable
subset, regarded as a measurable space in its own right. -/
def comap (f : α → β) (v : VectorMeasure β M) : VectorMeasure α M :=
  if hf : MeasurableEmbedding f then
    { measureOf' := fun s ↦ if MeasurableSet s then v (f '' s) else 0
      empty' := by simp
      not_measurable' := fun _ hs ↦ ite_eq_right hs
      m_iUnion' := fun s hs hdisj ↦ by
        simp only [hs, MeasurableSet.iUnion hs, ↓reduceIte, Set.image_iUnion]
        exact v.m_iUnion (fun i ↦ hf.measurableSet_image' (hs i))
          fun i j hij ↦ (Set.disjoint_image_iff hf.injective).2 (hdisj hij) }
  else 0

theorem comap_apply {f : α → β} (hf : MeasurableEmbedding f) (v : VectorMeasure β M)
    {s : Set α} (hs : MeasurableSet s) : v.comap f s = v (f '' s) := by
  rw [comap, dite_eq_left hf]
  exact ite_eq_left hs

@[simp]
theorem comap_zero (f : α → β) : (0 : VectorMeasure β M).comap f = 0 := by
  by_cases hf : MeasurableEmbedding f
  · ext s hs
    rw [comap_apply hf _ hs, zero_apply, zero_apply]
  · rw [comap, dite_eq_right hf]

theorem comap_map {f : α → β} (hf : MeasurableEmbedding f) (v : VectorMeasure α M) :
    (v.map f).comap f = v := by
  ext s hs
  rw [comap_apply hf _ hs, map_apply _ hf.measurable (hf.measurableSet_image' hs),
    hf.injective.preimage_image]

theorem map_comap {f : α → β} (hf : MeasurableEmbedding f) (v : VectorMeasure β M) :
    (v.comap f).map f = v.restrict (range f) := by
  ext t ht
  rw [map_apply _ hf.measurable ht, comap_apply hf _ (hf.measurable ht),
    restrict_apply _ hf.measurableSet_range ht, Set.image_preimage_eq_inter_range]

end Comap

section Concentrated

variable {α β F : Type*} [MeasurableSpace α] [MeasurableSpace β] [NormedAddCommGroup F]

/-- A vector measure whose variation vanishes off a measurable set `s` equals its restriction
to `s`. -/
theorem restrict_eq_self_of_variation_compl_eq_zero {v : VectorMeasure β F} {s : Set β}
    (hs : MeasurableSet s) (hv : v.variation sᶜ = 0) : v.restrict s = v := by
  ext t ht
  rw [restrict_apply _ hs ht]
  have h0 : v (t ∩ sᶜ) = 0 := by
    rw [← enorm_eq_zero, ← le_zero_iff, ← hv]
    exact (enorm_measure_le_variation _ _).trans (measure_mono inter_subset_right)
  have := of_union (v := v) ((disjoint_compl_right (a := s)).mono inter_subset_right
    inter_subset_right) (ht.inter hs) (ht.inter hs.compl)
  rw [inter_union_compl, h0, add_zero] at this
  exact this.symm

/-- If the variation of `v` vanishes off the range of a measurable embedding `f`, then `v` is the
pushforward of its pullback. -/
theorem map_comap_of_variation_compl_range_eq_zero {f : α → β} (hf : MeasurableEmbedding f)
    {v : VectorMeasure β F} (hv : v.variation (range f)ᶜ = 0) : (v.comap f).map f = v := by
  rw [map_comap hf, restrict_eq_self_of_variation_compl_eq_zero hf.measurableSet_range hv]

/-- If the variation of `v` vanishes off the range of a measurable embedding `f`, then the
pullback of `v` vanishes iff `v` does. -/
theorem comap_eq_zero_iff_of_variation_compl_range_eq_zero {f : α → β}
    (hf : MeasurableEmbedding f) {v : VectorMeasure β F} (hv : v.variation (range f)ᶜ = 0) :
    v.comap f = 0 ↔ v = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ by rw [h, comap_zero]⟩
  rw [← map_comap_of_variation_compl_range_eq_zero hf hv, h, map_zero]

/-- Integration against the pullback of a vector measure concentrated on the range of a
measurable embedding. -/
theorem integral_comap {E G : Type*} [NormedSpace ℝ F] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] {f : α → β} (hf : MeasurableEmbedding f)
    {v : VectorMeasure β F} (hv : v.variation (range f)ᶜ = 0) (B : E →L[ℝ] F →L[ℝ] G)
    (g : β → E) :
    ∫ᵛ x, g (f x) ∂[B; v.comap f] = ∫ᵛ y, g y ∂[B; v] := by
  rw [← hf.integral_map_vectorMeasure, map_comap_of_variation_compl_range_eq_zero hf hv]

end Concentrated

end VectorMeasure

/-! ### Complex measures -/

namespace ComplexMeasure

open ContinuousLinearMap

section Density

variable {μ : Measure X} {h : X → ℂ} {g : X → ℂ}

/-- Integration against `μ.withDensityᵥ h`: `∫ g d(h μ) = ∫ g h dμ`, for `g` a.e.-strongly
measurable with `g * h` integrable. -/
theorem integral_withDensityᵥ_of_integrable_mul (hh : Integrable h μ)
    (hg : AEStronglyMeasurable g μ) (hgh : Integrable (fun x ↦ g x * h x) μ) :
    ∫ᵛ x, g x ∂[ContinuousLinearMap.mul ℝ ℂ; μ.withDensityᵥ h] = ∫ x, g x * h x ∂μ := by
  rw [Measure.integral_withDensityᵥ hh _ (Measure.integrable_withDensityᵥ_of_integrable_norm_mul
    hh hg (by simpa only [norm_mul] using hgh.norm))]
  simp

/-- Integration against `μ.withDensityᵥ h` of a bounded a.e.-strongly measurable function. -/
theorem integral_withDensityᵥ_of_bounded (hh : Integrable h μ)
    (hg : AEStronglyMeasurable g μ) {C : ℝ} (hC : ∀ᵐ x ∂μ, ‖g x‖ ≤ C) :
    ∫ᵛ x, g x ∂[ContinuousLinearMap.mul ℝ ℂ; μ.withDensityᵥ h] = ∫ x, g x * h x ∂μ := by
  rw [Measure.integral_withDensityᵥ hh _ (Measure.integrable_withDensityᵥ_of_bounded hh hg hC)]
  simp

/-- Integration of a continuous function on a compact space against `μ.withDensityᵥ h`. -/
theorem integral_withDensityᵥ_continuousMap [TopologicalSpace X] [CompactSpace X]
    [OpensMeasurableSpace X] (hh : Integrable h μ) (g : C(X, ℂ)) :
    ∫ᵛ x, g x ∂[ContinuousLinearMap.mul ℝ ℂ; μ.withDensityᵥ h] = ∫ x, g x * h x ∂μ :=
  integral_withDensityᵥ_of_bounded hh g.continuous.aestronglyMeasurable
    (ae_of_all _ g.norm_coe_le_norm)

/-- Integration against the pushforward of `μ.withDensityᵥ h` along a measurable embedding. -/
theorem integral_map_withDensityᵥ_of_bounded {Y : Type*} [MeasurableSpace Y] {Γ : X → Y}
    (hΓ : MeasurableEmbedding Γ) (hh : Integrable h μ) {g : Y → ℂ}
    (hg : AEStronglyMeasurable (fun x ↦ g (Γ x)) μ) {C : ℝ} (hC : ∀ᵐ x ∂μ, ‖g (Γ x)‖ ≤ C) :
    ∫ᵛ y, g y ∂[ContinuousLinearMap.mul ℝ ℂ; (μ.withDensityᵥ h).map Γ] =
      ∫ x, g (Γ x) * h x ∂μ := by
  rw [hΓ.integral_map_vectorMeasure, integral_withDensityᵥ_of_bounded hh hg hC]

end Density

variable (η : ComplexMeasure X)

/-- The integral against a complex measure is `ℂ`-linear in the integrand. -/
theorem integral_const_mul (c : ℂ) (f : X → ℂ) :
    ∫ᵛ x, c * f x ∂[ContinuousLinearMap.mul ℝ ℂ; η] =
      c * ∫ᵛ x, f x ∂[ContinuousLinearMap.mul ℝ ℂ; η] := by
  simp only [VectorMeasure.integral_eq_setToFun]
  have := setToFun_smul (𝕜 := ℂ) (dominatedFinMeasAdditive_cbmApplyMeasure η
    (ContinuousLinearMap.mul ℝ ℂ)) (fun c s x ↦ ?_) c f
  · have hcf : (c • f) = fun x ↦ c * f x := rfl
    rwa [hcf] at this
  · rw [transpose_eq_cbmApplyMeasure, cbmApplyMeasure_apply, cbmApplyMeasure_apply]
    simp [mul_assoc]

/-- Bounded a.e.-strongly measurable functions are integrable against a complex measure. -/
theorem integrable_of_bounded {f : X → ℂ} (hf : AEStronglyMeasurable f η.variation) {C : ℝ}
    (hC : ∀ᵐ x ∂η.variation, ‖f x‖ ≤ C) : η.Integrable f :=
  Integrable.of_bound hf C hC

/-- Continuous functions on a compact space are integrable against a complex measure. -/
theorem integrable_continuousMap [TopologicalSpace X] [CompactSpace X] [OpensMeasurableSpace X]
    (f : C(X, ℂ)) : η.Integrable f :=
  η.integrable_of_bounded f.continuous.aestronglyMeasurable (ae_of_all _ f.norm_coe_le_norm)

/-- Integration against a complex measure, as a continuous `ℂ`-linear functional on `C(X, ℂ)`
for a compact space `X`. -/
def integralCLM [TopologicalSpace X] [CompactSpace X] [OpensMeasurableSpace X] :
    C(X, ℂ) →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun f ↦ ∫ᵛ x, f x ∂[ContinuousLinearMap.mul ℝ ℂ; η]
      map_add' := fun f g ↦ by
        simpa using VectorMeasure.integral_add (B := ContinuousLinearMap.mul ℝ ℂ)
          (η.integrable_continuousMap f) (η.integrable_continuousMap g)
      map_smul' := fun c f ↦ by
        simpa using η.integral_const_mul c f }
    (η.variation.real univ) fun f ↦ by
      simp only [LinearMap.coe_mk, AddHom.coe_mk]
      calc ‖∫ᵛ x, f x ∂[ContinuousLinearMap.mul ℝ ℂ; η]‖
          ≤ ‖f‖ * ‖ContinuousLinearMap.mul ℝ ℂ‖ * η.variation.real univ :=
            VectorMeasure.norm_integral_le_of_norm_le_const (ae_of_all _ f.norm_coe_le_norm)
        _ ≤ ‖f‖ * 1 * η.variation.real univ := by
            gcongr
            exact ContinuousLinearMap.opNorm_mul_le ℝ ℂ
        _ = η.variation.real univ * ‖f‖ := by ring

@[simp]
theorem integralCLM_apply [TopologicalSpace X] [CompactSpace X] [OpensMeasurableSpace X]
    (f : C(X, ℂ)) :
    η.integralCLM f = ∫ᵛ x, f x ∂[ContinuousLinearMap.mul ℝ ℂ; η] :=
  rfl

/-! ### Uniqueness -/

section Uniqueness

variable [TopologicalSpace X] [HasOuterApproxClosed X] [BorelSpace X]

/-- A complex Borel measure on a space with `HasOuterApproxClosed` (e.g. any pseudo-metrizable
space) which annihilates all real bounded continuous functions vanishes on closed sets. -/
theorem apply_isClosed_eq_zero_of_forall_integral_eq_zero {η : ComplexMeasure X}
    (h : ∀ f : X →ᵇ ℝ, ∫ᵛ x, (f x : ℂ) ∂[ContinuousLinearMap.mul ℝ ℂ; η] = 0)
    {F : Set X} (hF : IsClosed F) : η F = 0 := by
  let φ : ℕ → X →ᵇ ℝ := fun n ↦
    ⟨⟨fun x ↦ (hF.apprSeq n x : ℝ), NNReal.continuous_coe.comp (hF.apprSeq n).continuous⟩,
      (hF.apprSeq n).map_bounded'⟩
  have hφ : ∀ n x, φ n x = (hF.apprSeq n x : ℝ) := fun _ _ ↦ rfl
  have hlim : Tendsto (fun n ↦ ∫ᵛ x, ((φ n x : ℝ) : ℂ) ∂[ContinuousLinearMap.mul ℝ ℂ; η])
      atTop (𝓝 (∫ᵛ x, F.indicator (fun _ ↦ (1 : ℂ)) x ∂[ContinuousLinearMap.mul ℝ ℂ; η])) := by
    refine VectorMeasure.tendsto_integral_of_dominated_convergence (fun _ ↦ 1)
      (fun n ↦ (Complex.continuous_ofReal.comp (φ n).continuous).aestronglyMeasurable)
      (integrable_const _) (fun n ↦ ae_of_all _ fun x ↦ ?_) (ae_of_all _ fun x ↦ ?_)
    · rw [hφ, Complex.norm_real, Real.norm_eq_abs, NNReal.abs_eq]
      exact_mod_cast HasOuterApproxClosed.apprSeq_apply_le_one hF n x
    · have hx := tendsto_pi_nhds.1 (HasOuterApproxClosed.tendsto_apprSeq hF) x
      have hx' := ((Complex.continuous_ofReal.comp NNReal.continuous_coe).tendsto _).comp hx
      have hind : (Complex.ofReal ∘ NNReal.toReal) (F.indicator (fun _ ↦ (1 : ℝ≥0)) x) =
          F.indicator (fun _ ↦ (1 : ℂ)) x := by
        by_cases hxF : x ∈ F <;> simp [hxF]
      rw [hind] at hx'
      simpa only [hφ, Function.comp_def] using hx'
  rw [VectorMeasure.integral_indicator_const _ hF.measurableSet] at hlim
  simp only [ContinuousLinearMap.mul_apply', one_mul] at hlim
  simp only [h, tendsto_const_nhds_iff] at hlim
  exact hlim.symm

/-- **Uniqueness of complex measures.**  A complex Borel measure on a space with
`HasOuterApproxClosed` (e.g. any pseudo-metrizable space) which annihilates all real bounded
continuous functions is zero. -/
theorem eq_zero_of_forall_integral_eq_zero {η : ComplexMeasure X}
    (h : ∀ f : X →ᵇ ℝ, ∫ᵛ x, (f x : ℂ) ∂[ContinuousLinearMap.mul ℝ ℂ; η] = 0) : η = 0 := by
  have hclosed := fun F (hF : IsClosed F) ↦ apply_isClosed_eq_zero_of_forall_integral_eq_zero h hF
  have huniv : η univ = 0 := hclosed _ isClosed_univ
  have hcompl : ∀ t, MeasurableSet t → η t = 0 → η tᶜ = 0 := by
    intro t ht h0
    have := VectorMeasure.of_union (v := η) disjoint_compl_right ht ht.compl
    rw [union_compl_self, huniv, h0, zero_add] at this
    exact this.symm
  refine VectorMeasure.ext fun s hs ↦ ?_
  rw [zero_apply]
  induction s, hs using MeasurableSet.induction_on_open with
  | isOpen U hU => simpa using hcompl _ hU.measurableSet.compl (hclosed _ hU.isClosed_compl)
  | compl t ht iht => exact hcompl t ht iht
  | iUnion f hf hfm ihf =>
      rw [VectorMeasure.of_disjoint_iUnion hfm hf]
      simp [ihf]

/-- **Uniqueness of complex measures.**  Two complex Borel measures on a space with
`HasOuterApproxClosed` (e.g. any pseudo-metrizable space) with the same integrals of all real
bounded continuous functions are equal. -/
theorem ext_of_forall_integral_eq {η₁ η₂ : ComplexMeasure X}
    (h : ∀ f : X →ᵇ ℝ, ∫ᵛ x, (f x : ℂ) ∂[ContinuousLinearMap.mul ℝ ℂ; η₁] =
      ∫ᵛ x, (f x : ℂ) ∂[ContinuousLinearMap.mul ℝ ℂ; η₂]) : η₁ = η₂ := by
  rw [← sub_eq_zero]
  refine eq_zero_of_forall_integral_eq_zero fun f ↦ ?_
  have hint : ∀ η : ComplexMeasure X, η.Integrable fun x ↦ (f x : ℂ) := fun η ↦
    η.integrable_of_bounded (Complex.continuous_ofReal.comp f.continuous).aestronglyMeasurable
      (C := ‖f‖) (ae_of_all _ fun x ↦ by simpa using f.norm_coe_le_norm x)
  rw [VectorMeasure.integral_sub_vectorMeasure (hint η₁) (hint η₂), h f, sub_self]

/-- **Uniqueness of complex measures on compact spaces.**  A complex Borel measure on a compact
space with `HasOuterApproxClosed` (e.g. a compact metrizable space) which annihilates `C(X, ℂ)` is
zero. -/
theorem eq_zero_of_forall_continuousMap_integral_eq_zero [CompactSpace X]
    {η : ComplexMeasure X}
    (h : ∀ f : C(X, ℂ), ∫ᵛ x, f x ∂[ContinuousLinearMap.mul ℝ ℂ; η] = 0) : η = 0 :=
  eq_zero_of_forall_integral_eq_zero fun f ↦
    h ⟨fun x ↦ (f x : ℂ), Complex.continuous_ofReal.comp f.continuous⟩

end Uniqueness

end ComplexMeasure

end MeasureTheory
