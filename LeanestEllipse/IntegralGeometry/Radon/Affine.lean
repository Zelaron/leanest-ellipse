import LeanestEllipse.IntegralGeometry.Radon.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Affine covariance of the Radon transform

Let `A : E ≃L[ℝ] E` be invertible, `c : E`, and `u x = f (A⁻¹ (x - c))`.  The hyperplane
`{x | ⟪x, ω⟫ = p}` is mapped by `x ↦ A⁻¹ (x - c)` onto the hyperplane with unit normal
`ω' = A* ω / ‖A* ω‖` and offset `(p - ⟪c, ω⟫) / ‖A* ω‖`, and ([Hägg, (2.2)])

`𝓡 u ω p = (|det A| / ‖A* ω‖) • 𝓡 f ω' ((p - ⟪c, ω⟫) / ‖A* ω‖)`.

## Main results

* `RadonTransform.exists_pos_radonTransform_comp_symm`: the linear case, with a positive constant
  given by Haar uniqueness on the hyperplane;
* `radonTransform_comp_linearEquiv_symm`: the linear case with the exact constant
  `|det A| / ‖A* ω‖`;
* `radonTransform_comp_affine`: the affine case;
* `integral_comp_continuousLinearEquiv_symm`: `∫ g (A⁻¹ x) dx = |det A| ∫ g`.
-/

open MeasureTheory Set Submodule Metric
open scoped RealInnerProductSpace NNReal

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

namespace RadonTransform

variable (A : E ≃L[ℝ] E)

/-- The adjoint of (the underlying continuous linear map of) `A`. -/
abbrev adj : E →L[ℝ] E := ContinuousLinearMap.adjoint (A : E →L[ℝ] E)

theorem inner_adj (x ω : E) : ⟪x, adj A ω⟫ = ⟪A x, ω⟫ :=
  ContinuousLinearMap.adjoint_inner_right _ _ _

theorem inner_symm_adj (x ω : E) : ⟪A.symm x, adj A ω⟫ = ⟪x, ω⟫ := by
  rw [inner_adj]
  simp

theorem adj_injective : Function.Injective (adj A) := by
  intro x y h
  refine ext_inner_left ℝ fun z ↦ ?_
  obtain ⟨w, rfl⟩ := A.surjective z
  rw [← inner_adj, h, inner_adj]

theorem adj_ne_zero {ω : E} (hω : ω ≠ 0) : adj A ω ≠ 0 := fun h ↦
  hω (adj_injective A (h.trans (map_zero _).symm))

/-- The unit normal `A* ω / ‖A* ω‖` of the image hyperplane. -/
def adjNormal (ω : E) : E := ‖adj A ω‖⁻¹ • adj A ω

variable {A} {ω : E}

theorem norm_adjNormal (hω : ω ≠ 0) : ‖adjNormal A ω‖ = 1 := by
  rw [adjNormal, norm_smul, norm_inv, norm_norm,
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr (adj_ne_zero A hω))]

theorem inner_symm_adjNormal (x : E) :
    ⟪A.symm x, adjNormal A ω⟫ = ‖adj A ω‖⁻¹ * ⟪x, ω⟫ := by
  rw [adjNormal, real_inner_smul_right, inner_symm_adj]

variable (A) in
/-- `A⁻¹` maps the hyperplane `ω^⊥` onto `(A* ω)^⊥`. -/
def hyperplaneEquiv (ω : E) : (ℝ ∙ ω)ᗮ ≃ₗ[ℝ] (ℝ ∙ adjNormal A ω)ᗮ where
  toFun y := ⟨A.symm y, by
    rw [mem_orthogonal_singleton_iff_inner_right, real_inner_comm, inner_symm_adjNormal,
      inner_orthogonal_eq_zero, mul_zero]⟩
  invFun w := ⟨A w, by
    rw [mem_orthogonal_singleton_iff_inner_right, real_inner_comm, ← inner_adj]
    by_cases hω : adj A ω = 0
    · rw [hω, inner_zero_right]
    · have h : ⟪(w : E), ‖adj A ω‖⁻¹ • adj A ω⟫ = 0 := inner_orthogonal_eq_zero w
      rw [real_inner_smul_right] at h
      exact (mul_eq_zero.mp h).resolve_left (inv_ne_zero (norm_ne_zero_iff.mpr hω))⟩
  map_add' y z := by ext; simp
  map_smul' c y := by ext; simp
  left_inv y := by ext; simp
  right_inv w := by ext; simp

variable [MeasurableSpace E] [BorelSpace E]

variable (A) in
/-- `hyperplaneEquiv` as a measurable equivalence. -/
def hyperplaneMeasurableEquiv (ω : E) : (ℝ ∙ ω)ᗮ ≃ᵐ (ℝ ∙ adjNormal A ω)ᗮ :=
  (hyperplaneEquiv A ω).toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv

theorem coe_hyperplaneMeasurableEquiv (y : (ℝ ∙ ω)ᗮ) :
    (hyperplaneMeasurableEquiv A ω y : E) = A.symm y := rfl

variable (A) in
instance isAddHaarMeasure_map_hyperplaneMeasurableEquiv (ω : E) :
    (Measure.map (hyperplaneMeasurableEquiv A ω) volume).IsAddHaarMeasure :=
  (hyperplaneEquiv A ω).toContinuousLinearEquiv.isAddHaarMeasure_map volume

variable (A) in
/-- The Jacobian of `A⁻¹ : ω^⊥ → (A* ω)^⊥`: the Haar scaling factor between the push-forward of
Lebesgue measure on `ω^⊥` and Lebesgue measure on `(A* ω)^⊥`.  It equals `|det A| / ‖A* ω‖`
for unit `ω` (`RadonTransform.hyperplaneScale_eq`). -/
def hyperplaneScale (ω : E) : ℝ :=
  Measure.addHaarScalarFactor (Measure.map (hyperplaneMeasurableEquiv A ω) volume) volume

theorem map_hyperplaneMeasurableEquiv :
    Measure.map (hyperplaneMeasurableEquiv A ω) volume =
      (Measure.addHaarScalarFactor (Measure.map (hyperplaneMeasurableEquiv A ω) volume)
        volume : ℝ≥0) • volume :=
  Measure.isAddLeftInvariant_eq_smul _ _

theorem hyperplaneScale_pos : 0 < hyperplaneScale A ω := by
  rw [hyperplaneScale]
  refine lt_of_le_of_ne (NNReal.coe_nonneg _) (Ne.symm ?_)
  intro h
  have h0 : Measure.addHaarScalarFactor (Measure.map (hyperplaneMeasurableEquiv A ω) volume)
      volume = 0 := by exact_mod_cast h
  have hμ := map_hyperplaneMeasurableEquiv (A := A) (ω := ω)
  rw [h0, zero_smul] at hμ
  have := congrArg (fun m : Measure (ℝ ∙ adjNormal A ω)ᗮ ↦ m univ) hμ
  simp only [Measure.map_apply (hyperplaneMeasurableEquiv A ω).measurable MeasurableSet.univ,
    preimage_univ, Measure.coe_zero, Pi.zero_apply] at this
  exact (Measure.measure_univ_pos.mpr (NeZero.ne (volume : Measure (ℝ ∙ ω)ᗮ))).ne' this

/-- **Affine covariance, linear case, with the hyperplane Jacobian.**  For a unit vector `ω`,
`𝓡 (f ∘ A⁻¹) ω q = J • 𝓡 f ω' (q / ‖A* ω‖)` where `ω' = A* ω / ‖A* ω‖` and `J` is the
Jacobian `hyperplaneScale A ω`. -/
theorem radonTransform_comp_symm_eq_hyperplaneScale_smul (hω : ‖ω‖ = 1) (f : E → F) (q : ℝ) :
    radonTransform (fun x ↦ f (A.symm x)) ω q =
      hyperplaneScale A ω • radonTransform f (adjNormal A ω) (q / ‖adj A ω‖) := by
  have hω0 : ω ≠ 0 := norm_ne_zero_iff.mp (by rw [hω]; norm_num)
  set s := ‖adj A ω‖ with hs_def
  have hs : 0 < s := norm_pos_iff.mpr (adj_ne_zero A hω0)
  set ω' := adjNormal A ω with hω'_def
  set e := hyperplaneMeasurableEquiv A ω
  have hw₀ : q • A.symm ω - (q / s) • ω' ∈ (ℝ ∙ ω')ᗮ := by
    rw [mem_orthogonal_singleton_iff_inner_right, inner_sub_right, real_inner_smul_right,
      real_inner_smul_right, real_inner_comm, inner_symm_adjNormal, real_inner_self_eq_norm_sq,
      real_inner_self_eq_norm_sq, hω, norm_adjNormal hω0, ← hs_def]
    field_simp
    ring
  set w₀ : (ℝ ∙ ω')ᗮ := ⟨_, hw₀⟩
  have hpt : ∀ y : (ℝ ∙ ω)ᗮ,
      A.symm (q • ω + y) = (q / s) • ω' + ((w₀ + e y : (ℝ ∙ ω')ᗮ) : E) := by
    intro y
    simp only [Submodule.coe_add, e, coe_hyperplaneMeasurableEquiv, w₀, map_add, map_smul]
    abel
  calc radonTransform (fun x ↦ f (A.symm x)) ω q
      = ∫ y : (ℝ ∙ ω)ᗮ, f ((q / s) • ω' + ((w₀ + e y : (ℝ ∙ ω')ᗮ) : E)) := by
        simp only [radonTransform, hpt]
    _ = ∫ w, f ((q / s) • ω' + ((w₀ + w : (ℝ ∙ ω')ᗮ) : E)) ∂(Measure.map e volume) :=
        (integral_map_equiv e (fun w ↦ f ((q / s) • ω' + ((w₀ + w : (ℝ ∙ ω')ᗮ) : E)))).symm
    _ = hyperplaneScale A ω • ∫ w, f ((q / s) • ω' + ((w₀ + w : (ℝ ∙ ω')ᗮ) : E)) := by
        rw [map_hyperplaneMeasurableEquiv, integral_smul_nnreal_measure, NNReal.smul_def]
        rfl
    _ = hyperplaneScale A ω • ∫ w : (ℝ ∙ ω')ᗮ, f ((q / s) • ω' + (w : E)) := by
        rw [integral_add_left_eq_self (fun w : (ℝ ∙ ω')ᗮ ↦ f ((q / s) • ω' + (w : E))) w₀]
    _ = hyperplaneScale A ω • radonTransform f ω' (q / s) := rfl

end RadonTransform

open RadonTransform

variable [MeasurableSpace E] [BorelSpace E]

/-- **Linear change of variables**: `∫ g (A⁻¹ x) dx = |det A| ∫ g`. -/
theorem integral_comp_continuousLinearEquiv_symm [CompleteSpace F] (A : E ≃L[ℝ] E)
    (g : E → F) :
    ∫ x, g (A.symm x) = |LinearMap.det (A : E →ₗ[ℝ] E)| • ∫ x, g x := by
  have hdet : LinearMap.det ((A.symm : E →L[ℝ] E) : E →ₗ[ℝ] E) =
      (LinearMap.det (A : E →ₗ[ℝ] E))⁻¹ := by
    have := LinearEquiv.det_coe_symm A.toLinearEquiv
    simpa using this
  have hA : LinearMap.det (A : E →ₗ[ℝ] E) ≠ 0 := by
    have := LinearEquiv.isUnit_det' A.toLinearEquiv
    simpa using this.ne_zero
  have hne : LinearMap.det ((A.symm : E →L[ℝ] E) : E →ₗ[ℝ] E) ≠ 0 := by
    rw [hdet]; exact inv_ne_zero hA
  have hmap := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure E) hne
  rw [hdet, inv_inv] at hmap
  let e : E ≃ᵐ E := A.symm.toHomeomorph.toMeasurableEquiv
  have hmap' : Measure.map e volume =
      ENNReal.ofReal |LinearMap.det (A : E →ₗ[ℝ] E)| • volume := hmap
  calc ∫ x, g (A.symm x) = ∫ x, g x ∂(Measure.map e volume) := by
        rw [integral_map_equiv]; rfl
    _ = ∫ x, g x ∂(ENNReal.ofReal |LinearMap.det (A : E →ₗ[ℝ] E)| • volume) := by
        rw [hmap']
    _ = |LinearMap.det (A : E →ₗ[ℝ] E)| • ∫ x, g x := by
        rw [integral_smul_measure, ENNReal.toReal_ofReal (abs_nonneg _)]

/-- The hyperplane Jacobian of `A⁻¹` is `|det A| / ‖A* ω‖` (for unit `ω`). -/
theorem RadonTransform.hyperplaneScale_eq (A : E ≃L[ℝ] E) {ω : E} (hω : ‖ω‖ = 1) :
    hyperplaneScale A ω = |LinearMap.det (A : E →ₗ[ℝ] E)| / ‖adj A ω‖ := by
  have hω0 : ω ≠ 0 := norm_ne_zero_iff.mp (by rw [hω]; norm_num)
  have : Nontrivial E := ⟨⟨ω, 0, hω0⟩⟩
  have hs : 0 < ‖adj A ω‖ := norm_pos_iff.mpr (adj_ne_zero A hω0)
  have hω' : ‖adjNormal A ω‖ = 1 := norm_adjNormal hω0
  -- test with the indicator of the closed unit ball
  set f₀ : E → ℝ := (closedBall (0 : E) 1).indicator 1
  have hf₀ : Integrable f₀ :=
    (integrableOn_const measure_closedBall_lt_top.ne).integrable_indicator measurableSet_closedBall
  have hint₀ : 0 < ∫ x, f₀ x := by
    rw [integral_indicator_one measurableSet_closedBall, measureReal_def]
    exact ENNReal.toReal_pos (measure_closedBall_pos volume 0 one_pos).ne'
      measure_closedBall_lt_top.ne
  have hf₀A : Integrable fun x ↦ f₀ (A.symm x) := by
    have hK : IsCompact (A.symm ⁻¹' closedBall (0 : E) 1) := by
      rw [← A.image_eq_preimage_symm]
      exact (isCompact_closedBall 0 1).image A.continuous
    have heq : (fun x ↦ f₀ (A.symm x)) = (A.symm ⁻¹' closedBall (0 : E) 1).indicator 1 := by
      ext x
      simp [f₀, indicator]
    rw [heq]
    exact (integrableOn_const hK.measure_lt_top.ne).integrable_indicator
      (measurableSet_closedBall.preimage A.symm.continuous.measurable)
  have h1 : ∫ q, radonTransform (fun x ↦ f₀ (A.symm x)) ω q =
      |LinearMap.det (A : E →ₗ[ℝ] E)| * ∫ x, f₀ x := by
    rw [integral_radonTransform hf₀A hω, integral_comp_continuousLinearEquiv_symm, smul_eq_mul]
  have h2 : ∫ q, radonTransform (fun x ↦ f₀ (A.symm x)) ω q =
      hyperplaneScale A ω * ‖adj A ω‖ * ∫ x, f₀ x := by
    simp_rw [radonTransform_comp_symm_eq_hyperplaneScale_smul hω, smul_eq_mul]
    rw [integral_const_mul, Measure.integral_comp_div (fun p ↦ radonTransform f₀ (adjNormal A ω) p),
      integral_radonTransform hf₀ hω', abs_of_pos hs, smul_eq_mul, mul_assoc]
  have h3 : hyperplaneScale A ω * ‖adj A ω‖ = |LinearMap.det (A : E →ₗ[ℝ] E)| :=
    mul_right_cancel₀ hint₀.ne' (h2.symm.trans h1)
  field_simp
  linarith

/-- **Affine covariance, linear case** ([Hägg, (2.2)] with `c = 0`):
`𝓡 (f ∘ A⁻¹) ω q = (|det A| / ‖A* ω‖) • 𝓡 f (A* ω / ‖A* ω‖) (q / ‖A* ω‖)`. -/
theorem radonTransform_comp_linearEquiv_symm (A : E ≃L[ℝ] E) {ω : E}
    (hω : ‖ω‖ = 1) (f : E → F) (q : ℝ) :
    radonTransform (fun x ↦ f (A.symm x)) ω q =
      (|LinearMap.det (A : E →ₗ[ℝ] E)| / ‖adj A ω‖) •
        radonTransform f (adjNormal A ω) (q / ‖adj A ω‖) := by
  rw [radonTransform_comp_symm_eq_hyperplaneScale_smul hω, hyperplaneScale_eq A hω]

/-- **Affine covariance of the Radon transform** ([Hägg, (2.2)]): for `u x = f (A⁻¹ (x - c))`,
`𝓡 u ω p = (|det A| / ‖A* ω‖) • 𝓡 f (A* ω / ‖A* ω‖) ((p - ⟪c, ω⟫) / ‖A* ω‖)`. -/
theorem radonTransform_comp_affine (A : E ≃L[ℝ] E) (c : E) {ω : E} (hω : ‖ω‖ = 1)
    (f : E → F) (p : ℝ) :
    radonTransform (fun x ↦ f (A.symm (x - c))) ω p =
      (|LinearMap.det (A : E →ₗ[ℝ] E)| / ‖adj A ω‖) •
        radonTransform f (adjNormal A ω) ((p - ⟪c, ω⟫) / ‖adj A ω‖) := by
  have h := radonTransform_comp_add_right hω (fun x ↦ f (A.symm x)) (-c) p
  simp only [← sub_eq_add_neg, inner_neg_left] at h
  rw [h, radonTransform_comp_linearEquiv_symm A hω]

end
