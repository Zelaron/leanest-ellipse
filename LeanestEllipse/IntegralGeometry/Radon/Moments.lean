import LeanestEllipse.IntegralGeometry.Radon.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.InnerProductSpace.LinearMap
import LeanestEllipse.MeasureTheory.Function.EssentialSupport

/-!
# Radon moment tensors in arbitrary finite dimension

For an integrable function supported in a bounded set, its moment of order `j` is a
continuous multilinear form. On the diagonal this form is the offset moment of the Radon
transform. Thus the offset moments are homogeneous polynomials of degree `j` in the normal
vector. This is the dimension-independent Helgason–Ludwig moment condition used in the
article's final section; the angular expansion in the plane is developed separately in
`LeanestEllipse.EllipseCriterion.Moments`.

The multilinear forms and their estimates are defined before imposing finite dimensionality.
On a separable inner product space, the moment tensor can be integrated against any
measure; only the Radon identity uses Euclidean volume and finite dimensionality.
-/

open MeasureTheory
open scoped RealInnerProductSpace

noncomputable section

namespace RadonTransform

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The symmetric multilinear form `(v₁, …, vⱼ) ↦ ∏ᵢ ⟪x, vᵢ⟫`. -/
def innerMomentForm (j : ℕ) (x : E) : ContinuousMultilinearMap ℝ (fun _ : Fin j ↦ E) ℝ :=
  (ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin j) ℝ).compContinuousLinearMap
    (fun _ ↦ innerSL ℝ x)

@[simp]
theorem innerMomentForm_apply (j : ℕ) (x : E) (v : Fin j → E) :
    innerMomentForm j x v = ∏ i, ⟪x, v i⟫ := by
  simp [innerMomentForm]

/-- The norm of a rank-one moment form is bounded by the corresponding power of `‖x‖`. -/
theorem norm_innerMomentForm_le (j : ℕ) (x : E) : ‖innerMomentForm j x‖ ≤ ‖x‖ ^ j := by
  calc
    ‖innerMomentForm j x‖ ≤ ‖ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin j) ℝ‖ *
        ∏ _ : Fin j, ‖innerSL ℝ x‖ :=
      ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ = ‖x‖ ^ j := by simp [ContinuousMultilinearMap.norm_mkPiAlgebra, innerSL_apply_norm]

theorem continuous_innerMomentForm (j : ℕ) : Continuous (innerMomentForm (E := E) j) := by
  exact (ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin j) ℝ).compContinuousLinearMapLRight.cont.comp
    (continuous_pi fun _ ↦ (innerSL ℝ).continuous)

variable [MeasurableSpace E] {μ : Measure E}

/-- The `j`-th moment tensor of a vector-valued function. -/
def momentTensor (f : E → F) (j : ℕ) (μ : Measure E) :
    ContinuousMultilinearMap ℝ (fun _ : Fin j ↦ E) F :=
  ∫ x, (innerMomentForm j x).smulRight (f x) ∂μ

/-- Moment tensors depend only on the a.e. class of the function. -/
theorem momentTensor_congr_ae {f g : E → F} (hfg : f =ᵐ[μ] g) (j : ℕ) :
    momentTensor f j μ = momentTensor g j μ := by
  apply integral_congr_ae
  filter_upwards [hfg] with x hx
  rw [hx]

/-- Bounded support and integrability suffice to integrate all moment tensors. -/
theorem integrable_momentTensor_integrand [BorelSpace E] [SecondCountableTopology E]
    {f : E → F} (hf : Integrable f μ)
    {R : ℝ} (hR : ∀ᵐ x ∂μ, f x ≠ 0 → ‖x‖ ≤ R) (j : ℕ) :
    Integrable (fun x ↦ (innerMomentForm j x).smulRight (f x)) μ := by
  refine Integrable.mono' (hf.norm.const_mul (|R| ^ j)) ?_ ?_
  · exact (ContinuousMultilinearMap.smulRightL ℝ (fun _ : Fin j ↦ E) F).aestronglyMeasurable_comp₂
      (continuous_innerMomentForm j).aestronglyMeasurable hf.aestronglyMeasurable
  · filter_upwards [hR] with x hRx
    by_cases hx : f x = 0
    · simp [hx]
    · rw [ContinuousMultilinearMap.norm_smulRight]
      exact mul_le_mul_of_nonneg_right
        ((norm_innerMomentForm_le j x).trans
          (pow_le_pow_left₀ (norm_nonneg _) ((hRx hx).trans (le_abs_self R)) j))
        (norm_nonneg _)

/-- Evaluation of a moment tensor commutes with integration. -/
theorem momentTensor_apply [BorelSpace E] [SecondCountableTopology E]
    {f : E → F} (hf : Integrable f μ)
    {R : ℝ} (hR : ∀ᵐ x ∂μ, f x ≠ 0 → ‖x‖ ≤ R) (j : ℕ) (v : Fin j → E) :
    momentTensor f j μ v = ∫ x, (∏ i, ⟪x, v i⟫) • f x ∂μ := by
  rw [momentTensor, ContinuousMultilinearMap.integral_apply
    (integrable_momentTensor_integrand hf hR j)]
  congr 1

/-- The moment tensor is symmetric in its arguments. -/
theorem momentTensor_apply_perm [BorelSpace E] [SecondCountableTopology E]
    {f : E → F} (hf : Integrable f μ)
    {R : ℝ} (hR : ∀ᵐ x ∂μ, f x ≠ 0 → ‖x‖ ≤ R) (j : ℕ) (v : Fin j → E)
    (e : Equiv.Perm (Fin j)) :
    momentTensor f j μ (v ∘ e) = momentTensor f j μ v := by
  rw [momentTensor_apply hf hR, momentTensor_apply hf hR]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x ↦
    congrArg (fun t : ℝ ↦ t • f x) (Equiv.prod_comp e (fun i ↦ ⟪x, v i⟫))

/-- The diagonal of the moment tensor is a homogeneous polynomial of degree `j`. -/
theorem momentTensor_diagonal_smul (f : E → F) (j : ℕ) (c : ℝ) (ω : E) :
    momentTensor f j μ (fun _ ↦ c • ω) = c ^ j • momentTensor f j μ (fun _ ↦ ω) := by
  simpa using (momentTensor f j μ).map_smul_univ (fun _ ↦ c) (fun _ ↦ ω)

/-- A continuous multilinear form, evaluated diagonally, gives a continuous moment polynomial. -/
theorem continuous_momentTensor_diagonal (f : E → F) (j : ℕ) :
    Continuous fun ω : E ↦ momentTensor f j μ (fun _ ↦ ω) :=
  (momentTensor f j μ).cont.comp (continuous_pi fun _ ↦ continuous_id)

variable [FiniteDimensional ℝ E] [BorelSpace E]

/-- **Helgason–Ludwig moment conditions in any finite dimension.** The `j`-th offset moment
of the Radon transform is the restriction to unit normals of the diagonal moment polynomial. -/
theorem integral_pow_smul_radonTransform_eq_momentTensor [CompleteSpace F]
    {f : E → F} (hf : Integrable f)
    {R : ℝ} (hR : ∀ᵐ x, f x ≠ 0 → ‖x‖ ≤ R) (j : ℕ) {ω : E} (hω : ‖ω‖ = 1) :
    ∫ p : ℝ, p ^ j • radonTransform f ω p = momentTensor f j volume (fun _ ↦ ω) := by
  have hint := (integrable_momentTensor_integrand hf hR j)
  have heval := ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin j ↦ E) F
    (fun _ ↦ ω)).integrable_comp hint)
  have hweighted : Integrable (fun x ↦ ⟪x, ω⟫ ^ j • f x) := by
    simpa using heval
  rw [integral_pow_smul_radonTransform hω j hweighted, momentTensor_apply hf hR]
  simp

/-- The moment-polynomial identity for compactly supported integrable functions, as stated
in the article. No smoothness is required. -/
theorem integral_pow_smul_radonTransform_eq_momentTensor_of_hasCompactSupport [CompleteSpace F]
    {f : E → F} (hf : Integrable f) (hc : HasCompactSupport f) (j : ℕ)
    {ω : E} (hω : ‖ω‖ = 1) :
    ∫ p : ℝ, p ^ j • radonTransform f ω p = momentTensor f j volume (fun _ ↦ ω) := by
  obtain ⟨R, hR⟩ := (show IsCompact (tsupport f) from hc).isBounded.exists_norm_le
  exact integral_pow_smul_radonTransform_eq_momentTensor hf
    (Filter.Eventually.of_forall fun x hx ↦ hR x (subset_tsupport f hx)) j hω

/-- Essential compact support suffices: the moment identity holds for every representative
of a compactly supported L¹ class. -/
theorem integral_pow_smul_radonTransform_eq_momentTensor_of_isCompact_essSupport [CompleteSpace F]
    {f : E → F} (hf : Integrable f) (hc : IsCompact (essSupport f volume)) (j : ℕ)
    {ω : E} (hω : ‖ω‖ = 1) :
    ∫ p : ℝ, p ^ j • radonTransform f ω p = momentTensor f j volume (fun _ ↦ ω) := by
  obtain ⟨R, hR⟩ := hc.isBounded.exists_norm_le
  have hb : ∀ᵐ x, f x ≠ 0 → ‖x‖ ≤ R := by
    filter_upwards [ae_eq_zero_of_notMem_essSupport (f := f) (μ := volume)] with x hx hfx
    exact hR x (not_imp_comm.mp hx hfx)
  exact integral_pow_smul_radonTransform_eq_momentTensor hf hb j hω

end RadonTransform
