import LeanestEllipse.IntegralGeometry.Radon.Plane
import Mathlib.MeasureTheory.Function.L1Space.AEEqFun

/-!
# The planar Radon transform on joint L¹ space

The direction and offset are integrated together, against a finite measure on the unit
circle and Lebesgue measure on `ℝ`. In particular, surface measure gives the arc-length
normalization in the introduction of the article.

The results apply to arbitrary integrable representatives, not just Borel functions.
Changing the representative on a null set changes the joint transform only on a null set.
The joint L¹ norm is bounded by the total direction measure times the original L¹ norm.
-/

open MeasureTheory Set Metric

noncomputable section

namespace Complex

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Points on all oriented lines, in direction and offset coordinates. -/
def sphereLinePoint (z : (sphere (0 : ℂ) 1 × ℝ) × ℝ) : ℂ :=
  (z.1.1 : ℂ) * (z.1.2 + z.2 * I)

theorem measurable_sphereLinePoint : Measurable sphereLinePoint := by
  unfold sphereLinePoint
  fun_prop

/-- Orthogonal line coordinates preserve planar Lebesgue measure. -/
theorem measurePreserving_mul_equivRealProd_symm {ω : ℂ} (hω : ‖ω‖ = 1) :
    MeasurePreserving (fun z : ℝ × ℝ ↦ ω * (z.1 + z.2 * I)) := by
  have h := measurePreserving_rotate_equivRealProd_symm (arg ω)
  have he : exp (arg ω * I) = ω := by
    simpa [hω] using norm_mul_exp_arg_mul_I ω
  simpa only [he] using h

variable (μ : Measure (sphere (0 : ℂ) 1))

/-- Joint line coordinates do not charge planar Lebesgue null sets, for any direction
measure. -/
theorem quasiMeasurePreserving_sphereLinePoint :
    Measure.QuasiMeasurePreserving sphereLinePoint ((μ.prod volume).prod volume) volume := by
  refine ⟨measurable_sphereLinePoint, Measure.AbsolutelyContinuous.mk fun s hs h0 ↦ ?_⟩
  rw [Measure.map_apply measurable_sphereLinePoint hs]
  set A : Set (sphere (0 : ℂ) 1 × ℝ × ℝ) :=
    {z | (z.1 : ℂ) * (z.2.1 + z.2.2 * I) ∈ s}
  have hA : MeasurableSet A := hs.preimage (by fun_prop)
  have hpre : sphereLinePoint ⁻¹' s = MeasurableEquiv.prodAssoc ⁻¹' A := by
    ext z
    rfl
  rw [hpre, (measurePreserving_prodAssoc μ volume volume).measure_preimage
    hA.nullMeasurableSet, Measure.prod_apply hA]
  have hω : ∀ ω : sphere (0 : ℂ) 1, (volume.prod volume) (Prod.mk ω ⁻¹' A) = 0 := by
    intro ω
    have h := (measurePreserving_mul_equivRealProd_symm (by simp : ‖(ω : ℂ)‖ = 1)).measure_preimage
      hs.nullMeasurableSet
    rw [← Measure.volume_eq_prod,
      show Prod.mk ω ⁻¹' A = (fun z : ℝ × ℝ ↦ (ω : ℂ) * (z.1 + z.2 * I)) ⁻¹' s from rfl,
      h, h0]
  simp [hω]

/-- A null-set change of the input is a null-set change of the joint planar Radon transform. -/
theorem radonTransform_sphere_ae_eq_of_ae_eq {f g : ℂ → F} (hfg : f =ᵐ[volume] g) :
    (fun z : sphere (0 : ℂ) 1 × ℝ ↦ radonTransform f (z.1 : ℂ) z.2) =ᵐ[μ.prod volume]
      (fun z ↦ radonTransform g (z.1 : ℂ) z.2) := by
  have h := (quasiMeasurePreserving_sphereLinePoint μ).ae_eq_comp hfg
  filter_upwards [Measure.ae_ae_eq_curry_of_prod h] with z hz
  rw [radonTransform_eq_integral (by simp), radonTransform_eq_integral (by simp)]
  exact integral_congr_ae hz

/-- Joint a.e. strong measurability for an a.e. strongly measurable input. -/
theorem aestronglyMeasurable_radonTransform_sphere {f : ℂ → F}
    (hf : AEStronglyMeasurable f volume) :
    AEStronglyMeasurable (fun z : sphere (0 : ℂ) 1 × ℝ ↦ radonTransform f (z.1 : ℂ) z.2)
      (μ.prod volume) := by
  exact (stronglyMeasurable_radonTransform_sphere
    hf.stronglyMeasurable_mk).aestronglyMeasurable.congr
    (radonTransform_sphere_ae_eq_of_ae_eq μ hf.ae_eq_mk).symm

variable [IsFiniteMeasure μ]

/-- An integrable planar function has an integrable joint Radon transform for every finite
direction measure. -/
theorem integrable_radonTransform_sphere {f : ℂ → F} (hf : Integrable f) :
    Integrable (fun z : sphere (0 : ℂ) 1 × ℝ ↦ radonTransform f (z.1 : ℂ) z.2)
      (μ.prod volume) := by
  refine (integrable_prod_iff (μ := μ) (ν := (volume : Measure ℝ))
    (aestronglyMeasurable_radonTransform_sphere μ hf.aestronglyMeasurable)).mpr ⟨?_, ?_⟩
  · exact Filter.Eventually.of_forall fun ω : sphere (0 : ℂ) 1 ↦
      _root_.integrable_radonTransform hf (ω := (ω : ℂ)) (by simp)
  · have hm : AEStronglyMeasurable
        (fun ω : sphere (0 : ℂ) 1 ↦ ∫ p : ℝ, ‖radonTransform f (ω : ℂ) p‖) μ :=
      (aestronglyMeasurable_radonTransform_sphere μ
        hf.aestronglyMeasurable).norm.integral_prod_right'
    refine Integrable.mono' (integrable_const (∫ x, ‖f x‖)) hm ?_
    exact Filter.Eventually.of_forall fun ω : sphere (0 : ℂ) 1 ↦ by
      have hn : 0 ≤ ∫ p : ℝ, ‖radonTransform f (ω : ℂ) p‖ :=
        integral_nonneg fun p ↦ norm_nonneg (radonTransform f (ω : ℂ) p)
      simpa only [Real.norm_of_nonneg hn] using
        integral_norm_radonTransform_le hf (ω := (ω : ℂ)) (by simp)

/-- The joint L¹ estimate, with the total mass of the direction measure as constant. -/
theorem integral_norm_radonTransform_sphere_le {f : ℂ → F} (hf : Integrable f) :
    ∫ z : sphere (0 : ℂ) 1 × ℝ, ‖radonTransform f (z.1 : ℂ) z.2‖ ∂(μ.prod volume) ≤
      μ.real univ * ∫ x, ‖f x‖ := by
  rw [integral_prod _ (integrable_radonTransform_sphere μ hf).norm]
  calc
    ∫ ω : sphere (0 : ℂ) 1, (∫ p : ℝ, ‖radonTransform f (ω : ℂ) p‖) ∂μ ≤
        ∫ _ : sphere (0 : ℂ) 1, (∫ x, ‖f x‖) ∂μ := by
      exact integral_mono_ae (integrable_radonTransform_sphere μ hf).norm.integral_prod_left
        (integrable_const _) (Filter.Eventually.of_forall fun ω ↦
          integral_norm_radonTransform_le hf (by simp))
    _ = μ.real univ * ∫ x, ‖f x‖ := by simp [Measure.real, smul_eq_mul]

/-- The integral form of the article's joint L¹ estimate for arc-length measure. -/
theorem integral_norm_radonTransform_sphere_surface_le {f : ℂ → F} (hf : Integrable f) :
    ∫ z : sphere (0 : ℂ) 1 × ℝ, ‖radonTransform f (z.1 : ℂ) z.2‖
        ∂((volume : Measure ℂ).toSphere.prod volume) ≤ 2 * Real.pi * ∫ x, ‖f x‖ := by
  simpa only [toSphere_real_univ] using
    integral_norm_radonTransform_sphere_le (volume : Measure ℂ).toSphere hf

variable (𝕜 : Type*) [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 F] [SMulCommClass ℝ 𝕜 F]

private def radonTransformL1Fun (f : ℂ →₁[volume] F) :
    sphere (0 : ℂ) 1 × ℝ →₁[μ.prod volume] F :=
  (integrable_radonTransform_sphere μ (L1.integrable_coeFn f)).toL1 _

private theorem coe_radonTransformL1Fun (f : ℂ →₁[volume] F) :
    radonTransformL1Fun μ f =ᵐ[μ.prod volume]
      (fun z : sphere (0 : ℂ) 1 × ℝ ↦ radonTransform f (z.1 : ℂ) z.2) :=
  (integrable_radonTransform_sphere μ (L1.integrable_coeFn f)).coeFn_toL1

/-- The joint planar Radon transform as a linear map on L¹ equivalence classes. -/
def radonTransformL1LinearMap :
    (ℂ →₁[volume] F) →ₗ[𝕜] (sphere (0 : ℂ) 1 × ℝ →₁[μ.prod volume] F) where
  toFun := radonTransformL1Fun μ
  map_add' f g := by
    apply Lp.ext
    have hm := (stronglyMeasurable_radonTransform_sphere ((Lp.stronglyMeasurable f).add
        (Lp.stronglyMeasurable g))).measurableSet_eq_fun
        ((stronglyMeasurable_radonTransform_sphere (Lp.stronglyMeasurable f)).add
          (stronglyMeasurable_radonTransform_sphere (Lp.stronglyMeasurable g)))
    have hadd := (Measure.ae_prod_iff_ae_ae (μ := μ) (ν := (volume : Measure ℝ)) hm).mpr
      (Filter.Eventually.of_forall fun ω : sphere (0 : ℂ) 1 ↦
        radonTransform_add_ae (L1.integrable_coeFn f) (L1.integrable_coeFn g)
          (ω := (ω : ℂ)) (by simp))
    have h := (radonTransform_sphere_ae_eq_of_ae_eq μ (Lp.coeFn_add f g)).trans hadd
    filter_upwards [coe_radonTransformL1Fun μ (f + g),
      Lp.coeFn_add (radonTransformL1Fun μ f) (radonTransformL1Fun μ g),
      coe_radonTransformL1Fun μ f, coe_radonTransformL1Fun μ g, h] with z hz hs hzf hzg ha
    calc
      radonTransformL1Fun μ (f + g) z = radonTransform (f + g) (z.1 : ℂ) z.2 := hz
      _ = radonTransform f (z.1 : ℂ) z.2 + radonTransform g (z.1 : ℂ) z.2 := ha
      _ = radonTransformL1Fun μ f z + radonTransformL1Fun μ g z := by rw [hzf, hzg]
      _ = (radonTransformL1Fun μ f + radonTransformL1Fun μ g) z := hs.symm
  map_smul' r f := by
    apply Lp.ext
    have h := radonTransform_sphere_ae_eq_of_ae_eq μ (Lp.coeFn_smul r f)
    filter_upwards [coe_radonTransformL1Fun μ (r • f),
      Lp.coeFn_smul r (radonTransformL1Fun μ f), coe_radonTransformL1Fun μ f, h]
      with z hz hs hf hr
    calc
      radonTransformL1Fun μ (r • f) z = radonTransform (r • f) (z.1 : ℂ) z.2 := hz
      _ = radonTransform (r • (f : ℂ → F)) (z.1 : ℂ) z.2 := hr
      _ = r • radonTransform f (z.1 : ℂ) z.2 := radonTransform_smul r _ _ _
      _ = r • radonTransformL1Fun μ f z := by rw [hf]
      _ = (r • radonTransformL1Fun μ f) z := hs.symm

/-- The joint Radon transform is bounded on L¹, with constant the mass of the direction
measure. -/
theorem norm_radonTransformL1LinearMap_le (f : ℂ →₁[volume] F) :
    ‖radonTransformL1LinearMap μ 𝕜 f‖ ≤ μ.real univ * ‖f‖ := by
  change ‖(integrable_radonTransform_sphere μ (L1.integrable_coeFn f)).toL1 _‖ ≤ _
  rw [Integrable.norm_toL1_eq_lintegral_enorm, ← integral_norm_eq_lintegral_enorm
    (integrable_radonTransform_sphere μ (L1.integrable_coeFn f)).aestronglyMeasurable,
    L1.norm_eq_integral_norm]
  exact integral_norm_radonTransform_sphere_le μ (L1.integrable_coeFn f)

/-- The planar Radon transform on joint L¹ space. Taking `μ = volume.toSphere` gives the
surface-measure convention of the article, and `𝕜 = ℝ` or `𝕜 = ℂ` gives real or complex
linearity. -/
def radonTransformL1 :
    (ℂ →₁[volume] F) →L[𝕜] (sphere (0 : ℂ) 1 × ℝ →₁[μ.prod volume] F) :=
  (radonTransformL1LinearMap μ 𝕜).mkContinuous (μ.real univ)
    (norm_radonTransformL1LinearMap_le μ 𝕜)

/-- The bounded operator represents the hyperplane integral for almost every oriented line. -/
theorem coe_radonTransformL1 (f : ℂ →₁[volume] F) :
    radonTransformL1 μ 𝕜 f =ᵐ[μ.prod volume]
      (fun z : sphere (0 : ℂ) 1 × ℝ ↦ radonTransform f (z.1 : ℂ) z.2) :=
  (integrable_radonTransform_sphere μ (L1.integrable_coeFn f)).coeFn_toL1

/-- Applying the operator to the class of `f` gives the class of its Radon transform. -/
theorem coe_radonTransformL1_toL1 {f : ℂ → F} (hf : Integrable f) :
    radonTransformL1 μ 𝕜 (hf.toL1 f) =ᵐ[μ.prod volume]
      (fun z : sphere (0 : ℂ) 1 × ℝ ↦ radonTransform f (z.1 : ℂ) z.2) :=
  (coe_radonTransformL1 μ 𝕜 (hf.toL1 f)).trans
    (radonTransform_sphere_ae_eq_of_ae_eq μ hf.coeFn_toL1)

/-- Operator-norm estimate for the joint L¹ Radon transform. -/
theorem norm_radonTransformL1_le : ‖radonTransformL1 μ 𝕜 (F := F)‖ ≤ μ.real univ :=
  LinearMap.mkContinuous_norm_le _ ENNReal.toReal_nonneg _

/-- With arc-length measure on directions, the L¹ Radon transform has norm at most `2π`. -/
theorem norm_radonTransformL1_surface_le :
    ‖radonTransformL1 (volume : Measure ℂ).toSphere 𝕜 (F := F)‖ ≤ 2 * Real.pi := by
  simpa only [toSphere_real_univ] using
    norm_radonTransformL1_le (volume : Measure ℂ).toSphere 𝕜 (F := F)

end Complex
