import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.Normed.Module.Span

/-!
# The Radon transform

Let `E` be a finite dimensional real inner product space.  For a unit vector `ω : E` and
`p : ℝ`, the affine hyperplane `{x | ⟪x, ω⟫ = p}` is `p • ω + (ℝ ∙ ω)ᗮ`, and the *Radon
transform* of `f : E → F` is

`radonTransform f ω p = ∫ y : (ℝ ∙ ω)ᗮ, f (p • ω + y)`,

the integral of `f` over that hyperplane against the Lebesgue measure of the hyperplane
`(ℝ ∙ ω)ᗮ` (a finite dimensional inner product space in its own right).  In the plane this is the
integral over the line `L(ω, p)` with respect to arc length, `𝓡 u(ω, p)` of [Hägg].

The values for non-unit `ω` are not meaningful.  Integrals are Bochner integrals, so the value is
`0` where the restriction of `f` to the hyperplane is not integrable.

## Main results

* `RadonTransform.measurePreserving_smul_add`: the map `(p, y) ↦ p • ω + y` from
  `ℝ × (ℝ ∙ ω)ᗮ` to `E` is measure preserving.
* `integral_radonTransform` (Fubini in line coordinates): `∫ p, 𝓡 f ω p = ∫ x, f x`;
  `integrable_radonTransform`, `radonTransform_congr_ae`.
* `integral_pow_smul_radonTransform` (moment identities, [Hägg, (5.3)]):
  `∫ p, p ^ j • 𝓡 f ω p = ∫ x, ⟪x, ω⟫ ^ j • f x`.
* `integral_exp_smul_radonTransform` (Fourier slice identity):
  `∫ p, e^{-isp} • 𝓡 f ω p = ∫ x, e^{-is⟪x, ω⟫} • f x`.
* `radonTransform_neg_neg`: `𝓡 f (-ω) (-p) = 𝓡 f ω p` (the same hyperplane).
* `radonTransform_comp_add_left`: translation covariance.
* `radonTransform_comp_linearIsometryEquiv`: invariance under linear isometries.
* `radonTransform_eq_zero_of_forall`: vanishing when `f` vanishes on the hyperplane.
-/

open MeasureTheory Set Submodule
open scoped RealInnerProductSpace

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

namespace RadonTransform

variable {ω : E}

/-- Points of `(ℝ ∙ ω)ᗮ` are orthogonal to `ω`. -/
theorem inner_orthogonal_eq_zero (y : (ℝ ∙ ω)ᗮ) : ⟪(y : E), ω⟫ = 0 := by
  have := (mem_orthogonal_singleton_iff_inner_right (𝕜 := ℝ)).mp y.2
  rwa [real_inner_comm] at this

/-- The hyperplane `p • ω + (ℝ ∙ ω)ᗮ` is `{x | ⟪x, ω⟫ = p}` (for a unit vector `ω`). -/
theorem inner_smul_add (hω : ‖ω‖ = 1) (p : ℝ) (y : (ℝ ∙ ω)ᗮ) :
    ⟪p • ω + (y : E), ω⟫ = p := by
  rw [inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq, hω,
    inner_orthogonal_eq_zero]
  ring

theorem sub_inner_smul_mem (hω : ‖ω‖ = 1) (x : E) : x - ⟪x, ω⟫ • ω ∈ (ℝ ∙ ω)ᗮ := by
  rw [mem_orthogonal_singleton_iff_inner_right, inner_sub_right, real_inner_smul_right,
    real_inner_self_eq_norm_sq, hω, real_inner_comm]
  ring

/-- Every point `x` is `⟪x, ω⟫ • ω + y` with `y ∈ (ℝ ∙ ω)ᗮ` (for a unit vector `ω`). -/
theorem eq_inner_smul_add (hω : ‖ω‖ = 1) (x : E) :
    x = ⟪x, ω⟫ • ω + ((⟨x - ⟪x, ω⟫ • ω, sub_inner_smul_mem hω x⟩ : (ℝ ∙ ω)ᗮ) : E) := by
  simp

/-- For a unit vector `ω`, the linear isometry `(p, y) ↦ p • ω + y` from the `L²` product
`ℝ × (ℝ ∙ ω)ᗮ` onto `E`. -/
def lineHyperplaneEquiv (hω : ‖ω‖ = 1) : WithLp 2 (ℝ × (ℝ ∙ ω)ᗮ) ≃ₗᵢ[ℝ] E :=
  (LinearIsometryEquiv.withLpProdCongr 2 (LinearIsometryEquiv.toSpanUnitSingleton ω hω)
    (LinearIsometryEquiv.refl ℝ (ℝ ∙ ω)ᗮ)).trans (ℝ ∙ ω).orthogonalDecomposition.symm

theorem lineHyperplaneEquiv_apply (hω : ‖ω‖ = 1) (z : WithLp 2 (ℝ × (ℝ ∙ ω)ᗮ)) :
    lineHyperplaneEquiv hω z = (WithLp.ofLp z).1 • ω + ((WithLp.ofLp z).2 : E) := by
  simp [lineHyperplaneEquiv]

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- For a unit vector `ω`, `(p, y) ↦ p • ω + y` as a measurable equivalence
`ℝ × (ℝ ∙ ω)ᗮ ≃ᵐ E`. -/
def smulAddEquiv (hω : ‖ω‖ = 1) : ℝ × (ℝ ∙ ω)ᗮ ≃ᵐ E :=
  (MeasurableEquiv.toLp 2 (ℝ × (ℝ ∙ ω)ᗮ)).trans
    (lineHyperplaneEquiv hω).toHomeomorph.toMeasurableEquiv

@[simp] theorem smulAddEquiv_apply (hω : ‖ω‖ = 1) (z : ℝ × (ℝ ∙ ω)ᗮ) :
    smulAddEquiv hω z = z.1 • ω + (z.2 : E) := by
  simp [smulAddEquiv, lineHyperplaneEquiv_apply]

/-- **Line coordinates preserve volume.**  For a unit vector `ω`, the map `(p, y) ↦ p • ω + y`
from `ℝ × (ℝ ∙ ω)ᗮ` (with the product of the Lebesgue measures) to `E` is measure preserving. -/
theorem measurePreserving_smulAddEquiv (hω : ‖ω‖ = 1) :
    MeasurePreserving (smulAddEquiv hω) := by
  have h := ((lineHyperplaneEquiv hω).measurePreserving).comp
    (WithLp.volume_preserving_toLp ℝ (ℝ ∙ ω)ᗮ)
  exact h

theorem measurePreserving_smul_add (hω : ‖ω‖ = 1) :
    MeasurePreserving (fun z : ℝ × (ℝ ∙ ω)ᗮ ↦ z.1 • ω + (z.2 : E)) (volume.prod volume)
      volume := by
  rw [← Measure.volume_eq_prod]
  convert measurePreserving_smulAddEquiv hω using 1
  ext z
  simp

end RadonTransform

open RadonTransform

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The **Radon transform** of `f : E → F`: for a unit vector `ω` and `p : ℝ`,
`radonTransform f ω p = ∫ y : (ℝ ∙ ω)ᗮ, f (p • ω + y)` is the integral of `f` over the
hyperplane `{x | ⟪x, ω⟫ = p}` with respect to its Lebesgue measure.  (Values for non-unit
`ω` carry no meaning.) -/
def radonTransform (f : E → F) (ω : E) (p : ℝ) : F :=
  ∫ y : (ℝ ∙ ω)ᗮ, f (p • ω + y)

section Fubini

variable {f g : E → F} {ω : E}

theorem RadonTransform.measurableEmbedding_smul_add (hω : ‖ω‖ = 1) :
    MeasurableEmbedding (fun z : ℝ × (ℝ ∙ ω)ᗮ ↦ z.1 • ω + (z.2 : E)) := by
  have : (fun z : ℝ × (ℝ ∙ ω)ᗮ ↦ z.1 • ω + (z.2 : E)) = ⇑(smulAddEquiv hω) :=
    funext fun z ↦ (smulAddEquiv_apply hω z).symm
  rw [this]
  exact (smulAddEquiv hω).measurableEmbedding

omit [NormedSpace ℝ F] in
theorem integrable_comp_smul_add (hf : Integrable f) (hω : ‖ω‖ = 1) :
    Integrable (fun z : ℝ × (ℝ ∙ ω)ᗮ ↦ f (z.1 • ω + z.2)) (volume.prod volume) :=
  ((measurePreserving_smul_add hω).integrable_comp_emb
    (RadonTransform.measurableEmbedding_smul_add hω)).mpr hf

omit [NormedSpace ℝ F] in
/-- For integrable `f`, the restriction of `f` to almost every hyperplane orthogonal to a unit
vector is integrable. -/
theorem ae_integrable_radonTransform_fiber (hf : Integrable f) (hω : ‖ω‖ = 1) :
    ∀ᵐ p : ℝ, Integrable (fun y : (ℝ ∙ ω)ᗮ ↦ f (p • ω + y)) :=
  (integrable_comp_smul_add hf hω).prod_right_ae

/-- The Radon transform of an integrable function is integrable in the offset variable. -/
theorem integrable_radonTransform (hf : Integrable f) (hω : ‖ω‖ = 1) :
    Integrable (radonTransform f ω) :=
  (integrable_comp_smul_add hf hω).integral_prod_left

/-- **Fubini in line coordinates**: integrating the Radon transform over all parallel
hyperplanes recovers the integral of `f`. -/
theorem integral_radonTransform [CompleteSpace F] (hf : Integrable f) (hω : ‖ω‖ = 1) :
    ∫ p, radonTransform f ω p = ∫ x, f x := by
  rw [← (measurePreserving_smulAddEquiv hω).integral_comp' f, Measure.volume_eq_prod,
    integral_prod _ (by simpa using integrable_comp_smul_add hf hω)]
  simp [radonTransform]

/-- The `L¹` norm of the Radon transform is at most that of the function. -/
theorem integral_norm_radonTransform_le (hf : Integrable f) (hω : ‖ω‖ = 1) :
    ∫ p, ‖radonTransform f ω p‖ ≤ ∫ x, ‖f x‖ := by
  calc ∫ p, ‖radonTransform f ω p‖ ≤ ∫ p, ∫ y : (ℝ ∙ ω)ᗮ, ‖f (p • ω + y)‖ := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ ↦ norm_nonneg _)
          (integrable_comp_smul_add hf hω).norm.integral_prod_left
          (Filter.Eventually.of_forall fun p ↦ norm_integral_le_integral_norm _)
    _ = ∫ x, ‖f x‖ := by
        rw [← (measurePreserving_smulAddEquiv hω).integral_comp' (fun x ↦ ‖f x‖),
          Measure.volume_eq_prod,
          integral_prod _ (by simpa using (integrable_comp_smul_add hf hω).norm)]
        simp

/-- Changing an integrable function on a null set changes its Radon transform in a given
direction only for almost every offset. -/
theorem radonTransform_congr_ae (hfg : f =ᵐ[volume] g) (hω : ‖ω‖ = 1) :
    radonTransform f ω =ᵐ[volume] radonTransform g ω := by
  have hcomp : (fun z : ℝ × (ℝ ∙ ω)ᗮ ↦ f (z.1 • ω + z.2)) =ᵐ[volume.prod volume]
      (fun z ↦ g (z.1 • ω + z.2)) :=
    (measurePreserving_smul_add hω).quasiMeasurePreserving.ae_eq_comp hfg
  filter_upwards [Measure.ae_ae_eq_curry_of_prod hcomp] with p hp
  exact integral_congr_ae hp

end Fubini

section Algebra

variable {f g : E → F} {ω : E} {p : ℝ}

@[simp] theorem radonTransform_zero : radonTransform (0 : E → F) ω p = 0 := by
  simp [radonTransform]

theorem radonTransform_smul {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 F]
    [SMulCommClass ℝ 𝕜 F] (c : 𝕜) (f : E → F) (ω : E) (p : ℝ) :
    radonTransform (c • f) ω p = c • radonTransform f ω p := by
  simp only [radonTransform, Pi.smul_apply]
  exact integral_smul c _

theorem radonTransform_neg (f : E → F) (ω : E) (p : ℝ) :
    radonTransform (-f) ω p = -radonTransform f ω p := by
  simp only [radonTransform, Pi.neg_apply]
  exact integral_neg _

theorem radonTransform_add
    (hf : Integrable (fun y : (ℝ ∙ ω)ᗮ ↦ f (p • ω + y)))
    (hg : Integrable (fun y : (ℝ ∙ ω)ᗮ ↦ g (p • ω + y))) :
    radonTransform (f + g) ω p = radonTransform f ω p + radonTransform g ω p := by
  simp only [radonTransform, Pi.add_apply]
  exact integral_add hf hg

theorem radonTransform_sub
    (hf : Integrable (fun y : (ℝ ∙ ω)ᗮ ↦ f (p • ω + y)))
    (hg : Integrable (fun y : (ℝ ∙ ω)ᗮ ↦ g (p • ω + y))) :
    radonTransform (f - g) ω p = radonTransform f ω p - radonTransform g ω p := by
  simp only [radonTransform, Pi.sub_apply]
  exact integral_sub hf hg

theorem radonTransform_add_ae (hf : Integrable f) (hg : Integrable g) (hω : ‖ω‖ = 1) :
    radonTransform (f + g) ω =ᵐ[volume] radonTransform f ω + radonTransform g ω := by
  filter_upwards [ae_integrable_radonTransform_fiber hf hω,
    ae_integrable_radonTransform_fiber hg hω] with p hfp hgp
  exact radonTransform_add hfp hgp

theorem radonTransform_sub_ae (hf : Integrable f) (hg : Integrable g) (hω : ‖ω‖ = 1) :
    radonTransform (f - g) ω =ᵐ[volume] radonTransform f ω - radonTransform g ω := by
  filter_upwards [ae_integrable_radonTransform_fiber hf hω,
    ae_integrable_radonTransform_fiber hg hω] with p hfp hgp
  exact radonTransform_sub hfp hgp

/-- The Radon transform vanishes on a hyperplane on which the function vanishes. -/
theorem radonTransform_eq_zero_of_forall (hω : ‖ω‖ = 1)
    (h : ∀ x, ⟪x, ω⟫ = p → f x = 0) : radonTransform f ω p = 0 := by
  rw [radonTransform]
  have : (fun y : (ℝ ∙ ω)ᗮ ↦ f (p • ω + y)) = 0 := funext fun y ↦ h _ (inner_smul_add hω p y)
  rw [this, integral_zero']

/-- The Radon transform vanishes on hyperplanes missing the support of the function. -/
theorem radonTransform_eq_zero_of_support_subset {K : Set E} (hω : ‖ω‖ = 1)
    (hK : Function.support f ⊆ K) (hp : ∀ x ∈ K, ⟪x, ω⟫ ≠ p) : radonTransform f ω p = 0 :=
  radonTransform_eq_zero_of_forall hω fun x hx ↦ by
    by_contra hfx
    exact hp x (hK hfx) hx

/-- Multiplying by a function of `⟪x, ω⟫` multiplies the Radon transform by its value at `p`. -/
theorem radonTransform_smul_comp_inner {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    [NormedSpace 𝕜 F] [SMulCommClass ℝ 𝕜 F] (φ : ℝ → 𝕜) (hω : ‖ω‖ = 1) (f : E → F) (p : ℝ) :
    radonTransform (fun x ↦ φ ⟪x, ω⟫ • f x) ω p = φ p • radonTransform f ω p := by
  simp only [radonTransform, inner_smul_add hω]
  exact integral_smul (φ p) _

end Algebra

section Moments

variable [CompleteSpace F] {f : E → F} {ω : E}

/-- **Moment identity** ([Hägg, (5.3)], the Helgason–Ludwig moments):
`∫ p, p ^ j • 𝓡 f ω p = ∫ x, ⟪x, ω⟫ ^ j • f x`, whenever the right-hand integrand is
integrable. -/
theorem integral_pow_smul_radonTransform (hω : ‖ω‖ = 1) (j : ℕ)
    (hf : Integrable fun x ↦ ⟪x, ω⟫ ^ j • f x) :
    ∫ p, p ^ j • radonTransform f ω p = ∫ x, ⟪x, ω⟫ ^ j • f x := by
  rw [← integral_radonTransform hf hω]
  refine integral_congr_ae (Filter.Eventually.of_forall fun p ↦ ?_)
  exact (radonTransform_smul_comp_inner (fun t : ℝ ↦ t ^ j) hω f p).symm

end Moments

section FourierSlice

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G] [CompleteSpace G]
  {f : E → G} {ω : E}

/-- **Fourier slice identity**: the one-dimensional Fourier transform of `p ↦ 𝓡 f ω p` at
`s` is the Fourier transform of `f` at `s • ω` (with the kernel `e^{-i x·ξ}` of [Hägg]). -/
theorem integral_exp_smul_radonTransform (hf : Integrable f) (hω : ‖ω‖ = 1) (s : ℝ) :
    ∫ p, Complex.exp (-(s * p : ℝ) * Complex.I) • radonTransform f ω p =
      ∫ x, Complex.exp (-(s * ⟪x, ω⟫ : ℝ) * Complex.I) • f x := by
  have hint : Integrable fun x ↦ Complex.exp (-(s * ⟪x, ω⟫ : ℝ) * Complex.I) • f x := by
    have h := hf.bdd_smul (φ := fun x ↦ Complex.exp (-(s * ⟪x, ω⟫ : ℝ) * Complex.I)) 1
      (Continuous.aestronglyMeasurable (by fun_prop))
      (Filter.Eventually.of_forall fun x ↦ by rw [Complex.norm_exp]; simp)
    exact h
  rw [← integral_radonTransform hint hω]
  refine integral_congr_ae (Filter.Eventually.of_forall fun p ↦ ?_)
  exact (radonTransform_smul_comp_inner
    (fun t : ℝ ↦ Complex.exp (-(s * t : ℝ) * Complex.I)) hω f p).symm

end FourierSlice

section Symmetries

variable {f : E → F} {ω : E}

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- `(ℝ ∙ (-ω))ᗮ = (ℝ ∙ ω)ᗮ`. -/
theorem RadonTransform.orthogonal_span_neg (ω : E) : (ℝ ∙ (-ω))ᗮ = (ℝ ∙ ω)ᗮ := by
  rw [← Set.neg_singleton, Submodule.span_neg]

/-- The hyperplanes `(−ω, −p)` and `(ω, p)` coincide, hence so do the Radon transforms. -/
theorem radonTransform_neg_neg (f : E → F) (ω : E) (p : ℝ) :
    radonTransform f (-ω) (-p) = radonTransform f ω p := by
  let e : (ℝ ∙ (-ω))ᗮ ≃ₗᵢ[ℝ] (ℝ ∙ ω)ᗮ :=
    LinearIsometryEquiv.ofEq _ _ (RadonTransform.orthogonal_span_neg ω)
  rw [radonTransform, radonTransform, ← e.measurePreserving.integral_comp'
    (f := e.toHomeomorph.toMeasurableEquiv)]
  simp [e]

/-- **Translation covariance**: `𝓡 (f(· + c)) ω p = 𝓡 f ω (p + ⟪c, ω⟫)`. -/
theorem radonTransform_comp_add_right (hω : ‖ω‖ = 1) (f : E → F) (c : E) (p : ℝ) :
    radonTransform (fun x ↦ f (x + c)) ω p = radonTransform f ω (p + ⟪c, ω⟫) := by
  set c' : (ℝ ∙ ω)ᗮ := ⟨c - ⟪c, ω⟫ • ω, sub_inner_smul_mem hω c⟩
  have hc : ∀ y : (ℝ ∙ ω)ᗮ, p • ω + (y : E) + c = (p + ⟪c, ω⟫) • ω + ((y + c' : (ℝ ∙ ω)ᗮ) : E) := by
    intro y
    simp only [c', Submodule.coe_add, add_smul]
    abel
  simp only [radonTransform, hc]
  exact integral_add_right_eq_self (fun y : (ℝ ∙ ω)ᗮ ↦ f ((p + ⟪c, ω⟫) • ω + (y : E))) c'

/-- **Isometry invariance**: for a linear isometry equivalence `L`,
`𝓡 (f ∘ L) ω p = 𝓡 f (L ω) p`. -/
theorem radonTransform_comp_linearIsometryEquiv {E' : Type*} [NormedAddCommGroup E']
    [InnerProductSpace ℝ E'] [FiniteDimensional ℝ E'] [MeasurableSpace E'] [BorelSpace E']
    (L : E ≃ₗᵢ[ℝ] E') (f : E' → F) (ω : E) (p : ℝ) :
    radonTransform (f ∘ L) ω p = radonTransform f (L ω) p := by
  have hmap : ((ℝ ∙ ω)ᗮ).map (L.toLinearEquiv : E →ₗ[ℝ] E') = (ℝ ∙ L ω)ᗮ := by
    rw [Submodule.map_orthogonal_equiv, Submodule.map_span, Set.image_singleton]
    rfl
  let e : (ℝ ∙ ω)ᗮ ≃ₗᵢ[ℝ] (ℝ ∙ L ω)ᗮ :=
    (L.submoduleMap (ℝ ∙ ω)ᗮ).trans (LinearIsometryEquiv.ofEq _ _ hmap)
  have he : ∀ y : (ℝ ∙ ω)ᗮ, (e y : E') = L y := fun y ↦ rfl
  rw [radonTransform, radonTransform, ← e.measurePreserving.integral_comp'
    (f := e.toHomeomorph.toMeasurableEquiv)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y ↦ ?_)
  simp [he, map_add, map_smul]

/-- A function odd about a point `c` (`f (2 • c - x) = -f x`) has vanishing Radon transform on
every hyperplane through `c` ([Hägg, Section 7]). -/
theorem radonTransform_eq_zero_of_odd_about {f : E → F} {c : E} (hf : ∀ x, f (2 • c - x) = -f x)
    (hω : ‖ω‖ = 1) : radonTransform f ω ⟪c, ω⟫ = 0 := by
  set p := ⟪c, ω⟫
  set c' : (ℝ ∙ ω)ᗮ := ⟨c - p • ω, sub_inner_smul_mem hω c⟩
  have hrefl : ∀ y : (ℝ ∙ ω)ᗮ, p • ω + ((2 • c' - y : (ℝ ∙ ω)ᗮ) : E) = 2 • c - (p • ω + y) := by
    intro y
    simp only [c', Submodule.coe_sub, Submodule.coe_smul_of_tower, smul_sub]
    rw [two_smul, two_smul]
    abel
  have key : radonTransform f ω p = -radonTransform f ω p := by
    calc radonTransform f ω p = ∫ y : (ℝ ∙ ω)ᗮ, f (p • ω + ((2 • c' - y : (ℝ ∙ ω)ᗮ) : E)) :=
          (integral_sub_left_eq_self (fun y : (ℝ ∙ ω)ᗮ ↦ f (p • ω + (y : E))) volume (2 • c')).symm
      _ = ∫ y : (ℝ ∙ ω)ᗮ, -f (p • ω + y) := by simp only [hrefl, hf]
      _ = -radonTransform f ω p := integral_neg _
  have h2 : (2 : ℝ) • radonTransform f ω p = 0 := by
    rw [two_smul]
    nth_rewrite 1 [key]
    exact neg_add_cancel _
  exact (smul_eq_zero.mp h2).resolve_left two_ne_zero

end Symmetries

end
