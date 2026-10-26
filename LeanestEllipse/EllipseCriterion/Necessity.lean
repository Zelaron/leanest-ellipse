import LeanestEllipse.Analysis.Convex.Ellipsoid.Complex
import LeanestEllipse.EllipseCriterion.NecessaryMeasure
import LeanestEllipse.EllipseCriterion.HardyModel
import LeanestEllipse.Analysis.InnerProductSpace.SpectralGap
import LeanestEllipse.Analysis.Convex.QuadraticFeasibility
import LeanestEllipse.MeasureTheory.Constructions.SphereMeasure

/-!
# The necessary ellipse ([Hägg, Proposition 11])

Let `K₀` be a convex set with nonempty interior and `K₁` a compact convex set in a Euclidean
plane `E`.  If a nonzero `v ∈ L¹(E)` with essential support in `K₁` has Radon transform vanishing
for almost every line meeting `K₀`, then there is an ellipse `𝓔` with `closure K₀ ⊆ 𝓔 ⊆ K₁`
(`LeanestEllipse.exists_ellipsoid_of_radonVanishesAEOn`).

The proof follows [Hägg, Section 5] in the model `E = ℂ`:

1. the annihilating measure on the band set `X(K₀, K₁)`
   (`LeanestEllipse.exists_bandMeasure_of_radonVanishesAEOn`, via [Hägg, Lemma 6]);
2. the Hardy-model reduction ([Hägg, Lemma 7]): an operator `A ≠ 0`-space with
   `σ(e^{-iθ} A + e^{iθ} A†) ⊆ [a₁(θ), b₁(θ)] \ (a₀(θ), b₀(θ))`;
3. the spectral-gap theorem ([Hägg, Theorem 10]) for `𝐀 = 2A` together with the ellipse of a
   `2 × 2` matrix ([Hägg, Lemma 9]), which give the center and shape of an ellipse whose
   projection endpoints lie in the bands;
4. the support-function criterion.

Unbounded `K₀` are reduced to the bounded case by small disks, and a general Euclidean plane is
reduced to `ℂ` by a linear isometry.
-/

open MeasureTheory Set Complex Filter Matrix
open scoped Real ComplexConjugate RealInnerProductSpace ComplexStarModule

noncomputable section

namespace LeanestEllipse

/-! ### Scalar and operator identities -/

/-- `ℜ (e^{-iθ} • 2A) = e^{-iθ} A + e^{iθ} A†`. -/
theorem realPart_exp_neg_smul_two_smul {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (A : H →L[ℂ] H) (θ : ℝ) :
    (ℜ (exp (-(θ * I)) • ((2 : ℂ) • A)) : H →L[ℂ] H) =
      exp (-(θ * I)) • A + exp (θ * I) • ContinuousLinearMap.adjoint A := by
  have h1 : star (exp (-(θ * I))) = exp (θ * I) := by
    rw [Complex.star_def, ← Complex.exp_conj, map_neg, map_mul, Complex.conj_ofReal,
      Complex.conj_I, mul_neg, neg_neg]
  have h2 : star (2 : ℂ) = 2 := by simp
  rw [realPart_apply_coe, star_smul, star_smul, h1, h2, ← ContinuousLinearMap.star_eq_adjoint,
    ← Complex.coe_smul]
  simp only [smul_add, smul_smul]
  congr 2 <;> push_cast <;> ring

/-- `Re (e^{-iθ} z) = ⟪z, e^{iθ}⟫`. -/
theorem re_exp_neg_mul (θ : ℝ) (z : ℂ) : (exp (-(θ * I)) * z).re = ⟪z, exp (θ * I)⟫ := by
  rw [Complex.inner, ← neg_mul, ← ofReal_neg]
  simp only [mul_re, exp_ofReal_mul_I_re, exp_ofReal_mul_I_im, conj_re, conj_im, Real.cos_neg,
    Real.sin_neg]
  ring

/-- Every unit complex number is `e^{iθ}` for some real `θ`. -/
theorem exists_exp_eq_of_norm_eq_one {ω : ℂ} (hω : ‖ω‖ = 1) : ∃ θ : ℝ, exp (θ * I) = ω :=
  ⟨arg ω, by simpa [hω] using norm_mul_exp_arg_mul_I ω⟩

/-! ### Proposition 11 in the model plane `ℂ` -/

/-- **The necessary ellipse**, for bounded open `K₀` in the model plane `ℂ`
([Hägg, proof of Proposition 11]). -/
theorem exists_ellipsoid_of_radonVanishesAEOn_of_isOpen {K₀ K₁ : Set ℂ} (hK₀o : IsOpen K₀)
    (hK₀c : Convex ℝ K₀) (hK₀ne : K₀.Nonempty) (hK₀b : Bornology.IsBounded K₀)
    (hK₁ : IsCompact K₁) (hK₁c : Convex ℝ K₁) {v : ℂ → ℂ} (hv : Integrable v)
    (hv0 : ¬ v =ᵐ[volume] 0) (hsupp : essSupport v volume ⊆ K₁)
    (hvan : RadonVanishesAEOn v K₀) :
    ∃ e : Ellipsoid ℂ, closure K₀ ⊆ e ∧ (e : Set ℂ) ⊆ K₁ := by
  have hK₁ne : K₁.Nonempty := (essSupport_nonempty_iff.mpr hv0).mono hsupp
  -- the annihilating measure on the band set (Lemma 6)
  obtain ⟨η, hη0, hηmom⟩ :=
    exists_bandMeasure_of_radonVanishesAEOn hK₀c hK₀ne hK₀b hK₁ hv hv0 hsupp hvan
  -- the Hardy model (Lemma 7)
  obtain ⟨𝓔, _, _, _, _, A, hA⟩ := hardy_model_reduction
    (isCompact_bandSet hK₀b hK₁.isBounded) (bandSet_subset_mobius K₀ K₁) η hη0 hηmom
  set a₀ : ℝ → ℝ := fun θ ↦ lowerSupportFunction K₀ (exp (θ * I))
  set b₀ : ℝ → ℝ := fun θ ↦ supportFunction K₀ (exp (θ * I))
  set a₁ : ℝ → ℝ := fun θ ↦ lowerSupportFunction K₁ (exp (θ * I))
  set b₁ : ℝ → ℝ := fun θ ↦ supportFunction K₁ (exp (θ * I))
  have hband : ∀ θ : ℝ, spectrum ℝ (ℜ (exp (-(θ * I)) • ((2 : ℂ) • A)) : 𝓔 →L[ℂ] 𝓔) ⊆
      Icc (a₁ θ) (b₁ θ) \ Ioo (a₀ θ) (b₀ θ) := by
    intro θ p hp
    rw [realPart_exp_neg_smul_two_smul] at hp
    exact (unorientedLineCoords_mem_bandSet_iff (θ, p)).mp (hA θ hp)
  -- a point of `K₀` lies strictly inside all the bands
  obtain ⟨z, hz⟩ := hK₀ne
  have hz' : ∀ θ : ℝ, (exp (-(θ * I)) * z).re ∈ Ioo (a₀ θ) (b₀ θ) := fun θ ↦ by
    rw [re_exp_neg_mul]
    exact hK₀o.mem_Ioo_of_exists_inner_eq hK₀b (exp_ne_zero _) ⟨z, hz, rfl⟩
  -- the spectral-gap theorem (Theorem 10) and the matrix ellipse (Lemma 9)
  obtain ⟨c, Q, hQ, hcQ⟩ :=
    exists_center_shape_of_spectrum_gap ((2 : ℂ) • A) a₁ a₀ b₀ b₁ hband z hz'
  obtain ⟨e, he⟩ := exists_ellipsoid_of_posDef c hQ
  -- the support-function criterion
  refine ⟨e, ?_, ?_⟩
  · rw [e.isClosed.closure_subset_iff]
    refine subset_of_forall_supportFunction_le hK₀b e.nonempty e.convex e.isClosed
      (supportFunction_le_of_forall_norm_eq_one fun ω hω ↦ ?_)
    obtain ⟨θ, rfl⟩ := exists_exp_eq_of_norm_eq_one hω
    rw [he θ]
    exact (hcQ θ).2.2.1
  · refine subset_of_forall_supportFunction_le e.isBounded hK₁ne hK₁c hK₁.isClosed
      (supportFunction_le_of_forall_norm_eq_one fun ω hω ↦ ?_)
    obtain ⟨θ, rfl⟩ := exists_exp_eq_of_norm_eq_one hω
    rw [he θ]
    exact (hcQ θ).2.2.2

/-- **The necessary ellipse** ([Hägg, Proposition 11]) in the model plane `ℂ`. -/
theorem exists_ellipsoid_of_radonVanishesAEOn_complex {K₀ K₁ : Set ℂ} (hK₀c : Convex ℝ K₀)
    (hK₀i : (interior K₀).Nonempty) (hK₁ : IsCompact K₁) (hK₁c : Convex ℝ K₁) {v : ℂ → ℂ}
    (hv : Integrable v) (hv0 : ¬ v =ᵐ[volume] 0) (hsupp : essSupport v volume ⊆ K₁)
    (hvan : RadonVanishesAEOn v K₀) :
    ∃ e : Ellipsoid ℂ, closure K₀ ⊆ e ∧ (e : Set ℂ) ⊆ K₁ := by
  -- small disks in the interior of `K₀` lie in `K₁`, so the interior is bounded
  have hint : interior K₀ ⊆ K₁ := by
    intro x hx
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior x hx
    obtain ⟨e, he₀, he₁⟩ := exists_ellipsoid_of_radonVanishesAEOn_of_isOpen Metric.isOpen_ball
      (convex_ball x ε) ⟨x, Metric.mem_ball_self hε⟩ Metric.isBounded_ball hK₁ hK₁c hv hv0 hsupp
      (radonVanishesAEOn_mono hvan (hball.trans interior_subset))
    exact he₁ (he₀ (subset_closure (Metric.mem_ball_self hε)))
  obtain ⟨e, he₀, he₁⟩ := exists_ellipsoid_of_radonVanishesAEOn_of_isOpen isOpen_interior
    hK₀c.interior hK₀i (hK₁.isBounded.subset hint) hK₁ hK₁c hv hv0 hsupp
    (radonVanishesAEOn_mono hvan interior_subset)
  refine ⟨e, ?_, he₁⟩
  rwa [← hK₀c.closure_interior_eq_closure_of_nonempty_interior hK₀i]

/-! ### Transfer to a general Euclidean plane -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- A linear isometry from the model plane `ℂ` onto a Euclidean plane `E`. -/
def complexIsometry (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 2)] : ℂ ≃ₗᵢ[ℝ] E :=
  Complex.isometryOfOrthonormal
    ((stdOrthonormalBasis ℝ E).reindex (finCongr (Fact.out : Module.finrank ℝ E = 2)))

/-- Almost-everywhere vanishing of Radon data is invariant under linear isometries. -/
theorem RadonVanishesAEOn.comp_linearIsometryEquiv {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]
    (L : F ≃ₗᵢ[ℝ] E) {u : E → ℂ} {D₀ : Set E} (h : RadonVanishesAEOn u D₀) :
    RadonVanishesAEOn (u ∘ L) (L ⁻¹' D₀) := by
  have hS : MeasurePreserving L.sphereMap (volume : Measure F).toSphere
      (volume : Measure E).toSphere := ⟨L.continuous_sphereMap.measurable, L.toSphere_map⟩
  have hΦ := hS.prod (MeasurePreserving.id (volume : Measure ℝ))
  filter_upwards [hΦ.quasiMeasurePreserving.ae h] with z hz hmeet
  simp only [Prod.map_fst, Prod.map_snd, id, LinearIsometryEquiv.coe_sphereMap] at hz
  rw [radonTransform_comp_linearIsometryEquiv]
  obtain ⟨x, hx, hxp⟩ := hmeet
  exact hz ⟨L x, hx, by rw [LinearIsometryEquiv.inner_map_map]; exact hxp⟩

/-- **The necessary ellipse** ([Hägg, Proposition 11]).  Let `K₀` be a convex set with nonempty
interior and `K₁` a compact convex set in a Euclidean plane.  If a nonzero `v ∈ L¹` with
essential support in `K₁` has Radon transform vanishing for almost every line meeting `K₀`, then
there is an ellipse `𝓔` with `closure K₀ ⊆ 𝓔 ⊆ K₁`. -/
theorem exists_ellipsoid_of_radonVanishesAEOn [Fact (Module.finrank ℝ E = 2)] {K₀ K₁ : Set E}
    (hK₀c : Convex ℝ K₀) (hK₀i : (interior K₀).Nonempty) (hK₁ : IsCompact K₁)
    (hK₁c : Convex ℝ K₁) {v : E → ℂ} (hv : Integrable v) (hv0 : ¬ v =ᵐ[volume] 0)
    (hsupp : essSupport v volume ⊆ K₁) (hvan : RadonVanishesAEOn v K₀) :
    ∃ e : Ellipsoid E, closure K₀ ⊆ e ∧ (e : Set E) ⊆ K₁ := by
  set L : ℂ ≃ₗᵢ[ℝ] E := complexIsometry E
  have hL : MeasurePreserving L := L.measurePreserving
  have hint : interior (L ⁻¹' K₀) = L ⁻¹' interior K₀ := (L.toHomeomorph.preimage_interior K₀).symm
  have hv0' : ¬ (v ∘ L) =ᵐ[volume] 0 := fun h ↦ hv0 (by
    filter_upwards [L.symm.measurePreserving.quasiMeasurePreserving.ae_eq_comp h] with x hx
    simpa using hx)
  obtain ⟨e, he₀, he₁⟩ := exists_ellipsoid_of_radonVanishesAEOn_complex (K₀ := L ⁻¹' K₀)
    (K₁ := L ⁻¹' K₁) (hK₀c.linear_preimage L.toLinearEquiv.toLinearMap)
    (by
      obtain ⟨x, hx⟩ := hK₀i
      exact ⟨L.symm x, by rw [hint]; simpa using hx⟩)
    (L.toHomeomorph.isCompact_preimage.mpr hK₁) (hK₁c.linear_preimage L.toLinearEquiv.toLinearMap)
    (hL.integrable_comp_of_integrable hv) hv0'
    ((essSupport_comp_subset L.continuous hL.quasiMeasurePreserving).trans (preimage_mono hsupp))
    (hvan.comp_linearIsometryEquiv L)
  refine ⟨e.map L, ?_, ?_⟩
  · rw [Ellipsoid.coe_map]
    intro x hx
    refine ⟨L.symm x, he₀ ?_, L.apply_symm_apply x⟩
    have : L.symm x ∈ L.toHomeomorph ⁻¹' closure K₀ := by simpa using hx
    rwa [L.toHomeomorph.preimage_closure] at this
  · rw [Ellipsoid.coe_map, image_subset_iff]
    exact he₁

end LeanestEllipse
