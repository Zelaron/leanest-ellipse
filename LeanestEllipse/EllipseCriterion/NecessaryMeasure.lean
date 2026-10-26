import LeanestEllipse.EllipseCriterion.UnorientedTransfer
import LeanestEllipse.EllipseCriterion.Moments
import LeanestEllipse.EllipseCriterion.Defs
import LeanestEllipse.IntegralGeometry.Radon.PlaneInjective

/-!
# From Radon data to an annihilating measure ([Hägg, proof of Proposition 11, first part])

Let `K₀ ⊆ ℂ` be a nonempty bounded convex set and `K₁ ⊆ ℂ` compact, and let `v ∈ L¹` be
nonzero with essential support in `K₁`, whose Radon transform vanishes for almost every line
meeting `K₀`.  With a Borel representative `g` of `v` vanishing outside `K₁`, the function
`h(θ, p) = 𝓡 g(e^{iθ}, p)` satisfies all hypotheses of the unoriented-line transfer
([Hägg, Lemma 6]); hence there is a nonzero complex measure on `X(K₀, K₁)` annihilating the
monomials `z^j q^ℓ`, `ℓ ≥ 1` (`LeanestEllipse.exists_bandMeasure_of_radonVanishesAEOn`).
-/

open MeasureTheory Set Complex Filter
open scoped Real ComplexConjugate RealInnerProductSpace

noncomputable section

namespace LeanestEllipse

theorem exp_add_int_mul_two_pi (θ : ℝ) (k : ℤ) :
    exp (((θ + k * (2 * π) : ℝ) : ℂ) * I) = exp (θ * I) := by
  rw [show (((θ + k * (2 * π) : ℝ) : ℂ) * I) = θ * I + k * (2 * π * I) by push_cast; ring,
    exp_add, exp_int_mul_two_pi_mul_I, mul_one]

theorem exp_add_pi_mul_I (θ : ℝ) : exp (((θ + π : ℝ) : ℂ) * I) = -exp (θ * I) := by
  rw [show (((θ + π : ℝ) : ℂ) * I) = θ * I + π * I by push_cast; ring, exp_add, exp_pi_mul_I,
    mul_neg_one]

/-- The Radon transform of `g : ℂ → ℂ` in angle coordinates, `(θ, p) ↦ 𝓡 g(e^{iθ}, p)`. -/
def radonAngle (g : ℂ → ℂ) (w : ℝ × ℝ) : ℂ := radonTransform g (exp (w.1 * I)) w.2

theorem radonAngle_fiber (g : ℂ → ℂ) (θ : ℝ) :
    (fun p ↦ radonAngle g (θ, p)) = radonTransform g (exp (θ * I)) := rfl

/-- **The annihilating measure of the necessity proof** ([Hägg, Proposition 11, via Lemma 6]). -/
theorem exists_bandMeasure_of_radonVanishesAEOn {K₀ K₁ : Set ℂ}
    (hK₀c : Convex ℝ K₀) (hK₀ne : K₀.Nonempty) (hK₀b : Bornology.IsBounded K₀)
    (hK₁ : IsCompact K₁) {v : ℂ → ℂ} (hv : Integrable v) (hv0 : ¬ v =ᵐ[volume] 0)
    (hsupp : essSupport v volume ⊆ K₁) (hvan : RadonVanishesAEOn v K₀) :
    ∃ η : ComplexMeasure (bandSet K₀ K₁), η ≠ 0 ∧ ∀ j ℓ : ℕ, 1 ≤ ℓ →
      ∫ᵛ w, ((w : ℂ × ℂ).2 ^ j * (w : ℂ × ℂ).1 ^ ℓ) ∂[ContinuousLinearMap.mul ℝ ℂ; η] = 0 := by
  -- a Borel representative vanishing outside `K₁`
  obtain ⟨g, hgm, hgv, hg0⟩ := hv.aestronglyMeasurable.exists_eq_zero_outside_essSupport
  have hgK₁ : ∀ x, g x ≠ 0 → x ∈ K₁ := fun x hx ↦ hsupp (by
    by_contra h
    exact hx (hg0 x h))
  have hg : Integrable g := hv.congr hgv.symm
  obtain ⟨R, hR⟩ := hK₁.isBounded.subset_closedBall 0
  have hgR : ∀ x, g x ≠ 0 → ‖x‖ ≤ R := fun x hx ↦ by simpa using hR (hgK₁ x hx)
  set h : ℝ × ℝ → ℂ := radonAngle g with h_def
  have hhm : StronglyMeasurable h := Complex.stronglyMeasurable_radonTransform_angle hgm
  have hω : ∀ θ : ℝ, ‖exp (θ * I)‖ = 1 := fun θ ↦ norm_exp_ofReal_mul_I θ
  -- the data of `g` vanish on almost every line meeting `K₀`, in angle coordinates
  have hvanθ : ∀ᵐ w : ℝ × ℝ, LineMeets K₀ (exp (w.1 * I)) w.2 → h w = 0 := by
    have h1 := Complex.ae_angle_of_ae_sphere
      (P := fun ω p ↦ LineMeets K₀ (ω : ℂ) p → radonTransform v (ω : ℂ) p = 0) hvan
    have h2 := Complex.radonTransform_exp_ae_eq_of_ae_eq hgv
    filter_upwards [h1, h2] with w hw1 hw2 hmeet
    simp only [Complex.coe_expMapSphere] at hw1
    rw [h_def, radonAngle, hw2]
    exact hw1 hmeet
  -- line symmetry
  have hsymm : ∀ᵐ w : ℝ × ℝ, h (w.1 + π, -w.2) = h w := Eventually.of_forall fun w ↦ by
    simp only [h_def, radonAngle, exp_add_pi_mul_I]
    exact radonTransform_neg_neg g _ _
  -- integrability on `[0, 2π) × ℝ`
  have hrestrict : (volume : Measure (ℝ × ℝ)).restrict (Ico 0 (2 * π) ×ˢ univ) =
      ((volume : Measure ℝ).restrict (Ico 0 (2 * π))).prod volume := by
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]
  have hint : IntegrableOn h (Ico 0 (2 * π) ×ˢ univ) := by
    set μ : Measure ℝ := (volume : Measure ℝ).restrict (Ico 0 (2 * π))
    have hmeas : AEStronglyMeasurable h (μ.prod (volume : Measure ℝ)) := hhm.aestronglyMeasurable
    have hnm : StronglyMeasurable fun θ : ℝ ↦ ∫ p : ℝ, ‖h (θ, p)‖ :=
      hhm.norm.integral_prod_right'
    rw [IntegrableOn, hrestrict, integrable_prod_iff hmeas]
    refine ⟨Eventually.of_forall fun θ ↦ ?_, ?_⟩
    · rw [h_def, radonAngle_fiber]
      exact integrable_radonTransform hg (hω θ)
    refine Integrable.of_bound hnm.aestronglyMeasurable (∫ x, ‖g x‖)
      (Eventually.of_forall fun θ ↦ ?_)
    rw [Real.norm_of_nonneg (integral_nonneg fun _ ↦ norm_nonneg _)]
    have := integral_norm_radonTransform_le hg (hω θ)
    rwa [← radonAngle_fiber] at this
  -- `h` is not a.e. zero on `[0, 2π) × ℝ`, by injectivity of the Radon transform
  have hne : ¬ h =ᵐ[volume.restrict (Ico 0 (2 * π) ×ˢ univ)] 0 := by
    intro h0
    rw [hrestrict] at h0
    have h1 : ∀ᵐ θ : ℝ ∂(volume.restrict (Ico 0 (2 * π))),
        radonTransform g (exp (θ * I)) =ᵐ[volume] 0 := by
      filter_upwards [Measure.ae_ae_of_ae_prod h0] with θ hθ
      filter_upwards [hθ] with p hp
      simpa [h_def, radonAngle] using hp
    have h2 : ∀ᵐ θ : ℝ, radonTransform g (exp (θ * I)) =ᵐ[volume] 0 :=
      ae_of_ae_restrict_Ico_of_periodic (fun θ k ↦ by rw [exp_add_int_mul_two_pi]) h1
    exact hv0 (hgv.symm.trans (Complex.ae_eq_zero_of_ae_radonTransform_exp_ae_eq_zero hg h2))
  -- `h` vanishes unless the line lies in the band
  have hsuppθ : ∀ᵐ w : ℝ × ℝ, h w ≠ 0 → InBand K₀ K₁ (exp (w.1 * I)) w.2 := by
    filter_upwards [hvanθ] with w hw hw0
    refine ⟨?_, fun hmem ↦ hw0 (hw (hK₀c.exists_inner_eq_of_mem_Ioo hK₀ne hK₀b hmem))⟩
    by_contra hnot
    apply hw0
    rw [h_def, radonAngle]
    refine radonTransform_eq_zero_of_support_subset (K := K₁) (hω w.1)
      (fun x hx ↦ hgK₁ x hx) fun x hx hxp ↦ hnot ?_
    exact hxp ▸ ⟨lowerSupportFunction_le_inner hK₁.isBounded hx,
      inner_le_supportFunction hK₁.isBounded hx⟩
  -- the moment conditions
  have hmom : ∀ j : ℕ, ∃ c : ℤ → ℂ, (∀ k, c k ≠ 0 → |k| ≤ j ∧ Even ((j : ℤ) + k)) ∧
      ∀ᵐ θ : ℝ, ∫ p : ℝ, (p : ℂ) ^ j * h (θ, p) =
        ∑ k ∈ Finset.Icc (-(j : ℤ)) j, c k * exp (k * θ * I) := by
    intro j
    obtain ⟨c, hc, hcθ⟩ := exists_trigPoly_radon_moment hg hgR j
    exact ⟨c, hc, Eventually.of_forall fun θ ↦ by rw [← hcθ θ]; rfl⟩
  exact unoriented_line_transfer hK₀b hK₁.isBounded hsymm hint hne hsuppθ hmom

end LeanestEllipse
