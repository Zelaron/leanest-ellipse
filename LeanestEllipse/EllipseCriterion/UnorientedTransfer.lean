import LeanestEllipse.MeasureTheory.ComplexMeasure
import LeanestEllipse.Analysis.Convex.SupportFunction
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# The symmetry-free transfer to unoriented-line space ([Hägg, Section 2])

The coordinates `q = e^{2iθ}`, `z = p e^{iθ}` are invariant under `(θ, p) ↦ (θ + π, -p)`, hence
parametrize unoriented lines; their image is the Möbius real line bundle
`Σ = {(q, z) ∈ 𝕋 × ℂ | z = q z̄}`.

## Main results

* `LeanestEllipse.exists_complexMeasure_of_unoriented_moments`: the general form of
  [Hägg, Lemma 6]: a line-symmetric nonzero `h ∈ L¹([0, 2π) × ℝ)` supported (in unoriented-line
  coordinates) in a compact set `X ⊆ ℂ × ℂ`, all of whose offset moments are trigonometric
  polynomials of the Helgason–Ludwig type, yields a nonzero complex measure on `X` annihilating
  all monomials `z^j q^ℓ` with `ℓ ≥ 1`.
-/

open MeasureTheory Set Complex Filter
open scoped Real ComplexConjugate ENNReal RealInnerProductSpace

noncomputable section

namespace LeanestEllipse

/-- The unoriented-line coordinates `Γ(θ, p) = (e^{2iθ}, p e^{iθ})` of [Hägg, Section 2]. -/
def unorientedLineCoords (w : ℝ × ℝ) : ℂ × ℂ :=
  (exp (2 * w.1 * I), w.2 * exp (w.1 * I))

@[simp] theorem unorientedLineCoords_fst (w : ℝ × ℝ) :
    (unorientedLineCoords w).1 = exp (2 * w.1 * I) := rfl

@[simp] theorem unorientedLineCoords_snd (w : ℝ × ℝ) :
    (unorientedLineCoords w).2 = w.2 * exp (w.1 * I) := rfl

theorem continuous_unorientedLineCoords : Continuous unorientedLineCoords := by
  unfold unorientedLineCoords
  fun_prop

/-- `Γ` is invariant under the reversal of orientation `(θ, p) ↦ (θ + π, -p)`. -/
theorem unorientedLineCoords_add_pi_neg (θ p : ℝ) :
    unorientedLineCoords (θ + π, -p) = unorientedLineCoords (θ, p) := by
  simp only [unorientedLineCoords, Prod.mk.injEq]
  constructor
  · rw [show (2 : ℂ) * ((θ + π : ℝ) : ℂ) * I = 2 * θ * I + 2 * π * I by push_cast; ring,
      exp_add, exp_two_pi_mul_I, mul_one]
  · rw [show (((θ + π : ℝ) : ℂ) * I) = θ * I + π * I by push_cast; ring, exp_add, exp_pi_mul_I]
    push_cast
    ring

/-- The half-period `[0, π) × ℝ` of the parameter space of oriented lines. -/
def halfPeriod : Set (ℝ × ℝ) := Ico 0 π ×ˢ univ

theorem measurableSet_halfPeriod : MeasurableSet halfPeriod :=
  measurableSet_Ico.prod MeasurableSet.univ

/-- `Γ` is injective on the half-period `[0, π) × ℝ`. -/
theorem injOn_unorientedLineCoords : InjOn unorientedLineCoords halfPeriod := by
  rintro ⟨θ, p⟩ ⟨⟨hθ0, hθπ⟩, -⟩ ⟨θ', p'⟩ ⟨⟨hθ0', hθπ'⟩, -⟩ h
  simp only [unorientedLineCoords, Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  -- from `e^{2iθ} = e^{2iθ'}` and `0 ≤ θ, θ' < π` we get `θ = θ'`
  have hθ : θ = θ' := by
    rw [Complex.exp_eq_exp_iff_exists_int] at h1
    obtain ⟨n, hn⟩ := h1
    have hn' : (2 * θ : ℝ) = 2 * θ' + n * (2 * π) := by
      have := congrArg Complex.im hn
      simp at this
      linarith
    have hlt : |(n : ℝ)| < 1 := by
      rw [abs_lt]
      constructor <;> nlinarith [Real.pi_pos]
    have hn0 : n = 0 := by
      rw [abs_lt] at hlt
      have h₁ : (-1 : ℤ) < n := by exact_mod_cast hlt.1
      have h₂ : n < 1 := by exact_mod_cast hlt.2
      omega
    subst hn0
    simpa using hn'
  subst hθ
  refine Prod.ext rfl ?_
  have hne : exp (θ * I) ≠ 0 := exp_ne_zero _
  have := mul_right_cancel₀ hne h2
  exact_mod_cast this

/-- `Γ` restricted to the half-period `[0, π) × ℝ`. -/
def unorientedLineCoordsHalf (w : halfPeriod) : ℂ × ℂ := unorientedLineCoords w

/-- `Γ` is a Borel isomorphism from `[0, π) × ℝ` onto its image (Lusin–Souslin). -/
theorem measurableEmbedding_unorientedLineCoordsHalf :
    MeasurableEmbedding unorientedLineCoordsHalf :=
  continuous_unorientedLineCoords.continuousOn.measurableEmbedding measurableSet_halfPeriod
    injOn_unorientedLineCoords

/-- `∫_0^π e^{i m θ} dθ = 0` for even `m ≠ 0`. -/
theorem integral_Ico_zero_pi_exp_eq_zero {m : ℤ} (hm : m ≠ 0) (heven : Even m) :
    ∫ θ in Ico 0 π, exp (m * θ * I) = 0 := by
  obtain ⟨n, rfl⟩ := heven
  have hc : ((n + n : ℤ) : ℂ) * I ≠ 0 :=
    mul_ne_zero (by exact_mod_cast hm) I_ne_zero
  rw [integral_Ico_eq_integral_Ioo, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le Real.pi_pos.le]
  have : ∀ θ : ℝ, exp (((n + n : ℤ) : ℂ) * θ * I) = exp ((((n + n : ℤ) : ℂ) * I) * θ) :=
    fun θ ↦ by ring_nf
  simp_rw [this]
  rw [integral_exp_mul_complex hc]
  have h1 : exp ((((n + n : ℤ) : ℂ) * I) * π) = 1 := by
    rw [show (((n + n : ℤ) : ℂ) * I) * π = n * (2 * π * I) by push_cast; ring,
      exp_int_mul_two_pi_mul_I]
  rw [h1, Complex.ofReal_zero, mul_zero, exp_zero, sub_self, zero_div]

/-- The offset moments of a density supported (in unoriented-line coordinates) in a compact set
are bounded by the corresponding moments of `|h|`. -/
theorem exists_abs_snd_le_of_isCompact {X : Set (ℂ × ℂ)} (hX : IsCompact X) :
    ∃ R : ℝ, ∀ w : ℝ × ℝ, unorientedLineCoords w ∈ X → |w.2| ≤ R := by
  obtain ⟨R, hR⟩ := (hX.image continuous_snd).isBounded.subset_closedBall 0
  refine ⟨R, fun w hw ↦ ?_⟩
  have := hR ⟨_, hw, rfl⟩
  rw [Metric.mem_closedBall, dist_zero_right, unorientedLineCoords_snd, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, norm_exp_ofReal_mul_I, mul_one] at this
  exact this

/-- **Unoriented-line transfer** (general form of [Hägg, Lemma 6]).  Let `X ⊆ ℂ × ℂ` be
compact and let `h : ℝ × ℝ → ℂ` be line-symmetric (`h (θ + π, -p) = h (θ, p)` a.e.),
integrable and not a.e. zero on `[0, 2π) × ℝ`, vanishing a.e. unless `Γ(θ, p) ∈ X`, and such
that each offset moment `θ ↦ ∫ p^j h(θ, p) dp` agrees a.e. with a trigonometric polynomial with
frequencies `k`, `|k| ≤ j`, `k ≡ j mod 2`.  Then there is a nonzero complex measure `η` on `X`
with `∫ z^j q^ℓ dη = 0` for all `j ≥ 0`, `ℓ ≥ 1`. -/
theorem exists_complexMeasure_of_unoriented_moments {X : Set (ℂ × ℂ)} (hX : IsCompact X)
    {h : ℝ × ℝ → ℂ} (hsymm : ∀ᵐ w : ℝ × ℝ, h (w.1 + π, -w.2) = h w)
    (hint : IntegrableOn h (Ico 0 (2 * π) ×ˢ univ))
    (hne : ¬ h =ᵐ[volume.restrict (Ico 0 (2 * π) ×ˢ univ)] 0)
    (hsupp : ∀ᵐ w : ℝ × ℝ, h w ≠ 0 → unorientedLineCoords w ∈ X)
    (hmom : ∀ j : ℕ, ∃ c : ℤ → ℂ, (∀ k, c k ≠ 0 → |k| ≤ j ∧ Even ((j : ℤ) + k)) ∧
      ∀ᵐ θ : ℝ, ∫ p : ℝ, (p : ℂ) ^ j * h (θ, p) =
        ∑ k ∈ Finset.Icc (-(j : ℤ)) j, c k * exp (k * θ * I)) :
    ∃ η : ComplexMeasure X, η ≠ 0 ∧ ∀ j ℓ : ℕ, 1 ≤ ℓ →
      ∫ᵛ w, ((w : ℂ × ℂ).2 ^ j * (w : ℂ × ℂ).1 ^ ℓ) ∂[ContinuousLinearMap.mul ℝ ℂ; η] = 0 := by
  have hXm : MeasurableSet X := hX.isClosed.measurableSet
  have hS := measurableSet_halfPeriod
  set μS : Measure halfPeriod := (volume : Measure (ℝ × ℝ)).comap Subtype.val
  set hS' : halfPeriod → ℂ := fun x ↦ h x
  have hsub : halfPeriod ⊆ Ico 0 (2 * π) ×ˢ univ := by
    rintro ⟨θ, p⟩ ⟨⟨h0, hπ⟩, -⟩
    exact ⟨⟨h0, by linarith [Real.pi_pos]⟩, mem_univ _⟩
  have hintS : Integrable hS' μS :=
    (integrableOn_iff_comap_subtypeVal hS).mp (hint.mono_set hsub)
  -- a.e. statements transfer from `ℝ × ℝ` to the subtype
  have hae : ∀ {P : ℝ × ℝ → Prop}, (∀ᵐ w : ℝ × ℝ, P w) →
      ∀ᵐ x : halfPeriod ∂μS, P (x : ℝ × ℝ) := by
    intro P hP
    have hmap : (μS.map (Subtype.val : halfPeriod → ℝ × ℝ)) = volume.restrict halfPeriod :=
      map_comap_subtype_coe hS _
    have : ∀ᵐ y ∂(μS.map (Subtype.val : halfPeriod → ℝ × ℝ)), P y := by
      rw [hmap]; exact ae_restrict_of_ae hP
    exact ae_of_ae_map (measurable_subtype_coe.aemeasurable) this
  set Γh := unorientedLineCoordsHalf
  have hΓ : MeasurableEmbedding Γh := measurableEmbedding_unorientedLineCoordsHalf
  set η₀ : ComplexMeasure halfPeriod := μS.withDensityᵥ hS'
  set η₁ : VectorMeasure (ℂ × ℂ) ℂ := η₀.map Γh
  -- `η₁` is concentrated on `X`
  have hvar : η₁.variation (range (Subtype.val : X → ℂ × ℂ))ᶜ = 0 := by
    rw [Subtype.range_coe, hΓ.variation_map, Measure.variation_withDensityᵥ hintS,
      Measure.map_apply hΓ.measurable hXm.compl, withDensity_apply _ (hΓ.measurable hXm.compl)]
    have h0 : ∀ᵐ x ∂μS, x ∈ Γh ⁻¹' Xᶜ → ‖hS' x‖ₑ = (0 : ℝ≥0∞) := by
      filter_upwards [hae hsupp] with x hx hxX
      have : h x = 0 := by
        by_contra hne'
        exact hxX (hx hne')
      simp [hS', this]
    rw [setLIntegral_congr_fun_ae (hΓ.measurable hXm.compl) h0]
    simp
  set η : ComplexMeasure X := η₁.comap (Subtype.val : X → ℂ × ℂ)
  have hXemb : MeasurableEmbedding (Subtype.val : X → ℂ × ℂ) := MeasurableEmbedding.subtype_coe hXm
  refine ⟨η, ?_, ?_⟩
  · -- `η ≠ 0`
    intro hη0
    have h1 : η₁ = 0 :=
      (VectorMeasure.comap_eq_zero_iff_of_variation_compl_range_eq_zero hXemb hvar).mp hη0
    have h2 : η₀ = 0 := hΓ.vectorMeasure_map_eq_zero_iff.mp h1
    have h3 : hS' =ᵐ[μS] 0 := (Measure.withDensityᵥ_eq_zero_iff hintS).mp h2
    have h4 : ∀ᵐ w : ℝ × ℝ, w ∈ halfPeriod → h w = 0 := by
      have : ∀ᵐ w ∂(volume.restrict halfPeriod), h w = 0 := by
        rw [← map_comap_subtype_coe hS, (MeasurableEmbedding.subtype_coe hS).ae_map_iff]
        exact h3
      exact (ae_restrict_iff' hS).mp this
    have hτ : MeasurePreserving (fun w : ℝ × ℝ ↦ (w.1 - π, -w.2)) := by
      have := (measurePreserving_sub_right (volume : Measure ℝ) π).prod
        (Measure.measurePreserving_neg (volume : Measure ℝ))
      rw [← Measure.volume_eq_prod] at this
      exact this
    have h5 : ∀ᵐ w : ℝ × ℝ, (w.1 - π, -w.2) ∈ halfPeriod → h w = 0 := by
      filter_upwards [hτ.quasiMeasurePreserving.ae h4, hτ.quasiMeasurePreserving.ae hsymm]
        with w hw1 hw2 hw
      have hw' : ((w.1 - π) + π, -(-w.2)) = w := by ext <;> simp
      rw [hw'] at hw2
      rw [hw2]
      exact hw1 hw
    apply hne
    rw [EventuallyEq, ae_restrict_iff' (measurableSet_Ico.prod MeasurableSet.univ)]
    filter_upwards [h4, h5] with w hw4 hw5 hw
    obtain ⟨⟨h0, h2π⟩, -⟩ := hw
    rcases lt_or_ge w.1 π with hlt | hge
    · exact hw4 ⟨⟨h0, hlt⟩, mem_univ _⟩
    · exact hw5 ⟨⟨by linarith, by linarith⟩, mem_univ _⟩
  · -- the moments vanish
    intro j ℓ hℓ
    obtain ⟨c, hc, hcθ⟩ := hmom j
    obtain ⟨R, hR⟩ := exists_abs_snd_le_of_isCompact hX
    set G : ℂ × ℂ → ℂ := fun y ↦ y.2 ^ j * y.1 ^ ℓ with hG
    have hGΓ : ∀ w : ℝ × ℝ, G (unorientedLineCoords w) =
        (w.2 : ℂ) ^ j * exp (((j : ℂ) + 2 * ℓ) * w.1 * I) := by
      intro w
      simp only [G, unorientedLineCoords]
      rw [mul_pow, ← exp_nat_mul, ← exp_nat_mul, mul_assoc, ← exp_add]
      congr 2
      ring
    have hGcont : Continuous fun w : ℝ × ℝ ↦ G (unorientedLineCoords w) :=
      (by fun_prop : Continuous G).comp continuous_unorientedLineCoords
    have hbound : ∀ᵐ w : ℝ × ℝ, ‖G (unorientedLineCoords w) * h w‖ ≤ R ^ j * ‖h w‖ := by
      filter_upwards [hsupp] with w hw
      by_cases h0 : h w = 0
      · simp [h0]
      · have hRw := hR w (hw h0)
        rw [norm_mul, hGΓ, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
          show ((j : ℂ) + 2 * ℓ) * w.1 * I = ((j + 2 * ℓ : ℝ) * w.1 : ℝ) * I by push_cast; ring,
          norm_exp_ofReal_mul_I, mul_one]
        gcongr
    have hintG : IntegrableOn (fun w ↦ G (unorientedLineCoords w) * h w) halfPeriod := by
      refine Integrable.mono' ((hint.mono_set hsub).norm.const_mul (R ^ j)) ?_
        (ae_restrict_of_ae hbound)
      exact hGcont.aestronglyMeasurable.mul (hint.mono_set hsub).aestronglyMeasurable
    have hintG' : Integrable (fun x : halfPeriod ↦ G (Γh x) * hS' x) μS :=
      (integrableOn_iff_comap_subtypeVal hS).mp hintG
    have hterm : ∀ k : ℤ, IntegrableOn
        (fun θ : ℝ ↦ c k * exp (((j + 2 * ℓ + k : ℤ) : ℂ) * θ * I)) (Ico 0 π) := by
      intro k
      exact (by fun_prop : Continuous fun θ : ℝ ↦
        c k * exp (((j + 2 * ℓ + k : ℤ) : ℂ) * θ * I)).integrableOn_Icc.mono_set Ico_subset_Icc_self
    calc ∫ᵛ w, ((w : ℂ × ℂ).2 ^ j * (w : ℂ × ℂ).1 ^ ℓ) ∂[ContinuousLinearMap.mul ℝ ℂ; η]
        = ∫ᵛ y, G y ∂[ContinuousLinearMap.mul ℝ ℂ; η₁] :=
          VectorMeasure.integral_comap hXemb hvar _ G
      _ = ∫ᵛ x, G (Γh x) ∂[ContinuousLinearMap.mul ℝ ℂ; η₀] := hΓ.integral_map_vectorMeasure
      _ = ∫ x, G (Γh x) * hS' x ∂μS :=
          ComplexMeasure.integral_withDensityᵥ_of_integrable_mul hintS
            (hGcont.comp continuous_subtype_val).aestronglyMeasurable hintG'
      _ = ∫ w in halfPeriod, G (unorientedLineCoords w) * h w :=
          integral_subtype_comap hS (fun w ↦ G (unorientedLineCoords w) * h w)
      _ = ∫ θ in Ico 0 π, ∫ p, G (unorientedLineCoords (θ, p)) * h (θ, p) := by
          rw [halfPeriod, Measure.volume_eq_prod, setIntegral_prod _ (by
            rw [← Measure.volume_eq_prod]; exact hintG)]
          simp only [Measure.restrict_univ]
      _ = ∫ θ in Ico 0 π, exp (((j : ℂ) + 2 * ℓ) * θ * I) * ∫ p : ℝ, (p : ℂ) ^ j * h (θ, p) := by
          refine setIntegral_congr_fun measurableSet_Ico fun θ _ ↦ ?_
          rw [← integral_const_mul]
          refine integral_congr_ae (Eventually.of_forall fun p ↦ ?_)
          simp only [hGΓ]
          ring
      _ = ∫ θ in Ico 0 π, ∑ k ∈ Finset.Icc (-(j : ℤ)) j,
            c k * exp (((j + 2 * ℓ + k : ℤ) : ℂ) * θ * I) := by
          refine setIntegral_congr_ae measurableSet_Ico ?_
          filter_upwards [hcθ] with θ hθ _
          rw [hθ, Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ ↦ ?_
          rw [mul_left_comm, ← exp_add]
          congr 2
          push_cast
          ring
      _ = ∑ k ∈ Finset.Icc (-(j : ℤ)) j,
            c k * ∫ θ in Ico 0 π, exp (((j + 2 * ℓ + k : ℤ) : ℂ) * θ * I) := by
          rw [integral_finsetSum _ fun k _ ↦ hterm k]
          refine Finset.sum_congr rfl fun k _ ↦ ?_
          rw [integral_const_mul]
      _ = 0 := by
          refine Finset.sum_eq_zero fun k _ ↦ ?_
          by_cases hk : c k = 0
          · simp [hk]
          · obtain ⟨hk1, hk2⟩ := hc k hk
            rw [integral_Ico_zero_pi_exp_eq_zero, mul_zero]
            · have := abs_le.mp hk1
              omega
            · obtain ⟨r, hr⟩ := hk2
              exact ⟨r + ℓ, by omega⟩

/-! ### The band set `X(K₀, K₁)` -/

/-- The condition `p ∈ [a_{K₁}(ω), b_{K₁}(ω)] \ (a_{K₀}(ω), b_{K₀}(ω))` on an oriented line
`(ω, p)`: the line misses `K₀` (if `K₀` is open convex) but not the closed convex hull of `K₁`. -/
def InBand (K₀ K₁ : Set ℂ) (ω : ℂ) (p : ℝ) : Prop :=
  p ∈ Icc (lowerSupportFunction K₁ ω) (supportFunction K₁ ω) \
    Ioo (lowerSupportFunction K₀ ω) (supportFunction K₀ ω)

theorem inBand_neg_neg {K₀ K₁ : Set ℂ} {ω : ℂ} {p : ℝ} :
    InBand K₀ K₁ (-ω) (-p) ↔ InBand K₀ K₁ ω p := by
  simp only [InBand, lowerSupportFunction_neg, supportFunction_neg, Set.mem_sdiff, mem_Icc, mem_Ioo]
  constructor <;> rintro ⟨⟨h1, h2⟩, h3⟩ <;> refine ⟨⟨by linarith, by linarith⟩, ?_⟩ <;>
    rintro ⟨h4, h5⟩ <;> exact h3 ⟨by linarith, by linarith⟩

/-- The band `X(K₀, K₁) = {(ω², p ω) | ω ∈ 𝕊¹, p ∈ [a_{K₁}(ω), b_{K₁}(ω)] \ (a_{K₀}(ω), b_{K₀}(ω))}`
in unoriented-line coordinates [Hägg, Section 2]. -/
def bandSet (K₀ K₁ : Set ℂ) : Set (ℂ × ℂ) :=
  unorientedLineCoords '' {w : ℝ × ℝ | InBand K₀ K₁ (exp (w.1 * I)) w.2}

theorem unorientedLineCoords_eq_sq (w : ℝ × ℝ) :
    unorientedLineCoords w = (exp (w.1 * I) ^ 2, w.2 * exp (w.1 * I)) := by
  simp only [unorientedLineCoords, Prod.mk.injEq, and_true]
  rw [← exp_nat_mul]
  congr 1
  push_cast
  ring

/-- **Fibers of the band**: `(e^{2iθ}, p e^{iθ}) ∈ X(K₀, K₁)` iff
`p ∈ [a_{K₁}(e^{iθ}), b_{K₁}(e^{iθ})] \ (a_{K₀}(e^{iθ}), b_{K₀}(e^{iθ}))`. -/
theorem unorientedLineCoords_mem_bandSet_iff {K₀ K₁ : Set ℂ} (w : ℝ × ℝ) :
    unorientedLineCoords w ∈ bandSet K₀ K₁ ↔ InBand K₀ K₁ (exp (w.1 * I)) w.2 := by
  refine ⟨?_, fun h ↦ ⟨w, h, rfl⟩⟩
  rintro ⟨w', hw', he⟩
  rw [unorientedLineCoords_eq_sq, unorientedLineCoords_eq_sq, Prod.mk.injEq] at he
  obtain ⟨h1, h2⟩ := he
  have hne : exp (w.1 * I) ≠ 0 := exp_ne_zero _
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp h1 with h | h
  · rw [h] at h2
    have : (w'.2 : ℂ) = w.2 := mul_right_cancel₀ hne h2
    have hp : w'.2 = w.2 := by exact_mod_cast this
    simpa only [mem_ofPred_eq, h, hp] using hw'
  · rw [h] at h2
    have : (-(w'.2 : ℝ) : ℂ) = w.2 := by
      have := mul_right_cancel₀ hne
        (by rw [← h2]; ring : (-(w'.2 : ℂ)) * exp (w.1 * I) = w.2 * exp (w.1 * I))
      exact this
    have hp : -w'.2 = w.2 := by exact_mod_cast this
    have hw'' : InBand K₀ K₁ (-exp (w.1 * I)) w'.2 := by simpa only [mem_ofPred_eq, h] using hw'
    rw [← neg_neg w'.2, inBand_neg_neg, hp] at hw''
    · simpa using hw''

/-- The band lies in the Möbius real line bundle `Σ = {(q, z) | ‖q‖ = 1, z = q z̄}`. -/
theorem bandSet_subset_mobius (K₀ K₁ : Set ℂ) :
    bandSet K₀ K₁ ⊆ {w : ℂ × ℂ | ‖w.1‖ = 1 ∧ w.2 = w.1 * conj w.2} := by
  rintro _ ⟨w, -, rfl⟩
  constructor
  · simp only [unorientedLineCoords_fst]
    rw [show (2 : ℂ) * w.1 * I = ((2 * w.1 : ℝ) : ℂ) * I by push_cast; ring]
    exact norm_exp_ofReal_mul_I _
  · simp only [unorientedLineCoords_fst, unorientedLineCoords_snd, map_mul, Complex.conj_ofReal]
    rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I, mul_left_comm,
      ← exp_add]
    congr 2
    ring

theorem continuous_lowerSupportFunction_exp {K : Set ℂ} (hK : Bornology.IsBounded K) :
    Continuous fun θ : ℝ ↦ lowerSupportFunction K (exp (θ * I)) :=
  (continuous_lowerSupportFunction hK).comp (by fun_prop)

theorem continuous_supportFunction_exp {K : Set ℂ} (hK : Bornology.IsBounded K) :
    Continuous fun θ : ℝ ↦ supportFunction K (exp (θ * I)) :=
  (continuous_supportFunction hK).comp (by fun_prop)

theorem isClosed_setOf_inBand {K₀ K₁ : Set ℂ} (hK₀ : Bornology.IsBounded K₀)
    (hK₁ : Bornology.IsBounded K₁) :
    IsClosed {w : ℝ × ℝ | InBand K₀ K₁ (exp (w.1 * I)) w.2} := by
  have heq : {w : ℝ × ℝ | InBand K₀ K₁ (exp (w.1 * I)) w.2} =
      ({w | lowerSupportFunction K₁ (exp (w.1 * I)) ≤ w.2} ∩
        {w | w.2 ≤ supportFunction K₁ (exp (w.1 * I))}) ∩
      ({w | w.2 ≤ lowerSupportFunction K₀ (exp (w.1 * I))} ∪
        {w | supportFunction K₀ (exp (w.1 * I)) ≤ w.2}) := by
    ext w
    simp only [InBand, Set.mem_sdiff, mem_Icc, mem_Ioo, mem_inter_iff, mem_union, mem_ofPred_eq,
      not_and_or, not_lt]
  rw [heq]
  have cs : Continuous fun w : ℝ × ℝ ↦ w.2 := continuous_snd
  have cf : Continuous fun w : ℝ × ℝ ↦ w.1 := continuous_fst
  have c₀ := (continuous_lowerSupportFunction_exp hK₀).comp cf
  have c₀' := (continuous_supportFunction_exp hK₀).comp cf
  have c₁ := (continuous_lowerSupportFunction_exp hK₁).comp cf
  have c₁' := (continuous_supportFunction_exp hK₁).comp cf
  exact ((isClosed_le c₁ cs).inter (isClosed_le cs c₁')).inter
    ((isClosed_le cs c₀).union (isClosed_le c₀' cs))

/-- The band `X(K₀, K₁)` of two bounded sets is compact. -/
theorem isCompact_bandSet {K₀ K₁ : Set ℂ} (hK₀ : Bornology.IsBounded K₀)
    (hK₁ : Bornology.IsBounded K₁) : IsCompact (bandSet K₀ K₁) := by
  obtain ⟨R, hR⟩ := hK₁.subset_closedBall 0
  set R' := max R 0
  have hK₁R : K₁ ⊆ Metric.closedBall 0 R' :=
    hR.trans (Metric.closedBall_subset_closedBall (le_max_left _ _))
  -- offsets of lines in the band are bounded by `R'`
  have hbd : ∀ (θ p : ℝ), InBand K₀ K₁ (exp (θ * I)) p → p ∈ Icc (-R') R' := by
    intro θ p hp
    obtain ⟨⟨h1, h2⟩, -⟩ := hp
    rcases K₁.eq_empty_or_nonempty with rfl | hne
    · simp only [lowerSupportFunction_empty, supportFunction_empty] at h1 h2
      exact ⟨by linarith [le_max_right R 0], by linarith [le_max_right R 0]⟩
    · have hnorm : ‖exp (θ * I)‖ = 1 := norm_exp_ofReal_mul_I θ
      have hb : supportFunction K₁ (exp (θ * I)) ≤ R' := by
        have := supportFunction_mono (ω := exp (θ * I)) hne Metric.isBounded_closedBall hK₁R
        rwa [supportFunction_closedBall_zero (le_max_right R 0), hnorm, mul_one] at this
      have ha : -R' ≤ lowerSupportFunction K₁ (exp (θ * I)) := by
        have := lowerSupportFunction_anti (ω := exp (θ * I)) hne Metric.isBounded_closedBall hK₁R
        rwa [lowerSupportFunction_closedBall_zero (le_max_right R 0), hnorm, mul_one] at this
      exact ⟨by linarith, by linarith⟩
  have heq : bandSet K₀ K₁ = unorientedLineCoords ''
      ({w : ℝ × ℝ | InBand K₀ K₁ (exp (w.1 * I)) w.2} ∩ (Icc 0 (2 * π) ×ˢ Icc (-R') R')) := by
    refine Subset.antisymm ?_ (image_mono inter_subset_left)
    rintro _ ⟨w, hw, rfl⟩
    set θ₀ := toIcoMod Real.two_pi_pos 0 w.1
    have hθ₀ : θ₀ ∈ Ico 0 (2 * π) := toIcoMod_mem_Ico' _ _
    set n := toIcoDiv Real.two_pi_pos 0 w.1
    have hθ₀eq : θ₀ = w.1 - n * (2 * π) := by
      have := self_sub_toIcoDiv_zsmul Real.two_pi_pos 0 w.1
      rw [zsmul_eq_mul] at this
      simp only [θ₀, n]
      linarith
    have hexp : exp (θ₀ * I) = exp (w.1 * I) := by
      rw [hθ₀eq, show ((w.1 - n * (2 * π) : ℝ) : ℂ) * I = w.1 * I - n * (2 * π * I) by
        push_cast; ring, exp_sub, exp_int_mul_two_pi_mul_I, div_one]
    refine ⟨(θ₀, w.2), ⟨?_, ⟨hθ₀.1, hθ₀.2.le⟩, hbd w.1 w.2 hw⟩, ?_⟩
    · change InBand K₀ K₁ (exp (θ₀ * I)) w.2
      rw [hexp]
      exact hw
    · rw [unorientedLineCoords_eq_sq, unorientedLineCoords_eq_sq]
      simp only [hexp]
  rw [heq]
  exact ((isCompact_Icc.prod isCompact_Icc).inter_left (isClosed_setOf_inBand hK₀ hK₁)).image
    continuous_unorientedLineCoords

/-- **Unoriented-line transfer** ([Hägg, Lemma 6]).  Let `K₀, K₁ ⊆ ℂ ≅ ℝ²` be bounded (in the
paper: `K₀` open convex, `K₁` compact convex), and let `h : ℝ × ℝ → ℂ` be line-symmetric,
integrable and not a.e. zero on `[0, 2π) × ℝ`, with `h(θ, p) = 0` a.e. unless
`p ∈ X_θ = [a_{K₁}(ω_θ), b_{K₁}(ω_θ)] \ (a_{K₀}(ω_θ), b_{K₀}(ω_θ))`, and whose offset moments are
trigonometric polynomials with frequencies `|k| ≤ j`, `k ≡ j mod 2`.  Then there is a nonzero
complex measure `η` on `X(K₀, K₁)` with `∫ z^j q^ℓ dη = 0` for `j ≥ 0`, `ℓ ≥ 1`. -/
theorem unoriented_line_transfer {K₀ K₁ : Set ℂ} (hK₀ : Bornology.IsBounded K₀)
    (hK₁ : Bornology.IsBounded K₁)
    {h : ℝ × ℝ → ℂ} (hsymm : ∀ᵐ w : ℝ × ℝ, h (w.1 + π, -w.2) = h w)
    (hint : IntegrableOn h (Ico 0 (2 * π) ×ˢ univ))
    (hne : ¬ h =ᵐ[volume.restrict (Ico 0 (2 * π) ×ˢ univ)] 0)
    (hsupp : ∀ᵐ w : ℝ × ℝ, h w ≠ 0 → InBand K₀ K₁ (exp (w.1 * I)) w.2)
    (hmom : ∀ j : ℕ, ∃ c : ℤ → ℂ, (∀ k, c k ≠ 0 → |k| ≤ j ∧ Even ((j : ℤ) + k)) ∧
      ∀ᵐ θ : ℝ, ∫ p : ℝ, (p : ℂ) ^ j * h (θ, p) =
        ∑ k ∈ Finset.Icc (-(j : ℤ)) j, c k * exp (k * θ * I)) :
    ∃ η : ComplexMeasure (bandSet K₀ K₁), η ≠ 0 ∧ ∀ j ℓ : ℕ, 1 ≤ ℓ →
      ∫ᵛ w, ((w : ℂ × ℂ).2 ^ j * (w : ℂ × ℂ).1 ^ ℓ) ∂[ContinuousLinearMap.mul ℝ ℂ; η] = 0 :=
  exists_complexMeasure_of_unoriented_moments (isCompact_bandSet hK₀ hK₁) hsymm hint hne
    (hsupp.mono fun w hw hw0 ↦ (unorientedLineCoords_mem_bandSet_iff w).mpr (hw hw0)) hmom

end LeanestEllipse
