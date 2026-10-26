import LeanestEllipse.IntegralGeometry.Radon.Abel
import LeanestEllipse.IntegralGeometry.Radon.LinearMap
import LeanestEllipse.IntegralGeometry.Radon.Radial

/-!
# Concentric disks: radial functions whose Radon transform vanishes near the origin

In the plane, for `0 < r < R`, there is a nonzero smooth radial function `f` supported in the disk
of radius `R` whose Radon transform vanishes on every line at distance `≤ r` from the origin, and
which is strictly negative on a neighbourhood of the closed disk of radius `r` (so the closed disk
lies in its support).  This is the classical disk construction ([Hägg, Lemma 4],
cf. [Natterer, Section VI.4]): choose a nonnegative nonzero even bump `g` supported in
`{t | r' < |t| < R'}` with `r < r' < R' < R`, and let `f x = Φ ‖x‖` with `Φ` the inverse Abel
transform of `g`; then the Radon transform of `f` is `g`.

## Main results

* `exists_radial_radonTransform_eq_bump`: the construction with the one-dimensional datum `g`
  exposed: `radonTransform f ω p = g p` for all unit `ω` and all `p`;
* `exists_radial_radonTransform_eq_zero`: [Hägg, Lemma 4];
* `exists_radial_radonTransform_eq_zero_complex`: the same for the complex-valued function
  `x ↦ (f x : ℂ)`.

## References

* [C. Hägg, *An Ellipse Criterion for Exact Nonuniqueness in the Planar Interior Radon
  Problem*][Hägg]
* [F. Natterer, *The Mathematics of Computerized Tomography*][Natterer]
-/

open MeasureTheory Set Filter Topology Metric

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fact (Module.finrank ℝ E = 2)] [MeasurableSpace E] [BorelSpace E]

attribute [local instance] FiniteDimensional.of_fact_finrank_eq_two

/-- **Concentric disks, with the Radon datum exposed** ([Hägg, proof of Lemma 4]).  In the plane,
for `0 ≤ r < R` there are a nonnegative, nonzero, even `g ∈ C_c^∞(ℝ)` with
`tsupport g ⊆ {t | r < |t| < R}` and a smooth radial `f : E → ℝ` with
`tsupport f ⊆ ball 0 R` whose Radon transform is `g` in every direction; moreover `f` is strictly
negative on an open neighbourhood of `closedBall 0 r`. -/
theorem exists_radial_radonTransform_eq_bump {r R : ℝ} (hr : 0 ≤ r) (hrR : r < R) :
    ∃ (g : ℝ → ℝ) (f : E → ℝ),
      ContDiff ℝ (⊤ : ℕ∞) g ∧ HasCompactSupport g ∧ Function.Even g ∧ (∀ t, 0 ≤ g t) ∧
      g ≠ 0 ∧ tsupport g ⊆ {t | r < |t| ∧ |t| < R} ∧
      ContDiff ℝ (⊤ : ℕ∞) f ∧ HasCompactSupport f ∧ tsupport f ⊆ ball 0 R ∧ f ≠ 0 ∧
      (∃ Ψ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) Ψ ∧ ∀ x, f x = Ψ (‖x‖ ^ 2)) ∧
      (∀ ω : E, ‖ω‖ = 1 → ∀ p : ℝ, radonTransform f ω p = g p) ∧
      closedBall 0 r ⊆ tsupport f ∧
      ∃ U : Set E, IsOpen U ∧ closedBall 0 r ⊆ U ∧ ∀ x ∈ U, f x < 0 := by
  -- intermediate radii `r < r₁ < R₁ < R`
  set r₁ := (2 * r + R) / 3 with hr₁def
  set R₁ := (r + 2 * R) / 3 with hR₁def
  have hrr₁ : r < r₁ := by linarith
  have hr₁R₁ : r₁ < R₁ := by linarith
  have hR₁R : R₁ < R := by linarith
  have hr₁ : 0 < r₁ := by linarith
  obtain ⟨g, hg, hgc, hge, hgnn, hgne, hgts⟩ :=
    exists_contDiff_even_tsupport_subset_abs hr₁.le hr₁R₁
  have hg1 : ContDiff ℝ 1 g := hg.of_le (by simp)
  -- `g` vanishes on `[-r₁, r₁]`, `g'` vanishes near `0` and beyond `R₁`
  have hgz : ∀ t, |t| ≤ r₁ → g t = 0 := fun t ht ↦
    image_eq_zero_of_notMem_tsupport fun h ↦ (hgts h).1.not_ge ht
  have hdz : ∀ t, R₁ ≤ |t| → deriv g t = 0 := fun t ht ↦
    image_eq_zero_of_notMem_tsupport fun h ↦ (hgts (tsupport_deriv_subset h)).2.not_ge ht
  have h0 : ∀ᶠ t in 𝓝[>] 0, deriv g t = 0 := by
    have h0' : (0 : ℝ) ∉ tsupport (deriv g) := fun h ↦ by
      have := (hgts (tsupport_deriv_subset h)).1
      rw [abs_zero] at this
      exact this.not_gt hr₁
    exact (notMem_tsupport_iff_eventuallyEq.1 h0').filter_mono nhdsWithin_le_nhds
  have hgabs : ∀ t, g |t| = g t := fun t ↦ by
    rcases le_or_gt 0 t with ht | ht
    · rw [abs_of_nonneg ht]
    · rw [abs_of_neg ht, hge t]
  have hne : ∃ t, 0 ≤ t ∧ g t ≠ 0 := by
    obtain ⟨t, ht⟩ := Function.ne_iff.1 hgne
    exact ⟨|t|, abs_nonneg t, by rw [hgabs]; exact ht⟩
  -- the radial profile
  set Ψ := inverseAbelTransformSq g with hΨdef
  have hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ := contDiff_inverseAbelTransformSq hg hgc h0
  have hΨR : ∀ a, R₁ ^ 2 ≤ a → Ψ a = 0 := fun a ha ↦
    inverseAbelTransformSq_eq_zero_of_le (fun t ht ↦ hdz t (ht.trans (le_abs_self t))) ha
  have hΨneg : ∀ ρ, 0 ≤ ρ → ρ < r₁ → Ψ (ρ ^ 2) < 0 := fun ρ hρ hρr ↦
    inverseAbelTransformSq_sq_neg hg1 hgc
      (fun t ht ↦ hgz t (by rw [abs_of_nonneg ht.1]; exact ht.2)) (fun t _ ↦ hgnn t) hne hρ hρr
  set f : E → ℝ := fun x ↦ Ψ (‖x‖ ^ 2) with hfdef
  have hf : ContDiff ℝ (⊤ : ℕ∞) f := hΨ.comp (contDiff_norm_sq ℝ)
  -- support
  have hfs : Function.support f ⊆ ball 0 R₁ := by
    intro x hx
    rw [mem_ball_zero_iff]
    by_contra h
    exact hx (hΨR _ (pow_le_pow_left₀ (by linarith) (not_lt.1 h) 2))
  have hfts : tsupport f ⊆ closedBall 0 R₁ :=
    (closure_mono hfs).trans closure_ball_subset_closedBall
  have hfc : HasCompactSupport f :=
    (isCompact_closedBall (0 : E) R₁).of_isClosed_subset (isClosed_tsupport f) hfts
  -- negativity on `ball 0 r₁`
  have hfneg : ∀ x ∈ ball (0 : E) r₁, f x < 0 := fun x hx ↦
    hΨneg ‖x‖ (norm_nonneg x) (mem_ball_zero_iff.1 hx)
  have hball : closedBall (0 : E) r ⊆ ball 0 r₁ := closedBall_subset_ball hrr₁
  have hsupp : closedBall (0 : E) r ⊆ tsupport f := fun x hx ↦
    subset_tsupport f (hfneg x (hball hx)).ne
  have hfne : f ≠ 0 := fun h ↦ by
    have := hfneg 0 (mem_ball_self hr₁)
    rw [h, Pi.zero_apply] at this
    exact lt_irrefl 0 this
  -- the Radon transform is `g`
  have hradon : ∀ ω : E, ‖ω‖ = 1 → ∀ p : ℝ, radonTransform f ω p = g p := fun ω hω p ↦ by
    rw [hfdef, radonTransform_comp_norm_sq_eq_integral Ψ hω p,
      integral_inverseAbelTransformSq_sq_add_sq hg1 hgc h0 p, hgabs]
  refine ⟨g, f, hg, hgc, hge, hgnn, hgne, fun t ht ↦ ?_, hf, hfc,
    hfts.trans (closedBall_subset_ball hR₁R), hfne, ⟨Ψ, hΨ, fun x ↦ rfl⟩, hradon, hsupp,
    ball 0 r₁, isOpen_ball, hball, hfneg⟩
  exact ⟨hrr₁.trans (hgts ht).1, (hgts ht).2.trans hR₁R⟩

/-- **Concentric disks** ([Hägg, Lemma 4]).  In the plane, for `0 < r < R` there is a nonzero
smooth radial function `f : E → ℝ` with compact support in the open disk of radius `R` whose Radon
transform vanishes on every line at distance `≤ r` from the origin, such that the closed disk of
radius `r` lies in the support of `f` and `f` is strictly negative on an open neighbourhood of that
closed disk. -/
theorem exists_radial_radonTransform_eq_zero {r R : ℝ} (hr : 0 < r) (hrR : r < R) :
    ∃ f : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) f ∧ HasCompactSupport f ∧ tsupport f ⊆ Metric.ball 0 R ∧
      f ≠ 0 ∧
      (∃ Ψ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) Ψ ∧ ∀ x, f x = Ψ (‖x‖ ^ 2)) ∧
      (∀ ω : E, ‖ω‖ = 1 → ∀ p : ℝ, |p| ≤ r → radonTransform f ω p = 0) ∧
      Metric.closedBall 0 r ⊆ tsupport f ∧
      ∃ U : Set E, IsOpen U ∧ Metric.closedBall 0 r ⊆ U ∧ ∀ x ∈ U, f x < 0 := by
  obtain ⟨g, f, -, -, -, -, -, hgts, hf, hfc, hfts, hfne, hΨ, hradon, hsupp, hU⟩ :=
    exists_radial_radonTransform_eq_bump (E := E) hr.le hrR
  refine ⟨f, hf, hfc, hfts, hfne, hΨ, fun ω hω p hp ↦ ?_, hsupp, hU⟩
  rw [hradon ω hω p]
  exact image_eq_zero_of_notMem_tsupport fun h ↦ (hgts h).1.not_ge hp

/-- **Concentric disks, complex-valued version** ([Hägg, Lemma 4]): the conclusions of
`exists_radial_radonTransform_eq_zero` for the complex-valued function `u = (f · : ℂ)`, which is
real-valued and radial, `u x = Ψ (‖x‖ ^ 2)`. -/
theorem exists_radial_radonTransform_eq_zero_complex {r R : ℝ} (hr : 0 < r) (hrR : r < R) :
    ∃ u : E → ℂ, ContDiff ℝ (⊤ : ℕ∞) u ∧ HasCompactSupport u ∧ tsupport u ⊆ Metric.ball 0 R ∧
      u ≠ 0 ∧
      (∃ Ψ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) Ψ ∧ ∀ x, u x = (Ψ (‖x‖ ^ 2) : ℂ)) ∧
      (∀ ω : E, ‖ω‖ = 1 → ∀ p : ℝ, |p| ≤ r → radonTransform u ω p = 0) ∧
      Metric.closedBall 0 r ⊆ tsupport u ∧
      ∃ U : Set E, IsOpen U ∧ Metric.closedBall 0 r ⊆ U ∧ ∀ x ∈ U, (u x).re < 0 := by
  obtain ⟨f, hf, hfc, hfts, hfne, ⟨Ψ, hΨ, hfΨ⟩, hradon, hsupp, U, hU, hrU, hUneg⟩ :=
    exists_radial_radonTransform_eq_zero (E := E) hr hrR
  have hsu : Function.support (fun x ↦ (f x : ℂ)) = Function.support f := by
    ext x
    simp
  have hts : tsupport (fun x ↦ (f x : ℂ)) = tsupport f := by
    rw [tsupport, hsu, tsupport]
  refine ⟨fun x ↦ (f x : ℂ), Complex.ofRealCLM.contDiff.comp hf, ?_, hts ▸ hfts, ?_,
    ⟨Ψ, hΨ, fun x ↦ congrArg Complex.ofReal (hfΨ x)⟩, fun ω hω p hp ↦ ?_, hts ▸ hsupp, U, hU, hrU,
    fun x hx ↦ by simpa using hUneg x hx⟩
  · exact hfc.comp_left Complex.ofReal_zero
  · intro h
    apply hfne
    funext x
    have := congrFun h x
    simpa using this
  · rw [radonTransform_complex_ofReal, hradon ω hω p hp, Complex.ofReal_zero]

end
