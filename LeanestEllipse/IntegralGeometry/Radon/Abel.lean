import Mathlib.Algebra.Group.EvenFunction
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# The Abel transform and its inversion

For a profile `F : ℝ → ℝ`, the *Abel transform*

`abelTransform F p = ∫ s, F (√(p ^ 2 + s ^ 2))`

is the integral of the radial function `x ↦ F ‖x‖` of the plane along a line at distance `|p|`
from the origin.  For `g : ℝ → ℝ` the *inverse Abel transform* is ([Hägg, proof of Lemma 4])

`inverseAbelTransform g ρ = -(1 / π) * ∫ t in Ioi ρ, g' t / √(t ^ 2 - ρ ^ 2)`.

The integrand is singular at `t = ρ`; the substitution `t = √(ρ ^ 2 + y ^ 2)` removes the
singularity and shows `inverseAbelTransform g ρ = inverseAbelTransformSq g (ρ ^ 2)` for `ρ ≥ 0`,
where

`inverseAbelTransformSq g a = -(1 / π) * ∫ y in Ioi 0, ψ (a + y ^ 2)`,
`ψ b = g' (√b) / √b` for `b > 0`, `ψ b = 0` for `b ≤ 0`

(`AbelTransform.divSqrt`).  If `g` is smooth with compact support and `g'` vanishes near `0`, then
`ψ` is smooth with compact support and `inverseAbelTransformSq g` is smooth on all of `ℝ`, so that
`x ↦ inverseAbelTransformSq g ‖x‖²` is a smooth radial function on any real inner product space.

## Main results

Write `Φ = inverseAbelTransform g` and `Ψ = inverseAbelTransformSq g`.

* `contDiff_inverseAbelTransformSq`: `Ψ` is smooth on `ℝ`;
* `inverseAbelTransformSq_eq_zero_of_le`: `Ψ` vanishes beyond the square of the support of `g'`;
* `inverseAbelTransform_eq_inverseAbelTransformSq`: `Φ ρ = Ψ (ρ ^ 2)` for `ρ ≥ 0`;
* `exists_contDiff_hasCompactSupport_eq_inverseAbelTransform_sqrt`: a smooth compactly supported
  function agreeing with `a ↦ Φ (√a)` on `[0, ∞)`;
* `integral_inverseAbelTransformSq_sq_add_sq`, `abelTransform_inverseAbelTransform`: the
  **Abel inversion formula** `∫ s, Ψ (p ^ 2 + s ^ 2) = ∫ s, Φ (√(p ^ 2 + s ^ 2)) = g |p|`, hence
  `abelTransform (inverseAbelTransform g) = g` for even `g`
  (`abelTransform_inverseAbelTransform_of_even`);
* `inverseAbelTransformSq_sq_neg`, `inverseAbelTransform_neg`: **sign**: if `g ≥ 0` on `[0, ∞)`,
  `g = 0` on `[0, r]` and `g ≠ 0` on `[0, ∞)`, then `Φ ρ < 0` for `0 ≤ ρ < r`; in particular
  (`inverseAbelTransform_neg_of_tsupport_subset`) for nonnegative nonzero even `g` with
  `tsupport g ⊆ {t | r < |t|}`;
* `exists_contDiff_even_tsupport_subset_abs`: nonnegative nonzero even bumps supported in
  `{t | r < |t| < R}`.

These are the one-dimensional ingredients of [Hägg, Lemma 4] (concentric disks).

## Implementation notes

The inversion formula is proved through the plane: by Fubini, `∫ s, Ψ (p ^ 2 + s ^ 2)` is
`-(1 / 2π)` times `∫_{ℝ²} ψ (p ^ 2 + |z| ^ 2) dz`, which polar coordinates
(`integral_fun_norm_addHaar` on `ℂ`) turn into `2π ∫_0^∞ r ψ (p ^ 2 + r ^ 2) dr`; the last integrand
is the derivative of `r ↦ g (√(p ^ 2 + r ^ 2))`, so the fundamental theorem of calculus gives
`-2π g |p|`.  This replaces the Beta-integral computation of the classical proof.

## References

* [C. Hägg, *An Ellipse Criterion for Exact Nonuniqueness in the Planar Interior Radon
  Problem*][Hägg]
-/

open MeasureTheory Set Filter Topology Metric
open scoped Real

noncomputable section

/-- The **Abel transform** of a profile `F : ℝ → ℝ`:
`abelTransform F p = ∫ s, F (√(p ^ 2 + s ^ 2))`, the integral of the radial function `x ↦ F ‖x‖`
of the plane along a line at distance `|p|` from the origin. -/
def abelTransform (F : ℝ → ℝ) (p : ℝ) : ℝ :=
  ∫ s : ℝ, F √(p ^ 2 + s ^ 2)

/-- The **inverse Abel transform** of `g : ℝ → ℝ` ([Hägg, proof of Lemma 4]):
`inverseAbelTransform g ρ = -(1 / π) * ∫ t in Ioi ρ, g' t / √(t ^ 2 - ρ ^ 2)`.
See `abelTransform_inverseAbelTransform` for the inversion formula. -/
def inverseAbelTransform (g : ℝ → ℝ) (ρ : ℝ) : ℝ :=
  -(1 / π) * ∫ t in Ioi ρ, deriv g t / √(t ^ 2 - ρ ^ 2)

namespace AbelTransform

/-- `divSqrt h b = h (√b) / √b` for `b > 0`, extended by `0` to `b ≤ 0`.  For `h = g'` this is the
function `ψ` of [Hägg, proof of Lemma 4]. -/
def divSqrt (h : ℝ → ℝ) (b : ℝ) : ℝ :=
  if 0 < b then h √b / √b else 0

/-- `divSqrt h b = h (√b) / √b` for `b > 0`. -/
theorem divSqrt_of_pos (h : ℝ → ℝ) {b : ℝ} (hb : 0 < b) : divSqrt h b = h √b / √b :=
  ite_eq_left hb

/-- `divSqrt h b = 0` for `b ≤ 0`. -/
theorem divSqrt_of_nonpos (h : ℝ → ℝ) {b : ℝ} (hb : b ≤ 0) : divSqrt h b = 0 :=
  ite_eq_right hb.not_gt

/-- `divSqrt h` vanishes beyond the square of a bound for the support of `h` on `[0, ∞)`. -/
theorem divSqrt_eq_zero_of_le {h : ℝ → ℝ} {R b : ℝ} (hh : ∀ t, R ≤ t → h t = 0)
    (hb : R ^ 2 ≤ b) : divSqrt h b = 0 := by
  rcases le_or_gt b 0 with hb0 | hb0
  · exact divSqrt_of_nonpos h hb0
  · rw [divSqrt_of_pos h hb0, hh √b ?_, zero_div]
    calc R ≤ |R| := le_abs_self R
      _ = √(R ^ 2) := (Real.sqrt_sq_eq_abs R).symm
      _ ≤ √b := Real.sqrt_le_sqrt hb

/-- `divSqrt h` has compact support if `h` has. -/
theorem hasCompactSupport_divSqrt {h : ℝ → ℝ} (hh : HasCompactSupport h) :
    HasCompactSupport (divSqrt h) := by
  obtain ⟨R, -, hRh⟩ := hh.exists_pos_le_norm
  refine HasCompactSupport.intro (isCompact_Icc (a := 0) (b := R ^ 2)) fun b hb ↦ ?_
  rcases le_or_gt b 0 with hb0 | hb0
  · exact divSqrt_of_nonpos h hb0
  · refine divSqrt_eq_zero_of_le (R := R) (fun t ht ↦ hRh t ?_) ?_
    · rw [Real.norm_eq_abs]
      exact ht.trans (le_abs_self t)
    · by_contra hbR
      exact hb ⟨hb0.le, (not_le.1 hbR).le⟩

/-- `divSqrt h` is as smooth as `h`, provided `h` vanishes on a right neighbourhood of `0`. -/
theorem contDiff_divSqrt {n : ℕ∞} {h : ℝ → ℝ} (hh : ContDiff ℝ n h)
    (h0 : ∀ᶠ t in 𝓝[>] 0, h t = 0) : ContDiff ℝ n (divSqrt h) := by
  obtain ⟨δ, hδ, hδh⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 h0
  have hδ : (0 : ℝ) < δ := hδ
  rw [contDiff_iff_contDiffAt]
  intro a
  rcases lt_trichotomy a 0 with ha | rfl | ha
  · refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [Iio_mem_nhds ha] with b hb
    exact divSqrt_of_nonpos h (le_of_lt hb)
  · refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [Iio_mem_nhds (pow_pos hδ 2)] with b hb
    rcases le_or_gt b 0 with hb0 | hb0
    · exact divSqrt_of_nonpos h hb0
    · have hzero : h √b = 0 := hδh ⟨Real.sqrt_pos.2 hb0, (Real.sqrt_lt' hδ).2 hb⟩
      rw [divSqrt_of_pos h hb0, hzero, zero_div]
  · have hs : ContDiffAt ℝ n (fun b : ℝ ↦ √b) a := Real.contDiffAt_sqrt ha.ne'
    refine ((hh.contDiffAt.comp a hs).div hs (Real.sqrt_ne_zero'.2 ha)).congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds ha] with b hb
    exact divSqrt_of_pos h hb

/-- If `φ` has compact support, then so has `y ↦ φ (a + y ^ 2)`. -/
theorem hasCompactSupport_comp_add_sq {E : Type*} [Zero E] {φ : ℝ → E}
    (hφ : HasCompactSupport φ) (a : ℝ) : HasCompactSupport fun y : ℝ ↦ φ (a + y ^ 2) := by
  obtain ⟨R, hR, hRφ⟩ := hφ.exists_pos_le_norm
  refine HasCompactSupport.intro (isCompact_closedBall (0 : ℝ) √(R + |a|)) fun y hy ↦ hRφ _ ?_
  rw [mem_closedBall, dist_zero_right, not_le] at hy
  have hy2 : R + |a| < y ^ 2 := by
    have := (Real.sqrt_lt' (lt_of_le_of_lt (Real.sqrt_nonneg _) hy)).1 hy
    rwa [Real.norm_eq_abs, sq_abs] at this
  rw [Real.norm_eq_abs]
  have : R ≤ a + y ^ 2 := by linarith [neg_abs_le a]
  exact this.trans (le_abs_self _)

/-- **Differentiation under the integral sign** for `a ↦ ∫ y in Ioi 0, ψ (a + y ^ 2)`. -/
theorem hasDerivAt_integral_comp_add_sq {ψ : ℝ → ℝ} (hψ : ContDiff ℝ 1 ψ)
    (hψc : HasCompactSupport ψ) (a : ℝ) :
    HasDerivAt (fun a ↦ ∫ y in Ioi (0 : ℝ), ψ (a + y ^ 2))
      (∫ y in Ioi (0 : ℝ), deriv ψ (a + y ^ 2)) a := by
  have hdc : Continuous (deriv ψ) := hψ.continuous_deriv le_rfl
  obtain ⟨R, hR, hRψ⟩ := hψc.deriv.exists_pos_le_norm
  obtain ⟨M, hM⟩ := hdc.bounded_above_of_compact_support hψc.deriv
  set Y := √(R + |a| + 1)
  have hzero : ∀ x ∈ Ioo (a - 1) (a + 1), ∀ y : ℝ, Y < |y| → deriv ψ (x + y ^ 2) = 0 := by
    intro x hx y hy
    apply hRψ
    have hy2 : R + |a| + 1 < y ^ 2 := by
      have := (Real.sqrt_lt' (lt_of_le_of_lt (Real.sqrt_nonneg _) hy)).1 hy
      rwa [sq_abs] at this
    rw [Real.norm_eq_abs]
    have : R ≤ x + y ^ 2 := by linarith [hx.1, neg_abs_le a]
    exact this.trans (le_abs_self _)
  have hF : ∀ x, Continuous fun y : ℝ ↦ ψ (x + y ^ 2) := fun x ↦ hψ.continuous.comp (by fun_prop)
  have hF' : ∀ x, Continuous fun y : ℝ ↦ deriv ψ (x + y ^ 2) := fun x ↦ hdc.comp (by fun_prop)
  have hbound : Integrable ((Icc (-Y) Y).indicator fun _ ↦ M) (volume.restrict (Ioi (0 : ℝ))) :=
    ((integrableOn_const (μ := volume) (by simp)).integrable_indicator measurableSet_Icc).restrict
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi (0 : ℝ)))
    (F := fun x y ↦ ψ (x + y ^ 2)) (F' := fun x y ↦ deriv ψ (x + y ^ 2))
    (bound := (Icc (-Y) Y).indicator fun _ ↦ M) (x₀ := a) (s := Ioo (a - 1) (a + 1))
    (Ioo_mem_nhds (by linarith) (by linarith))
    (Eventually.of_forall fun x ↦ (hF x).aestronglyMeasurable)
    ((hF a).integrable_of_hasCompactSupport (hasCompactSupport_comp_add_sq hψc a)).integrableOn
    (hF' a).aestronglyMeasurable (Eventually.of_forall fun y x hx ↦ ?_) hbound
    (Eventually.of_forall fun y x _ ↦ ?_)).2
  · by_cases hy : y ∈ Icc (-Y) Y
    · rw [indicator_of_mem hy]
      exact hM _
    · have hYy : Y < |y| := by
        by_contra h
        exact hy (abs_le.1 (not_lt.1 h))
      rw [indicator_of_notMem hy, hzero x hx y hYy, norm_zero]
  · exact ((hψ.differentiable one_ne_zero) (x + y ^ 2)).hasDerivAt.comp_add_const x (y ^ 2)

/-- `a ↦ ∫ y in Ioi 0, ψ (a + y ^ 2)` is smooth for smooth compactly supported `ψ`. -/
theorem contDiff_integral_comp_add_sq {ψ : ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψc : HasCompactSupport ψ) :
    ContDiff ℝ (⊤ : ℕ∞) fun a ↦ ∫ y in Ioi (0 : ℝ), ψ (a + y ^ 2) := by
  rw [contDiff_infty]
  intro n
  induction n generalizing ψ with
  | zero =>
    exact contDiff_zero.2 (continuous_iff_continuousAt.2 fun a ↦
      (hasDerivAt_integral_comp_add_sq (hψ.of_le (by simp)) hψc a).continuousAt)
  | succ n ih =>
    have hd := hasDerivAt_integral_comp_add_sq (hψ.of_le (by simp)) hψc
    change ContDiff ℝ ((n : WithTop ℕ∞) + 1) _
    rw [contDiff_succ_iff_deriv]
    refine ⟨fun a ↦ (hd a).differentiableAt, by simp, ?_⟩
    rw [show deriv (fun a ↦ ∫ y in Ioi (0 : ℝ), ψ (a + y ^ 2)) =
        fun a ↦ ∫ y in Ioi (0 : ℝ), deriv ψ (a + y ^ 2) from funext fun a ↦ (hd a).deriv]
    exact ih (contDiff_infty_iff_deriv.1 hψ).2 hψc.deriv

/-- The derivative of `y ↦ g (√(c + y ^ 2))` is `y ↦ y * divSqrt g' (c + y ^ 2)` where
`c + y ^ 2 > 0`. -/
theorem hasDerivAt_comp_sqrt_add_sq {g : ℝ → ℝ} (hg : Differentiable ℝ g) {c y : ℝ}
    (h : 0 < c + y ^ 2) :
    HasDerivAt (fun y ↦ g √(c + y ^ 2)) (y * divSqrt (deriv g) (c + y ^ 2)) y := by
  have h1 : HasDerivAt (fun y : ℝ ↦ c + y ^ 2) (2 * y) y := by
    simpa using (hasDerivAt_pow 2 y).const_add c
  have h2 := (Real.hasDerivAt_sqrt h.ne').comp y h1
  have h3 := (hg √(c + y ^ 2)).hasDerivAt.comp y h2
  have hs : √(c + y ^ 2) ≠ 0 := (Real.sqrt_pos.2 h).ne'
  have he : y * divSqrt (deriv g) (c + y ^ 2) =
      deriv g √(c + y ^ 2) * (1 / (2 * √(c + y ^ 2)) * (2 * y)) := by
    rw [divSqrt_of_pos _ h]
    field_simp
  rw [he]
  exact h3

end AbelTransform

open AbelTransform

/-- The inverse Abel transform as a function of the squared radius:
`inverseAbelTransformSq g a = -(1 / π) * ∫ y in Ioi 0, g' (√(a + y ^ 2)) / √(a + y ^ 2)`
(with the convention `AbelTransform.divSqrt` at nonpositive arguments).  For `ρ ≥ 0`,
`inverseAbelTransform g ρ = inverseAbelTransformSq g (ρ ^ 2)`
(`inverseAbelTransform_eq_inverseAbelTransformSq`), and unlike `ρ ↦ inverseAbelTransform g ρ`
this is a smooth function of `a ∈ ℝ` (`contDiff_inverseAbelTransformSq`). -/
def inverseAbelTransformSq (g : ℝ → ℝ) (a : ℝ) : ℝ :=
  -(1 / π) * ∫ y in Ioi (0 : ℝ), divSqrt (deriv g) (a + y ^ 2)

/-- **Smoothness of the Abel profile** ([Hägg, proof of Lemma 4]): if `g` is smooth with compact
support and `g'` vanishes on a right neighbourhood of `0`, then `inverseAbelTransformSq g` is
smooth on `ℝ`. -/
theorem contDiff_inverseAbelTransformSq {g : ℝ → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hgc : HasCompactSupport g) (h0 : ∀ᶠ t in 𝓝[>] 0, deriv g t = 0) :
    ContDiff ℝ (⊤ : ℕ∞) (inverseAbelTransformSq g) :=
  contDiff_const.mul (contDiff_integral_comp_add_sq
    (contDiff_divSqrt (contDiff_infty_iff_deriv.1 hg).2 h0) (hasCompactSupport_divSqrt hgc.deriv))

/-- The Abel profile vanishes beyond the square of a bound for the support of `g'` on
`[0, ∞)`. -/
theorem inverseAbelTransformSq_eq_zero_of_le {g : ℝ → ℝ} {R a : ℝ}
    (hR : ∀ t, R ≤ t → deriv g t = 0) (ha : R ^ 2 ≤ a) : inverseAbelTransformSq g a = 0 := by
  have : ∀ y : ℝ, divSqrt (deriv g) (a + y ^ 2) = 0 := fun y ↦
    divSqrt_eq_zero_of_le hR (by nlinarith [sq_nonneg y])
  simp [inverseAbelTransformSq, this]

/-- The singular and the nonsingular formulas for the inverse Abel transform agree:
`inverseAbelTransform g ρ = inverseAbelTransformSq g (ρ ^ 2)` for `ρ ≥ 0` (substitution
`t = √(ρ ^ 2 + y ^ 2)`, [Hägg, proof of Lemma 4]). -/
theorem inverseAbelTransform_eq_inverseAbelTransformSq {g : ℝ → ℝ}
    (hgc : HasCompactSupport (deriv g)) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    inverseAbelTransform g ρ = inverseAbelTransformSq g (ρ ^ 2) := by
  obtain ⟨A, hA, hAg⟩ := hgc.exists_pos_le_norm
  have hAg' : ∀ t, A ≤ t → deriv g t = 0 := fun t ht ↦
    hAg t (by rw [Real.norm_eq_abs]; exact ht.trans (le_abs_self t))
  unfold inverseAbelTransform inverseAbelTransformSq
  congr 1
  rcases lt_or_ge ρ A with hρA | hAρ
  · -- the substitution `t = L y = √(ρ ^ 2 + y ^ 2)` on `[0, Y]`, `L 0 = ρ`, `L Y = A`
    set L : ℝ → ℝ := fun y ↦ √(ρ ^ 2 + y ^ 2) with hLdef
    have hAρ2 : 0 < A ^ 2 - ρ ^ 2 := by nlinarith
    set Y := √(A ^ 2 - ρ ^ 2) with hYdef
    have hY : 0 < Y := Real.sqrt_pos.2 hAρ2
    have hL0 : L 0 = ρ := by simp [L, Real.sqrt_sq hρ]
    have hLY : L Y = A := by
      simp only [L, Y]
      rw [Real.sq_sqrt hAρ2.le, add_sub_cancel, Real.sqrt_sq hA.le]
    have hLpos : ∀ y, 0 < y → 0 < ρ ^ 2 + y ^ 2 := fun y hy ↦ by positivity
    have hsub := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg (a := 0) (b := Y)
      (f := L) (f' := fun y ↦ y / L y) (g := fun t ↦ deriv g t / √(t ^ 2 - ρ ^ 2))
      (by simp only [L]; fun_prop)
      (fun y hy ↦ by
        rw [min_eq_left hY.le, max_eq_right hY.le] at hy
        have h1 : HasDerivAt (fun y : ℝ ↦ ρ ^ 2 + y ^ 2) (2 * y) y := by
          simpa using (hasDerivAt_pow 2 y).const_add (ρ ^ 2)
        have h2 := (Real.hasDerivAt_sqrt (hLpos y hy.1).ne').comp y h1
        have hs : √(ρ ^ 2 + y ^ 2) ≠ 0 := (Real.sqrt_pos.2 (hLpos y hy.1)).ne'
        have he : y / L y = 1 / (2 * √(ρ ^ 2 + y ^ 2)) * (2 * y) := by
          simp only [L]
          field_simp
        rw [he]
        exact h2)
      (fun y hy ↦ by
        rw [min_eq_left hY.le, max_eq_right hY.le] at hy
        exact div_nonneg hy.1.le (Real.sqrt_nonneg _))
    rw [hL0, hLY] at hsub
    -- the singular integral only sees `(ρ, A]`
    have hleft : ∫ t in Ioi ρ, deriv g t / √(t ^ 2 - ρ ^ 2) =
        ∫ t in ρ..A, deriv g t / √(t ^ 2 - ρ ^ 2) := by
      rw [intervalIntegral.integral_of_le hρA.le]
      refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
        Ioc_subset_Ioi_self fun t ht ↦ ?_
      have hAt : A < t := lt_of_not_ge fun htA ↦ ht.2 ⟨ht.1, htA⟩
      simp [hAg' t hAt.le]
    -- the nonsingular integral only sees `(0, Y]`
    have hright : ∫ y in Ioi (0 : ℝ), divSqrt (deriv g) (ρ ^ 2 + y ^ 2) =
        ∫ y in (0 : ℝ)..Y, divSqrt (deriv g) (ρ ^ 2 + y ^ 2) := by
      rw [intervalIntegral.integral_of_le hY.le]
      refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
        Ioc_subset_Ioi_self fun y hy ↦ ?_
      have hYy : Y < y := lt_of_not_ge fun hyY ↦ hy.2 ⟨hy.1, hyY⟩
      refine divSqrt_eq_zero_of_le hAg' ?_
      have hY2 : Y ^ 2 = A ^ 2 - ρ ^ 2 := Real.sq_sqrt hAρ2.le
      nlinarith
    rw [hleft, hright, ← hsub, intervalIntegral.integral_of_le hY.le,
      intervalIntegral.integral_of_le hY.le]
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
    have hy0 : 0 < y := hy.1
    have hpos := hLpos y hy0
    have hLy : L y ^ 2 - ρ ^ 2 = y ^ 2 := by
      simp only [L]
      rw [Real.sq_sqrt hpos.le]
      ring
    have hs : L y ≠ 0 := (Real.sqrt_pos.2 hpos).ne'
    simp only [Function.comp_apply, hLy, Real.sqrt_sq hy0.le, divSqrt_of_pos _ hpos]
    simp only [L] at hs ⊢
    field_simp
  · -- both integrals vanish
    have h1 : ∫ t in Ioi ρ, deriv g t / √(t ^ 2 - ρ ^ 2) = 0 := by
      refine setIntegral_eq_zero_of_forall_eq_zero fun t ht ↦ ?_
      simp [hAg' t (hAρ.trans (le_of_lt ht))]
    have h2 : ∫ y in Ioi (0 : ℝ), divSqrt (deriv g) (ρ ^ 2 + y ^ 2) = 0 := by
      refine setIntegral_eq_zero_of_forall_eq_zero fun y _ ↦ divSqrt_eq_zero_of_le hAg' ?_
      nlinarith [sq_nonneg y]
    rw [h1, h2]

/-- A smooth, compactly supported function on `ℝ` agreeing with `a ↦ Φ (√a)` on `[0, ∞)`, where
`Φ = inverseAbelTransform g` ([Hägg, proof of Lemma 4]).  (`inverseAbelTransformSq g` itself is
smooth and agrees with `a ↦ Φ (√a)` on `[0, ∞)`, but in general it does not vanish on `(-∞, 0)`.) -/
theorem exists_contDiff_hasCompactSupport_eq_inverseAbelTransform_sqrt {g : ℝ → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hgc : HasCompactSupport g)
    (h0 : ∀ᶠ t in 𝓝[>] 0, deriv g t = 0) :
    ∃ Ψ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) Ψ ∧ HasCompactSupport Ψ ∧
      ∀ a, 0 ≤ a → Ψ a = inverseAbelTransform g √a := by
  obtain ⟨A, hA, hAg⟩ := hgc.deriv.exists_pos_le_norm
  have hAg' : ∀ t, A ≤ t → deriv g t = 0 := fun t ht ↦
    hAg t (by rw [Real.norm_eq_abs]; exact ht.trans (le_abs_self t))
  let χ : ContDiffBump (A ^ 2 / 2) := ⟨A ^ 2 / 2 + 1, A ^ 2 / 2 + 2, by positivity, by linarith⟩
  refine ⟨fun a ↦ χ a * inverseAbelTransformSq g a,
    χ.contDiff.mul (contDiff_inverseAbelTransformSq hg hgc h0), χ.hasCompactSupport.mul_right,
    fun a ha ↦ ?_⟩
  dsimp only
  rw [inverseAbelTransform_eq_inverseAbelTransformSq hgc.deriv (Real.sqrt_nonneg a),
    Real.sq_sqrt ha]
  rcases le_or_gt a (A ^ 2) with haA | haA
  · have hχ : χ.rIn = A ^ 2 / 2 + 1 := rfl
    rw [χ.one_of_mem_closedBall, one_mul]
    rw [mem_closedBall, Real.dist_eq, abs_le, hχ]
    constructor <;> linarith
  · rw [inverseAbelTransformSq_eq_zero_of_le hAg' haA.le, mul_zero]

/-- **Abel inversion formula**, nonsingular form: if `g` is `C¹` with compact support and `g'`
vanishes on a right neighbourhood of `0`, then `∫ s, inverseAbelTransformSq g (p ^ 2 + s ^ 2) =
g |p|` for every `p`. -/
theorem integral_inverseAbelTransformSq_sq_add_sq {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g)
    (hgc : HasCompactSupport g) (h0 : ∀ᶠ t in 𝓝[>] 0, deriv g t = 0) (p : ℝ) :
    ∫ s : ℝ, inverseAbelTransformSq g (p ^ 2 + s ^ 2) = g |p| := by
  have hψ : Continuous (divSqrt (deriv g)) :=
    (contDiff_divSqrt (n := 0) (contDiff_zero.2 (hg.continuous_deriv le_rfl)) h0).continuous
  have hψc : HasCompactSupport (divSqrt (deriv g)) := hasCompactSupport_divSqrt hgc.deriv
  -- the planar integrand
  set H : ℝ × ℝ → ℝ := fun w ↦ divSqrt (deriv g) (p ^ 2 + w.1 ^ 2 + w.2 ^ 2) with hHdef
  have hHc : Continuous H := hψ.comp (by fun_prop)
  have hHs : HasCompactSupport H := by
    obtain ⟨A, hA, hAψ⟩ := hψc.exists_pos_le_norm
    refine HasCompactSupport.intro (isCompact_closedBall (0 : ℝ × ℝ) (A + 1)) fun w hw ↦
      hAψ _ ?_
    rw [mem_closedBall, dist_zero_right, not_le, Prod.norm_def] at hw
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    rcases lt_max_iff.1 hw with h | h
    · rw [Real.norm_eq_abs] at h
      nlinarith [mul_self_lt_mul_self (by linarith : 0 ≤ A + 1) h, sq_abs w.1, sq_nonneg w.2,
        sq_nonneg p]
    · rw [Real.norm_eq_abs] at h
      nlinarith [mul_self_lt_mul_self (by linarith : 0 ≤ A + 1) h, sq_abs w.2, sq_nonneg w.1,
        sq_nonneg p]
  have hH : Integrable H (volume.prod volume) := by
    rw [← Measure.volume_eq_prod]
    exact hHc.integrable_of_hasCompactSupport hHs
  -- the inner half-line integral is half of a full-line integral
  have h1 : ∀ s : ℝ, inverseAbelTransformSq g (p ^ 2 + s ^ 2) =
      -(1 / (2 * π)) * ∫ y, H (s, y) := by
    intro s
    have := integral_comp_abs (f := fun y ↦ divSqrt (deriv g) (p ^ 2 + s ^ 2 + y ^ 2))
    simp only [sq_abs] at this
    simp only [inverseAbelTransformSq, H, this]
    field_simp
  -- polar coordinates in the plane `ℂ`
  have h2 : ∫ w, H w ∂(volume.prod volume) =
      2 * π * ∫ r in Ioi (0 : ℝ), r * divSqrt (deriv g) (p ^ 2 + r ^ 2) := by
    rw [← Measure.volume_eq_prod, ← Complex.volume_preserving_equiv_real_prod.integral_comp']
    have hz : ∀ z : ℂ, H (Complex.measurableEquivRealProd z) =
        divSqrt (deriv g) (p ^ 2 + ‖z‖ ^ 2) := by
      intro z
      simp only [H, Complex.measurableEquivRealProd_apply, Complex.sq_norm, Complex.normSq_apply]
      ring_nf
    simp_rw [hz]
    have hpolar := integral_fun_norm_addHaar (volume : Measure ℂ)
      (fun r ↦ divSqrt (deriv g) (p ^ 2 + r ^ 2))
    rw [hpolar]
    simp [Complex.finrank_real_complex, measureReal_def, nsmul_eq_mul, smul_eq_mul, mul_assoc]
  -- the fundamental theorem of calculus
  have h5 : ∫ r in Ioi (0 : ℝ), r * divSqrt (deriv g) (p ^ 2 + r ^ 2) = -g |p| := by
    have hderiv : ∀ r ∈ Ioi (0 : ℝ), HasDerivAt (fun r ↦ g √(p ^ 2 + r ^ 2))
        (r * divSqrt (deriv g) (p ^ 2 + r ^ 2)) r := fun r hr ↦
      hasDerivAt_comp_sqrt_add_sq (hg.differentiable one_ne_zero)
        (by have : 0 < r := hr; positivity)
    have hint : IntegrableOn (fun r ↦ r * divSqrt (deriv g) (p ^ 2 + r ^ 2)) (Ioi 0) :=
      ((continuous_id.mul (hψ.comp (by fun_prop))).integrable_of_hasCompactSupport
        (hasCompactSupport_comp_add_sq hψc (p ^ 2)).mul_left).integrableOn
    have hlim : Tendsto (fun r ↦ g √(p ^ 2 + r ^ 2)) atTop (𝓝 0) := by
      obtain ⟨B, hB, hBg⟩ := hgc.exists_pos_le_norm
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop B] with r hr
      refine (hBg _ ?_).symm
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
      calc B ≤ r := hr
        _ = √(r ^ 2) := (Real.sqrt_sq (hB.le.trans hr)).symm
        _ ≤ √(p ^ 2 + r ^ 2) := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg p])
    have hcont : ContinuousWithinAt (fun r ↦ g √(p ^ 2 + r ^ 2)) (Ici 0) 0 :=
      (hg.continuous.comp (by fun_prop)).continuousWithinAt
    rw [integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv hint hlim]
    simp [Real.sqrt_sq_eq_abs]
  calc ∫ s : ℝ, inverseAbelTransformSq g (p ^ 2 + s ^ 2)
      = ∫ s : ℝ, -(1 / (2 * π)) * ∫ y, H (s, y) := by simp_rw [h1]
    _ = -(1 / (2 * π)) * ∫ w, H w ∂(volume.prod volume) := by
        rw [integral_const_mul, integral_prod H hH]
    _ = g |p| := by
        rw [h2, h5]
        field_simp

/-- **Abel inversion formula** ([Hägg, proof of Lemma 4]): if `g` is `C¹` with compact support
and `g'` vanishes on a right neighbourhood of `0`, then `∫ s, Φ (√(p ^ 2 + s ^ 2)) = g |p|` for
the inverse Abel transform `Φ` of `g`. -/
theorem abelTransform_inverseAbelTransform {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g)
    (hgc : HasCompactSupport g) (h0 : ∀ᶠ t in 𝓝[>] 0, deriv g t = 0) (p : ℝ) :
    abelTransform (inverseAbelTransform g) p = g |p| := by
  rw [abelTransform, ← integral_inverseAbelTransformSq_sq_add_sq hg hgc h0 p]
  refine integral_congr_ae (Eventually.of_forall fun s ↦ ?_)
  simp only
  rw [inverseAbelTransform_eq_inverseAbelTransformSq hgc.deriv (Real.sqrt_nonneg _),
    Real.sq_sqrt (by positivity)]

/-- **Abel inversion formula** for even data: `abelTransform (inverseAbelTransform g) = g`. -/
theorem abelTransform_inverseAbelTransform_of_even {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g)
    (hgc : HasCompactSupport g) (h0 : ∀ᶠ t in 𝓝[>] 0, deriv g t = 0) (hge : Function.Even g)
    (p : ℝ) : abelTransform (inverseAbelTransform g) p = g p := by
  rw [abelTransform_inverseAbelTransform hg hgc h0 p]
  rcases le_or_gt 0 p with hp | hp
  · rw [abs_of_nonneg hp]
  · rw [abs_of_neg hp, hge p]

/-- **Sign of the Abel profile** ([Hägg, proof of Lemma 4]): if `g` is `C¹` with compact support,
`g = 0` on `[0, r]`, `g ≥ 0` on `[0, ∞)` and `g ≠ 0` somewhere on `[0, ∞)`, then
`inverseAbelTransformSq g (ρ ^ 2) < 0` for `0 ≤ ρ < r`.  Indeed, integrating by parts,
`inverseAbelTransformSq g (ρ ^ 2) = -(1 / π) * ∫_0^∞ g (√(ρ ^ 2 + y ^ 2)) / y ^ 2 dy`. -/
theorem inverseAbelTransformSq_sq_neg {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g)
    (hgc : HasCompactSupport g) {r : ℝ} (hgr : ∀ t ∈ Icc 0 r, g t = 0)
    (hnn : ∀ t, 0 ≤ t → 0 ≤ g t) (hne : ∃ t, 0 ≤ t ∧ g t ≠ 0) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hρr : ρ < r) : inverseAbelTransformSq g (ρ ^ 2) < 0 := by
  have hgd : Differentiable ℝ g := hg.differentiable one_ne_zero
  have hr : 0 < r := hρ.trans_lt hρr
  obtain ⟨A, hA, hAg⟩ := hgc.exists_pos_le_norm
  obtain ⟨t₁, ht₁, hgt₁⟩ := hne
  have hgt₁' : 0 < g t₁ := lt_of_le_of_ne (hnn t₁ ht₁) (Ne.symm hgt₁)
  have hrt₁ : r < t₁ := by
    by_contra h
    exact hgt₁ (hgr t₁ ⟨ht₁, not_lt.1 h⟩)
  have ht₁A : t₁ < A := by
    by_contra h
    exact hgt₁ (hAg t₁ (by rw [Real.norm_eq_abs, abs_of_nonneg ht₁]; exact not_lt.1 h))
  -- `g'` vanishes on `(0, r)` and on `(A, ∞)`
  have hd0 : ∀ t ∈ Ioo 0 r, deriv g t = 0 := by
    intro t ht
    have : g =ᶠ[𝓝 t] 0 := by
      filter_upwards [Ioo_mem_nhds ht.1 ht.2] with u hu using hgr u ⟨hu.1.le, hu.2.le⟩
    rw [this.deriv_eq]
    simp
  have hgA : ∀ t, A ≤ t → g t = 0 := fun t ht ↦
    hAg t (by rw [Real.norm_eq_abs]; exact ht.trans (le_abs_self t))
  have hdA : ∀ t, A < t → deriv g t = 0 := by
    intro t ht
    have : g =ᶠ[𝓝 t] 0 := by
      filter_upwards [Ioi_mem_nhds ht] with u hu using hgA u hu.le
    rw [this.deriv_eq]
    simp
  have hψ : Continuous (divSqrt (deriv g)) := by
    refine (contDiff_divSqrt (n := 0) (contDiff_zero.2 (hg.continuous_deriv le_rfl))
      ?_).continuous
    filter_upwards [Ioo_mem_nhdsGT hr] with t ht using hd0 t ht
  set c := ρ ^ 2 with hc
  have hc0 : 0 ≤ c := by positivity
  have hrc : 0 < r ^ 2 - c := by nlinarith
  set y₀ := √(r ^ 2 - c) / 2 with hy₀def
  have hy₀ : 0 < y₀ := by
    have := Real.sqrt_pos.2 hrc
    positivity
  have hy₀sq : y₀ ^ 2 = (r ^ 2 - c) / 4 := by
    rw [hy₀def, div_pow, Real.sq_sqrt hrc.le]
    norm_num
  set Y := A + y₀ with hYdef
  have hY : 0 < Y := by positivity
  have hy₀Y : y₀ < Y := by linarith
  have hmem : ∀ x ∈ uIcc y₀ Y, 0 < x := fun x hx ↦ by
    rw [uIcc_of_le hy₀Y.le] at hx
    exact hy₀.trans_le hx.1
  set G : ℝ → ℝ := fun y ↦ g √(c + y ^ 2) with hGdef
  have hGc : Continuous G := hg.continuous.comp (by fun_prop)
  -- `G` vanishes at the ends of `[y₀, Y]`
  have hGy₀ : G y₀ = 0 := by
    refine hgr _ ⟨Real.sqrt_nonneg _, ((Real.sqrt_lt' hr).2 ?_).le⟩
    nlinarith
  have hGY : G Y = 0 := by
    refine hgA _ ((Real.le_sqrt hA.le (by positivity)).2 ?_)
    nlinarith
  -- integration by parts on `[y₀, Y]`
  have hibp : ∫ y in y₀..Y, divSqrt (deriv g) (c + y ^ 2) = ∫ y in y₀..Y, G y * (y ^ 2)⁻¹ := by
    have hu : ∀ x ∈ uIcc y₀ Y, HasDerivAt G (x * divSqrt (deriv g) (c + x ^ 2)) x :=
      fun x hx ↦ hasDerivAt_comp_sqrt_add_sq hgd (by have := hmem x hx; positivity)
    have hv : ∀ x ∈ uIcc y₀ Y, HasDerivAt (fun y : ℝ ↦ -y⁻¹) ((x ^ 2)⁻¹) x := fun x hx ↦ by
      have h := (hasDerivAt_inv (hmem x hx).ne').neg
      rw [neg_neg] at h
      exact h
    have hu' : IntervalIntegrable (fun x ↦ x * divSqrt (deriv g) (c + x ^ 2)) volume y₀ Y :=
      (continuous_id.mul (hψ.comp (by fun_prop))).intervalIntegrable _ _
    have hv' : IntervalIntegrable (fun x : ℝ ↦ (x ^ 2)⁻¹) volume y₀ Y := by
      refine ContinuousOn.intervalIntegrable ?_
      exact (continuous_pow 2).continuousOn.inv₀ fun x hx ↦ pow_ne_zero 2 (hmem x hx).ne'
    rw [intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv hu' hv', hGy₀, hGY, zero_mul,
      zero_mul, sub_zero, zero_sub, ← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr fun x hx ↦ ?_
    have hx0 : x ≠ 0 := (hmem x hx).ne'
    field_simp
  -- positivity of `∫_{y₀}^{Y} G y / y ^ 2`
  set F : ℝ → ℝ := fun y ↦ G y * (y ^ 2)⁻¹ with hFdef
  have hFcont : ContinuousOn F (uIcc y₀ Y) :=
    hGc.continuousOn.mul ((continuous_pow 2).continuousOn.inv₀ fun x hx ↦
      pow_ne_zero 2 (hmem x hx).ne')
  have hFpos : 0 < ∫ y in y₀..Y, F y := by
    have hF0 : 0 ≤ᵐ[volume.restrict (uIoc y₀ Y)] F := Eventually.of_forall fun y ↦
      mul_nonneg (hnn _ (Real.sqrt_nonneg _)) (inv_nonneg.2 (sq_nonneg y))
    refine (intervalIntegral.integral_pos_iff_support_of_nonneg_ae' hF0
      hFcont.intervalIntegrable).2 ⟨hy₀Y, ?_⟩
    -- an open nonempty subset of the support
    set y₁ := √(t₁ ^ 2 - c) with hy₁def
    have ht₁c : 0 < t₁ ^ 2 - c := by nlinarith
    have hy₀y₁ : y₀ < y₁ := (Real.lt_sqrt hy₀.le).2 (by nlinarith)
    have hy₁Y : y₁ < Y := (Real.sqrt_lt' hY).2 (by nlinarith)
    have hFy₁ : F y₁ ≠ 0 := by
      have hy₁0 : 0 < y₁ := hy₀.trans hy₀y₁
      have hGy₁ : G y₁ = g t₁ := by
        simp only [G, y₁]
        rw [Real.sq_sqrt ht₁c.le, add_sub_cancel, Real.sqrt_sq ht₁]
      simp only [F, hGy₁]
      positivity
    have hopen : IsOpen (Ioo y₀ Y ∩ F ⁻¹' {0}ᶜ) := by
      refine ContinuousOn.isOpen_inter_preimage ?_ isOpen_Ioo isOpen_compl_singleton
      exact hFcont.mono (Ioo_subset_Icc_self.trans (uIcc_of_le hy₀Y.le).symm.subset)
    calc (0 : ENNReal) < volume (Ioo y₀ Y ∩ F ⁻¹' {0}ᶜ) :=
          hopen.measure_pos volume ⟨y₁, ⟨hy₀y₁, hy₁Y⟩, hFy₁⟩
      _ ≤ volume (Function.support F ∩ Ioc y₀ Y) :=
          measure_mono fun y hy ↦ ⟨hy.2, Ioo_subset_Ioc_self hy.1⟩
  -- the half-line integral only sees `(y₀, Y]`
  have hsupp : ∫ y in Ioi (0 : ℝ), divSqrt (deriv g) (c + y ^ 2) =
      ∫ y in y₀..Y, divSqrt (deriv g) (c + y ^ 2) := by
    rw [intervalIntegral.integral_of_le hy₀Y.le]
    refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
      (fun y hy ↦ hy₀.trans hy.1) fun y hy ↦ ?_
    obtain ⟨hy0, hy'⟩ := hy
    have hy0 : 0 < y := hy0
    have hpos : 0 < c + y ^ 2 := by positivity
    rw [divSqrt_of_pos _ hpos]
    rcases le_or_gt y y₀ with h | h
    · rw [hd0 _ ⟨Real.sqrt_pos.2 hpos, (Real.sqrt_lt' hr).2 (by nlinarith)⟩, zero_div]
    · have hYy : Y < y := lt_of_not_ge fun h' ↦ hy' ⟨h, h'⟩
      rw [hdA _ ?_, zero_div]
      calc A < y := by linarith
        _ = √(y ^ 2) := (Real.sqrt_sq hy0.le).symm
        _ ≤ √(c + y ^ 2) := Real.sqrt_le_sqrt (by linarith)
  have hπ : 0 < 1 / π := by positivity
  rw [inverseAbelTransformSq, hsupp, hibp]
  nlinarith

/-- **Sign of the inverse Abel transform** ([Hägg, proof of Lemma 4]): if `g` is `C¹` with compact
support, `g = 0` on `[0, r]`, `g ≥ 0` on `[0, ∞)` and `g ≠ 0` somewhere on `[0, ∞)`, then
`inverseAbelTransform g ρ < 0` for `0 ≤ ρ < r`. -/
theorem inverseAbelTransform_neg {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g)
    (hgc : HasCompactSupport g) {r : ℝ} (hgr : ∀ t ∈ Icc 0 r, g t = 0)
    (hnn : ∀ t, 0 ≤ t → 0 ≤ g t) (hne : ∃ t, 0 ≤ t ∧ g t ≠ 0) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hρr : ρ < r) : inverseAbelTransform g ρ < 0 := by
  rw [inverseAbelTransform_eq_inverseAbelTransformSq hgc.deriv hρ]
  exact inverseAbelTransformSq_sq_neg hg hgc hgr hnn hne hρ hρr

/-- **Sign of the inverse Abel transform**, support form ([Hägg, proof of Lemma 4]): if `g` is a
nonnegative, nonzero, even `C¹` function with compact support and `tsupport g ⊆ {t | r < |t|}`,
then `inverseAbelTransform g ρ < 0` for `0 ≤ ρ < r`. -/
theorem inverseAbelTransform_neg_of_tsupport_subset {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g)
    (hgc : HasCompactSupport g) (hge : Function.Even g) (hnn : ∀ t, 0 ≤ g t) (hne : g ≠ 0)
    {r : ℝ} (hgts : tsupport g ⊆ {t | r < |t|}) {ρ : ℝ} (hρ : 0 ≤ ρ) (hρr : ρ < r) :
    inverseAbelTransform g ρ < 0 := by
  refine inverseAbelTransform_neg hg hgc (r := r) (fun t ht ↦ ?_) (fun t _ ↦ hnn t) ?_ hρ hρr
  · refine image_eq_zero_of_notMem_tsupport fun h ↦ (show r < |t| from hgts h).not_ge ?_
    rw [abs_of_nonneg ht.1]
    exact ht.2
  · obtain ⟨t, ht⟩ := Function.ne_iff.1 hne
    refine ⟨|t|, abs_nonneg t, ?_⟩
    rcases le_or_gt 0 t with h | h
    · rwa [abs_of_nonneg h]
    · rwa [abs_of_neg h, hge]

/-- **Even bumps in a one-dimensional annulus**: for `0 ≤ r < R` there is a nonnegative, nonzero,
even, smooth, compactly supported `g : ℝ → ℝ` with `tsupport g ⊆ {t | r < |t| < R}` (the datum of
[Hägg, proof of Lemma 4]). -/
theorem exists_contDiff_even_tsupport_subset_abs {r R : ℝ} (hr : 0 ≤ r) (hrR : r < R) :
    ∃ g : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) g ∧ HasCompactSupport g ∧ Function.Even g ∧
      (∀ t, 0 ≤ g t) ∧ g ≠ 0 ∧ tsupport g ⊆ {t | r < |t| ∧ |t| < R} := by
  have hR : 0 < R := hr.trans_lt hrR
  have hrR2 : r ^ 2 < R ^ 2 := by nlinarith
  set m := (r ^ 2 + R ^ 2) / 2 with hm
  obtain ⟨b, hbs, -, hb, hb01, hb1⟩ := exists_contDiff_tsupport_subset (n := ⊤) (x := m)
    (Ioo_mem_nhds (by linarith : r ^ 2 < m) (by linarith : m < R ^ 2))
  have hts : tsupport (fun t : ℝ ↦ b (t ^ 2)) ⊆ {t | r < |t| ∧ |t| < R} := by
    intro t ht
    have ht' := hbs (tsupport_comp_subset_preimage b (continuous_pow 2) ht)
    refine ⟨?_, ?_⟩
    · rw [← abs_of_nonneg hr]
      exact sq_lt_sq.1 ht'.1
    · rw [← abs_of_pos hR]
      exact sq_lt_sq.1 ht'.2
  refine ⟨fun t ↦ b (t ^ 2), hb.comp (contDiff_id.pow 2), ?_, fun t ↦ by simp,
    fun t ↦ (hb01 ⟨_, rfl⟩).1, ?_, hts⟩
  · refine HasCompactSupport.intro (isCompact_Icc (a := -R) (b := R)) fun t ht ↦ ?_
    refine image_eq_zero_of_notMem_tsupport (f := fun t : ℝ ↦ b (t ^ 2)) fun ht' ↦ ht ?_
    have := (hts ht').2
    exact ⟨by linarith [neg_abs_le t], by linarith [le_abs_self t]⟩
  · intro h
    have := congrFun h √m
    simp only [Pi.zero_apply] at this
    rw [Real.sq_sqrt (by positivity), hb1] at this
    exact one_ne_zero this
