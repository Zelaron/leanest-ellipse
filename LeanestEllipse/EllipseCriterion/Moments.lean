import LeanestEllipse.IntegralGeometry.Radon.Plane

/-!
# Helgason–Ludwig moment conditions in the plane ([Hägg, (5.3)])

For a compactly supported integrable `g : ℂ → ℂ` (the plane `ℝ²` is modelled by `ℂ`), the `j`-th
offset moment of its Radon transform,
`θ ↦ ∫ p^j 𝓡 g(e^{iθ}, p) dp = ∫ ⟪x, e^{iθ}⟫^j g(x) dx`,
is a trigonometric polynomial containing only the frequencies `e^{ikθ}` with `|k| ≤ j` and
`k ≡ j (mod 2)` (`LeanestEllipse.exists_trigPoly_radon_moment`).
-/

open MeasureTheory Set Complex Filter
open scoped Real ComplexConjugate RealInnerProductSpace

noncomputable section

namespace LeanestEllipse

/-- `⟪x, e^{iθ}⟫ = (e^{iθ} x̄ + e^{-iθ} x) / 2`. -/
theorem ofReal_inner_exp (x : ℂ) (θ : ℝ) :
    ((⟪x, exp (θ * I)⟫ : ℝ) : ℂ) = (exp (θ * I) * conj x + exp (-(θ * I)) * x) / 2 := by
  rw [Complex.inner, Complex.re_eq_add_conj, map_mul, Complex.conj_conj, ← Complex.exp_conj,
    map_mul, Complex.conj_ofReal, Complex.conj_I]
  ring_nf

theorem exp_pow_mul_exp_neg_pow (θ : ℝ) {m j : ℕ} (hm : m ≤ j) :
    exp (θ * I) ^ m * exp (-(θ * I)) ^ (j - m) = exp (((2 * (m : ℤ) - j : ℤ) : ℂ) * θ * I) := by
  rw [← exp_nat_mul, ← exp_nat_mul, ← exp_add]
  congr 1
  push_cast [Nat.cast_sub hm]
  ring

/-- **Helgason–Ludwig moments in the plane.**  For an integrable `g` vanishing outside a ball,
the `j`-th offset moment of its Radon transform is a trigonometric polynomial in the angle with
frequencies `|k| ≤ j`, `k ≡ j (mod 2)`. -/
theorem exists_trigPoly_radon_moment {g : ℂ → ℂ} (hg : Integrable g) {R : ℝ}
    (hgR : ∀ x, g x ≠ 0 → ‖x‖ ≤ R) (j : ℕ) :
    ∃ c : ℤ → ℂ, (∀ k, c k ≠ 0 → |k| ≤ j ∧ Even ((j : ℤ) + k)) ∧
      ∀ θ : ℝ, ∫ p : ℝ, (p : ℂ) ^ j * radonTransform g (exp (θ * I)) p =
        ∑ k ∈ Finset.Icc (-(j : ℤ)) j, c k * exp (k * θ * I) := by
  have hR : ∀ x, ‖x‖ ≤ R ∨ g x = 0 := fun x ↦ by
    by_cases h : g x = 0
    · exact Or.inr h
    · exact Or.inl (hgR x h)
  -- weighted moments of `g` are integrable
  have hbd : ∀ (m n : ℕ), Integrable fun x : ℂ ↦ conj x ^ m * x ^ n * g x := by
    intro m n
    refine Integrable.mono' (hg.norm.const_mul (|R| ^ (m + n)))
      ((by fun_prop : Continuous fun x : ℂ ↦ conj x ^ m * x ^ n).aestronglyMeasurable.mul
        hg.aestronglyMeasurable) (Eventually.of_forall fun x ↦ ?_)
    rcases hR x with h | h
    · rw [norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_conj, ← pow_add]
      gcongr
      exact h.trans (le_abs_self R)
    · simp [h]
  set a : ℕ → ℂ := fun m ↦ (Nat.choose j m : ℂ) / 2 ^ j * ∫ x, conj x ^ m * x ^ (j - m) * g x
  set f : ℕ → ℤ := fun m ↦ 2 * (m : ℤ) - j
  set c : ℤ → ℂ := fun k ↦ ∑ m ∈ (Finset.range (j + 1)).filter (fun m ↦ f m = k), a m
  refine ⟨c, fun k hk ↦ ?_, fun θ ↦ ?_⟩
  · obtain ⟨m, hm, hmk⟩ : ∃ m ∈ Finset.range (j + 1), f m = k := by
      by_contra hne
      push Not at hne
      apply hk
      refine Finset.sum_eq_zero fun m hm ↦ ?_
      rw [Finset.mem_filter] at hm
      exact absurd hm.2 (hne m hm.1)
    rw [Finset.mem_range] at hm
    subst hmk
    refine ⟨?_, ⟨m, by simp only [f]; ring⟩⟩
    rw [abs_le]
    simp only [f]
    constructor <;> omega
  · have hω : ‖exp (θ * I)‖ = 1 := norm_exp_ofReal_mul_I θ
    have hint : Integrable fun x : ℂ ↦ (⟪x, exp (θ * I)⟫ : ℝ) ^ j • g x := by
      have hc : Continuous fun x : ℂ ↦ (⟪x, exp (θ * I)⟫ : ℝ) ^ j := by fun_prop
      refine Integrable.mono' (hg.norm.const_mul (|R| ^ j))
        (hc.aestronglyMeasurable.smul hg.aestronglyMeasurable)
        (Eventually.of_forall fun x ↦ ?_)
      rcases hR x with h | h
      · rw [norm_smul, norm_pow, Real.norm_eq_abs]
        have h1 : |⟪x, exp (θ * I)⟫| ≤ |R| :=
          (abs_real_inner_le_norm _ _).trans (by rw [hω, mul_one]; exact h.trans (le_abs_self R))
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) h1 j) (norm_nonneg _)
      · simp [h]
    have hmaps : ∀ m ∈ Finset.range (j + 1), f m ∈ Finset.Icc (-(j : ℤ)) j := by
      intro m hm
      rw [Finset.mem_range] at hm
      rw [Finset.mem_Icc]
      simp only [f]
      constructor <;> omega
    calc ∫ p : ℝ, (p : ℂ) ^ j * radonTransform g (exp (θ * I)) p
        = ∫ p : ℝ, (p ^ j : ℝ) • radonTransform g (exp (θ * I)) p := by
          refine integral_congr_ae (Eventually.of_forall fun p ↦ ?_)
          dsimp only
          rw [Complex.real_smul]
          push_cast
          rfl
      _ = ∫ x : ℂ, (⟪x, exp (θ * I)⟫ : ℝ) ^ j • g x :=
          integral_pow_smul_radonTransform hω j hint
      _ = ∫ x : ℂ, ∑ m ∈ Finset.range (j + 1),
            ((Nat.choose j m : ℂ) / 2 ^ j * (conj x ^ m * x ^ (j - m) * g x)) *
              exp ((f m : ℂ) * θ * I) := by
          refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
          simp only
          rw [Complex.real_smul, ofReal_pow, ofReal_inner_exp, div_pow, add_pow, Finset.sum_div,
            Finset.sum_mul]
          refine Finset.sum_congr rfl fun m hm ↦ ?_
          rw [Finset.mem_range] at hm
          have hmj : m ≤ j := Nat.lt_succ_iff.mp hm
          rw [mul_pow, mul_pow]
          have := exp_pow_mul_exp_neg_pow θ hmj
          simp only [f]
          rw [← this]
          ring
      _ = ∑ m ∈ Finset.range (j + 1), a m * exp ((f m : ℂ) * θ * I) := by
          rw [integral_finsetSum _ fun m _ ↦ ((hbd m (j - m)).const_mul _).mul_const _]
          refine Finset.sum_congr rfl fun m _ ↦ ?_
          rw [integral_mul_const, integral_const_mul]
      _ = ∑ k ∈ Finset.Icc (-(j : ℤ)) j, c k * exp (k * θ * I) := by
          rw [← Finset.sum_fiberwise_of_maps_to hmaps]
          refine Finset.sum_congr rfl fun k _ ↦ ?_
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun m hm ↦ ?_
          rw [Finset.mem_filter] at hm
          rw [hm.2]

end LeanestEllipse
