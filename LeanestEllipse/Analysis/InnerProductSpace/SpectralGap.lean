import LeanestEllipse.Analysis.InnerProductSpace.NeutralSubspace
import LeanestEllipse.Analysis.InnerProductSpace.SchurComplement
import LeanestEllipse.LinearAlgebra.Matrix.HermitianFinTwo

/-!
# The spectral-gap theorem

Let `A` be a bounded operator on a nonzero complex Hilbert space and suppose that, for every
`θ : ℝ`, the spectrum of the self-adjoint operator `ℜ (exp (-θ i) • A)` lies in
`[a₁ θ, b₁ θ] \ (a₀ θ, b₀ θ)`, and that some `z : ℂ` satisfies
`a₀ θ < re (exp (-θ i) * z) < b₀ θ` for every `θ`.  Then there is a matrix
`C : Matrix (Fin 2) (Fin 2) ℂ` (of the form `!![z, β; γ, d]`) such that for every `θ` the two
eigenvalues `l θ < u θ` of `ℜ (exp (-θ i) • C)` satisfy
`a₁ θ ≤ l θ ≤ a₀ θ` and `b₀ θ ≤ u θ ≤ b₁ θ` ([Hägg, Theorem 10]).

The proof follows [Hägg]: a common neutral subspace `M` for the pencil
`ℜ (exp (-θ i) • (A - z))` (`exists_common_neutral_subspace`) gives `ℜ (exp (-θ i) • A)` the block
form `[[α_θ, Y_θ], [Y_θ*, D_θ]]` with respect to `M ⊕ Mᗮ`; the auxiliary matrix is built from a unit
vector `w ∈ Mᗮ`, and the Schur complement of `ℜ (exp (-θ i) • A) - t` along `M` compares the
eigenvalues of the auxiliary matrix with the spectral bands
(`IsSelfAdjoint.roots_mem_bands_of_map_eq_orthogonal`).

## Main results

* `IsSelfAdjoint.roots_mem_bands_of_map_eq_orthogonal`: the fixed-angle version, for a
  self-adjoint operator `T` such that `T - α` maps a closed subspace `K` onto `Kᗮ`.
* `exists_matrix_of_spectrum_gap'`: [Hägg, Theorem 10] with an explicit matrix `!![z, β; γ, d]`.
* `exists_matrix_of_spectrum_gap`: [Hägg, Theorem 10].

## References

* C. Hägg, *An ellipse criterion for exact nonuniqueness in the planar interior Radon problem*.
-/

noncomputable section

open Set
open scoped ComplexStarModule InnerProductSpace ComplexConjugate Matrix

/-! ### Elementary scalar facts -/

section Scalar

/-- The two roots `(a + d) / 2 ∓ √(((a - d) / 2) ^ 2 + r)` of `(t - a) * (t - d) = r` factor the
characteristic polynomial. -/
private theorem roots_factor (a d r t : ℝ) (hr : 0 ≤ r) :
    ((a + d) / 2 - √(((a - d) / 2) ^ 2 + r) - t) * ((a + d) / 2 + √(((a - d) / 2) ^ 2 + r) - t) =
      (a - t) * (d - t) - r := by
  have := Real.sq_sqrt (by positivity : 0 ≤ ((a - d) / 2) ^ 2 + r)
  nlinarith [this]

private theorem lower_root_lt (a d r : ℝ) (hr : 0 < r) :
    (a + d) / 2 - √(((a - d) / 2) ^ 2 + r) < a := by
  have h : |(a - d) / 2| < √(((a - d) / 2) ^ 2 + r) := by
    rw [Real.lt_sqrt (abs_nonneg _), sq_abs]
    linarith
  linarith [neg_abs_le ((a - d) / 2)]

private theorem lt_upper_root (a d r : ℝ) (hr : 0 < r) :
    a < (a + d) / 2 + √(((a - d) / 2) ^ 2 + r) := by
  have h : |(a - d) / 2| < √(((a - d) / 2) ^ 2 + r) := by
    rw [Real.lt_sqrt (abs_nonneg _), sq_abs]
    linarith
  linarith [le_abs_self ((a - d) / 2)]

/-- The sign analysis of the scalar Schur complement `q t = d - t - r / (a - t)`: if `q ≥ 0` below
`min b a` then the lower root is at least `b`; if `q ≤ 0` on `(b, a)` then the lower root is at
most `b`; symmetrically for the upper root. -/
private theorem roots_bounds (a d r : ℝ) (hr : 0 < r) {a₁ a₀ b₀ b₁ : ℝ}
    (h₁ : ∀ t, t < a₁ → t < a → 0 ≤ d - t - (a - t)⁻¹ * r)
    (h₂ : ∀ t, a₀ < t → t < a → d - t - (a - t)⁻¹ * r ≤ 0)
    (h₃ : ∀ t, a < t → t < b₀ → 0 ≤ d - t - (a - t)⁻¹ * r)
    (h₄ : ∀ t, b₁ < t → a < t → d - t - (a - t)⁻¹ * r ≤ 0) :
    a₁ ≤ (a + d) / 2 - √(((a - d) / 2) ^ 2 + r) ∧ (a + d) / 2 - √(((a - d) / 2) ^ 2 + r) ≤ a₀ ∧
      b₀ ≤ (a + d) / 2 + √(((a - d) / 2) ^ 2 + r) ∧
      (a + d) / 2 + √(((a - d) / 2) ^ 2 + r) ≤ b₁ := by
  set L := (a + d) / 2 - √(((a - d) / 2) ^ 2 + r) with hL
  set U := (a + d) / 2 + √(((a - d) / 2) ^ 2 + r) with hU
  have hLa : L < a := lower_root_lt a d r hr
  have haU : a < U := lt_upper_root a d r hr
  -- the scalar Schur complement is the characteristic polynomial divided by the pivot
  have hq : ∀ t, t ≠ a → d - t - (a - t)⁻¹ * r = (L - t) * (U - t) / (a - t) := by
    intro t ht
    have hat : a - t ≠ 0 := sub_ne_zero.mpr (Ne.symm ht)
    rw [hL, hU, roots_factor a d r t hr.le]
    field_simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · by_contra h
    push Not at h
    have hmin : L < min a₁ a := lt_min h hLa
    set t := (L + min a₁ a) / 2
    have hLt : L < t := by simp only [t]; linarith
    have htm : t < min a₁ a := by simp only [t]; linarith
    have hta : t < a := htm.trans_le (min_le_right _ _)
    have := h₁ t (htm.trans_le (min_le_left _ _)) hta
    rw [hq t hta.ne] at this
    have hneg : (L - t) * (U - t) / (a - t) < 0 :=
      div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (by linarith) (by linarith)) (by linarith)
    linarith
  · by_contra h
    push Not at h
    set t := (a₀ + L) / 2
    have hat : a₀ < t := by simp only [t]; linarith
    have htL : t < L := by simp only [t]; linarith
    have := h₂ t hat (htL.trans hLa)
    rw [hq t (htL.trans hLa).ne] at this
    have hpos : 0 < (L - t) * (U - t) / (a - t) :=
      div_pos (mul_pos (by linarith) (by linarith)) (by linarith)
    linarith
  · by_contra h
    push Not at h
    set t := (U + b₀) / 2
    have hUt : U < t := by simp only [t]; linarith
    have htb : t < b₀ := by simp only [t]; linarith
    have := h₃ t (haU.trans hUt) htb
    rw [hq t (haU.trans hUt).ne'] at this
    have hneg : (L - t) * (U - t) / (a - t) < 0 :=
      div_neg_of_pos_of_neg (mul_pos_of_neg_of_neg (by linarith) (by linarith)) (by linarith)
    linarith
  · by_contra h
    push Not at h
    have hmax : max b₁ a < U := max_lt h haU
    set t := (max b₁ a + U) / 2
    have hmt : max b₁ a < t := by simp only [t]; linarith
    have htU : t < U := by simp only [t]; linarith
    have hat : a < t := (le_max_right _ _).trans_lt hmt
    have := h₄ t ((le_max_left _ _).trans_lt hmt) hat
    rw [hq t hat.ne'] at this
    have hpos : 0 < (L - t) * (U - t) / (a - t) :=
      div_pos_of_neg_of_neg (mul_neg_of_neg_of_pos (by linarith) (by linarith)) (by linarith)
    linarith

/-- If `2 ‖ζ‖ ≤ r + s` with `r s ≥ 0`, then `ζ` is a product `β * γ` with
`‖β‖ ^ 2 + ‖γ‖ ^ 2 = r + s`. -/
theorem Complex.exists_mul_eq_of_two_norm_le_add {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) (ζ : ℂ)
    (hζ : 2 * ‖ζ‖ ≤ r + s) : ∃ β γ : ℂ, ‖β‖ ^ 2 + ‖γ‖ ^ 2 = r + s ∧ β * γ = ζ := by
  set t : ℝ := r + s with ht_def
  have ht : 0 ≤ t := by positivity
  by_cases hzero : ζ = 0
  · subst hzero
    refine ⟨(√t : ℂ), 0, ?_, by simp⟩
    simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg t), Real.sq_sqrt ht]
  · set n : ℝ := ‖ζ‖ with hn_def
    have hn : 0 < n := norm_pos_iff.mpr hzero
    have hnt : 2 * n ≤ t := hζ
    have hdisc : 0 ≤ t ^ 2 - 4 * n ^ 2 := by nlinarith
    set d : ℝ := √(t ^ 2 - 4 * n ^ 2) with hd_def
    have hd : 0 ≤ d := Real.sqrt_nonneg _
    have hdsq : d ^ 2 = t ^ 2 - 4 * n ^ 2 := Real.sq_sqrt hdisc
    set x : ℝ := (t + d) / 2 with hx_def
    have hx : 0 < x := by rw [hx_def]; linarith
    have hxroot : x ^ 2 - t * x + n ^ 2 = 0 := by rw [hx_def]; nlinarith [hdsq]
    set β : ℂ := (√x : ℂ) with hβ_def
    have hβnorm : ‖β‖ ^ 2 = x := by
      rw [hβ_def, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg x),
        Real.sq_sqrt hx.le]
    have hβne : β ≠ 0 := by
      intro hβ
      rw [hβ, norm_zero] at hβnorm
      linarith [hβnorm]
    refine ⟨β, ζ / β, ?_, mul_div_cancel₀ ζ hβne⟩
    rw [norm_div, div_pow, hβnorm, ← hn_def]
    field_simp
    nlinarith [hxroot]

/-- The off-diagonal identity of [Hägg, (4.6)]: if `‖β‖² + ‖γ‖² = ‖u‖² + ‖v‖²` and
`β * γ = ⟪v, u⟫`, then `‖conj p * β + p * conj γ‖ = ‖conj p • u + p • v‖` for every `p : ℂ`. -/
theorem norm_conj_mul_add_mul_conj_eq {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M]
    (p β γ : ℂ) (u v : M) (hsum : ‖β‖ ^ 2 + ‖γ‖ ^ 2 = ‖u‖ ^ 2 + ‖v‖ ^ 2)
    (hprod : β * γ = ⟪v, u⟫_ℂ) :
    ‖conj p * β + p * conj γ‖ = ‖conj p • u + p • v‖ := by
  have huv : ⟪u, v⟫_ℂ = conj (β * γ) := by rw [hprod, inner_conj_symm]
  have hsq : ‖conj p * β + p * conj γ‖ ^ 2 = ‖conj p • u + p • v‖ ^ 2 := by
    rw [@norm_add_sq ℂ, @norm_add_sq ℂ]
    simp only [norm_mul, Complex.norm_conj, norm_smul, inner_smul_left, inner_smul_right, huv,
      Complex.conj_conj, RCLike.inner_apply, map_mul]
    have hw : (‖p‖ * ‖β‖) ^ 2 + (‖p‖ * ‖γ‖) ^ 2 = (‖p‖ * ‖u‖) ^ 2 + (‖p‖ * ‖v‖) ^ 2 := by
      rw [mul_pow, mul_pow, mul_pow, mul_pow, ← mul_add, ← mul_add, hsum]
    have hc : RCLike.re (p * conj γ * (p * conj β)) =
        RCLike.re (p * (p * (conj β * conj γ))) := by
      congr 1
      ring
    rw [hc]
    linarith [hw]
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp hsq

end Scalar

/-! ### The spectral-gap theorem at a fixed angle -/

section FixedAngle

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in
private theorem algebraMap_real_eq_smul_one (t : ℝ) :
    algebraMap ℝ (E →L[ℂ] E) t = (t : ℂ) • 1 :=
  rfl

/-- **The spectral-gap theorem at a fixed angle** ([Hägg, proof of Theorem 10]).  Let `T` be a
self-adjoint operator with `spectrum ℝ T ⊆ [a₁, b₁] \ (a₀, b₀)`, let `α ∈ (a₀, b₀)` and let `K` be
a closed subspace which `T - α` maps onto `Kᗮ` (so that `K` is neutral for `T - α`).  For a unit
vector `w ∈ Kᗮ` put `δ = re ⟪T w, w⟫` and `ξ = ‖P_K (T w)‖`.  Then the two roots
`λ∓ = (α + δ) / 2 ∓ √(((α - δ) / 2) ^ 2 + ξ ^ 2)` of `(α - t) * (δ - t) = ξ ^ 2` (the eigenvalues of
the compression `[[α, ξ], [ξ, δ]]` of `T`) satisfy `λ₋ < α < λ₊`, `a₁ ≤ λ₋ ≤ a₀` and
`b₀ ≤ λ₊ ≤ b₁`. -/
theorem IsSelfAdjoint.roots_mem_bands_of_map_eq_orthogonal {T : E →L[ℂ] E} (hT : IsSelfAdjoint T)
    {K : Submodule ℂ E} [CompleteSpace K] {α : ℝ}
    (hmap : K.map (T - (α : ℂ) • 1 : E →L[ℂ] E).toLinearMap = Kᗮ) {a₁ a₀ b₀ b₁ : ℝ}
    (hspec : spectrum ℝ T ⊆ Icc a₁ b₁ \ Ioo a₀ b₀) (hα : α ∈ Ioo a₀ b₀) {w : E} (hw : w ∈ Kᗮ)
    (hw1 : ‖w‖ = 1) {δ ξ : ℝ} (hδ : δ = (⟪T w, w⟫_ℂ).re) (hξ : ξ = ‖K.starProjection (T w)‖) :
    (α + δ) / 2 - √(((α - δ) / 2) ^ 2 + ξ ^ 2) < α ∧
      α < (α + δ) / 2 + √(((α - δ) / 2) ^ 2 + ξ ^ 2) ∧
      a₁ ≤ (α + δ) / 2 - √(((α - δ) / 2) ^ 2 + ξ ^ 2) ∧
      (α + δ) / 2 - √(((α - δ) / 2) ^ 2 + ξ ^ 2) ≤ a₀ ∧
      b₀ ≤ (α + δ) / 2 + √(((α - δ) / 2) ^ 2 + ξ ^ 2) ∧
      (α + δ) / 2 + √(((α - δ) / 2) ^ 2 + ξ ^ 2) ≤ b₁ := by
  have happ : ∀ (t : ℝ) (x : E), (T - (t : ℂ) • 1) x = T x - (t : ℂ) • x := fun t x ↦ by simp
  -- the compression of `T` to `K` is `α`
  have hK : ∀ x ∈ K, K.starProjection (T x) = (α : ℂ) • x := by
    intro x hx
    have hmem : (T - (α : ℂ) • 1) x ∈ Kᗮ := by
      rw [← hmap]
      exact Submodule.mem_map_of_mem hx
    have h0 := (K.starProjection_apply_eq_zero_iff).mpr hmem
    rwa [happ, map_sub, map_smul, K.starProjection_eq_self_iff.mpr hx, sub_eq_zero] at h0
  have hKt : ∀ t : ℝ, ∀ x ∈ K,
      K.starProjection ((T - (t : ℂ) • 1) x) = ((α : ℂ) - t) • x := by
    intro t x hx
    rw [happ, map_sub, map_smul, hK x hx, K.starProjection_eq_self_iff.mpr hx, sub_smul]
  -- `P_K T` is bounded below on `Kᗮ`
  obtain ⟨κ, hκ, hY⟩ : ∃ κ > 0, ∀ n : Kᗮ, κ * ‖(n : E)‖ ≤ ‖K.starProjection (T n)‖ := by
    have hG : IsSelfAdjoint (T - (α : ℂ) • 1) :=
      hT.sub ((isSelfAdjoint_iff.mpr (Complex.conj_ofReal α)).smul (IsSelfAdjoint.one _))
    obtain ⟨κ, hκ, h⟩ := Submodule.exists_pos_mul_norm_le_norm_starProjection_apply hG hmap
    refine ⟨κ, hκ, fun n ↦ ?_⟩
    have hn : K.starProjection ((T - (α : ℂ) • 1) n) = K.starProjection (T n) := by
      rw [happ, map_sub, map_smul, (K.starProjection_apply_eq_zero_iff).mpr n.2, smul_zero,
        sub_zero]
    have := h n n.2
    rwa [hn] at this
  -- the shifts `T - t` with `t` in the gap are invertible
  have hunit : ∀ t ∈ Ioo a₀ b₀, IsUnit (T - (t : ℂ) • 1) := by
    intro t ht
    have ht' : t ∉ spectrum ℝ T := fun h ↦ (hspec h).2 ht
    rw [spectrum.notMem_iff, algebraMap_real_eq_smul_one] at ht'
    exact IsUnit.sub_iff.mp ht'
  -- the Schur complements
  set S : ℝ → (Kᗮ →L[ℂ] Kᗮ) := fun t ↦ K.schurComplement (T - (t : ℂ) • 1) ((α : ℂ) - t)
    with hS
  have hc : ∀ t : ℝ, t ≠ α → (α : ℂ) - t ≠ 0 := fun t ht ↦ by
    rw [← Complex.ofReal_sub]
    exact Complex.ofReal_ne_zero.mpr (sub_ne_zero.mpr (Ne.symm ht))
  have hSunit : ∀ t ∈ Ioo a₀ b₀, t ≠ α → IsUnit (S t) := fun t ht hta ↦
    (Submodule.isUnit_schurComplement_iff (hc t hta) (hKt t)).mpr (hunit t ht)
  have hSsa : ∀ t, IsSelfAdjoint (S t) := fun t ↦
    Submodule.isSelfAdjoint_schurComplement_sub_ofReal_smul_one hT α t
  have hScont : ContinuousOn S {t | t ≠ α} :=
    Submodule.continuousOn_schurComplement_sub_ofReal_smul_one T α
  -- the unit vector as an element of `Kᗮ`
  obtain ⟨n₀, hn₀w⟩ : ∃ n₀ : Kᗮ, (n₀ : E) = w := ⟨⟨w, hw⟩, rfl⟩
  have hn₀ : n₀ ≠ 0 := fun h ↦ by
    rw [h, ZeroMemClass.coe_zero] at hn₀w
    rw [← hn₀w, norm_zero] at hw1
    exact zero_ne_one hw1
  have : Nontrivial Kᗮ := ⟨⟨n₀, 0, hn₀⟩⟩
  -- signs of the Schur complements in the gap, propagated from the pole
  obtain ⟨ε, hε, hright, hleft⟩ := Submodule.exists_pos_schurComplement_sign hT α hκ hY
  have hposGap : ∀ t ∈ Ioo α b₀, IsStrictlyPositive (S t) := by
    have hm : 0 < min (b₀ - α) ε := lt_min (sub_pos.mpr hα.2) hε
    have hm₁ := min_le_left (b₀ - α) ε
    have hm₂ := min_le_right (b₀ - α) ε
    have ht₀ : α + min (b₀ - α) ε / 2 ∈ Ioo α b₀ := ⟨by linarith, by linarith⟩
    have h₀ : IsStrictlyPositive (S (α + min (b₀ - α) ε / 2)) :=
      (hSunit _ ⟨by linarith [hα.1], by linarith⟩ (by linarith)).isStrictlyPositive
        (hright (α + min (b₀ - α) ε / 2) (by linarith) (by linarith))
    exact isPreconnected_Ioo.isStrictlyPositive_of_continuousOn (f := S)
      (hScont.mono fun t (ht : t ∈ Ioo α b₀) ↦ ne_of_gt ht.1) (fun t _ ↦ hSsa t)
      (fun t (ht : t ∈ Ioo α b₀) ↦ hSunit t ⟨hα.1.trans ht.1, ht.2⟩ ht.1.ne') ht₀ h₀
  have hnegGap : ∀ t ∈ Ioo a₀ α, IsStrictlyPositive (-S t) := by
    have hm : 0 < min (α - a₀) ε := lt_min (sub_pos.mpr hα.1) hε
    have hm₁ := min_le_left (α - a₀) ε
    have hm₂ := min_le_right (α - a₀) ε
    have ht₀ : α - min (α - a₀) ε / 2 ∈ Ioo a₀ α := ⟨by linarith, by linarith⟩
    have h₀ : IsStrictlyPositive (-S (α - min (α - a₀) ε / 2)) :=
      (hSunit _ ⟨by linarith, by linarith [hα.2]⟩ (by linarith)).neg.isStrictlyPositive
        (hleft (α - min (α - a₀) ε / 2) (by linarith) (by linarith))
    exact isPreconnected_Ioo.isStrictlyPositive_of_continuousOn (f := fun t ↦ -S t)
      ((hScont.mono fun t (ht : t ∈ Ioo a₀ α) ↦ ne_of_lt ht.2).neg) (fun t _ ↦ (hSsa t).neg)
      (fun t (ht : t ∈ Ioo a₀ α) ↦ (hSunit t ⟨ht.1, ht.2.trans hα.2⟩ ht.2.ne).neg) ht₀ h₀
  -- the scalar Schur complement
  have hq : ∀ t : ℝ, (⟪(S t n₀ : E), (n₀ : E)⟫_ℂ).re = δ - t - (α - t)⁻¹ * ξ ^ 2 := by
    intro t
    have h := Submodule.re_inner_schurComplement_sub_ofReal_smul_one_apply_self hT α t n₀
    simp only [RCLike.re_to_complex] at h
    refine h.trans ?_
    rw [hn₀w, hδ, hξ, hw1]
    ring
  have hre : ∀ t : ℝ, t ≠ α → (⟪(S t n₀ : E), (n₀ : E)⟫_ℂ).re =
      (⟪(T - (t : ℂ) • 1) ((n₀ : E) - ((α : ℂ) - t)⁻¹ • K.starProjection ((T - (t : ℂ) • 1) n₀)),
        (n₀ : E) - ((α : ℂ) - t)⁻¹ • K.starProjection ((T - (t : ℂ) • 1) n₀)⟫_ℂ).re :=
    fun t ht ↦
      congrArg Complex.re (Submodule.inner_schurComplement_apply_self (hc t ht) (hKt t) n₀)
  have hξpos : 0 < ξ ^ 2 := by
    have := hY n₀
    rw [hn₀w, hw1, mul_one, ← hξ] at this
    exact pow_pos (hκ.trans_le this) 2
  have h₁ : ∀ t, t < a₁ → t < α → 0 ≤ δ - t - (α - t)⁻¹ * ξ ^ 2 := by
    intro t ht₁ htα
    rw [← hq, hre t htα.ne]
    have hpos : 0 ≤ T - (t : ℂ) • 1 := by
      rw [← algebraMap_real_eq_smul_one, sub_nonneg]
      exact algebraMap_le_of_le_spectrum (fun x hx ↦ ht₁.le.trans (hspec hx).1.1) hT
    exact (ContinuousLinearMap.nonneg_iff_isPositive.mp hpos).re_inner_nonneg_left _
  have h₄ : ∀ t, b₁ < t → α < t → δ - t - (α - t)⁻¹ * ξ ^ 2 ≤ 0 := by
    intro t ht₁ htα
    rw [← hq, hre t htα.ne']
    have hpos : 0 ≤ (t : ℂ) • 1 - T := by
      rw [← algebraMap_real_eq_smul_one, sub_nonneg]
      exact le_algebraMap_of_spectrum_le (fun x hx ↦ (hspec hx).1.2.trans ht₁.le) hT
    have := (ContinuousLinearMap.nonneg_iff_isPositive.mp hpos).re_inner_nonneg_left
      ((n₀ : E) - ((α : ℂ) - t)⁻¹ • K.starProjection ((T - (t : ℂ) • 1) n₀))
    rw [← neg_sub, _root_.neg_apply, inner_neg_left, map_neg] at this
    simpa using this
  have h₂ : ∀ t, a₀ < t → t < α → δ - t - (α - t)⁻¹ * ξ ^ 2 ≤ 0 := by
    intro t ht₀ htα
    rw [← hq]
    have := (ContinuousLinearMap.nonneg_iff_isPositive.mp (hnegGap t ⟨ht₀, htα⟩).nonneg
      ).re_inner_nonneg_left n₀
    rw [_root_.neg_apply, inner_neg_left, map_neg, Submodule.coe_inner] at this
    simpa using this
  have h₃ : ∀ t, α < t → t < b₀ → 0 ≤ δ - t - (α - t)⁻¹ * ξ ^ 2 := by
    intro t htα ht₀
    rw [← hq]
    have := (ContinuousLinearMap.nonneg_iff_isPositive.mp (hposGap t ⟨htα, ht₀⟩).nonneg
      ).re_inner_nonneg_left n₀
    rw [Submodule.coe_inner] at this
    simpa using this
  exact ⟨lower_root_lt α δ _ hξpos, lt_upper_root α δ _ hξpos,
    roots_bounds α δ (ξ ^ 2) hξpos h₁ h₂ h₃ h₄⟩

end FixedAngle

/-! ### The spectral-gap theorem -/

section SpectralGap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private theorem exp_neg_mul_I_re (θ : ℝ) : (Complex.exp (-(θ * Complex.I))).re = Real.cos θ := by
  rw [← neg_mul, ← Complex.ofReal_neg, Complex.exp_ofReal_mul_I_re, Real.cos_neg]

private theorem exp_neg_mul_I_im (θ : ℝ) : (Complex.exp (-(θ * Complex.I))).im = -Real.sin θ := by
  rw [← neg_mul, ← Complex.ofReal_neg, Complex.exp_ofReal_mul_I_im, Real.sin_neg]

/-- The rotated real part of `A - z` is the cosine–sine pencil of the real and imaginary parts of
`A - z`: `cos θ • ℜ (A - z) + sin θ • ℑ (A - z) = ℜ (exp (-θ i) • A) - re (exp (-θ i) * z)`. -/
theorem cos_smul_realPart_add_sin_smul_imaginaryPart (A : H →L[ℂ] H) (z : ℂ) (θ : ℝ) :
    Real.cos θ • (ℜ (A - z • 1) : H →L[ℂ] H) + Real.sin θ • (ℑ (A - z • 1) : H →L[ℂ] H) =
      (ℜ (Complex.exp (-(θ * Complex.I)) • A) : H →L[ℂ] H) -
        (((Complex.exp (-(θ * Complex.I)) * z).re : ℝ) : ℂ) • 1 := by
  set w := Complex.exp (-(θ * Complex.I)) with hw
  have h1 : (ℜ (w • (A - z • 1)) : H →L[ℂ] H) =
      Real.cos θ • (ℜ (A - z • 1) : H →L[ℂ] H) + Real.sin θ • (ℑ (A - z • 1) : H →L[ℂ] H) := by
    rw [realPart_smul, hw, exp_neg_mul_I_re, exp_neg_mul_I_im]
    simp only [AddMemClass.coe_add, selfAdjoint.val_smul, neg_smul, sub_neg_eq_add]
  have h2 : (ℜ (w • (A - z • 1)) : H →L[ℂ] H) =
      (ℜ (w • A) : H →L[ℂ] H) - (((w * z).re : ℝ) : ℂ) • 1 := by
    rw [smul_sub, smul_smul, map_sub, AddSubgroupClass.coe_sub, realPart_smul (w * z),
      AddSubgroupClass.coe_sub, selfAdjoint.val_smul, selfAdjoint.val_smul, realPart_one,
      (IsSelfAdjoint.one (H →L[ℂ] H)).imaginaryPart, ZeroMemClass.coe_zero, smul_zero, sub_zero,
      selfAdjoint.val_one, Complex.coe_smul]
  rw [← h1, h2]

private theorem realPart_smul_apply (A : H →L[ℂ] H) (w : ℂ) (x : H) :
    (ℜ (w • A) : H →L[ℂ] H) x = (2 : ℂ)⁻¹ • (w • A x + star w • (star A) x) := by
  rw [realPart_apply_coe, star_smul, ← Complex.coe_smul]
  simp

private theorem pair_eq_pair_of_lt {l u a b : ℝ} (hlu : l < u) (hab : a ≤ b)
    (h : ({l, u} : Set ℝ) = {a, b}) : l = a ∧ u = b := by
  have hl : l ∈ ({a, b} : Set ℝ) := h ▸ Set.mem_insert l {u}
  have hu : u ∈ ({a, b} : Set ℝ) := h ▸ Set.mem_insert_of_mem l rfl
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hl hu
  rcases hl with hl | hl <;> rcases hu with hu | hu
  · exfalso; linarith
  · exact ⟨hl, hu⟩
  · exfalso; linarith
  · exfalso; linarith

/-- **The spectral-gap theorem** [Hägg, Theorem 10], explicit form.  Let `A` be a bounded operator
on a nonzero complex Hilbert space such that, for every `θ`, the spectrum of
`ℜ (exp (-θ i) • A)` lies in `[a₁ θ, b₁ θ] \ (a₀ θ, b₀ θ)`, and let `z : ℂ` satisfy
`re (exp (-θ i) * z) ∈ (a₀ θ, b₀ θ)` for every `θ`.  Then there are `β γ d : ℂ` such that for every
`θ` the two eigenvalues `l < u` of `ℜ (exp (-θ i) • !![z, β; γ, d])` satisfy
`a₁ θ ≤ l ≤ a₀ θ`, `b₀ θ ≤ u ≤ b₁ θ` and `l < re (exp (-θ i) * z) < u`. -/
theorem exists_matrix_of_spectrum_gap' [Nontrivial H] (A : H →L[ℂ] H) (a₁ a₀ b₀ b₁ : ℝ → ℝ)
    (hband : ∀ θ : ℝ, spectrum ℝ (ℜ (Complex.exp (-(θ * Complex.I)) • A) : H →L[ℂ] H) ⊆
      Set.Icc (a₁ θ) (b₁ θ) \ Set.Ioo (a₀ θ) (b₀ θ))
    (z : ℂ) (hz : ∀ θ : ℝ, (Complex.exp (-(θ * Complex.I)) * z).re ∈ Set.Ioo (a₀ θ) (b₀ θ)) :
    ∃ β γ d : ℂ, ∀ θ : ℝ, ∃ l u : ℝ,
      spectrum ℝ (ℜ (Complex.exp (-(θ * Complex.I)) • !![z, β; γ, d]) :
        Matrix (Fin 2) (Fin 2) ℂ) = {l, u} ∧
      l < (Complex.exp (-(θ * Complex.I)) * z).re ∧ (Complex.exp (-(θ * Complex.I)) * z).re < u ∧
      a₁ θ ≤ l ∧ l ≤ a₀ θ ∧ b₀ θ ≤ u ∧ u ≤ b₁ θ := by
  -- the rotated real parts and the centering scalars
  have hpencil := cos_smul_realPart_add_sin_smul_imaginaryPart A z
  have hunit : ∀ θ : ℝ, IsUnit (Real.cos θ • (ℜ (A - z • 1) : H →L[ℂ] H) +
      Real.sin θ • (ℑ (A - z • 1) : H →L[ℂ] H)) := by
    intro θ
    rw [hpencil]
    have hnot : (Complex.exp (-(θ * Complex.I)) * z).re ∉
        spectrum ℝ (ℜ (Complex.exp (-(θ * Complex.I)) • A) : H →L[ℂ] H) :=
      fun h ↦ (hband θ h).2 (hz θ)
    rw [spectrum.notMem_iff] at hnot
    exact IsUnit.sub_iff.mp hnot
  -- the common neutral subspace
  obtain ⟨M, hMc, hM0, hM⟩ := exists_common_neutral_subspace (ℜ (A - z • 1)).2 (ℑ (A - z • 1)).2
    hunit
  have : CompleteSpace M := hMc.completeSpace_coe
  have hmap : ∀ θ : ℝ, M.map ((ℜ (Complex.exp (-(θ * Complex.I)) • A) : H →L[ℂ] H) -
      (((Complex.exp (-(θ * Complex.I)) * z).re : ℝ) : ℂ) • 1 : H →L[ℂ] H).toLinearMap = Mᗮ := by
    intro θ
    rw [← hpencil]
    exact (hM θ).2
  -- a unit vector in `Mᗮ`
  obtain ⟨w, hw, hw1⟩ : ∃ w ∈ Mᗮ, ‖w‖ = 1 := by
    have hne : Mᗮ ≠ ⊥ := by
      intro hbot
      apply hM0
      rw [Submodule.eq_bot_iff]
      intro x hx
      have hGx : (Real.cos 0 • (ℜ (A - z • 1) : H →L[ℂ] H) +
          Real.sin 0 • (ℑ (A - z • 1) : H →L[ℂ] H)) x ∈ Mᗮ := by
        rw [← (hM 0).2]
        exact Submodule.mem_map_of_mem hx
      rw [hbot, Submodule.mem_bot] at hGx
      exact (ContinuousLinearMap.isUnit_iff_bijective.mp (hunit 0)).1 (by rw [hGx, map_zero])
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    refine ⟨((‖v‖⁻¹ : ℝ) : ℂ) • v, Submodule.smul_mem _ _ hv, ?_⟩
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_norm,
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv0)]
  -- the entries of the auxiliary matrix
  set u : H := M.starProjection (A w) with hu
  set v : H := M.starProjection ((star A) w) with hv
  have hcs : 2 * ‖⟪v, u⟫_ℂ‖ ≤ ‖u‖ ^ 2 + ‖v‖ ^ 2 := by
    have := norm_inner_le_norm (𝕜 := ℂ) v u
    nlinarith [sq_nonneg (‖u‖ - ‖v‖), norm_nonneg u, norm_nonneg v]
  obtain ⟨β, γ, hsum, hprod⟩ :=
    Complex.exists_mul_eq_of_two_norm_le_add (sq_nonneg ‖u‖) (sq_nonneg ‖v‖) ⟪v, u⟫_ℂ hcs
  set d : ℂ := ⟪w, A w⟫_ℂ with hd
  refine ⟨β, γ, d, fun θ ↦ ?_⟩
  set e := Complex.exp (-(θ * Complex.I)) with he
  set T : H →L[ℂ] H := (ℜ (e • A) : H →L[ℂ] H) with hT
  have hTw : T w = (2 : ℂ)⁻¹ • (e • A w + star e • (star A) w) := realPart_smul_apply A e w
  have hδ : (⟪T w, w⟫_ℂ).re = (e * d).re := by
    have h1 : ⟪(star A) w, w⟫_ℂ = d := by
      rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]
    have h2 : ⟪A w, w⟫_ℂ = star d := by rw [hd, ← inner_conj_symm]; rfl
    rw [hTw, inner_smul_left, inner_add_left, inner_smul_left, inner_smul_left, h1, h2]
    simp [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im]
    ring
  have hξ : ‖M.starProjection (T w)‖ = ‖(2 : ℂ)⁻¹ * (e * β + star e * star γ)‖ := by
    rw [hTw, map_smul, map_add, map_smul, map_smul, ← hu, ← hv, norm_smul, norm_mul]
    congr 1
    have := norm_conj_mul_add_mul_conj_eq (star e) β γ u v hsum hprod
    simp only [Complex.star_def, Complex.conj_conj] at this ⊢
    exact this.symm
  obtain ⟨hL, hU, h1, h2, h3, h4⟩ := (ℜ (e • A)).2.roots_mem_bands_of_map_eq_orthogonal
    (hmap θ) (hband θ) (hz θ) hw hw1 rfl rfl
  set X := (ℜ (e • !![z, β; γ, d]) : Matrix (Fin 2) (Fin 2) ℂ) with hX
  have hX00 : RCLike.re (X 0 0) = (e * z).re := by
    rw [hX, Matrix.realPart_apply]
    simp [Complex.mul_re]
    ring
  have hX11 : RCLike.re (X 1 1) = (⟪T w, w⟫_ℂ).re := by
    rw [hδ, hX, Matrix.realPart_apply]
    simp [Complex.mul_re]
    ring
  have hX01 : ‖X 0 1‖ = ‖M.starProjection (T w)‖ := by
    rw [hξ, hX, Matrix.realPart_apply]
    simp [star_mul']
  refine ⟨_, _, (Matrix.isHermitian_realPart _).spectrum_real_fin_two, ?_⟩
  rw [hX00, hX11, hX01]
  exact ⟨hL, hU, h1, h2, h3, h4⟩

/-- **The spectral-gap theorem** [Hägg, Theorem 10].  Let `A` be a bounded operator on a nonzero
complex Hilbert space such that, for every `θ`, the spectrum of `ℜ (exp (-θ i) • A)` lies in
`[a₁ θ, b₁ θ] \ (a₀ θ, b₀ θ)`, and let `z : ℂ` satisfy `re (exp (-θ i) * z) ∈ (a₀ θ, b₀ θ)` for
every `θ`.  Then there is a complex `2 × 2` matrix `C` such that for every `θ` the Hermitian matrix
`ℜ (exp (-θ i) • C)` has two eigenvalues `l θ < u θ` with `a₁ θ ≤ l θ ≤ a₀ θ` and
`b₀ θ ≤ u θ ≤ b₁ θ`.  The matrix can be taken of the form `!![z, β; γ, d]`, see
`exists_matrix_of_spectrum_gap'`. -/
theorem exists_matrix_of_spectrum_gap [Nontrivial H] (A : H →L[ℂ] H) (a₁ a₀ b₀ b₁ : ℝ → ℝ)
    (hband : ∀ θ : ℝ, spectrum ℝ (ℜ (Complex.exp (-(θ * Complex.I)) • A) : H →L[ℂ] H) ⊆
      Set.Icc (a₁ θ) (b₁ θ) \ Set.Ioo (a₀ θ) (b₀ θ))
    (z : ℂ) (hz : ∀ θ : ℝ, (Complex.exp (-(θ * Complex.I)) * z).re ∈ Set.Ioo (a₀ θ) (b₀ θ)) :
    ∃ C : Matrix (Fin 2) (Fin 2) ℂ, ∃ l u : ℝ → ℝ, ∀ θ : ℝ,
      l θ < u θ ∧
      spectrum ℝ (ℜ (Complex.exp (-(θ * Complex.I)) • C) : Matrix (Fin 2) (Fin 2) ℂ) =
        {l θ, u θ} ∧
      a₁ θ ≤ l θ ∧ l θ ≤ a₀ θ ∧ b₀ θ ≤ u θ ∧ u θ ≤ b₁ θ := by
  obtain ⟨β, γ, d, h⟩ := exists_matrix_of_spectrum_gap' A a₁ a₀ b₀ b₁ hband z hz
  choose l u hlu using h
  exact ⟨!![z, β; γ, d], l, u, fun θ ↦
    ⟨(hlu θ).2.1.trans (hlu θ).2.2.1, (hlu θ).1, (hlu θ).2.2.2⟩⟩

/-- [Hägg, Theorem 10 and Lemma 9]: under the hypotheses of the spectral-gap theorem there is a
nondegenerate ellipse `c + Q^{1/2} (closed unit disk)` (i.e. `c : Fin 2 → ℝ` and a positive definite
`Q`) whose projection endpoints `c ⬝ᵥ ω_θ ∓ √(ω_θ ⬝ᵥ Q *ᵥ ω_θ)`, `ω_θ = ![cos θ, sin θ]`, lie in
`[a₁ θ, a₀ θ]` and `[b₀ θ, b₁ θ]` respectively. -/
theorem exists_center_shape_of_spectrum_gap [Nontrivial H] (A : H →L[ℂ] H) (a₁ a₀ b₀ b₁ : ℝ → ℝ)
    (hband : ∀ θ : ℝ, spectrum ℝ (ℜ (Complex.exp (-(θ * Complex.I)) • A) : H →L[ℂ] H) ⊆
      Set.Icc (a₁ θ) (b₁ θ) \ Set.Ioo (a₀ θ) (b₀ θ))
    (z : ℂ) (hz : ∀ θ : ℝ, (Complex.exp (-(θ * Complex.I)) * z).re ∈ Set.Ioo (a₀ θ) (b₀ θ)) :
    ∃ (c : Fin 2 → ℝ) (Q : Matrix (Fin 2) (Fin 2) ℝ), Q.PosDef ∧ ∀ θ : ℝ,
      a₁ θ ≤ c ⬝ᵥ ![Real.cos θ, Real.sin θ] -
          √(![Real.cos θ, Real.sin θ] ⬝ᵥ (Q *ᵥ ![Real.cos θ, Real.sin θ])) ∧
      c ⬝ᵥ ![Real.cos θ, Real.sin θ] -
          √(![Real.cos θ, Real.sin θ] ⬝ᵥ (Q *ᵥ ![Real.cos θ, Real.sin θ])) ≤ a₀ θ ∧
      b₀ θ ≤ c ⬝ᵥ ![Real.cos θ, Real.sin θ] +
          √(![Real.cos θ, Real.sin θ] ⬝ᵥ (Q *ᵥ ![Real.cos θ, Real.sin θ])) ∧
      c ⬝ᵥ ![Real.cos θ, Real.sin θ] +
          √(![Real.cos θ, Real.sin θ] ⬝ᵥ (Q *ᵥ ![Real.cos θ, Real.sin θ])) ≤ b₁ θ := by
  obtain ⟨C, l, u, h⟩ := exists_matrix_of_spectrum_gap A a₁ a₀ b₀ b₁ hband z hz
  have heq : ∀ θ : ℝ, l θ = Matrix.ellipseCenter C ⬝ᵥ ![Real.cos θ, Real.sin θ] -
        √(![Real.cos θ, Real.sin θ] ⬝ᵥ (Matrix.ellipseShape C *ᵥ ![Real.cos θ, Real.sin θ])) ∧
      u θ = Matrix.ellipseCenter C ⬝ᵥ ![Real.cos θ, Real.sin θ] +
        √(![Real.cos θ, Real.sin θ] ⬝ᵥ (Matrix.ellipseShape C *ᵥ ![Real.cos θ, Real.sin θ])) := by
    intro θ
    have hs := Real.sqrt_nonneg
      (![Real.cos θ, Real.sin θ] ⬝ᵥ (Matrix.ellipseShape C *ᵥ ![Real.cos θ, Real.sin θ]))
    refine pair_eq_pair_of_lt (h θ).1 (by linarith) ?_
    rw [← (h θ).2.1, Matrix.spectrum_realPart_exp_smul_fin_two]
  refine ⟨Matrix.ellipseCenter C, Matrix.ellipseShape C,
    Matrix.posDef_ellipseShape_of_nontrivial fun θ ↦ ?_, fun θ ↦ ?_⟩
  · rw [(h θ).2.1]
    exact ⟨l θ, Set.mem_insert _ _, u θ, Set.mem_insert_of_mem _ rfl, (h θ).1.ne⟩
  · rw [← (heq θ).1, ← (heq θ).2]
    exact (h θ).2.2

end SpectralGap
