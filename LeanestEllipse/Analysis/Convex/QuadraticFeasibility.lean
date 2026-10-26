import LeanestEllipse.Analysis.Convex.Ellipsoid
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Basic.Real.Pointwise

/-!
# Ellipsoid sandwiches as a quadratic feasibility problem

Let `D₀ ⊆ D` be sets in a finite dimensional real inner product space `E`, with `D₀` nonempty
and open and `D` open, convex and bounded.  [Hägg, Remark 3] observes that the existence of an
ellipsoid `𝓔` with `closure D₀ ⊆ 𝓔 ⊆ D` is a convex feasibility problem in the center `c` and a
self-adjoint operator `B` (five real variables in the plane): for the monic quadratic

  `F_ω(p) = p² - 2⟪c, ω⟫ p + ⟪B ω, ω⟫`

one requires, for every unit vector `ω`,

  `F_ω(a_D(ω)) > 0`, `F_ω(a_{D₀}(ω)) ≤ 0`, `F_ω(b_{D₀}(ω)) ≤ 0`, `F_ω(b_D(ω)) > 0`,

where `a_K = lowerSupportFunction K` and `b_K = supportFunction K` are the projection endpoints.
For an ellipsoid with center `c` and shape `Q` one takes `B = c cᵀ - Q`; then `F_ω` vanishes at
the two projection endpoints `⟪c, ω⟫ ∓ √⟪Q ω, ω⟫` of the ellipsoid, and the conditions are the
*interval sandwich* `[a_{D₀}, b_{D₀}] ⊆ [a_𝓔, b_𝓔] ⊆ (a_D, b_D)`.

## Main definitions and results

* `feasibilityQuadratic c B ω p`: the monic quadratic `F_ω(p)`.
* `exists_ellipsoid_iff_quadratic_feasibility`: [Hägg, Remark 3].
* `exists_ellipsoid_of_quadratic_feasibility`: the converse direction, with the ellipsoid
  (center `c`, shape `c cᵀ - B`) made explicit.
* `Ellipsoid.quadratic_feasibility`, `Ellipsoid.interval_sandwich`,
  `Ellipsoid.projection_endpoints_sandwich`: the direct direction (in any real Hilbert space).
* `isLinearMap_feasibilityQuadratic_sub_sq`, `convex_setOf_quadratic_feasibility`: for fixed
  `ω` and `p`, `F_ω(p) - p²` is linear in `(c, B)`, so the feasible set is convex.

Along the way we prove some general facts about support functions: positive homogeneity
(`supportFunction_smul`), the strict inclusion criterion for open convex sets
(`subset_of_forall_supportFunction_lt`), and attainment of the support function of an ellipsoid
(`Ellipsoid.exists_inner_eq_supportFunction`).

## References

* C. Hägg, *An ellipse criterion for exact nonuniqueness in the planar interior Radon problem*.
-/

open Set Metric Bornology InnerProductSpace
open scoped RealInnerProductSpace Pointwise

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ### Auxiliary facts on support functions -/

section SupportFunction

/-- Support functions are positively homogeneous. -/
theorem supportFunction_smul (K : Set E) {t : ℝ} (ht : 0 ≤ t) (ω : E) :
    supportFunction K (t • ω) = t * supportFunction K ω := by
  have h : (fun x ↦ ⟪x, t • ω⟫) '' K = t • ((fun x ↦ ⟪x, ω⟫) '' K) := by
    rw [← Set.image_smul, Set.image_image]
    simp_rw [real_inner_smul_right, smul_eq_mul]
  rw [supportFunction, h, Real.sSup_smul_of_nonneg ht, smul_eq_mul, supportFunction]

/-- Lower support functions are positively homogeneous. -/
theorem lowerSupportFunction_smul (K : Set E) {t : ℝ} (ht : 0 ≤ t) (ω : E) :
    lowerSupportFunction K (t • ω) = t * lowerSupportFunction K ω := by
  rw [lowerSupportFunction_eq_neg_supportFunction_neg, ← smul_neg, supportFunction_smul K ht,
    lowerSupportFunction_eq_neg_supportFunction_neg, mul_neg]

/-- By homogeneity, support functions may be compared on unit vectors only. -/
theorem supportFunction_le_of_forall_norm_eq_one {K L : Set E}
    (h : ∀ ω : E, ‖ω‖ = 1 → supportFunction K ω ≤ supportFunction L ω) (ω : E) :
    supportFunction K ω ≤ supportFunction L ω := by
  rcases eq_or_ne ω 0 with rfl | hω
  · simp
  have hn : 0 < ‖ω‖ := norm_pos_iff.mpr hω
  have hω' : ω = ‖ω‖ • (‖ω‖⁻¹ • ω) := by rw [smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
  rw [hω', supportFunction_smul K hn.le, supportFunction_smul L hn.le]
  exact mul_le_mul_of_nonneg_left (h _ (norm_smul_inv_norm hω)) hn.le

/-- **Strict support-function criterion.**  Let `D` be a nonempty open convex set in a real
Hilbert space.  If a bounded set `K` satisfies `b_K(ω) < b_D(ω)` for every unit vector `ω`, then
`K ⊆ D`: at a point of `K \ D`, a supporting hyperplane of `D` would give a unit vector `ω`
with `b_D(ω) ≤ b_K(ω)`. -/
theorem subset_of_forall_supportFunction_lt [CompleteSpace E] {K D : Set E} (hK : IsBounded K)
    (hDne : D.Nonempty) (hDo : IsOpen D) (hDc : Convex ℝ D)
    (h : ∀ ω : E, ‖ω‖ = 1 → supportFunction K ω < supportFunction D ω) : K ⊆ D := by
  intro x hx
  by_contra hxD
  obtain ⟨f, hf⟩ := geometric_hahn_banach_open_point hDc hDo hxD
  set v : E := (InnerProductSpace.toDual ℝ E).symm f
  have hv : ∀ y, f y = ⟪y, v⟫ := fun y ↦ by
    rw [real_inner_comm, InnerProductSpace.toDual_symm_apply]
  obtain ⟨y, hy⟩ := hDne
  have hv0 : v ≠ 0 := by
    intro hv0
    have := hf y hy
    rw [hv, hv, hv0, inner_zero_right, inner_zero_right] at this
    exact lt_irrefl _ this
  have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv0
  have hle : ∀ z ∈ D, ⟪z, ‖v‖⁻¹ • v⟫ ≤ ⟪x, ‖v‖⁻¹ • v⟫ := fun z hz ↦ by
    rw [real_inner_smul_right, real_inner_smul_right, ← hv, ← hv]
    exact mul_le_mul_of_nonneg_left (hf z hz).le (inv_nonneg.mpr hn.le)
  have h1 : supportFunction D (‖v‖⁻¹ • v) ≤ ⟪x, ‖v‖⁻¹ • v⟫ := supportFunction_le ⟨y, hy⟩ hle
  have h2 : ⟪x, ‖v‖⁻¹ • v⟫ ≤ supportFunction K (‖v‖⁻¹ • v) := inner_le_supportFunction hK hx
  exact (h _ (norm_smul_inv_norm hv0)).not_ge (h1.trans h2)

end SupportFunction

/-! ### Projection endpoints of an ellipsoid inside an open set -/

namespace Ellipsoid

section Hilbert

variable [CompleteSpace E] (e : Ellipsoid E)

/-- The support function of an ellipsoid is attained, in any real Hilbert space: at
`c + A (A* ω / ‖A* ω‖)`. -/
theorem exists_inner_eq_supportFunction (ω : E) :
    ∃ x ∈ (e : Set E), ⟪x, ω⟫ = supportFunction (e : Set E) ω := by
  obtain ⟨w, hw⟩ : ∃ w, ContinuousLinearMap.adjoint (e.linearPart : E →L[ℝ] E) ω = w := ⟨_, rfl⟩
  have hnorm : ‖‖w‖⁻¹ • w‖ ≤ 1 := by
    rw [norm_smul, norm_inv, norm_norm]
    rcases eq_or_ne ‖w‖ 0 with h | h
    · simp [h]
    · rw [inv_mul_cancel₀ h]
  refine ⟨e.center + e.linearPart (‖w‖⁻¹ • w), ⟨‖w‖⁻¹ • w, by simpa using hnorm, rfl⟩, ?_⟩
  rw [e.supportFunction_eq, hw, inner_add_left, ← ContinuousLinearEquiv.coe_coe,
    ← ContinuousLinearMap.adjoint_inner_right, hw, real_inner_smul_left,
    real_inner_self_eq_norm_sq]
  congr 1
  rcases eq_or_ne ‖w‖ 0 with h | h
  · simp [h]
  · field_simp

/-- The lower support function of an ellipsoid is attained, in any real Hilbert space. -/
theorem exists_inner_eq_lowerSupportFunction (ω : E) :
    ∃ x ∈ (e : Set E), ⟪x, ω⟫ = lowerSupportFunction (e : Set E) ω := by
  obtain ⟨x, hx, hxω⟩ := e.exists_inner_eq_supportFunction (-ω)
  refine ⟨x, hx, ?_⟩
  rw [inner_neg_right, supportFunction_neg] at hxω
  linarith

/-- An ellipsoid contained in an open bounded set `D` projects strictly inside the projection of
`D`: `b_𝓔(ω) < b_D(ω)` for `ω ≠ 0`. -/
theorem supportFunction_lt_of_subset {D : Set E} (hD : IsOpen D) (hDb : IsBounded D)
    (he : (e : Set E) ⊆ D) {ω : E} (hω : ω ≠ 0) :
    supportFunction (e : Set E) ω < supportFunction D ω := by
  obtain ⟨x, hx, hxω⟩ := e.exists_inner_eq_supportFunction ω
  rw [← hxω]
  exact hD.inner_lt_supportFunction hDb (he hx) hω

/-- An ellipsoid contained in an open bounded set `D` projects strictly inside the projection of
`D`: `a_D(ω) < a_𝓔(ω)` for `ω ≠ 0`. -/
theorem lowerSupportFunction_lt_of_subset {D : Set E} (hD : IsOpen D) (hDb : IsBounded D)
    (he : (e : Set E) ⊆ D) {ω : E} (hω : ω ≠ 0) :
    lowerSupportFunction D ω < lowerSupportFunction (e : Set E) ω := by
  obtain ⟨x, hx, hxω⟩ := e.exists_inner_eq_lowerSupportFunction ω
  rw [← hxω]
  exact hD.lowerSupportFunction_lt_inner hDb (he hx) hω

/-- **Interval sandwich** [Hägg, Remark 3], as a chain of inequalities: if `D₀ ⊆ 𝓔 ⊆ D` for a
nonempty set `D₀`, an ellipsoid `𝓔` and an open bounded set `D`, then for `ω ≠ 0`
`a_D(ω) < a_𝓔(ω) ≤ a_{D₀}(ω) ≤ b_{D₀}(ω) ≤ b_𝓔(ω) < b_D(ω)`. -/
theorem projection_endpoints_sandwich {D₀ D : Set E} (hD₀ : D₀.Nonempty) (hD : IsOpen D)
    (hDb : IsBounded D) (h₀ : D₀ ⊆ e) (h₁ : (e : Set E) ⊆ D) {ω : E} (hω : ω ≠ 0) :
    lowerSupportFunction D ω < lowerSupportFunction (e : Set E) ω ∧
      lowerSupportFunction (e : Set E) ω ≤ lowerSupportFunction D₀ ω ∧
      lowerSupportFunction D₀ ω ≤ supportFunction D₀ ω ∧
      supportFunction D₀ ω ≤ supportFunction (e : Set E) ω ∧
      supportFunction (e : Set E) ω < supportFunction D ω :=
  ⟨e.lowerSupportFunction_lt_of_subset hD hDb h₁ hω, lowerSupportFunction_anti hD₀ e.isBounded h₀,
    lowerSupportFunction_le_supportFunction hD₀ (e.isBounded.subset h₀),
    supportFunction_mono hD₀ e.isBounded h₀, e.supportFunction_lt_of_subset hD hDb h₁ hω⟩

/-- **Interval sandwich** [Hägg, Remark 3]: if `D₀ ⊆ 𝓔 ⊆ D` for a nonempty set `D₀`, an
ellipsoid `𝓔` and an open bounded set `D`, then for `ω ≠ 0`
`[a_{D₀}(ω), b_{D₀}(ω)] ⊆ [a_𝓔(ω), b_𝓔(ω)] ⊆ (a_D(ω), b_D(ω))`. -/
theorem interval_sandwich {D₀ D : Set E} (hD₀ : D₀.Nonempty) (hD : IsOpen D) (hDb : IsBounded D)
    (h₀ : D₀ ⊆ e) (h₁ : (e : Set E) ⊆ D) {ω : E} (hω : ω ≠ 0) :
    Icc (lowerSupportFunction D₀ ω) (supportFunction D₀ ω) ⊆
        Icc (lowerSupportFunction (e : Set E) ω) (supportFunction (e : Set E) ω) ∧
      Icc (lowerSupportFunction (e : Set E) ω) (supportFunction (e : Set E) ω) ⊆
        Ioo (lowerSupportFunction D ω) (supportFunction D ω) := by
  obtain ⟨h1, h2, -, h4, h5⟩ := e.projection_endpoints_sandwich hD₀ hD hDb h₀ h₁ hω
  exact ⟨Icc_subset_Icc h2 h4, Icc_subset_Ioo h1 h5⟩

end Hilbert

end Ellipsoid

/-! ### The monic quadratic `F_ω` -/

/-- The monic quadratic `F_ω(p) = p² - 2⟪c, ω⟫ p + ⟪B ω, ω⟫` of [Hägg, Remark 3]. -/
def feasibilityQuadratic (c : E) (B : E →L[ℝ] E) (ω : E) (p : ℝ) : ℝ :=
  p ^ 2 - 2 * ⟪c, ω⟫ * p + ⟪B ω, ω⟫

/-- With `B = c cᵀ - Q`, `F_ω(p) = (p - ⟪c, ω⟫)² - ⟪Q ω, ω⟫`. -/
theorem feasibilityQuadratic_rankOne_sub (c : E) (Q : E →L[ℝ] E) (ω : E) (p : ℝ) :
    feasibilityQuadratic c (rankOne ℝ c c - Q) ω p = (p - ⟪c, ω⟫) ^ 2 - ⟪Q ω, ω⟫ := by
  simp only [feasibilityQuadratic, sub_apply, rankOne_apply, inner_sub_left,
    real_inner_smul_left]
  ring

/-- For fixed `ω` and `p`, the map `(c, B) ↦ F_ω(p) - p²` is linear.  In the plane this says
that each condition of [Hägg, Remark 3] is affine in the five real variables (the two entries
of `c` and the three independent entries of the symmetric matrix `B`). -/
theorem isLinearMap_feasibilityQuadratic_sub_sq (ω : E) (p : ℝ) :
    IsLinearMap ℝ fun cB : E × (E →L[ℝ] E) ↦ feasibilityQuadratic cB.1 cB.2 ω p - p ^ 2 where
  map_add x y := by
    simp only [feasibilityQuadratic, Prod.fst_add, Prod.snd_add, inner_add_left,
      add_apply]
    ring
  map_smul r x := by
    simp only [feasibilityQuadratic, Prod.smul_fst, Prod.smul_snd, real_inner_smul_left,
      smul_apply, smul_eq_mul]
    ring

/-- `F_ω(p)` is affine in `(c, B)`. -/
theorem feasibilityQuadratic_add_smul {a b : ℝ} (hab : a + b = 1) (x y : E × (E →L[ℝ] E))
    (ω : E) (p : ℝ) :
    feasibilityQuadratic (a • x + b • y).1 (a • x + b • y).2 ω p =
      a * feasibilityQuadratic x.1 x.2 ω p + b * feasibilityQuadratic y.1 y.2 ω p := by
  have h := isLinearMap_feasibilityQuadratic_sub_sq ω p
  have h1 := h.map_add (a • x) (b • y)
  rw [h.map_smul, h.map_smul, smul_eq_mul, smul_eq_mul] at h1
  linear_combination h1 - p ^ 2 * hab

/-- The set of solutions `(c, B)` of the feasibility problem of [Hägg, Remark 3] is convex. -/
theorem convex_setOf_quadratic_feasibility [CompleteSpace E] (D₀ D : Set E) :
    Convex ℝ {cB : E × (E →L[ℝ] E) | IsSelfAdjoint cB.2 ∧ ∀ ω : E, ‖ω‖ = 1 →
      0 < feasibilityQuadratic cB.1 cB.2 ω (lowerSupportFunction D ω) ∧
      feasibilityQuadratic cB.1 cB.2 ω (lowerSupportFunction D₀ ω) ≤ 0 ∧
      feasibilityQuadratic cB.1 cB.2 ω (supportFunction D₀ ω) ≤ 0 ∧
      0 < feasibilityQuadratic cB.1 cB.2 ω (supportFunction D ω)} := by
  intro x hx y hy a b ha hb hab
  refine ⟨?_, fun ω hω ↦ ?_⟩
  · simpa using ((IsSelfAdjoint.all a).smul hx.1).add ((IsSelfAdjoint.all b).smul hy.1)
  obtain ⟨hx1, hx2, hx3, hx4⟩ := hx.2 ω hω
  obtain ⟨hy1, hy2, hy3, hy4⟩ := hy.2 ω hω
  simp only [feasibilityQuadratic_add_smul hab]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa using convex_Ioi (0 : ℝ) hx1 hy1 ha hb hab
  · simpa using convex_Iic (0 : ℝ) hx2 hy2 ha hb hab
  · simpa using convex_Iic (0 : ℝ) hx3 hy3 ha hb hab
  · simpa using convex_Ioi (0 : ℝ) hx4 hy4 ha hb hab

namespace Ellipsoid

variable [CompleteSpace E] (e : Ellipsoid E)

/-- The shape of an ellipsoid is positive semidefinite. -/
theorem inner_shape_nonneg (ω : E) : 0 ≤ ⟪e.shape ω, ω⟫ := by
  rw [e.inner_shape_self]
  positivity

/-- For an ellipsoid with center `c` and shape `Q`, the quadratic `F_ω` with `B = c cᵀ - Q`
vanishes at the projection endpoints of the ellipsoid [Hägg, Remark 3]:
`F_ω(p) = (p - a_𝓔(ω)) (p - b_𝓔(ω))`. -/
theorem feasibilityQuadratic_eq_mul (ω : E) (p : ℝ) :
    feasibilityQuadratic e.center (rankOne ℝ e.center e.center - e.shape) ω p =
      (p - lowerSupportFunction (e : Set E) ω) * (p - supportFunction (e : Set E) ω) := by
  rw [feasibilityQuadratic_rankOne_sub, e.lowerSupportFunction_eq_sqrt, e.supportFunction_eq_sqrt]
  linear_combination Real.sq_sqrt (e.inner_shape_nonneg ω)

/-- For an ellipsoid with center `c` and shape `Q` and `B = c cᵀ - Q`, `F_ω(p) ≤ 0` iff `p` lies
in the projection interval `[a_𝓔(ω), b_𝓔(ω)]` of the ellipsoid. -/
theorem feasibilityQuadratic_nonpos_iff (ω : E) (p : ℝ) :
    feasibilityQuadratic e.center (rankOne ℝ e.center e.center - e.shape) ω p ≤ 0 ↔
      p ∈ Icc (lowerSupportFunction (e : Set E) ω) (supportFunction (e : Set E) ω) := by
  have hab := lowerSupportFunction_le_supportFunction (ω := ω) e.nonempty e.isBounded
  rw [e.feasibilityQuadratic_eq_mul, mem_Icc]
  constructor
  · intro h
    by_contra hp
    rw [not_and_or, not_le, not_le] at hp
    rcases hp with hp | hp
    · exact h.not_gt (mul_pos_of_neg_of_neg (by linarith) (by linarith))
    · exact h.not_gt (mul_pos (by linarith) (by linarith))
  · rintro ⟨h1, h2⟩
    exact mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)

/-- For an ellipsoid with center `c` and shape `Q` and `B = c cᵀ - Q`, `F_ω(p) > 0` iff `p` lies
outside the projection interval `[a_𝓔(ω), b_𝓔(ω)]` of the ellipsoid. -/
theorem feasibilityQuadratic_pos_iff (ω : E) (p : ℝ) :
    0 < feasibilityQuadratic e.center (rankOne ℝ e.center e.center - e.shape) ω p ↔
      p ∉ Icc (lowerSupportFunction (e : Set E) ω) (supportFunction (e : Set E) ω) := by
  rw [← e.feasibilityQuadratic_nonpos_iff, not_le]

/-- The direct half of [Hägg, Remark 3], in any real Hilbert space: if `D₀ ⊆ 𝓔 ⊆ D` for a
nonempty set `D₀`, an ellipsoid `𝓔` with center `c` and shape `Q` and an open bounded set `D`,
then `(c, B) = (c, c cᵀ - Q)` satisfies the four sign conditions in every direction `ω ≠ 0`. -/
theorem quadratic_feasibility {D₀ D : Set E} (hD₀ : D₀.Nonempty) (hD : IsOpen D)
    (hDb : IsBounded D) (h₀ : D₀ ⊆ e) (h₁ : (e : Set E) ⊆ D) {ω : E} (hω : ω ≠ 0) :
    0 < feasibilityQuadratic e.center (rankOne ℝ e.center e.center - e.shape) ω
        (lowerSupportFunction D ω) ∧
      feasibilityQuadratic e.center (rankOne ℝ e.center e.center - e.shape) ω
        (lowerSupportFunction D₀ ω) ≤ 0 ∧
      feasibilityQuadratic e.center (rankOne ℝ e.center e.center - e.shape) ω
        (supportFunction D₀ ω) ≤ 0 ∧
      0 < feasibilityQuadratic e.center (rankOne ℝ e.center e.center - e.shape) ω
        (supportFunction D ω) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := e.projection_endpoints_sandwich hD₀ hD hDb h₀ h₁ hω
  rw [e.feasibilityQuadratic_pos_iff, e.feasibilityQuadratic_nonpos_iff,
    e.feasibilityQuadratic_nonpos_iff, e.feasibilityQuadratic_pos_iff, mem_Icc, mem_Icc, mem_Icc,
    mem_Icc]
  exact ⟨fun h ↦ h1.not_ge h.1, ⟨h2, h3.trans h4⟩, ⟨h2.trans h3, h4⟩, fun h ↦ h5.not_ge h.2⟩

end Ellipsoid

/-! ### The feasibility criterion -/

/-- The converse half of [Hägg, Remark 3]: a solution `(c, B)` of the feasibility problem gives
an ellipsoid with center `c` and shape `Q = c cᵀ - B` such that `closure D₀ ⊆ 𝓔 ⊆ D`.  (Since
`F_ω` is monic and nonpositive at the distinct points `a_{D₀}(ω) < b_{D₀}(ω)`, it has two
distinct real roots, so `Q` is positive definite; these roots are the projection endpoints of
`𝓔`, and the sign conditions give the interval sandwich.) -/
theorem exists_ellipsoid_of_quadratic_feasibility [FiniteDimensional ℝ E] {D₀ D : Set E}
    (hD₀ : IsOpen D₀) (hD₀ne : D₀.Nonempty) (hD₀D : D₀ ⊆ D) (hD : IsOpen D) (hDc : Convex ℝ D)
    (hDb : IsBounded D) {c : E} {B : E →L[ℝ] E} (hB : IsSelfAdjoint B)
    (h : ∀ ω : E, ‖ω‖ = 1 →
      0 < feasibilityQuadratic c B ω (lowerSupportFunction D ω) ∧
      feasibilityQuadratic c B ω (lowerSupportFunction D₀ ω) ≤ 0 ∧
      feasibilityQuadratic c B ω (supportFunction D₀ ω) ≤ 0 ∧
      0 < feasibilityQuadratic c B ω (supportFunction D ω)) :
    ∃ e : Ellipsoid E, e.center = c ∧ e.shape = rankOne ℝ c c - B ∧ closure D₀ ⊆ e ∧
      (e : Set E) ⊆ D := by
  have hD₀b : IsBounded D₀ := hDb.subset hD₀D
  set Q : E →L[ℝ] E := rankOne ℝ c c - B with hQ
  have hQsa : IsSelfAdjoint Q := (isPositive_rankOne_self (𝕜 := ℝ) c).isSelfAdjoint.sub hB
  have hF : ∀ ω p, feasibilityQuadratic c B ω p = (p - ⟪c, ω⟫) ^ 2 - ⟪Q ω, ω⟫ := fun ω p ↦ by
    rw [← feasibilityQuadratic_rankOne_sub, hQ, sub_sub_cancel]
  -- `F_ω` has two distinct real roots, so `Q` is positive on unit vectors
  have hunit : ∀ ω : E, ‖ω‖ = 1 → 0 < ⟪Q ω, ω⟫ := by
    intro ω hω
    have hω0 : ω ≠ 0 := by
      rintro rfl
      simp at hω
    obtain ⟨x, hx⟩ := hD₀ne
    have hab : lowerSupportFunction D₀ ω < supportFunction D₀ ω :=
      (hD₀.lowerSupportFunction_lt_inner hD₀b hx hω0).trans
        (hD₀.inner_lt_supportFunction hD₀b hx hω0)
    obtain ⟨-, ha, hb, -⟩ := h ω hω
    rw [hF] at ha hb
    nlinarith [sq_nonneg (lowerSupportFunction D₀ ω + supportFunction D₀ ω - 2 * ⟪c, ω⟫),
      mul_pos (sub_pos.mpr hab) (sub_pos.mpr hab)]
  have hpos : ∀ x : E, x ≠ 0 → 0 < ⟪Q x, x⟫ := by
    intro x hx
    have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
    have h1 := hunit (‖x‖⁻¹ • x) (norm_smul_inv_norm hx)
    rw [map_smul, real_inner_smul_left, real_inner_smul_right] at h1
    exact pos_of_mul_pos_right (pos_of_mul_pos_right h1 (inv_nonneg.mpr hn.le))
      (inv_nonneg.mpr hn.le)
  obtain ⟨e, hec, heQ⟩ := Ellipsoid.exists_center_shape_eq c hQsa hpos
  have hFe : feasibilityQuadratic c B =
      feasibilityQuadratic e.center (rankOne ℝ e.center e.center - e.shape) := by
    rw [heQ, hec, hQ, sub_sub_cancel]
  -- the interval sandwich on unit vectors
  have hend : ∀ ω : E, ‖ω‖ = 1 →
      lowerSupportFunction D ω < lowerSupportFunction (e : Set E) ω ∧
      lowerSupportFunction (e : Set E) ω ≤ lowerSupportFunction D₀ ω ∧
      supportFunction D₀ ω ≤ supportFunction (e : Set E) ω ∧
      supportFunction (e : Set E) ω < supportFunction D ω := by
    intro ω hω
    obtain ⟨h1, h2, h3, h4⟩ := h ω hω
    rw [hFe, e.feasibilityQuadratic_pos_iff, mem_Icc] at h1 h4
    rw [hFe, e.feasibilityQuadratic_nonpos_iff, mem_Icc] at h2 h3
    have ha : lowerSupportFunction D ω ≤ lowerSupportFunction D₀ ω :=
      lowerSupportFunction_anti hD₀ne hDb hD₀D
    have hb : supportFunction D₀ ω ≤ supportFunction D ω := supportFunction_mono hD₀ne hDb hD₀D
    refine ⟨?_, h2.1, h3.2, ?_⟩
    · by_contra hc
      exact h1 ⟨not_lt.mp hc, ha.trans h2.2⟩
    · by_contra hc
      exact h4 ⟨h3.1.trans hb, not_lt.mp hc⟩
  refine ⟨e, hec, heQ.trans hQ, ?_, ?_⟩
  · -- the support-function criterion gives `closure D₀ ⊆ 𝓔`
    refine subset_of_forall_supportFunction_le hD₀b.closure e.nonempty e.convex e.isClosed
      fun ω ↦ ?_
    rw [supportFunction_closure hD₀b]
    exact supportFunction_le_of_forall_norm_eq_one (fun ω hω ↦ (hend ω hω).2.2.1) ω
  · -- a supporting hyperplane at a point of `𝓔 \ D` would contradict `b_𝓔 < b_D`
    exact subset_of_forall_supportFunction_lt e.isBounded (hD₀ne.mono hD₀D) hD hDc
      fun ω hω ↦ (hend ω hω).2.2.2

/-- **Five-variable feasibility** [Hägg, Remark 3].  Let `D₀ ⊆ D` in a finite dimensional real
inner product space, with `D₀` nonempty and open and `D` open, convex and bounded.  There is an
ellipsoid `𝓔` with `closure D₀ ⊆ 𝓔 ⊆ D` iff there are `c` and a self-adjoint `B` such that the
monic quadratic `F_ω(p) = p² - 2⟪c, ω⟫ p + ⟪B ω, ω⟫` satisfies, for every unit vector `ω`,
`F_ω(a_D(ω)) > 0`, `F_ω(a_{D₀}(ω)) ≤ 0`, `F_ω(b_{D₀}(ω)) ≤ 0` and `F_ω(b_D(ω)) > 0`.
(Convexity of `D₀` is not needed.) -/
theorem exists_ellipsoid_iff_quadratic_feasibility [FiniteDimensional ℝ E] {D₀ D : Set E}
    (hD₀ : IsOpen D₀) (hD₀ne : D₀.Nonempty) (hD₀D : D₀ ⊆ D) (hD : IsOpen D) (hDc : Convex ℝ D)
    (hDb : IsBounded D) :
    (∃ e : Ellipsoid E, closure D₀ ⊆ e ∧ (e : Set E) ⊆ D) ↔
      ∃ (c : E) (B : E →L[ℝ] E), IsSelfAdjoint B ∧ ∀ ω : E, ‖ω‖ = 1 →
        0 < feasibilityQuadratic c B ω (lowerSupportFunction D ω) ∧
        feasibilityQuadratic c B ω (lowerSupportFunction D₀ ω) ≤ 0 ∧
        feasibilityQuadratic c B ω (supportFunction D₀ ω) ≤ 0 ∧
        0 < feasibilityQuadratic c B ω (supportFunction D ω) := by
  constructor
  · rintro ⟨e, h₀, h₁⟩
    refine ⟨e.center, rankOne ℝ e.center e.center - e.shape,
      (isPositive_rankOne_self (𝕜 := ℝ) _).isSelfAdjoint.sub e.shape_isSelfAdjoint,
      fun ω hω ↦ e.quadratic_feasibility hD₀ne hD hDb (subset_closure.trans h₀) h₁ ?_⟩
    rintro rfl
    simp at hω
  · rintro ⟨c, B, hB, h⟩
    obtain ⟨e, -, -, h₀, h₁⟩ :=
      exists_ellipsoid_of_quadratic_feasibility hD₀ hD₀ne hD₀D hD hDc hDb hB h
    exact ⟨e, h₀, h₁⟩

end
