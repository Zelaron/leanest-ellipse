import LeanestEllipse.Analysis.Convex.SupportFunction
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.MetricSpace.Thickening

/-!
# Ellipsoids

An *ellipsoid* (closed, nondegenerate) in a real inner product space `E` is a set of the form
`c + A (closedBall 0 1)` with `c : E` and `A : E ≃L[ℝ] E`.  In dimension two these are the
*ellipses* `c + Q^{1/2} \overline{𝔻_1}` of [Hägg]; the positive definite matrix `Q` is recovered
as the *shape* `A A*` of the ellipsoid.

## Main definitions and results

* `Ellipsoid E`: the data `(center, linearPart)` of an ellipsoid; it coerces to `Set E`.
* `Ellipsoid.supportFunction_eq`, `Ellipsoid.supportFunction_eq_sqrt`: the projection endpoints
  `a_E(ω) = ⟪c, ω⟫ - √⟪Q ω, ω⟫`, `b_E(ω) = ⟪c, ω⟫ + √⟪Q ω, ω⟫` of [Hägg, (1.3)].
* `Ellipsoid.exists_center_shape_eq`: every positive definite self-adjoint `Q` (in finite
  dimension) is the shape of an ellipsoid with any prescribed center.
* `Ellipsoid.toSet_eq_of_center_shape`: an ellipsoid, as a set, only depends on its center and
  shape.
* `Ellipsoid.map`: transport along linear isometry equivalences.
* `Ellipsoid.closedBall`: closed balls as ellipsoids.
* `Ellipsoid.exists_one_lt_image_closedBall_subset`: an ellipsoid inside an open set stays
  inside after a slight dilation about its center.
* `exists_sqrt_of_pos`: positive definite self-adjoint operators on finite dimensional real
  inner product spaces have invertible self-adjoint square roots.
-/

open Set Metric Bornology
open scoped RealInnerProductSpace

noncomputable section

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-! ### Square roots of positive definite operators -/

section Sqrt

variable [FiniteDimensional ℝ E]

/-- A positive definite self-adjoint operator on a finite dimensional real inner product space
has an invertible self-adjoint square root. -/
theorem exists_sqrt_of_pos {Q : E →L[ℝ] E} (hQ : IsSelfAdjoint Q)
    (hpos : ∀ x : E, x ≠ 0 → 0 < ⟪Q x, x⟫) :
    ∃ S : E ≃L[ℝ] E, IsSelfAdjoint (S : E →L[ℝ] E) ∧ (S : E →L[ℝ] E) * S = Q := by
  have hT : (Q : E →ₗ[ℝ] E).IsSymmetric := hQ.isSymmetric
  set b := hT.eigenvectorBasis (rfl : Module.finrank ℝ E = Module.finrank ℝ E)
  set lam := hT.eigenvalues (rfl : Module.finrank ℝ E = Module.finrank ℝ E)
  have hb : ∀ i, Q (b i) = lam i • b i := fun i ↦ hT.apply_eigenvectorBasis rfl i
  have hlam : ∀ i, 0 < lam i := by
    intro i
    have h := hpos (b i) (b.orthonormal.ne_zero i)
    rw [hb, real_inner_smul_left, real_inner_self_eq_norm_sq, b.orthonormal.1 i] at h
    simpa using h
  -- the square root, defined on the eigenbasis
  let S₀ : E →ₗ[ℝ] E := b.toBasis.constr ℝ fun i ↦ Real.sqrt (lam i) • b i
  have hS₀b : ∀ i, S₀ (b i) = Real.sqrt (lam i) • b i := fun i ↦ by
    simp [S₀]
  have hS₀sq : S₀ ∘ₗ S₀ = (Q : E →ₗ[ℝ] E) := by
    apply b.toBasis.ext
    intro i
    simp only [OrthonormalBasis.coe_toBasis, LinearMap.comp_apply, hS₀b, map_smul, smul_smul,
      ContinuousLinearMap.coe_coe, hb]
    rw [Real.mul_self_sqrt (hlam i).le]
  have hS₀apply : ∀ x, S₀ x = ∑ i, (Real.sqrt (lam i) * ⟪b i, x⟫) • b i := by
    intro x
    conv_lhs => rw [← b.sum_repr' x]
    simp only [map_sum, map_smul, hS₀b, smul_smul]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [mul_comm]
  have hS₀symm : S₀.IsSymmetric := by
    intro x y
    rw [hS₀apply, hS₀apply, sum_inner, inner_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [real_inner_smul_left, real_inner_smul_right, real_inner_comm (b i) x]
    ring
  have hQinj : Function.Injective Q := by
    intro u v huv
    by_contra hne
    have := hpos (u - v) (sub_ne_zero.mpr hne)
    rw [map_sub, huv, sub_self, inner_zero_left] at this
    exact lt_irrefl _ this
  have hS₀inj : Function.Injective S₀ := by
    intro x y hxy
    apply hQinj
    have h := congrArg S₀ hxy
    rw [← ContinuousLinearMap.coe_coe Q, ← hS₀sq, LinearMap.comp_apply, LinearMap.comp_apply, h]
  let S : E ≃L[ℝ] E := (LinearEquiv.ofInjectiveEndo S₀ hS₀inj).toContinuousLinearEquiv
  refine ⟨S, ?_, ?_⟩
  · rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
    exact hS₀symm
  · ext x
    change S₀ (S₀ x) = Q x
    rw [← LinearMap.comp_apply, hS₀sq, ContinuousLinearMap.coe_coe]

end Sqrt

/-! ### Ellipsoids -/

/-- A closed nondegenerate ellipsoid in a real inner product space `E`, given by its center and
the linear part of an affine parametrization: the underlying set is
`center + linearPart (closedBall 0 1)`.  In dimension two these are the ellipses of [Hägg]. -/
structure Ellipsoid (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] where
  /-- The center of the ellipsoid. -/
  center : E
  /-- The linear part: the ellipsoid is `center + linearPart (closedBall 0 1)`. -/
  linearPart : E ≃L[ℝ] E

namespace Ellipsoid

variable (e : Ellipsoid E)

/-- The underlying set `center + linearPart (closedBall 0 1)` of an ellipsoid. -/
def toSet : Set E := (fun y ↦ e.center + e.linearPart y) '' closedBall 0 1

instance : CoeOut (Ellipsoid E) (Set E) := ⟨toSet⟩

theorem coe_def : (e : Set E) = (fun y ↦ e.center + e.linearPart y) '' closedBall 0 1 := rfl

theorem coe_eq_image_add : (e : Set E) =
    (e.center + ·) '' ((e.linearPart : E →L[ℝ] E) '' closedBall 0 1) := by
  rw [coe_def, Set.image_image]
  rfl

theorem mem_iff {x : E} : x ∈ (e : Set E) ↔ ‖e.linearPart.symm (x - e.center)‖ ≤ 1 := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy
  · intro hx
    exact ⟨e.linearPart.symm (x - e.center), by simpa using hx, by simp⟩

theorem add_mem_iff {x : E} :
    e.center + x ∈ (e : Set E) ↔ ‖e.linearPart.symm x‖ ≤ 1 := by
  simp [mem_iff]

/-- Ellipsoids are centrally symmetric about their center. -/
theorem add_mem_iff_sub_mem {x : E} :
    e.center + x ∈ (e : Set E) ↔ e.center - x ∈ (e : Set E) := by
  rw [add_mem_iff, sub_eq_add_neg, add_mem_iff, map_neg, norm_neg]

theorem center_mem : e.center ∈ (e : Set E) := ⟨0, by simp, by simp⟩

theorem nonempty : (e : Set E).Nonempty := ⟨e.center, e.center_mem⟩

theorem convex : Convex ℝ (e : Set E) := by
  intro x hx y hy a b ha hb hab
  rw [mem_iff] at hx hy ⊢
  have hc : a • x + b • y - e.center = a • (x - e.center) + b • (y - e.center) := by
    have : e.center = a • e.center + b • e.center := by rw [← add_smul, hab, one_smul]
    conv_lhs => rw [this]
    simp only [smul_sub]
    abel
  rw [hc, map_add, map_smul, map_smul]
  calc ‖a • e.linearPart.symm (x - e.center) + b • e.linearPart.symm (y - e.center)‖
      ≤ a * ‖e.linearPart.symm (x - e.center)‖ + b * ‖e.linearPart.symm (y - e.center)‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]
    _ ≤ a * 1 + b * 1 := by gcongr
    _ = 1 := by rw [mul_one, mul_one, hab]

theorem isClosed : IsClosed (e : Set E) := by
  have : (e : Set E) = (fun x ↦ ‖e.linearPart.symm (x - e.center)‖) ⁻¹' Iic 1 := by
    ext x; simp [mem_iff]
  rw [this]
  exact isClosed_Iic.preimage (by fun_prop)

theorem subset_closedBall : (e : Set E) ⊆ closedBall e.center ‖(e.linearPart : E →L[ℝ] E)‖ := by
  rintro _ ⟨y, hy, rfl⟩
  rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left]
  calc ‖e.linearPart y‖ ≤ ‖(e.linearPart : E →L[ℝ] E)‖ * ‖y‖ :=
        (e.linearPart : E →L[ℝ] E).le_opNorm y
    _ ≤ ‖(e.linearPart : E →L[ℝ] E)‖ * 1 := by gcongr; simpa using hy
    _ = _ := mul_one _

theorem isBounded : IsBounded (e : Set E) := isBounded_closedBall.subset e.subset_closedBall

theorem isCompact [FiniteDimensional ℝ E] : IsCompact (e : Set E) :=
  Metric.isCompact_of_isClosed_isBounded e.isClosed e.isBounded

/-! #### Support function -/

section SupportFunction

variable [CompleteSpace E]

/-- The support function of an ellipsoid: `h_E(ω) = ⟪c, ω⟫ + ‖A* ω‖`. -/
theorem supportFunction_eq (ω : E) : supportFunction (e : Set E) ω =
    ⟪e.center, ω⟫ + ‖ContinuousLinearMap.adjoint (e.linearPart : E →L[ℝ] E) ω‖ := by
  rw [coe_eq_image_add, supportFunction_image_add ((nonempty_closedBall.mpr zero_le_one).image _)
    ((e.linearPart : E →L[ℝ] E).lipschitzWith.isBounded_image isBounded_closedBall),
    supportFunction_image_continuousLinearMap, supportFunction_closedBall_zero zero_le_one, one_mul]

/-- The lower support function of an ellipsoid: `a_E(ω) = ⟪c, ω⟫ - ‖A* ω‖`. -/
theorem lowerSupportFunction_eq (ω : E) : lowerSupportFunction (e : Set E) ω =
    ⟪e.center, ω⟫ - ‖ContinuousLinearMap.adjoint (e.linearPart : E →L[ℝ] E) ω‖ := by
  rw [lowerSupportFunction_eq_neg_supportFunction_neg, supportFunction_eq, inner_neg_right,
    map_neg, norm_neg]
  ring

/-- The *shape* `Q = A A*` of an ellipsoid `c + A (closedBall 0 1)`.  The ellipsoid is
`c + Q^{1/2} (closedBall 0 1)`, and it only depends on its center and shape
(`Ellipsoid.toSet_eq_of_center_shape`). -/
def shape : E →L[ℝ] E :=
  (e.linearPart : E →L[ℝ] E) ∘L ContinuousLinearMap.adjoint (e.linearPart : E →L[ℝ] E)

theorem inner_shape_self (ω : E) :
    ⟪e.shape ω, ω⟫ = ‖ContinuousLinearMap.adjoint (e.linearPart : E →L[ℝ] E) ω‖ ^ 2 := by
  rw [shape, ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.adjoint_inner_right,
    real_inner_self_eq_norm_sq]

theorem shape_isSelfAdjoint : IsSelfAdjoint e.shape := by
  rw [shape, ← ContinuousLinearMap.star_eq_adjoint]
  exact IsSelfAdjoint.mul_star_self _

theorem inner_shape_pos {ω : E} (hω : ω ≠ 0) : 0 < ⟪e.shape ω, ω⟫ := by
  rw [inner_shape_self]
  apply pow_pos (norm_pos_iff.mpr _)
  intro h
  apply hω
  have hinj : Function.Injective (ContinuousLinearMap.adjoint (e.linearPart : E →L[ℝ] E)) := by
    intro x y hxy
    apply ext_inner_left ℝ
    intro v
    obtain ⟨w, rfl⟩ := e.linearPart.surjective v
    rw [← ContinuousLinearEquiv.coe_coe, ← ContinuousLinearMap.adjoint_inner_right,
      ← ContinuousLinearMap.adjoint_inner_right, hxy]
  exact hinj (h.trans (map_zero _).symm)

/-- The support function of an ellipsoid in terms of its shape:
`b_E(ω) = ⟪c, ω⟫ + √⟪Q ω, ω⟫` [Hägg, (1.3)]. -/
theorem supportFunction_eq_sqrt (ω : E) :
    supportFunction (e : Set E) ω = ⟪e.center, ω⟫ + Real.sqrt ⟪e.shape ω, ω⟫ := by
  rw [supportFunction_eq, inner_shape_self, Real.sqrt_sq (norm_nonneg _)]

/-- The lower support function of an ellipsoid in terms of its shape:
`a_E(ω) = ⟪c, ω⟫ - √⟪Q ω, ω⟫` [Hägg, (1.3)]. -/
theorem lowerSupportFunction_eq_sqrt (ω : E) :
    lowerSupportFunction (e : Set E) ω = ⟪e.center, ω⟫ - Real.sqrt ⟪e.shape ω, ω⟫ := by
  rw [lowerSupportFunction_eq, inner_shape_self, Real.sqrt_sq (norm_nonneg _)]

/-- An ellipsoid, as a set, only depends on its center and its shape. -/
theorem toSet_eq_of_center_shape {e e' : Ellipsoid E} (hc : e.center = e'.center)
    (hQ : e.shape = e'.shape) : (e : Set E) = e' := by
  have h : ∀ ω, supportFunction (e : Set E) ω = supportFunction (e' : Set E) ω := by
    intro ω
    rw [supportFunction_eq_sqrt, supportFunction_eq_sqrt, hc, hQ]
  apply Subset.antisymm
  · exact subset_of_forall_supportFunction_le e.isBounded e'.nonempty e'.convex e'.isClosed
      fun ω ↦ (h ω).le
  · exact subset_of_forall_supportFunction_le e'.isBounded e.nonempty e.convex e.isClosed
      fun ω ↦ (h ω).ge

end SupportFunction

/-- Every positive definite self-adjoint operator `Q` on a finite dimensional real inner product
space is the shape of an ellipsoid with any prescribed center `c`; its projection endpoints are
`⟪c, ω⟫ ∓ √⟪Q ω, ω⟫`. -/
theorem exists_center_shape_eq [FiniteDimensional ℝ E] (c : E) {Q : E →L[ℝ] E}
    (hQ : IsSelfAdjoint Q) (hpos : ∀ x : E, x ≠ 0 → 0 < ⟪Q x, x⟫) :
    ∃ e : Ellipsoid E, e.center = c ∧ e.shape = Q := by
  obtain ⟨S, hS, hSS⟩ := exists_sqrt_of_pos hQ hpos
  refine ⟨⟨c, S⟩, rfl, ?_⟩
  rw [shape, ← ContinuousLinearMap.star_eq_adjoint, hS.star_eq]
  exact hSS

/-! #### Transport along linear isometries -/

/-- The image of an ellipsoid under a linear isometry equivalence. -/
def map (L : E ≃ₗᵢ[ℝ] F) (e : Ellipsoid E) : Ellipsoid F where
  center := L e.center
  linearPart := (L.symm.toContinuousLinearEquiv.trans e.linearPart).trans L.toContinuousLinearEquiv

@[simp] theorem map_center (L : E ≃ₗᵢ[ℝ] F) : (e.map L).center = L e.center := rfl

theorem map_linearPart_symm_apply (L : E ≃ₗᵢ[ℝ] F) (x : F) :
    (e.map L).linearPart.symm x = L (e.linearPart.symm (L.symm x)) := rfl

theorem coe_map (L : E ≃ₗᵢ[ℝ] F) : ((e.map L : Ellipsoid F) : Set F) = L '' (e : Set E) := by
  ext x
  rw [mem_iff, map_linearPart_symm_apply, LinearIsometryEquiv.norm_map, map_center, map_sub,
    LinearIsometryEquiv.symm_apply_apply]
  constructor
  · intro hx
    exact ⟨L.symm x, (mem_iff e).mpr hx, by simp⟩
  · rintro ⟨y, hy, rfl⟩
    simpa using (mem_iff e).mp hy

/-! #### Dilations -/

/-- An ellipsoid contained in an open set stays in it after a slight dilation about its center
(in finite dimension). -/
theorem exists_one_lt_image_closedBall_subset [FiniteDimensional ℝ E] {D : Set E}
    (hD : IsOpen D) (heD : (e : Set E) ⊆ D) :
    ∃ r : ℝ, 1 < r ∧ (fun y ↦ e.center + e.linearPart y) '' closedBall 0 r ⊆ D := by
  obtain ⟨δ, hδ, hthick⟩ := e.isCompact.exists_thickening_subset_open hD heD
  set M := ‖(e.linearPart : E →L[ℝ] E)‖
  have hM0 : 0 ≤ M := norm_nonneg _
  have hpos : 0 < δ / (2 * (M + 1)) := by positivity
  refine ⟨1 + δ / (2 * (M + 1)), by linarith, ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  have hM : 0 ≤ M := norm_nonneg _
  have hy' : ‖y‖ ≤ 1 + δ / (2 * (M + 1)) := by simpa using hy
  apply hthick
  rcases le_or_gt ‖y‖ 1 with hy1 | hy1
  · exact self_subset_thickening hδ _ ⟨y, by simpa using hy1, rfl⟩
  -- rescale `y` to the unit sphere
  set y₀ : E := ‖y‖⁻¹ • y
  have hynorm : 0 < ‖y‖ := lt_trans one_pos hy1
  have hy₀ : y₀ ∈ closedBall (0 : E) 1 := by
    rw [mem_closedBall_zero_iff, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hynorm.ne']
  rw [mem_thickening_iff]
  refine ⟨e.center + e.linearPart y₀, ⟨y₀, hy₀, rfl⟩, ?_⟩
  rw [dist_eq_norm, add_sub_add_left_eq_sub, ← map_sub]
  have hdiff : y - y₀ = (1 - ‖y‖⁻¹) • y := by rw [sub_smul, one_smul]
  calc ‖e.linearPart (y - y₀)‖ ≤ M * ‖y - y₀‖ := (e.linearPart : E →L[ℝ] E).le_opNorm _
    _ = M * (‖y‖ - 1) := by
        rw [hdiff, norm_smul, Real.norm_of_nonneg, sub_mul, one_mul, inv_mul_cancel₀ hynorm.ne']
        rw [sub_nonneg]
        exact inv_le_one_of_one_le₀ hy1.le
    _ ≤ M * (δ / (2 * (M + 1))) := by gcongr; linarith
    _ < δ := by
        rw [mul_div_assoc']
        rw [div_lt_iff₀ (by positivity)]
        nlinarith

/-! #### Balls -/

/-- The closed ball `Metric.closedBall c r` (`0 < r`) as an ellipsoid. -/
def closedBall (c : E) {r : ℝ} (hr : 0 < r) : Ellipsoid E :=
  ⟨c, ContinuousLinearEquiv.smulLeft (Units.mk0 r hr.ne')⟩

@[simp] theorem closedBall_center (c : E) {r : ℝ} (hr : 0 < r) :
    (Ellipsoid.closedBall c hr).center = c :=
  rfl

theorem coe_closedBall (c : E) {r : ℝ} (hr : 0 < r) :
    (Ellipsoid.closedBall c hr : Set E) = Metric.closedBall c r := by
  ext x
  simp only [coe_def, Ellipsoid.closedBall, ContinuousLinearEquiv.smulLeft_apply_apply,
    Units.smul_def, Units.val_mk0, mem_image, Metric.mem_closedBall, dist_zero_right]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hr.le]
    exact mul_le_of_le_one_right hr.le hy
  · intro hx
    refine ⟨r⁻¹ • (x - c), ?_, by rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul, add_sub_cancel]⟩
    rw [norm_smul, norm_inv, Real.norm_of_nonneg hr.le, inv_mul_le_iff₀ hr, mul_one,
      ← dist_eq_norm]
    exact hx

end Ellipsoid

end
