import LeanestEllipse.Analysis.Convex.QuadraticFeasibility
import Mathlib.Analysis.Complex.ReImTopology
import Mathlib.Analysis.InnerProductSpace.Trace

/-!
# The geometry of two concentric squares

This file contains the convex geometry behind [Hägg, Corollary 12] (*two concentric squares*),
[Hägg, Corollary 13] (*support in the closed outer square*) and [Hägg, Remark 14] (*the
endpoint*).  As in the paper, the plane is modelled by `ℂ` (`(x₁, x₂) ↔ x₁ + i x₂`); ellipses
are `Ellipsoid ℂ`, with center `c` and shape `Q` (a positive definite self-adjoint `ℝ`-linear
map of `ℂ`), and `Q₁₁ = ⟪Q 1, 1⟫`, `Q₂₂ = ⟪Q I, I⟫`, `Q₁₂ = ⟪Q 1, I⟫`.

The proofs follow the paper.  Projecting onto the coordinate axes, an ellipse inside the open
(closed) square `(-1, 1)²` satisfies `√Q_ii < 1 - |c_i|` (resp. `≤`), hence `tr Q < 2`
(resp. `≤ 2`).  Projecting onto the diagonal directions `1 ± I`, an ellipse containing the
closed square `[-δ, δ]²` satisfies `tr Q ≥ 4 δ²`.  (We use the unnormalized diagonal
directions `1 ± I` of norm `√2` instead of the paper's unit vectors `ω_± = (1, ±1)/√2`.)

## Main results

* `LeanestEllipse.exists_ellipsoid_openSquare_iff`: for `δ > 0` there is an ellipse `𝓔` with
  `closure (-δ, δ)² ⊆ 𝓔 ⊆ (-1, 1)²` iff `δ < 1/√2` (the geometric content of
  [Hägg, Corollary 12]).
* `LeanestEllipse.exists_ellipsoid_closedSquare_iff`: for `δ ≥ 0` there is an ellipse `𝓔` with
  `[-δ, δ]² ⊆ 𝓔 ⊆ [-1, 1]²` iff `δ ≤ 1/√2` (the geometric content of [Hägg, Corollary 13]).
* `LeanestEllipse.eq_closedBall_of_closedSquare_subset_of_subset_closedSquare`: the closed unit
  disk is the only ellipse with `[-1/√2, 1/√2]² ⊆ 𝓔 ⊆ [-1, 1]²` [Hägg, Remark 14].
* The trace inequalities `LeanestEllipse.trace_shape_lt_two`, `LeanestEllipse.trace_shape_le`,
  `LeanestEllipse.trace_shape_le_two` and `LeanestEllipse.four_mul_sq_le_trace_shape` of the
  proofs.

## References

* C. Hägg, *An ellipse criterion for exact nonuniqueness in the planar interior Radon problem*.
-/

open Set Metric Bornology Complex
open scoped RealInnerProductSpace

noncomputable section

namespace LeanestEllipse

/-! ### The squares -/

/-- The open square `(-r, r)²` in `ℂ = ℝ²`. -/
def openSquare (r : ℝ) : Set ℂ := Set.Ioo (-r) r ×ℂ Set.Ioo (-r) r

/-- The closed square `[-r, r]²` in `ℂ = ℝ²`. -/
def closedSquare (r : ℝ) : Set ℂ := Set.Icc (-r) r ×ℂ Set.Icc (-r) r

/-- `z ∈ (-r, r)²` iff both coordinates of `z` lie in `(-r, r)`. -/
theorem mem_openSquare {r : ℝ} {z : ℂ} :
    z ∈ openSquare r ↔ z.re ∈ Ioo (-r) r ∧ z.im ∈ Ioo (-r) r :=
  Iff.rfl

/-- `z ∈ [-r, r]²` iff both coordinates of `z` lie in `[-r, r]`. -/
theorem mem_closedSquare {r : ℝ} {z : ℂ} :
    z ∈ closedSquare r ↔ z.re ∈ Icc (-r) r ∧ z.im ∈ Icc (-r) r :=
  Iff.rfl

/-- The open square is contained in the closed square. -/
theorem openSquare_subset_closedSquare (r : ℝ) : openSquare r ⊆ closedSquare r :=
  fun _ hz ↦ ⟨Ioo_subset_Icc_self hz.1, Ioo_subset_Icc_self hz.2⟩

/-- The open square is open. -/
theorem isOpen_openSquare (r : ℝ) : IsOpen (openSquare r) :=
  isOpen_Ioo.reProdIm isOpen_Ioo

/-- The closed square is closed. -/
theorem isClosed_closedSquare (r : ℝ) : IsClosed (closedSquare r) :=
  isClosed_Icc.reProdIm isClosed_Icc

/-- The closed square is compact. -/
theorem isCompact_closedSquare (r : ℝ) : IsCompact (closedSquare r) :=
  isCompact_Icc.reProdIm isCompact_Icc

/-- The closed square is bounded. -/
theorem isBounded_closedSquare (r : ℝ) : IsBounded (closedSquare r) :=
  (isCompact_closedSquare r).isBounded

/-- The open square is bounded. -/
theorem isBounded_openSquare (r : ℝ) : IsBounded (openSquare r) :=
  (isBounded_closedSquare r).subset (openSquare_subset_closedSquare r)

/-- The open square is convex. -/
theorem convex_openSquare (r : ℝ) : Convex ℝ (openSquare r) :=
  ((convex_Ioo (-r) r).linear_preimage reLm).inter ((convex_Ioo (-r) r).linear_preimage imLm)

/-- The closed square is convex. -/
theorem convex_closedSquare (r : ℝ) : Convex ℝ (closedSquare r) :=
  ((convex_Icc (-r) r).linear_preimage reLm).inter ((convex_Icc (-r) r).linear_preimage imLm)

/-- The open square `(-r, r)²` is nonempty for `r > 0`. -/
theorem openSquare_nonempty {r : ℝ} (hr : 0 < r) : (openSquare r).Nonempty :=
  ⟨0, by simp [mem_openSquare, hr]⟩

/-- The closed square `[-r, r]²` is nonempty for `r ≥ 0`. -/
theorem closedSquare_nonempty {r : ℝ} (hr : 0 ≤ r) : (closedSquare r).Nonempty :=
  ⟨0, by simp [mem_closedSquare, hr]⟩

/-- The closure of the open square `(-r, r)²` (`r > 0`) is the closed square `[-r, r]²`. -/
theorem closure_openSquare {r : ℝ} (hr : 0 < r) : closure (openSquare r) = closedSquare r := by
  rw [openSquare, closedSquare, closure_reProdIm, closure_Ioo (neg_lt_self hr).ne]

/-- Points of the closed square `[-r, r]²` have norm at most `√2 r`. -/
theorem norm_sq_le_of_mem_closedSquare {r : ℝ} {z : ℂ} (hz : z ∈ closedSquare r) :
    ‖z‖ ^ 2 ≤ 2 * r ^ 2 := by
  rw [Complex.sq_norm, normSq_apply]
  have h1 : z.re ^ 2 ≤ r ^ 2 := sq_le_sq' hz.1.1 hz.1.2
  have h2 : z.im ^ 2 ≤ r ^ 2 := sq_le_sq' hz.2.1 hz.2.2
  nlinarith

/-! ### Coordinates in `ℂ = ℝ²` -/

/-- The real inner product on `ℂ = ℝ²` is the dot product of the coordinates. -/
theorem inner_eq_re_mul_re_add_im_mul_im (z w : ℂ) : ⟪z, w⟫ = z.re * w.re + z.im * w.im := by
  rw [Complex.inner, mul_re, conj_re, conj_im]
  ring

/-- The first coordinate is the projection onto the direction `1`. -/
theorem inner_one_right_eq_re (z : ℂ) : ⟪z, 1⟫ = z.re := by
  simp

/-- The second coordinate is the projection onto the direction `I`. -/
theorem inner_I_right_eq_im (z : ℂ) : ⟪z, I⟫ = z.im := by
  simp

/-- The trace of an `ℝ`-linear map `Q` of `ℂ = ℝ²` is `Q₁₁ + Q₂₂ = ⟪Q 1, 1⟫ + ⟪Q I, I⟫`. -/
theorem trace_eq_inner_one_add_inner_I (Q : ℂ →L[ℝ] ℂ) :
    LinearMap.trace ℝ ℂ (Q : ℂ →ₗ[ℝ] ℂ) = ⟪Q 1, 1⟫ + ⟪Q I, I⟫ := by
  rw [LinearMap.trace_eq_sum_inner _ Complex.orthonormalBasisOneI, Fin.sum_univ_two]
  simp only [Complex.coe_orthonormalBasisOneI, Matrix.cons_val_zero, Matrix.cons_val_one,
    ContinuousLinearMap.coe_coe]
  rw [real_inner_comm (Q 1), real_inner_comm (Q I)]

/-- The diagonal directions `1 ± I` see twice the trace: `⟪Q (1 + I), 1 + I⟫ + ⟪Q (1 - I), 1 - I⟫
= 2 (Q₁₁ + Q₂₂)`. -/
theorem inner_one_add_I_add_inner_one_sub_I (Q : ℂ →L[ℝ] ℂ) :
    ⟪Q (1 + I), 1 + I⟫ + ⟪Q (1 - I), 1 - I⟫ = 2 * (⟪Q 1, 1⟫ + ⟪Q I, I⟫) := by
  simp only [map_add, map_sub, inner_add_left, inner_add_right, inner_sub_left, inner_sub_right]
  ring

/-- The trace of `Q` computed in the (unnormalized) diagonal directions `1 ± I`. -/
theorem trace_eq_inner_diagonals (Q : ℂ →L[ℝ] ℂ) :
    LinearMap.trace ℝ ℂ (Q : ℂ →ₗ[ℝ] ℂ) = (⟪Q (1 + I), 1 + I⟫ + ⟪Q (1 - I), 1 - I⟫) / 2 := by
  rw [inner_one_add_I_add_inner_one_sub_I, trace_eq_inner_one_add_inner_I]
  ring

/-! ### Projection bounds for ellipses -/

section Bounds

variable (e : Ellipsoid ℂ)

/-- If all points of an ellipse project into `[-1, 1]` in direction `ω`, then
`√⟪Q ω, ω⟫ ≤ 1 - |⟪c, ω⟫|`. -/
theorem sqrt_inner_shape_le_of_forall_mem_Icc {ω : ℂ}
    (h : ∀ x ∈ (e : Set ℂ), ⟪x, ω⟫ ∈ Icc (-1 : ℝ) 1) :
    √⟪e.shape ω, ω⟫ ≤ 1 - |⟪e.center, ω⟫| := by
  have hb : supportFunction (e : Set ℂ) ω ≤ 1 := supportFunction_le e.nonempty fun x hx ↦ (h x hx).2
  have ha : -1 ≤ lowerSupportFunction (e : Set ℂ) ω :=
    le_lowerSupportFunction e.nonempty fun x hx ↦ (h x hx).1
  rw [e.supportFunction_eq_sqrt] at hb
  rw [e.lowerSupportFunction_eq_sqrt] at ha
  have := abs_le.mpr (⟨by linarith, by linarith⟩ :
    -(1 - √⟪e.shape ω, ω⟫) ≤ ⟪e.center, ω⟫ ∧ ⟪e.center, ω⟫ ≤ 1 - √⟪e.shape ω, ω⟫)
  linarith

/-- If all points of an ellipse project into `(-1, 1)` in direction `ω`, then
`√⟪Q ω, ω⟫ < 1 - |⟪c, ω⟫|`. -/
theorem sqrt_inner_shape_lt_of_forall_mem_Ioo {ω : ℂ}
    (h : ∀ x ∈ (e : Set ℂ), ⟪x, ω⟫ ∈ Ioo (-1 : ℝ) 1) :
    √⟪e.shape ω, ω⟫ < 1 - |⟪e.center, ω⟫| := by
  have hb : supportFunction (e : Set ℂ) ω < 1 := by
    obtain ⟨x, hx, hxω⟩ := e.exists_inner_eq_supportFunction ω
    exact hxω ▸ (h x hx).2
  have ha : -1 < lowerSupportFunction (e : Set ℂ) ω := by
    obtain ⟨x, hx, hxω⟩ := e.exists_inner_eq_lowerSupportFunction ω
    exact hxω ▸ (h x hx).1
  rw [e.supportFunction_eq_sqrt] at hb
  rw [e.lowerSupportFunction_eq_sqrt] at ha
  have := abs_lt.mpr (⟨by linarith, by linarith⟩ :
    -(1 - √⟪e.shape ω, ω⟫) < ⟪e.center, ω⟫ ∧ ⟪e.center, ω⟫ < 1 - √⟪e.shape ω, ω⟫)
  linarith

/-- [Hägg, proof of Corollary 12]: an ellipse inside the open square `(-1, 1)²` satisfies
`√Q₁₁ < 1 - |c₁|`. -/
theorem sqrt_inner_shape_one_lt (h : (e : Set ℂ) ⊆ openSquare 1) :
    √⟪e.shape 1, 1⟫ < 1 - |e.center.re| := by
  simpa using sqrt_inner_shape_lt_of_forall_mem_Ioo e (ω := 1) fun x hx ↦ by
    simpa using (h hx).1

/-- [Hägg, proof of Corollary 12]: an ellipse inside the open square `(-1, 1)²` satisfies
`√Q₂₂ < 1 - |c₂|`. -/
theorem sqrt_inner_shape_I_lt (h : (e : Set ℂ) ⊆ openSquare 1) :
    √⟪e.shape I, I⟫ < 1 - |e.center.im| := by
  simpa using sqrt_inner_shape_lt_of_forall_mem_Ioo e (ω := I) fun x hx ↦ by
    simpa using (h hx).2

/-- [Hägg, proof of Corollary 13]: an ellipse inside the closed square `[-1, 1]²` satisfies
`√Q₁₁ ≤ 1 - |c₁|`. -/
theorem sqrt_inner_shape_one_le (h : (e : Set ℂ) ⊆ closedSquare 1) :
    √⟪e.shape 1, 1⟫ ≤ 1 - |e.center.re| := by
  simpa using sqrt_inner_shape_le_of_forall_mem_Icc e (ω := 1) fun x hx ↦ by
    simpa using (h hx).1

/-- [Hägg, proof of Corollary 13]: an ellipse inside the closed square `[-1, 1]²` satisfies
`√Q₂₂ ≤ 1 - |c₂|`. -/
theorem sqrt_inner_shape_I_le (h : (e : Set ℂ) ⊆ closedSquare 1) :
    √⟪e.shape I, I⟫ ≤ 1 - |e.center.im| := by
  simpa using sqrt_inner_shape_le_of_forall_mem_Icc e (ω := I) fun x hx ↦ by
    simpa using (h hx).2

/-- If an ellipse contains the points `z` and `-z`, then `⟪z, ω⟫ + |⟪c, ω⟫| ≤ √⟪Q ω, ω⟫`. -/
theorem inner_add_abs_inner_le_sqrt_inner_shape {z : ℂ} (hz : z ∈ (e : Set ℂ))
    (hz' : -z ∈ (e : Set ℂ)) (ω : ℂ) :
    ⟪z, ω⟫ + |⟪e.center, ω⟫| ≤ √⟪e.shape ω, ω⟫ := by
  have hb := inner_le_supportFunction (ω := ω) e.isBounded hz
  have ha := lowerSupportFunction_le_inner (ω := ω) e.isBounded hz'
  rw [e.supportFunction_eq_sqrt] at hb
  rw [e.lowerSupportFunction_eq_sqrt, inner_neg_left] at ha
  rcases abs_cases ⟪e.center, ω⟫ with ⟨h, -⟩ | ⟨h, -⟩ <;> linarith

/-- [Hägg, proof of Corollary 12], diagonal `1 + I`: an ellipse containing `[-δ, δ]²` satisfies
`2 δ + |⟪c, 1 + I⟫| ≤ √⟪Q (1 + I), 1 + I⟫` (i.e. `δ √2 + |⟪c, ω₊⟫| ≤ √⟪Q ω₊, ω₊⟫` for the unit
vector `ω₊ = (1 + I)/√2`). -/
theorem two_mul_add_abs_inner_le_sqrt_inner_shape_one_add_I {δ : ℝ} (hδ : 0 ≤ δ)
    (h : closedSquare δ ⊆ e) :
    2 * δ + |⟪e.center, 1 + I⟫| ≤ √⟪e.shape (1 + I), 1 + I⟫ := by
  have hz : (⟨δ, δ⟩ : ℂ) ∈ closedSquare δ := by simp [mem_closedSquare, hδ]
  have hz' : -(⟨δ, δ⟩ : ℂ) ∈ closedSquare δ := by simp [mem_closedSquare, hδ]
  have := inner_add_abs_inner_le_sqrt_inner_shape e (h hz) (h hz') (1 + I)
  rw [inner_eq_re_mul_re_add_im_mul_im] at this
  simp only [add_re, one_re, I_re, add_im, one_im, I_im] at this
  linarith

/-- [Hägg, proof of Corollary 12], diagonal `1 - I`: an ellipse containing `[-δ, δ]²` satisfies
`2 δ + |⟪c, 1 - I⟫| ≤ √⟪Q (1 - I), 1 - I⟫`. -/
theorem two_mul_add_abs_inner_le_sqrt_inner_shape_one_sub_I {δ : ℝ} (hδ : 0 ≤ δ)
    (h : closedSquare δ ⊆ e) :
    2 * δ + |⟪e.center, 1 - I⟫| ≤ √⟪e.shape (1 - I), 1 - I⟫ := by
  have hz : (⟨δ, -δ⟩ : ℂ) ∈ closedSquare δ := by simp [mem_closedSquare, hδ]
  have hz' : -(⟨δ, -δ⟩ : ℂ) ∈ closedSquare δ := by simp [mem_closedSquare, hδ]
  have := inner_add_abs_inner_le_sqrt_inner_shape e (h hz) (h hz') (1 - I)
  rw [inner_eq_re_mul_re_add_im_mul_im] at this
  simp only [sub_re, one_re, I_re, sub_im, one_im, I_im] at this
  linarith

/-- [Hägg, proof of Corollary 12]: an ellipse inside the open square `(-1, 1)²` has
`tr Q < 2`. -/
theorem trace_shape_lt_two (h : (e : Set ℂ) ⊆ openSquare 1) :
    LinearMap.trace ℝ ℂ (e.shape : ℂ →ₗ[ℝ] ℂ) < 2 := by
  have h1 := (Real.sqrt_lt' one_pos).mp
    ((sqrt_inner_shape_one_lt e h).trans_le (by linarith [abs_nonneg e.center.re]))
  have h2 := (Real.sqrt_lt' one_pos).mp
    ((sqrt_inner_shape_I_lt e h).trans_le (by linarith [abs_nonneg e.center.im]))
  rw [trace_eq_inner_one_add_inner_I]
  linarith

/-- [Hägg, proof of Remark 14]: an ellipse inside the closed square `[-1, 1]²` has
`tr Q ≤ (1 - |c₁|)² + (1 - |c₂|)²`. -/
theorem trace_shape_le (h : (e : Set ℂ) ⊆ closedSquare 1) :
    LinearMap.trace ℝ ℂ (e.shape : ℂ →ₗ[ℝ] ℂ) ≤
      (1 - |e.center.re|) ^ 2 + (1 - |e.center.im|) ^ 2 := by
  have h1 := (Real.sqrt_le_left ((Real.sqrt_nonneg _).trans (sqrt_inner_shape_one_le e h))).mp
    (sqrt_inner_shape_one_le e h)
  have h2 := (Real.sqrt_le_left ((Real.sqrt_nonneg _).trans (sqrt_inner_shape_I_le e h))).mp
    (sqrt_inner_shape_I_le e h)
  rw [trace_eq_inner_one_add_inner_I]
  linarith

/-- [Hägg, proof of Corollary 13]: an ellipse inside the closed square `[-1, 1]²` has
`tr Q ≤ 2`. -/
theorem trace_shape_le_two (h : (e : Set ℂ) ⊆ closedSquare 1) :
    LinearMap.trace ℝ ℂ (e.shape : ℂ →ₗ[ℝ] ℂ) ≤ 2 := by
  have h1 := (Real.sqrt_nonneg _).trans (sqrt_inner_shape_one_le e h)
  have h2 := (Real.sqrt_nonneg _).trans (sqrt_inner_shape_I_le e h)
  have := trace_shape_le e h
  nlinarith [abs_nonneg e.center.re, abs_nonneg e.center.im]

/-- [Hägg, proof of Corollary 12]: an ellipse containing the closed square `[-δ, δ]²` has
`tr Q ≥ 4 δ²`. -/
theorem four_mul_sq_le_trace_shape {δ : ℝ} (hδ : 0 ≤ δ) (h : closedSquare δ ⊆ e) :
    4 * δ ^ 2 ≤ LinearMap.trace ℝ ℂ (e.shape : ℂ →ₗ[ℝ] ℂ) := by
  have hp := two_mul_add_abs_inner_le_sqrt_inner_shape_one_add_I e hδ h
  have hm := two_mul_add_abs_inner_le_sqrt_inner_shape_one_sub_I e hδ h
  have hp' := (Real.le_sqrt (by positivity) (e.inner_shape_nonneg _)).mp
    ((le_add_of_nonneg_right (abs_nonneg _)).trans hp)
  have hm' := (Real.le_sqrt (by positivity) (e.inner_shape_nonneg _)).mp
    ((le_add_of_nonneg_right (abs_nonneg _)).trans hm)
  rw [trace_eq_inner_diagonals]
  linarith

end Bounds

/-! ### Disks -/

/-- The closed unit disk as an ellipse: center `0`, linear part the identity. -/
def unitDiskEllipsoid : Ellipsoid ℂ := ⟨0, ContinuousLinearEquiv.refl ℝ ℂ⟩

/-- The center of the unit disk is `0`. -/
@[simp] theorem unitDiskEllipsoid_center : unitDiskEllipsoid.center = 0 := rfl

/-- The unit disk ellipse is the closed unit ball of `ℂ`. -/
theorem coe_unitDiskEllipsoid : (unitDiskEllipsoid : Set ℂ) = closedBall 0 1 := by
  simp [unitDiskEllipsoid, Ellipsoid.coe_def]

/-- The shape of the unit disk ellipse is the identity. -/
theorem unitDiskEllipsoid_shape : unitDiskEllipsoid.shape = ContinuousLinearMap.id ℝ ℂ := by
  simp [unitDiskEllipsoid, Ellipsoid.shape, ContinuousLinearMap.adjoint_id]

/-- The closed disk of radius `r > 0` about `0` as an ellipse. -/
def diskEllipsoid (r : ℝ) (hr : 0 < r) : Ellipsoid ℂ :=
  ⟨0, ContinuousLinearEquiv.smulLeft (Units.mk0 r hr.ne')⟩

/-- The disk ellipse of radius `r` is the closed ball of radius `r` about `0`. -/
theorem coe_diskEllipsoid {r : ℝ} (hr : 0 < r) :
    (diskEllipsoid r hr : Set ℂ) = closedBall 0 r := by
  ext z
  simp only [Ellipsoid.coe_def, diskEllipsoid, zero_add, ContinuousLinearEquiv.smulLeft_apply_apply,
    Units.smul_def, Units.val_mk0, mem_image, mem_closedBall, dist_zero_right]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [norm_smul, Real.norm_of_nonneg hr.le]
    exact mul_le_of_le_one_right hr.le hy
  · intro hz
    refine ⟨r⁻¹ • z, ?_, by rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]⟩
    rw [norm_smul, norm_inv, Real.norm_of_nonneg hr.le, inv_mul_le_iff₀ hr, mul_one]
    exact hz

/-- A closed disk of radius `r < 1` about `0` lies in the open square `(-1, 1)²`. -/
theorem closedBall_subset_openSquare {r : ℝ} (hr : r < 1) :
    closedBall (0 : ℂ) r ⊆ openSquare 1 := by
  intro z hz
  rw [mem_closedBall, dist_zero_right] at hz
  have h1 := (abs_re_le_norm z).trans hz
  have h2 := (abs_im_le_norm z).trans hz
  exact ⟨abs_lt.mp (h1.trans_lt hr), abs_lt.mp (h2.trans_lt hr)⟩

/-- The closed unit disk lies in the closed square `[-1, 1]²`. -/
theorem closedBall_subset_closedSquare : closedBall (0 : ℂ) 1 ⊆ closedSquare 1 := by
  intro z hz
  rw [mem_closedBall, dist_zero_right] at hz
  exact ⟨abs_le.mp ((abs_re_le_norm z).trans hz), abs_le.mp ((abs_im_le_norm z).trans hz)⟩

/-- The closed square `[-δ, δ]²` lies in the closed disk of radius `r` if `2 δ² ≤ r²`. -/
theorem closedSquare_subset_closedBall {δ r : ℝ} (hr : 0 ≤ r) (h : 2 * δ ^ 2 ≤ r ^ 2) :
    closedSquare δ ⊆ closedBall (0 : ℂ) r := by
  intro z hz
  rw [mem_closedBall, dist_zero_right]
  have := norm_sq_le_of_mem_closedSquare hz
  nlinarith [norm_nonneg z]

private theorem lt_one_div_sqrt_two_iff {δ : ℝ} (hδ : 0 ≤ δ) : δ < 1 / √2 ↔ 2 * δ ^ 2 < 1 := by
  rw [one_div, ← Real.sqrt_inv, Real.lt_sqrt hδ]
  constructor <;> intro h <;> linarith

private theorem le_one_div_sqrt_two_iff {δ : ℝ} (hδ : 0 ≤ δ) : δ ≤ 1 / √2 ↔ 2 * δ ^ 2 ≤ 1 := by
  rw [one_div, ← Real.sqrt_inv, Real.le_sqrt hδ (by norm_num)]
  constructor <;> intro h <;> linarith

/-! ### The square threshold -/

/-- **Two concentric squares**, geometric part [Hägg, Corollary 12]: for `δ > 0`, there is an
ellipse `𝓔` with `closure (-δ, δ)² ⊆ 𝓔 ⊆ (-1, 1)²` iff `δ < 1/√2`. -/
theorem exists_ellipsoid_openSquare_iff {δ : ℝ} (hδ : 0 < δ) :
    (∃ e : Ellipsoid ℂ, closure (openSquare δ) ⊆ e ∧ (e : Set ℂ) ⊆ openSquare 1) ↔
      δ < 1 / √2 := by
  rw [lt_one_div_sqrt_two_iff hδ.le, closure_openSquare hδ]
  constructor
  · rintro ⟨e, h₀, h₁⟩
    have := trace_shape_lt_two e h₁
    have := four_mul_sq_le_trace_shape e hδ.le h₀
    linarith
  · intro h
    -- a disk of radius `r` with `2 δ² < r² < 1`
    obtain ⟨r, hr₁, hr₂⟩ : ∃ r : ℝ, √(2 * δ ^ 2) < r ∧ r < 1 :=
      exists_between ((Real.sqrt_lt' one_pos).mpr (by linarith))
    have hr : 0 < r := (Real.sqrt_nonneg _).trans_lt hr₁
    refine ⟨diskEllipsoid r hr, ?_, ?_⟩
    · rw [coe_diskEllipsoid hr]
      refine closedSquare_subset_closedBall hr.le ?_
      have := (Real.sqrt_lt' hr).mp hr₁
      linarith
    · rw [coe_diskEllipsoid hr]
      exact closedBall_subset_openSquare hr₂

/-- **Support in the closed outer square**, geometric part [Hägg, Corollary 13]: for `δ ≥ 0`,
there is an ellipse `𝓔` with `[-δ, δ]² ⊆ 𝓔 ⊆ [-1, 1]²` iff `δ ≤ 1/√2`. -/
theorem exists_ellipsoid_closedSquare_iff {δ : ℝ} (hδ : 0 ≤ δ) :
    (∃ e : Ellipsoid ℂ, closedSquare δ ⊆ e ∧ (e : Set ℂ) ⊆ closedSquare 1) ↔ δ ≤ 1 / √2 := by
  rw [le_one_div_sqrt_two_iff hδ]
  constructor
  · rintro ⟨e, h₀, h₁⟩
    have := trace_shape_le_two e h₁
    have := four_mul_sq_le_trace_shape e hδ h₀
    linarith
  · intro h
    refine ⟨unitDiskEllipsoid, ?_, ?_⟩
    · rw [coe_unitDiskEllipsoid]
      exact closedSquare_subset_closedBall zero_le_one (by linarith)
    · rw [coe_unitDiskEllipsoid]
      exact closedBall_subset_closedSquare

/-- [Hägg, Remark 14]: at the endpoint `δ = 1/√2`, every ellipse `𝓔` with
`[-1/√2, 1/√2]² ⊆ 𝓔 ⊆ [-1, 1]²` has center `c = 0` and shape `Q = 1` (i.e. `Q₁₁ = Q₂₂ = 1`,
`Q₁₂ = 0`). -/
theorem center_eq_zero_and_shape_eq_id_of_closedSquare_subset_of_subset_closedSquare
    (e : Ellipsoid ℂ) (h₀ : closedSquare (1 / √2) ⊆ e) (h₁ : (e : Set ℂ) ⊆ closedSquare 1) :
    e.center = 0 ∧ e.shape = ContinuousLinearMap.id ℝ ℂ := by
  have hδ : (0 : ℝ) ≤ 1 / √2 := by positivity
  have h2δ : 2 * (1 / √2) = √2 := by
    field_simp
    rw [Real.sq_sqrt zero_le_two]
  -- coordinate directions
  have hs₁ := sqrt_inner_shape_one_le e h₁
  have hs₂ := sqrt_inner_shape_I_le e h₁
  have hQ₁₁ := Real.sq_sqrt (e.inner_shape_nonneg 1)
  have hQ₂₂ := Real.sq_sqrt (e.inner_shape_nonneg I)
  have hs₁0 := Real.sqrt_nonneg ⟪e.shape 1, 1⟫
  have hs₂0 := Real.sqrt_nonneg ⟪e.shape I, I⟫
  -- diagonal directions
  have hp := two_mul_add_abs_inner_le_sqrt_inner_shape_one_add_I e hδ h₀
  have hm := two_mul_add_abs_inner_le_sqrt_inner_shape_one_sub_I e hδ h₀
  rw [h2δ] at hp hm
  have hp' := (Real.sqrt_le_sqrt_iff (e.inner_shape_nonneg _)).mp
    ((le_add_of_nonneg_right (abs_nonneg _)).trans hp)
  have hm' := (Real.sqrt_le_sqrt_iff (e.inner_shape_nonneg _)).mp
    ((le_add_of_nonneg_right (abs_nonneg _)).trans hm)
  have hdiag := inner_one_add_I_add_inner_one_sub_I e.shape
  -- `Q₁₁ = Q₂₂ = 1`
  have hQ₁₁le : ⟪e.shape 1, 1⟫ ≤ 1 := by nlinarith [abs_nonneg e.center.re]
  have hQ₂₂le : ⟪e.shape I, I⟫ ≤ 1 := by nlinarith [abs_nonneg e.center.im]
  have hQ₁₁ : ⟪e.shape 1, 1⟫ = 1 := by linarith
  have hQ₂₂ : ⟪e.shape I, I⟫ = 1 := by linarith
  -- `c = 0`
  have hc₁ : |e.center.re| ≤ 0 := by
    rw [hQ₁₁, Real.sqrt_one] at hs₁
    linarith
  have hc₂ : |e.center.im| ≤ 0 := by
    rw [hQ₂₂, Real.sqrt_one] at hs₂
    linarith
  have hc : e.center = 0 := Complex.ext (abs_nonpos_iff.mp hc₁) (abs_nonpos_iff.mp hc₂)
  -- `Q₁₂ = 0`
  have hsymm : ⟪e.shape I, 1⟫ = ⟪e.shape 1, I⟫ :=
    (e.shape_isSelfAdjoint.isSymmetric I 1).trans (real_inner_comm _ _)
  have hexp : ∀ s : ℝ, ⟪e.shape (1 + s • I), 1 + s • I⟫ =
      ⟪e.shape 1, 1⟫ + 2 * s * ⟪e.shape 1, I⟫ + s ^ 2 * ⟪e.shape I, I⟫ := by
    intro s
    simp only [map_add, map_smul, inner_add_left, inner_add_right, real_inner_smul_left,
      real_inner_smul_right, hsymm]
    ring
  have hp'' := hexp 1
  have hm'' := hexp (-1)
  simp only [one_smul, neg_smul, ← sub_eq_add_neg] at hp'' hm''
  have hQ₁₂ : ⟪e.shape 1, I⟫ = 0 := by nlinarith
  -- hence `Q 1 = 1`, `Q I = I` and `Q = 1`
  have hQ1 : e.shape 1 = 1 := Complex.ext (by simpa using hQ₁₁) (by simpa using hQ₁₂)
  have hQI : e.shape I = I :=
    Complex.ext (by simpa [hQ₁₂] using hsymm) (by simpa using hQ₂₂)
  refine ⟨hc, ContinuousLinearMap.ext fun z ↦ ?_⟩
  have hz : z = z.re • (1 : ℂ) + z.im • I := by
    rw [Complex.real_smul, Complex.real_smul, mul_one, Complex.re_add_im]
  rw [ContinuousLinearMap.id_apply]
  conv_lhs => rw [hz]
  rw [map_add, map_smul, map_smul, hQ1, hQI, ← hz]

/-- **The endpoint** [Hägg, Remark 14]: the closed unit disk is the only ellipse `𝓔` with
`[-1/√2, 1/√2]² ⊆ 𝓔 ⊆ [-1, 1]²`. -/
theorem eq_closedBall_of_closedSquare_subset_of_subset_closedSquare (e : Ellipsoid ℂ)
    (h₀ : closedSquare (1 / √2) ⊆ e) (h₁ : (e : Set ℂ) ⊆ closedSquare 1) :
    (e : Set ℂ) = Metric.closedBall 0 1 := by
  obtain ⟨hc, hQ⟩ :=
    center_eq_zero_and_shape_eq_id_of_closedSquare_subset_of_subset_closedSquare e h₀ h₁
  rw [← coe_unitDiskEllipsoid]
  exact Ellipsoid.toSet_eq_of_center_shape (hc.trans unitDiskEllipsoid_center.symm)
    (hQ.trans unitDiskEllipsoid_shape.symm)

end LeanestEllipse
