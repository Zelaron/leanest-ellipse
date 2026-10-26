import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Topology.Connected.Clopen

/-!
# Schur complements with respect to an orthogonal decomposition

Let `K` be a closed subspace of a Hilbert space `E` and let `T : E →L[𝕜] E` be an operator whose
compression to `K` is a scalar `c ≠ 0`, i.e. `P_K (T x) = c • x` for `x ∈ K`.  With respect to
`E = K ⊕ Kᗮ` the operator `T` has the block form `[[c, Y], [Z, D]]`, and its *Schur complement*
is the operator `S = D - c⁻¹ Z Y` on `Kᗮ`; we define it as
`K.schurComplement T c = P_{Kᗮ} (T - c⁻¹ T P_K T)|_{Kᗮ}`.

The basic identity is the completing-the-square formula `T (n - c⁻¹ P_K T n) = S n` for `n ∈ Kᗮ`,
from which we deduce that `T` is invertible iff `S` is, and that `⟪S n, n⟫ = ⟪T v, v⟫` with
`v = n - c⁻¹ P_K T n`.  For self-adjoint `T` and real `c`, `S` is self-adjoint.

We then study the family `S(t) = K.schurComplement (T - t) (α - t)` for a self-adjoint `T` with
compression `α` on `K`, where `t` is a real parameter different from `α`.  We show that `S(t)`
depends continuously on `t`, compute its quadratic form, and show that if `P_K T` is bounded below
on `Kᗮ` then `S(t) ≥ 0` for `t` slightly larger than `α` and `S(t) ≤ 0` for `t` slightly smaller
than `α`.  Together with the fact that an invertible self-adjoint continuous path cannot change sign
(`IsPreconnected.isStrictlyPositive_of_continuousOn`), this is the operator-theoretic core of
[Hägg, Theorem 10].

## Main results

* `IsPreconnected.isStrictlyPositive_of_continuousOn`: in a C⋆-algebra, a continuous path of
  invertible self-adjoint elements over a preconnected set which is strictly positive at one point
  is strictly positive everywhere.
* `Submodule.schurComplement`, `Submodule.apply_sub_smul_starProjection_eq_schurComplement`,
  `Submodule.isUnit_schurComplement_iff`, `Submodule.inner_schurComplement_apply_self`,
  `Submodule.isSelfAdjoint_schurComplement`.
* `Submodule.schurComplement_sub_smul_one`, `Submodule.continuousOn_schurComplement_sub_smul_one`,
  `Submodule.re_inner_schurComplement_sub_smul_one_apply_self`.
* `Submodule.exists_pos_schurComplement_sign`: the signs of `S(t)` near the pole `t = α`.
* `Submodule.exists_pos_mul_norm_le_norm_starProjection_apply`: if `T - α` maps `K` onto `Kᗮ`,
  then `P_K T` is bounded below on `Kᗮ`.

## References

* C. Hägg, *An ellipse criterion for exact nonuniqueness in the planar interior Radon problem*.
-/

noncomputable section

open Set

/-! ### Sign propagation for invertible self-adjoint paths -/

section SignPropagation

variable {A X : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [TopologicalSpace X]

/-- Nonnegativity is an open condition along a continuous path of invertible self-adjoint
elements. -/
theorem isOpen_setOf_nonneg_of_continuous [Nontrivial A] {f : X → A} (hf : Continuous f)
    (hsa : ∀ x, IsSelfAdjoint (f x)) (hu : ∀ x, IsUnit (f x)) : IsOpen {x | 0 ≤ f x} := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  have hxpos : IsStrictlyPositive (f x) := (hu x).isStrictlyPositive hx
  obtain ⟨r, hr, hrle⟩ : ∃ r > 0, algebraMap ℝ A r ≤ f x :=
    (CFC.exists_pos_algebraMap_le_iff (f x) hxpos.isSelfAdjoint).2 fun s hs ↦
      hxpos.spectrum_pos hs
  refine Filter.mem_of_superset (hf.continuousAt.preimage_mem_nhds (Metric.ball_mem_nhds _ hr))
    fun y hy ↦ ?_
  have hynorm : ‖f y - f x‖ < r := by simpa [dist_eq_norm] using hy
  have hdiff : -(algebraMap ℝ A ‖f y - f x‖) ≤ f y - f x :=
    ((hsa y).sub (hsa x)).neg_algebraMap_norm_le_self
  have hscalar : 0 ≤ algebraMap ℝ A (r - ‖f y - f x‖) := by
    rw [Algebra.algebraMap_eq_smul_one]
    exact smul_nonneg (sub_pos.mpr hynorm).le zero_le_one
  refine hscalar.trans ?_
  calc algebraMap ℝ A (r - ‖f y - f x‖) = algebraMap ℝ A r + -(algebraMap ℝ A ‖f y - f x‖) := by
        rw [map_sub, sub_eq_add_neg]
    _ ≤ f x + (f y - f x) := add_le_add hrle hdiff
    _ = f y := add_sub_cancel _ _

/-- **Sign propagation.**  In a C⋆-algebra, a continuous path of invertible self-adjoint elements
over a preconnected set which is strictly positive at one point is strictly positive at every
point. -/
theorem IsPreconnected.isStrictlyPositive_of_continuousOn [Nontrivial A] {s : Set X}
    (hs : IsPreconnected s) {f : X → A} (hf : ContinuousOn f s)
    (hsa : ∀ x ∈ s, IsSelfAdjoint (f x)) (hu : ∀ x ∈ s, IsUnit (f x)) {x₀ : X} (hx₀ : x₀ ∈ s)
    (h₀ : IsStrictlyPositive (f x₀)) : ∀ x ∈ s, IsStrictlyPositive (f x) := by
  have : PreconnectedSpace s := Subtype.preconnectedSpace hs
  let g : s → A := fun x ↦ f x
  have hg : Continuous g := hf.domRestrict
  have hclosed : IsClosed {x : s | 0 ≤ g x} := CStarAlgebra.isClosed_nonneg.preimage hg
  have hopen : IsOpen {x : s | 0 ≤ g x} :=
    isOpen_setOf_nonneg_of_continuous hg (fun x ↦ hsa x x.2) fun x ↦ hu x x.2
  have huniv : {x : s | 0 ≤ g x} = univ :=
    IsClopen.eq_univ ⟨hclosed, hopen⟩ ⟨⟨x₀, hx₀⟩, h₀.nonneg⟩
  intro x hx
  refine (hu x hx).isStrictlyPositive ?_
  have : (⟨x, hx⟩ : s) ∈ {x : s | 0 ≤ g x} := huniv ▸ mem_univ _
  exact this

end SignPropagation

/-! ### The Schur complement -/

namespace Submodule

section Schur

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable (K : Submodule 𝕜 E) [K.HasOrthogonalProjection]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

/-- The **Schur complement** of `T` with respect to the decomposition `E = K ⊕ Kᗮ` and the scalar
`c`: the operator `P_{Kᗮ} (T - c⁻¹ T P_K T)` on `Kᗮ`.  If the compression of `T` to `K` is `c • 1`
with `c ≠ 0`, this is the usual Schur complement `D - Z c⁻¹ Y` of the block operator
`[[c, Y], [Z, D]]` (see `Submodule.apply_sub_smul_starProjection_eq_schurComplement`). -/
def schurComplement (T : E →L[𝕜] E) (c : 𝕜) : Kᗮ →L[𝕜] Kᗮ :=
  Kᗮ.orthogonalProjectionOnto ∘L (T - c⁻¹ • (T ∘L K.starProjection ∘L T)) ∘L Kᗮ.subtypeL

/-- The Schur complement, evaluated in the ambient space. -/
theorem coe_schurComplement_apply (T : E →L[𝕜] E) (c : 𝕜) (n : Kᗮ) :
    (K.schurComplement T c n : E) = Kᗮ.starProjection (T n - c⁻¹ • T (K.starProjection (T n))) :=
  rfl

variable {K}

/-- **Completing the square**: if the compression of `T` to `K` is the scalar `c ≠ 0`, then
`T (n - c⁻¹ P_K T n) = S n` for `n ∈ Kᗮ`, where `S` is the Schur complement. -/
theorem apply_sub_smul_starProjection_eq_schurComplement {T : E →L[𝕜] E} {c : 𝕜} (hc : c ≠ 0)
    (hT : ∀ x ∈ K, K.starProjection (T x) = c • x) (n : Kᗮ) :
    T ((n : E) - c⁻¹ • K.starProjection (T n)) = K.schurComplement T c n := by
  have hmem : T n - c⁻¹ • T (K.starProjection (T n)) ∈ Kᗮ := by
    rw [← K.starProjection_apply_eq_zero_iff, map_sub, map_smul,
      hT _ (K.starProjection_apply_mem _), smul_smul, inv_mul_cancel₀ hc, one_smul, sub_self]
  rw [coe_schurComplement_apply, (Kᗮ.starProjection_eq_self_iff).mpr hmem, map_sub, map_smul]

private theorem eq_sub_smul_of_starProjection_apply_eq_zero {T : E →L[𝕜] E} {c : 𝕜} (hc : c ≠ 0)
    (hT : ∀ x ∈ K, K.starProjection (T x) = c • x) {v : E} (hv : K.starProjection (T v) = 0) :
    v = Kᗮ.starProjection v - c⁻¹ • K.starProjection (T (Kᗮ.starProjection v)) := by
  have hsplit := K.starProjection_add_starProjection_orthogonal v
  have h1 : K.starProjection (T v) =
      c • K.starProjection v + K.starProjection (T (Kᗮ.starProjection v)) := by
    conv_lhs => rw [← hsplit]
    rw [map_add, map_add, hT _ (K.starProjection_apply_mem _)]
  rw [hv, eq_comm, add_eq_zero_iff_eq_neg] at h1
  have h2 : K.starProjection v = -(c⁻¹ • K.starProjection (T (Kᗮ.starProjection v))) := by
    rw [← smul_neg, ← h1, smul_smul, inv_mul_cancel₀ hc, one_smul]
  conv_lhs => rw [← hsplit, h2]
  abel

/-- If the compression of `T` to `K` is the scalar `c ≠ 0`, then `T` is invertible iff its Schur
complement is invertible. -/
theorem isUnit_schurComplement_iff [CompleteSpace E] {T : E →L[𝕜] E} {c : 𝕜} (hc : c ≠ 0)
    (hT : ∀ x ∈ K, K.starProjection (T x) = c • x) :
    IsUnit (K.schurComplement T c) ↔ IsUnit T := by
  rw [ContinuousLinearMap.isUnit_iff_bijective, ContinuousLinearMap.isUnit_iff_bijective]
  have hschur := apply_sub_smul_starProjection_eq_schurComplement hc hT
  constructor
  · rintro ⟨hinj, hsurj⟩
    constructor
    · intro v₁ v₂ hv
      rw [← sub_eq_zero]
      set v := v₁ - v₂ with hv_def
      have hTv : T v = 0 := by rw [hv_def, map_sub, hv, sub_self]
      have hdec := eq_sub_smul_of_starProjection_apply_eq_zero hc hT (v := v)
        (by rw [hTv, map_zero])
      set n : Kᗮ := Kᗮ.orthogonalProjectionOnto v with hn
      have hn' : (n : E) = Kᗮ.starProjection v := rfl
      have hSn : K.schurComplement T c n = 0 := by
        apply Subtype.ext
        rw [← hschur n, hn', ← hdec, hTv, ZeroMemClass.coe_zero]
      have hn0 : n = 0 := hinj (by rw [hSn, map_zero])
      rw [hdec, ← hn', hn0, ZeroMemClass.coe_zero, map_zero, map_zero, smul_zero, sub_zero]
    · intro y
      have hw : y - c⁻¹ • T (K.starProjection y) ∈ Kᗮ := by
        rw [← K.starProjection_apply_eq_zero_iff, map_sub, map_smul,
          hT _ (K.starProjection_apply_mem _), smul_smul, inv_mul_cancel₀ hc, one_smul,
          sub_self]
      obtain ⟨n, hn⟩ := hsurj ⟨_, hw⟩
      refine ⟨((n : E) - c⁻¹ • K.starProjection (T n)) + c⁻¹ • K.starProjection y, ?_⟩
      rw [map_add, hschur n, hn, map_smul]
      exact sub_add_cancel _ _
  · rintro ⟨hinj, hsurj⟩
    constructor
    · intro n₁ n₂ hn
      have h := congrArg (fun n : Kᗮ ↦ (n : E)) hn
      simp only [← hschur] at h
      have h' := hinj h
      have := congrArg Kᗮ.starProjection h'
      rw [map_sub, map_sub, map_smul, map_smul, Kᗮ.starProjection_eq_self_iff.mpr n₁.2,
        Kᗮ.starProjection_eq_self_iff.mpr n₂.2,
        (Kᗮ.starProjection_apply_eq_zero_iff).mpr
          (K.le_orthogonal_orthogonal (K.starProjection_apply_mem _)),
        (Kᗮ.starProjection_apply_eq_zero_iff).mpr
          (K.le_orthogonal_orthogonal (K.starProjection_apply_mem _)),
        smul_zero, sub_zero, sub_zero] at this
      exact Subtype.ext this
    · intro w
      obtain ⟨v, hv⟩ := hsurj w
      have hKv : K.starProjection (T v) = 0 := by
        rw [hv]
        exact (K.starProjection_apply_eq_zero_iff).mpr w.2
      refine ⟨Kᗮ.orthogonalProjectionOnto v, Subtype.ext ?_⟩
      rw [← hschur, coe_orthogonalProjectionOnto_apply,
        ← eq_sub_smul_of_starProjection_apply_eq_zero hc hT hKv, hv]

/-- The quadratic form of the Schur complement: `⟪S n, n⟫ = ⟪T v, v⟫` with
`v = n - c⁻¹ P_K T n`. -/
theorem inner_schurComplement_apply_self {T : E →L[𝕜] E} {c : 𝕜} (hc : c ≠ 0)
    (hT : ∀ x ∈ K, K.starProjection (T x) = c • x) (n : Kᗮ) :
    ⟪(K.schurComplement T c n : E), n⟫ =
      ⟪T ((n : E) - c⁻¹ • K.starProjection (T n)), (n : E) - c⁻¹ • K.starProjection (T n)⟫ := by
  rw [apply_sub_smul_starProjection_eq_schurComplement hc hT, inner_sub_right, inner_smul_right,
    inner_left_of_mem_orthogonal (K.starProjection_apply_mem _) (K.schurComplement T c n).2,
    mul_zero, sub_zero]

/-- The Schur complement of a self-adjoint operator with respect to a real scalar is
self-adjoint. -/
theorem isSelfAdjoint_schurComplement [CompleteSpace E] {T : E →L[𝕜] E} (hT : IsSelfAdjoint T)
    {c : 𝕜} (hc : IsSelfAdjoint c) : IsSelfAdjoint (K.schurComplement T c) := by
  have hc' : (starRingEnd 𝕜) c⁻¹ = c⁻¹ := by rw [map_inv₀, starRingEnd_apply, hc.star_eq]
  have hTs : ∀ x y : E, ⟪T x, y⟫ = ⟪x, T y⟫ := hT.isSymmetric
  have hX : ∀ x y : E, ⟪T x - c⁻¹ • T (K.starProjection (T x)), y⟫ =
      ⟪x, T y - c⁻¹ • T (K.starProjection (T y))⟫ := by
    intro x y
    rw [inner_sub_left, inner_smul_left, hc', inner_sub_right, inner_smul_right,
      hTs x y, hTs (K.starProjection (T x)) y, K.inner_starProjection_left_eq_right,
      hTs x (K.starProjection (T y))]
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro n n'
  change ⟪(K.schurComplement T c n : E), n'⟫ = ⟪(n : E), K.schurComplement T c n'⟫
  rw [coe_schurComplement_apply, coe_schurComplement_apply,
    Kᗮ.inner_starProjection_left_eq_right, ← Kᗮ.inner_starProjection_left_eq_right (n : E),
    Kᗮ.starProjection_eq_self_iff.mpr n.2, Kᗮ.starProjection_eq_self_iff.mpr n'.2, hX]

end Schur

/-! ### The shifted Schur complement of a self-adjoint operator -/

section Shifted

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable {K : Submodule 𝕜 E} [K.HasOrthogonalProjection]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

open RCLike

/-- The Schur complement of `T - t` with respect to `c - t`, in block form:
`S(t) = D - t - (c - t)⁻¹ Z Y` where `D = P_{Kᗮ} T|_{Kᗮ}` and `Z Y = P_{Kᗮ} T P_K T|_{Kᗮ}`. -/
theorem schurComplement_sub_smul_one (T : E →L[𝕜] E) (c t : 𝕜) :
    K.schurComplement (T - t • 1) (c - t) =
      Kᗮ.orthogonalProjectionOnto ∘L T ∘L Kᗮ.subtypeL - t • 1 -
        (c - t)⁻¹ • (Kᗮ.orthogonalProjectionOnto ∘L T ∘L K.starProjection ∘L T ∘L
          Kᗮ.subtypeL) := by
  ext n
  have hn : K.starProjection (n : E) = 0 := (K.starProjection_apply_eq_zero_iff).mpr n.2
  have hKK : Kᗮ.starProjection (K.starProjection (T n)) = 0 :=
    (Kᗮ.starProjection_apply_eq_zero_iff).mpr
      (K.le_orthogonal_orthogonal (K.starProjection_apply_mem _))
  simp [coe_schurComplement_apply, map_sub, map_smul, hn, hKK,
    Kᗮ.starProjection_eq_self_iff.mpr n.2]

/-- The shifted Schur complement depends continuously on the shift away from its pole. -/
theorem continuousOn_schurComplement_sub_smul_one (T : E →L[𝕜] E) (c : 𝕜) :
    ContinuousOn (fun t : 𝕜 ↦ K.schurComplement (T - t • 1) (c - t)) {t | t ≠ c} := by
  simp_rw [schurComplement_sub_smul_one]
  have h1 : ContinuousOn (fun t : 𝕜 ↦ (c - t)⁻¹) {t | t ≠ c} :=
    (continuousOn_const.sub continuousOn_id).inv₀ fun t ht ↦ sub_ne_zero.mpr (Ne.symm ht)
  exact (continuousOn_const.sub (continuousOn_id.smul continuousOn_const)).sub
    (h1.smul continuousOn_const)

/-- The shifted Schur complement, as a function of a real shift, is continuous away from its
pole. -/
theorem continuousOn_schurComplement_sub_ofReal_smul_one (T : E →L[𝕜] E) (α : ℝ) :
    ContinuousOn (fun t : ℝ ↦ K.schurComplement (T - (t : 𝕜) • 1) ((α : 𝕜) - t))
      {t | t ≠ α} :=
  (continuousOn_schurComplement_sub_smul_one T (α : 𝕜)).comp continuous_ofReal.continuousOn
    fun _ ht h ↦ ht (ofReal_injective h)

/-- The shifted Schur complement of a self-adjoint operator with respect to a real shift is
self-adjoint. -/
theorem isSelfAdjoint_schurComplement_sub_ofReal_smul_one [CompleteSpace E] {T : E →L[𝕜] E}
    (hT : IsSelfAdjoint T) (α t : ℝ) :
    IsSelfAdjoint (K.schurComplement (T - (t : 𝕜) • 1) ((α : 𝕜) - t)) := by
  refine isSelfAdjoint_schurComplement (hT.sub ?_) ?_
  · exact (isSelfAdjoint_iff.mpr (conj_ofReal t)).smul (IsSelfAdjoint.one _)
  · rw [← ofReal_sub]
    exact isSelfAdjoint_iff.mpr (conj_ofReal _)

/-- The quadratic form of the shifted Schur complement of a self-adjoint operator. -/
theorem re_inner_schurComplement_sub_ofReal_smul_one_apply_self [CompleteSpace E] {T : E →L[𝕜] E}
    (hT : IsSelfAdjoint T) (α t : ℝ) (n : Kᗮ) :
    re ⟪(K.schurComplement (T - (t : 𝕜) • 1) ((α : 𝕜) - t) n : E), n⟫ =
      re ⟪T n, n⟫ - t * ‖(n : E)‖ ^ 2 - (α - t)⁻¹ * ‖K.starProjection (T n)‖ ^ 2 := by
  have hTs : ∀ x y : E, ⟪T x, y⟫ = ⟪x, T y⟫ := hT.isSymmetric
  have h1 : ⟪Kᗮ.starProjection (T n), (n : E)⟫ = ⟪T n, n⟫ := by
    rw [Kᗮ.inner_starProjection_left_eq_right, Kᗮ.starProjection_eq_self_iff.mpr n.2]
  have h2 : re ⟪Kᗮ.starProjection (T (K.starProjection (T n))), (n : E)⟫ =
      ‖K.starProjection (T n)‖ ^ 2 := by
    rw [Kᗮ.inner_starProjection_left_eq_right, Kᗮ.starProjection_eq_self_iff.mpr n.2, hTs,
      re_inner_starProjection_eq_normSq]
    rfl
  have happly : (K.schurComplement (T - (t : 𝕜) • 1) ((α : 𝕜) - t) n : E) =
      Kᗮ.starProjection (T n) - (t : 𝕜) • (n : E) -
        (((α - t)⁻¹ : ℝ) : 𝕜) • Kᗮ.starProjection (T (K.starProjection (T n))) := by
    rw [schurComplement_sub_smul_one]
    simp
  rw [happly, inner_sub_left, inner_sub_left, inner_smul_left, inner_smul_left, h1,
    inner_self_eq_norm_sq_to_K, conj_ofReal, conj_ofReal, map_sub, map_sub, re_ofReal_mul,
    re_ofReal_mul, h2, ← ofReal_pow, ofReal_re]

end Shifted

/-! ### Signs of the shifted Schur complement near its pole -/

section Signs

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
variable {K : Submodule 𝕜 E} [K.HasOrthogonalProjection]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

open RCLike

/-- **Signs near the pole.**  Let `T` be self-adjoint and suppose that `P_K T` is bounded below on
`Kᗮ`.  Then the shifted Schur complement `S(t) = K.schurComplement (T - t) (α - t)` is `≥ 0` for
`t` slightly larger than `α` and `≤ 0` for `t` slightly smaller than `α`. -/
theorem exists_pos_schurComplement_sign {T : E →L[𝕜] E} (hT : IsSelfAdjoint T) (α : ℝ) {κ : ℝ}
    (hκ : 0 < κ) (hY : ∀ n : Kᗮ, κ * ‖(n : E)‖ ≤ ‖K.starProjection (T n)‖) :
    ∃ ε > 0,
      (∀ t : ℝ, α < t → t < α + ε → 0 ≤ K.schurComplement (T - (t : 𝕜) • 1) ((α : 𝕜) - t)) ∧
      ∀ t : ℝ, α - ε < t → t < α → 0 ≤ -K.schurComplement (T - (t : 𝕜) • 1) ((α : 𝕜) - t) := by
  set L : ℝ := ‖T‖ + |α| + 1 with hL
  have hLpos : 0 < L := by positivity
  refine ⟨min 1 (κ ^ 2 / L), lt_min one_pos (by positivity), ?_, ?_⟩
  · intro t hαt ht
    have ht1 : t - α < 1 := by linarith [min_le_left 1 (κ ^ 2 / L)]
    have ht2 : t - α ≤ κ ^ 2 / L := by linarith [min_le_right 1 (κ ^ 2 / L)]
    rw [ContinuousLinearMap.nonneg_iff_isPositive, ContinuousLinearMap.isPositive_def']
    refine ⟨isSelfAdjoint_schurComplement_sub_ofReal_smul_one hT α t, fun n ↦ ?_⟩
    rw [ContinuousLinearMap.reApplyInnerSelf_apply, coe_inner,
      re_inner_schurComplement_sub_ofReal_smul_one_apply_self hT α t n]
    have hTn : |re ⟪T n, n⟫| ≤ ‖T‖ * ‖(n : E)‖ ^ 2 := by
      calc |re ⟪T n, n⟫| ≤ ‖⟪T n, n⟫‖ := abs_re_le_norm _
        _ ≤ ‖T n‖ * ‖(n : E)‖ := norm_inner_le_norm _ _
        _ ≤ ‖T‖ * ‖(n : E)‖ * ‖(n : E)‖ := by gcongr; exact T.le_opNorm _
        _ = ‖T‖ * ‖(n : E)‖ ^ 2 := by ring
    have hYn : κ ^ 2 * ‖(n : E)‖ ^ 2 ≤ ‖K.starProjection (T n)‖ ^ 2 := by
      have := hY n
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by positivity) this 2
    have htabs : |t| ≤ |α| + 1 := by
      have := abs_sub_abs_le_abs_sub t α
      rw [abs_of_pos (sub_pos.mpr hαt)] at this
      linarith
    have hinv : (α - t)⁻¹ = -(t - α)⁻¹ := by rw [← inv_neg, neg_sub]
    have hdom : L * ‖(n : E)‖ ^ 2 ≤ (t - α)⁻¹ * ‖K.starProjection (T n)‖ ^ 2 := by
      have hpos : 0 < t - α := sub_pos.mpr hαt
      rw [inv_mul_eq_div, le_div_iff₀ hpos]
      calc L * ‖(n : E)‖ ^ 2 * (t - α) = (L * (t - α)) * ‖(n : E)‖ ^ 2 := by ring
        _ ≤ κ ^ 2 * ‖(n : E)‖ ^ 2 := by
          gcongr
          rwa [le_div_iff₀ hLpos, mul_comm] at ht2
        _ ≤ ‖K.starProjection (T n)‖ ^ 2 := hYn
    rw [hinv]
    have h1 : -(‖T‖ * ‖(n : E)‖ ^ 2) ≤ re ⟪T n, n⟫ := neg_le_of_abs_le hTn
    have h2 : t * ‖(n : E)‖ ^ 2 ≤ (|α| + 1) * ‖(n : E)‖ ^ 2 :=
      mul_le_mul_of_nonneg_right ((le_abs_self t).trans htabs) (sq_nonneg _)
    nlinarith
  · intro t ht hta
    have ht1 : α - t < 1 := by linarith [min_le_left 1 (κ ^ 2 / L)]
    have ht2 : α - t ≤ κ ^ 2 / L := by linarith [min_le_right 1 (κ ^ 2 / L)]
    rw [ContinuousLinearMap.nonneg_iff_isPositive, ContinuousLinearMap.isPositive_def']
    refine ⟨(isSelfAdjoint_schurComplement_sub_ofReal_smul_one hT α t).neg, fun n ↦ ?_⟩
    rw [ContinuousLinearMap.reApplyInnerSelf_apply, _root_.neg_apply, inner_neg_left,
      map_neg, coe_inner, re_inner_schurComplement_sub_ofReal_smul_one_apply_self hT α t n]
    have hTn : |re ⟪T n, n⟫| ≤ ‖T‖ * ‖(n : E)‖ ^ 2 := by
      calc |re ⟪T n, n⟫| ≤ ‖⟪T n, n⟫‖ := abs_re_le_norm _
        _ ≤ ‖T n‖ * ‖(n : E)‖ := norm_inner_le_norm _ _
        _ ≤ ‖T‖ * ‖(n : E)‖ * ‖(n : E)‖ := by gcongr; exact T.le_opNorm _
        _ = ‖T‖ * ‖(n : E)‖ ^ 2 := by ring
    have hYn : κ ^ 2 * ‖(n : E)‖ ^ 2 ≤ ‖K.starProjection (T n)‖ ^ 2 := by
      have := hY n
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by positivity) this 2
    have htabs : |t| ≤ |α| + 1 := by
      have := abs_sub_abs_le_abs_sub t α
      rw [abs_of_neg (sub_neg.mpr hta)] at this
      linarith
    have hdom : L * ‖(n : E)‖ ^ 2 ≤ (α - t)⁻¹ * ‖K.starProjection (T n)‖ ^ 2 := by
      have hpos : 0 < α - t := sub_pos.mpr hta
      rw [inv_mul_eq_div, le_div_iff₀ hpos]
      calc L * ‖(n : E)‖ ^ 2 * (α - t) = (L * (α - t)) * ‖(n : E)‖ ^ 2 := by ring
        _ ≤ κ ^ 2 * ‖(n : E)‖ ^ 2 := by
          gcongr
          rwa [le_div_iff₀ hLpos, mul_comm] at ht2
        _ ≤ ‖K.starProjection (T n)‖ ^ 2 := hYn
    have h1 : re ⟪T n, n⟫ ≤ ‖T‖ * ‖(n : E)‖ ^ 2 := le_of_abs_le hTn
    have h2 : -((|α| + 1) * ‖(n : E)‖ ^ 2) ≤ t * ‖(n : E)‖ ^ 2 := by
      have := mul_le_mul_of_nonneg_right (neg_abs_le t) (sq_nonneg ‖(n : E)‖)
      have h3 : -|t| * ‖(n : E)‖ ^ 2 ≥ -((|α| + 1) * ‖(n : E)‖ ^ 2) := by
        nlinarith [sq_nonneg ‖(n : E)‖]
      linarith
    nlinarith

/-- If a self-adjoint `G` maps the closed subspace `K` onto `Kᗮ`, then `P_K G` is bounded below
on `Kᗮ`. -/
theorem exists_pos_mul_norm_le_norm_starProjection_apply [CompleteSpace K] {G : E →L[𝕜] E}
    (hG : IsSelfAdjoint G) (hmap : K.map (G : E →ₗ[𝕜] E) = Kᗮ) :
    ∃ κ > 0, ∀ n ∈ Kᗮ, κ * ‖n‖ ≤ ‖K.starProjection (G n)‖ := by
  have hGs : ∀ x y : E, ⟪G x, y⟫ = ⟪x, G y⟫ := hG.isSymmetric
  have hGK : ∀ m ∈ K, G m ∈ Kᗮ := fun m hm ↦ by
    rw [← hmap]
    exact Submodule.mem_map_of_mem hm
  let Z : K →L[𝕜] Kᗮ := Kᗮ.orthogonalProjectionOnto ∘L G ∘L K.subtypeL
  have hZ : ∀ m : K, (Z m : E) = G m := fun m ↦
    (Kᗮ.starProjection_eq_self_iff).mpr (hGK m m.2)
  have hsurj : Function.Surjective Z := by
    intro n
    have hn : (n : E) ∈ K.map (G : E →ₗ[𝕜] E) := by rw [hmap]; exact n.2
    obtain ⟨m, hm, hGm⟩ := Submodule.mem_map.mp hn
    exact ⟨⟨m, hm⟩, Subtype.ext ((hZ _).trans hGm)⟩
  obtain ⟨C, hC, hpre⟩ := Z.exists_preimage_norm_le hsurj
  refine ⟨C⁻¹, inv_pos.mpr hC, fun n hn ↦ ?_⟩
  obtain ⟨m, hm, hmC⟩ := hpre ⟨n, hn⟩
  have hGm : G m = n := by rw [← hZ, hm]
  have hsq : ‖n‖ ^ 2 ≤ ‖K.starProjection (G n)‖ * (C * ‖n‖) := by
    calc ‖n‖ ^ 2 = ‖⟪n, n⟫‖ := by rw [inner_self_eq_norm_sq_to_K, norm_pow, norm_ofReal, abs_norm]
      _ = ‖⟪K.starProjection (G n), (m : E)⟫‖ := by
        rw [K.inner_starProjection_left_eq_right, K.starProjection_eq_self_iff.mpr m.2,
          hGs, hGm]
      _ ≤ ‖K.starProjection (G n)‖ * ‖(m : E)‖ := norm_inner_le_norm _ _
      _ ≤ ‖K.starProjection (G n)‖ * (C * ‖n‖) := by
        gcongr
        simpa using hmC
  rcases eq_or_ne n 0 with rfl | hn0
  · simp
  have hnpos : 0 < ‖n‖ := norm_pos_iff.mpr hn0
  rw [inv_mul_eq_div, div_le_iff₀ hC]
  nlinarith [norm_nonneg (K.starProjection (G n))]

end Signs

end Submodule
