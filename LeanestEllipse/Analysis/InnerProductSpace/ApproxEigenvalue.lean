import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Algebra.Spectrum

/-!
# Approximate eigenvalues of normal operators

A scalar `a` is an *approximate eigenvalue* of a bounded operator `T` if there are unit vectors
`uₙ` with `‖T uₙ - a • uₙ‖ → 0`.

## Main results

* `ContinuousLinearMap.mem_spectrum_of_tendsto_norm_sub_smul`: every approximate eigenvalue of a
  bounded operator on a normed space lies in its spectrum.
* `ContinuousLinearMap.IsStarNormal.isUnit_of_antilipschitz`: a normal operator on a Hilbert
  space which is bounded below is invertible.
* `ContinuousLinearMap.IsStarNormal.exists_seq_tendsto_norm_sub_smul_of_mem_spectrum`: for a
  normal operator every point of the spectrum is an approximate eigenvalue.  Together with the
  previous item: the spectrum of a normal operator is its approximate point spectrum.
* `ContinuousLinearMap.isStarNormal_add_smul_adjoint`: `A + w A†` is normal whenever `|w| = 1`.
-/

open Filter Topology
open scoped NNReal InnerProductSpace

namespace ContinuousLinearMap

section Normed

variable {𝕜 F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Every approximate eigenvalue of a bounded operator lies in its spectrum. -/
theorem mem_spectrum_of_tendsto_norm_sub_smul (T : F →L[𝕜] F) {a : 𝕜} {u : ℕ → F}
    (hu : ∀ n, ‖u n‖ = 1) (hlim : Tendsto (fun n ↦ ‖T (u n) - a • u n‖) atTop (𝓝 0)) :
    a ∈ spectrum 𝕜 T := by
  rw [spectrum.mem_iff]
  rintro ⟨S, hS⟩
  have hle : ∀ n, (1 : ℝ) ≤ ‖(↑S⁻¹ : F →L[𝕜] F)‖ * ‖T (u n) - a • u n‖ := fun n ↦ by
    have hinv : (↑S⁻¹ : F →L[𝕜] F) ((S : F →L[𝕜] F) (u n)) = u n := by
      exact congrArg (fun L : F →L[𝕜] F ↦ L (u n)) S.inv_mul
    calc (1 : ℝ) = ‖u n‖ := (hu n).symm
      _ = ‖(↑S⁻¹ : F →L[𝕜] F) ((algebraMap 𝕜 (F →L[𝕜] F) a - T) (u n))‖ := by
          rw [← hS, hinv]
      _ ≤ ‖(↑S⁻¹ : F →L[𝕜] F)‖ * ‖(algebraMap 𝕜 (F →L[𝕜] F) a - T) (u n)‖ :=
          le_opNorm _ _
      _ = ‖(↑S⁻¹ : F →L[𝕜] F)‖ * ‖T (u n) - a • u n‖ := by
          simp [Algebra.algebraMap_eq_smul_one, norm_sub_rev]
  have hlim' := hlim.const_mul ‖(↑S⁻¹ : F →L[𝕜] F)‖
  rw [mul_zero] at hlim'
  exact absurd (ge_of_tendsto' hlim' hle) (by norm_num)

end Normed

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]

/-- If `|w| = 1`, then `A + w • A†` is a normal operator: its adjoint is `star w • (A + w • A†)`. -/
theorem isStarNormal_add_smul_adjoint (A : E →L[𝕜] E) {w : 𝕜} (hw : ‖w‖ = 1) :
    IsStarNormal (A + w • adjoint A) := by
  have hww : star w * w = 1 := by
    rw [RCLike.star_def, RCLike.conj_mul, hw]
    simp
  have hstar : star (A + w • adjoint A) = star w • (A + w • adjoint A) := by
    rw [star_add, star_smul, star_eq_adjoint, star_eq_adjoint, adjoint_adjoint, smul_add,
      smul_smul, hww, one_smul, add_comm]
  refine ⟨?_⟩
  rw [hstar, Commute, SemiconjBy, smul_mul_assoc, mul_smul_comm]

namespace IsStarNormal

variable {T : E →L[𝕜] E}

/-- A normal operator on a Hilbert space which is bounded below is invertible. -/
theorem isUnit_of_antilipschitz (hT : IsStarNormal T) {K : ℝ≥0} (hK : AntilipschitzWith K T) :
    IsUnit T := by
  rw [ContinuousLinearMap.isUnit_iff_bijective,
    ContinuousLinearMap.bijective_iff_dense_range_and_antilipschitz]
  refine ⟨?_, K, hK⟩
  rw [Submodule.topologicalClosure_eq_top_iff, IsStarNormal.orthogonal_range hT]
  exact LinearMap.ker_eq_bot.mpr hK.injective

/-- A normal operator on a Hilbert space which is not invertible takes arbitrarily small values on
unit vectors. -/
theorem exists_norm_eq_one_norm_apply_lt (hT : IsStarNormal T) (hT' : ¬ IsUnit T) {ε : ℝ}
    (hε : 0 < ε) : ∃ x : E, ‖x‖ = 1 ∧ ‖T x‖ < ε := by
  have hnolower : ¬ ∀ x, ε * ‖x‖ ≤ ‖T x‖ := fun hall ↦ by
    obtain ⟨K, hK⟩ := (antilipschitzWith_iff_exists_mul_le_norm (f := T)).2 ⟨ε, hε, hall⟩
    exact hT' (isUnit_of_antilipschitz hT hK)
  push Not at hnolower
  obtain ⟨x, hx⟩ := hnolower
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at hx
  have hxpos : 0 < ‖x‖ := norm_pos_iff.2 hx0
  refine ⟨(‖x‖ : 𝕜)⁻¹ • x, norm_smul_inv_norm hx0, ?_⟩
  calc ‖T ((‖x‖ : 𝕜)⁻¹ • x)‖ = ‖x‖⁻¹ * ‖T x‖ := by
        rw [map_smul, norm_smul, norm_inv, RCLike.norm_ofReal, abs_of_pos hxpos]
    _ < ‖x‖⁻¹ * (ε * ‖x‖) := mul_lt_mul_of_pos_left hx (inv_pos.2 hxpos)
    _ = ε := by field_simp

/-- A normal operator on a Hilbert space which is not invertible admits a sequence of unit vectors
`uₙ` with `T uₙ → 0`. -/
theorem exists_seq_norm_eq_one_tendsto_norm_apply (hT : IsStarNormal T) (hT' : ¬ IsUnit T) :
    ∃ u : ℕ → E, (∀ n, ‖u n‖ = 1) ∧ Tendsto (fun n ↦ ‖T (u n)‖) atTop (𝓝 0) := by
  choose u hu hsmall using fun n : ℕ ↦
    exists_norm_eq_one_norm_apply_lt hT hT' (Nat.one_div_pos_of_nat (n := n))
  exact ⟨u, hu, squeeze_zero (fun n ↦ norm_nonneg _) (fun n ↦ (hsmall n).le)
    tendsto_one_div_add_atTop_nhds_zero_nat⟩

/-- The shift `T - a` of a normal operator by a scalar is normal. -/
theorem sub_algebraMap (hT : IsStarNormal T) (a : 𝕜) :
    IsStarNormal (T - algebraMap 𝕜 (E →L[𝕜] E) a) := by
  have hstar : star (algebraMap 𝕜 (E →L[𝕜] E) a) = algebraMap 𝕜 (E →L[𝕜] E) (star a) :=
    (algebraMap_star_comm a).symm
  have hb : IsStarNormal (algebraMap 𝕜 (E →L[𝕜] E) a) :=
    ⟨by rw [hstar]; exact Algebra.commute_algebraMap_left _ _⟩
  have hab : Commute T (star (algebraMap 𝕜 (E →L[𝕜] E) a)) := by
    rw [hstar]
    exact Algebra.commute_algebraMap_right _ _
  exact hab.isStarNormal_sub

/-- **Approximate eigenvalues of normal operators.**  For a normal operator `T` on a Hilbert
space, every point `a` of the spectrum is an approximate eigenvalue: there are unit vectors `uₙ`
with `‖T uₙ - a • uₙ‖ → 0`. -/
theorem exists_seq_tendsto_norm_sub_smul_of_mem_spectrum (hT : IsStarNormal T) {a : 𝕜}
    (ha : a ∈ spectrum 𝕜 T) :
    ∃ u : ℕ → E, (∀ n, ‖u n‖ = 1) ∧ Tendsto (fun n ↦ ‖T (u n) - a • u n‖) atTop (𝓝 0) := by
  have hnu : ¬ IsUnit (T - algebraMap 𝕜 (E →L[𝕜] E) a) := by
    rw [← neg_sub, IsUnit.neg_iff]
    exact spectrum.mem_iff.1 ha
  obtain ⟨u, hu, hlim⟩ := exists_seq_norm_eq_one_tendsto_norm_apply (sub_algebraMap hT a) hnu
  refine ⟨u, hu, ?_⟩
  simpa [Algebra.algebraMap_eq_smul_one] using hlim

/-- For a normal operator on a Hilbert space, a scalar is in the spectrum iff it is an
approximate eigenvalue. -/
theorem mem_spectrum_iff_exists_seq (hT : IsStarNormal T) {a : 𝕜} :
    a ∈ spectrum 𝕜 T ↔
      ∃ u : ℕ → E, (∀ n, ‖u n‖ = 1) ∧ Tendsto (fun n ↦ ‖T (u n) - a • u n‖) atTop (𝓝 0) :=
  ⟨exists_seq_tendsto_norm_sub_smul_of_mem_spectrum hT, fun ⟨_, hu, hlim⟩ ↦
    mem_spectrum_of_tendsto_norm_sub_smul T hu hlim⟩

end IsStarNormal

end ContinuousLinearMap
