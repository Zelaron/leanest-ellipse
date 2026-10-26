import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Convex hulls of compact sets in finite dimension

By Carathéodory's theorem, every point of the convex hull of a set `s` in a real vector space of
dimension `d` is a convex combination of `d + 1` points of `s`
(`convexHull_eq_image_simplex_fin`).  Hence, in a finite dimensional real topological vector
space, the convex hull of a compact set is compact (`IsCompact.convexHull`): it is the image of
the compact set `Δ_d × s ^ (d + 1)` under the continuous map `(w, z) ↦ ∑ i, w i • z i`, where
`Δ_d = {w : Fin (d + 1) → ℝ | (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1}` is the standard simplex.
-/

open Set Finset Module

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

private theorem sum_eq_sum_comp_embedding {ι κ M : Type*} [Fintype ι] [Fintype κ]
    [AddCommMonoid M] (j : ι ↪ κ) (g : κ → M) (hg : ∀ k, (¬ ∃ i, j i = k) → g k = 0) :
    ∑ k, g k = ∑ i, g (j i) := by
  rw [← Finset.sum_map univ j g]
  refine (Finset.sum_subset (subset_univ _) fun k _ hk ↦ hg k ?_).symm
  rintro ⟨i, rfl⟩
  exact hk (Finset.mem_map_of_mem j (mem_univ i))

/-- **Carathéodory's theorem**, fixed-size form: in a real vector space of finite dimension `d`,
the convex hull of `s` consists of the convex combinations of `d + 1` points of `s`. -/
theorem convexHull_eq_image_simplex_fin [FiniteDimensional ℝ E] (s : Set E) :
    convexHull ℝ s =
      (fun wz : (Fin (finrank ℝ E + 1) → ℝ) × (Fin (finrank ℝ E + 1) → E) ↦
          ∑ i, wz.1 i • wz.2 i) ''
        ({w | (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1} ×ˢ univ.pi fun _ ↦ s) := by
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨z₀, hz₀⟩ := convexHull_nonempty_iff.mp ⟨x, hx⟩
    obtain ⟨ι, _, z, w, hzs, hind, hw0, hw1, hwz⟩ := eq_pos_convex_span_of_mem_convexHull hx
    have hcard : Fintype.card ι ≤ Fintype.card (Fin (finrank ℝ E + 1)) := by
      rw [Fintype.card_fin]
      exact hind.card_le_finrank_succ.trans (Nat.add_le_add_right (Submodule.finrank_le _) 1)
    obtain ⟨j⟩ := Function.Embedding.nonempty_of_card_le hcard
    set w' : Fin (finrank ℝ E + 1) → ℝ := Function.extend j w 0
    set z' : Fin (finrank ℝ E + 1) → E := Function.extend j z fun _ ↦ z₀
    have hw'j : ∀ i, w' (j i) = w i := fun i ↦ j.injective.extend_apply _ _ i
    have hz'j : ∀ i, z' (j i) = z i := fun i ↦ j.injective.extend_apply _ _ i
    have hw'0 : ∀ k, (¬ ∃ i, j i = k) → w' k = 0 := fun k hk ↦ by
      simp only [w', Function.extend_apply' _ _ _ hk, Pi.zero_apply]
    refine ⟨(w', z'), ⟨⟨fun k ↦ ?_, ?_⟩, fun k _ ↦ ?_⟩, ?_⟩
    · change 0 ≤ w' k
      by_cases hk : ∃ i, j i = k
      · obtain ⟨i, rfl⟩ := hk
        rw [hw'j]
        exact (hw0 i).le
      · rw [hw'0 k hk]
    · change ∑ k, w' k = 1
      rw [sum_eq_sum_comp_embedding j w' hw'0]
      simp only [hw'j, hw1]
    · change z' k ∈ s
      by_cases hk : ∃ i, j i = k
      · obtain ⟨i, rfl⟩ := hk
        rw [hz'j]
        exact hzs (mem_range_self i)
      · simp only [z', Function.extend_apply' _ _ _ hk]
        exact hz₀
    · change ∑ k, w' k • z' k = x
      rw [sum_eq_sum_comp_embedding j (fun k ↦ w' k • z' k) fun k hk ↦ by
        simp only [hw'0 k hk, zero_smul]]
      simp only [hw'j, hz'j, hwz]
  · rintro _ ⟨⟨w, z⟩, ⟨hw, hz⟩, rfl⟩
    exact (convex_convexHull ℝ s).sum_mem (fun i _ ↦ hw.1 i) hw.2
      fun i _ ↦ subset_convexHull ℝ s (hz i (mem_univ i))

variable [TopologicalSpace E] [ContinuousAdd E] [ContinuousSMul ℝ E] [FiniteDimensional ℝ E]

/-- The standard simplex `{w : ι → ℝ | (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1}` is compact. -/
theorem isCompact_setOf_nonneg_sum_eq_one (ι : Type*) [Fintype ι] :
    IsCompact {w : ι → ℝ | (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1} := by
  refine (isCompact_univ_pi fun _ ↦ isCompact_Icc (a := (0 : ℝ)) (b := 1)).of_isClosed_subset
    ?_ fun w hw i _ ↦ ⟨hw.1 i, ?_⟩
  · have h1 : IsClosed {w : ι → ℝ | ∀ i, 0 ≤ w i} := by
      simp only [ofPred_forall]
      exact isClosed_iInter fun i ↦ isClosed_le continuous_const (continuous_apply i)
    have h2 : IsClosed {w : ι → ℝ | ∑ i, w i = 1} :=
      isClosed_eq (continuous_finsetSum _ fun i _ ↦ continuous_apply i) continuous_const
    exact h1.inter h2
  · rw [← hw.2]
    exact Finset.single_le_sum (fun j _ ↦ hw.1 j) (mem_univ i)

/-- In a finite dimensional real topological vector space, the convex hull of a compact set is
compact. -/
theorem IsCompact.convexHull {s : Set E} (hs : IsCompact s) :
    IsCompact (_root_.convexHull ℝ s) := by
  rw [convexHull_eq_image_simplex_fin]
  exact ((isCompact_setOf_nonneg_sum_eq_one _).prod (isCompact_univ_pi fun _ ↦ hs)).image
    (by fun_prop)

/-- In a finite dimensional real Hausdorff topological vector space, the convex hull of a compact
set is closed. -/
theorem IsCompact.isClosed_convexHull [T2Space E] {s : Set E} (hs : IsCompact s) :
    IsClosed (_root_.convexHull ℝ s) :=
  hs.convexHull.isClosed
