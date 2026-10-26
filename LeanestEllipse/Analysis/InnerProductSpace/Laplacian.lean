import Mathlib.Analysis.InnerProductSpace.Laplacian

/-!
# Locality of iterated Laplacians

Every power of the negative Laplacian preserves vanishing on an open set. The functions
need not be globally smooth: the statement uses only their germs at points of the open set.
-/

open Set Filter Laplacian
open scoped Topology

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The negative Laplacian preserves vanishing on an open set. -/
theorem Set.EqOn.neg_laplacian {f : E → F} {D : Set E} (hf : EqOn f 0 D)
    (hD : IsOpen D) : EqOn (-laplacian f) 0 D := by
  intro x hx
  have hg : f =ᶠ[𝓝 x] 0 := Filter.eventuallyEq_of_mem (hD.mem_nhds hx) hf
  have hΔ := (InnerProductSpace.laplacian_congr_nhds hg).eq_of_nhds
  simpa [Pi.zero_def] using congrArg Neg.neg hΔ

/-- Every iterate of the negative Laplacian preserves vanishing on an open set. -/
theorem Set.EqOn.iterate_neg_laplacian {f : E → F} {D : Set E} (hf : EqOn f 0 D)
    (hD : IsOpen D) (k : ℕ) : EqOn ((fun g : E → F ↦ -laplacian g)^[k] f) 0 D := by
  induction k with
  | zero => exact hf
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact ih.neg_laplacian hD
