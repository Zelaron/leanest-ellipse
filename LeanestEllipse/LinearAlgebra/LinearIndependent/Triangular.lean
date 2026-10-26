import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.BigOperators.Pi

/-!
# Linear independence from triangular evaluations

A sequence of functions over any division ring is linearly independent if its evaluation
matrix at a sequence of points is triangular with nonzero diagonal.
-/

/-- **Triangular evaluations give linear independence.**  If `u m (x m) ≠ 0` and `u n (x m) = 0`
for `n < m`, then the family `u` is linearly independent. -/
theorem linearIndependent_of_triangular_evaluations {K X : Type*} [DivisionRing K]
    {u : ℕ → X → K} (x : ℕ → X)
    (hdiag : ∀ m, u m (x m) ≠ 0) (hlow : ∀ n m, n < m → u n (x m) = 0) :
    LinearIndependent K u := by
  classical
  rw [linearIndependent_iff']
  intro s c hsum i hi
  by_contra hci
  -- the largest index with a nonzero coefficient
  set t := s.filter fun j ↦ c j ≠ 0
  have ht : t.Nonempty := ⟨i, Finset.mem_filter.mpr ⟨hi, hci⟩⟩
  set m := t.max' ht
  have hmt : m ∈ t := t.max'_mem ht
  have hm := Finset.mem_filter.mp hmt
  have heval := congrFun hsum (x m)
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at heval
  rw [Finset.sum_eq_single_of_mem m hm.1] at heval
  · exact mul_ne_zero hm.2 (hdiag m) heval
  · intro j hj hjm
    by_cases hcj : c j = 0
    · simp [hcj]
    · have hjt : j ∈ t := Finset.mem_filter.mpr ⟨hj, hcj⟩
      have hle : j ≤ m := t.le_max' j hjt
      rw [hlow j m (lt_of_le_of_ne hle hjm), mul_zero]

