import LeanestEllipse.EllipseCriterion.SquareGeometry

/-!
# The endpoint incidences in the square figure

At the threshold `δ = 1 / √2`, all four corners of the inner square lie on the unit circle.
The four side midpoints of the outer square lie both on the unit circle and on the frontier
of the closed outer square. These are the literal incidences shown in [Hägg, Figure 2].
-/

open Set Metric Complex

noncomputable section

namespace LeanestEllipse

/-- The interior of a closed coordinate square is the corresponding open square. -/
theorem interior_closedSquare (r : ℝ) : interior (closedSquare r) = openSquare r := by
  rw [closedSquare, openSquare, interior_reProdIm, interior_Icc]

/-- The boundary of a closed coordinate square consists of its points outside the open square. -/
theorem frontier_closedSquare (r : ℝ) :
    frontier (closedSquare r) = closedSquare r \ openSquare r := by
  rw [(isClosed_closedSquare r).frontier_eq, interior_closedSquare]

/-- The boundary of a positive-radius open square is its closure minus the open square. -/
theorem frontier_openSquare (r : ℝ) (hr : 0 < r) :
    frontier (openSquare r) = closedSquare r \ openSquare r := by
  rw [(isOpen_openSquare r).frontier_eq, closure_openSquare hr]

/-- The open and closed squares have the same boundary when the half-side is positive. -/
theorem frontier_openSquare_eq_frontier_closedSquare (r : ℝ) (hr : 0 < r) :
    frontier (openSquare r) = frontier (closedSquare r) := by
  rw [frontier_openSquare r hr, frontier_closedSquare]

/-- A corner of a square of half-side `δ ≥ 0` lies on the circle of radius `δ * √2`. -/
theorem square_corner_mem_sphere {δ x y : ℝ} (hδ : 0 ≤ δ)
    (hx : x = δ ∨ x = -δ) (hy : y = δ ∨ y = -δ) :
    (⟨x, y⟩ : ℂ) ∈ sphere (0 : ℂ) (δ * Real.sqrt 2) := by
  have hx2 : x ^ 2 = δ ^ 2 := by rcases hx with rfl | rfl <;> ring
  have hy2 : y ^ 2 = δ ^ 2 := by rcases hy with rfl | rfl <;> ring
  have hn : ‖(⟨x, y⟩ : ℂ)‖ ^ 2 = 2 * δ ^ 2 := by
    rw [Complex.sq_norm, normSq_apply]
    change x * x + y * y = 2 * δ ^ 2
    nlinarith
  have hr2 : (δ * Real.sqrt 2) ^ 2 = 2 * δ ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num)]
    ring
  rw [mem_sphere_zero_iff_norm]
  have hr : 0 ≤ δ * Real.sqrt 2 := mul_nonneg hδ (Real.sqrt_nonneg _)
  nlinarith [norm_nonneg (⟨x, y⟩ : ℂ)]

/-- All four corners of `[-δ, δ]²` lie on its circumcircle of radius `δ * √2`. -/
theorem square_corners_subset_sphere {δ : ℝ} (hδ : 0 ≤ δ) :
    ({(⟨δ, δ⟩ : ℂ), ⟨δ, -δ⟩, ⟨-δ, δ⟩, ⟨-δ, -δ⟩} : Set ℂ) ⊆
      sphere (0 : ℂ) (δ * Real.sqrt 2) := by
  intro z hz
  simp only [mem_insert_iff, mem_singleton_iff] at hz
  rcases hz with rfl | rfl | rfl | rfl <;>
    exact square_corner_mem_sphere hδ (by simp) (by simp)

/-- Either sign of each threshold coordinate gives a corner on the unit circle. -/
theorem square_threshold_corner_mem_unitSphere {x y : ℝ}
    (hx : x = 1 / Real.sqrt 2 ∨ x = -(1 / Real.sqrt 2))
    (hy : y = 1 / Real.sqrt 2 ∨ y = -(1 / Real.sqrt 2)) :
    (⟨x, y⟩ : ℂ) ∈ sphere (0 : ℂ) 1 := by
  have hx2 : x ^ 2 = (1 / Real.sqrt 2) ^ 2 := by
    rcases hx with rfl | rfl <;> ring
  have hy2 : y ^ 2 = (1 / Real.sqrt 2) ^ 2 := by
    rcases hy with rfl | rfl <;> ring
  have hδ2 : (1 / Real.sqrt 2) ^ 2 = (1 / 2 : ℝ) := by
    rw [div_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  rw [mem_sphere_zero_iff_norm]
  have hn : ‖(⟨x, y⟩ : ℂ)‖ ^ 2 = 1 := by
    rw [Complex.sq_norm, normSq_apply]
    change x * x + y * y = 1
    nlinarith
  nlinarith [norm_nonneg (⟨x, y⟩ : ℂ)]

/-- The four corners of `[-1 / √2, 1 / √2]²` lie on the unit circle. -/
theorem square_threshold_corners_subset_unitSphere :
    ({(⟨1 / Real.sqrt 2, 1 / Real.sqrt 2⟩ : ℂ),
      ⟨1 / Real.sqrt 2, -(1 / Real.sqrt 2)⟩,
      ⟨-(1 / Real.sqrt 2), 1 / Real.sqrt 2⟩,
      ⟨-(1 / Real.sqrt 2), -(1 / Real.sqrt 2)⟩} : Set ℂ) ⊆ sphere (0 : ℂ) 1 := by
  intro z hz
  simp only [mem_insert_iff, mem_singleton_iff] at hz
  rcases hz with rfl | rfl | rfl | rfl <;>
    exact square_threshold_corner_mem_unitSphere (by simp) (by simp)

/-- The four side midpoints of `[-1, 1]²` lie on both the unit circle and the square boundary. -/
theorem square_side_midpoints_subset_unitSphere_frontier :
    ({1, -1, I, -I} : Set ℂ) ⊆ sphere (0 : ℂ) 1 ∩ frontier (closedSquare 1) := by
  intro z hz
  simp only [mem_insert_iff, mem_singleton_iff] at hz
  rcases hz with rfl | rfl | rfl | rfl
  all_goals
    constructor
    · simp
    · simp [frontier_closedSquare, mem_closedSquare, mem_openSquare]

/-- The outer open square in Figure 2 has the same four side-midpoint incidences. -/
theorem square_side_midpoints_subset_unitSphere_openFrontier :
    ({1, -1, I, -I} : Set ℂ) ⊆ sphere (0 : ℂ) 1 ∩ frontier (openSquare 1) := by
  rw [frontier_openSquare_eq_frontier_closedSquare 1 zero_lt_one]
  exact square_side_midpoints_subset_unitSphere_frontier

/-- The unit circle meets the outer open square boundary exactly at its four side midpoints. -/
theorem unitSphere_inter_frontier_openSquare_eq_sideMidpoints :
    sphere (0 : ℂ) 1 ∩ frontier (openSquare 1) = ({1, -1, I, -I} : Set ℂ) := by
  apply Subset.antisymm
  · rintro z ⟨hsphere, hfront⟩
    rw [frontier_openSquare 1 zero_lt_one] at hfront
    obtain ⟨hclosed, hopen⟩ := hfront
    have hn := congrArg (fun t : ℝ ↦ t ^ 2) (mem_sphere_zero_iff_norm.mp hsphere)
    rw [Complex.sq_norm, normSq_apply] at hn
    have hboundary : z.re = -1 ∨ z.re = 1 ∨ z.im = -1 ∨ z.im = 1 := by
      rcases hclosed.1.1.eq_or_lt with h | h₁
      · exact Or.inl h.symm
      rcases hclosed.1.2.eq_or_lt with h | h₂
      · exact Or.inr (Or.inl h)
      rcases hclosed.2.1.eq_or_lt with h | h₃
      · exact Or.inr (Or.inr (Or.inl h.symm))
      rcases hclosed.2.2.eq_or_lt with h | h₄
      · exact Or.inr (Or.inr (Or.inr h))
      exact False.elim (hopen ⟨⟨h₁, h₂⟩, ⟨h₃, h₄⟩⟩)
    rcases hboundary with hre | hre | him | him
    · rw [hre] at hn
      have him : z.im = 0 := sq_eq_zero_iff.mp (by nlinarith : z.im ^ 2 = 0)
      simp [Complex.ext_iff, hre, him]
    · rw [hre] at hn
      have him : z.im = 0 := sq_eq_zero_iff.mp (by nlinarith : z.im ^ 2 = 0)
      simp [Complex.ext_iff, hre, him]
    · rw [him] at hn
      have hre : z.re = 0 := sq_eq_zero_iff.mp (by nlinarith : z.re ^ 2 = 0)
      simp [Complex.ext_iff, hre, him]
    · rw [him] at hn
      have hre : z.re = 0 := sq_eq_zero_iff.mp (by nlinarith : z.re ^ 2 = 0)
      simp [Complex.ext_iff, hre, him]
  · exact square_side_midpoints_subset_unitSphere_openFrontier

/-- The corresponding closed-square boundary has exactly the same four contact points. -/
theorem unitSphere_inter_frontier_closedSquare_eq_sideMidpoints :
    sphere (0 : ℂ) 1 ∩ frontier (closedSquare 1) = ({1, -1, I, -I} : Set ℂ) := by
  rw [← frontier_openSquare_eq_frontier_closedSquare 1 zero_lt_one]
  exact unitSphere_inter_frontier_openSquare_eq_sideMidpoints

/-- The closed unit disk itself has exactly the four boundary contacts stated in Figure 2. -/
theorem unitDisk_inter_frontier_openSquare_eq_sideMidpoints :
    closedBall (0 : ℂ) 1 ∩ frontier (openSquare 1) = ({1, -1, I, -I} : Set ℂ) := by
  have hcontact : closedBall (0 : ℂ) 1 ∩ frontier (openSquare 1) =
      sphere (0 : ℂ) 1 ∩ frontier (openSquare 1) := by
    apply Subset.antisymm
    · rintro z ⟨hz, hfront⟩
      refine ⟨?_, hfront⟩
      rw [mem_sphere_zero_iff_norm]
      apply le_antisymm
      · simpa using hz
      · by_contra hnorm
        have hopen : z ∈ openSquare 1 :=
          closedBall_subset_openSquare (lt_of_not_ge hnorm) (by simp)
        rw [frontier_openSquare 1 zero_lt_one] at hfront
        exact hfront.2 hopen
    · rintro z ⟨hz, hfront⟩
      exact ⟨sphere_subset_closedBall hz, hfront⟩
  rw [hcontact, unitSphere_inter_frontier_openSquare_eq_sideMidpoints]

end LeanestEllipse
