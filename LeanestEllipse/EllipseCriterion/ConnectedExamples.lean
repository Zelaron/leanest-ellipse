import LeanestEllipse.EllipseCriterion.MainTheorem
import Mathlib.Analysis.Normed.Module.Connected

/-!
# Connected examples of the ellipse criterion

A sphere of positive radius in a real normed space of dimension greater than one is connected
and not contained in a line. In particular, the connected-set form of the ellipse criterion
applies to every circle in a Euclidean plane, as asserted in [Hägg, Remark 2].
-/

open Set Metric

noncomputable section

namespace LeanestEllipse

section NormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- A sphere of nonnegative radius is connected in real dimension greater than one. -/
theorem isConnected_sphere_of_one_lt_finrank (hE : 1 < Module.finrank ℝ E)
    (c : E) {r : ℝ} (hr : 0 ≤ r) : IsConnected (sphere c r) := by
  apply _root_.isConnected_sphere (x := c) (r := r) ?_ hr
  rw [← Module.finrank_eq_rank]
  exact_mod_cast hE

/-- A sphere of positive radius is not contained in a line in real dimension greater than one. -/
theorem not_collinear_sphere_of_one_lt_finrank (hE : 1 < Module.finrank ℝ E)
    (c : E) {r : ℝ} (hr : 0 < r) : ¬ Collinear ℝ (sphere c r) := by
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (lt_trans zero_lt_one hE)
  have hinter : (interior (convexHull ℝ (sphere c r))).Nonempty := by
    rw [convexHull_sphere_eq_closedBall c hr.le]
    exact ⟨c, ball_subset_interior_closedBall (mem_ball_self hr)⟩
  have hspan : affineSpan ℝ (sphere c r) = ⊤ :=
    interior_convexHull_nonempty_iff_affineSpan_eq_top.mp hinter
  have hvspan := AffineSubspace.vectorSpan_eq_top_of_affineSpan_eq_top ℝ E E hspan
  intro hcol
  have hdim := hcol.finrank_le_one
  rw [hvspan, finrank_top] at hdim
  omega

end NormedSpace

section Plane

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Fact (Module.finrank ℝ E = 2)]

/-- **Circle data sets** [Hägg, Remark 2]: the ellipse criterion holds when `D₀` is any circle
of positive radius in the plane and `D` is open and convex. -/
theorem ellipse_criterion_sphere (c : E) {r : ℝ} (hr : 0 < r) {D : Set E}
    (hDo : IsOpen D) (hDc : Convex ℝ D) :
    List.TFAE [SmoothNullExists (sphere c r) D, IntegrableNullExists (sphere c r) D,
      EllipseSandwich (sphere c r) D] := by
  have hE : 1 < Module.finrank ℝ E := by
    rw [(Fact.out : Module.finrank ℝ E = 2)]
    norm_num
  exact ellipse_criterion_of_isConnected
    (isConnected_sphere_of_one_lt_finrank hE c hr.le)
    (not_collinear_sphere_of_one_lt_finrank hE c hr) hDo hDc

end Plane

end LeanestEllipse
