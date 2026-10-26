import LeanestEllipse.Analysis.Convex.SupportFunction

/-!
# Support functions of possibly degenerate ellipsoids

The image of a closed unit ball under an affine continuous linear map has the usual
ellipsoid support function, even if the map is singular. The source and target may be
different real Hilbert spaces, and they need not be finite dimensional.
-/

open Set Metric Bornology
open scoped RealInnerProductSpace

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- The upper support function of an affine image of a closed unit ball. -/
theorem supportFunction_affine_image_closedBall (c : F) (A : E →L[ℝ] F) (ω : F) :
    supportFunction ((fun x ↦ c + A x) '' closedBall (0 : E) 1) ω =
      ⟪c, ω⟫ + ‖ContinuousLinearMap.adjoint A ω‖ := by
  have heq : (fun x ↦ c + A x) '' closedBall (0 : E) 1 =
      (c + ·) '' (A '' closedBall (0 : E) 1) := by rw [Set.image_image]
  rw [heq, supportFunction_image_add ((nonempty_closedBall.mpr zero_le_one).image _)
    (A.lipschitzWith.isBounded_image isBounded_closedBall),
    supportFunction_image_continuousLinearMap, supportFunction_closedBall_zero zero_le_one,
    one_mul]

/-- The lower support function of an affine image of a closed unit ball. -/
theorem lowerSupportFunction_affine_image_closedBall (c : F) (A : E →L[ℝ] F) (ω : F) :
    lowerSupportFunction ((fun x ↦ c + A x) '' closedBall (0 : E) 1) ω =
      ⟪c, ω⟫ - ‖ContinuousLinearMap.adjoint A ω‖ := by
  rw [lowerSupportFunction_eq_neg_supportFunction_neg, supportFunction_affine_image_closedBall,
    inner_neg_right, map_neg, norm_neg]
  ring
