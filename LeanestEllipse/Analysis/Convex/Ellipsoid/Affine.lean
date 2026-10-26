import LeanestEllipse.Analysis.Convex.Ellipsoid

/-!
# Affine normalization of ellipsoids

These constructions hold in arbitrary real inner product spaces.
-/

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The affine homeomorphism `x ↦ A⁻¹ (x - c)` normalizing an ellipse to the unit disk. -/
def Ellipsoid.normalizeHomeomorph (e : Ellipsoid E) : E ≃ₜ E :=
  (Homeomorph.subRight e.center).trans e.linearPart.symm.toHomeomorph

@[simp] theorem Ellipsoid.normalizeHomeomorph_apply (e : Ellipsoid E) (x : E) :
    e.normalizeHomeomorph x = e.linearPart.symm (x - e.center) := rfl

