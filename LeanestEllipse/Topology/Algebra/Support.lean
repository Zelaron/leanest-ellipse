import Mathlib.Topology.Algebra.Support

/-!
# Topological support under a homeomorphism
-/

open Function

/-- Precomposing with a homeomorphism pulls back the closed support. -/
theorem tsupport_comp_homeomorph {X Y M : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [Zero M] (f : Y → M) (h : X ≃ₜ Y) : tsupport (f ∘ h) = h ⁻¹' tsupport f := by
  rw [tsupport, tsupport, Function.support_comp_eq_preimage, h.preimage_closure]

