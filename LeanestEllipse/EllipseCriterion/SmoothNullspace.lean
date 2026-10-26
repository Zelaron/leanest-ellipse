import LeanestEllipse.EllipseCriterion.MainTheorem
import LeanestEllipse.IntegralGeometry.Radon.Continuous

/-!
# The real smooth nullspace is zero or infinite dimensional

This formalizes the sentence following Proposition 5. The nullspace consists of real-valued
smooth functions with compact support in the outer set and zero Radon data on every line
meeting the inner set. No openness or convexity is needed to define the vector space.
-/

open MeasureTheory Set
open scoped CompactlyContained

noncomputable section

namespace LeanestEllipse

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The real vector space of smooth compactly supported null functions for the two sets. -/
def realSmoothNullspace (D₀ D : Set E) : Submodule ℝ (E → ℝ) where
  carrier := {u | ContDiff ℝ (⊤ : ℕ∞) u ∧ HasCompactSupport u ∧ tsupport u ⊆ D ∧
    ∀ ω : E, ‖ω‖ = 1 → ∀ p : ℝ, LineMeets D₀ ω p → radonTransform u ω p = 0}
  zero_mem' := ⟨contDiff_const, HasCompactSupport.zero, by simp, by simp⟩
  add_mem' := by
    rintro u v ⟨hu, huc, hus, huv⟩ ⟨hv, hvc, hvs, hvv⟩
    refine ⟨hu.add hv, huc.add hvc, (tsupport_add u v).trans (union_subset hus hvs), ?_⟩
    intro ω hω p hp
    rw [radonTransform_add_of_continuous hu.continuous huc hv.continuous hvc,
      huv ω hω p hp, hvv ω hω p hp, add_zero]
  smul_mem' := by
    rintro a u ⟨hu, huc, hus, huv⟩
    refine ⟨hu.const_smul a, huc.smul_left,
      (tsupport_smul_subset_right (fun _ ↦ a) u).trans hus, ?_⟩
    intro ω hω p hp
    rw [radonTransform_smul, huv ω hω p hp, smul_zero]

/-- A nonzero member of the real nullspace gives a witness for condition (i). -/
theorem smoothNullExists_of_realSmoothNullspace_ne_bot {D₀ D : Set E}
    (h : realSmoothNullspace D₀ D ≠ ⊥) : SmoothNullExists D₀ D := by
  obtain ⟨u, ⟨hs, hc, hsupp, hvan⟩, hu⟩ := (realSmoothNullspace D₀ D).ne_bot_iff.mp h
  have htsupp : tsupport (fun x ↦ (u x : ℂ)) = tsupport u := by
    simp only [tsupport, Function.support, ne_eq, Complex.ofReal_eq_zero]
  refine ⟨fun x ↦ (u x : ℂ), fun hz ↦ hu (funext fun x ↦ ?_),
    Complex.ofRealCLM.contDiff.comp hs,
    htsupp ▸ CompactlyContained.of_isCompact hc hsupp, ?_⟩
  · simpa using congrFun hz x
  · intro ω hω p hp
    rw [radonTransform_complex_ofReal, hvan ω hω p hp, Complex.ofReal_zero]

variable [Fact (Module.finrank ℝ E = 2)]

/-- Every ellipse sandwich gives an infinite-dimensional real smooth nullspace, even when
the inner set is arbitrary and the outer open set is not convex. -/
theorem realSmoothNullspace_infinite_of_ellipseSandwich {D₀ D : Set E} (hD : IsOpen D)
    (h : EllipseSandwich D₀ D) : ¬ Module.Finite ℝ (realSmoothNullspace D₀ D) := by
  obtain ⟨e, h₀, h₁⟩ := h
  obtain ⟨u, hli, hu⟩ := sufficiency_linearIndependent hD e h₁.subset
  let v : ℕ → realSmoothNullspace D₀ D := fun n ↦ ⟨u n,
    (hu n).2.1,
    (CompactlyContained.iff_of_isClosed (isClosed_tsupport _)).mp (hu n).2.2.1 |>.1,
    (hu n).2.2.1.subset,
    fun ω hω p ⟨x, hx, hxp⟩ ↦ (hu n).2.2.2.1 ω hω p ⟨x, h₀ (subset_closure hx), hxp⟩⟩
  have hv : LinearIndependent ℝ v :=
    LinearIndependent.of_comp (realSmoothNullspace D₀ D).subtype hli
  intro hfinite
  let := hfinite
  exact Module.Finite.not_linearIndependent_of_infinite v hv

/-- For open convex planar sets, a nontrivial real smooth nullspace is equivalent to an
ellipse sandwich. -/
theorem realSmoothNullspace_ne_bot_iff {D₀ D : Set E} (hD₀o : IsOpen D₀)
    (hD₀c : Convex ℝ D₀) (hDo : IsOpen D) (hDc : Convex ℝ D) :
    realSmoothNullspace D₀ D ≠ ⊥ ↔ EllipseSandwich D₀ D := by
  constructor
  · intro h
    exact ((ellipse_criterion hD₀o hD₀c hDo hDc).out 1 3).mp
      (smoothNullExists_of_realSmoothNullspace_ne_bot h)
  · intro h hbot
    have hfinite : Module.Finite ℝ (realSmoothNullspace D₀ D) := by
      rw [hbot]
      infer_instance
    exact realSmoothNullspace_infinite_of_ellipseSandwich hDo h hfinite

/-- Infinite dimension is equivalent to the ellipse criterion for open convex planar sets. -/
theorem realSmoothNullspace_infinite_iff {D₀ D : Set E} (hD₀o : IsOpen D₀)
    (hD₀c : Convex ℝ D₀) (hDo : IsOpen D) (hDc : Convex ℝ D) :
    (¬ Module.Finite ℝ (realSmoothNullspace D₀ D)) ↔ EllipseSandwich D₀ D := by
  refine ⟨fun h ↦ (realSmoothNullspace_ne_bot_iff hD₀o hD₀c hDo hDc).mp ?_,
    realSmoothNullspace_infinite_of_ellipseSandwich hDo⟩
  intro hbot
  apply h
  rw [hbot]
  infer_instance

/-- The sentence after **Proposition 5**: the real smooth nullspace for open convex planar
sets is either zero or infinite dimensional. Empty and unbounded sets are allowed. -/
theorem realSmoothNullspace_eq_bot_or_infinite {D₀ D : Set E} (hD₀o : IsOpen D₀)
    (hD₀c : Convex ℝ D₀) (hDo : IsOpen D) (hDc : Convex ℝ D) :
    realSmoothNullspace D₀ D = ⊥ ∨ ¬ Module.Finite ℝ (realSmoothNullspace D₀ D) := by
  by_cases h : realSmoothNullspace D₀ D = ⊥
  · exact Or.inl h
  · exact Or.inr ((realSmoothNullspace_infinite_iff hD₀o hD₀c hDo hDc).mpr
      ((realSmoothNullspace_ne_bot_iff hD₀o hD₀c hDo hDc).mp h))

end LeanestEllipse
