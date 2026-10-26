import LeanestEllipse.IntegralGeometry.Radon.Basic
import Mathlib.MeasureTheory.Constructions.HaarToSphere

/-!
# Backprojection of hyperplane data

Backprojection integrates the data of all hyperplanes through a point, with surface measure
on the unit sphere. Data vanishing on every hyperplane meeting a set give a backprojection
vanishing on that set, in every finite dimension.
-/

open MeasureTheory Metric
open scoped RealInnerProductSpace

noncomputable section

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Backprojection of hyperplane data against surface measure on the unit sphere. -/
def radonBackprojection (φ : E → ℝ → F) (x : E) : F :=
  ∫ ω : sphere (0 : E) 1, φ ω ⟪x, (ω : E)⟫ ∂(volume : Measure E).toSphere

/-- If the data vanish on each hyperplane through `x`, their backprojection is zero at `x`. -/
theorem radonBackprojection_eq_zero {φ : E → ℝ → F} {x : E}
    (h : ∀ ω : E, ‖ω‖ = 1 → φ ω ⟪x, ω⟫ = 0) : radonBackprojection φ x = 0 := by
  apply integral_eq_zero_of_ae
  exact Filter.Eventually.of_forall fun ω ↦ h ω (by simp)

/-- Vanishing on all hyperplanes meeting a set implies vanishing of backprojection on that
set. Neither openness nor regularity of the set or data is required. -/
theorem radonBackprojection_eqOn_zero {φ : E → ℝ → F} {D : Set E}
    (h : ∀ ω : E, ‖ω‖ = 1 → ∀ p : ℝ,
      (∃ x ∈ D, ⟪x, ω⟫ = p) → φ ω p = 0) : Set.EqOn (radonBackprojection φ) 0 D :=
  fun x hx ↦ radonBackprojection_eq_zero fun ω hω ↦ h ω hω _ ⟨x, hx, rfl⟩
