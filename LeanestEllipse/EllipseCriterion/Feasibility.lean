import LeanestEllipse.EllipseCriterion.Defs
import LeanestEllipse.Analysis.Convex.QuadraticFeasibility
import LeanestEllipse.Analysis.Convex.Ellipsoid.Complex

/-!
# The quadratic feasibility formulation (Remark 3)

This is the paper's compact-containment formulation of the general feasibility
theorem. In a Euclidean plane the center has two real coordinates and a self-adjoint
operator has three independent real matrix entries. The feasible set is convex by
`convex_setOf_quadratic_feasibility`.
-/

open Set Bornology
open scoped CompactlyContained RealInnerProductSpace

noncomputable section

namespace LeanestEllipse

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- **Remark 3**: the ellipse sandwich is equivalent to the four quadratic sign constraints.
The result holds in every finite dimension; convexity of the inner set is unnecessary. -/
theorem ellipseSandwich_iff_quadratic_feasibility {D₀ D : Set E}
    (hD₀o : IsOpen D₀) (hD₀ne : D₀.Nonempty) (hD₀D : D₀ ⋐ D)
    (hDo : IsOpen D) (hDc : Convex ℝ D) (hDb : IsBounded D) :
    EllipseSandwich D₀ D ↔
      ∃ (c : E) (B : E →L[ℝ] E), IsSelfAdjoint B ∧ ∀ ω : E, ‖ω‖ = 1 →
        0 < feasibilityQuadratic c B ω (lowerSupportFunction D ω) ∧
        feasibilityQuadratic c B ω (lowerSupportFunction D₀ ω) ≤ 0 ∧
        feasibilityQuadratic c B ω (supportFunction D₀ ω) ≤ 0 ∧
        0 < feasibilityQuadratic c B ω (supportFunction D ω) := by
  rw [← exists_ellipsoid_iff_quadratic_feasibility hD₀o hD₀ne hD₀D.subset hDo hDc hDb]
  exact ⟨fun ⟨e, h₀, h₁⟩ ↦ ⟨e, h₀, h₁.subset⟩,
    fun ⟨e, h₀, h₁⟩ ↦ ⟨e, h₀, CompactlyContained.of_isCompact e.isCompact h₁⟩⟩

/-- The monic quadratic in Remark 3, written in the five real coordinates
`c₁, c₂, b₁₁, b₁₂, b₂₂`. -/
def planarFeasibilityQuadratic (c₁ c₂ b₁₁ b₁₂ b₂₂ : ℝ) (ω : ℂ) (p : ℝ) : ℝ :=
  p ^ 2 - 2 * (c₁ * ω.re + c₂ * ω.im) * p +
    b₁₁ * ω.re ^ 2 + 2 * b₁₂ * ω.re * ω.im + b₂₂ * ω.im ^ 2

private theorem feasibilityQuadratic_coordinates (c₁ c₂ b₁₁ b₁₂ b₂₂ : ℝ)
    (ω : ℂ) (p : ℝ) :
    feasibilityQuadratic (⟨c₁, c₂⟩ : ℂ)
      (Complex.matrixToComplexCLM !![b₁₁, b₁₂; b₁₂, b₂₂]) ω p =
        planarFeasibilityQuadratic c₁ c₂ b₁₁ b₁₂ b₂₂ ω p := by
  simp [feasibilityQuadratic, planarFeasibilityQuadratic, Complex.inner, Complex.mul_re]
  ring

/-- **Remark 3**, literally in five real variables: two center coordinates and the three
independent entries of the real symmetric matrix. -/
theorem ellipseSandwich_iff_five_variable_feasibility {D₀ D : Set ℂ}
    (hD₀o : IsOpen D₀) (hD₀ne : D₀.Nonempty) (hD₀D : D₀ ⋐ D)
    (hDo : IsOpen D) (hDc : Convex ℝ D) (hDb : IsBounded D) :
    EllipseSandwich D₀ D ↔
      ∃ c₁ c₂ b₁₁ b₁₂ b₂₂ : ℝ, ∀ ω : ℂ, ‖ω‖ = 1 →
        0 < planarFeasibilityQuadratic c₁ c₂ b₁₁ b₁₂ b₂₂ ω (lowerSupportFunction D ω) ∧
        planarFeasibilityQuadratic c₁ c₂ b₁₁ b₁₂ b₂₂ ω (lowerSupportFunction D₀ ω) ≤ 0 ∧
        planarFeasibilityQuadratic c₁ c₂ b₁₁ b₁₂ b₂₂ ω (supportFunction D₀ ω) ≤ 0 ∧
        0 < planarFeasibilityQuadratic c₁ c₂ b₁₁ b₁₂ b₂₂ ω (supportFunction D ω) := by
  rw [ellipseSandwich_iff_quadratic_feasibility hD₀o hD₀ne hD₀D hDo hDc hDb]
  constructor
  · rintro ⟨c, B, hB, h⟩
    obtain ⟨a, b, d, rfl⟩ := Complex.exists_eq_matrixToComplexCLM_of_isSelfAdjoint hB
    refine ⟨c.re, c.im, a, b, d, ?_⟩
    simpa only [← feasibilityQuadratic_coordinates, Complex.eta] using h
  · rintro ⟨c₁, c₂, a, b, d, h⟩
    refine ⟨⟨c₁, c₂⟩, Complex.matrixToComplexCLM !![a, b; b, d],
      Complex.isSelfAdjoint_matrixToComplexCLM ?_, ?_⟩
    · ext i j
      fin_cases i <;> fin_cases j <;> simp
    · simpa only [feasibilityQuadratic_coordinates] using h

end LeanestEllipse
