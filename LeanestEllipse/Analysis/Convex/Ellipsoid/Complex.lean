import LeanestEllipse.Analysis.Convex.Ellipsoid
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Real matrices and ellipses in the complex plane

Identify the Euclidean plane with `ℂ`. A real two by two matrix defines a real continuous
linear map, and a positive definite matrix determines an ellipsoid with the expected support
function. These results are independent of Radon transforms.
-/

open Complex Matrix
open scoped Real RealInnerProductSpace

noncomputable section

namespace Complex

/-! ### The ellipse with prescribed center and shape matrix -/

/-- The `ℝ`-linear map of `ℂ` whose matrix in the basis `(1, i)` is `Q`. -/
def matrixToComplexCLM (Q : Matrix (Fin 2) (Fin 2) ℝ) : ℂ →L[ℝ] ℂ :=
  (Q 0 0 • reCLM + Q 0 1 • imCLM).smulRight (1 : ℂ) + (Q 1 0 • reCLM + Q 1 1 • imCLM).smulRight I

@[simp] theorem matrixToComplexCLM_apply_re (Q : Matrix (Fin 2) (Fin 2) ℝ) (z : ℂ) :
    (matrixToComplexCLM Q z).re = Q 0 0 * z.re + Q 0 1 * z.im := by
  simp [matrixToComplexCLM]

@[simp] theorem matrixToComplexCLM_apply_im (Q : Matrix (Fin 2) (Fin 2) ℝ) (z : ℂ) :
    (matrixToComplexCLM Q z).im = Q 1 0 * z.re + Q 1 1 * z.im := by
  simp [matrixToComplexCLM]

theorem inner_matrixToComplexCLM (Q : Matrix (Fin 2) (Fin 2) ℝ) (z w : ℂ) :
    ⟪matrixToComplexCLM Q z, w⟫ = ![w.re, w.im] ⬝ᵥ (Q *ᵥ ![z.re, z.im]) := by
  rw [Complex.inner]
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, mul_re]
  ring

/-- A real symmetric matrix defines a self-adjoint real operator on the complex plane. -/
theorem isSelfAdjoint_matrixToComplexCLM {Q : Matrix (Fin 2) (Fin 2) ℝ}
    (hQ : Q.IsHermitian) : IsSelfAdjoint (matrixToComplexCLM Q) := by
  have hsym : Q 1 0 = Q 0 1 := by simpa using hQ.apply 0 1
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro x y
  change ⟪matrixToComplexCLM Q x, y⟫ = ⟪x, matrixToComplexCLM Q y⟫
  rw [real_inner_comm (matrixToComplexCLM Q y) x, inner_matrixToComplexCLM,
    inner_matrixToComplexCLM]
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, hsym]
  simp
  ring

/-- Every self-adjoint real operator on the complex plane is determined by three real
matrix entries. This is the coordinate parametrization of real symmetric `2 × 2` matrices. -/
theorem exists_eq_matrixToComplexCLM_of_isSelfAdjoint {B : ℂ →L[ℝ] ℂ}
    (hB : IsSelfAdjoint B) :
    ∃ a b d : ℝ, B = matrixToComplexCLM !![a, b; b, d] := by
  have hsym : (B I).re = (B 1).im := by
    have h := hB.isSymmetric I 1
    change ⟪B I, 1⟫ = ⟪I, B 1⟫ at h
    simpa [Complex.inner] using h
  refine ⟨(B 1).re, (B 1).im, (B I).im, ContinuousLinearMap.ext fun z ↦ ?_⟩
  have hz : z = z.re • (1 : ℂ) + z.im • I := by
    simp [Complex.real_smul, Complex.re_add_im]
  have hBz : B z = z.re • B 1 + z.im • B I := by
    conv_lhs => rw [hz]
    rw [map_add, map_smul, map_smul]
  apply Complex.ext <;> simp [hBz, hsym] <;> ring

/-- A vector `c` and a positive definite real `2 × 2` matrix `Q` define an ellipse in `ℂ` whose
support function in the direction `e^{iθ}` is `c ⬝ᵥ ω_θ + √(ω_θ ⬝ᵥ Q ω_θ)`,
`ω_θ = (cos θ, sin θ)` ([Hägg, (1.3)]). -/
theorem exists_ellipsoid_of_posDef (c : Fin 2 → ℝ) {Q : Matrix (Fin 2) (Fin 2) ℝ}
    (hQ : Q.PosDef) :
    ∃ e : Ellipsoid ℂ, ∀ θ : ℝ, supportFunction (e : Set ℂ) (exp (θ * I)) =
      c ⬝ᵥ ![Real.cos θ, Real.sin θ] +
        √(![Real.cos θ, Real.sin θ] ⬝ᵥ (Q *ᵥ ![Real.cos θ, Real.sin θ])) := by
  have hsym : Q 1 0 = Q 0 1 := by simpa using hQ.isHermitian.apply 0 1
  have hsa : IsSelfAdjoint (matrixToComplexCLM Q) := by
    rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
    intro x y
    change ⟪matrixToComplexCLM Q x, y⟫ = ⟪x, matrixToComplexCLM Q y⟫
    rw [real_inner_comm (matrixToComplexCLM Q y) x, inner_matrixToComplexCLM,
      inner_matrixToComplexCLM]
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, hsym]
    simp
    ring
  have hpos : ∀ x : ℂ, x ≠ 0 → 0 < ⟪matrixToComplexCLM Q x, x⟫ := by
    intro x hx
    rw [inner_matrixToComplexCLM]
    have hx' : ![x.re, x.im] ≠ 0 := by
      intro h
      apply hx
      apply Complex.ext
      · simpa using congrFun h 0
      · simpa using congrFun h 1
    simpa using hQ.dotProduct_mulVec_pos hx'
  obtain ⟨e, hc, hQe⟩ := Ellipsoid.exists_center_shape_eq (⟨c 0, c 1⟩ : ℂ) hsa hpos
  refine ⟨e, fun θ ↦ ?_⟩
  rw [e.supportFunction_eq_sqrt, hc, hQe, inner_matrixToComplexCLM, exp_ofReal_mul_I_re,
    exp_ofReal_mul_I_im]
  congr 1
  rw [Complex.inner]
  simp [dotProduct, Fin.sum_univ_two, mul_re, exp_ofReal_mul_I_re, exp_ofReal_mul_I_im]
  ring

end Complex
