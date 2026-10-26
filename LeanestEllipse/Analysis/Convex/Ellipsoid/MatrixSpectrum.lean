import LeanestEllipse.Analysis.Convex.Ellipsoid.Complex
import LeanestEllipse.Analysis.Convex.Ellipsoid.Degenerate
import LeanestEllipse.LinearAlgebra.Matrix.HermitianFinTwo
import Mathlib.Analysis.Matrix.Order

/-!
# The possibly degenerate elliptic disk of a complex matrix

Every complex `2 × 2` matrix has an affine image of the closed unit disk whose projection
endpoints are the eigenvalues of its rotated real parts. This includes scalar matrices and
degenerate line segments. The linear parametrization is the positive square root of the
real shape matrix from `Matrix.ellipseShape`.
-/

open Complex Matrix Set Metric
open scoped Real RealInnerProductSpace ComplexStarModule MatrixOrder

noncomputable section

namespace Complex

/-- The matrix-to-operator correspondence respects multiplication. -/
theorem matrixToComplexCLM_mul (A B : Matrix (Fin 2) (Fin 2) ℝ) :
    matrixToComplexCLM (A * B) = matrixToComplexCLM A * matrixToComplexCLM B := by
  ext z
  apply Complex.ext <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- The norm of the square-root operator in a direction is the square root of the
corresponding quadratic form, including singular positive semidefinite matrices. -/
theorem norm_adjoint_matrixToComplexCLM_sqrt {Q : Matrix (Fin 2) (Fin 2) ℝ}
    (hQ : Q.PosSemidef) (ω : ℂ) :
    ‖ContinuousLinearMap.adjoint (matrixToComplexCLM (CFC.sqrt Q)) ω‖ =
      √(![ω.re, ω.im] ⬝ᵥ (Q *ᵥ ![ω.re, ω.im])) := by
  set A := matrixToComplexCLM (CFC.sqrt Q)
  have hA : IsSelfAdjoint A :=
    isSelfAdjoint_matrixToComplexCLM (CFC.sqrt_nonneg Q).posSemidef.isHermitian
  have hAA : A * A = matrixToComplexCLM Q := by
    rw [← matrixToComplexCLM_mul, CFC.sqrt_mul_sqrt_self Q hQ.nonneg]
  have hs : ‖ContinuousLinearMap.adjoint A ω‖ ^ 2 =
      ![ω.re, ω.im] ⬝ᵥ (Q *ᵥ ![ω.re, ω.im]) := by
    rw [← inner_matrixToComplexCLM, ← hAA, mul_apply_eq_comp]
    rw [← ContinuousLinearMap.adjoint_inner_right]
    have hstar : ContinuousLinearMap.adjoint A = A := hA.star_eq
    rw [hstar, real_inner_self_eq_norm_sq]
  calc
    ‖ContinuousLinearMap.adjoint A ω‖ = √(‖ContinuousLinearMap.adjoint A ω‖ ^ 2) :=
      (Real.sqrt_sq (norm_nonneg _)).symm
    _ = √(![ω.re, ω.im] ⬝ᵥ (Q *ᵥ ![ω.re, ω.im])) := congrArg Real.sqrt hs

end Complex

namespace Matrix

/-- The possibly degenerate elliptic disk associated with a complex `2 × 2` matrix. -/
def ellipseDisk (C : Matrix (Fin 2) (Fin 2) ℂ) : Set ℂ :=
  (fun z ↦ (⟨ellipseCenter C 0, ellipseCenter C 1⟩ : ℂ) +
    Complex.matrixToComplexCLM (CFC.sqrt (ellipseShape C)) z) '' closedBall 0 1

/-- The geometric consequence of the matrix-ellipse theorem: the two directional eigenvalues
are exactly the lower and upper projection endpoints of a possibly degenerate elliptic disk. -/
theorem spectrum_realPart_eq_endpoints_ellipseDisk (C : Matrix (Fin 2) (Fin 2) ℂ) (θ : ℝ) :
    spectrum ℝ (ℜ (exp (-(θ * I)) • C) : Matrix (Fin 2) (Fin 2) ℂ) =
      {lowerSupportFunction (ellipseDisk C) (exp (θ * I)),
        supportFunction (ellipseDisk C) (exp (θ * I))} := by
  rw [spectrum_realPart_exp_smul_fin_two, ellipseDisk,
    lowerSupportFunction_affine_image_closedBall, supportFunction_affine_image_closedBall,
    Complex.norm_adjoint_matrixToComplexCLM_sqrt (posSemidef_ellipseShape C),
    exp_ofReal_mul_I_re, exp_ofReal_mul_I_im]
  have hc : ⟪(⟨ellipseCenter C 0, ellipseCenter C 1⟩ : ℂ), exp (θ * I)⟫ =
      ellipseCenter C ⬝ᵥ ![Real.cos θ, Real.sin θ] := by
    simp [Complex.inner, dotProduct, Fin.sum_univ_two,
      exp_ofReal_mul_I_re, exp_ofReal_mul_I_im, Complex.mul_re]
    ring
  rw [hc]

/-- If all directional eigenvalues are distinct, the disk associated with the matrix is
a nondegenerate ellipse, as a set and not only at the level of its shape matrix. -/
theorem exists_ellipsoid_eq_ellipseDisk {C : Matrix (Fin 2) (Fin 2) ℂ}
    (h : ∀ θ : ℝ,
      (spectrum ℝ (ℜ (exp (-(θ * I)) • C) : Matrix (Fin 2) (Fin 2) ℂ)).Nontrivial) :
    ∃ e : Ellipsoid ℂ, (e : Set ℂ) = ellipseDisk C := by
  have hQ := posDef_ellipseShape_of_nontrivial h
  let A := Complex.matrixToComplexCLM (CFC.sqrt (ellipseShape C))
  have hstar : ContinuousLinearMap.adjoint A = A :=
    (Complex.isSelfAdjoint_matrixToComplexCLM
      (CFC.sqrt_nonneg (ellipseShape C)).posSemidef.isHermitian).star_eq
  have hinj : Function.Injective A := by
    intro x y hxy
    apply sub_eq_zero.mp
    by_contra hne
    have hv : ![(x - y).re, (x - y).im] ≠ 0 := by
      intro hv
      apply hne
      apply Complex.ext
      · simpa using congrFun hv 0
      · simpa using congrFun hv 1
    have hpos := Real.sqrt_pos.mpr (hQ.dotProduct_mulVec_pos hv)
    have hn := Complex.norm_adjoint_matrixToComplexCLM_sqrt hQ.posSemidef (x - y)
    change ‖ContinuousLinearMap.adjoint A (x - y)‖ = _ at hn
    rw [hstar, map_sub, hxy, sub_self, norm_zero] at hn
    exact hpos.ne' hn.symm
  exact ⟨⟨⟨ellipseCenter C 0, ellipseCenter C 1⟩,
    (LinearEquiv.ofInjectiveEndo A.toLinearMap hinj).toContinuousLinearEquiv⟩, rfl⟩

end Matrix
