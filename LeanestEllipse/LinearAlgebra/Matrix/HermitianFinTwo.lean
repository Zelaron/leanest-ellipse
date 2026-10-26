import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Hermitian `2 × 2` matrices and the ellipse of a complex `2 × 2` matrix

We compute the (real) spectrum of a Hermitian `2 × 2` matrix: the spectrum of
`!![a, x; star x, d]` (with `a d : ℝ`) is `{m - √r, m + √r}` where `m = (a + d) / 2` and
`r = ((a - d) / 2) ^ 2 + ‖x‖ ^ 2`.

As an application we prove [Hägg, Lemma 9]: for every `C : Matrix (Fin 2) (Fin 2) ℂ` there are a
center `c : Fin 2 → ℝ` and a positive semidefinite `Q : Matrix (Fin 2) (Fin 2) ℝ` such that, for
every `θ`, the two eigenvalues of the Hermitian matrix `ℜ (exp (-θ i) • C)` are
`c ⬝ᵥ ω_θ ∓ √(ω_θ ⬝ᵥ Q *ᵥ ω_θ)`, where `ω_θ = ![cos θ, sin θ]`.  Explicitly, with `τ = tr C / 2`,
`c = (Re τ, Im τ)` and `Q i j = tr (C_i C_j) / 2` where `C₁ = ℜ (C - τ • 1)` and
`C₂ = ℑ (C - τ • 1)`.  These are the projection endpoints of the (possibly degenerate) elliptic disk
`c + Q^{1/2} (closed unit disk)`; if the two eigenvalues are distinct for every `θ`, then `Q` is
positive definite.

## Main results

* `Matrix.mem_spectrum_real_fin_two_iff`, `Matrix.spectrum_real_fin_two`: the spectrum of
  `!![a, x; star x, d]`.
* `Matrix.IsHermitian.spectrum_real_fin_two`: the spectrum of a Hermitian `2 × 2` matrix.
* `Matrix.ellipseCenter`, `Matrix.ellipseShape`, `Matrix.spectrum_realPart_exp_smul_fin_two`,
  `Matrix.posSemidef_ellipseShape`, `Matrix.posDef_ellipseShape_of_forall_pos`,
  `Matrix.posDef_ellipseShape_of_nontrivial`.
* `Matrix.exists_center_shape_fin_two`: [Hägg, Lemma 9].

## References

* C. Hägg, *An ellipse criterion for exact nonuniqueness in the planar interior Radon problem*.
-/

noncomputable section

open scoped ComplexStarModule Matrix ComplexConjugate

namespace Matrix

/-! ### The spectrum of a Hermitian `2 × 2` matrix -/

section Hermitian

variable {𝕜 : Type*} [RCLike 𝕜]

open RCLike in
/-- A real number `t` lies in the spectrum of `!![a, x; star x, d]` iff it is a root of the
characteristic polynomial `(t - a) * (t - d) - ‖x‖ ^ 2`. -/
theorem mem_spectrum_real_fin_two_iff (a d : ℝ) (x : 𝕜) (t : ℝ) :
    t ∈ spectrum ℝ !![(a : 𝕜), x; star x, (d : 𝕜)] ↔ (t - a) * (t - d) = ‖x‖ ^ 2 := by
  have hdet : (algebraMap ℝ (Matrix (Fin 2) (Fin 2) 𝕜) t - !![(a : 𝕜), x; star x, (d : 𝕜)]).det =
      (((t - a) * (t - d) - ‖x‖ ^ 2 : ℝ) : 𝕜) := by
    rw [det_fin_two, algebraMap_eq_diagonal]
    simp only [sub_apply, diagonal_apply_eq, diagonal_apply_ne _ (by decide : (0 : Fin 2) ≠ 1),
      diagonal_apply_ne _ (by decide : (1 : Fin 2) ≠ 0), of_apply, cons_val', cons_val_zero,
      cons_val_one, empty_val', cons_val_fin_one, zero_sub, neg_mul_neg, star_def, mul_conj,
      Pi.algebraMap_apply, algebraMap_eq_ofReal]
    push_cast
    ring
  rw [spectrum.mem_iff, isUnit_iff_isUnit_det, hdet, isUnit_iff_ne_zero, not_not,
    ofReal_eq_zero, sub_eq_zero]

/-- Solving the characteristic equation of a Hermitian `2 × 2` matrix. -/
private theorem sub_mul_sub_eq_iff (a d r t : ℝ) (hr : 0 ≤ r) :
    (t - a) * (t - d) = r ↔
      t = (a + d) / 2 - √(((a - d) / 2) ^ 2 + r) ∨ t = (a + d) / 2 + √(((a - d) / 2) ^ 2 + r) := by
  have hD : 0 ≤ ((a - d) / 2) ^ 2 + r := by positivity
  have hsq := Real.sq_sqrt hD
  have key : (t - a) * (t - d) = r ↔
      (t - (a + d) / 2) ^ 2 = (√(((a - d) / 2) ^ 2 + r)) ^ 2 := by
    rw [hsq]
    constructor <;> intro h <;> linarith
  rw [key, sq_eq_sq_iff_eq_or_eq_neg]
  constructor
  · rintro (h | h)
    · right; linarith
    · left; linarith
  · rintro (h | h)
    · right; linarith
    · left; linarith

/-- **The spectrum of a Hermitian `2 × 2` matrix** `!![a, x; star x, d]`. -/
theorem spectrum_real_fin_two (a d : ℝ) (x : 𝕜) :
    spectrum ℝ !![(a : 𝕜), x; star x, (d : 𝕜)] =
      {(a + d) / 2 - √(((a - d) / 2) ^ 2 + ‖x‖ ^ 2),
        (a + d) / 2 + √(((a - d) / 2) ^ 2 + ‖x‖ ^ 2)} := by
  ext t
  rw [mem_spectrum_real_fin_two_iff, sub_mul_sub_eq_iff a d _ t (sq_nonneg _),
    Set.mem_insert_iff, Set.mem_singleton_iff]

open RCLike in
/-- Membership in the spectrum of a Hermitian `2 × 2` matrix. -/
theorem IsHermitian.mem_spectrum_real_fin_two_iff {A : Matrix (Fin 2) (Fin 2) 𝕜}
    (hA : A.IsHermitian) (t : ℝ) :
    t ∈ spectrum ℝ A ↔ (t - re (A 0 0)) * (t - re (A 1 1)) = ‖A 0 1‖ ^ 2 := by
  have hA' : A = !![((re (A 0 0) : ℝ) : 𝕜), A 0 1; star (A 0 1), ((re (A 1 1) : ℝ) : 𝕜)] := by
    conv_lhs => rw [eta_fin_two A]
    rw [hA.coe_re_apply_self 0, hA.coe_re_apply_self 1, hA.apply 1 0]
  rw [hA', Matrix.mem_spectrum_real_fin_two_iff]
  simp

open RCLike in
/-- **The spectrum of a Hermitian `2 × 2` matrix** `A` consists of the two roots
`m ∓ √(((re A₀₀ - re A₁₁) / 2) ^ 2 + ‖A₀₁‖ ^ 2)`, `m = (re A₀₀ + re A₁₁) / 2`, of its
characteristic polynomial. -/
theorem IsHermitian.spectrum_real_fin_two {A : Matrix (Fin 2) (Fin 2) 𝕜} (hA : A.IsHermitian) :
    spectrum ℝ A =
      {(re (A 0 0) + re (A 1 1)) / 2 - √(((re (A 0 0) - re (A 1 1)) / 2) ^ 2 + ‖A 0 1‖ ^ 2),
        (re (A 0 0) + re (A 1 1)) / 2 + √(((re (A 0 0) - re (A 1 1)) / 2) ^ 2 + ‖A 0 1‖ ^ 2)} := by
  ext t
  rw [hA.mem_spectrum_real_fin_two_iff, sub_mul_sub_eq_iff _ _ _ t (sq_nonneg _),
    Set.mem_insert_iff, Set.mem_singleton_iff]

end Hermitian

/-! ### Real and imaginary parts of complex matrices -/

section RealPart

variable {n : Type*}

/-- The entries of the real part `ℜ M = (M + Mᴴ) / 2` of a complex matrix. -/
theorem realPart_apply (M : Matrix n n ℂ) (i j : n) :
    (ℜ M : Matrix n n ℂ) i j = 2⁻¹ * (M i j + star (M j i)) := by
  rw [realPart_apply_coe, smul_apply, add_apply, star_eq_conjTranspose, conjTranspose_apply,
    Complex.real_smul]
  push_cast
  ring

/-- The entries of the imaginary part `ℑ M = (M - Mᴴ) / (2 i)` of a complex matrix. -/
theorem imaginaryPart_apply (M : Matrix n n ℂ) (i j : n) :
    (ℑ M : Matrix n n ℂ) i j = -Complex.I * 2⁻¹ * (M i j - star (M j i)) := by
  rw [imaginaryPart_apply_coe, smul_apply, smul_apply, sub_apply, star_eq_conjTranspose,
    conjTranspose_apply, smul_eq_mul, Complex.real_smul]
  push_cast
  ring

/-- The real part of a complex matrix is Hermitian. -/
theorem isHermitian_realPart (M : Matrix n n ℂ) : (ℜ M : Matrix n n ℂ).IsHermitian :=
  (ℜ M).2.isHermitian

end RealPart

/-! ### The ellipse of a complex `2 × 2` matrix -/

section Ellipse

private theorem exp_neg_mul_I (θ : ℝ) :
    Complex.exp (-(θ * Complex.I)) = Real.cos θ - Real.sin θ * Complex.I := by
  rw [← neg_mul, ← Complex.ofReal_neg, Complex.exp_ofReal_mul_I, Real.cos_neg, Real.sin_neg,
    Complex.ofReal_neg]
  ring

/-- The center `c = (Re τ, Im τ)`, `τ = tr C / 2`, of the ellipse of a complex `2 × 2` matrix
([Hägg, Lemma 9]). -/
def ellipseCenter (C : Matrix (Fin 2) (Fin 2) ℂ) : Fin 2 → ℝ :=
  ![(C.trace / 2).re, (C.trace / 2).im]

/-- The traceless Hermitian matrices `C₁ = ℜ (C - τ • 1)` and `C₂ = ℑ (C - τ • 1)`, `τ = tr C / 2`,
of [Hägg, proof of Lemma 9], so that `ℜ (exp (-θ i) • C) = (c ⬝ᵥ ω_θ) • 1 + cos θ • C₁ + sin θ • C₂`
with `c = ellipseCenter C`. -/
def ellipseAxes (C : Matrix (Fin 2) (Fin 2) ℂ) : Fin 2 → Matrix (Fin 2) (Fin 2) ℂ :=
  ![(ℜ (C - (C.trace / 2) • 1) : Matrix (Fin 2) (Fin 2) ℂ),
    (ℑ (C - (C.trace / 2) • 1) : Matrix (Fin 2) (Fin 2) ℂ)]

/-- The shape matrix `Q` of the ellipse of a complex `2 × 2` matrix: `Q i j = tr (C_i C_j) / 2`
where `C_i = ellipseAxes C i` ([Hägg, Lemma 9]). -/
def ellipseShape (C : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of fun i j ↦ ((ellipseAxes C i * ellipseAxes C j).trace / 2).re

/-- The entries `Q i j = tr (C_i C_j) / 2` of the shape matrix. -/
theorem ellipseShape_apply (C : Matrix (Fin 2) (Fin 2) ℂ) (i j : Fin 2) :
    ellipseShape C i j = ((ellipseAxes C i * ellipseAxes C j).trace / 2).re :=
  rfl

/-- The center of the ellipse, paired with `ω_θ = ![cos θ, sin θ]`, is `re (exp (-θ i) * τ)`
written out in coordinates. -/
theorem ellipseCenter_dotProduct (C : Matrix (Fin 2) (Fin 2) ℂ) (θ : ℝ) :
    ellipseCenter C ⬝ᵥ ![Real.cos θ, Real.sin θ] =
      Real.cos θ * ((C 0 0).re + (C 1 1).re) / 2 + Real.sin θ * ((C 0 0).im + (C 1 1).im) / 2 := by
  simp [ellipseCenter, trace_fin_two]
  ring

/-- The quadratic form of the shape matrix is a sum of three squares of linear forms (in particular
it is nonnegative). -/
theorem dotProduct_ellipseShape_mulVec (C : Matrix (Fin 2) (Fin 2) ℂ) (x : Fin 2 → ℝ) :
    x ⬝ᵥ (ellipseShape C *ᵥ x) =
      (x 0 * ((C 0 0).re - (C 1 1).re) / 2 + x 1 * ((C 0 0).im - (C 1 1).im) / 2) ^ 2 +
      (x 0 * ((C 0 1).re + (C 1 0).re) / 2 + x 1 * ((C 0 1).im + (C 1 0).im) / 2) ^ 2 +
      (x 0 * ((C 0 1).im - (C 1 0).im) / 2 + x 1 * ((C 1 0).re - (C 0 1).re) / 2) ^ 2 := by
  simp [ellipseShape, ellipseAxes, mulVec, dotProduct, Fin.sum_univ_two,
    trace_fin_two, mul_apply, realPart_apply, imaginaryPart_apply, Complex.mul_re, Complex.mul_im]
  ring

/-- The shape matrix of a complex `2 × 2` matrix is positive semidefinite. -/
theorem posSemidef_ellipseShape (C : Matrix (Fin 2) (Fin 2) ℂ) : (ellipseShape C).PosSemidef := by
  refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x ↦ ?_
  · refine IsHermitian.ext fun i j ↦ ?_
    simp only [star_trivial, ellipseShape_apply]
    rw [trace_mul_comm]
  · rw [star_trivial, dotProduct_ellipseShape_mulVec]
    positivity

/-- The rotated real part `ℜ (exp (-θ i) • C)` of a complex `2 × 2` matrix. -/
private theorem realPart_exp_smul_apply (C : Matrix (Fin 2) (Fin 2) ℂ) (θ : ℝ) (i j : Fin 2) :
    (ℜ (Complex.exp (-(θ * Complex.I)) • C) : Matrix (Fin 2) (Fin 2) ℂ) i j =
      2⁻¹ * ((Real.cos θ - Real.sin θ * Complex.I) * C i j +
        (Real.cos θ + Real.sin θ * Complex.I) * star (C j i)) := by
  rw [realPart_apply, smul_apply, smul_apply, exp_neg_mul_I, smul_eq_mul, smul_eq_mul, star_mul']
  congr 2
  simp [Complex.ext_iff]

/-- The decomposition `ℜ (exp (-θ i) • C) = (c ⬝ᵥ ω_θ) • 1 + cos θ • C₁ + sin θ • C₂` of
[Hägg, proof of Lemma 9], with `c = ellipseCenter C`, `C_i = ellipseAxes C i` and
`ω_θ = ![cos θ, sin θ]`. -/
theorem realPart_exp_smul_eq_ellipseAxes (C : Matrix (Fin 2) (Fin 2) ℂ) (θ : ℝ) :
    (ℜ (Complex.exp (-(θ * Complex.I)) • C) : Matrix (Fin 2) (Fin 2) ℂ) =
      ((ellipseCenter C ⬝ᵥ ![Real.cos θ, Real.sin θ] : ℝ) : ℂ) • 1 +
        (Real.cos θ : ℂ) • ellipseAxes C 0 + (Real.sin θ : ℂ) • ellipseAxes C 1 := by
  ext i j
  rw [realPart_exp_smul_apply, ellipseCenter_dotProduct]
  fin_cases i <;> fin_cases j <;>
    simp [ellipseAxes, realPart_apply, imaginaryPart_apply, trace_fin_two, Complex.ext_iff,
      Complex.mul_re, Complex.mul_im] <;> constructor <;> ring

private theorem pair_eq {m₁ m₂ r₁ r₂ : ℝ} (hm : m₁ = m₂) (hr : r₁ = r₂) :
    ({m₁ - √r₁, m₁ + √r₁} : Set ℝ) = {m₂ - √r₂, m₂ + √r₂} := by
  rw [hm, hr]

/-- **The eigenvalues of `ℜ (exp (-θ i) • C)`** for a complex `2 × 2` matrix `C`
([Hägg, Lemma 9]): they are `c ⬝ᵥ ω_θ ∓ √(ω_θ ⬝ᵥ Q *ᵥ ω_θ)` with `c = ellipseCenter C`,
`Q = ellipseShape C` and `ω_θ = ![cos θ, sin θ]`. -/
theorem spectrum_realPart_exp_smul_fin_two (C : Matrix (Fin 2) (Fin 2) ℂ) (θ : ℝ) :
    spectrum ℝ (ℜ (Complex.exp (-(θ * Complex.I)) • C) : Matrix (Fin 2) (Fin 2) ℂ) =
      {ellipseCenter C ⬝ᵥ ![Real.cos θ, Real.sin θ] -
          √(![Real.cos θ, Real.sin θ] ⬝ᵥ (ellipseShape C *ᵥ ![Real.cos θ, Real.sin θ])),
        ellipseCenter C ⬝ᵥ ![Real.cos θ, Real.sin θ] +
          √(![Real.cos θ, Real.sin θ] ⬝ᵥ (ellipseShape C *ᵥ ![Real.cos θ, Real.sin θ]))} := by
  set H := (ℜ (Complex.exp (-(θ * Complex.I)) • C) : Matrix (Fin 2) (Fin 2) ℂ) with hH
  have h00 : RCLike.re (H 0 0) = Real.cos θ * (C 0 0).re + Real.sin θ * (C 0 0).im := by
    rw [hH, realPart_exp_smul_apply]
    simp [Complex.mul_re, Complex.mul_im, Complex.cos_ofReal_re, Complex.sin_ofReal_re]
    ring
  have h11 : RCLike.re (H 1 1) = Real.cos θ * (C 1 1).re + Real.sin θ * (C 1 1).im := by
    rw [hH, realPart_exp_smul_apply]
    simp [Complex.mul_re, Complex.mul_im, Complex.cos_ofReal_re, Complex.sin_ofReal_re]
    ring
  have h01 : ‖H 0 1‖ ^ 2 =
      ((Real.cos θ * ((C 0 1).re + (C 1 0).re) + Real.sin θ * ((C 0 1).im + (C 1 0).im)) / 2) ^ 2 +
      ((Real.cos θ * ((C 0 1).im - (C 1 0).im) +
        Real.sin θ * ((C 1 0).re - (C 0 1).re)) / 2) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hH, realPart_exp_smul_apply]
    simp [Complex.mul_re, Complex.mul_im, Complex.cos_ofReal_re, Complex.sin_ofReal_re]
    ring
  rw [(isHermitian_realPart _).spectrum_real_fin_two]
  refine pair_eq ?_ ?_
  · rw [h00, h11, ellipseCenter_dotProduct]
    ring
  · rw [h00, h11, h01, dotProduct_ellipseShape_mulVec]
    simp
    ring

private theorem ellipseShape_smul (C : Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (x : Fin 2 → ℝ) :
    (r • x) ⬝ᵥ (ellipseShape C *ᵥ (r • x)) = r ^ 2 * (x ⬝ᵥ (ellipseShape C *ᵥ x)) := by
  rw [mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
  ring

/-- If the quadratic form of the shape matrix is positive on the unit circle, then the shape matrix
is positive definite. -/
theorem posDef_ellipseShape_of_forall_pos {C : Matrix (Fin 2) (Fin 2) ℂ}
    (h : ∀ θ : ℝ, 0 < ![Real.cos θ, Real.sin θ] ⬝ᵥ (ellipseShape C *ᵥ ![Real.cos θ, Real.sin θ])) :
    (ellipseShape C).PosDef := by
  refine posDef_iff_dotProduct_mulVec.mpr ⟨(posSemidef_ellipseShape C).isHermitian, fun x hx ↦ ?_⟩
  rw [star_trivial]
  obtain ⟨z, hz⟩ : ∃ z : ℂ, z = ⟨x 0, x 1⟩ := ⟨_, rfl⟩
  have hre : z.re = x 0 := by rw [hz]
  have him : z.im = x 1 := by rw [hz]
  have hz0 : z ≠ 0 := by
    intro h0
    apply hx
    ext i
    fin_cases i
    · simpa [hre] using congrArg Complex.re h0
    · simpa [him] using congrArg Complex.im h0
  have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz0
  have h0' : ‖z‖ * Real.cos (Complex.arg z) = x 0 := by
    rw [Complex.cos_arg hz0, hre]
    field_simp
  have h1' : ‖z‖ * Real.sin (Complex.arg z) = x 1 := by
    rw [Complex.sin_arg, him]
    field_simp
  have hx' : x = ‖z‖ • ![Real.cos (Complex.arg z), Real.sin (Complex.arg z)] := by
    ext i
    fin_cases i <;> simp [h0', h1']
  rw [hx', ellipseShape_smul]
  exact mul_pos (pow_pos (norm_pos_iff.mpr hz0) 2) (h _)

/-- The two eigenvalues of `ℜ (exp (-θ i) • C)` are distinct iff the quadratic form of the shape
matrix is positive at `ω_θ = ![cos θ, sin θ]`. -/
theorem nontrivial_spectrum_realPart_exp_smul_iff (C : Matrix (Fin 2) (Fin 2) ℂ) (θ : ℝ) :
    (spectrum ℝ (ℜ (Complex.exp (-(θ * Complex.I)) • C) : Matrix (Fin 2) (Fin 2) ℂ)).Nontrivial ↔
      0 < ![Real.cos θ, Real.sin θ] ⬝ᵥ (ellipseShape C *ᵥ ![Real.cos θ, Real.sin θ]) := by
  rw [spectrum_realPart_exp_smul_fin_two]
  have hq : 0 ≤ ![Real.cos θ, Real.sin θ] ⬝ᵥ (ellipseShape C *ᵥ ![Real.cos θ, Real.sin θ]) := by
    rw [dotProduct_ellipseShape_mulVec]
    positivity
  constructor
  · intro h
    rcases eq_or_lt_of_le hq with h0 | h0
    · rw [← h0, Real.sqrt_zero, sub_zero, add_zero, Set.pair_eq_singleton] at h
      exact absurd h Set.not_nontrivial_singleton
    · exact h0
  · intro h
    refine ⟨_, Set.mem_insert _ _, _, Set.mem_insert_of_mem _ rfl, fun heq ↦ ?_⟩
    have := Real.sqrt_pos.mpr h
    linarith

/-- If `ℜ (exp (-θ i) • C)` has two distinct eigenvalues for every `θ`, then the shape matrix of
`C` is positive definite ([Hägg, Lemma 9]). -/
theorem posDef_ellipseShape_of_nontrivial {C : Matrix (Fin 2) (Fin 2) ℂ}
    (h : ∀ θ : ℝ,
      (spectrum ℝ (ℜ (Complex.exp (-(θ * Complex.I)) • C) : Matrix (Fin 2) (Fin 2) ℂ)).Nontrivial) :
    (ellipseShape C).PosDef :=
  posDef_ellipseShape_of_forall_pos fun θ ↦ (nontrivial_spectrum_realPart_exp_smul_iff C θ).mp (h θ)

/-- **The ellipse of a `2 × 2` matrix** [Hägg, Lemma 9].  For every complex `2 × 2` matrix `C`
there are `c : Fin 2 → ℝ` and a positive semidefinite real matrix `Q` such that for every `θ` the
two eigenvalues of `ℜ (exp (-θ i) • C)` are `c ⬝ᵥ ω_θ ∓ √(ω_θ ⬝ᵥ Q *ᵥ ω_θ)`,
`ω_θ = ![cos θ, sin θ]`.  One can take `c = ellipseCenter C` and `Q = ellipseShape C`, see
`Matrix.spectrum_realPart_exp_smul_fin_two`; if the eigenvalues are distinct for every `θ`, then
`Q` is positive definite, see `Matrix.posDef_ellipseShape_of_nontrivial`. -/
theorem exists_center_shape_fin_two (C : Matrix (Fin 2) (Fin 2) ℂ) :
    ∃ (c : Fin 2 → ℝ) (Q : Matrix (Fin 2) (Fin 2) ℝ), Q.PosSemidef ∧ ∀ θ : ℝ,
      spectrum ℝ (ℜ (Complex.exp (-(θ * Complex.I)) • C) : Matrix (Fin 2) (Fin 2) ℂ) =
        {c ⬝ᵥ ![Real.cos θ, Real.sin θ] -
            √(![Real.cos θ, Real.sin θ] ⬝ᵥ (Q *ᵥ ![Real.cos θ, Real.sin θ])),
          c ⬝ᵥ ![Real.cos θ, Real.sin θ] +
            √(![Real.cos θ, Real.sin θ] ⬝ᵥ (Q *ᵥ ![Real.cos θ, Real.sin θ]))} :=
  ⟨ellipseCenter C, ellipseShape C, posSemidef_ellipseShape C,
    spectrum_realPart_exp_smul_fin_two C⟩

end Ellipse

end Matrix
