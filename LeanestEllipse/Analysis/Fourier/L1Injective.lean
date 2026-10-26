import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# Uniqueness of the Fourier transform on `L¹`

For an integrable function `f` on a finite dimensional real inner product space `E` we write
`∫ x, e^{-i⟪x, ξ⟫} f x` for its (unnormalized) Fourier transform at `ξ` (the convention of
[Hägg]).  We prove:

* `continuous_integral_exp_inner_smul`: this is a continuous function of `ξ`;
* `ae_eq_zero_of_integral_exp_inner_smul_eq_zero`: **uniqueness**, if it vanishes for every `ξ`
  then `f = 0` almost everywhere.

The proof avoids Fourier inversion (which needs integrability of the Fourier transform): for real
`f` the positive and negative parts `f^± dx` are finite measures with the same characteristic
function, hence equal (`MeasureTheory.Measure.ext_of_charFunDual`).
-/

open MeasureTheory Filter
open scoped RealInnerProductSpace ComplexConjugate

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem norm_exp_neg_inner_mul_I (x ξ : E) :
    ‖Complex.exp (-(⟪x, ξ⟫ : ℝ) * Complex.I)‖ = 1 := by
  rw [Complex.norm_exp]
  simp

theorem integrable_exp_inner_smul {f : E → G} (hf : Integrable f) (ξ : E) :
    Integrable fun x ↦ Complex.exp (-(⟪x, ξ⟫ : ℝ) * Complex.I) • f x :=
  hf.bdd_smul (φ := fun x ↦ Complex.exp (-(⟪x, ξ⟫ : ℝ) * Complex.I)) 1
    (Continuous.aestronglyMeasurable (by fun_prop))
    (Eventually.of_forall fun x ↦ (norm_exp_neg_inner_mul_I x ξ).le)

/-- The Fourier transform `ξ ↦ ∫ x, e^{-i⟪x, ξ⟫} f x` of an integrable function is continuous. -/
theorem continuous_integral_exp_inner_smul {f : E → G} (hf : Integrable f) :
    Continuous fun ξ : E ↦ ∫ x, Complex.exp (-(⟪x, ξ⟫ : ℝ) * Complex.I) • f x := by
  refine continuous_of_dominated (bound := fun x ↦ ‖f x‖)
    (fun ξ ↦ (integrable_exp_inner_smul hf ξ).aestronglyMeasurable)
    (fun ξ ↦ Eventually.of_forall fun x ↦ ?_) hf.norm (Eventually.of_forall fun x ↦ ?_)
  · rw [norm_smul, norm_exp_neg_inner_mul_I, one_mul]
  · exact Continuous.smul (by fun_prop) continuous_const

section Real

/-- The characteristic function of `f⁺ dx - f⁻ dx`. -/
private theorem charFunDual_withDensity_posPart_sub_negPart {f : E → ℝ} (hf : Integrable f)
    (L : StrongDual ℝ E) :
    charFunDual (volume.withDensity fun x ↦ ENNReal.ofReal (f x)) L -
        charFunDual (volume.withDensity fun x ↦ ENNReal.ofReal (-f x)) L =
      ∫ x, (f x : ℂ) * Complex.exp ((L x : ℂ) * Complex.I) := by
  have hpos : Integrable (fun x ↦ (max (f x) 0 : ℝ) • Complex.exp ((L x : ℂ) * Complex.I)) :=
    hf.pos_part.smul_bdd (f := fun x ↦ Complex.exp ((L x : ℂ) * Complex.I)) 1
      (Continuous.aestronglyMeasurable (by fun_prop))
      (Eventually.of_forall fun x ↦ by rw [Complex.norm_exp]; simp)
  have hneg : Integrable (fun x ↦ (max (-f x) 0 : ℝ) • Complex.exp ((L x : ℂ) * Complex.I)) :=
    hf.neg_part.smul_bdd (f := fun x ↦ Complex.exp ((L x : ℂ) * Complex.I)) 1
      (Continuous.aestronglyMeasurable (by fun_prop))
      (Eventually.of_forall fun x ↦ by rw [Complex.norm_exp]; simp)
  rw [charFunDual_apply, charFunDual_apply,
    integral_withDensity_eq_integral_toReal_smul₀
      hf.aestronglyMeasurable.aemeasurable.ennreal_ofReal (Eventually.of_forall fun _ ↦ by simp),
    integral_withDensity_eq_integral_toReal_smul₀
      (show AEMeasurable (fun x ↦ ENNReal.ofReal (-f x)) volume from
        hf.aestronglyMeasurable.aemeasurable.neg.ennreal_ofReal)
      (Eventually.of_forall fun _ ↦ by simp)]
  simp only [ENNReal.toReal_ofReal']
  rw [← integral_sub hpos hneg]
  refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
  simp only [Complex.real_smul]
  rw [← sub_mul]
  congr 1
  exact_mod_cast max_zero_sub_max_neg_zero_eq_self (f x)

/-- Uniqueness for real integrable functions. -/
theorem ae_eq_zero_of_integral_exp_inner_mul_ofReal_eq_zero {f : E → ℝ} (hf : Integrable f)
    (h : ∀ ξ : E, ∫ x, Complex.exp (-(⟪x, ξ⟫ : ℝ) * Complex.I) * (f x : ℂ) = 0) :
    f =ᵐ[volume] 0 := by
  set μp : Measure E := volume.withDensity fun x ↦ ENNReal.ofReal (f x)
  set μn : Measure E := volume.withDensity fun x ↦ ENNReal.ofReal (-f x)
  have : IsFiniteMeasure μp := isFiniteMeasure_withDensity_ofReal hf.2
  have : IsFiniteMeasure μn := isFiniteMeasure_withDensity_ofReal hf.neg.2
  have hchar : charFunDual μp = charFunDual μn := by
    funext L
    rw [← sub_eq_zero, charFunDual_withDensity_posPart_sub_negPart hf L]
    have hL : ∀ x, (L x : ℂ) = -(⟪x, -(InnerProductSpace.toDual ℝ E).symm L⟫ : ℝ) := by
      intro x
      rw [inner_neg_right, Complex.ofReal_neg, neg_neg, real_inner_comm,
        InnerProductSpace.toDual_symm_apply]
    have := h (-(InnerProductSpace.toDual ℝ E).symm L)
    rw [← this]
    refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
    dsimp only
    rw [hL x, mul_comm]
  have hμ : μp = μn := Measure.ext_of_charFunDual hchar
  have hdens : (fun x ↦ ENNReal.ofReal (f x)) =ᵐ[volume] fun x ↦ ENNReal.ofReal (-f x) :=
    (withDensity_eq_iff_of_sigmaFinite hf.aestronglyMeasurable.aemeasurable.ennreal_ofReal
      (show AEMeasurable (fun x ↦ ENNReal.ofReal (-f x)) volume from
        hf.aestronglyMeasurable.aemeasurable.neg.ennreal_ofReal)).mp hμ
  filter_upwards [hdens] with x hx
  rcases lt_trichotomy (f x) 0 with hlt | heq | hgt
  · rw [ENNReal.ofReal_of_nonpos hlt.le, eq_comm, ENNReal.ofReal_eq_zero] at hx
    linarith
  · exact heq
  · rw [ENNReal.ofReal_of_nonpos (by linarith : -f x ≤ 0), ENNReal.ofReal_eq_zero] at hx
    linarith

end Real

private theorem ofReal_re_eq (z : ℂ) : ((z.re : ℝ) : ℂ) = (2 : ℂ)⁻¹ * (z + conj z) := by
  apply Complex.ext <;> simp
  ring

private theorem ofReal_im_eq (z : ℂ) : ((z.im : ℝ) : ℂ) = (-Complex.I / 2) * (z - conj z) := by
  apply Complex.ext <;> simp
  ring

/-- **Uniqueness of the Fourier transform on `L¹`**: an integrable complex function whose
Fourier transform `ξ ↦ ∫ x, e^{-i⟪x, ξ⟫} f x` vanishes identically is zero almost
everywhere. -/
theorem ae_eq_zero_of_integral_exp_inner_mul_eq_zero {f : E → ℂ} (hf : Integrable f)
    (h : ∀ ξ : E, ∫ x, Complex.exp (-(⟪x, ξ⟫ : ℝ) * Complex.I) * f x = 0) :
    f =ᵐ[volume] 0 := by
  have hint : ∀ (g : E → ℂ), Integrable g → ∀ ξ : E,
      Integrable fun x ↦ Complex.exp (-(⟪x, ξ⟫ : ℝ) * Complex.I) * g x := fun g hg ξ ↦ by
    simpa only [smul_eq_mul] using integrable_exp_inner_smul hg ξ
  have hconj : Integrable fun x ↦ conj (f x) := (Complex.conjCLE : ℂ →L[ℝ] ℂ).integrable_comp hf
  -- the Fourier transform of `conj f` vanishes too
  have hc : ∀ ξ : E, ∫ x, Complex.exp (-(⟪x, ξ⟫ : ℝ) * Complex.I) * conj (f x) = 0 := by
    intro ξ
    have := congrArg conj (h (-ξ))
    rw [map_zero, ← integral_conj] at this
    rw [← this]
    refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
    simp only [map_mul, ← Complex.exp_conj, inner_neg_right]
    congr 2
    simp [Complex.conj_ofReal]
  have hre : (fun x ↦ (f x).re) =ᵐ[volume] 0 := by
    refine ae_eq_zero_of_integral_exp_inner_mul_ofReal_eq_zero hf.re fun ξ ↦ ?_
    have hsplit : ∀ x, Complex.exp (-(⟪x, ξ⟫ : ℝ) * Complex.I) * ((f x).re : ℂ) =
        (2 : ℂ)⁻¹ * (Complex.exp (-(⟪x, ξ⟫ : ℝ) * Complex.I) * f x +
          Complex.exp (-(⟪x, ξ⟫ : ℝ) * Complex.I) * conj (f x)) := by
      intro x
      rw [ofReal_re_eq]
      ring
    simp_rw [hsplit]
    rw [integral_const_mul, integral_add (hint f hf ξ) (hint _ hconj ξ), h ξ, hc ξ]
    simp
  have him : (fun x ↦ (f x).im) =ᵐ[volume] 0 := by
    refine ae_eq_zero_of_integral_exp_inner_mul_ofReal_eq_zero hf.im fun ξ ↦ ?_
    have hsplit : ∀ x, Complex.exp (-(⟪x, ξ⟫ : ℝ) * Complex.I) * ((f x).im : ℂ) =
        (-Complex.I / 2) * (Complex.exp (-(⟪x, ξ⟫ : ℝ) * Complex.I) * f x -
          Complex.exp (-(⟪x, ξ⟫ : ℝ) * Complex.I) * conj (f x)) := by
      intro x
      rw [ofReal_im_eq]
      ring
    simp_rw [hsplit]
    rw [integral_const_mul, integral_sub (hint f hf ξ) (hint _ hconj ξ), h ξ, hc ξ]
    simp
  filter_upwards [hre, him] with x hx hy
  exact Complex.ext (by simpa using hx) (by simpa using hy)

end
