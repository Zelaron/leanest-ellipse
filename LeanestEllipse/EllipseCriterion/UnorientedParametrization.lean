import LeanestEllipse.EllipseCriterion.UnorientedTransfer
import LeanestEllipse.EllipseCriterion.HardyModel

/-!
# Parametrizing the Möbius bundle of unoriented lines

The coordinates `Γ(θ,p) = (exp(2iθ), p exp(iθ))` identify the half-period `[0,π) × ℝ`
with `Σ = {(q,z) | ‖q‖ = 1, z = q conj z}` as measurable spaces. The existing
Lusin–Souslin embedding supplies the measurable inverse; the results here identify its
image with the algebraic set `Σ`.
-/

open MeasureTheory Set Complex
open scoped Real ComplexConjugate

noncomputable section

namespace LeanestEllipse

/-- Every unoriented-line coordinate pair satisfies the defining Möbius relation. -/
theorem unorientedLineCoords_mem_mobiusBundle (w : ℝ × ℝ) :
    unorientedLineCoords w ∈ mobiusBundle := by
  constructor
  · change ‖exp (2 * (w.1 : ℂ) * I)‖ = 1
    rw [show (2 : ℂ) * (w.1 : ℂ) * I = ((2 * w.1 : ℝ) : ℂ) * I by push_cast; ring]
    exact norm_exp_ofReal_mul_I _
  · change (w.2 : ℂ) * exp ((w.1 : ℂ) * I) =
      exp (2 * (w.1 : ℂ) * I) * conj ((w.2 : ℂ) * exp ((w.1 : ℂ) * I))
    simp only [map_mul, conj_ofReal, ← exp_conj, conj_I]
    rw [mul_left_comm, ← exp_add]
    congr 2
    ring

/-- Every point of the Möbius bundle has coordinates with angle in `(-π/2,π/2]`. -/
theorem exists_unorientedLineCoords_eq_of_mem_mobiusBundle
    {q z : ℂ} (hw : (q, z) ∈ mobiusBundle) :
    ∃ θ p : ℝ, unorientedLineCoords (θ, p) = (q, z) ∧ -π / 2 < θ ∧ θ ≤ π / 2 := by
  obtain ⟨hqnorm, hz⟩ := hw
  let θ : ℝ := arg q / 2
  have hqθ : exp (2 * (θ : ℂ) * I) = q := by
    rw [show (2 : ℂ) * (θ : ℂ) * I = arg q * I by dsimp [θ]; push_cast; ring]
    simpa only [hqnorm, ofReal_one, one_mul] using norm_mul_exp_arg_mul_I q
  let t : ℂ := exp (-(θ : ℂ) * I) * z
  have htconj : conj t = t := by
    calc
      conj t = exp ((θ : ℂ) * I) * conj z := by
        simp only [t, map_mul, ← exp_conj, map_neg, conj_ofReal, conj_I, neg_mul_neg]
      _ = exp (-(θ : ℂ) * I) * (q * conj z) := by
        rw [← hqθ, ← mul_assoc, ← exp_add]
        congr 1
        congr 1
        ring
      _ = t := by rw [← hz]
  have htim : t.im = 0 := by
    have hh := congrArg Complex.im htconj
    simp only [conj_im] at hh
    linarith
  have htre : (t.re : ℂ) = t := by
    apply Complex.ext
    · simp
    · simpa using htim.symm
  refine ⟨θ, t.re, ?_, ?_, ?_⟩
  · apply Prod.ext hqθ
    change (t.re : ℂ) * exp ((θ : ℂ) * I) = z
    rw [htre]
    dsimp [t]
    rw [mul_right_comm, ← exp_add]
    simp
  · dsimp [θ]
    linarith [neg_pi_lt_arg q]
  · dsimp [θ]
    linarith [arg_le_pi q]

/-- The half-period coordinates cover exactly the Möbius bundle. -/
theorem range_unorientedLineCoordsHalf : range unorientedLineCoordsHalf = mobiusBundle := by
  apply subset_antisymm
  · rintro _ ⟨w, rfl⟩
    exact unorientedLineCoords_mem_mobiusBundle w
  · rintro ⟨q, z⟩ hw
    obtain ⟨θ, p, hθp, hθlo, hθhi⟩ :=
      exists_unorientedLineCoords_eq_of_mem_mobiusBundle hw
    by_cases hθ : 0 ≤ θ
    · refine ⟨⟨(θ, p), ⟨⟨hθ, ?_⟩, mem_univ _⟩⟩, hθp⟩
      linarith [Real.pi_pos]
    · refine ⟨⟨(θ + π, -p), ⟨⟨?_, ?_⟩, mem_univ _⟩⟩, ?_⟩
      · linarith [Real.pi_pos]
      · linarith
      · exact (unorientedLineCoords_add_pi_neg θ p).trans hθp

/-- The Möbius bundle is measurably equivalent to the half-period of line coordinates. -/
def unorientedLineCoordsMeasurableEquiv : halfPeriod ≃ᵐ mobiusBundle :=
  measurableEmbedding_unorientedLineCoordsHalf.equivRange.trans
    { toEquiv := Set.equivOfEq range_unorientedLineCoordsHalf
      measurable_toFun := measurable_subtype_coe.subtype_mk
      measurable_invFun := measurable_subtype_coe.subtype_mk }

@[simp] theorem coe_unorientedLineCoordsMeasurableEquiv (w : halfPeriod) :
    (unorientedLineCoordsMeasurableEquiv w : ℂ × ℂ) = unorientedLineCoordsHalf w := by
  change ((measurableEmbedding_unorientedLineCoordsHalf.equivRange w) : ℂ × ℂ) = _
  rw [MeasurableEmbedding.equivRange_apply]

end LeanestEllipse
