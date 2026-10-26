import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.RingTheory.Idempotents

/-!
# Riesz idempotents and the half-plane idempotent

Let `A` be a complex Banach algebra and `a : A`.  For a circle `C(c, R)` contained in the resolvent
set of `a`, the *Riesz integral*
`rieszCircleIntegral a c R = (2 π i)⁻¹ ∮_{C(c, R)} (z - a)⁻¹ dz`
is an idempotent commuting with everything that commutes with `a` (the Riesz projection of the part
of the spectrum inside the circle).  We develop this for circles only, which is all that is needed
to split a spectrum avoiding the real axis into its upper and lower parts; Mathlib's continuous
functional calculus is not available here since `a` need not be normal.

## Main definitions and results

* `spectrum.resolvent_sub_resolvent_eq_smul_mul`: the first resolvent identity.
* `rieszCircleIntegral a c R`: the normalized circle integral of the resolvent.
* `isIdempotentElem_rieszCircleIntegral`, `commute_rieszCircleIntegral`: a Riesz integral over a
  circle in the resolvent set is an idempotent in the bicommutant of `a`.
* `rieszCircleIntegral_add_rieszCircleIntegral_eq_one`: two orthogonal Riesz idempotents whose open
  disks cover the spectrum add up to `1`.  The proof uses that the corner `e A e` of a Banach
  algebra at an idempotent `e ≠ 0` is again a (nontrivial) Banach algebra, so it has nonempty
  spectrum.
* `exists_isIdempotentElem_upperHalfPlane`: if the spectrum of `a` avoids the real axis, there is
  an idempotent `P` (the Riesz projection of the upper half-plane) in the bicommutant of `a` with
  `P ≠ 0` iff the spectrum meets the upper half-plane, `P ≠ 1` iff it meets the lower half-plane,
  and `star P * u = u * (1 - P)` for every unit `u` with `star a * u = u * a`.

The last statement is the analytic input of [Hägg, Lemma 8].

## References

* C. Hägg, *An ellipse criterion for exact nonuniqueness in the planar interior Radon problem*.
-/

noncomputable section

open Set Metric MeasureTheory

/-! ### Circle integrals -/

section CircleIntegral

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- A continuous complex-linear map commutes with a circle integral. -/
theorem ContinuousLinearMap.circleIntegral_comp_comm [CompleteSpace E] [CompleteSpace F]
    (L : E →L[ℂ] F) {f : ℂ → E} {c : ℂ} {R : ℝ} (hf : CircleIntegrable f c R) :
    ∮ z in C(c, R), L (f z) = L (∮ z in C(c, R), f z) := by
  simp only [circleIntegral, ← L.map_smul]
  exact L.intervalIntegral_comp_comm hf.out

/-- Fubini's theorem for two circle integrals.  The continuity hypothesis is on the square of
angle parameters, so `f` may have singularities away from the product of the two circles. -/
theorem circleIntegral.integral_integral_swap [CompleteSpace E]
    {f : ℂ → ℂ → E} {c₁ c₂ : ℂ} {R₁ R₂ : ℝ}
    (hf : ContinuousOn (fun p : ℝ × ℝ ↦ f (circleMap c₁ R₁ p.1) (circleMap c₂ R₂ p.2))
      (Icc 0 (2 * Real.pi) ×ˢ Icc 0 (2 * Real.pi))) :
    ∮ z in C(c₁, R₁), ∮ w in C(c₂, R₂), f z w = ∮ w in C(c₂, R₂), ∮ z in C(c₁, R₁), f z w := by
  let Q : Set (ℝ × ℝ) := Icc 0 (2 * Real.pi) ×ˢ Icc 0 (2 * Real.pi)
  let Q' : Set (ℝ × ℝ) := Ioc 0 (2 * Real.pi) ×ˢ Ioc 0 (2 * Real.pi)
  let G : ℝ × ℝ → E := fun p ↦
    deriv (circleMap c₁ R₁) p.1 • deriv (circleMap c₂ R₂) p.2 •
      f (circleMap c₁ R₁ p.1) (circleMap c₂ R₂ p.2)
  have hd₁ : Continuous (fun p : ℝ × ℝ ↦ deriv (circleMap c₁ R₁) p.1) := by
    simp_rw [deriv_circleMap]
    fun_prop
  have hd₂ : Continuous (fun p : ℝ × ℝ ↦ deriv (circleMap c₂ R₂) p.2) := by
    simp_rw [deriv_circleMap]
    fun_prop
  have hG : ContinuousOn G Q := hd₁.continuousOn.smul (hd₂.continuousOn.smul hf)
  have hQ : IsCompact Q := isCompact_Icc.prod isCompact_Icc
  have hQ'Q : Q' ⊆ Q := prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self
  have hGint : Integrable G
      ((volume.restrict (Ioc 0 (2 * Real.pi))).prod (volume.restrict (Ioc 0 (2 * Real.pi)))) := by
    rw [Measure.prod_restrict]
    exact (hG.integrableOn_compact (μ := volume.prod volume) hQ).mono_set hQ'Q
  simp only [circleIntegral]
  simp_rw [← intervalIntegral.integral_smul, intervalIntegral.integral_of_le Real.two_pi_pos.le]
  have hswap := MeasureTheory.integral_integral_swap (f := fun x y ↦ G (x, y)) hGint
  simp only [G] at hswap
  simpa only [smul_smul, mul_comm] using hswap

/-- The Cauchy kernel has zero circle integral when its pole lies outside the closed disk. -/
theorem circleIntegral.integral_sub_inv_of_notMem_closedBall {c w : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hw : w ∉ closedBall c R) : ∮ z in C(c, R), (z - w)⁻¹ = 0 := by
  apply Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable hR countable_empty
  · exact (continuousOn_id.sub continuousOn_const).inv₀ fun z hz ↦
      sub_ne_zero.mpr (ne_of_mem_of_not_mem hz hw)
  · intro z hz
    exact (differentiableAt_id.sub_const w).inv
      (sub_ne_zero.mpr (ne_of_mem_of_not_mem (ball_subset_closedBall hz.1) hw))

/-- The reversed Cauchy kernel `(w - z)⁻¹` integrates to `-2πi` when `w` is inside the circle. -/
theorem circleIntegral.integral_inv_sub_of_mem_ball {c w : ℂ} {R : ℝ} (hw : w ∈ ball c R) :
    ∮ z in C(c, R), (w - z)⁻¹ = -(2 * Real.pi * Complex.I) := by
  have h : (fun z : ℂ ↦ (w - z)⁻¹) = fun z ↦ (-1 : ℂ) • (z - w)⁻¹ := by
    funext z
    rw [show w - z = -(z - w) by abel, inv_neg, neg_one_smul]
  rw [h, circleIntegral.integral_smul, circleIntegral.integral_sub_inv_of_mem_ball hw,
    neg_one_smul]

/-- The reversed Cauchy kernel `(w - z)⁻¹` integrates to zero when `w` is outside the closed
disk. -/
theorem circleIntegral.integral_inv_sub_of_notMem_closedBall {c w : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hw : w ∉ closedBall c R) : ∮ z in C(c, R), (w - z)⁻¹ = 0 := by
  have h : (fun z : ℂ ↦ (w - z)⁻¹) = fun z ↦ (-1 : ℂ) • (z - w)⁻¹ := by
    funext z
    rw [show w - z = -(z - w) by abel, inv_neg, neg_one_smul]
  rw [h, circleIntegral.integral_smul,
    circleIntegral.integral_sub_inv_of_notMem_closedBall hR hw, smul_zero]

private theorem star_circleMap_two_pi_sub (c : ℂ) (R θ : ℝ) :
    star (circleMap (star c) R (2 * Real.pi - θ)) = circleMap c R θ := by
  rw [show star (circleMap (star c) R (2 * Real.pi - θ)) =
    circleMap (star (star c)) R (-(2 * Real.pi - θ)) from
      conj_circleMap (star c) R (2 * Real.pi - θ)]
  rw [star_star, neg_sub]
  exact (periodic_circleMap c R).sub_eq θ

private theorem star_deriv_circleMap (c : ℂ) (R θ : ℝ) :
    star (deriv (circleMap c R) θ) = -deriv (circleMap (star c) R) (2 * Real.pi - θ) := by
  rw [deriv_circleMap, deriv_circleMap, star_mul]
  rw [show star (circleMap 0 R θ) = circleMap 0 R (-θ) from conj_circleMap_zero R θ]
  rw [show star Complex.I = -Complex.I from Complex.conj_I]
  rw [show circleMap 0 R (2 * Real.pi - θ) = circleMap 0 R (-θ) from
    (periodic_circleMap 0 R).sub_eq']
  ring

/-- Complex conjugation reverses the orientation of a circle integral: the conjugated integrand
is evaluated at the conjugate point and integrated over the conjugate circle. -/
theorem circleIntegral.star_integral [CompleteSpace E] [StarAddMonoid E] [StarModule ℂ E]
    [ContinuousStar E] {f : ℂ → E} {c : ℂ} {R : ℝ} (hf : CircleIntegrable f c R) :
    star (∮ z in C(c, R), f z) = -∮ z in C(star c, R), star (f (star z)) := by
  have hstar :=
    (starL' ℝ : E ≃L[ℝ] E).toContinuousLinearMap.intervalIntegral_comp_comm hf.out
  simp only [circleIntegral] at hstar ⊢
  have hstar' : star (∫ θ in 0..2 * Real.pi, deriv (circleMap c R) θ • f (circleMap c R θ)) =
      ∫ θ in 0..2 * Real.pi, star (deriv (circleMap c R) θ • f (circleMap c R θ)) := by
    simpa [starL'] using hstar.symm
  rw [hstar']
  let g : ℝ → E := fun θ ↦
    deriv (circleMap (star c) R) θ • star (f (star (circleMap (star c) R θ)))
  have hpoint : ∀ θ : ℝ, star (deriv (circleMap c R) θ • f (circleMap c R θ)) =
      -g (2 * Real.pi - θ) := by
    intro θ
    simp only [g, star_smul, star_deriv_circleMap, star_circleMap_two_pi_sub, neg_smul]
  calc (∫ θ in 0..2 * Real.pi, star (deriv (circleMap c R) θ • f (circleMap c R θ)))
      = ∫ θ in 0..2 * Real.pi, -g (2 * Real.pi - θ) :=
        intervalIntegral.integral_congr fun θ _ ↦ hpoint θ
    _ = -(∫ θ in 0..2 * Real.pi, g (2 * Real.pi - θ)) := by rw [intervalIntegral.integral_neg]
    _ = -(∫ θ in 0..2 * Real.pi, g θ) := by
      rw [intervalIntegral.integral_comp_sub_left]
      congr 2 <;> simp

end CircleIntegral

/-! ### Algebraic identities for the resolvent -/

namespace spectrum

section Algebra

variable {𝕜 A : Type*} [Field 𝕜] [Ring A] [Algebra 𝕜 A]

local notation "↑ₐ" => algebraMap 𝕜 A

/-- On the resolvent set, the resolvent is a left inverse of the shifted element. -/
theorem resolvent_mul_algebraMap_sub {a : A} {z : 𝕜} (hz : z ∈ resolventSet 𝕜 a) :
    resolvent a z * (↑ₐ z - a) = 1 :=
  Ring.inverse_mul_cancel _ hz

/-- On the resolvent set, the resolvent is a right inverse of the shifted element. -/
theorem algebraMap_sub_mul_resolvent {a : A} {z : 𝕜} (hz : z ∈ resolventSet 𝕜 a) :
    (↑ₐ z - a) * resolvent a z = 1 :=
  Ring.mul_inverse_cancel _ hz

/-- The resolvent of `a` commutes with every element commuting with `a` (at every scalar, since
outside the resolvent set the resolvent is `0`). -/
theorem commute_resolvent_of_commute {a b : A} (h : Commute a b) (z : 𝕜) :
    Commute (resolvent a z) b := by
  have h' : Commute (↑ₐ z - a) b := (Algebra.commute_algebraMap_left z b).sub_left h
  by_cases hz : IsUnit (↑ₐ z - a)
  · rw [resolvent, ← hz.unit_spec, Ring.inverse_unit]
    exact Commute.units_inv_left (by rwa [hz.unit_spec])
  · rw [resolvent, Ring.inverse_non_unit _ hz]
    exact Commute.zero_left b

/-- The resolvent of `a` commutes with `a`. -/
theorem commute_resolvent (a : A) (z : 𝕜) : Commute (resolvent a z) a :=
  commute_resolvent_of_commute (Commute.refl a) z

/-- Resolvents at any two scalars commute. -/
theorem commute_resolvent_resolvent (a : A) (z w : 𝕜) :
    Commute (resolvent a z) (resolvent a w) := by
  have hzw : Commute (↑ₐ z) (↑ₐ w) := Algebra.commute_algebraMap_left z _
  have hshift : Commute (↑ₐ z - a) (↑ₐ w - a) :=
    (hzw.sub_right (Algebra.commute_algebraMap_left z a)).sub_left
      ((Algebra.commute_algebraMap_left w a).symm.sub_right (Commute.refl a))
  exact hshift.ringInverse_ringInverse

/-- The **first resolvent identity** (for two scalars and a fixed element), in a form valid in a
noncommutative algebra: `R(z) - R(w) = (w - z) R(z) R(w)` where `R = resolvent a`. -/
theorem resolvent_sub_resolvent_eq_smul_mul {a : A} {z w : 𝕜} (hz : z ∈ resolventSet 𝕜 a)
    (hw : w ∈ resolventSet 𝕜 a) :
    resolvent a z - resolvent a w = (w - z) • (resolvent a z * resolvent a w) := by
  calc resolvent a z - resolvent a w
      = resolvent a z * ((↑ₐ w - a) * resolvent a w) -
          (resolvent a z * (↑ₐ z - a)) * resolvent a w := by
        rw [algebraMap_sub_mul_resolvent hw, resolvent_mul_algebraMap_sub hz, mul_one, one_mul]
    _ = resolvent a z * ↑ₐ (w - z) * resolvent a w := by rw [map_sub]; noncomm_ring
    _ = (w - z) • (resolvent a z * resolvent a w) := by
        rw [← Algebra.commutes, Algebra.smul_def, mul_assoc]

/-- The divided form of the first resolvent identity. -/
theorem resolvent_mul_resolvent {a : A} {z w : 𝕜} (hz : z ∈ resolventSet 𝕜 a)
    (hw : w ∈ resolventSet 𝕜 a) (hzw : z ≠ w) :
    resolvent a z * resolvent a w = (w - z)⁻¹ • (resolvent a z - resolvent a w) := by
  rw [resolvent_sub_resolvent_eq_smul_mul hz hw, smul_smul,
    inv_mul_cancel₀ (sub_ne_zero.mpr hzw.symm), one_smul]

/-- Multiplying the resolvent at `z` by another shift `w - a`. -/
theorem algebraMap_sub_mul_resolvent_eq {a : A} {z : 𝕜} (hz : z ∈ resolventSet 𝕜 a) (w : 𝕜) :
    (↑ₐ w - a) * resolvent a z = (w - z) • resolvent a z + 1 := by
  calc (↑ₐ w - a) * resolvent a z = (↑ₐ (w - z) + (↑ₐ z - a)) * resolvent a z := by
        rw [map_sub]; abel_nf
    _ = (w - z) • resolvent a z + 1 := by
        rw [add_mul, algebraMap_sub_mul_resolvent hz, Algebra.smul_def]

/-- Multiplying the resolvent at `z` by another shift `w - a`, on the right. -/
theorem resolvent_mul_algebraMap_sub_eq {a : A} {z : 𝕜} (hz : z ∈ resolventSet 𝕜 a) (w : 𝕜) :
    resolvent a z * (↑ₐ w - a) = (w - z) • resolvent a z + 1 := by
  calc resolvent a z * (↑ₐ w - a) = resolvent a z * (↑ₐ (w - z) + (↑ₐ z - a)) := by
        rw [map_sub]; abel_nf
    _ = (w - z) • resolvent a z + 1 := by
        rw [mul_add, resolvent_mul_algebraMap_sub hz, ← Algebra.commutes, Algebra.smul_def]

/-- The resolvent is covariant under conjugation by a unit. -/
theorem resolvent_units_conj (a : A) (u : Aˣ) (z : 𝕜) :
    resolvent ((u : A) * a * ↑u⁻¹) z = u * resolvent a z * ↑u⁻¹ := by
  have hshift : ↑ₐ z - (u : A) * a * ↑u⁻¹ = u * (↑ₐ z - a) * ↑u⁻¹ := by
    rw [mul_sub, sub_mul, ← Algebra.commutes, mul_assoc (↑ₐ z), Units.mul_inv, mul_one]
  simp only [resolvent, hshift]
  rw [Ring.inverse_mul (Or.inr u⁻¹.isUnit), Ring.inverse_mul (Or.inl u.isUnit)]
  simp [mul_assoc]

section Star

variable [StarRing 𝕜] [StarRing A] [StarModule 𝕜 A]

/-- Taking `star` conjugates the scalar argument of the resolvent. -/
theorem star_resolvent (a : A) (z : 𝕜) : star (resolvent a z) = resolvent (star a) (star z) := by
  simp only [resolvent, ← Ring.inverse_star, star_sub, ← algebraMap_star_comm]

/-- If a unit `u` intertwines `a` and `star a`, i.e. `star a * u = u * a`, then the spectrum of `a`
is invariant under `star`. -/
theorem star_eq_self_of_star_mul_eq_mul {a : A} (u : Aˣ) (h : star a * u = u * a) :
    star (spectrum 𝕜 a) = spectrum 𝕜 a := by
  have ha : star a = u * a * ↑u⁻¹ := by
    rw [← h, mul_assoc, Units.mul_inv, mul_one]
  rw [← spectrum.map_star, ha, spectrum.units_conjugate]

end Star

end Algebra

end spectrum

/-- A nonempty `star`-invariant subset of `ℂ` avoiding the real axis meets both open half-planes. -/
theorem Set.exists_im_pos_and_exists_im_neg_of_star_eq {s : Set ℂ} (hne : s.Nonempty)
    (hreal : ∀ z ∈ s, z.im ≠ 0) (hstar : star s = s) :
    (∃ z ∈ s, 0 < z.im) ∧ ∃ z ∈ s, z.im < 0 := by
  obtain ⟨z, hz⟩ := hne
  have hzstar : star z ∈ s := by
    rw [← hstar]
    exact Set.star_mem_star.mpr hz
  rcases lt_or_gt_of_ne (hreal z hz) with hzneg | hzpos
  · exact ⟨⟨star z, hzstar, by simpa using hzneg⟩, ⟨z, hz, hzneg⟩⟩
  · exact ⟨⟨z, hz, hzpos⟩, ⟨star z, hzstar, by simpa using hzpos⟩⟩

/-! ### Corners of Banach algebras -/

/-- The corner `e * A * e` of an algebra, as a non-unital subalgebra. -/
def NonUnitalSubalgebra.corner (R : Type*) {A : Type*} [CommSemiring R] [NonUnitalSemiring A]
    [Module R A] [IsScalarTower R A A] [SMulCommClass R A A] (e : A) :
    NonUnitalSubalgebra R A where
  __ := NonUnitalSubsemiring.corner e
  smul_mem' := by
    rintro r _ ⟨a, rfl⟩
    exact ⟨r • a, by simp only [mul_smul_comm, smul_mul_assoc]⟩

/-- An element lies in the corner at an idempotent `e` iff it is fixed by left and right
multiplication by `e`. -/
theorem NonUnitalSubalgebra.mem_corner_iff {R A : Type*} [CommSemiring R] [NonUnitalSemiring A]
    [Module R A] [IsScalarTower R A A] [SMulCommClass R A A] {e x : A} (he : IsIdempotentElem e) :
    x ∈ NonUnitalSubalgebra.corner R e ↔ e * x = x ∧ x * e = x :=
  Subsemigroup.mem_corner_iff he

section Corner

variable {𝕜 A : Type*} [NormedField 𝕜] [NormedRing A] [NormedAlgebra 𝕜 A]

/-- The corner `e A e` of a normed algebra at an idempotent `e`, which is a normed algebra with
unit `e`. -/
abbrev IsIdempotentElem.BanachCorner (𝕜 : Type*) [NormedField 𝕜] [NormedAlgebra 𝕜 A] {e : A}
    (_he : IsIdempotentElem e) : Type _ :=
  NonUnitalSubalgebra.corner 𝕜 e

namespace IsIdempotentElem.BanachCorner

variable {e : A} (he : IsIdempotentElem e)

instance instSemiring : Semiring (BanachCorner 𝕜 he) where
  __ : NonUnitalSemiring (BanachCorner 𝕜 he) :=
    inferInstanceAs (NonUnitalSemiring (NonUnitalSubalgebra.corner 𝕜 e))
  one := ⟨e, e, by simp only [he.eq]⟩
  one_mul x := Subtype.ext ((Subsemigroup.mem_corner_iff he).mp x.2).1
  mul_one x := Subtype.ext ((Subsemigroup.mem_corner_iff he).mp x.2).2

instance instRing : Ring (BanachCorner 𝕜 he) where
  __ : Semiring (BanachCorner 𝕜 he) := inferInstance
  __ : NonUnitalRing (BanachCorner 𝕜 he) :=
    inferInstanceAs (NonUnitalRing (NonUnitalSubalgebra.corner 𝕜 e))

instance instNormedRing : NormedRing (BanachCorner 𝕜 he) :=
  NormedRing.induced (BanachCorner 𝕜 he) A
    (NonUnitalSubalgebraClass.subtype (NonUnitalSubalgebra.corner 𝕜 e)) Subtype.val_injective

instance instAlgebra : Algebra 𝕜 (BanachCorner 𝕜 he) :=
  Algebra.ofModule smul_mul_assoc mul_smul_comm

instance instNormedAlgebra : NormedAlgebra 𝕜 (BanachCorner 𝕜 he) where
  norm_smul_le r x := by
    change ‖r • (x : A)‖ ≤ ‖r‖ * ‖(x : A)‖
    exact norm_smul_le r (x : A)

omit he in
/-- The corner of a normed algebra at an idempotent is closed. -/
theorem _root_.NonUnitalSubalgebra.isClosed_corner {e : A} (he : IsIdempotentElem e) :
    IsClosed (NonUnitalSubalgebra.corner 𝕜 e : Set A) := by
  rw [show (NonUnitalSubalgebra.corner 𝕜 e : Set A) = {x : A | e * x = x} ∩ {x : A | x * e = x} by
    ext x
    exact NonUnitalSubalgebra.mem_corner_iff he]
  exact (isClosed_eq (continuous_const.mul continuous_id) continuous_id).inter
    (isClosed_eq (continuous_id.mul continuous_const) continuous_id)

/-- The unit of the corner at `e` is `e`. -/
@[simp]
theorem coe_one : ((1 : BanachCorner 𝕜 he) : A) = e := rfl

/-- The scalars of the corner at `e` are the multiples of `e`. -/
theorem coe_algebraMap (z : 𝕜) : ((algebraMap 𝕜 (BanachCorner 𝕜 he) z : BanachCorner 𝕜 he) : A) =
    z • e := by
  rw [Algebra.algebraMap_eq_smul_one]
  rfl

end IsIdempotentElem.BanachCorner

/-- **Liouville's theorem in a corner.**  Let `e` be an idempotent of a complex Banach algebra and
`a` any element.  If for every `z : ℂ` the compressed shift `z • e - e * a * e` has a two-sided
inverse relative to `e`, then `e = 0`.  (Otherwise the corner `e A e` would be a nontrivial complex
Banach algebra in which `e * a * e` has empty spectrum.) -/
theorem IsIdempotentElem.eq_zero_of_forall_exists_inverse {A : Type*} [NormedRing A]
    [NormedAlgebra ℂ A] [CompleteSpace A] {e : A} (he : IsIdempotentElem e) (a : A)
    (h : ∀ z : ℂ, ∃ b : A, (z • e - e * a * e) * b = e ∧ b * (z • e - e * a * e) = e) :
    e = 0 := by
  by_contra hne
  have : Nontrivial (IsIdempotentElem.BanachCorner ℂ he) :=
    ⟨⟨1, 0, fun h ↦ hne (by simpa using congrArg Subtype.val h)⟩⟩
  let x : IsIdempotentElem.BanachCorner ℂ he := ⟨e * a * e, ⟨a, rfl⟩⟩
  obtain ⟨z, hz⟩ := @spectrum.nonempty (IsIdempotentElem.BanachCorner ℂ he) _ _
    (NonUnitalSubalgebra.isClosed_corner he).completeSpace_coe _ x
  obtain ⟨b, hb₁, hb₂⟩ := h z
  set s : A := z • e - e * a * e with hs
  have hse : s * e = s := by
    simp only [hs, sub_mul, smul_mul_assoc, he.eq, mul_assoc]
  have hes : e * s = s := by
    simp only [hs, mul_sub, mul_smul_comm, he.eq, ← mul_assoc]
  let y : IsIdempotentElem.BanachCorner ℂ he := ⟨e * b * e, ⟨b, rfl⟩⟩
  have hcoe : ((algebraMap ℂ (IsIdempotentElem.BanachCorner ℂ he) z - x :
      IsIdempotentElem.BanachCorner ℂ he) : A) = s := by
    rw [AddSubgroupClass.coe_sub, IsIdempotentElem.BanachCorner.coe_algebraMap]
  apply hz
  refine isUnit_iff_exists.mpr ⟨y, Subtype.ext ?_, Subtype.ext ?_⟩
  · change ((algebraMap ℂ _ z - x : IsIdempotentElem.BanachCorner ℂ he) : A) * (e * b * e) = e
    rw [hcoe, ← mul_assoc, ← mul_assoc, hse, hb₁, he.eq]
  · change (e * b * e) * ((algebraMap ℂ _ z - x : IsIdempotentElem.BanachCorner ℂ he) : A) = e
    rw [hcoe, mul_assoc, hes, mul_assoc, hb₂, he.eq]

end Corner


/-! ### Riesz integrals over circles -/

section Riesz

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

/-- The resolvent is continuous on the resolvent set. -/
theorem spectrum.continuousOn_resolvent (a : A) :
    ContinuousOn (resolvent a) (resolventSet ℂ a) := fun _ hz ↦
  (spectrum.hasDerivAt_resolvent_const_left hz).continuousAt.continuousWithinAt

/-- The resolvent is integrable over a circle contained in the resolvent set. -/
theorem circleIntegrable_resolvent {a : A} {c : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hc : sphere c R ⊆ resolventSet ℂ a) : CircleIntegrable (resolvent a) c R :=
  ((spectrum.continuousOn_resolvent a).mono hc).circleIntegrable hR

private theorem circleIntegral_mul_left {f : ℂ → A} {c : ℂ} {R : ℝ} (hf : CircleIntegrable f c R)
    (x : A) : ∮ z in C(c, R), x * f z = x * ∮ z in C(c, R), f z := by
  simpa using (ContinuousLinearMap.mulLeftRight ℂ A x 1).circleIntegral_comp_comm hf

private theorem circleIntegral_mul_right {f : ℂ → A} {c : ℂ} {R : ℝ}
    (hf : CircleIntegrable f c R) (y : A) :
    ∮ z in C(c, R), f z * y = (∮ z in C(c, R), f z) * y := by
  simpa using (ContinuousLinearMap.mulLeftRight ℂ A 1 y).circleIntegral_comp_comm hf

/-- The spectrum has a positive distance from a circle contained in the resolvent set. -/
theorem exists_pos_forall_le_abs_norm_sub_sub_of_sphere_subset {a : A} {c : ℂ} {R : ℝ}
    (hc : sphere c R ⊆ resolventSet ℂ a) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z ∈ spectrum ℂ a, δ ≤ |‖z - c‖ - R| := by
  rcases (spectrum ℂ a).eq_empty_or_nonempty with h | h
  · exact ⟨1, one_pos, by simp [h]⟩
  obtain ⟨z, hz, hmin⟩ := (spectrum.isCompact a).exists_isMinOn h
    (by fun_prop : ContinuousOn (fun z : ℂ ↦ |‖z - c‖ - R|) (spectrum ℂ a))
  have hne : ‖z - c‖ - R ≠ 0 := fun h0 ↦
    hz (hc (mem_sphere_iff_norm.mpr (sub_eq_zero.mp h0)))
  exact ⟨|‖z - c‖ - R|, abs_pos.mpr hne, fun _ hw ↦ hmin hw⟩

/-- A circle in the resolvent set has a slightly larger concentric closed annulus in the resolvent
set. -/
theorem exists_closedBall_diff_ball_subset_resolventSet_of_lt {a : A} {c : ℂ} {R : ℝ}
    (hc : sphere c R ⊆ resolventSet ℂ a) :
    ∃ S : ℝ, R < S ∧ closedBall c S \ ball c R ⊆ resolventSet ℂ a := by
  obtain ⟨δ, hδ, hgap⟩ := exists_pos_forall_le_abs_norm_sub_sub_of_sphere_subset hc
  refine ⟨R + δ / 2, by linarith, fun z hz ↦ ?_⟩
  by_contra hzs
  have hlower : R ≤ ‖z - c‖ := not_lt.mp fun h ↦ hz.2 (mem_ball_iff_norm.mpr h)
  have hupper : ‖z - c‖ ≤ R + δ / 2 := mem_closedBall_iff_norm.mp hz.1
  have habs : |‖z - c‖ - R| ≤ δ / 2 := by
    rw [abs_of_nonneg (sub_nonneg.mpr hlower)]
    linarith
  linarith [hgap z hzs]

/-- A circle of positive radius in the resolvent set has a slightly smaller concentric closed
annulus in the resolvent set. -/
theorem exists_closedBall_diff_ball_subset_resolventSet_of_gt {a : A} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hc : sphere c R ⊆ resolventSet ℂ a) :
    ∃ r : ℝ, 0 < r ∧ r < R ∧ closedBall c R \ ball c r ⊆ resolventSet ℂ a := by
  obtain ⟨δ, hδ, hgap⟩ := exists_pos_forall_le_abs_norm_sub_sub_of_sphere_subset hc
  have hε : 0 < min (δ / 2) (R / 2) := lt_min (by linarith) (by linarith)
  have hεR : min (δ / 2) (R / 2) < R := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hεδ : min (δ / 2) (R / 2) < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  refine ⟨R - min (δ / 2) (R / 2), sub_pos.mpr hεR, sub_lt_self R hε, fun z hz ↦ ?_⟩
  by_contra hzs
  have hlower : R - min (δ / 2) (R / 2) ≤ ‖z - c‖ :=
    not_lt.mp fun h ↦ hz.2 (mem_ball_iff_norm.mpr h)
  have hupper : ‖z - c‖ ≤ R := mem_closedBall_iff_norm.mp hz.1
  have habs : |‖z - c‖ - R| ≤ min (δ / 2) (R / 2) := by
    rw [abs_of_nonpos (sub_nonpos.mpr hupper)]
    linarith
  linarith [hgap z hzs]

/-- The outer boundary circle of a closed annulus lies in the annulus. -/
theorem sphere_subset_of_closedBall_diff_ball_subset {s : Set ℂ} {c : ℂ} {r R : ℝ} (hrR : r ≤ R)
    (h : closedBall c R \ ball c r ⊆ s) : sphere c R ⊆ s := fun z hz ↦
  h ⟨sphere_subset_closedBall hz, by
    rw [mem_ball_iff_norm, not_lt, mem_sphere_iff_norm.mp hz]; exact hrR⟩

/-- The inner boundary circle of a closed annulus lies in the annulus. -/
theorem sphere_subset_of_closedBall_diff_ball_subset' {s : Set ℂ} {c : ℂ} {r R : ℝ} (hrR : r ≤ R)
    (h : closedBall c R \ ball c r ⊆ s) : sphere c r ⊆ s := fun z hz ↦
  h ⟨by rw [mem_closedBall_iff_norm, mem_sphere_iff_norm.mp hz]; exact hrR, by
    rw [mem_ball_iff_norm, not_lt, mem_sphere_iff_norm.mp hz]⟩

/-- The **Riesz integral** `(2πi)⁻¹ ∮_{C(c, R)} (z - a)⁻¹ dz` of `a` over the circle `C(c, R)`.
When the circle lies in the resolvent set of `a`, this is the Riesz idempotent of the part of the
spectrum of `a` inside the circle. -/
def rieszCircleIntegral (a : A) (c : ℂ) (R : ℝ) : A :=
  (2 * Real.pi * Complex.I : ℂ)⁻¹ • ∮ z in C(c, R), resolvent a z

private theorem continuousOn_sub_inv_sphere {c w : ℂ} {R : ℝ} (hw : w ∉ sphere c R) :
    ContinuousOn (fun z : ℂ ↦ (z - w)⁻¹) (sphere c R) :=
  (continuousOn_id.sub continuousOn_const).inv₀ fun _ hz ↦
    sub_ne_zero.mpr (ne_of_mem_of_not_mem hz hw)

/-- Multiplying a Cauchy-weighted resolvent integral `K` by the corresponding shift.  Here `s` is
the winding number of the circle around `w`. This elementary inverse formula underlies the
nontriviality statements for Riesz idempotents. -/
theorem algebraMap_sub_mul_cauchy_resolvent {a : A} {c w : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hc : sphere c R ⊆ resolventSet ℂ a) (hw : w ∉ sphere c R) :
    (algebraMap ℂ A w - a) *
        ((2 * Real.pi * Complex.I : ℂ)⁻¹ • ∮ z in C(c, R), (z - w)⁻¹ • resolvent a z) =
      ((2 * Real.pi * Complex.I : ℂ)⁻¹ * ∮ z in C(c, R), (z - w)⁻¹) • 1 -
        rieszCircleIntegral a c R ∧
    ((2 * Real.pi * Complex.I : ℂ)⁻¹ • ∮ z in C(c, R), (z - w)⁻¹ • resolvent a z) *
        (algebraMap ℂ A w - a) =
      ((2 * Real.pi * Complex.I : ℂ)⁻¹ * ∮ z in C(c, R), (z - w)⁻¹) • 1 -
        rieszCircleIntegral a c R := by
  have hres : ContinuousOn (resolvent a) (sphere c R) :=
    (spectrum.continuousOn_resolvent a).mono hc
  have hk := continuousOn_sub_inv_sphere hw
  have hweighted : CircleIntegrable (fun z ↦ (z - w)⁻¹ • resolvent a z) c R :=
    (hk.smul hres).circleIntegrable hR
  have hone : CircleIntegrable (fun z ↦ (z - w)⁻¹ • (1 : A)) c R :=
    (hk.smul continuousOn_const).circleIntegrable hR
  have hneg : CircleIntegrable (fun z ↦ -resolvent a z) c R := (hres.circleIntegrable hR).neg
  have hscalar : ∀ z ∈ sphere c R, (z - w)⁻¹ * (w - z) = -1 := by
    intro z hz
    rw [show w - z = -(z - w) by abel, mul_neg,
      inv_mul_cancel₀ (sub_ne_zero.mpr (ne_of_mem_of_not_mem hz hw))]
  have hsum : ∮ z in C(c, R), (-resolvent a z + (z - w)⁻¹ • (1 : A)) =
      (∮ z in C(c, R), (z - w)⁻¹) • (1 : A) - ∮ z in C(c, R), resolvent a z := by
    rw [circleIntegral.integral_add hneg hone, circleIntegral.integral_smul_const]
    have : ∮ z in C(c, R), -resolvent a z = -∮ z in C(c, R), resolvent a z := by
      simpa using circleIntegral.integral_smul (-1 : ℂ) (resolvent a) c R
    rw [this]
    abel
  have hleft : (algebraMap ℂ A w - a) * ∮ z in C(c, R), (z - w)⁻¹ • resolvent a z =
      (∮ z in C(c, R), (z - w)⁻¹) • (1 : A) - ∮ z in C(c, R), resolvent a z := by
    rw [← circleIntegral_mul_left hweighted, ← hsum]
    refine circleIntegral.integral_congr hR fun z hz ↦ ?_
    simp only [mul_smul_comm, spectrum.algebraMap_sub_mul_resolvent_eq (hc hz), smul_add,
      smul_smul, hscalar z hz, neg_one_smul]
  have hright : (∮ z in C(c, R), (z - w)⁻¹ • resolvent a z) * (algebraMap ℂ A w - a) =
      (∮ z in C(c, R), (z - w)⁻¹) • (1 : A) - ∮ z in C(c, R), resolvent a z := by
    rw [← circleIntegral_mul_right hweighted, ← hsum]
    refine circleIntegral.integral_congr hR fun z hz ↦ ?_
    simp only [smul_mul_assoc, spectrum.resolvent_mul_algebraMap_sub_eq (hc hz), smul_add,
      smul_smul, hscalar z hz, neg_one_smul]
  constructor
  · rw [mul_smul_comm, hleft, rieszCircleIntegral, smul_sub, smul_smul]
  · rw [smul_mul_assoc, hright, rieszCircleIntegral, smul_sub, smul_smul]

/-- The key computation for products of Riesz integrals: if the first circle does not meet the
second closed disk, the product of the two resolvent integrals is an iterated integral of the
reversed Cauchy kernel. -/
private theorem circleIntegral_resolvent_mul_circleIntegral_resolvent {a : A} {c₁ c₂ : ℂ}
    {R₁ R₂ : ℝ} (hR₁ : 0 ≤ R₁) (hR₂ : 0 ≤ R₂) (h₁ : sphere c₁ R₁ ⊆ resolventSet ℂ a)
    (h₂ : sphere c₂ R₂ ⊆ resolventSet ℂ a) (hsep : Disjoint (sphere c₁ R₁) (closedBall c₂ R₂)) :
    (∮ z in C(c₁, R₁), resolvent a z) * (∮ w in C(c₂, R₂), resolvent a w) =
      -∮ w in C(c₂, R₂), (∮ z in C(c₁, R₁), (w - z)⁻¹) • resolvent a w := by
  have hint₁ := circleIntegrable_resolvent hR₁ h₁
  have hint₂ := circleIntegrable_resolvent hR₂ h₂
  have hres₂ : ContinuousOn (resolvent a) (sphere c₂ R₂) :=
    (spectrum.continuousOn_resolvent a).mono h₂
  have hne : ∀ z ∈ sphere c₁ R₁, ∀ w ∈ sphere c₂ R₂, z ≠ w := fun z hz w hw hzw ↦
    Set.disjoint_left.mp hsep hz (hzw ▸ sphere_subset_closedBall hw)
  have hprod : (∮ z in C(c₁, R₁), resolvent a z) * (∮ w in C(c₂, R₂), resolvent a w) =
      ∮ z in C(c₁, R₁), ∮ w in C(c₂, R₂), resolvent a z * resolvent a w := by
    rw [← circleIntegral_mul_right hint₁]
    exact circleIntegral.integral_congr hR₁ fun z _ ↦ (circleIntegral_mul_left hint₂ _).symm
  have hinner : ∀ z ∈ sphere c₁ R₁, ∮ w in C(c₂, R₂), resolvent a z * resolvent a w =
      -∮ w in C(c₂, R₂), (w - z)⁻¹ • resolvent a w := by
    intro z hz
    have hk : ContinuousOn (fun w : ℂ ↦ (w - z)⁻¹) (sphere c₂ R₂) :=
      (continuousOn_id.sub continuousOn_const).inv₀ fun w hw ↦ sub_ne_zero.mpr (hne z hz w hw).symm
    have hfirst : CircleIntegrable (fun w ↦ (w - z)⁻¹ • resolvent a z) c₂ R₂ :=
      (hk.smul continuousOn_const).circleIntegrable hR₂
    have hsecond : CircleIntegrable (fun w ↦ (w - z)⁻¹ • resolvent a w) c₂ R₂ :=
      (hk.smul hres₂).circleIntegrable hR₂
    have hz₂ : z ∉ closedBall c₂ R₂ := fun h ↦ Set.disjoint_left.mp hsep hz h
    calc ∮ w in C(c₂, R₂), resolvent a z * resolvent a w
        = ∮ w in C(c₂, R₂), ((w - z)⁻¹ • resolvent a z - (w - z)⁻¹ • resolvent a w) := by
          refine circleIntegral.integral_congr hR₂ fun w hw ↦ ?_
          rw [spectrum.resolvent_mul_resolvent (h₁ hz) (h₂ hw) (hne z hz w hw), smul_sub]
      _ = -∮ w in C(c₂, R₂), (w - z)⁻¹ • resolvent a w := by
          rw [circleIntegral.integral_sub hfirst hsecond, circleIntegral.integral_smul_const,
            circleIntegral.integral_sub_inv_of_notMem_closedBall hR₂ hz₂, zero_smul, zero_sub]
  have hkernel : ContinuousOn
      (fun p : ℝ × ℝ ↦ (circleMap c₂ R₂ p.2 - circleMap c₁ R₁ p.1)⁻¹ •
        resolvent a (circleMap c₂ R₂ p.2))
      (Icc 0 (2 * Real.pi) ×ˢ Icc 0 (2 * Real.pi)) := by
    refine ContinuousOn.smul ?_ ?_
    · refine (Continuous.continuousOn (by fun_prop)).inv₀ fun p _ ↦ sub_ne_zero.mpr ?_
      exact (hne _ (circleMap_mem_sphere _ hR₁ _) _ (circleMap_mem_sphere _ hR₂ _)).symm
    · exact hres₂.comp (Continuous.continuousOn (by fun_prop))
        (fun p _ ↦ circleMap_mem_sphere _ hR₂ _)
  rw [hprod, circleIntegral.integral_congr hR₁ hinner]
  have hneg : ∮ z in C(c₁, R₁), -∮ w in C(c₂, R₂), (w - z)⁻¹ • resolvent a w =
      -∮ z in C(c₁, R₁), ∮ w in C(c₂, R₂), (w - z)⁻¹ • resolvent a w := by
    simpa using circleIntegral.integral_smul (-1 : ℂ)
      (fun z ↦ ∮ w in C(c₂, R₂), (w - z)⁻¹ • resolvent a w) c₁ R₁
  rw [hneg, circleIntegral.integral_integral_swap hkernel]
  congr 1
  exact circleIntegral.integral_congr hR₂ fun w _ ↦ circleIntegral.integral_smul_const _ _ _ _

/-- Product formula for resolvent integrals over nested circles. -/
theorem circleIntegral_resolvent_mul_of_closedBall_subset_ball {a : A} {c₁ c₂ : ℂ} {R₁ R₂ : ℝ}
    (hR₁ : 0 ≤ R₁) (hR₂ : 0 ≤ R₂) (h₁ : sphere c₁ R₁ ⊆ resolventSet ℂ a)
    (h₂ : sphere c₂ R₂ ⊆ resolventSet ℂ a) (hnest : closedBall c₂ R₂ ⊆ ball c₁ R₁) :
    (∮ z in C(c₁, R₁), resolvent a z) * (∮ w in C(c₂, R₂), resolvent a w) =
      (2 * Real.pi * Complex.I : ℂ) • ∮ w in C(c₂, R₂), resolvent a w := by
  have hsep : Disjoint (sphere c₁ R₁) (closedBall c₂ R₂) :=
    Set.disjoint_of_subset_right hnest sphere_disjoint_ball
  have hcongr : ∮ w in C(c₂, R₂), (∮ z in C(c₁, R₁), (w - z)⁻¹) • resolvent a w =
      ∮ w in C(c₂, R₂), (-(2 * Real.pi * Complex.I : ℂ)) • resolvent a w :=
    circleIntegral.integral_congr hR₂ fun w hw ↦ by
      rw [circleIntegral.integral_inv_sub_of_mem_ball (hnest (sphere_subset_closedBall hw))]
  rw [circleIntegral_resolvent_mul_circleIntegral_resolvent hR₁ hR₂ h₁ h₂ hsep, hcongr,
    circleIntegral.integral_smul (-(2 * Real.pi * Complex.I : ℂ)) (resolvent a) c₂ R₂,
    neg_smul, neg_neg]

/-- Resolvent integrals around disjoint closed disks have zero product. -/
theorem circleIntegral_resolvent_mul_eq_zero_of_disjoint {a : A} {c₁ c₂ : ℂ} {R₁ R₂ : ℝ}
    (hR₁ : 0 ≤ R₁) (hR₂ : 0 ≤ R₂) (h₁ : sphere c₁ R₁ ⊆ resolventSet ℂ a)
    (h₂ : sphere c₂ R₂ ⊆ resolventSet ℂ a)
    (hdisj : Disjoint (closedBall c₁ R₁) (closedBall c₂ R₂)) :
    (∮ z in C(c₁, R₁), resolvent a z) * (∮ w in C(c₂, R₂), resolvent a w) = 0 := by
  have hsep : Disjoint (sphere c₁ R₁) (closedBall c₂ R₂) :=
    Set.disjoint_of_subset_left sphere_subset_closedBall hdisj
  have hcongr : ∮ w in C(c₂, R₂), (∮ z in C(c₁, R₁), (w - z)⁻¹) • resolvent a w =
      ∮ w in C(c₂, R₂), (0 : A) :=
    circleIntegral.integral_congr hR₂ fun w hw ↦ by
      rw [circleIntegral.integral_inv_sub_of_notMem_closedBall hR₁
        (fun h ↦ Set.disjoint_left.mp hdisj h (sphere_subset_closedBall hw)), zero_smul]
  rw [circleIntegral_resolvent_mul_circleIntegral_resolvent hR₁ hR₂ h₁ h₂ hsep, hcongr]
  simp [circleIntegral]

/-- If the closed disk of the second circle lies in the open disk of the first one (both circles
in the resolvent set), then the product of the Riesz integrals is the inner one. -/
theorem rieszCircleIntegral_mul_of_closedBall_subset_ball {a : A} {c₁ c₂ : ℂ} {R₁ R₂ : ℝ}
    (hR₁ : 0 ≤ R₁) (hR₂ : 0 ≤ R₂) (h₁ : sphere c₁ R₁ ⊆ resolventSet ℂ a)
    (h₂ : sphere c₂ R₂ ⊆ resolventSet ℂ a) (hnest : closedBall c₂ R₂ ⊆ ball c₁ R₁) :
    rieszCircleIntegral a c₁ R₁ * rieszCircleIntegral a c₂ R₂ = rieszCircleIntegral a c₂ R₂ := by
  simp only [rieszCircleIntegral, smul_mul_smul_comm,
    circleIntegral_resolvent_mul_of_closedBall_subset_ball hR₁ hR₂ h₁ h₂ hnest, smul_smul]
  rw [inv_mul_cancel_right₀ Complex.two_pi_I_ne_zero]

/-- Riesz integrals over circles bounding disjoint closed disks are orthogonal. -/
theorem rieszCircleIntegral_mul_eq_zero_of_disjoint {a : A} {c₁ c₂ : ℂ} {R₁ R₂ : ℝ}
    (hR₁ : 0 ≤ R₁) (hR₂ : 0 ≤ R₂) (h₁ : sphere c₁ R₁ ⊆ resolventSet ℂ a)
    (h₂ : sphere c₂ R₂ ⊆ resolventSet ℂ a)
    (hdisj : Disjoint (closedBall c₁ R₁) (closedBall c₂ R₂)) :
    rieszCircleIntegral a c₁ R₁ * rieszCircleIntegral a c₂ R₂ = 0 := by
  simp only [rieszCircleIntegral, smul_mul_smul_comm,
    circleIntegral_resolvent_mul_eq_zero_of_disjoint hR₁ hR₂ h₁ h₂ hdisj, smul_zero]

/-- The Riesz integral is unchanged when its circle is moved through an annulus in the resolvent
set. -/
theorem rieszCircleIntegral_eq_of_closedBall_diff_ball_subset {a : A} {c : ℂ} {r R : ℝ}
    (hr : 0 < r) (hrR : r ≤ R) (h : closedBall c R \ ball c r ⊆ resolventSet ℂ a) :
    rieszCircleIntegral a c R = rieszCircleIntegral a c r := by
  rw [rieszCircleIntegral, rieszCircleIntegral,
    Complex.circleIntegral_eq_of_differentiable_on_annulus_off_countable hr hrR countable_empty
      ((spectrum.continuousOn_resolvent a).mono h) fun z hz ↦
        (spectrum.hasDerivAt_resolvent_const_left (h ⟨ball_subset_closedBall hz.1.1,
          fun h' ↦ hz.1.2 (ball_subset_closedBall h')⟩)).differentiableAt]

/-- The Riesz integral over a circle whose closed disk lies in the resolvent set vanishes. -/
theorem rieszCircleIntegral_eq_zero_of_closedBall_subset {a : A} {c : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (h : closedBall c R ⊆ resolventSet ℂ a) : rieszCircleIntegral a c R = 0 := by
  rw [rieszCircleIntegral,
    Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable hR countable_empty
      ((spectrum.continuousOn_resolvent a).mono h) fun z hz ↦
        (spectrum.hasDerivAt_resolvent_const_left
          (h (ball_subset_closedBall hz.1))).differentiableAt,
    smul_zero]

/-- A Riesz integral over a circle of positive radius in the resolvent set is idempotent. -/
theorem isIdempotentElem_rieszCircleIntegral {a : A} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hc : sphere c R ⊆ resolventSet ℂ a) : IsIdempotentElem (rieszCircleIntegral a c R) := by
  obtain ⟨S, hRS, hann⟩ := exists_closedBall_diff_ball_subset_resolventSet_of_lt hc
  have hS : sphere c S ⊆ resolventSet ℂ a :=
    sphere_subset_of_closedBall_diff_ball_subset hRS.le hann
  have hprod := rieszCircleIntegral_mul_of_closedBall_subset_ball (hR.trans hRS).le hR.le hS hc
    (closedBall_subset_ball hRS)
  rwa [rieszCircleIntegral_eq_of_closedBall_diff_ball_subset hR hRS.le hann] at hprod

/-- A Riesz integral over a circle in the resolvent set of `a` commutes with every element that
commutes with `a`. -/
theorem commute_rieszCircleIntegral {a b : A} {c : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hc : sphere c R ⊆ resolventSet ℂ a) (h : Commute a b) :
    Commute (rieszCircleIntegral a c R) b := by
  refine Commute.smul_left ?_ _
  have hint := circleIntegrable_resolvent hR hc
  change (∮ z in C(c, R), resolvent a z) * b = b * ∮ z in C(c, R), resolvent a z
  rw [← circleIntegral_mul_right hint, ← circleIntegral_mul_left hint]
  exact circleIntegral.integral_congr hR fun z _ ↦ (spectrum.commute_resolvent_of_commute h z).eq

/-- A spectral point inside the circle forces the Riesz idempotent to be nonzero. -/
theorem rieszCircleIntegral_ne_zero {a : A} {c w : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hc : sphere c R ⊆ resolventSet ℂ a) (hw : w ∈ spectrum ℂ a) (hwc : w ∈ ball c R) :
    rieszCircleIntegral a c R ≠ 0 := by
  intro hzero
  obtain ⟨hleft, hright⟩ := algebraMap_sub_mul_cauchy_resolvent hR hc
    (fun h ↦ Set.disjoint_left.mp sphere_disjoint_ball h hwc)
  rw [circleIntegral.integral_sub_inv_of_mem_ball hwc, inv_mul_cancel₀ Complex.two_pi_I_ne_zero,
    one_smul, hzero, sub_zero] at hleft hright
  exact hw (isUnit_iff_exists.mpr ⟨_, hleft, hright⟩)

/-- A spectral point outside the closed disk forces the Riesz idempotent to differ from `1`. -/
theorem rieszCircleIntegral_ne_one {a : A} {c w : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hc : sphere c R ⊆ resolventSet ℂ a) (hw : w ∈ spectrum ℂ a) (hwc : w ∉ closedBall c R) :
    rieszCircleIntegral a c R ≠ 1 := by
  intro hone
  obtain ⟨hleft, hright⟩ := algebraMap_sub_mul_cauchy_resolvent hR hc
    (fun h ↦ hwc (sphere_subset_closedBall h))
  rw [circleIntegral.integral_sub_inv_of_notMem_closedBall hR hwc, mul_zero, zero_smul, hone,
    zero_sub] at hleft hright
  refine hw (isUnit_iff_exists.mpr ⟨-((2 * Real.pi * Complex.I : ℂ)⁻¹ •
    ∮ z in C(c, R), (z - w)⁻¹ • resolvent a z), ?_, ?_⟩)
  · rw [mul_neg, hleft, neg_neg]
  · rw [neg_mul, hright, neg_neg]

/-- Riesz integrals are covariant under conjugation by a unit. -/
theorem rieszCircleIntegral_units_conj {a : A} (u : Aˣ) {c : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hc : sphere c R ⊆ resolventSet ℂ a) :
    rieszCircleIntegral ((u : A) * a * ↑u⁻¹) c R = u * rieszCircleIntegral a c R * ↑u⁻¹ := by
  have hint := circleIntegrable_resolvent hR hc
  have hmap : ∮ z in C(c, R), (u : A) * resolvent a z * ↑u⁻¹ =
      (u : A) * (∮ z in C(c, R), resolvent a z) * ↑u⁻¹ := by
    simpa using (ContinuousLinearMap.mulLeftRight ℂ A (u : A) ↑u⁻¹).circleIntegral_comp_comm hint
  simp only [rieszCircleIntegral, spectrum.resolvent_units_conj, hmap, mul_smul_comm,
    smul_mul_assoc]

/-- Taking `star` sends a Riesz integral to the Riesz integral of `star a` over the conjugate
circle. -/
theorem star_rieszCircleIntegral [StarRing A] [StarModule ℂ A] [ContinuousStar A] {a : A} {c : ℂ}
    {R : ℝ} (hR : 0 ≤ R) (hc : sphere c R ⊆ resolventSet ℂ a) :
    star (rieszCircleIntegral a c R) = rieszCircleIntegral (star a) (star c) R := by
  rw [rieszCircleIntegral, rieszCircleIntegral, star_smul,
    circleIntegral.star_integral (circleIntegrable_resolvent hR hc)]
  simp only [spectrum.star_resolvent, star_star, star_inv₀]
  have hK : star (2 * Real.pi * Complex.I : ℂ) = -(2 * Real.pi * Complex.I : ℂ) := by simp
  rw [hK, inv_neg, neg_smul_neg]

/-- Two orthogonal Riesz idempotents whose open disks cover the spectrum add up to `1`. -/
theorem rieszCircleIntegral_add_rieszCircleIntegral_eq_one {a : A} {c₁ c₂ : ℂ} {R₁ R₂ : ℝ}
    (hR₁ : 0 < R₁) (hR₂ : 0 < R₂) (h₁ : sphere c₁ R₁ ⊆ resolventSet ℂ a)
    (h₂ : sphere c₂ R₂ ⊆ resolventSet ℂ a)
    (h₁₂ : rieszCircleIntegral a c₁ R₁ * rieszCircleIntegral a c₂ R₂ = 0)
    (h₂₁ : rieszCircleIntegral a c₂ R₂ * rieszCircleIntegral a c₁ R₁ = 0)
    (hcover : spectrum ℂ a ⊆ ball c₁ R₁ ∪ ball c₂ R₂) :
    rieszCircleIntegral a c₁ R₁ + rieszCircleIntegral a c₂ R₂ = 1 := by
  set P := rieszCircleIntegral a c₁ R₁ with hP_def
  set Q := rieszCircleIntegral a c₂ R₂ with hQ_def
  have hP : IsIdempotentElem P := isIdempotentElem_rieszCircleIntegral hR₁ h₁
  have hQ : IsIdempotentElem Q := isIdempotentElem_rieszCircleIntegral hR₂ h₂
  have hPa : Commute P a := commute_rieszCircleIntegral hR₁.le h₁ (Commute.refl a)
  have hQa : Commute Q a := commute_rieszCircleIntegral hR₂.le h₂ (Commute.refl a)
  set e : A := 1 - (P + Q) with he_def
  clear_value P Q e
  have hsum : IsIdempotentElem (P + Q) := by
    rw [IsIdempotentElem, add_mul, mul_add, mul_add, hP.eq, hQ.eq, h₁₂, h₂₁, zero_add, add_zero]
  have he : IsIdempotentElem e := he_def ▸ hsum.one_sub
  have hea : Commute e a := he_def ▸ (Commute.one_left a).sub_left (hPa.add_left hQa)
  have heP : e * P = 0 := by
    rw [he_def, sub_mul, one_mul, add_mul, hP.eq, h₂₁, add_zero, sub_self]
  have hPe : P * e = 0 := by
    rw [he_def, mul_sub, mul_one, mul_add, hP.eq, h₁₂, add_zero, sub_self]
  have heQ : e * Q = 0 := by
    rw [he_def, sub_mul, one_mul, add_mul, hQ.eq, h₁₂, zero_add, sub_self]
  have hQe : Q * e = 0 := by
    rw [he_def, mul_sub, mul_one, mul_add, hQ.eq, h₂₁, zero_add, sub_self]
  -- the compressed shift factors through `e`
  have hshift : ∀ z : ℂ, z • e - e * a * e = e * (algebraMap ℂ A z - a) ∧
      z • e - e * a * e = (algebraMap ℂ A z - a) * e := by
    intro z
    have heae : e * a * e = e * a := by rw [mul_assoc, ← hea.eq, ← mul_assoc, he.eq]
    rw [heae]
    refine ⟨?_, ?_⟩
    · rw [mul_sub e (algebraMap ℂ A z) a, ← Algebra.commutes, ← Algebra.smul_def]
    · rw [sub_mul (algebraMap ℂ A z) a e, ← Algebra.smul_def, ← hea.eq]
  have hzero : e = 0 := by
    refine he.eq_zero_of_forall_exists_inverse a fun z ↦ ?_
    by_cases hz : z ∈ spectrum ℂ a
    · -- `z` lies inside one of the two circles
      have hinv : ∀ (c : ℂ) (R : ℝ) (Pc : A), 0 < R → sphere c R ⊆ resolventSet ℂ a →
          rieszCircleIntegral a c R = Pc → z ∈ ball c R → e * Pc = 0 → Pc * e = 0 →
          ∃ b : A, (z • e - e * a * e) * b = e ∧ b * (z • e - e * a * e) = e := by
        intro c R Pc hR hc hPc hzc heP' hPe'
        obtain ⟨hleft, hright⟩ := algebraMap_sub_mul_cauchy_resolvent hR.le hc
          (fun h ↦ Set.disjoint_left.mp sphere_disjoint_ball h hzc)
        rw [circleIntegral.integral_sub_inv_of_mem_ball hzc,
          inv_mul_cancel₀ Complex.two_pi_I_ne_zero, one_smul, hPc] at hleft hright
        refine ⟨(2 * Real.pi * Complex.I : ℂ)⁻¹ • ∮ w in C(c, R), (w - z)⁻¹ • resolvent a w,
          ?_, ?_⟩
        · rw [(hshift z).1, mul_assoc, hleft, mul_sub, mul_one, heP', sub_zero]
        · rw [(hshift z).2, ← mul_assoc, hright, sub_mul, one_mul, hPe', sub_zero]
      rcases hcover hz with hz₁ | hz₂
      · exact hinv c₁ R₁ P hR₁ h₁ hP_def.symm hz₁ heP hPe
      · exact hinv c₂ R₂ Q hR₂ h₂ hQ_def.symm hz₂ heQ hQe
    · have hres : z ∈ resolventSet ℂ a := spectrum.notMem_iff.mp hz
      refine ⟨resolvent a z, ?_, ?_⟩
      · rw [(hshift z).1, mul_assoc, spectrum.algebraMap_sub_mul_resolvent hres, mul_one]
      · rw [(hshift z).2, ← mul_assoc, spectrum.resolvent_mul_algebraMap_sub hres, one_mul]
  rw [he_def, sub_eq_zero] at hzero
  exact hzero.symm

/-! ### The upper half-plane -/

private theorem norm_sub_ofReal_mul_I_sq (z : ℂ) (C : ℝ) :
    ‖z - (C : ℂ) * Complex.I‖ ^ 2 = ‖z‖ ^ 2 + C ^ 2 - 2 * C * z.im := by
  rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
  simp
  ring

private theorem norm_add_ofReal_mul_I_sq (z : ℂ) (C : ℝ) :
    ‖z + (C : ℂ) * Complex.I‖ ^ 2 = ‖z‖ ^ 2 + C ^ 2 + 2 * C * z.im := by
  rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
  simp
  ring

private theorem mem_ball_mul_I_iff {z : ℂ} {C : ℝ} (hC : 0 < C) :
    z ∈ ball ((C : ℂ) * Complex.I) C ↔ ‖z‖ ^ 2 < 2 * C * z.im := by
  rw [mem_ball_iff_norm, ← sq_lt_sq₀ (norm_nonneg _) hC.le, norm_sub_ofReal_mul_I_sq]
  constructor <;> intro h <;> linarith

private theorem mem_closedBall_mul_I_iff {z : ℂ} {C : ℝ} (hC : 0 < C) :
    z ∈ closedBall ((C : ℂ) * Complex.I) C ↔ ‖z‖ ^ 2 ≤ 2 * C * z.im := by
  rw [mem_closedBall_iff_norm, ← sq_le_sq₀ (norm_nonneg _) hC.le, norm_sub_ofReal_mul_I_sq]
  constructor <;> intro h <;> linarith

private theorem mem_ball_neg_mul_I_iff {z : ℂ} {C : ℝ} (hC : 0 < C) :
    z ∈ ball (-((C : ℂ) * Complex.I)) C ↔ ‖z‖ ^ 2 < -(2 * C * z.im) := by
  rw [mem_ball_iff_norm, sub_neg_eq_add, ← sq_lt_sq₀ (norm_nonneg _) hC.le,
    norm_add_ofReal_mul_I_sq]
  constructor <;> intro h <;> linarith

private theorem mem_closedBall_neg_mul_I_iff {z : ℂ} {C : ℝ} (hC : 0 < C) :
    z ∈ closedBall (-((C : ℂ) * Complex.I)) C ↔ ‖z‖ ^ 2 ≤ -(2 * C * z.im) := by
  rw [mem_closedBall_iff_norm, sub_neg_eq_add, ← sq_le_sq₀ (norm_nonneg _) hC.le,
    norm_add_ofReal_mul_I_sq]
  constructor <;> intro h <;> linarith

/-- If the spectrum of `a` avoids the real axis, there is a circle centered on the positive
imaginary axis and tangent to the real axis at `0` whose open disk contains the upper part of the
spectrum, while the conjugate disk contains the lower part. -/
theorem exists_pos_forall_mem_ball_mul_I (a : A) (ha : ∀ z ∈ spectrum ℂ a, z.im ≠ 0) :
    ∃ C : ℝ, 0 < C ∧ (∀ z ∈ spectrum ℂ a, 0 < z.im → z ∈ ball ((C : ℂ) * Complex.I) C) ∧
      ∀ z ∈ spectrum ℂ a, z.im < 0 → z ∈ ball (-((C : ℂ) * Complex.I)) C := by
  obtain ⟨δ, hδ, hgap⟩ : ∃ δ : ℝ, 0 < δ ∧ ∀ z ∈ spectrum ℂ a, δ ≤ |z.im| := by
    rcases (spectrum ℂ a).eq_empty_or_nonempty with h | h
    · exact ⟨1, one_pos, by simp [h]⟩
    obtain ⟨z, hz, hmin⟩ := (spectrum.isCompact a).exists_isMinOn h
      Complex.continuous_im.abs.continuousOn
    exact ⟨|z.im|, abs_pos.mpr (ha z hz), fun _ hw ↦ hmin hw⟩
  obtain ⟨N, hN⟩ := (spectrum.isCompact (𝕜 := ℂ) a).isBounded.exists_norm_le
  set C : ℝ := (N ^ 2 + 1) / (2 * δ) with hC_def
  have hC : 0 < C := div_pos (by positivity) (by positivity)
  have hsep : N ^ 2 < 2 * C * δ := by
    rw [hC_def]
    field_simp
    linarith
  have hnorm : ∀ z ∈ spectrum ℂ a, ‖z‖ ^ 2 < 2 * C * |z.im| := by
    intro z hz
    have h1 : ‖z‖ ^ 2 ≤ N ^ 2 := by
      have := hN z hz
      nlinarith [norm_nonneg z]
    have h2 : 2 * C * δ ≤ 2 * C * |z.im| := by
      have := hgap z hz
      nlinarith
    linarith
  refine ⟨C, hC, fun z hz him ↦ ?_, fun z hz him ↦ ?_⟩
  · rw [mem_ball_mul_I_iff hC]
    simpa [abs_of_pos him] using hnorm z hz
  · rw [mem_ball_neg_mul_I_iff hC]
    have := hnorm z hz
    rw [abs_of_neg him] at this
    linarith

/-- **The Riesz idempotent of the upper half-plane.**  Let `a` be an element of a complex Banach
star algebra whose spectrum avoids the real axis.  Then there is an idempotent `P` commuting with
every element commuting with `a`, such that `P ≠ 0` iff the spectrum of `a` meets the open upper
half-plane, `P ≠ 1` iff it meets the open lower half-plane, and `star P * u = u * (1 - P)` for every
unit `u` intertwining `a` and `star a` in the sense that `star a * u = u * a`.

`P` is the Riesz integral over a circle tangent to the real axis whose disk contains the upper part
of the spectrum; `1 - P` is the Riesz integral over the conjugate circle. -/
theorem exists_isIdempotentElem_upperHalfPlane [StarRing A] [StarModule ℂ A] [ContinuousStar A]
    (a : A) (ha : ∀ z ∈ spectrum ℂ a, z.im ≠ 0) :
    ∃ P : A, IsIdempotentElem P ∧ (∀ b : A, Commute a b → Commute P b) ∧
      (P ≠ 0 ↔ ∃ z ∈ spectrum ℂ a, 0 < z.im) ∧ (P ≠ 1 ↔ ∃ z ∈ spectrum ℂ a, z.im < 0) ∧
      ∀ u : Aˣ, star a * u = u * a → star P * u = u * (1 - P) := by
  obtain ⟨C, hC, hupper, hlower⟩ := exists_pos_forall_mem_ball_mul_I a ha
  set c : ℂ := (C : ℂ) * Complex.I with hc_def
  have hstar_c : star c = -c := by simp [hc_def]
  -- the two circles lie in the resolvent set
  have hsphU : sphere c C ⊆ resolventSet ℂ a := by
    intro z hz
    by_contra hzs
    have hnorm : ‖z - c‖ = C := mem_sphere_iff_norm.mp hz
    rcases lt_or_gt_of_ne (ha z hzs) with him | him
    · have h1 := (mem_ball_neg_mul_I_iff hC).mp (hlower z hzs him)
      have h2 := (mem_closedBall_mul_I_iff hC).mp (mem_closedBall_iff_norm.mpr hnorm.le)
      nlinarith
    · exact (mem_ball_iff_norm.mp (hupper z hzs him)).ne hnorm
  have hsphL : sphere (-c) C ⊆ resolventSet ℂ a := by
    intro z hz
    by_contra hzs
    have hnorm : ‖z - -c‖ = C := mem_sphere_iff_norm.mp hz
    rcases lt_or_gt_of_ne (ha z hzs) with him | him
    · exact (mem_ball_iff_norm.mp (hlower z hzs him)).ne hnorm
    · have h1 := (mem_ball_mul_I_iff hC).mp (hupper z hzs him)
      have h2 := (mem_closedBall_neg_mul_I_iff hC).mp (mem_closedBall_iff_norm.mpr hnorm.le)
      nlinarith
  set P := rieszCircleIntegral a c C with hP_def
  set Q := rieszCircleIntegral a (-c) C with hQ_def
  -- orthogonality, after shrinking both circles
  have horth : P * Q = 0 ∧ Q * P = 0 := by
    obtain ⟨r, hr, hrC, hannU⟩ := exists_closedBall_diff_ball_subset_resolventSet_of_gt hC hsphU
    obtain ⟨s, hs, hsC, hannL⟩ := exists_closedBall_diff_ball_subset_resolventSet_of_gt hC hsphL
    have hr' := sphere_subset_of_closedBall_diff_ball_subset' hrC.le hannU
    have hs' := sphere_subset_of_closedBall_diff_ball_subset' hsC.le hannL
    have hdisj : Disjoint (closedBall c r) (closedBall (-c) s) := by
      apply closedBall_disjoint_closedBall
      have : dist c (-c) = 2 * C := by
        rw [dist_eq_norm, sub_neg_eq_add, ← two_mul, hc_def, norm_mul, norm_mul]
        simp [abs_of_pos hC]
      rw [this]
      linarith
    rw [hP_def, hQ_def, rieszCircleIntegral_eq_of_closedBall_diff_ball_subset hr hrC.le hannU,
      rieszCircleIntegral_eq_of_closedBall_diff_ball_subset hs hsC.le hannL]
    exact ⟨rieszCircleIntegral_mul_eq_zero_of_disjoint hr.le hs.le hr' hs' hdisj,
      rieszCircleIntegral_mul_eq_zero_of_disjoint hs.le hr.le hs' hr' hdisj.symm⟩
  have hcover : spectrum ℂ a ⊆ ball c C ∪ ball (-c) C := by
    intro z hz
    rcases lt_or_gt_of_ne (ha z hz) with him | him
    · exact Or.inr (hlower z hz him)
    · exact Or.inl (hupper z hz him)
  have hPQ : P + Q = 1 :=
    rieszCircleIntegral_add_rieszCircleIntegral_eq_one hC hC hsphU hsphL horth.1 horth.2 hcover
  refine ⟨P, isIdempotentElem_rieszCircleIntegral hC hsphU,
    fun b hb ↦ commute_rieszCircleIntegral hC.le hsphU hb, ⟨fun hP ↦ ?_, fun ⟨z, hz, him⟩ ↦
      rieszCircleIntegral_ne_zero hC.le hsphU hz (hupper z hz him)⟩,
    ⟨fun hP ↦ ?_, fun ⟨z, hz, him⟩ ↦ rieszCircleIntegral_ne_one hC.le hsphU hz ?_⟩, ?_⟩
  · -- if there is no upper spectrum, the closed upper disk lies in the resolvent set
    by_contra hno
    push Not at hno
    apply hP
    refine rieszCircleIntegral_eq_zero_of_closedBall_subset hC.le fun z hz ↦ ?_
    by_contra hzs
    have h1 := (mem_closedBall_mul_I_iff hC).mp hz
    have h2 : z.im < 0 := lt_of_le_of_ne (hno z hzs) (ha z hzs)
    nlinarith [sq_nonneg ‖z‖]
  · by_contra hno
    push Not at hno
    apply hP
    have hQ0 : Q = 0 := by
      refine rieszCircleIntegral_eq_zero_of_closedBall_subset hC.le fun z hz ↦ ?_
      by_contra hzs
      have h1 := (mem_closedBall_neg_mul_I_iff hC).mp hz
      have h2 : 0 < z.im := lt_of_le_of_ne (hno z hzs) (ha z hzs).symm
      nlinarith [sq_nonneg ‖z‖]
    rw [← hPQ, hQ0, add_zero]
  · rw [mem_closedBall_mul_I_iff hC, not_le]
    nlinarith [sq_nonneg ‖z‖]
  · intro u hu
    have ha' : star a = u * a * ↑u⁻¹ := by rw [← hu, mul_assoc, Units.mul_inv, mul_one]
    have hstarP : star P = u * (1 - P) * ↑u⁻¹ := by
      rw [hP_def, star_rieszCircleIntegral hC.le hsphU, ha', hstar_c,
        rieszCircleIntegral_units_conj u hC.le hsphL, ← hQ_def, ← hPQ, add_sub_cancel_left]
    rw [hstarP, mul_assoc, Units.inv_mul, mul_one]

end Riesz
