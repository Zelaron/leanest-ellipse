import LeanestEllipse.EllipseCriterion.UnorientedParametrization
import Mathlib.Topology.Maps.Proper.CompactlyGenerated
import Mathlib.Topology.Homeomorph.Quotient
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Normed.Module.Span

/-!
# The Möbius line bundle of unoriented lines

The standard Möbius real line bundle is the associated sign quotient
`(Circle × ℝ) / ((ω,p) ∼ (-ω,-p))`, with base projection `[ω,p] ↦ ω²` and the quotient topology.
Its real fiber coordinate is unrestricted.

We construct a homeomorphism from this quotient to the concrete surface
`Σ = {(q,z) : ℂ × ℂ | ‖q‖ = 1, z = q conj z}` used in the article. The map is
`[ω,p] ↦ (ω²,pω)` and preserves the base projection. The proof first shows that the map from
`Circle × ℝ` is proper: compact subsets of `Σ` bound `|p|`, and `Circle` is compact. It is
therefore a closed quotient map. Its fibers are exactly simultaneous sign reversal.

We also prove the explicit angle gluing at `θ + π`, identify each fiber with the real line
`ℝ ∙ ω`, and give its linear isometric coordinate map from `ℝ` and its real dimension one.
Thus the topological statement is stronger than the Borel parametrization of the half-period.
-/

open Set Metric Complex
open scoped Real ComplexConjugate

set_option autoImplicit false

noncomputable section

namespace LeanestEllipse

/-- The double-cover map defining the Möbius real line bundle. -/
def mobiusCover : C(Circle × ℝ, mobiusBundle) where
  toFun x := ⟨((x.1 : ℂ) ^ 2, (x.2 : ℂ) * x.1), by
    constructor
    · simp
    · change (x.2 : ℂ) * x.1 = (x.1 : ℂ) ^ 2 * conj ((x.2 : ℂ) * x.1)
      have hω : (x.1 : ℂ) * conj (x.1 : ℂ) = 1 := by
        rw [Complex.mul_conj']
        simp
      rw [map_mul, conj_ofReal]
      calc
        (x.2 : ℂ) * x.1 = (x.2 : ℂ) * x.1 * ((x.1 : ℂ) * conj (x.1 : ℂ)) := by
          rw [hω, mul_one]
        _ = _ := by ring⟩
  continuous_toFun := by fun_prop

theorem mobiusCover_surjective : Function.Surjective mobiusCover := by
  rintro ⟨⟨q,z⟩, hw⟩
  obtain ⟨θ, p, hθp, -, -⟩ := exists_unorientedLineCoords_eq_of_mem_mobiusBundle hw
  refine ⟨(Circle.exp θ, p), Subtype.ext ?_⟩
  change ((Complex.exp (θ * I)) ^ 2, (p : ℂ) * Complex.exp (θ * I)) = (q,z)
  rw [← unorientedLineCoords_eq_sq (θ,p)]
  exact hθp

theorem mobiusCover_eq_iff (x y : Circle × ℝ) :
    mobiusCover x = mobiusCover y ↔ x = y ∨ x = -y := by
  constructor
  · intro h
    have h1 : (x.1 : ℂ) ^ 2 = (y.1 : ℂ) ^ 2 := congrArg (fun a : mobiusBundle ↦ a.val.1) h
    have h2 : (x.2 : ℂ) * x.1 = (y.2 : ℂ) * y.1 :=
      congrArg (fun a : mobiusBundle ↦ a.val.2) h
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp h1 with he | he
    · left
      have hω : x.1 = y.1 := Circle.ext he
      refine Prod.ext hω ?_
      rw [hω] at h2
      exact Complex.ofReal_inj.mp (mul_right_cancel₀ (Circle.coe_ne_zero y.1) h2)
    · right
      have hω : x.1 = -y.1 := Circle.ext he
      refine Prod.ext hω ?_
      rw [hω] at h2
      have hp : (-(x.2 : ℂ)) = (y.2 : ℂ) :=
        mul_right_cancel₀ (Circle.coe_ne_zero y.1) (by simpa using h2)
      have hp' : -x.2 = y.2 := by exact_mod_cast hp
      simpa using congrArg Neg.neg hp'
  · rintro (rfl | rfl)
    · rfl
    · apply Subtype.ext
      simp [mobiusCover]

theorem isProperMap_mobiusCover : IsProperMap mobiusCover := by
  apply isProperMap_iff_isCompact_preimage.mpr
  refine ⟨mobiusCover.continuous, ?_⟩
  intro K hK
  have himage : IsCompact ((fun a : mobiusBundle ↦ a.val.2) '' K) :=
    hK.image (continuous_snd.comp continuous_subtype_val)
  obtain ⟨R,hR⟩ := himage.isBounded.exists_norm_le
  refine ((isCompact_univ : IsCompact (univ : Set Circle)).prod
    (isCompact_Icc : IsCompact (Icc (-R) R))).of_isClosed_subset
      (hK.isClosed.preimage mobiusCover.continuous) ?_
  intro x hx
  refine ⟨mem_univ _, ?_⟩
  have hp : |x.2| ≤ R := by
    have := hR (mobiusCover x).val.2 ⟨mobiusCover x, hx, rfl⟩
    simpa [mobiusCover, norm_mul, Complex.norm_real, Real.norm_eq_abs] using this
  exact abs_le.mp hp

/-- The equivalence relation for the standard associated-bundle construction:
simultaneously reverse the unit normal and the real fiber coordinate. -/
def mobiusSignSetoid : Setoid (Circle × ℝ) where
  r x y := x = y ∨ x = -y
  iseqv := by
    refine ⟨fun x ↦ Or.inl rfl, ?_, ?_⟩
    · intro x y h
      exact (mobiusCover_eq_iff y x).mp ((mobiusCover_eq_iff x y).mpr h).symm
    · intro x y z hxy hyz
      exact (mobiusCover_eq_iff x z).mp
        (((mobiusCover_eq_iff x y).mpr hxy).trans ((mobiusCover_eq_iff y z).mpr hyz))

/-- The standard Möbius line bundle associated to the squaring double cover of the circle
and its sign action on `ℝ`, equipped with the quotient topology. -/
abbrev MobiusLineBundle := Quotient mobiusSignSetoid

/-- The algebraic unoriented-line surface is homeomorphic to the standard Möbius quotient. -/
def mobiusLineBundleHomeomorph : MobiusLineBundle ≃ₜ mobiusBundle :=
  (Homeomorph.Quotient.congrRight (r := mobiusSignSetoid) (r' := Setoid.ker mobiusCover)
    (fun x y ↦ (mobiusCover_eq_iff x y).symm)).trans
      (isProperMap_mobiusCover.isClosedMap.isQuotientMap mobiusCover.continuous
        mobiusCover_surjective).homeomorph

@[simp]
theorem mobiusLineBundleHomeomorph_mk (ω : Circle) (p : ℝ) :
    (mobiusLineBundleHomeomorph (Quotient.mk mobiusSignSetoid (ω,p)) : ℂ × ℂ) =
      ((ω : ℂ) ^ 2, (p : ℂ) * ω) := by
  rfl

/-- The base projection of the Möbius quotient is the squaring map on its unit normal. -/
def mobiusLineBundleProjection : C(MobiusLineBundle, Circle) where
  toFun := Quotient.lift (fun x : Circle × ℝ ↦ x.1 ^ 2) (by
    rintro x y (rfl | rfl)
    · rfl
    · simp)
  continuous_toFun := continuous_quot_lift _ (by fun_prop)

@[simp]
theorem mobiusLineBundleProjection_mk (ω : Circle) (p : ℝ) :
    mobiusLineBundleProjection (Quotient.mk mobiusSignSetoid (ω,p)) = ω ^ 2 := rfl

/-- The homeomorphism identifies the standard bundle projection with the `q` coordinate. -/
theorem mobiusLineBundleHomeomorph_base (m : MobiusLineBundle) :
    (mobiusLineBundleHomeomorph m : ℂ × ℂ).1 = (mobiusLineBundleProjection m : ℂ) := by
  refine Quotient.inductionOn m fun x ↦ ?_
  rfl

/-- Every point of the base circle has a nonempty fiber. -/
theorem mobiusLineBundleProjection_surjective :
    Function.Surjective mobiusLineBundleProjection := by
  intro q
  have hq : ((q : ℂ),0) ∈ mobiusBundle := ⟨Circle.norm_coe q, by simp⟩
  obtain ⟨x,hx⟩ := mobiusCover_surjective ⟨((q : ℂ),0),hq⟩
  refine ⟨Quotient.mk mobiusSignSetoid x, Circle.ext ?_⟩
  exact congrArg (fun a : mobiusBundle ↦ a.val.1) hx

/-- The transition at the other square root of the base point reverses the real coordinate. -/
theorem mobiusLineBundle_mk_neg (ω : Circle) (p : ℝ) :
    Quotient.mk mobiusSignSetoid (-ω,-p) = Quotient.mk mobiusSignSetoid (ω,p) := by
  apply Quotient.sound
  exact Or.inr rfl

/-- In angle coordinates one circuit of the base changes the sign of the real coordinate. -/
theorem mobiusLineBundle_angle_gluing (θ p : ℝ) :
    Quotient.mk mobiusSignSetoid (Circle.exp (θ + π), -p) =
      Quotient.mk mobiusSignSetoid (Circle.exp θ, p) := by
  apply mobiusLineBundleHomeomorph.injective
  apply Subtype.ext
  change ((Complex.exp (((θ + π : ℝ) : ℂ) * I)) ^ 2,
    ((-p : ℝ) : ℂ) * Complex.exp (((θ + π : ℝ) : ℂ) * I)) =
      ((Complex.exp (θ * I)) ^ 2, (p : ℂ) * Complex.exp (θ * I))
  rw [← unorientedLineCoords_eq_sq (θ + π, -p), ← unorientedLineCoords_eq_sq (θ,p)]
  exact unorientedLineCoords_add_pi_neg θ p

/-- The fiber at `q = ω²` is exactly the real line spanned by `ω`, with no restriction on
the real coordinate. -/
theorem mobiusBundle_fiber_eq_realLine (ω : Circle) :
    {z : ℂ | ((ω : ℂ) ^ 2,z) ∈ mobiusBundle} = (ℝ ∙ (ω : ℂ) : Set ℂ) := by
  let a : ℂ := ω
  change {z : ℂ | (a ^ 2,z) ∈ mobiusBundle} = (ℝ ∙ a : Set ℂ)
  ext z
  constructor
  · intro hz
    obtain ⟨⟨v,p⟩, h⟩ := mobiusCover_surjective ⟨(a ^ 2,z),hz⟩
    have hq : (v : ℂ) ^ 2 = a ^ 2 := congrArg (fun a : mobiusBundle ↦ a.val.1) h
    have hp : (p : ℂ) * v = z := congrArg (fun a : mobiusBundle ↦ a.val.2) h
    change z ∈ (ℝ ∙ a)
    rw [Submodule.mem_span_singleton]
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hq with hv | hv
    · refine ⟨p, ?_⟩
      simpa only [Complex.real_smul, hv] using hp
    · refine ⟨-p, ?_⟩
      rw [Complex.real_smul, Complex.ofReal_neg, ← hp, hv]
      ring
  · intro hz
    change z ∈ (ℝ ∙ a) at hz
    rw [Submodule.mem_span_singleton] at hz
    obtain ⟨p,rfl⟩ := hz
    exact (mobiusCover (ω,p)).property

/-- The real-line fiber coordinates are linear isometries, hence homeomorphisms. -/
def mobiusFiberLinearIsometry (ω : Circle) : ℝ ≃ₗᵢ[ℝ] ℝ ∙ (ω : ℂ) :=
  LinearIsometryEquiv.toSpanUnitSingleton (ω : ℂ) (Circle.norm_coe ω)

@[simp]
theorem mobiusFiberLinearIsometry_apply (ω : Circle) (p : ℝ) :
    (mobiusFiberLinearIsometry ω p : ℂ) = (p : ℂ) * ω := rfl

/-- The fibers are one-dimensional real vector spaces. -/
theorem finrank_mobius_fiber (ω : Circle) : Module.finrank ℝ (ℝ ∙ (ω : ℂ)) = 1 :=
  finrank_span_singleton (Circle.coe_ne_zero ω)

end LeanestEllipse
