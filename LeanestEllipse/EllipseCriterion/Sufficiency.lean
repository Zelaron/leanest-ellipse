import LeanestEllipse.LinearAlgebra.LinearIndependent.Triangular
import LeanestEllipse.Topology.Algebra.Support
import LeanestEllipse.Analysis.Convex.Ellipsoid.Affine
import LeanestEllipse.IntegralGeometry.Radon.ConcentricDisks
import LeanestEllipse.IntegralGeometry.Radon.Affine
import LeanestEllipse.EllipseCriterion.Defs

/-!
# Sufficiency ([Hägg, Proposition 5])

Let `D` be an open subset of a two-dimensional real inner product space and `e ⋐ D` an ellipse
with center `c` and parametrization `c + A (closedBall 0 1)`.  Transporting the concentric-disk
function of [Hägg, Lemma 4] by `x ↦ A⁻¹ (x - c)` gives a nonzero real `u ∈ C_c^∞(D)` whose Radon
transform vanishes on every line meeting `e`, including its tangent lines; it is centrally
symmetric about `c`, strictly negative on an open neighbourhood of `e`, and `e ⊆ supp u`.  Nested
annuli give a linearly independent sequence of such witnesses.

## Main results

* `LeanestEllipse.sufficiency`: [Hägg, Proposition 5] for a single witness;
* `LeanestEllipse.sufficiency_linearIndependent`: the countably infinite linearly independent
  family;
* `linearIndependent_of_triangular_evaluations`: a triangularity criterion for linear
  independence of functions.
-/

open MeasureTheory Set Metric Function
open scoped RealInnerProductSpace CompactlyContained

noncomputable section

namespace LeanestEllipse

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fact (Module.finrank ℝ E = 2)] [MeasurableSpace E] [BorelSpace E]

attribute [local instance] FiniteDimensional.of_fact_finrank_eq_two

omit [MeasurableSpace E] [BorelSpace E] in
/-- A line meeting an ellipse `c + A (closedBall 0 1)` has offset within `‖A* ω‖` of `⟪c, ω⟫`. -/
theorem _root_.Ellipsoid.abs_sub_le_of_lineMeets (e : Ellipsoid E) {ω : E} {p : ℝ}
    (h : LineMeets (e : Set E) ω p) :
    |p - ⟪e.center, ω⟫| ≤ ‖ContinuousLinearMap.adjoint (e.linearPart : E →L[ℝ] E) ω‖ := by
  have := mem_Icc_of_exists_inner_eq e.isBounded h
  rw [e.lowerSupportFunction_eq, e.supportFunction_eq] at this
  rw [abs_le]
  constructor <;> linarith [this.1, this.2]

/-- The transported concentric-disk witness for radii `r < R` (with `1 ≤ r`), before choosing the
radii. -/
theorem exists_ellipse_witness (e : Ellipsoid E) {r R : ℝ} (hr : 1 ≤ r) (hrR : r < R) :
    ∃ u : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) u ∧ HasCompactSupport u ∧
      tsupport u ⊆ (fun y ↦ e.center + e.linearPart y) '' ball 0 R ∧
      (∀ ω : E, ‖ω‖ = 1 → ∀ p : ℝ, LineMeets (e : Set E) ω p → radonTransform u ω p = 0) ∧
      (∀ x, u (e.center + x) = u (e.center - x)) ∧
      (∃ U : Set E, IsOpen U ∧ (fun y ↦ e.center + e.linearPart y) '' closedBall 0 r ⊆ U ∧
        ∀ x ∈ U, u x < 0) := by
  obtain ⟨f, hfs, hfc, hfR, -, ⟨Ψ, -, hΨ⟩, hfvan, -, U, hUo, hrU, hfU⟩ :=
    exists_radial_radonTransform_eq_zero (E := E) (by linarith) hrR
  set φ := e.normalizeHomeomorph
  refine ⟨f ∘ φ, ?_, hfc.comp_homeomorph φ, ?_, ?_, ?_, ?_⟩
  · exact hfs.comp ((e.linearPart.symm : E →L[ℝ] E).contDiff.comp (contDiff_id.sub contDiff_const))
  · rw [tsupport_comp_homeomorph]
    intro x hx
    refine ⟨φ x, hfR hx, ?_⟩
    simp [φ]
  · intro ω hω p hp
    have hform := radonTransform_comp_affine e.linearPart e.center hω f p
    change radonTransform (fun x ↦ f (e.linearPart.symm (x - e.center))) ω p = 0
    rw [hform]
    have hs : 0 < ‖ContinuousLinearMap.adjoint (e.linearPart : E →L[ℝ] E) ω‖ :=
      norm_pos_iff.mpr (RadonTransform.adj_ne_zero e.linearPart
        (norm_ne_zero_iff.mp (by rw [hω]; norm_num)))
    rw [hfvan _ (RadonTransform.norm_adjNormal (norm_ne_zero_iff.mp (by rw [hω]; norm_num))) _,
      smul_zero]
    rw [abs_div, abs_of_pos hs, div_le_iff₀ hs]
    exact (e.abs_sub_le_of_lineMeets hp).trans (le_mul_of_one_le_left hs.le hr)
  · intro x
    simp only [comp_apply, φ, Ellipsoid.normalizeHomeomorph_apply, add_sub_cancel_left,
      sub_sub_cancel_left, map_neg, hΨ, norm_neg]
  · refine ⟨φ ⁻¹' U, hUo.preimage φ.continuous, ?_, fun x hx ↦ hfU _ hx⟩
    rintro _ ⟨y, hy, rfl⟩
    change φ (e.center + e.linearPart y) ∈ U
    simpa [φ] using hrU hy

/-- **Sufficiency** ([Hägg, Proposition 5]).  Let `D` be open and `e ⋐ D` an ellipse.  There is a
nonzero real `u ∈ C_c^∞(D)` whose Radon transform vanishes on every line meeting `e`, including
its tangent lines.  It is centrally symmetric about the center of `e` and strictly negative on an
open neighbourhood of `e`; in particular `e ⊆ supp u`. -/
theorem sufficiency {D : Set E} (hD : IsOpen D) (e : Ellipsoid E) (heD : (e : Set E) ⊆ D) :
    ∃ u : E → ℝ, u ≠ 0 ∧ ContDiff ℝ (⊤ : ℕ∞) u ∧ tsupport u ⋐ D ∧
      (∀ ω : E, ‖ω‖ = 1 → ∀ p : ℝ, LineMeets (e : Set E) ω p → radonTransform u ω p = 0) ∧
      (∀ x, u (e.center + x) = u (e.center - x)) ∧
      (∃ U : Set E, IsOpen U ∧ (e : Set E) ⊆ U ∧ ∀ x ∈ U, u x < 0) ∧
      (e : Set E) ⊆ tsupport u := by
  obtain ⟨R, hR1, hRD⟩ := e.exists_one_lt_image_closedBall_subset hD heD
  obtain ⟨u, hus, huc, husupp, huvan, husymm, U, hUo, hU, huU⟩ :=
    exists_ellipse_witness e le_rfl hR1
  have heU : (e : Set E) ⊆ U := hU
  have hneg : ∀ x ∈ (e : Set E), u x ≠ 0 := fun x hx ↦ (huU x (heU hx)).ne
  refine ⟨u, fun h0 ↦ hneg _ e.center_mem (by rw [h0]; rfl), hus,
    CompactlyContained.of_isCompact huc (husupp.trans ((image_mono ball_subset_closedBall).trans
      hRD)), huvan, husymm, ⟨U, hUo, heU, huU⟩, fun x hx ↦ subset_tsupport u (hneg x hx)⟩

/-- **Infinitely many independent witnesses** ([Hägg, Proposition 5]).  The witnesses of
`LeanestEllipse.sufficiency` can be chosen to form a linearly independent sequence. -/
theorem sufficiency_linearIndependent {D : Set E} (hD : IsOpen D) (e : Ellipsoid E)
    (heD : (e : Set E) ⊆ D) :
    ∃ u : ℕ → E → ℝ, LinearIndependent ℝ u ∧ ∀ n, u n ≠ 0 ∧ ContDiff ℝ (⊤ : ℕ∞) (u n) ∧
      tsupport (u n) ⋐ D ∧
      (∀ ω : E, ‖ω‖ = 1 → ∀ p : ℝ, LineMeets (e : Set E) ω p → radonTransform (u n) ω p = 0) ∧
      (∀ x, u n (e.center + x) = u n (e.center - x)) ∧
      (∃ U : Set E, IsOpen U ∧ (e : Set E) ⊆ U ∧ ∀ x ∈ U, u n x < 0) ∧
      (e : Set E) ⊆ tsupport (u n) := by
  obtain ⟨R, hR1, hRD⟩ := e.exists_one_lt_image_closedBall_subset hD heD
  -- radii `1 ≤ s 0 < s 1 < ⋯ < R`
  set s : ℕ → ℝ := fun k ↦ 1 + (R - 1) * (1 - 1 / (k + 2))
  have hs_mono : StrictMono s := by
    intro a b hab
    simp only [s]
    have ha : (0 : ℝ) < a + 2 := by positivity
    have hb : (a + 2 : ℝ) < b + 2 := by exact_mod_cast Nat.add_lt_add_right hab 2
    have : 1 / ((b : ℝ) + 2) < 1 / (a + 2) := one_div_lt_one_div_of_lt ha hb
    nlinarith
  have hs1 : ∀ k, 1 ≤ s k := fun k ↦ by
    simp only [s]
    have : 1 / ((k : ℝ) + 2) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
    nlinarith
  have hsR : ∀ k, s k < R := fun k ↦ by
    simp only [s]
    have : 0 < 1 / ((k : ℝ) + 2) := by positivity
    nlinarith
  choose u hus huc husupp huvan husymm U hUo hU huU using fun n : ℕ ↦
    exists_ellipse_witness e (hs1 (2 * n)) (hs_mono (Nat.lt_succ_self (2 * n)))
  have heU : ∀ n, (e : Set E) ⊆ U n := fun n ↦ (image_mono
    (closedBall_subset_closedBall (hs1 (2 * n)))).trans (hU n)
  have hneg : ∀ n, ∀ x ∈ (e : Set E), u n x ≠ 0 := fun n x hx ↦ (huU n x (heU n hx)).ne
  -- evaluation points `x m = c + A (s (2m) • v)` for a unit vector `v`
  have : Nontrivial E := Module.nontrivial_of_finrank_pos
    (by rw [(Fact.out : Module.finrank ℝ E = 2)]; norm_num)
  obtain ⟨v, hv⟩ := exists_norm_eq E zero_le_one
  set x : ℕ → E := fun m ↦ e.center + e.linearPart (s (2 * m) • v)
  refine ⟨u, linearIndependent_of_triangular_evaluations x (fun m ↦ ?_) (fun n m hnm ↦ ?_), fun n ↦
    ⟨fun h0 ↦ hneg n _ e.center_mem (by rw [h0]; rfl), hus n,
      CompactlyContained.of_isCompact (huc n) ((husupp n).trans
        ((image_mono ball_subset_closedBall).trans ((image_mono (closedBall_subset_closedBall
          (hsR (2 * n + 1)).le)).trans hRD))),
      huvan n, husymm n, ⟨U n, hUo n, heU n, huU n⟩, fun x hx ↦ subset_tsupport _ (hneg n x hx)⟩⟩
  · refine (huU m (x m) (hU m ⟨s (2 * m) • v, ?_, rfl⟩)).ne
    rw [mem_closedBall_zero_iff, norm_smul, hv, mul_one,
      Real.norm_of_nonneg (by linarith [hs1 (2 * m)])]
  · apply image_eq_zero_of_notMem_tsupport
    intro hmem
    obtain ⟨y, hy, hyx⟩ := husupp n hmem
    have hy' : y = s (2 * m) • v :=
      e.linearPart.injective (add_left_cancel (hyx.trans rfl))
    rw [hy', mem_ball_zero_iff, norm_smul, hv, mul_one,
      Real.norm_of_nonneg (by linarith [hs1 (2 * m)])] at hy
    have : s (2 * n + 1) < s (2 * m) := hs_mono (by omega)
    linarith

end LeanestEllipse
