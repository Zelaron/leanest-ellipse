import LeanestEllipse.IntegralGeometry.Radon.Basic
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import LeanestEllipse.IntegralGeometry.Radon.Backprojection
import LeanestEllipse.IntegralGeometry.Radon.Inversion
import LeanestEllipse.Analysis.InnerProductSpace.Laplacian
import LeanestEllipse.EllipseCriterion.Defs

/-!
# Point data and local inversion ([Hägg, Section 7, "Further questions"])

"If the inner set is a single point `{x_*} ⊂ D`, any nonzero smooth function `g` supported in a
sufficiently small ball centered at `x_*` and satisfying `g(2x_* - x) = -g(x)` has zero integral
over every line through `x_*`."

* `radonTransform_eq_zero_of_odd_about` (in `LeanestEllipse.IntegralGeometry.Radon.Basic`):
  the Radon transform of a function odd about
  `c` vanishes on every hyperplane through `c` (any dimension).
* `LeanestEllipse.exists_smooth_odd_radonTransform_eq_zero_through_point`: such nonzero smooth
  functions exist, with compact support in any prescribed open neighbourhood of the point; so the
  one-point data set `{x_*}` always exhibits nonuniqueness, with no ellipse involved.
* `LeanestEllipse.eqOn_zero_of_radonVanishesOn_of_odd_finrank`: odd-dimensional local
  uniqueness, using the proved Radon inversion formula for smooth compactly supported functions.
* `LeanestEllipse.eqOn_zero_of_radonVanishesOn_of_local_inversion`: the dimension-independent
  locality implication of any exact reconstruction by an iterated negative Laplacian.
-/

open MeasureTheory Set Metric
open scoped RealInnerProductSpace

noncomputable section

namespace LeanestEllipse

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **Nonuniqueness for a one-point data set** ([Hägg, Section 7]).  For every point `x₀` of an
open set `D` there is a nonzero real smooth function with compact support in `D`, odd about
`x₀`, whose Radon transform vanishes on every line (hyperplane) through `x₀`. -/
theorem exists_smooth_odd_radonTransform_eq_zero_through_point [Nontrivial E] {D : Set E}
    (hD : IsOpen D) {x₀ : E} (hx₀ : x₀ ∈ D) :
    ∃ g : E → ℝ, g ≠ 0 ∧ ContDiff ℝ (⊤ : ℕ∞) g ∧ HasCompactSupport g ∧ tsupport g ⊆ D ∧
      (∀ x, g (2 • x₀ - x) = -g x) ∧
      ∀ ω : E, ‖ω‖ = 1 → ∀ p : ℝ, (∃ x ∈ ({x₀} : Set E), ⟪x, ω⟫ = p) →
        radonTransform g ω p = 0 := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hD x₀ hx₀
  obtain ⟨v, hv⟩ := exists_norm_eq E (half_pos hr).le
  set a := x₀ + v
  let φ : ContDiffBump a := ⟨r / 8, r / 4, by positivity, by linarith⟩
  set g : E → ℝ := fun x ↦ φ x - φ (2 • x₀ - x) with hg
  have hrefl : ∀ x : E, 2 • x₀ - (2 • x₀ - x) = x := fun x ↦ sub_sub_cancel _ _
  have hodd : ∀ x, g (2 • x₀ - x) = -g x := by
    intro x
    simp only [g, hrefl]
    ring
  -- support considerations
  have hsupp : Function.support g ⊆ closedBall x₀ (3 * r / 4) := by
    intro x hx
    have : φ x ≠ 0 ∨ φ (2 • x₀ - x) ≠ 0 := by
      by_contra h
      push Not at h
      exact hx (by simp [g, h.1, h.2])
    rw [mem_closedBall, dist_eq_norm]
    rcases this with h | h
    · have hx' : x ∈ ball a (r / 4) := by rw [← φ.support_eq]; exact h
      rw [mem_ball, dist_eq_norm] at hx'
      calc ‖x - x₀‖ = ‖(x - a) + v‖ := by simp only [a]; congr 1; abel
        _ ≤ ‖x - a‖ + ‖v‖ := norm_add_le _ _
        _ ≤ 3 * r / 4 := by rw [hv]; linarith
    · have hx' : 2 • x₀ - x ∈ ball a (r / 4) := by rw [← φ.support_eq]; exact h
      rw [mem_ball, dist_eq_norm] at hx'
      calc ‖x - x₀‖ = ‖(2 • x₀ - x - a) + v‖ := by
            rw [← norm_neg]; simp only [a, two_smul]; congr 1; abel
        _ ≤ ‖2 • x₀ - x - a‖ + ‖v‖ := norm_add_le _ _
        _ ≤ 3 * r / 4 := by rw [hv]; linarith
  have htsupp : tsupport g ⊆ closedBall x₀ (3 * r / 4) :=
    closure_minimal hsupp isClosed_closedBall
  refine ⟨g, ?_, ?_, ?_, ?_, hodd, ?_⟩
  · -- `g a = 1`
    intro h0
    have hga : g a = 0 := by rw [h0]; rfl
    have h1 : φ a = 1 := φ.one_of_mem_closedBall (by
      simp only [mem_closedBall, dist_self]
      positivity)
    have h2 : φ (2 • x₀ - a) = 0 := by
      apply Function.notMem_support.mp
      rw [φ.support_eq, mem_ball, dist_eq_norm, not_lt]
      have : 2 • x₀ - a - a = -((2 : ℝ) • v) := by simp only [a, two_smul]; abel
      rw [this, norm_neg, norm_smul, hv, Real.norm_two]
      change r / 4 ≤ 2 * (r / 2)
      linarith
    simp [g, h1, h2] at hga
  · exact φ.contDiff.sub (φ.contDiff.comp (contDiff_const.sub contDiff_id))
  · exact (isCompact_closedBall x₀ (3 * r / 4)).of_isClosed_subset (isClosed_tsupport _) htsupp
  · exact htsupp.trans ((closedBall_subset_ball (by linarith)).trans hball)
  · rintro ω hω p ⟨x, hx, rfl⟩
    rw [mem_singleton_iff] at hx
    subst hx
    exact radonTransform_eq_zero_of_odd_about hodd hω

/-- **Section 7**, vanishing data give zero backprojection on the inner set in every dimension. -/
theorem RadonVanishesOn.backprojection_eqOn_zero {u : E → ℂ} {D₀ : Set E}
    (h : RadonVanishesOn u D₀) : Set.EqOn (radonBackprojection (radonTransform u)) 0 D₀ :=
  radonBackprojection_eqOn_zero h

/-- **Section 7**, the consequence of the cited local inversion formula: if reconstruction
uses a power of the negative Laplacian of backprojection, vanishing hyperplane data on an open
set force `u` to vanish there. For the classical odd-dimensional formula take
`k = (n - 1) / 2` and its normalization constant `κ`. The inversion identity is assumed here;
the locality implication is proved without additional smoothness or dimensional restrictions. -/
theorem eqOn_zero_of_radonVanishesOn_of_local_inversion {u : E → ℂ} {D₀ : Set E}
    (hD₀ : IsOpen D₀) (hvan : RadonVanishesOn u D₀) (k : ℕ) (κ : ℝ)
    (hinv : ∀ x, u x = κ •
      ((fun g : E → ℂ ↦ -Laplacian.laplacian g)^[k]
        (radonBackprojection (radonTransform u))) x) : Set.EqOn u 0 D₀ := by
  intro x hx
  rw [hinv x, hvan.backprojection_eqOn_zero.iterate_neg_laplacian hD₀ k hx]
  simp

/-- **Odd-dimensional local uniqueness** [Hägg, Section 7]. A smooth compactly supported
function whose Radon transform vanishes on all hyperplanes meeting an open set vanishes
on that open set. The inversion identity is proved, rather than assumed. -/
theorem eqOn_zero_of_radonVanishesOn_of_odd_finrank {u : E → ℂ} {D₀ : Set E}
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (hc : HasCompactSupport u)
    (hD₀ : IsOpen D₀) (hvan : RadonVanishesOn u D₀)
    (k : ℕ) (hdim : Module.finrank ℝ E = 2 * k + 1) : Set.EqOn u 0 D₀ :=
  eqOn_zero_of_radonVanishesOn_of_local_inversion hD₀ hvan k
    (2 * (2 * Real.pi) ^ (2 * k))⁻¹ (fun x ↦ radon_inversion_odd hu hc k hdim x)

end LeanestEllipse
