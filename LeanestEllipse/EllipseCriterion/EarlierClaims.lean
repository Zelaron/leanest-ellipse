import LeanestEllipse.EllipseCriterion.SquareCorollaries
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Counterexamples to the earlier universal claims (Remark 15)

The propositions below spell out the planar universal nonuniqueness assertions as stated
in the paper. The counterexamples are concentric squares with half-side ratio `3/4`.
The inner and outer domains are nonempty, bounded, open, convex, centrally symmetric about
the same point, and compactly nested. For the closed-support assertion the inner set is closed.

The final example isolates the logical distinction between convergence of positive minima
to zero and their eventual equality to zero. It makes no assertion about the numerical values
of the variational minima in the cited paper.
-/

open MeasureTheory Set Bornology Filter
open scoped CompactlyContained Topology

noncomputable section

namespace LeanestEllipse

/-- Conjecture 1.2 as quoted in Remark 15: universal smooth nonuniqueness with support in
the closure of a bounded convex domain, for every closed inner set compactly contained in it. -/
def BomanClosedSupportConjecture : Prop :=
  ∀ D K : Set ℂ, IsOpen D → Convex ℝ D → IsBounded D → D.Nonempty →
    IsClosed K → K ⋐ D →
    ∃ u : ℂ → ℂ, u ≠ 0 ∧ ContDiff ℝ (⊤ : ℕ∞) u ∧
      tsupport u ⊆ closure D ∧ RadonVanishesOn u K

/-- The universal centrally symmetric planar interior assertion discussed in Remark 15
(Theorem 40.1). Both domains have a common center and satisfy strict compact containment. -/
def BomanSymmetricInteriorAssertion : Prop :=
  ∀ D₀ D : Set ℂ, IsOpen D₀ → Convex ℝ D₀ → IsBounded D₀ → D₀.Nonempty →
    IsOpen D → Convex ℝ D → IsBounded D → D.Nonempty → D₀ ⋐ D →
    (∃ c : ℂ, (∀ z, c + z ∈ D₀ ↔ c - z ∈ D₀) ∧
      (∀ z, c + z ∈ D ↔ c - z ∈ D)) → SmoothNullExists D₀ D

/-- Every concentric closed inner square of half-side less than one is compactly contained
in the unit open square. -/
theorem closedSquare_compactlyContained_openSquare {δ : ℝ} (hδ : δ < 1) :
    closedSquare δ ⋐ openSquare 1 := by
  refine CompactlyContained.of_isCompact (isCompact_closedSquare δ) ?_
  intro z hz
  constructor <;> constructor <;> linarith [hz.1.1, hz.1.2, hz.2.1, hz.2.2]

/-- The analogous compact containment for the open inner square. -/
theorem openSquare_compactlyContained_openSquare {δ : ℝ} (hδ : δ < 1) :
    openSquare δ ⋐ openSquare 1 :=
  (closedSquare_compactlyContained_openSquare hδ).mono_left
    (openSquare_subset_closedSquare δ)

/-- An open square is centrally symmetric about the origin. -/
theorem openSquare_centrallySymmetric (r : ℝ) (z : ℂ) :
    (0 : ℂ) + z ∈ openSquare r ↔ (0 : ℂ) - z ∈ openSquare r := by
  simp only [zero_add, zero_sub, mem_openSquare, Complex.neg_re, Complex.neg_im, mem_Ioo]
  constructor <;> rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ <;>
    constructor <;> constructor <;> linarith

/-- The explicit rational ratio `3/4` lies strictly above the square threshold. -/
theorem one_div_sqrt_two_lt_three_quarters : (1 : ℝ) / Real.sqrt 2 < 3 / 4 := by
  rw [div_lt_iff₀ (Real.sqrt_pos.mpr (by norm_num))]
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg (2 : ℝ)]

/-- **Remark 15**, the closed-support counterexample, for every ratio between the threshold
and one. In fact every continuous function satisfying the support and data conditions is zero. -/
theorem closedSquare_counterexample {δ : ℝ} (hδ : 1 / Real.sqrt 2 < δ) (hδ1 : δ < 1) :
    closedSquare δ ⋐ openSquare 1 ∧
      ¬ ∃ u : ℂ → ℂ, u ≠ 0 ∧ ContDiff ℝ (⊤ : ℕ∞) u ∧
        tsupport u ⊆ closure (openSquare 1) ∧ RadonVanishesOn u (closedSquare δ) := by
  refine ⟨closedSquare_compactlyContained_openSquare hδ1, ?_⟩
  rintro ⟨u, hu0, hu, hsupp, hvan⟩
  rw [closure_openSquare zero_lt_one] at hsupp
  exact hu0 (eq_zero_of_radonVanishesOn_closedSquare hδ hu.continuous hsupp hvan)

/-- **Remark 15**: Conjecture 1.2, in the planar form quoted in the paper, is false. -/
theorem not_bomanClosedSupportConjecture : ¬ BomanClosedSupportConjecture := by
  intro h
  have hc := closedSquare_counterexample one_div_sqrt_two_lt_three_quarters (by norm_num)
  exact hc.2 (h (openSquare 1) (closedSquare (3 / 4)) (isOpen_openSquare 1)
    (convex_openSquare 1) (isBounded_openSquare 1) (openSquare_nonempty zero_lt_one)
    (isClosed_closedSquare _) hc.1)

/-- **Remark 15**: the universal centrally symmetric planar assertion is false. The
counterexample satisfies boundedness, openness, convexity, nonemptiness and compact nesting. -/
theorem not_bomanSymmetricInteriorAssertion : ¬ BomanSymmetricInteriorAssertion := by
  intro h
  have hn := h (openSquare (3 / 4)) (openSquare 1) (isOpen_openSquare _)
    (convex_openSquare _) (isBounded_openSquare _) (openSquare_nonempty (by norm_num))
    (isOpen_openSquare _) (convex_openSquare _) (isBounded_openSquare _)
    (openSquare_nonempty zero_lt_one) (openSquare_compactlyContained_openSquare (by norm_num))
    ⟨0, openSquare_centrallySymmetric _, openSquare_centrallySymmetric _⟩
  exact one_div_sqrt_two_lt_three_quarters.not_gt
    ((smoothNullExists_openSquare_iff (by norm_num)).mp hn)

/-- **Remark 15**, the limit versus attainment distinction: a strictly positive sequence
can tend to zero without ever being zero, and hence without being eventually zero. -/
theorem exists_positive_tendsto_zero_not_eventually_zero :
    ∃ μ : ℕ → ℝ, (∀ n, 0 < μ n) ∧ Tendsto μ atTop (𝓝 0) ∧
      ¬ ∀ᶠ n in atTop, μ n = 0 := by
  refine ⟨fun n ↦ 1 / ((n : ℝ) + 1), fun n ↦ by positivity,
    tendsto_one_div_add_atTop_nhds_zero_nat, ?_⟩
  intro h
  obtain ⟨n, hn⟩ := h.exists
  exact (by positivity : (0 : ℝ) < 1 / ((n : ℝ) + 1)).ne' hn

end LeanestEllipse
