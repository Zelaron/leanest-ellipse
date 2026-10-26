import LeanestEllipse.EllipseCriterion.MainTheorem
import LeanestEllipse.EllipseCriterion.SquareGeometry

/-!
# The square threshold and the endpoint

The Radon-transform conclusions of Corollaries 12–13 and Remark 14 follow from the
ellipse criterion and the geometry in `SquareGeometry`. Equality of integrable functions
means equality almost everywhere, as in the paper.
-/

open MeasureTheory Set Metric
open scoped CompactlyContained

noncomputable section

namespace LeanestEllipse

private instance : Fact (Module.finrank ℝ ℂ = 2) := ⟨Complex.finrank_real_complex⟩

/-- The ellipse sandwich for two open squares is equivalent to the strict square threshold. -/
theorem ellipseSandwich_openSquare_iff {δ : ℝ} (hδ : 0 < δ) :
    EllipseSandwich (openSquare δ) (openSquare 1) ↔ δ < 1 / Real.sqrt 2 := by
  rw [← exists_ellipsoid_openSquare_iff hδ]
  exact ⟨fun ⟨e, h₀, h₁⟩ ↦ ⟨e, h₀, h₁.subset⟩,
    fun ⟨e, h₀, h₁⟩ ↦ ⟨e, h₀, CompactlyContained.of_isCompact e.isCompact h₁⟩⟩

/-- **Corollary 12**, smooth form: the sharp threshold for two concentric open squares. -/
theorem smoothNullExists_openSquare_iff {δ : ℝ} (hδ : 0 < δ) :
    SmoothNullExists (openSquare δ) (openSquare 1) ↔ δ < 1 / Real.sqrt 2 :=
  ((ellipse_criterion (isOpen_openSquare δ) (convex_openSquare δ)
    (isOpen_openSquare 1) (convex_openSquare 1)).out 1 3).trans
      (ellipseSandwich_openSquare_iff hδ)

/-- **Corollary 12**, integrable form: the same sharp threshold with essential support
compactly contained in the open outer square and almost-everywhere vanishing data. -/
theorem integrableNullExists_openSquare_iff {δ : ℝ} (hδ : 0 < δ) :
    IntegrableNullExists (openSquare δ) (openSquare 1) ↔ δ < 1 / Real.sqrt 2 :=
  ((ellipse_criterion (isOpen_openSquare δ) (convex_openSquare δ)
    (isOpen_openSquare 1) (convex_openSquare 1)).out 2 3).trans
      (ellipseSandwich_openSquare_iff hδ)

/-- The closed square has nonempty interior when its half-side is positive. -/
theorem interior_closedSquare_nonempty {δ : ℝ} (hδ : 0 < δ) :
    (interior (closedSquare δ)).Nonempty :=
  (openSquare_nonempty hδ).mono
    ((isOpen_openSquare δ).subset_interior_iff.mpr (openSquare_subset_closedSquare δ))

/-- **Corollary 13**: above the threshold, closed outer support and vanishing data on lines
meeting the closed inner square force an integrable function to be zero almost everywhere. -/
theorem ae_eq_zero_of_radonVanishesAEOn_closedSquare {δ : ℝ}
    (hδ : 1 / Real.sqrt 2 < δ) {u : ℂ → ℂ} (hu : Integrable u)
    (hsupp : essSupport u volume ⊆ closedSquare 1)
    (hvan : RadonVanishesAEOn u (closedSquare δ)) : u =ᵐ[volume] 0 := by
  by_contra hu0
  have hδ0 : 0 < δ := (by positivity : (0 : ℝ) < 1 / Real.sqrt 2).trans hδ
  obtain ⟨e, h₀, h₁⟩ := exists_ellipsoid_of_radonVanishesAEOn (convex_closedSquare δ)
    (interior_closedSquare_nonempty hδ0) (isCompact_closedSquare 1) (convex_closedSquare 1)
    hu hu0 hsupp hvan
  exact hδ.not_ge ((exists_ellipsoid_closedSquare_iff hδ0.le).mp
    ⟨e, (subset_closure.trans h₀), h₁⟩)

/-- The continuous version of Corollary 13, with ordinary closed support and pointwise data. -/
theorem eq_zero_of_radonVanishesOn_closedSquare {δ : ℝ} (hδ : 1 / Real.sqrt 2 < δ)
    {u : ℂ → ℂ} (hu : Continuous u) (hsupp : tsupport u ⊆ closedSquare 1)
    (hvan : RadonVanishesOn u (closedSquare δ)) : u = 0 := by
  have hc : HasCompactSupport u :=
    (isCompact_closedSquare 1).of_isClosed_subset (isClosed_tsupport _) hsupp
  apply (hu.ae_eq_iff_eq (μ := volume) continuous_zero).mp
  exact ae_eq_zero_of_radonVanishesAEOn_closedSquare hδ (hu.integrable_of_hasCompactSupport hc)
    (by rwa [hu.essSupport_eq_tsupport]) hvan.radonVanishesAEOn

/-- **Remark 14**, the compact-support endpoint: no smooth null function exists in the
open outer square at `δ = 1 / √2`. -/
theorem not_smoothNullExists_openSquare_endpoint :
    ¬ SmoothNullExists (openSquare (1 / Real.sqrt 2)) (openSquare 1) := by
  rw [smoothNullExists_openSquare_iff (by positivity)]
  exact lt_irrefl _

/-- **Remark 14**, the integrable compact-support endpoint. The closed-support endpoint
is a different question, which is left open in the paper. -/
theorem not_integrableNullExists_openSquare_endpoint :
    ¬ IntegrableNullExists (openSquare (1 / Real.sqrt 2)) (openSquare 1) := by
  rw [integrableNullExists_openSquare_iff (by positivity)]
  exact lt_irrefl _

/-- **Remark 14**: the unique geometric sandwich at the endpoint meets the boundary of
the outer square, so Proposition 5 cannot be applied inside that open square. -/
theorem unitDisk_not_subset_openSquare :
    ¬ Metric.closedBall (0 : ℂ) 1 ⊆ openSquare 1 := by
  intro h
  have h1 := h (show (1 : ℂ) ∈ Metric.closedBall 0 1 by simp)
  have := h1.1.2
  norm_num at this

end LeanestEllipse
