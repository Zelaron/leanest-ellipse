import LeanestEllipse.IntegralGeometry.Radon.Basic
import LeanestEllipse.Analysis.Convex.Ellipsoid
import LeanestEllipse.MeasureTheory.Function.EssentialSupport
import LeanestEllipse.Topology.CompactlyContained
import Mathlib.MeasureTheory.Constructions.HaarToSphere

/-!
# The three conditions of the ellipse criterion ([Hägg, Theorem 1])

Throughout, `E` is a finite dimensional real inner product space (in the paper `E = ℝ²`), lines
(hyperplanes) are `L(ω, p) = {x | ⟪x, ω⟫ = p}` for unit vectors `ω`, and the Radon transform is
`radonTransform` from `LeanestEllipse.IntegralGeometry.Radon.Basic`.
"Almost every line" refers to the product of the surface measure
`volume.toSphere` of the unit sphere (arc length `dω` in the plane) and Lebesgue measure `dp`.

* `LeanestEllipse.SmoothNullExists D₀ D` — condition (i): a nonzero `u ∈ C_c^∞(D)` whose Radon
  transform vanishes on every line meeting `D₀`;
* `LeanestEllipse.IntegrableNullExists D₀ D` — condition (ii): a nonzero `u ∈ L¹` with
  (essential) support compactly contained in `D`, whose Radon transform vanishes for almost every
  line meeting `D₀`;
* `LeanestEllipse.EllipseSandwich D₀ D` — condition (iii): an ellipse `E` with
  `closure D₀ ⊆ E ⋐ D`.
-/

open MeasureTheory Set Metric
open scoped RealInnerProductSpace CompactlyContained

noncomputable section

namespace LeanestEllipse

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The line (hyperplane) `L(ω, p) = {x | ⟪x, ω⟫ = p}` meets `D₀`. -/
def LineMeets (D₀ : Set E) (ω : E) (p : ℝ) : Prop := ∃ x ∈ D₀, ⟪x, ω⟫ = p

/-- The Radon transform of `u` vanishes on every line meeting `D₀` ([Hägg, (1.4)]). -/
def RadonVanishesOn (u : E → ℂ) (D₀ : Set E) : Prop :=
  ∀ ω : E, ‖ω‖ = 1 → ∀ p : ℝ, LineMeets D₀ ω p → radonTransform u ω p = 0

/-- The Radon transform of `u` vanishes for almost every line `(ω, p) ∈ 𝕊 × ℝ` meeting `D₀`
([Hägg, (1.5)]); `𝕊` carries its surface measure. -/
def RadonVanishesAEOn (u : E → ℂ) (D₀ : Set E) : Prop :=
  ∀ᵐ z : sphere (0 : E) 1 × ℝ ∂((volume : Measure E).toSphere.prod volume),
    LineMeets D₀ (z.1 : E) z.2 → radonTransform u (z.1 : E) z.2 = 0

/-- **Condition (i)** of [Hägg, Theorem 1]: there is a nonzero `u ∈ C_c^∞(D)` (smooth, with
`supp u ⋐ D`) whose Radon transform vanishes on every line meeting `D₀`. -/
def SmoothNullExists (D₀ D : Set E) : Prop :=
  ∃ u : E → ℂ, u ≠ 0 ∧ ContDiff ℝ (⊤ : ℕ∞) u ∧ tsupport u ⋐ D ∧ RadonVanishesOn u D₀

/-- **Condition (ii)** of [Hägg, Theorem 1]: there is a nonzero `u ∈ L¹` (i.e. not a.e. zero)
with essential support compactly contained in `D`, whose Radon transform vanishes for almost
every line meeting `D₀`. -/
def IntegrableNullExists (D₀ D : Set E) : Prop :=
  ∃ u : E → ℂ, Integrable u ∧ ¬ u =ᵐ[volume] 0 ∧ essSupport u volume ⋐ D ∧
    RadonVanishesAEOn u D₀

/-- **Condition (iii)** of [Hägg, Theorem 1]: there is an ellipse (ellipsoid) `e` with
`closure D₀ ⊆ e ⋐ D`. -/
def EllipseSandwich (D₀ D : Set E) : Prop :=
  ∃ e : Ellipsoid E, closure D₀ ⊆ e ∧ (e : Set E) ⋐ D

theorem radonVanishesOn_mono {u : E → ℂ} {D₀ D₁ : Set E} (h : RadonVanishesOn u D₁)
    (hD : D₀ ⊆ D₁) : RadonVanishesOn u D₀ := fun ω hω p ⟨x, hx, hxp⟩ ↦ h ω hω p ⟨x, hD hx, hxp⟩

theorem radonVanishesAEOn_mono {u : E → ℂ} {D₀ D₁ : Set E} (h : RadonVanishesAEOn u D₁)
    (hD : D₀ ⊆ D₁) : RadonVanishesAEOn u D₀ := by
  filter_upwards [h] with z hz ⟨x, hx, hxp⟩ using hz ⟨x, hD hx, hxp⟩

/-- The a.e. condition is insensitive to changing `u` on a null set in each direction:
here, a pointwise vanishing condition implies the almost-everywhere one. -/
theorem RadonVanishesOn.radonVanishesAEOn {u : E → ℂ} {D₀ : Set E} (h : RadonVanishesOn u D₀) :
    RadonVanishesAEOn u D₀ :=
  Filter.Eventually.of_forall fun z hz ↦ h z.1 (by simp) z.2 hz

omit [MeasurableSpace E] [BorelSpace E] in
theorem EllipseSandwich.compactlyContained {D₀ D : Set E} (h : EllipseSandwich D₀ D) :
    D₀ ⋐ D := by
  obtain ⟨e, h₀, h₁⟩ := h
  exact ⟨e.isCompact.of_isClosed_subset isClosed_closure h₀, h₀.trans h₁.subset⟩

end LeanestEllipse
