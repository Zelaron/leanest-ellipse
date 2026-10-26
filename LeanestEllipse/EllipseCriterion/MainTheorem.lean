import LeanestEllipse.EllipseCriterion.Necessity
import LeanestEllipse.EllipseCriterion.Sufficiency
import LeanestEllipse.Analysis.Convex.CompactConvexHull
import LeanestEllipse.Analysis.Convex.HyperplaneHull
import LeanestEllipse.IntegralGeometry.Radon.LinearMap

/-!
# The ellipse criterion ([Hägg, Theorem 1 and Remark 2])

Let `D₀, D` be open convex sets in a Euclidean plane `E`.  The following are equivalent
(`LeanestEllipse.ellipse_criterion`):

1. (`SmoothNullExists D₀ D`) there is a nonzero `u ∈ C_c^∞(D)` whose Radon transform vanishes on
   every line meeting `D₀`;
2. (`IntegrableNullExists D₀ D`) there is a nonzero `u ∈ L¹` with support compactly contained in
   `D` whose Radon transform vanishes on almost every line meeting `D₀`;
3. (`EllipseSandwich D₀ D`) there is an ellipse `𝓔` with `closure D₀ ⊆ 𝓔 ⋐ D`.

Each condition forces `D₀ ⋐ D` (`LeanestEllipse.ellipse_criterion_compactlyContained`), and if
(3) holds with an ellipse `𝓔`, the function in (1) may be chosen real valued, centrally symmetric
about the center of `𝓔` and strictly negative on a neighbourhood of `𝓔`
(`LeanestEllipse.ellipse_criterion_witness`).

The criterion also holds for connected, non-collinear data sets `D₀`
([Hägg, Remark 2], `LeanestEllipse.ellipse_criterion_of_isConnected`).
-/

open MeasureTheory Set Metric
open scoped RealInnerProductSpace CompactlyContained

noncomputable section

namespace LeanestEllipse

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-! ### Condition (iii) implies condition (i) -/

section Sufficiency

variable [Fact (Module.finrank ℝ E = 2)]

/-- **The witness of [Hägg, Theorem 1]**: if `closure D₀ ⊆ 𝓔 ⋐ D` for an ellipse `𝓔`, there is a
nonzero real valued `u ∈ C_c^∞(D)`, centrally symmetric about the center of `𝓔` and strictly
negative on an open neighbourhood of `𝓔` (in particular `𝓔 ⊆ supp u`), whose Radon transform
vanishes on every line meeting `D₀` (indeed, on every line meeting `𝓔`). -/
theorem ellipse_criterion_witness {D₀ D : Set E} (hD : IsOpen D) (e : Ellipsoid E)
    (h₀ : closure D₀ ⊆ e) (h₁ : (e : Set E) ⋐ D) :
    ∃ u : E → ℝ, u ≠ 0 ∧ ContDiff ℝ (⊤ : ℕ∞) u ∧ tsupport u ⋐ D ∧
      RadonVanishesOn (fun x ↦ (u x : ℂ)) D₀ ∧
      (∀ ω : E, ‖ω‖ = 1 → ∀ p : ℝ, LineMeets (e : Set E) ω p → radonTransform u ω p = 0) ∧
      (∀ x, u (e.center + x) = u (e.center - x)) ∧
      (∃ U : Set E, IsOpen U ∧ (e : Set E) ⊆ U ∧ ∀ x ∈ U, u x < 0) ∧
      (e : Set E) ⊆ tsupport u := by
  obtain ⟨u, hu0, hs, hsupp, hvan, hsymm, hneg, hsub⟩ := sufficiency hD e h₁.subset
  refine ⟨u, hu0, hs, hsupp, fun ω hω p ⟨x, hx, hxp⟩ ↦ ?_, hvan, hsymm, hneg, hsub⟩
  rw [radonTransform_complex_ofReal, hvan ω hω p ⟨x, h₀ (subset_closure hx), hxp⟩,
    Complex.ofReal_zero]

/-- [Hägg, Theorem 1], (iii) ⟹ (i). -/
theorem smoothNullExists_of_ellipseSandwich {D₀ D : Set E} (hD : IsOpen D)
    (h : EllipseSandwich D₀ D) : SmoothNullExists D₀ D := by
  obtain ⟨e, h₀, h₁⟩ := h
  obtain ⟨u, hu0, hs, hsupp, hvan, -⟩ := ellipse_criterion_witness hD e h₀ h₁
  have htsupp : tsupport (fun x ↦ (u x : ℂ)) = tsupport u := by
    simp only [tsupport, Function.support, ne_eq, Complex.ofReal_eq_zero]
  refine ⟨fun x ↦ (u x : ℂ), fun h0 ↦ hu0 (funext fun x ↦ ?_),
    Complex.ofRealCLM.contDiff.comp hs, htsupp ▸ hsupp, hvan⟩
  simpa using congrFun h0 x

end Sufficiency

/-! ### Condition (i) implies condition (ii) -/

/-- [Hägg, Theorem 1], (i) ⟹ (ii): a compactly supported smooth function is integrable, and its
essential support is its support. -/
theorem integrableNullExists_of_smoothNullExists {D₀ D : Set E} (h : SmoothNullExists D₀ D) :
    IntegrableNullExists D₀ D := by
  obtain ⟨u, hu0, hs, hsupp, hvan⟩ := h
  have hc : Continuous u := hs.continuous
  have hcs : HasCompactSupport u := by
    have := hsupp.isCompact_closure
    rwa [(isClosed_tsupport u).closure_eq] at this
  refine ⟨u, hc.integrable_of_hasCompactSupport hcs, fun h0 ↦ hu0 ?_, ?_,
    hvan.radonVanishesAEOn⟩
  · exact (hc.ae_eq_iff_eq (μ := volume) continuous_zero).mp h0
  · rwa [hc.essSupport_eq_tsupport]

/-! ### Condition (ii) implies condition (iii) -/

omit [MeasurableSpace E] [BorelSpace E] in
/-- A nonempty open set contains an ellipse (a small closed disk). -/
theorem exists_ellipsoid_subset_of_isOpen {D : Set E} (hD : IsOpen D) {x : E} (hx : x ∈ D) :
    ∃ e : Ellipsoid E, (e : Set E) ⋐ D := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hD x hx
  refine ⟨Ellipsoid.closedBall x (half_pos hε), ?_⟩
  rw [Ellipsoid.coe_closedBall]
  exact CompactlyContained.of_isCompact (isCompact_closedBall x _)
    ((closedBall_subset_ball (half_lt_self hε)).trans hball)

section Necessity

variable [Fact (Module.finrank ℝ E = 2)]

/-- [Hägg, Theorem 1], (ii) ⟹ (iii), for an arbitrary data set `D₀` in terms of an open convex
set `K₀` meeting the same lines as `D₀` (up to null sets) and with `closure D₀ ⊆ closure K₀`. -/
theorem ellipseSandwich_of_integrableNullExists_of_subset {D₀ K₀ D : Set E} (hDo : IsOpen D)
    (hDc : Convex ℝ D) (hK₀o : IsOpen K₀) (hK₀c : Convex ℝ K₀) (hK₀ne : D₀.Nonempty → K₀.Nonempty)
    (hcl : closure D₀ ⊆ closure K₀)
    (hlines : ∀ ω : E, ∀ p : ℝ, LineMeets K₀ ω p → LineMeets D₀ ω p)
    (h : IntegrableNullExists D₀ D) : EllipseSandwich D₀ D := by
  obtain ⟨u, hu, hu0, hsupp, hvan⟩ := h
  set S := essSupport u volume
  have hSc : IsCompact S := by
    have := hsupp.isCompact_closure
    rwa [isClosed_essSupport.closure_eq] at this
  have hSD : S ⊆ D := hsupp.subset
  obtain ⟨x₀, hx₀⟩ : S.Nonempty := essSupport_nonempty_iff.mpr hu0
  rcases D₀.eq_empty_or_nonempty with rfl | hD₀ne
  · obtain ⟨e, he⟩ := exists_ellipsoid_subset_of_isOpen hDo (hSD hx₀)
    exact ⟨e, by simp, he⟩
  -- `K₁ = co(supp u)` is compact, convex and contained in `D`
  have hK₁ : IsCompact (convexHull ℝ S) := hSc.convexHull
  have hK₁D : convexHull ℝ S ⊆ D := convexHull_min hSD hDc
  have hvan₀ : RadonVanishesAEOn u K₀ := by
    filter_upwards [hvan] with z hz hmeet using hz (hlines _ _ hmeet)
  obtain ⟨e, he₀, he₁⟩ := exists_ellipsoid_of_radonVanishesAEOn hK₀c
    (by rw [hK₀o.interior_eq]; exact hK₀ne hD₀ne) hK₁ (convex_convexHull ℝ S) hu hu0
    (subset_convexHull ℝ S) hvan₀
  exact ⟨e, hcl.trans he₀, CompactlyContained.of_isCompact e.isCompact (he₁.trans hK₁D)⟩

/-- [Hägg, Theorem 1], (ii) ⟹ (iii). -/
theorem ellipseSandwich_of_integrableNullExists {D₀ D : Set E} (hD₀o : IsOpen D₀)
    (hD₀c : Convex ℝ D₀) (hDo : IsOpen D) (hDc : Convex ℝ D) (h : IntegrableNullExists D₀ D) :
    EllipseSandwich D₀ D :=
  ellipseSandwich_of_integrableNullExists_of_subset hDo hDc hD₀o hD₀c id subset_rfl
    (fun _ _ ↦ id) h

end Necessity

/-! ### The main theorem -/

section Main

variable [Fact (Module.finrank ℝ E = 2)]

/-- **The ellipse criterion** [Hägg, Theorem 1].  For open convex sets `D₀, D` in a Euclidean
plane, the following are equivalent:
1. there is a nonzero `u ∈ C_c^∞(D)` whose Radon transform vanishes on every line meeting `D₀`;
2. there is a nonzero `u ∈ L¹` with `supp u ⋐ D` whose Radon transform vanishes on almost every
   line meeting `D₀`;
3. there is an ellipse `𝓔` with `closure D₀ ⊆ 𝓔 ⋐ D`. -/
theorem ellipse_criterion {D₀ D : Set E} (hD₀o : IsOpen D₀) (hD₀c : Convex ℝ D₀)
    (hDo : IsOpen D) (hDc : Convex ℝ D) :
    List.TFAE [SmoothNullExists D₀ D, IntegrableNullExists D₀ D, EllipseSandwich D₀ D] := by
  tfae_have 1 → 2 := integrableNullExists_of_smoothNullExists
  tfae_have 2 → 3 := ellipseSandwich_of_integrableNullExists hD₀o hD₀c hDo hDc
  tfae_have 3 → 1 := smoothNullExists_of_ellipseSandwich hDo
  tfae_finish

/-- Each condition of the ellipse criterion forces `D₀ ⋐ D` [Hägg, Theorem 1]. -/
theorem ellipse_criterion_compactlyContained {D₀ D : Set E} (hD₀o : IsOpen D₀)
    (hD₀c : Convex ℝ D₀) (hDo : IsOpen D) (hDc : Convex ℝ D) (h : IntegrableNullExists D₀ D) :
    D₀ ⋐ D :=
  (ellipseSandwich_of_integrableNullExists hD₀o hD₀c hDo hDc h).compactlyContained

/-- **Connected data sets** [Hägg, Remark 2]: the ellipse criterion holds for a connected data set
`D₀` that is not contained in a line (and `D` open and convex). -/
theorem ellipse_criterion_of_isConnected {D₀ D : Set E} (hD₀ : IsConnected D₀)
    (hcol : ¬ Collinear ℝ D₀) (hDo : IsOpen D) (hDc : Convex ℝ D) :
    List.TFAE [SmoothNullExists D₀ D, IntegrableNullExists D₀ D, EllipseSandwich D₀ D] := by
  have hint : (interior (convexHull ℝ D₀)).Nonempty :=
    interior_convexHull_nonempty_of_not_collinear Fact.out hcol
  tfae_have 1 → 2 := integrableNullExists_of_smoothNullExists
  tfae_have 2 → 3 := ellipseSandwich_of_integrableNullExists_of_subset hDo hDc isOpen_interior
    (convex_interior_convexHull D₀) (fun _ ↦ hint)
    (closure_subset_closure_interior_convexHull hint) fun ω p ⟨x, hx, hxp⟩ ↦
      (hD₀.isPreconnected.exists_inner_eq_iff_convexHull ω p).mpr ⟨x, interior_subset hx, hxp⟩
  tfae_have 3 → 1 := smoothNullExists_of_ellipseSandwich hDo
  tfae_finish

end Main

end LeanestEllipse
