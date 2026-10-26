import LeanestEllipse.EllipseCriterion.ConnectedExamples
import Mathlib.Analysis.Convex.GaugeRescale
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.Convex.Strict.Extreme

/-!
# Convex polygonal boundaries in the ellipse criterion

The boundary of a bounded convex body with nonempty interior is connected in real
dimension greater than one: an ambient gauge-rescaling homeomorphism sends it to the unit
sphere. For a compact convex set, Krein–Milman gives the stronger identity that the set is
the convex hull of its boundary; a nonempty interior then prevents that boundary from
being collinear.

For general polygons, the union of consecutive closed segments is connected because
neighboring segments share an endpoint. This union contains every vertex, so it cannot be
collinear if the vertices are not. The connected-set ellipse criterion therefore applies
to every nondegenerate closed polygonal chain, including nonconvex polygons, and also to
every convex polygonal boundary represented by a finite convex hull.
-/

open Set Metric Bornology

noncomputable section

variable {E : Type*}

section NormedSpace

variable [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
/-- Extreme points lie on the frontier in a nontrivial real normed space. -/
theorem extremePoints_subset_frontier [Nontrivial E] (K : Set E) :
    K.extremePoints ℝ ⊆ frontier K := by
  intro x hx
  refine ⟨subset_closure (extremePoints_subset hx), ?_⟩
  exact fun hxi ↦ (disjoint_left.mp (disjoint_interior_extremePoints K)) hxi hx

/-- A compact convex set in a nontrivial finite-dimensional real normed space is the convex
hull of its frontier. -/
theorem IsCompact.convexHull_frontier_eq [Nontrivial E] {K : Set E}
    (hK : IsCompact K) (hconv : Convex ℝ K) : _root_.convexHull ℝ (frontier K) = K := by
  have hfront : frontier K ⊆ K := by
    simpa only [hK.isClosed.closure_eq] using (frontier_subset_closure : frontier K ⊆ closure K)
  have hfrontc : IsCompact (frontier K) := hK.of_isClosed_subset isClosed_frontier hfront
  apply subset_antisymm (convexHull_min hfront hconv)
  calc
    K = closure (_root_.convexHull ℝ (K.extremePoints ℝ)) :=
      (closure_convexHull_extremePoints hK hconv).symm
    _ ⊆ _root_.convexHull ℝ (frontier K) :=
      closure_minimal (convexHull_mono (extremePoints_subset_frontier K))
        hfrontc.convexHull.isClosed

/-- The frontier of a bounded convex body with nonempty interior is connected in real
dimension greater than one. -/
theorem isConnected_frontier_of_convex (hE : 1 < Module.finrank ℝ E) {K : Set E}
    (hconv : Convex ℝ K) (hint : (interior K).Nonempty) (hbound : IsBounded K) :
    IsConnected (frontier K) := by
  obtain ⟨h, -, -, hfront⟩ :=
    exists_homeomorph_image_interior_closure_frontier_eq_unitBall hconv hint hbound
  have hconn : IsConnected (sphere (0 : E) 1) :=
    LeanestEllipse.isConnected_sphere_of_one_lt_finrank hE 0 (by norm_num)
  rw [← hfront, h.isConnected_image] at hconn
  exact hconn

/-- The frontier of a compact convex body with nonempty interior is not contained in a
line when the ambient real dimension exceeds one. -/
theorem not_collinear_frontier_of_isCompact (hE : 1 < Module.finrank ℝ E) {K : Set E}
    (hK : IsCompact K) (hconv : Convex ℝ K) (hint : (interior K).Nonempty) :
    ¬ Collinear ℝ (frontier K) := by
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (lt_trans zero_lt_one hE)
  have hinter : (interior (convexHull ℝ (frontier K))).Nonempty := by
    rwa [hK.convexHull_frontier_eq hconv]
  have hspan : affineSpan ℝ (frontier K) = ⊤ :=
    interior_convexHull_nonempty_iff_affineSpan_eq_top.mp hinter
  have hvspan := AffineSubspace.vectorSpan_eq_top_of_affineSpan_eq_top ℝ E E hspan
  intro hcol
  have hdim := hcol.finrank_le_one
  rw [hvspan, finrank_top] at hdim
  omega

end NormedSpace

namespace LeanestEllipse

section PolygonalChain

variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The union of the first `n` consecutive closed segments of a vertex sequence.
When `v n = v 0`, this is the closed polygonal chain with those vertices. -/
def polygonalChain (v : ℕ → E) (n : ℕ) : Set E :=
  ⋃ i ∈ Iio n, segment ℝ (v i) (v (i + 1))

/-- A nonempty finite chain of consecutive closed segments is connected. -/
theorem isConnected_polygonalChain (v : ℕ → E) {n : ℕ} (hn : 0 < n) :
    IsConnected (polygonalChain v n) := by
  unfold polygonalChain
  refine IsConnected.biUnion_of_chain ⟨0, hn⟩ ordConnected_Iio
    (fun i _ ↦ (convex_segment (v i) (v (i + 1))).isConnected
      ⟨v i, left_mem_segment ℝ _ _⟩) ?_
  intro i _ _
  exact ⟨v (i + 1), right_mem_segment ℝ _ _, left_mem_segment ℝ _ _⟩

/-- All vertices, including both endpoints, belong to a nonempty polygonal chain. -/
theorem vertices_subset_polygonalChain (v : ℕ → E) {n : ℕ} (hn : 0 < n) :
    v '' Iic n ⊆ polygonalChain v n := by
  rintro _ ⟨i, hi, rfl⟩
  rcases lt_or_eq_of_le (show i ≤ n from hi) with hi | hi
  · exact mem_iUnion₂.mpr ⟨i, hi, left_mem_segment ℝ _ _⟩
  · subst i
    refine mem_iUnion₂.mpr ⟨n - 1, (show n - 1 < n by omega), ?_⟩
    rw [show n - 1 + 1 = n by omega]
    exact right_mem_segment ℝ _ _

/-- Noncollinear vertices prevent their polygonal chain from being collinear. -/
theorem not_collinear_polygonalChain (v : ℕ → E) {n : ℕ} (hn : 0 < n)
    (hcol : ¬ Collinear ℝ (v '' Iic n)) : ¬ Collinear ℝ (polygonalChain v n) :=
  fun h ↦ hcol (Collinear.subset (vertices_subset_polygonalChain v hn) h)

end PolygonalChain

section Plane

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [Fact (Module.finrank ℝ E = 2)]

/-- The ellipse criterion applies to the boundary of any planar compact convex body with
nonempty interior. -/
theorem ellipse_criterion_convex_boundary {K : Set E} (hK : IsCompact K)
    (hconv : Convex ℝ K) (hint : (interior K).Nonempty)
    {D : Set E} (hDo : IsOpen D) (hDc : Convex ℝ D) :
    List.TFAE [SmoothNullExists (frontier K) D, IntegrableNullExists (frontier K) D,
      EllipseSandwich (frontier K) D] := by
  have hE : 1 < Module.finrank ℝ E := by
    rw [(Fact.out : Module.finrank ℝ E = 2)]
    norm_num
  exact ellipse_criterion_of_isConnected
    (isConnected_frontier_of_convex hE hconv hint hK.isBounded)
    (not_collinear_frontier_of_isCompact hE hK hconv hint) hDo hDc

/-- **Convex polygonal data sets** [Hägg, Remark 2]: the ellipse criterion applies to the
boundary of the convex hull of any finite noncollinear set of vertices. -/
theorem ellipse_criterion_polygon_boundary {S : Set E} (hS : S.Finite)
    (hcol : ¬ Collinear ℝ S) {D : Set E} (hDo : IsOpen D) (hDc : Convex ℝ D) :
    List.TFAE [SmoothNullExists (frontier (convexHull ℝ S)) D,
      IntegrableNullExists (frontier (convexHull ℝ S)) D,
      EllipseSandwich (frontier (convexHull ℝ S)) D] := by
  have hK : IsCompact (convexHull ℝ S) := hS.isCompact.convexHull
  have hint : (interior (convexHull ℝ S)).Nonempty :=
    interior_convexHull_nonempty_of_not_collinear Fact.out hcol
  exact ellipse_criterion_convex_boundary hK (convex_convexHull ℝ S) hint hDo hDc

/-- **Polygonal data sets** [Hägg, Remark 2]: the ellipse criterion applies to every finite
polygonal chain with noncollinear vertices. In particular this includes every nondegenerate
closed polygon, without any convexity requirement. -/
theorem ellipse_criterion_polygonalChain (v : ℕ → E) (n : ℕ)
    (hcol : ¬ Collinear ℝ (v '' Iic n)) {D : Set E} (hDo : IsOpen D) (hDc : Convex ℝ D) :
    List.TFAE [SmoothNullExists (polygonalChain v n) D,
      IntegrableNullExists (polygonalChain v n) D, EllipseSandwich (polygonalChain v n) D] := by
  have hn : 0 < n := by
    by_contra hn
    have hn0 : n = 0 := by omega
    subst n
    apply hcol
    apply Collinear.subset (s₂ := {v 0}) ?_ (collinear_singleton ℝ (v 0))
    rintro _ ⟨i, hi, rfl⟩
    have hi0 : i = 0 := Nat.eq_zero_of_le_zero hi
    simp [hi0]
  exact ellipse_criterion_of_isConnected (isConnected_polygonalChain v hn)
    (not_collinear_polygonalChain v hn hcol) hDo hDc

end Plane

end LeanestEllipse
