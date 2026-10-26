import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Normed.Group.Pointwise
import Mathlib.Topology.Order.Compact

/-!
# Support functions and projection endpoints

For a set `K` in a real inner product space `E` and a direction `ω : E` we define

* `supportFunction K ω = sup_{x ∈ K} ⟪x, ω⟫`, the *support function* of `K`;
* `lowerSupportFunction K ω = inf_{x ∈ K} ⟪x, ω⟫ = - supportFunction K (-ω)`.

For a unit vector `ω` these are the endpoints `a_K(ω) ≤ b_K(ω)` of the orthogonal projection of
`K` onto the line `ℝ ω` (the *projection endpoints* of [Hägg, (1.1)]).  Both are defined with
`sSup`/`sInf` on `ℝ`, so they only carry meaning for nonempty bounded sets.

## Main results

* `subset_of_forall_supportFunction_le`, `subset_iff_forall_supportFunction_le`: the classical
  support-function criterion: a nonempty bounded set `K` is contained in a nonempty bounded
  closed convex set `L` of a Hilbert space iff `h_K ≤ h_L`.
* `subset_iff_forall_projection_endpoints`: the same criterion in the form
  `K ⊆ L ↔ a_L ≤ a_K ≤ b_K ≤ b_L` used in [Hägg, (1.2)].
* `exists_inner_eq_iff_mem_Ioo`, `exists_inner_eq_iff_mem_Icc`: a (bounded, nonempty) open,
  resp. compact, convex set meets the hyperplane `{x | ⟪x, ω⟫ = p}` iff `a_K(ω) < p < b_K(ω)`,
  resp. `a_K(ω) ≤ p ≤ b_K(ω)`.
* `supportFunction_closure`, `supportFunction_closedBall`, `supportFunction_image_add`,
  `supportFunction_image_continuousLinearMap`, `lipschitzWith_supportFunction`.

## References

* C. Hägg, *An ellipse criterion for exact nonuniqueness in the planar interior Radon problem*.
-/

open Set Metric Bornology
open scoped RealInnerProductSpace

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The support function `h_K(ω) = sup_{x ∈ K} ⟪x, ω⟫` of a set `K`.  This is the upper
projection endpoint `b_K(ω)` of [Hägg].  It is only meaningful for nonempty bounded `K`
(otherwise it takes the junk value of `sSup` on `ℝ`). -/
def supportFunction (K : Set E) (ω : E) : ℝ :=
  sSup ((fun x ↦ ⟪x, ω⟫) '' K)

/-- The lower support function `inf_{x ∈ K} ⟪x, ω⟫ = - h_K(-ω)`, i.e. the lower projection
endpoint `a_K(ω)` of [Hägg].  It is only meaningful for nonempty bounded `K`. -/
def lowerSupportFunction (K : Set E) (ω : E) : ℝ :=
  sInf ((fun x ↦ ⟪x, ω⟫) '' K)

section Basic

variable {K L : Set E} {ω x : E} {c : ℝ}

theorem image_inner_neg (K : Set E) (ω : E) :
    (fun x ↦ ⟪x, -ω⟫) '' K = -((fun x ↦ ⟪x, ω⟫) '' K) := by
  ext r
  simp only [mem_image, inner_neg_right, Set.mem_neg]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, by ring⟩
  · rintro ⟨x, hx, hxr⟩
    exact ⟨x, hx, by linarith⟩

theorem lowerSupportFunction_eq_neg_supportFunction_neg (K : Set E) (ω : E) :
    lowerSupportFunction K ω = -supportFunction K (-ω) := by
  rw [lowerSupportFunction, supportFunction, image_inner_neg, Real.sInf_def]

theorem supportFunction_neg (K : Set E) (ω : E) :
    supportFunction K (-ω) = -lowerSupportFunction K ω := by
  rw [lowerSupportFunction_eq_neg_supportFunction_neg, neg_neg]

theorem lowerSupportFunction_neg (K : Set E) (ω : E) :
    lowerSupportFunction K (-ω) = -supportFunction K ω := by
  rw [lowerSupportFunction_eq_neg_supportFunction_neg, neg_neg]

theorem bddAbove_image_inner (hK : IsBounded K) (ω : E) :
    BddAbove ((fun x ↦ ⟪x, ω⟫) '' K) := by
  obtain ⟨R, hR⟩ := hK.subset_closedBall 0
  refine ⟨R * ‖ω‖, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  have hx' : ‖x‖ ≤ R := by simpa using hR hx
  calc ⟪x, ω⟫ ≤ ‖x‖ * ‖ω‖ := real_inner_le_norm x ω
    _ ≤ R * ‖ω‖ := by gcongr

theorem bddBelow_image_inner (hK : IsBounded K) (ω : E) :
    BddBelow ((fun x ↦ ⟪x, ω⟫) '' K) := by
  have := bddAbove_image_inner hK (-ω)
  rw [image_inner_neg, bddAbove_neg] at this
  exact this

theorem inner_le_supportFunction (hK : IsBounded K) (hx : x ∈ K) :
    ⟪x, ω⟫ ≤ supportFunction K ω :=
  le_csSup (bddAbove_image_inner hK ω) ⟨x, hx, rfl⟩

theorem lowerSupportFunction_le_inner (hK : IsBounded K) (hx : x ∈ K) :
    lowerSupportFunction K ω ≤ ⟪x, ω⟫ :=
  csInf_le (bddBelow_image_inner hK ω) ⟨x, hx, rfl⟩

theorem supportFunction_le (hK : K.Nonempty) (h : ∀ x ∈ K, ⟪x, ω⟫ ≤ c) :
    supportFunction K ω ≤ c :=
  csSup_le (hK.image _) (by rintro _ ⟨x, hx, rfl⟩; exact h x hx)

theorem le_lowerSupportFunction (hK : K.Nonempty) (h : ∀ x ∈ K, c ≤ ⟪x, ω⟫) :
    c ≤ lowerSupportFunction K ω :=
  le_csInf (hK.image _) (by rintro _ ⟨x, hx, rfl⟩; exact h x hx)

theorem supportFunction_le_iff (hKne : K.Nonempty) (hK : IsBounded K) :
    supportFunction K ω ≤ c ↔ ∀ x ∈ K, ⟪x, ω⟫ ≤ c :=
  ⟨fun h _ hx ↦ (inner_le_supportFunction hK hx).trans h, supportFunction_le hKne⟩

theorem le_lowerSupportFunction_iff (hKne : K.Nonempty) (hK : IsBounded K) :
    c ≤ lowerSupportFunction K ω ↔ ∀ x ∈ K, c ≤ ⟪x, ω⟫ :=
  ⟨fun h _ hx ↦ h.trans (lowerSupportFunction_le_inner hK hx), le_lowerSupportFunction hKne⟩

theorem lt_supportFunction_iff (hKne : K.Nonempty) (hK : IsBounded K) :
    c < supportFunction K ω ↔ ∃ x ∈ K, c < ⟪x, ω⟫ := by
  rw [← not_le, supportFunction_le_iff hKne hK]
  push Not
  rfl

theorem lowerSupportFunction_lt_iff (hKne : K.Nonempty) (hK : IsBounded K) :
    lowerSupportFunction K ω < c ↔ ∃ x ∈ K, ⟪x, ω⟫ < c := by
  rw [← not_le, le_lowerSupportFunction_iff hKne hK]
  push Not
  rfl

theorem lowerSupportFunction_le_supportFunction (hKne : K.Nonempty) (hK : IsBounded K) :
    lowerSupportFunction K ω ≤ supportFunction K ω := by
  obtain ⟨x, hx⟩ := hKne
  exact (lowerSupportFunction_le_inner hK hx).trans (inner_le_supportFunction hK hx)

@[simp] theorem supportFunction_empty (ω : E) : supportFunction (∅ : Set E) ω = 0 := by
  simp [supportFunction]

@[simp] theorem lowerSupportFunction_empty (ω : E) :
    lowerSupportFunction (∅ : Set E) ω = 0 := by
  simp [lowerSupportFunction]

@[simp] theorem supportFunction_singleton (x ω : E) :
    supportFunction {x} ω = ⟪x, ω⟫ := by
  simp [supportFunction]

@[simp] theorem lowerSupportFunction_singleton (x ω : E) :
    lowerSupportFunction {x} ω = ⟪x, ω⟫ := by
  simp [lowerSupportFunction]

@[simp] theorem supportFunction_zero (K : Set E) : supportFunction K 0 = 0 := by
  rcases K.eq_empty_or_nonempty with rfl | hK
  · simp
  · simp [supportFunction, hK.image_const]

@[simp] theorem lowerSupportFunction_zero (K : Set E) : lowerSupportFunction K 0 = 0 := by
  rw [lowerSupportFunction_eq_neg_supportFunction_neg, neg_zero, supportFunction_zero, neg_zero]

theorem supportFunction_mono (hKne : K.Nonempty) (hL : IsBounded L) (hKL : K ⊆ L) :
    supportFunction K ω ≤ supportFunction L ω :=
  supportFunction_le hKne fun _ hx ↦ inner_le_supportFunction hL (hKL hx)

theorem lowerSupportFunction_anti (hKne : K.Nonempty) (hL : IsBounded L) (hKL : K ⊆ L) :
    lowerSupportFunction L ω ≤ lowerSupportFunction K ω :=
  le_lowerSupportFunction hKne fun _ hx ↦ lowerSupportFunction_le_inner hL (hKL hx)

/-- The support function does not see the closure of a bounded set. -/
theorem supportFunction_closure (hK : IsBounded K) :
    supportFunction (closure K) ω = supportFunction K ω := by
  rcases K.eq_empty_or_nonempty with rfl | hKne
  · simp
  apply le_antisymm
  · refine supportFunction_le hKne.closure fun x hx ↦ ?_
    have hclosed : IsClosed {y : E | ⟪y, ω⟫ ≤ supportFunction K ω} :=
      isClosed_le (continuous_id.inner continuous_const) continuous_const
    exact closure_minimal (fun y hy ↦ inner_le_supportFunction hK hy) hclosed hx
  · exact supportFunction_mono hKne hK.closure subset_closure

theorem lowerSupportFunction_closure (hK : IsBounded K) :
    lowerSupportFunction (closure K) ω = lowerSupportFunction K ω := by
  rw [lowerSupportFunction_eq_neg_supportFunction_neg,
    lowerSupportFunction_eq_neg_supportFunction_neg, supportFunction_closure hK]

/-- Translating a set adds the corresponding linear function to the support function. -/
theorem supportFunction_image_add (hKne : K.Nonempty) (hK : IsBounded K) (c ω : E) :
    supportFunction ((c + ·) '' K) ω = ⟪c, ω⟫ + supportFunction K ω := by
  have hcK : ((c + ·) '' K).Nonempty := hKne.image _
  have hcKb : IsBounded ((c + ·) '' K) := by
    obtain ⟨R, hR⟩ := hK.subset_closedBall 0
    refine (isBounded_closedBall (x := (0 : E)) (r := ‖c‖ + R)).subset ?_
    rintro _ ⟨x, hx, rfl⟩
    have hx' : ‖x‖ ≤ R := by simpa using hR hx
    rw [mem_closedBall_zero_iff]
    exact (norm_add_le _ _).trans (by linarith)
  apply le_antisymm
  · refine supportFunction_le hcK ?_
    rintro _ ⟨x, hx, rfl⟩
    simp only [inner_add_left]
    linarith [inner_le_supportFunction (ω := ω) hK hx]
  · have : supportFunction K ω ≤ supportFunction ((c + ·) '' K) ω - ⟪c, ω⟫ := by
      refine supportFunction_le hKne fun x hx ↦ ?_
      have := inner_le_supportFunction (ω := ω) hcKb ⟨x, hx, rfl⟩
      simp only [inner_add_left] at this
      linarith
    linarith

theorem lowerSupportFunction_image_add (hKne : K.Nonempty) (hK : IsBounded K) (c ω : E) :
    lowerSupportFunction ((c + ·) '' K) ω = ⟪c, ω⟫ + lowerSupportFunction K ω := by
  rw [lowerSupportFunction_eq_neg_supportFunction_neg,
    lowerSupportFunction_eq_neg_supportFunction_neg, supportFunction_image_add hKne hK,
    inner_neg_right]
  ring

/-- The support function of the image of a set under a continuous linear map, in terms of the
adjoint. -/
theorem supportFunction_image_continuousLinearMap {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [CompleteSpace E] [CompleteSpace F] (A : E →L[ℝ] F) (K : Set E)
    (ω : F) :
    supportFunction (A '' K) ω = supportFunction K (ContinuousLinearMap.adjoint A ω) := by
  rw [supportFunction, supportFunction, Set.image_image]
  congr 1
  ext r
  simp [ContinuousLinearMap.adjoint_inner_right]

theorem lowerSupportFunction_image_continuousLinearMap {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [CompleteSpace E] [CompleteSpace F] (A : E →L[ℝ] F) (K : Set E)
    (ω : F) :
    lowerSupportFunction (A '' K) ω =
      lowerSupportFunction K (ContinuousLinearMap.adjoint A ω) := by
  rw [lowerSupportFunction_eq_neg_supportFunction_neg,
    lowerSupportFunction_eq_neg_supportFunction_neg,
    supportFunction_image_continuousLinearMap, map_neg]

/-- The support function of a closed ball centered at the origin. -/
theorem supportFunction_closedBall_zero {r : ℝ} (hr : 0 ≤ r) (ω : E) :
    supportFunction (closedBall (0 : E) r) ω = r * ‖ω‖ := by
  apply le_antisymm
  · refine supportFunction_le ⟨0, by simpa using hr⟩ fun x hx ↦ ?_
    have hx' : ‖x‖ ≤ r := by simpa using hx
    calc ⟪x, ω⟫ ≤ ‖x‖ * ‖ω‖ := real_inner_le_norm x ω
      _ ≤ r * ‖ω‖ := by gcongr
  · rcases eq_or_ne ω 0 with rfl | hω
    · simp
    · have hωpos : 0 < ‖ω‖ := norm_pos_iff.mpr hω
      have hmem : (r / ‖ω‖) • ω ∈ closedBall (0 : E) r := by
        rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs, abs_div, abs_norm,
          abs_of_nonneg hr, div_mul_cancel₀ _ hωpos.ne']
      calc r * ‖ω‖ = ⟪(r / ‖ω‖) • ω, ω⟫ := by
            rw [real_inner_smul_left, real_inner_self_eq_norm_sq]
            field_simp
        _ ≤ _ := inner_le_supportFunction isBounded_closedBall hmem

theorem lowerSupportFunction_closedBall_zero {r : ℝ} (hr : 0 ≤ r) (ω : E) :
    lowerSupportFunction (closedBall (0 : E) r) ω = -(r * ‖ω‖) := by
  rw [lowerSupportFunction_eq_neg_supportFunction_neg, supportFunction_closedBall_zero hr,
    norm_neg]

/-- On a set contained in `closedBall 0 R`, the support function is `R`-Lipschitz. -/
theorem abs_supportFunction_sub_le {R : ℝ} (hKne : K.Nonempty) (hKR : K ⊆ closedBall 0 R)
    (ω ω' : E) : |supportFunction K ω - supportFunction K ω'| ≤ R * ‖ω - ω'‖ := by
  have hK : IsBounded K := isBounded_closedBall.subset hKR
  have key : ∀ ω ω' : E, supportFunction K ω ≤ supportFunction K ω' + R * ‖ω - ω'‖ := by
    intro ω ω'
    refine supportFunction_le hKne fun x hx ↦ ?_
    have hx' : ‖x‖ ≤ R := by simpa using hKR hx
    have h1 : ⟪x, ω⟫ = ⟪x, ω'⟫ + ⟪x, ω - ω'⟫ := by rw [inner_sub_right]; ring
    have h2 : ⟪x, ω - ω'⟫ ≤ R * ‖ω - ω'‖ :=
      (real_inner_le_norm _ _).trans (by gcongr)
    linarith [inner_le_supportFunction (ω := ω') hK hx]
  rw [abs_le]
  constructor
  · have := key ω' ω
    rw [norm_sub_rev] at this
    linarith
  · linarith [key ω ω']

theorem continuous_supportFunction (hK : IsBounded K) : Continuous (supportFunction K) := by
  rcases K.eq_empty_or_nonempty with rfl | hKne
  · rw [show supportFunction (∅ : Set E) = fun _ ↦ 0 from funext supportFunction_empty]
    exact continuous_const
  obtain ⟨R, hR⟩ := hK.subset_closedBall 0
  have hR0 : 0 ≤ R := by
    obtain ⟨x, hx⟩ := hKne
    exact (norm_nonneg x).trans (by simpa using hR hx)
  refine (LipschitzWith.of_dist_le_mul fun ω ω' ↦ ?_ : LipschitzWith ⟨R, hR0⟩ _).continuous
  rw [Real.dist_eq, dist_eq_norm]
  exact abs_supportFunction_sub_le hKne hR ω ω'

theorem continuous_lowerSupportFunction (hK : IsBounded K) :
    Continuous (lowerSupportFunction K) := by
  simp_rw [funext (lowerSupportFunction_eq_neg_supportFunction_neg K)]
  exact ((continuous_supportFunction hK).comp continuous_neg).neg

/-- On a compact set the supremum defining the support function is attained. -/
theorem IsCompact.exists_inner_eq_supportFunction (hK : IsCompact K) (hKne : K.Nonempty)
    (ω : E) : ∃ x ∈ K, ⟪x, ω⟫ = supportFunction K ω := by
  obtain ⟨x, hx, hmax⟩ := hK.exists_isMaxOn hKne
    (by fun_prop : Continuous fun y : E ↦ ⟪y, ω⟫).continuousOn
  refine ⟨x, hx, le_antisymm (inner_le_supportFunction hK.isBounded hx) ?_⟩
  exact supportFunction_le hKne fun y hy ↦ hmax hy

theorem IsCompact.exists_inner_eq_lowerSupportFunction (hK : IsCompact K) (hKne : K.Nonempty)
    (ω : E) : ∃ x ∈ K, ⟪x, ω⟫ = lowerSupportFunction K ω := by
  obtain ⟨x, hx, hmin⟩ := hK.exists_isMinOn hKne
    (by fun_prop : Continuous fun y : E ↦ ⟪y, ω⟫).continuousOn
  refine ⟨x, hx, le_antisymm ?_ (lowerSupportFunction_le_inner hK.isBounded hx)⟩
  exact le_lowerSupportFunction hKne fun y hy ↦ hmin hy

end Basic

/-! ### The support-function inclusion criterion -/

section Inclusion

variable [CompleteSpace E] {K L : Set E}

/-- **Support-function criterion.**  If `K` is bounded and `L` is a nonempty closed convex set
in a real Hilbert space with `h_K ≤ h_L`, then `K ⊆ L`.  (For unbounded `L` the hypothesis
involves junk values of `h_L`; it is still sufficient.) -/
theorem subset_of_forall_supportFunction_le (hK : IsBounded K) (hLne : L.Nonempty)
    (hLconv : Convex ℝ L) (hLclosed : IsClosed L)
    (h : ∀ ω, supportFunction K ω ≤ supportFunction L ω) : K ⊆ L := by
  intro x hx
  by_contra hxL
  obtain ⟨f, u, hfL, hfx⟩ := geometric_hahn_banach_closed_point hLconv hLclosed hxL
  set ω : E := (InnerProductSpace.toDual ℝ E).symm f
  have hf : ∀ y, f y = ⟪y, ω⟫ := fun y ↦ by
    rw [real_inner_comm, InnerProductSpace.toDual_symm_apply]
  have h1 : supportFunction L ω ≤ u := supportFunction_le hLne fun y hy ↦ by
    rw [← hf]; exact (hfL y hy).le
  have h2 : ⟪x, ω⟫ ≤ supportFunction K ω := inner_le_supportFunction hK hx
  have := h ω
  rw [hf] at hfx
  linarith

/-- **Support-function criterion**: a nonempty bounded set is contained in a nonempty bounded
closed convex set of a real Hilbert space iff its support function is smaller.  (The
nonemptiness of `L` cannot be dropped: `h_∅ = 0 = h_{0}`.) -/
theorem subset_iff_forall_supportFunction_le (hKne : K.Nonempty) (hK : IsBounded K)
    (hLne : L.Nonempty) (hLconv : Convex ℝ L) (hLclosed : IsClosed L) (hLb : IsBounded L) :
    K ⊆ L ↔ ∀ ω, supportFunction K ω ≤ supportFunction L ω :=
  ⟨fun hKL _ ↦ supportFunction_mono hKne hLb hKL,
    subset_of_forall_supportFunction_le hK hLne hLconv hLclosed⟩

/-- **Support-function criterion** in the form [Hägg, (1.2)]:
`K ⊆ L ↔ a_L ≤ a_K ≤ b_K ≤ b_L` (in every direction). -/
theorem subset_iff_forall_projection_endpoints (hKne : K.Nonempty) (hK : IsBounded K)
    (hLne : L.Nonempty) (hLconv : Convex ℝ L) (hLclosed : IsClosed L) (hLb : IsBounded L) :
    K ⊆ L ↔ ∀ ω, lowerSupportFunction L ω ≤ lowerSupportFunction K ω ∧
      lowerSupportFunction K ω ≤ supportFunction K ω ∧
      supportFunction K ω ≤ supportFunction L ω := by
  rw [subset_iff_forall_supportFunction_le hKne hK hLne hLconv hLclosed hLb]
  refine ⟨fun h ω ↦ ⟨?_, lowerSupportFunction_le_supportFunction hKne hK, h ω⟩,
    fun h ω ↦ (h ω).2.2⟩
  rw [lowerSupportFunction_eq_neg_supportFunction_neg,
    lowerSupportFunction_eq_neg_supportFunction_neg]
  exact neg_le_neg (h (-ω))

end Inclusion

/-! ### Hyperplanes meeting convex sets -/

section Hyperplane

variable {K : Set E} {ω x : E} {p : ℝ}

/-- A point of an open bounded set lies strictly below the support function in every nonzero
direction. -/
theorem IsOpen.inner_lt_supportFunction (hKo : IsOpen K) (hK : IsBounded K) (hx : x ∈ K)
    (hω : ω ≠ 0) : ⟪x, ω⟫ < supportFunction K ω := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hKo x hx
  have hωpos : 0 < ‖ω‖ := norm_pos_iff.mpr hω
  set t : ℝ := ε / (2 * ‖ω‖)
  have ht : 0 < t := by positivity
  have hmem : x + t • ω ∈ K := by
    apply hball
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht.le]
    have : t * ‖ω‖ = ε / 2 := by
      simp only [t]
      field_simp
    linarith
  have := inner_le_supportFunction (ω := ω) hK hmem
  rw [inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq] at this
  have : 0 < t * ‖ω‖ ^ 2 := by positivity
  linarith

/-- A point of an open bounded set lies strictly above the lower support function in every
nonzero direction. -/
theorem IsOpen.lowerSupportFunction_lt_inner (hKo : IsOpen K) (hK : IsBounded K) (hx : x ∈ K)
    (hω : ω ≠ 0) : lowerSupportFunction K ω < ⟪x, ω⟫ := by
  have := hKo.inner_lt_supportFunction hK hx (neg_ne_zero.mpr hω)
  rw [supportFunction_neg, inner_neg_right] at this
  linarith

/-- A bounded set can only meet the hyperplane `⟪x, ω⟫ = p` if `a_K(ω) ≤ p ≤ b_K(ω)`. -/
theorem mem_Icc_of_exists_inner_eq (hK : IsBounded K) (h : ∃ x ∈ K, ⟪x, ω⟫ = p) :
    p ∈ Icc (lowerSupportFunction K ω) (supportFunction K ω) := by
  obtain ⟨x, hx, rfl⟩ := h
  exact ⟨lowerSupportFunction_le_inner hK hx, inner_le_supportFunction hK hx⟩

/-- A bounded open set can only meet the hyperplane `⟪x, ω⟫ = p` (`ω ≠ 0`) if
`a_K(ω) < p < b_K(ω)`. -/
theorem IsOpen.mem_Ioo_of_exists_inner_eq (hKo : IsOpen K) (hK : IsBounded K) (hω : ω ≠ 0)
    (h : ∃ x ∈ K, ⟪x, ω⟫ = p) :
    p ∈ Ioo (lowerSupportFunction K ω) (supportFunction K ω) := by
  obtain ⟨x, hx, rfl⟩ := h
  exact ⟨hKo.lowerSupportFunction_lt_inner hK hx hω, hKo.inner_lt_supportFunction hK hx hω⟩

/-- The set of values `⟪x, ω⟫` on a convex set is order-connected (an interval). -/
theorem Convex.ordConnected_image_inner (hK : Convex ℝ K) (ω : E) :
    ((fun x ↦ ⟪x, ω⟫) '' K).OrdConnected := by
  rw [← convex_iff_ordConnected]
  exact hK.is_linear_image
    ⟨fun x y ↦ inner_add_left x y ω, fun c x ↦ real_inner_smul_left x ω c⟩

/-- A convex bounded set meets every hyperplane `⟪x, ω⟫ = p` with `a_K(ω) < p < b_K(ω)`. -/
theorem Convex.exists_inner_eq_of_mem_Ioo (hK : Convex ℝ K) (hKne : K.Nonempty)
    (hKb : IsBounded K) (hp : p ∈ Ioo (lowerSupportFunction K ω) (supportFunction K ω)) :
    ∃ x ∈ K, ⟪x, ω⟫ = p := by
  obtain ⟨y, hy, hyp⟩ := (lowerSupportFunction_lt_iff hKne hKb).mp hp.1
  obtain ⟨z, hz, hzp⟩ := (lt_supportFunction_iff hKne hKb).mp hp.2
  exact (hK.ordConnected_image_inner ω).out ⟨y, hy, rfl⟩ ⟨z, hz, rfl⟩ ⟨hyp.le, hzp.le⟩

/-- A nonempty bounded open convex set meets the hyperplane `⟪x, ω⟫ = p` (`ω ≠ 0`) iff
`a_K(ω) < p < b_K(ω)`. -/
theorem Convex.exists_inner_eq_iff_mem_Ioo (hK : Convex ℝ K) (hKo : IsOpen K)
    (hKne : K.Nonempty) (hKb : IsBounded K) (hω : ω ≠ 0) :
    (∃ x ∈ K, ⟪x, ω⟫ = p) ↔ p ∈ Ioo (lowerSupportFunction K ω) (supportFunction K ω) :=
  ⟨hKo.mem_Ioo_of_exists_inner_eq hKb hω, hK.exists_inner_eq_of_mem_Ioo hKne hKb⟩

/-- A nonempty compact convex set meets the hyperplane `⟪x, ω⟫ = p` iff
`a_K(ω) ≤ p ≤ b_K(ω)`. -/
theorem Convex.exists_inner_eq_iff_mem_Icc (hK : Convex ℝ K) (hKc : IsCompact K)
    (hKne : K.Nonempty) :
    (∃ x ∈ K, ⟪x, ω⟫ = p) ↔ p ∈ Icc (lowerSupportFunction K ω) (supportFunction K ω) := by
  refine ⟨mem_Icc_of_exists_inner_eq hKc.isBounded, fun hp ↦ ?_⟩
  obtain ⟨y, hy, hyp⟩ := hKc.exists_inner_eq_lowerSupportFunction hKne ω
  obtain ⟨z, hz, hzp⟩ := hKc.exists_inner_eq_supportFunction hKne ω
  exact (hK.ordConnected_image_inner ω).out ⟨y, hy, rfl⟩ ⟨z, hz, rfl⟩
    ⟨by simpa [hyp] using hp.1, by simpa [hzp] using hp.2⟩

end Hyperplane

end
