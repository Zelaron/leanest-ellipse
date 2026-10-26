import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# Pure isometries and the Wold decomposition

Let `T` be an isometry of a Hilbert space `H`.  Its *wandering subspace* is
`𝓔 = ker T† = (range T)ᗮ` (`ContinuousLinearMap.wanderingSubspace`).  The subspaces `Tⁿ 𝓔` are
pairwise orthogonal, and the orthogonal complement of their closed span is `⋂ₙ range Tⁿ`
(the *Wold decomposition*).

`T` is a *pure isometry* (`ContinuousLinearMap.IsPureIsometry`) if moreover `T†ⁿ → 0` strongly.
Then `⋂ₙ range Tⁿ = 0`, so `H = ⨁ₙ Tⁿ 𝓔` is a Hilbert sum (`IsPureIsometry.isHilbertSum`) and
`H ≃ ℓ²(ℕ, 𝓔)` with `T` corresponding to the shift (`IsPureIsometry.woldEquiv`).  In particular
`𝓔 ≠ 0` as soon as `H ≠ 0`.

## Main results

* `ContinuousLinearMap.orthogonalFamily_woldEmbedding`: the summands `Tⁿ 𝓔` are orthogonal.
* `ContinuousLinearMap.orthogonal_iSup_range_woldEmbedding`: the Wold decomposition
  `(⨆ₙ Tⁿ 𝓔)ᗮ = ⨅ₙ range Tⁿ`.
* `ContinuousLinearMap.IsPureIsometry.isHilbertSum`, `IsPureIsometry.woldEquiv`,
  `IsPureIsometry.wanderingSubspace_ne_bot`.
* `ContinuousLinearMap.tendsto_pow_apply_zero_of_dense`: a contraction whose eventually-killed
  vectors are dense has `Aⁿ → 0` strongly; `ContinuousLinearMap.isPureIsometry_of_dense` is the
  resulting purity criterion.
-/

open Filter Topology
open scoped InnerProductSpace

noncomputable section

namespace ContinuousLinearMap

section Pow

variable {𝕜 F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  (A : F →L[𝕜] F)

theorem pow_succ_apply (n : ℕ) (x : F) : (A ^ (n + 1)) x = (A ^ n) (A x) := by
  rw [pow_succ]; rfl

theorem pow_succ_apply' (n : ℕ) (x : F) : (A ^ (n + 1)) x = A ((A ^ n) x) := by
  rw [pow_succ']; rfl

theorem pow_add_apply (m n : ℕ) (x : F) : (A ^ (m + n)) x = (A ^ m) ((A ^ n) x) := by
  rw [pow_add]; rfl

theorem pow_apply_eq_zero_of_le {m n : ℕ} {x : F} (hm : (A ^ m) x = 0) (hmn : m ≤ n) :
    (A ^ n) x = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  rw [add_comm, pow_add_apply, hm, map_zero]

/-- If `‖A x‖ ≤ ‖x‖` for all `x`, then `‖Aⁿ x‖ ≤ ‖x‖`. -/
theorem norm_pow_apply_le_of_forall_norm_apply_le {A : F →L[𝕜] F} (hA : ∀ x, ‖A x‖ ≤ ‖x‖)
    (n : ℕ) (x : F) : ‖(A ^ n) x‖ ≤ ‖x‖ := by
  induction n generalizing x with
  | zero => simp
  | succ n ih => exact (pow_succ_apply A n x ▸ ih (A x)).trans (hA x)

/-- A contraction `A` whose *eventually killed* vectors `{x | ∃ n, Aⁿ x = 0}` are dense satisfies
`Aⁿ x → 0` for every `x`. -/
theorem tendsto_pow_apply_zero_of_dense {A : F →L[𝕜] F} (hA : ∀ x, ‖A x‖ ≤ ‖x‖)
    (hdense : Dense {x | ∃ n, (A ^ n) x = 0}) (x : F) :
    Tendsto (fun n ↦ (A ^ n) x) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨y, ⟨N, hN⟩, hxy⟩ := hdense.exists_dist_lt x hε
  refine ⟨N, fun n hn ↦ ?_⟩
  calc dist ((A ^ n) x) 0 = ‖(A ^ n) (x - y)‖ := by
        rw [dist_zero_right, map_sub, pow_apply_eq_zero_of_le A hN hn, sub_zero]
    _ ≤ ‖x - y‖ := norm_pow_apply_le_of_forall_norm_apply_le hA n _
    _ < ε := by rwa [← dist_eq_norm]

end Pow

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  [CompleteSpace H]

theorem adjoint_pow (T : H →L[𝕜] H) (n : ℕ) : adjoint (T ^ n) = adjoint T ^ n := by
  simp only [← star_eq_adjoint, star_pow]

theorem inner_pow_apply_left (T : H →L[𝕜] H) (n : ℕ) (x y : H) :
    ⟪(T ^ n) x, y⟫_𝕜 = ⟪x, (adjoint T ^ n) y⟫_𝕜 := by
  rw [← adjoint_pow, adjoint_inner_right]

/-! ### Isometries -/

section Isometry

variable {T : H →L[𝕜] H}

theorem adjoint_apply_apply_of_isometry (hT : Isometry T) (x : H) : adjoint T (T x) = x :=
  congrArg (fun L : H →L[𝕜] H ↦ L x) ((isometry_iff_adjoint_comp_self T).1 hT)

omit [CompleteSpace H] in
theorem norm_pow_apply_of_isometry (hT : Isometry T) (n : ℕ) (x : H) : ‖(T ^ n) x‖ = ‖x‖ := by
  induction n generalizing x with
  | zero => simp
  | succ n ih => rw [pow_succ_apply, ih, hT.norm_map_of_map_zero (map_zero T)]

theorem adjoint_pow_apply_pow_apply_of_isometry (hT : Isometry T) (n : ℕ) (x : H) :
    (adjoint T ^ n) ((T ^ n) x) = x := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
      rw [pow_succ_apply', pow_succ_apply, ih, adjoint_apply_apply_of_isometry hT]

omit [CompleteSpace H] in
theorem norm_le_one_of_isometry (hT : Isometry T) : ‖T‖ ≤ 1 :=
  T.opNorm_le_bound zero_le_one fun x ↦ by rw [hT.norm_map_of_map_zero (map_zero T), one_mul]

theorem norm_adjoint_apply_le_of_isometry (hT : Isometry T) (x : H) : ‖adjoint T x‖ ≤ ‖x‖ :=
  calc ‖adjoint T x‖ ≤ ‖adjoint T‖ * ‖x‖ := le_opNorm _ _
    _ ≤ 1 * ‖x‖ := by
        gcongr
        rw [adjoint.norm_map]
        exact norm_le_one_of_isometry hT
    _ = ‖x‖ := one_mul _

/-- The *wandering subspace* `ker T†` of an operator `T`.  For an isometry this is the orthogonal
complement of its range (`ContinuousLinearMap.wanderingSubspace_eq_orthogonal_range`). -/
def wanderingSubspace (T : H →L[𝕜] H) : Submodule 𝕜 H :=
  (adjoint T).ker

theorem mem_wanderingSubspace {x : H} : x ∈ T.wanderingSubspace ↔ adjoint T x = 0 :=
  LinearMap.mem_ker

theorem wanderingSubspace_eq_orthogonal_range : T.wanderingSubspace = T.rangeᗮ :=
  T.orthogonal_range.symm

theorem isClosed_wanderingSubspace : IsClosed (T.wanderingSubspace : Set H) :=
  (adjoint T).isClosed_ker

/-- The wandering subspace is closed, hence complete. -/
instance : CompleteSpace T.wanderingSubspace :=
  isClosed_wanderingSubspace.completeSpace_coe

/-- For an isometry `T`, the orthogonal projection onto `ker T†` is `1 - T T†`. -/
theorem starProjection_wanderingSubspace_apply (hT : Isometry T) (x : H) :
    T.wanderingSubspace.starProjection x = x - T (adjoint T x) := by
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero ?_ fun w hw ↦ ?_
  · rw [mem_wanderingSubspace, map_sub, adjoint_apply_apply_of_isometry hT, sub_self]
  · rw [sub_sub_cancel, ← adjoint_inner_right, mem_wanderingSubspace.1 hw, inner_zero_right]

/-- For an isometry `T`, a vector orthogonal to `ker T†` lies in the range of `T`. -/
theorem apply_adjoint_apply_of_mem_orthogonal (hT : Isometry T) {x : H}
    (hx : x ∈ T.wanderingSubspaceᗮ) : T (adjoint T x) = x := by
  have := starProjection_wanderingSubspace_apply hT x
  rw [Submodule.starProjection_apply, Submodule.orthogonalProjectionOnto_eq_zero_iff.2 hx,
    Submodule.coe_zero] at this
  exact (sub_eq_zero.1 this.symm).symm

/-- For an isometry `T`, `Tᵐ 𝓔 ⟂ Tⁿ H` when `m < n`. -/
theorem inner_pow_apply_pow_apply_eq_zero_of_lt (hT : Isometry T) {e : H}
    (he : e ∈ T.wanderingSubspace) {m n : ℕ} (hmn : m < n) (y : H) :
    ⟪(T ^ m) e, (T ^ n) y⟫_𝕜 = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hmn
  rw [show m + k + 1 = m + (k + 1) by omega, pow_add_apply, inner_pow_apply_left,
    adjoint_pow_apply_pow_apply_of_isometry hT, pow_succ_apply', ← adjoint_inner_left,
    mem_wanderingSubspace.1 he, inner_zero_left]

/-- For an isometry `T`, the `n`-th Wold summand `𝓔 → H, e ↦ Tⁿ e`, as a linear isometry. -/
def woldEmbedding (hT : Isometry T) (n : ℕ) : T.wanderingSubspace →ₗᵢ[𝕜] H where
  toLinearMap := (T ^ n : H →L[𝕜] H).toLinearMap ∘ₗ T.wanderingSubspace.subtype
  norm_map' e := norm_pow_apply_of_isometry hT n e

@[simp]
theorem woldEmbedding_apply (hT : Isometry T) (n : ℕ) (e : T.wanderingSubspace) :
    woldEmbedding hT n e = (T ^ n) e :=
  rfl

/-- The Wold summands `Tⁿ 𝓔` of an isometry are pairwise orthogonal. -/
theorem orthogonalFamily_woldEmbedding (hT : Isometry T) :
    OrthogonalFamily 𝕜 (fun _ : ℕ ↦ T.wanderingSubspace) (woldEmbedding hT) := by
  intro m n hmn e f
  rcases lt_or_gt_of_ne hmn with h | h
  · exact inner_pow_apply_pow_apply_eq_zero_of_lt hT e.2 h _
  · rw [← inner_conj_symm, woldEmbedding_apply, woldEmbedding_apply,
      inner_pow_apply_pow_apply_eq_zero_of_lt hT f.2 h, map_zero]

/-- A vector orthogonal to all Wold summands satisfies `x = Tⁿ T†ⁿ x` for all `n`. -/
theorem eq_pow_apply_adjoint_pow_apply_of_mem_orthogonal (hT : Isometry T) {x : H}
    (hx : x ∈ (⨆ n, LinearMap.range (woldEmbedding hT n).toLinearMap)ᗮ) (n : ℕ) :
    (T ^ n) ((adjoint T ^ n) x) = x := by
  have horth : ∀ k, (adjoint T ^ k) x ∈ T.wanderingSubspaceᗮ := fun k ↦ by
    rw [Submodule.mem_orthogonal]
    intro e he
    rw [← inner_pow_apply_left]
    exact (Submodule.mem_orthogonal _ _).1 hx _
      (Submodule.mem_iSup_of_mem k ⟨⟨e, he⟩, rfl⟩)
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ_apply T, pow_succ_apply' (adjoint T),
        apply_adjoint_apply_of_mem_orthogonal hT (horth n), ih]

/-- **The Wold decomposition.**  For an isometry `T`, the orthogonal complement of the closed
span of the Wold summands `Tⁿ 𝓔` is `⋂ₙ range Tⁿ`. -/
theorem orthogonal_iSup_range_woldEmbedding (hT : Isometry T) :
    (⨆ n, LinearMap.range (woldEmbedding hT n).toLinearMap)ᗮ = ⨅ n, (T ^ n).range := by
  apply le_antisymm
  · intro x hx
    rw [Submodule.mem_iInf]
    intro n
    exact ⟨(adjoint T ^ n) x, eq_pow_apply_adjoint_pow_apply_of_mem_orthogonal hT hx n⟩
  · intro x hx
    rw [← Submodule.iInf_orthogonal, Submodule.mem_iInf]
    intro n
    rw [Submodule.mem_orthogonal]
    rintro _ ⟨e, rfl⟩
    obtain ⟨y, rfl⟩ := Submodule.mem_iInf _ |>.1 hx (n + 1)
    exact inner_pow_apply_pow_apply_eq_zero_of_lt hT e.2 (Nat.lt_succ_self n) y

end Isometry

/-! ### Pure isometries -/

/-- A *pure isometry* (unilateral shift): an isometry `T` with `T†ⁿ x → 0` for every `x`. -/
structure IsPureIsometry (T : H →L[𝕜] H) : Prop where
  isometry : Isometry T
  tendsto_adjoint_pow_apply : ∀ x, Tendsto (fun n ↦ (adjoint T ^ n) x) atTop (𝓝 0)

namespace IsPureIsometry

variable {T : H →L[𝕜] H}

/-- A pure isometry has no unitary part: `⋂ₙ range Tⁿ = 0`. -/
theorem iInf_range_pow_eq_bot (hT : IsPureIsometry T) : ⨅ n, (T ^ n).range = ⊥ := by
  refine eq_bot_iff.2 fun x hx ↦ ?_
  have hnorm : ∀ n, ‖(adjoint T ^ n) x‖ = ‖x‖ := fun n ↦ by
    obtain ⟨y, rfl⟩ := Submodule.mem_iInf _ |>.1 hx n
    change ‖(adjoint T ^ n) ((T ^ n) y)‖ = ‖(T ^ n) y‖
    rw [adjoint_pow_apply_pow_apply_of_isometry hT.isometry, norm_pow_apply_of_isometry
      hT.isometry]
  have hlim := (hT.tendsto_adjoint_pow_apply x).norm
  simp only [hnorm, norm_zero, tendsto_const_nhds_iff] at hlim
  exact (Submodule.mem_bot 𝕜).2 (norm_eq_zero.1 hlim)

/-- **Wold decomposition of a pure isometry**: the Wold summands `Tⁿ 𝓔` span a dense
subspace. -/
theorem topologicalClosure_iSup_range_woldEmbedding (hT : IsPureIsometry T) :
    (⨆ n, LinearMap.range (woldEmbedding hT.isometry n).toLinearMap).topologicalClosure = ⊤ := by
  rw [Submodule.topologicalClosure_eq_top_iff, orthogonal_iSup_range_woldEmbedding,
    hT.iInf_range_pow_eq_bot]

/-- **Wold decomposition of a pure isometry**: `H = ⨁ₙ Tⁿ 𝓔` is a Hilbert sum. -/
theorem isHilbertSum (hT : IsPureIsometry T) :
    IsHilbertSum 𝕜 (fun _ : ℕ ↦ T.wanderingSubspace) (woldEmbedding hT.isometry) :=
  IsHilbertSum.mk (orthogonalFamily_woldEmbedding hT.isometry)
    (hT.topologicalClosure_iSup_range_woldEmbedding).ge

/-- The Wold coordinates `H ≃ ℓ²(ℕ, 𝓔)` of a pure isometry. -/
noncomputable def woldEquiv (hT : IsPureIsometry T) :
    H ≃ₗᵢ[𝕜] lp (fun _ : ℕ ↦ T.wanderingSubspace) 2 :=
  hT.isHilbertSum.linearIsometryEquiv

theorem woldEquiv_symm_single (hT : IsPureIsometry T) (n : ℕ) (e : T.wanderingSubspace) :
    hT.woldEquiv.symm (lp.single 2 n e) = (T ^ n) e := by
  classical
  exact hT.isHilbertSum.linearIsometryEquiv_symm_apply_single e

/-- In Wold coordinates a pure isometry is the unilateral shift. -/
theorem apply_woldEquiv_symm_single (hT : IsPureIsometry T) (n : ℕ) (e : T.wanderingSubspace) :
    T (hT.woldEquiv.symm (lp.single 2 n e)) = hT.woldEquiv.symm (lp.single 2 (n + 1) e) := by
  rw [woldEquiv_symm_single, woldEquiv_symm_single, pow_succ_apply']

/-- The wandering subspace of a pure isometry of a nonzero Hilbert space is nonzero. -/
theorem wanderingSubspace_ne_bot [Nontrivial H] (hT : IsPureIsometry T) :
    T.wanderingSubspace ≠ ⊥ := by
  intro hbot
  have htop := hT.topologicalClosure_iSup_range_woldEmbedding
  have hmem : ∀ x : H, x ∈ T.wanderingSubspace → x = 0 := fun x hx ↦ by
    rw [hbot] at hx
    exact (Submodule.mem_bot 𝕜).1 hx
  have hzero : ⨆ n, LinearMap.range (woldEmbedding hT.isometry n).toLinearMap = ⊥ := by
    refine eq_bot_iff.2 (iSup_le fun n ↦ ?_)
    rintro _ ⟨e, rfl⟩
    have : (e : H) = 0 := hmem e e.2
    simp [this]
  have hclosed : IsClosed ((⊥ : Submodule 𝕜 H) : Set H) := by
    rw [Submodule.bot_coe]
    exact isClosed_singleton
  rw [hzero, hclosed.submodule_topologicalClosure_eq] at htop
  exact bot_ne_top htop

end IsPureIsometry

/-- **Purity criterion.**  An isometry `T` is pure as soon as the vectors killed by some power of
`T†` are dense. -/
theorem isPureIsometry_of_dense {T : H →L[𝕜] H} (hT : Isometry T)
    (hdense : Dense {x | ∃ n, (adjoint T ^ n) x = 0}) : IsPureIsometry T :=
  ⟨hT, tendsto_pow_apply_zero_of_dense (norm_adjoint_apply_le_of_isometry hT) hdense⟩

end ContinuousLinearMap

end
