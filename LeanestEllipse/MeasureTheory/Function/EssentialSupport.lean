import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.Topology.Algebra.Support

/-!
# The essential support of a function

For a function `f : α → β` on a topological measure space, `MeasureTheory.essSupport f μ` is the
support of the measure `μ.restrict (Function.support f)`.

* It is the complement of the largest open set on which `f = 0` almost everywhere
  (`MeasureTheory.notMem_essSupport_iff`); this is the notion of support of an `L¹`-class used
  in [Hägg].
* It only depends on the a.e.-class of `f` (`MeasureTheory.essSupport_congr_ae`), is closed,
  and is contained in the topological support `tsupport f`.
* For continuous `f` and a measure charging all nonempty open sets it coincides with
  `tsupport f` (`Continuous.essSupport_eq_tsupport`).
* On hereditarily Lindelöf spaces (e.g. second countable ones), `f` vanishes a.e. outside its
  essential support, and it has a strongly measurable representative vanishing identically
  there (`MeasureTheory.AEStronglyMeasurable.exists_eq_zero_outside_essSupport`).
-/

open Set Filter Topology

namespace MeasureTheory

variable {α β : Type*} [TopologicalSpace α] [MeasurableSpace α] [Zero β]
  {f g : α → β} {μ : Measure α}

/-- The essential support of `f` with respect to `μ`: the support of the measure
`μ.restrict (Function.support f)`, i.e. the complement of the largest open set on which `f`
vanishes almost everywhere (see `MeasureTheory.notMem_essSupport_iff`). -/
def essSupport (f : α → β) (μ : Measure α) : Set α :=
  (μ.restrict (Function.support f)).support

theorem isClosed_essSupport : IsClosed (essSupport f μ) := Measure.isClosed_support

/-- The essential support only depends on the almost-everywhere class of the function. -/
theorem essSupport_congr_ae (h : f =ᵐ[μ] g) : essSupport f μ = essSupport g μ := by
  have hs : Function.support f =ᵐ[μ] Function.support g := by
    filter_upwards [h] with x hx
    simp [Function.mem_support, hx]
  rw [essSupport, essSupport, Measure.restrict_congr_set hs]

variable [OpensMeasurableSpace α]

/-- A point lies outside the essential support iff `f` vanishes almost everywhere on some
neighbourhood of it. -/
theorem notMem_essSupport_iff {x : α} :
    x ∉ essSupport f μ ↔ ∃ U ∈ 𝓝 x, ∀ᵐ y ∂μ, y ∈ U → f y = 0 := by
  rw [essSupport, Measure.notMem_support_iff_exists]
  constructor
  · rintro ⟨U, hU, hU0⟩
    refine ⟨interior U, interior_mem_nhds.mpr hU, ?_⟩
    have h0 : μ (interior U ∩ Function.support f) = 0 := by
      rw [← Measure.restrict_apply isOpen_interior.measurableSet]
      exact measure_mono_null interior_subset hU0
    rw [ae_iff]
    refine measure_mono_null (fun y hy ↦ ?_) h0
    simp only [mem_ofPred_eq, Classical.not_imp] at hy
    exact ⟨hy.1, hy.2⟩
  · rintro ⟨U, hU, hae⟩
    refine ⟨interior U, interior_mem_nhds.mpr hU, ?_⟩
    rw [Measure.restrict_apply isOpen_interior.measurableSet]
    rw [ae_iff] at hae
    refine measure_mono_null (fun y hy ↦ ?_) hae
    simp only [mem_ofPred_eq, Classical.not_imp]
    exact ⟨interior_subset hy.1, hy.2⟩

/-- If `f` vanishes almost everywhere outside a closed set `K`, then its essential support is
contained in `K`. -/
theorem essSupport_subset_of_ae {K : Set α} (hK : IsClosed K)
    (h : ∀ᵐ x ∂μ, x ∉ K → f x = 0) : essSupport f μ ⊆ K := by
  apply Measure.support_subset_of_isClosed hK
  rw [mem_ae_iff, Measure.restrict_apply hK.isOpen_compl.measurableSet]
  rw [ae_iff] at h
  refine measure_mono_null (fun y hy ↦ ?_) h
  simp only [mem_ofPred_eq, Classical.not_imp]
  exact ⟨hy.1, hy.2⟩

/-- The essential support is contained in the topological support. -/
theorem essSupport_subset_tsupport : essSupport f μ ⊆ tsupport f :=
  essSupport_subset_of_ae (isClosed_tsupport f) (Eventually.of_forall fun _ hx ↦
    Function.notMem_support.mp fun h ↦ hx (subset_tsupport f h))

/-- For a continuous function and a measure charging nonempty open sets, the essential support
is the usual (topological) support. -/
theorem _root_.Continuous.essSupport_eq_tsupport [TopologicalSpace β] [T1Space β]
    [μ.IsOpenPosMeasure] (hf : Continuous f) : essSupport f μ = tsupport f := by
  refine Subset.antisymm essSupport_subset_tsupport (closure_minimal (fun x hx ↦ ?_)
    isClosed_essSupport)
  rw [essSupport, Measure.mem_support_iff_forall]
  intro U hU
  have hsupp : IsOpen (Function.support f) := by
    rw [Function.support_eq_preimage]
    exact isClosed_singleton.isOpen_compl.preimage hf
  have hopen : IsOpen (interior U ∩ Function.support f) := isOpen_interior.inter hsupp
  have hne : (interior U ∩ Function.support f).Nonempty :=
    ⟨x, mem_interior_iff_mem_nhds.mpr hU, hx⟩
  calc 0 < μ (interior U ∩ Function.support f) := hopen.measure_pos μ hne
    _ = μ.restrict (Function.support f) (interior U) :=
        (Measure.restrict_apply isOpen_interior.measurableSet).symm
    _ ≤ μ.restrict (Function.support f) U := measure_mono interior_subset

variable [HereditarilyLindelofSpace α]

/-- A function vanishes almost everywhere outside its essential support. -/
theorem ae_eq_zero_of_notMem_essSupport : ∀ᵐ x ∂μ, x ∉ essSupport f μ → f x = 0 := by
  have h := Measure.measure_compl_support (μ := μ.restrict (Function.support f))
  change (μ.restrict (Function.support f)) (essSupport f μ)ᶜ = 0 at h
  rw [Measure.restrict_apply isClosed_essSupport.isOpen_compl.measurableSet] at h
  rw [ae_iff]
  refine measure_mono_null (fun y hy ↦ ?_) h
  simp only [mem_ofPred_eq, Classical.not_imp] at hy
  exact ⟨hy.1, hy.2⟩

/-- The essential support of `f ∘ φ` is contained in the preimage of the essential support of
`f`, for a continuous quasi-measure-preserving map `φ`. -/
theorem essSupport_comp_subset {γ : Type*} [TopologicalSpace γ] [MeasurableSpace γ]
    [OpensMeasurableSpace γ] {ν : Measure γ} {φ : γ → α} (hφ : Continuous φ)
    (hφm : Measure.QuasiMeasurePreserving φ ν μ) :
    essSupport (f ∘ φ) ν ⊆ φ ⁻¹' essSupport f μ :=
  essSupport_subset_of_ae (isClosed_essSupport.preimage hφ)
    (hφm.ae (ae_eq_zero_of_notMem_essSupport (f := f) (μ := μ)))

omit [OpensMeasurableSpace α] in
theorem essSupport_eq_empty_iff : essSupport f μ = ∅ ↔ f =ᵐ[μ] 0 := by
  rw [essSupport, Measure.support_eq_empty_iff, Measure.restrict_eq_zero, EventuallyEq, ae_iff]
  rfl

omit [OpensMeasurableSpace α] in
theorem essSupport_nonempty_iff : (essSupport f μ).Nonempty ↔ ¬ f =ᵐ[μ] 0 := by
  rw [nonempty_iff_ne_empty, Ne, essSupport_eq_empty_iff]

/-- `f` agrees a.e. with its restriction to the essential support. -/
theorem indicator_essSupport_ae_eq : (essSupport f μ).indicator f =ᵐ[μ] f := by
  filter_upwards [ae_eq_zero_of_notMem_essSupport (f := f) (μ := μ)] with x hx
  by_cases hmem : x ∈ essSupport f μ
  · rw [indicator_of_mem hmem]
  · rw [indicator_of_notMem hmem, hx hmem]

/-- An a.e. strongly measurable function has a strongly measurable representative that vanishes
identically outside the essential support. -/
theorem AEStronglyMeasurable.exists_eq_zero_outside_essSupport [TopologicalSpace β]
    (hf : AEStronglyMeasurable f μ) :
    ∃ g : α → β, StronglyMeasurable g ∧ g =ᵐ[μ] f ∧ ∀ x ∉ essSupport f μ, g x = 0 := by
  refine ⟨(essSupport f μ).indicator (hf.mk f),
    hf.stronglyMeasurable_mk.indicator isClosed_essSupport.measurableSet, ?_,
    fun x hx ↦ indicator_of_notMem hx _⟩
  filter_upwards [hf.ae_eq_mk, ae_eq_zero_of_notMem_essSupport (f := f) (μ := μ)] with x h1 h2
  by_cases hmem : x ∈ essSupport f μ
  · rw [indicator_of_mem hmem, ← h1]
  · rw [indicator_of_notMem hmem, h2 hmem]

end MeasureTheory
