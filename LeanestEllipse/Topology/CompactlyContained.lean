import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Separation.Hausdorff

/-!
# Compact containment

`CompactlyContained A B` (notation `A ⋐ B`, scoped in `CompactlyContained`) means that the closure
of `A` is compact and contained in `B`, as in [Hägg]: "`Ω₀ ⋐ Ω₁` if `\overline{Ω₀}` is compact and
contained in `Ω₁`".
-/

open Set

variable {X : Type*} [TopologicalSpace X] {A B C : Set X}

/-- `A ⋐ B`: the closure of `A` is compact and contained in `B`. -/
def CompactlyContained (A B : Set X) : Prop :=
  IsCompact (closure A) ∧ closure A ⊆ B

@[inherit_doc] scoped[CompactlyContained] infix:50 " ⋐ " => CompactlyContained

open scoped CompactlyContained

namespace CompactlyContained

theorem isCompact_closure (h : A ⋐ B) : IsCompact (closure A) := h.1

theorem closure_subset (h : A ⋐ B) : closure A ⊆ B := h.2

theorem subset (h : A ⋐ B) : A ⊆ B := subset_closure.trans h.2

theorem mono_left (h : B ⋐ C) (hAB : A ⊆ B) : A ⋐ C :=
  ⟨h.1.of_isClosed_subset isClosed_closure (closure_mono hAB), (closure_mono hAB).trans h.2⟩

theorem mono_right (h : A ⋐ B) (hBC : B ⊆ C) : A ⋐ C := ⟨h.1, h.2.trans hBC⟩

/-- A compact subset of `B` is compactly contained in `B` (in a T₂ space). -/
theorem of_isCompact [T2Space X] (hA : IsCompact A) (hAB : A ⊆ B) : A ⋐ B := by
  rw [CompactlyContained, hA.isClosed.closure_eq]
  exact ⟨hA, hAB⟩

theorem iff_of_isCompact [T2Space X] (hA : IsCompact A) : A ⋐ B ↔ A ⊆ B :=
  ⟨subset, of_isCompact hA⟩

theorem iff_of_isClosed (hA : IsClosed A) : A ⋐ B ↔ IsCompact A ∧ A ⊆ B := by
  rw [CompactlyContained, hA.closure_eq]

theorem trans (h₁ : A ⋐ B) (h₂ : B ⋐ C) : A ⋐ C := h₂.mono_left h₁.subset

end CompactlyContained
