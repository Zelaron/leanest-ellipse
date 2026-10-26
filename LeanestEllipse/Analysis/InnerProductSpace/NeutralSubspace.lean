import LeanestEllipse.Analysis.Normed.Algebra.RieszIdempotent
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Idempotent

/-!
# Common neutral subspaces of self-adjoint pencils

Let `H₀, H₁` be bounded self-adjoint operators on a nonzero complex Hilbert space such that every
member `cos θ • H₀ + sin θ • H₁` of the real pencil they span is invertible.  We show that there
is a nonzero closed subspace `M` which is *neutral* for the whole pencil
(`⟪(cos θ • H₀ + sin θ • H₁) x, y⟫ = 0` for `x y ∈ M`) and which every member of the pencil maps
onto `Mᗮ` ([Hägg, Lemma 8]).

The subspace is the range of the Riesz idempotent of the upper half-plane of `R = H₀⁻¹ H₁`: the
spectrum of `R` avoids the real axis, and the adjoint of that idempotent is conjugate, via `H₀`, to
the complementary idempotent.

## Main results

* `forall_isUnit_cos_smul_add_sin_smul_iff`: in any real algebra, `cos θ • J + sin θ • K` is
  invertible for all `θ` iff `J` is invertible and `J⁻¹ K` has empty real spectrum.
* `IsIdempotentElem.inner_apply_eq_zero_of_adjoint_mul_eq`,
  `IsIdempotentElem.map_range_eq_orthogonal_of_adjoint_mul_eq`: an idempotent `P` with
  `P† * G = G * (1 - P)` has a `G`-neutral range, mapped onto its orthogonal complement by `G`
  if `G` is invertible.
* `exists_neutral_subspace_of_forall_isUnit`: the general form of Lemma 8, for all complex
  combinations `c • H₀ + d • H₁`.
* `exists_common_neutral_subspace`: [Hägg, Lemma 8].
* `exists_common_neutral_subspace_orthogonalProjection`: the same, with neutrality in the form
  `P_M G|_M = 0`.

## References

* C. Hägg, *An ellipse criterion for exact nonuniqueness in the planar interior Radon problem*.
-/

noncomputable section

open scoped InnerProductSpace InnerProduct

/-! ### Real pencils in real algebras -/

section Pencil

variable {A : Type*} [Ring A] [Algebra ℝ A]

private theorem isUnit_real_smul {c : ℝ} (hc : c ≠ 0) {x : A} (hx : IsUnit x) :
    IsUnit (c • x) := by
  rw [Algebra.smul_def]
  exact ((isUnit_iff_ne_zero.mpr hc).map (algebraMap ℝ A)).mul hx

private theorem isUnit_of_isUnit_real_smul {c : ℝ} (hc : c ≠ 0) {x : A} (hx : IsUnit (c • x)) :
    IsUnit x := by
  have := isUnit_real_smul (inv_ne_zero hc) hx
  rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this

/-- The real pencil `cos θ • J + sin θ • K` is invertible for every `θ` if and only if `J` is
invertible and `J⁻¹ K` has no real spectrum. -/
theorem forall_isUnit_cos_smul_add_sin_smul_iff {J K : A} :
    (∀ θ : ℝ, IsUnit (Real.cos θ • J + Real.sin θ • K)) ↔
      IsUnit J ∧ spectrum ℝ (Ring.inverse J * K) = ∅ := by
  constructor
  · intro h
    have hJ : IsUnit J := by simpa using h 0
    refine ⟨hJ, Set.eq_empty_of_forall_notMem fun r hr ↦ hr ?_⟩
    -- the angle `θ = arctan r + π / 2` detects the real point `r`
    have hθ := h (Real.arctan r + Real.pi / 2)
    rw [Real.cos_add_pi_div_two, Real.sin_add_pi_div_two, Real.sin_arctan, Real.cos_arctan]
      at hθ
    have hs : (0 : ℝ) < √(1 + r ^ 2) := Real.sqrt_pos.mpr (by positivity)
    have hfactor : -(r / √(1 + r ^ 2)) • J + (1 / √(1 + r ^ 2)) • K =
        (1 / √(1 + r ^ 2)) • (J * (Ring.inverse J * K - algebraMap ℝ A r)) := by
      rw [mul_sub, ← mul_assoc, Ring.mul_inverse_cancel J hJ, one_mul,
        Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one, smul_sub, smul_smul, neg_smul,
        div_eq_mul_inv, div_eq_mul_inv]
      rw [one_mul, mul_comm r]
      abel
    rw [hfactor] at hθ
    have h1 := isUnit_of_isUnit_real_smul (one_div_ne_zero hs.ne') hθ
    rw [hJ.mul_left_iff] at h1
    exact IsUnit.sub_iff.mp h1
  · rintro ⟨hJ, hspec⟩ θ
    have hJK : J * (Ring.inverse J * K) = K := by
      rw [← mul_assoc, Ring.mul_inverse_cancel J hJ, one_mul]
    by_cases hsin : Real.sin θ = 0
    · have hcos : Real.cos θ ≠ 0 := by
        intro hcos
        have := Real.sin_sq_add_cos_sq θ
        rw [hsin, hcos] at this
        norm_num at this
      rw [hsin, zero_smul, add_zero]
      exact isUnit_real_smul hcos hJ
    · set t : ℝ := -(Real.cos θ / Real.sin θ)
      have ht : t ∉ spectrum ℝ (Ring.inverse J * K) := by simp [hspec]
      have hfactor : Real.cos θ • J + Real.sin θ • K =
          J * (Real.sin θ • (Ring.inverse J * K - algebraMap ℝ A t)) := by
        rw [mul_smul_comm, mul_sub, hJK, Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one,
          smul_sub, smul_smul]
        simp only [t, mul_neg, mul_div_cancel₀ _ hsin, neg_smul, sub_neg_eq_add, add_comm]
      rw [hfactor]
      exact hJ.mul (isUnit_real_smul hsin (IsUnit.sub_iff.mp (spectrum.notMem_iff.mp ht)))

/-- In a complex algebra, empty real spectrum means that the complex spectrum avoids the real
axis. -/
theorem spectrum.im_ne_zero_of_spectrum_real_eq_empty {B : Type*} [Ring B] [Algebra ℂ B]
    {a : B} (h : spectrum ℝ a = ∅) : ∀ z ∈ spectrum ℂ a, z.im ≠ 0 := by
  intro z hz him
  have hz' : (z.re : ℂ) ∈ spectrum ℂ a := by
    rwa [show (z.re : ℂ) = z from Complex.ext rfl (by simp [him])]
  have : z.re ∈ spectrum ℝ a := by
    rw [← spectrum.preimage_algebraMap ℂ]
    exact hz'
  simp [h] at this

/-- For self-adjoint `J, K` with `J` invertible, the adjoint of `J⁻¹ K` is intertwined with
`J⁻¹ K` by `J`. -/
theorem IsSelfAdjoint.star_inverse_mul_mul_eq {B : Type*} [Ring B] [StarRing B] {J K : B}
    (hJ : IsSelfAdjoint J) (hK : IsSelfAdjoint K) (hJu : IsUnit J) :
    star (Ring.inverse J * K) * J = J * (Ring.inverse J * K) := by
  rw [star_mul, hK.star_eq, ← Ring.inverse_star, hJ.star_eq, mul_assoc,
    Ring.inverse_mul_cancel J hJu, mul_one, ← mul_assoc, Ring.mul_inverse_cancel J hJu, one_mul]

end Pencil

/-! ### Covariant idempotents -/

section Covariant

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

/-- If `P† * G = G * (1 - P)` for an idempotent `P`, then the range of `P` is `G`-neutral. -/
theorem IsIdempotentElem.inner_apply_eq_zero_of_adjoint_mul_eq {P G : E →L[𝕜] E}
    (hP : IsIdempotentElem P) (hcov : P† * G = G * (1 - P)) {x y : E}
    (hx : x ∈ LinearMap.range (P : E →ₗ[𝕜] E)) (hy : y ∈ LinearMap.range (P : E →ₗ[𝕜] E)) :
    ⟪G x, y⟫ = 0 := by
  obtain ⟨u, rfl⟩ := hx
  obtain ⟨v, rfl⟩ := hy
  have hzero : (P†) (G (P u)) = 0 := by
    have h2 : ((1 - P) * P) u = 0 := by rw [hP.one_sub_mul_self]; rfl
    calc (P†) (G (P u)) = (P† * G) (P u) := rfl
      _ = (G * (1 - P)) (P u) := by rw [hcov]
      _ = G (((1 - P) * P) u) := rfl
      _ = 0 := by rw [h2, map_zero]
  change ⟪G (P u), P v⟫ = 0
  rw [← ContinuousLinearMap.adjoint_inner_left, hzero, inner_zero_left]

private theorem adjoint_one_sub_mul_eq {P G : E →L[𝕜] E} (hcov : P† * G = G * (1 - P)) :
    (1 - P)† * G = G * (1 - (1 - P)) := by
  rw [map_sub, ContinuousLinearMap.adjoint_one, sub_mul, one_mul, hcov, sub_sub_cancel, mul_sub,
    mul_one, sub_sub_cancel]

/-- If `P† * G = G * (1 - P)` for an idempotent `P` and an invertible `G`, then `G` maps the
range of `P` onto its orthogonal complement. -/
theorem IsIdempotentElem.map_range_eq_orthogonal_of_adjoint_mul_eq {P G : E →L[𝕜] E}
    (hP : IsIdempotentElem P) (hcov : P† * G = G * (1 - P)) (hG : IsUnit G) :
    (LinearMap.range (P : E →ₗ[𝕜] E)).map (G : E →ₗ[𝕜] E) =
      (LinearMap.range (P : E →ₗ[𝕜] E))ᗮ := by
  have hneutral : ∀ x ∈ LinearMap.range (P : E →ₗ[𝕜] E),
      G x ∈ (LinearMap.range (P : E →ₗ[𝕜] E))ᗮ := fun x hx ↦
    (Submodule.mem_orthogonal' _ _).mpr fun y hy ↦
      hP.inner_apply_eq_zero_of_adjoint_mul_eq hcov hx hy
  have hneutral' : ∀ x ∈ LinearMap.range ((1 - P : E →L[𝕜] E) : E →ₗ[𝕜] E),
      G x ∈ (LinearMap.range ((1 - P : E →L[𝕜] E) : E →ₗ[𝕜] E))ᗮ := fun x hx ↦
    (Submodule.mem_orthogonal' _ _).mpr fun y hy ↦
      hP.one_sub.inner_apply_eq_zero_of_adjoint_mul_eq (adjoint_one_sub_mul_eq hcov) hx hy
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact hneutral x hx
  · intro y hy
    obtain ⟨x, rfl⟩ := (ContinuousLinearMap.isUnit_iff_bijective.mp hG).2 y
    have he : P x ∈ LinearMap.range (P : E →ₗ[𝕜] E) := ⟨x, rfl⟩
    have hw : (1 - P) x ∈ LinearMap.range ((1 - P : E →L[𝕜] E) : E →ₗ[𝕜] E) := ⟨x, rfl⟩
    have hxe : x = P x + (1 - P) x := by simp
    have hGwM : G ((1 - P) x) ∈ (LinearMap.range (P : E →ₗ[𝕜] E))ᗮ := by
      have hsplit : G (P x) + G ((1 - P) x) = G x := by
        rw [← map_add]
        simp
      have : G ((1 - P) x) = G x - G (P x) := by rw [← hsplit, add_sub_cancel_left]
      rw [this]
      exact Submodule.sub_mem _ hy (hneutral _ he)
    have hGw : G ((1 - P) x) = 0 := by
      refine ext_inner_left 𝕜 fun t ↦ ?_
      have ht : t = P t + (1 - P) t := by simp
      have h1 : ⟪P t, G ((1 - P) x)⟫ = 0 :=
        Submodule.inner_right_of_mem_orthogonal (LinearMap.mem_range_self (P : E →ₗ[𝕜] E) t) hGwM
      have h2 : ⟪(1 - P) t, G ((1 - P) x)⟫ = 0 :=
        Submodule.inner_right_of_mem_orthogonal
          (LinearMap.mem_range_self ((1 - P : E →L[𝕜] E) : E →ₗ[𝕜] E) t) (hneutral' _ hw)
      rw [ht, inner_add_left, inner_zero_right, h1, h2, add_zero]
    have hw0 : (1 - P) x = 0 :=
      (ContinuousLinearMap.isUnit_iff_bijective.mp hG).1 (by rw [hGw, map_zero])
    refine ⟨P x, he, ?_⟩
    change G (P x) = G x
    rw [← sub_eq_zero, ← map_sub, show P x - x = -((1 - P) x) by simp, hw0, neg_zero, map_zero]

end Covariant

/-! ### The common neutral subspace -/

section Neutral

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **Common neutral subspace**, general form.  Let `H₀, H₁` be self-adjoint operators on a
nonzero complex Hilbert space such that `cos θ • H₀ + sin θ • H₁` is invertible for every `θ`.
Then there is a nonzero closed subspace `M` which is neutral for every complex combination
`c • H₀ + d • H₁`, and every invertible such combination maps `M` onto `Mᗮ`. -/
theorem exists_neutral_subspace_of_forall_isUnit [Nontrivial H] {H₀ H₁ : H →L[ℂ] H}
    (h₀ : IsSelfAdjoint H₀) (h₁ : IsSelfAdjoint H₁)
    (hunit : ∀ θ : ℝ, IsUnit (Real.cos θ • H₀ + Real.sin θ • H₁)) :
    ∃ M : Submodule ℂ H, IsClosed (M : Set H) ∧ M ≠ ⊥ ∧
      (∀ c d : ℂ, ∀ x ∈ M, ∀ y ∈ M, ⟪(c • H₀ + d • H₁) x, y⟫_ℂ = 0) ∧
      ∀ c d : ℂ, IsUnit (c • H₀ + d • H₁) →
        M.map (c • H₀ + d • H₁ : H →L[ℂ] H).toLinearMap = Mᗮ := by
  obtain ⟨hJ, hspec⟩ := forall_isUnit_cos_smul_add_sin_smul_iff.mp hunit
  set R : H →L[ℂ] H := Ring.inverse H₀ * H₁ with hR
  have hRim : ∀ z ∈ spectrum ℂ R, z.im ≠ 0 := spectrum.im_ne_zero_of_spectrum_real_eq_empty hspec
  have hstarR : star R * (hJ.unit : H →L[ℂ] H) = hJ.unit * R := by
    rw [hJ.unit_spec]
    exact h₀.star_inverse_mul_mul_eq h₁ hJ
  obtain ⟨P, hP, hcomm, hne0, -, hcov⟩ := exists_isIdempotentElem_upperHalfPlane R hRim
  have hcovJ : P† * H₀ = H₀ * (1 - P) := by
    simpa [hJ.unit_spec, ContinuousLinearMap.star_eq_adjoint] using hcov hJ.unit hstarR
  have hPR : Commute P R := hcomm R (Commute.refl R)
  have hH₁ : H₁ = H₀ * R := by
    rw [hR, ← mul_assoc, Ring.mul_inverse_cancel H₀ hJ, one_mul]
  have hP0 : P ≠ 0 := hne0.mpr
    (Set.exists_im_pos_and_exists_im_neg_of_star_eq (spectrum.nonempty R) hRim
      (spectrum.star_eq_self_of_star_mul_eq_mul hJ.unit hstarR)).1
  -- covariance of every member of the complex pencil
  have hcovG : ∀ c d : ℂ, P† * (c • H₀ + d • H₁) = (c • H₀ + d • H₁) * (1 - P) := by
    intro c d
    have hcomm' : (1 - P) * R = R * (1 - P) := by
      rw [sub_mul, mul_sub, one_mul, mul_one, hPR.eq]
    rw [hH₁, mul_add, mul_smul_comm, mul_smul_comm, hcovJ, ← mul_assoc, hcovJ, add_mul,
      smul_mul_assoc, smul_mul_assoc, mul_assoc, mul_assoc, hcomm']
  refine ⟨LinearMap.range (P : H →ₗ[ℂ] H),
    ContinuousLinearMap.IsIdempotentElem.isClosed_range hP, ?_,
    fun c d x hx y hy ↦ hP.inner_apply_eq_zero_of_adjoint_mul_eq (hcovG c d) hx hy,
    fun c d hG ↦ hP.map_range_eq_orthogonal_of_adjoint_mul_eq (hcovG c d) hG⟩
  intro hbot
  apply hP0
  ext x
  have hx : P x ∈ LinearMap.range (P : H →ₗ[ℂ] H) := ⟨x, rfl⟩
  rw [hbot, Submodule.mem_bot] at hx
  simp [hx]

omit [CompleteSpace H] in
private theorem real_pencil_eq_complex (H₀ H₁ : H →L[ℂ] H) (θ : ℝ) :
    Real.cos θ • H₀ + Real.sin θ • H₁ = (Real.cos θ : ℂ) • H₀ + (Real.sin θ : ℂ) • H₁ :=
  rfl

/-- **Common neutral subspace** [Hägg, Lemma 8].  Let `H₀, H₁` be bounded self-adjoint operators on
a nonzero complex Hilbert space such that `cos θ • H₀ + sin θ • H₁` is invertible for every
`θ : ℝ`.  Then there is a nonzero closed subspace `M` such that, for every `θ`, `M` is neutral for
`cos θ • H₀ + sin θ • H₁` and `cos θ • H₀ + sin θ • H₁` maps `M` onto `Mᗮ`. -/
theorem exists_common_neutral_subspace [Nontrivial H] {H₀ H₁ : H →L[ℂ] H}
    (h₀ : IsSelfAdjoint H₀) (h₁ : IsSelfAdjoint H₁)
    (hunit : ∀ θ : ℝ, IsUnit (Real.cos θ • H₀ + Real.sin θ • H₁)) :
    ∃ M : Submodule ℂ H, IsClosed (M : Set H) ∧ M ≠ ⊥ ∧ ∀ θ : ℝ,
      (∀ x ∈ M, ∀ y ∈ M, ⟪(Real.cos θ • H₀ + Real.sin θ • H₁) x, y⟫_ℂ = 0) ∧
      M.map (Real.cos θ • H₀ + Real.sin θ • H₁ : H →L[ℂ] H).toLinearMap = Mᗮ := by
  obtain ⟨M, hMc, hM0, hneutral, hmap⟩ := exists_neutral_subspace_of_forall_isUnit h₀ h₁ hunit
  refine ⟨M, hMc, hM0, fun θ ↦ ⟨?_, ?_⟩⟩
  · rw [real_pencil_eq_complex]
    exact hneutral _ _
  · rw [real_pencil_eq_complex]
    exact hmap _ _ (real_pencil_eq_complex H₀ H₁ θ ▸ hunit θ)

/-- [Hägg, Lemma 8], in the form `P_M G|_M = 0`: the compression of every member `G` of the pencil
to the common neutral subspace `M` vanishes. -/
theorem exists_common_neutral_subspace_orthogonalProjection [Nontrivial H] {H₀ H₁ : H →L[ℂ] H}
    (h₀ : IsSelfAdjoint H₀) (h₁ : IsSelfAdjoint H₁)
    (hunit : ∀ θ : ℝ, IsUnit (Real.cos θ • H₀ + Real.sin θ • H₁)) :
    ∃ (M : Submodule ℂ H) (_ : CompleteSpace M), M ≠ ⊥ ∧ ∀ θ : ℝ,
      M.orthogonalProjectionOnto ∘L (Real.cos θ • H₀ + Real.sin θ • H₁) ∘L M.subtypeL = 0 ∧
      M.map (Real.cos θ • H₀ + Real.sin θ • H₁ : H →L[ℂ] H).toLinearMap = Mᗮ := by
  obtain ⟨M, hMc, hM0, hM⟩ := exists_common_neutral_subspace h₀ h₁ hunit
  have : CompleteSpace M := hMc.completeSpace_coe
  refine ⟨M, this, hM0, fun θ ↦ ⟨ContinuousLinearMap.ext fun x ↦ Subtype.ext ?_, (hM θ).2⟩⟩
  have h0 : M.starProjection ((Real.cos θ • H₀ + Real.sin θ • H₁) x) = 0 :=
    (M.starProjection_apply_eq_zero_iff).mpr
      ((Submodule.mem_orthogonal' _ _).mpr fun y hy ↦ (hM θ).1 x x.2 y hy)
  simpa using h0

end Neutral
