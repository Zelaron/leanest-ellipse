import Mathlib.Analysis.CStarAlgebra.GelfandDuality
import Mathlib.Analysis.Normed.Algebra.Basic
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import Mathlib.Topology.ContinuousMap.StoneWeierstrass

/-!
# Characters of uniform algebras and representing measures

Let `X` be a compact Hausdorff space and let `A ⊆ C(X, ℂ)` be a closed unital subalgebra (a
*uniform algebra*).

## Main results

* `Subalgebra.exists_characterSpace_apply_eq_zero`: in a closed subalgebra of a complex
  commutative Banach algebra, every nonunit is killed by a character (maximal ideals and
  Gelfand–Mazur, via Mathlib's `WeakDual.characterSpace`).
* `WeakDual.CharacterSpace.norm_toCLM_eq_one`: characters of a unital Banach algebra have norm
  one.
* `ContinuousMap.exists_isProbabilityMeasure_integral_eq_of_norm_le_one`: a functional `Λ` on
  `C(X, ℂ)` with `‖Λ‖ ≤ 1` and `Λ 1 = 1` is integration against a probability measure.
* `Subalgebra.exists_isProbabilityMeasure_integral_eq_characterSpace`: every character of a
  uniform algebra has a *representing probability measure* (norm-one Hahn–Banach extension
  followed by the previous item).
* `ContinuousMap.subalgebra_eq_top_of_star_mem`,
  `ContinuousMap.star_mem_topologicalClosure_adjoin`: Stone–Weierstrass consequences.
* `AddCircle.eq_haarAddCircle_of_integral_fourier_eq_zero`: a probability measure on the circle
  whose positive Fourier coefficients vanish is normalized Haar measure.
-/

open MeasureTheory Set Filter Topology
open scoped CompactlySupported ComplexConjugate

noncomputable section

/-! ### Characters -/

namespace WeakDual.CharacterSpace

variable {𝕜 A : Type*} [NontriviallyNormedField 𝕜] [NormedRing A] [NormedAlgebra 𝕜 A]
  [CompleteSpace A] [NormOneClass A]

/-- A character of a unital Banach algebra with `‖1‖ = 1` has norm one. -/
theorem norm_toCLM_eq_one (χ : characterSpace 𝕜 A) : ‖toCLM χ‖ = 1 := by
  refine le_antisymm ((norm_le_norm_one χ).trans_eq norm_one) ?_
  have h := (toCLM χ).le_opNorm 1
  rwa [coe_toCLM, map_one, norm_one, norm_one, mul_one] at h

end WeakDual.CharacterSpace

namespace Subalgebra

/-- In a closed subalgebra `A` of a complex commutative Banach algebra, every nonunit of `A` is
killed by some character of `A` (it lies in a maximal ideal, which is the kernel of a character
by Gelfand–Mazur). -/
theorem exists_characterSpace_apply_eq_zero {B : Type*} [NormedCommRing B] [NormedAlgebra ℂ B]
    [CompleteSpace B] (A : Subalgebra ℂ B) (hA : IsClosed (A : Set B)) {a : A}
    (ha : ¬ IsUnit a) : ∃ χ : WeakDual.characterSpace ℂ A, χ a = 0 := by
  have : CompleteSpace A := @IsClosed.completeSpace_coe _ _ _ _ hA
  exact WeakDual.CharacterSpace.exists_apply_eq_zero ha

end Subalgebra

/-! ### Norm-one functionals on `C(X, ℂ)` are integrals -/

namespace ContinuousMap

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]

/-- Complexification of real continuous functions. -/
private def ofRealL : C(X, ℝ) →ₗ[ℝ] C(X, ℂ) where
  toFun f := ⟨fun x ↦ (f x : ℂ), Complex.continuous_ofReal.comp f.continuous⟩
  map_add' f g := by ext; simp
  map_smul' c f := by ext; simp

omit [CompactSpace X] in
@[simp] private theorem ofRealL_apply (f : C(X, ℝ)) (x : X) : ofRealL f x = (f x : ℂ) := rfl

/-- If `‖Λ‖ ≤ 1` and `Λ 1 = 1`, then `re Λ` is nonnegative on nonnegative real functions. -/
private theorem re_nonneg_of_norm_le_one [Nonempty X] (Λ : StrongDual ℂ C(X, ℂ))
    (hΛnorm : ‖Λ‖ ≤ 1) (hΛone : Λ 1 = 1) (f : C(X, ℝ)) (hf : ∀ x, 0 ≤ f x) :
    0 ≤ (Λ (ofRealL f)).re := by
  let r : ℝ := ‖f‖
  let g : C(X, ℝ) := r • 1 - f
  have hfr (x : X) : f x ≤ r := by
    have h := f.norm_coe_le_norm x
    rwa [Real.norm_eq_abs, abs_of_nonneg (hf x)] at h
  have hgx (x : X) : 0 ≤ g x := by
    simp only [g, ContinuousMap.sub_apply, ContinuousMap.smul_apply, ContinuousMap.one_apply,
      smul_eq_mul, mul_one]
    exact sub_nonneg.mpr (hfr x)
  have hgxr (x : X) : g x ≤ r := by
    simp only [g, ContinuousMap.sub_apply, ContinuousMap.smul_apply, ContinuousMap.one_apply,
      smul_eq_mul, mul_one]
    linarith [hf x]
  have hg_norm : ‖ofRealL g‖ ≤ r := by
    refine (ContinuousMap.norm_le _ (norm_nonneg f)).2 fun x ↦ ?_
    rw [ofRealL_apply, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hgx x)]
    exact hgxr x
  have hΛg : ‖Λ (ofRealL g)‖ ≤ r :=
    calc ‖Λ (ofRealL g)‖ ≤ ‖Λ‖ * ‖ofRealL g‖ := Λ.le_opNorm _
      _ ≤ 1 * r := mul_le_mul hΛnorm hg_norm (norm_nonneg _) zero_le_one
      _ = r := one_mul r
  have hre : (Λ (ofRealL g)).re ≤ r := (Complex.re_le_norm _).trans hΛg
  have hgmap : ofRealL g = (r : ℂ) • (1 : C(X, ℂ)) - ofRealL f := by
    ext x
    simp [g]
  have heval : Λ (ofRealL g) = (r : ℂ) - Λ (ofRealL f) := by
    rw [hgmap, map_sub, map_smul, hΛone, smul_eq_mul, mul_one]
  rw [heval, Complex.sub_re, Complex.ofReal_re] at hre
  linarith

/-- If `‖Λ‖ ≤ 1` and `Λ 1 = 1`, then `Λ` is real on real functions: the uniform norm of
`1 + i s f` has no term linear in `s`. -/
private theorem im_eq_zero_of_norm_le_one [Nonempty X] (Λ : StrongDual ℂ C(X, ℂ))
    (hΛnorm : ‖Λ‖ ≤ 1) (hΛone : Λ 1 = 1) (f : C(X, ℝ)) :
    (Λ (ofRealL f)).im = 0 := by
  let F : C(X, ℂ) := ofRealL f
  let r : ℝ := ‖f‖
  have key (s : ℝ) :
      Complex.normSq (1 + ((s : ℂ) * Complex.I) * Λ F) ≤ 1 + s ^ 2 * r ^ 2 := by
    let g : C(X, ℂ) := 1 + ((s : ℂ) * Complex.I) • F
    have hpoint (x : X) : ‖g x‖ ^ 2 = 1 + s ^ 2 * (f x) ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp [g, F]
      ring
    have harg : 0 ≤ 1 + s ^ 2 * r ^ 2 := by positivity
    have hg : ‖g‖ ≤ Real.sqrt (1 + s ^ 2 * r ^ 2) := by
      refine (ContinuousMap.norm_le _ (Real.sqrt_nonneg _)).2 fun x ↦ ?_
      refine (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp ?_
      rw [Real.sq_sqrt harg, hpoint]
      have hfx : |f x| ≤ r := by
        simpa [r, Real.norm_eq_abs] using f.norm_coe_le_norm x
      have hfsq : (f x) ^ 2 ≤ r ^ 2 := by
        rw [← sq_abs]
        exact (sq_le_sq₀ (abs_nonneg _) (norm_nonneg f)).mpr hfx
      nlinarith [mul_le_mul_of_nonneg_left hfsq (sq_nonneg s)]
    have hΛg : ‖Λ g‖ ≤ ‖g‖ :=
      calc ‖Λ g‖ ≤ ‖Λ‖ * ‖g‖ := Λ.le_opNorm g
        _ ≤ 1 * ‖g‖ := mul_le_mul_of_nonneg_right hΛnorm (norm_nonneg g)
        _ = ‖g‖ := one_mul _
    have hΛg' : ‖Λ g‖ ^ 2 ≤ 1 + s ^ 2 * r ^ 2 :=
      calc ‖Λ g‖ ^ 2 ≤ ‖g‖ ^ 2 := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hΛg
        _ ≤ (Real.sqrt (1 + s ^ 2 * r ^ 2)) ^ 2 :=
            (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mpr hg
        _ = 1 + s ^ 2 * r ^ 2 := Real.sq_sqrt harg
    have hΛgEval : Λ g = 1 + ((s : ℂ) * Complex.I) * Λ F := by
      simp [g, hΛone]
    rwa [hΛgEval, Complex.sq_norm] at hΛg'
  let y : ℝ := (Λ F).im
  by_contra hy
  have hy0 : y ≠ 0 := hy
  let d : ℝ := r ^ 2 + 1
  have hd : 0 < d := by positivity
  let s : ℝ := -y / d
  have hs0 : s ≠ 0 := div_ne_zero (neg_ne_zero.mpr hy0) (ne_of_gt hd)
  have hsd : s * d = -y := by
    dsimp [s]
    field_simp
  have hk := key s
  have hk' : (1 - s * y) ^ 2 + (s * (Λ F).re) ^ 2 ≤ 1 + s ^ 2 * r ^ 2 := by
    simpa [Complex.normSq_apply, y, pow_two, sub_eq_add_neg] using hk
  have hmul := congrArg (fun x : ℝ ↦ s * x) hsd
  have hspos : 0 < s ^ 2 := by positivity
  dsimp [d] at hmul
  nlinarith [sq_nonneg (s * y), sq_nonneg (s * (Λ F).re)]

private theorem integrable_continuousMap {E : Type*} [NormedAddCommGroup E]
    [SecondCountableTopologyEither X E] [MeasurableSpace X] [OpensMeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (f : C(X, E)) : Integrable f μ :=
  Integrable.of_bound f.continuous.aestronglyMeasurable ‖f‖ (ae_of_all _ f.norm_coe_le_norm)

/-- **Norm-one functionals are integrals.**  On a compact Hausdorff space `X`, a continuous linear
functional `Λ` on `C(X, ℂ)` with `‖Λ‖ ≤ 1` and `Λ 1 = 1` is integration against a probability
measure. -/
theorem exists_isProbabilityMeasure_integral_eq_of_norm_le_one [T2Space X] [MeasurableSpace X]
    [BorelSpace X] (Λ : StrongDual ℂ C(X, ℂ)) (hΛnorm : ‖Λ‖ ≤ 1) (hΛone : Λ 1 = 1) :
    ∃ μ : Measure X, IsProbabilityMeasure μ ∧ ∀ f : C(X, ℂ), ∫ x, f x ∂μ = Λ f := by
  have : Nonempty X := by
    by_contra hX
    rw [not_nonempty_iff] at hX
    have h10 : (1 : C(X, ℂ)) = 0 := Subsingleton.elim _ _
    rw [h10, map_zero] at hΛone
    exact zero_ne_one hΛone
  -- the positive functional `f ↦ re Λ f` on `C_c(X, ℝ)`
  let L : C_c(X, ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun f ↦ (Λ (ofRealL f.toContinuousMap)).re
      map_add' := fun f g ↦ by
        have : (f + g).toContinuousMap = f.toContinuousMap + g.toContinuousMap := rfl
        simp only [this, map_add, Complex.add_re]
      map_smul' := fun c f ↦ by
        have : (c • f).toContinuousMap = c • f.toContinuousMap := rfl
        simp only [this, map_smul, RingHom.id_apply, smul_eq_mul]
        rw [LinearMapClass.map_smul_of_tower Λ c, Complex.real_smul, Complex.re_ofReal_mul] }
  let P : C_c(X, ℝ) →ₚ[ℝ] ℝ := PositiveLinearMap.mk₀ L fun f hf ↦
    re_nonneg_of_norm_le_one Λ hΛnorm hΛone f.toContinuousMap fun x ↦
      (CompactlySupportedContinuousMap.le_def.1 hf) x
  let μ : Measure X := RealRMK.rieszMeasure P
  have hμ : ∀ f : C_c(X, ℝ), ∫ x, f x ∂μ = (Λ (ofRealL f.toContinuousMap)).re :=
    RealRMK.integral_rieszMeasure P
  have : IsFiniteMeasure μ := by dsimp [μ]; infer_instance
  have hprob : IsProbabilityMeasure μ := by
    have h1 := hμ ⟨1, HasCompactSupport.of_compactSpace 1⟩
    have hone : ofRealL (⟨1, HasCompactSupport.of_compactSpace 1⟩ : C_c(X, ℝ)).toContinuousMap =
        (1 : C(X, ℂ)) := by
      ext x
      simp
    rw [hone, hΛone, Complex.one_re] at h1
    have h1' : ∫ _ : X, (1 : ℝ) ∂μ = 1 := h1
    rw [integral_const, smul_eq_mul, mul_one] at h1'
    exact isProbabilityMeasure_iff_real.2 h1'
  refine ⟨μ, hprob, fun f ↦ ?_⟩
  have hreal (g : C(X, ℝ)) : ∫ x, (g x : ℂ) ∂μ = Λ (ofRealL g) := by
    rw [integral_complex_ofReal]
    have hr : ∫ x, g x ∂μ = (Λ (ofRealL g)).re := hμ ⟨g, HasCompactSupport.of_compactSpace g⟩
    apply Complex.ext
    · simpa using hr
    · simpa using (im_eq_zero_of_norm_le_one Λ hΛnorm hΛone g).symm
  let fr : C(X, ℝ) := ⟨fun x ↦ (f x).re, Complex.continuous_re.comp f.continuous⟩
  let fi : C(X, ℝ) := ⟨fun x ↦ (f x).im, Complex.continuous_im.comp f.continuous⟩
  have hf : f = ofRealL fr + Complex.I • ofRealL fi := by
    ext x
    apply Complex.ext <;> simp [fr, fi]
  have hint : ∀ g : C(X, ℝ), Integrable (fun x ↦ (g x : ℂ)) μ := fun g ↦
    integrable_continuousMap μ (ofRealL g)
  calc ∫ x, f x ∂μ = ∫ x, ((fr x : ℂ) + Complex.I * (fi x : ℂ)) ∂μ := by
        congr 1
        ext x
        apply Complex.ext <;> simp [fr, fi]
    _ = ∫ x, (fr x : ℂ) ∂μ + Complex.I * ∫ x, (fi x : ℂ) ∂μ := by
        rw [integral_add (hint fr) ((hint fi).const_mul _), integral_const_mul]
    _ = Λ f := by
        rw [hreal, hreal]
        conv_rhs => rw [hf, map_add, map_smul, smul_eq_mul]

end ContinuousMap

/-! ### Representing measures of characters of uniform algebras -/

namespace Subalgebra

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]

/-- A character `χ` of a closed unital subalgebra `A ⊆ C(X, ℂ)` has a norm-one Hahn–Banach
extension `Λ` to `C(X, ℂ)`; it satisfies `Λ 1 = 1`. -/
theorem exists_extension_characterSpace (A : Subalgebra ℂ C(X, ℂ))
    (hA : IsClosed (A : Set C(X, ℂ))) (χ : WeakDual.characterSpace ℂ A) :
    ∃ Λ : StrongDual ℂ C(X, ℂ), (∀ f : A, Λ f = χ f) ∧ ‖Λ‖ = 1 ∧ Λ 1 = 1 := by
  have : Nonempty X := by
    by_contra hX
    rw [not_nonempty_iff] at hX
    have : Subsingleton A := ⟨fun a b ↦ Subtype.ext (Subsingleton.elim _ _)⟩
    exact IsEmpty.false χ
  have : CompleteSpace A := @IsClosed.completeSpace_coe _ _ _ _ hA
  have : NormOneClass A := ⟨by
    change ‖(1 : C(X, ℂ))‖ = 1
    exact norm_one⟩
  obtain ⟨Λ, hΛ, hΛnorm⟩ := exists_extension_norm_eq A.toSubmodule
    (WeakDual.CharacterSpace.toCLM χ : StrongDual ℂ A.toSubmodule)
  refine ⟨Λ, hΛ, ?_, ?_⟩
  · rw [hΛnorm]
    exact WeakDual.CharacterSpace.norm_toCLM_eq_one χ
  · exact (hΛ (1 : A)).trans (map_one χ)

/-- **Representing measures.**  Let `A` be a closed unital subalgebra of `C(X, ℂ)`, `X` compact
Hausdorff.  Every character `χ` of `A` is represented by a probability measure `μ` on `X`:
`χ f = ∫ f dμ` for all `f ∈ A`. -/
theorem exists_isProbabilityMeasure_integral_eq_characterSpace [T2Space X] [MeasurableSpace X]
    [BorelSpace X] (A : Subalgebra ℂ C(X, ℂ)) (hA : IsClosed (A : Set C(X, ℂ)))
    (χ : WeakDual.characterSpace ℂ A) :
    ∃ μ : Measure X, IsProbabilityMeasure μ ∧ ∀ f : A, ∫ x, (f : C(X, ℂ)) x ∂μ = χ f := by
  obtain ⟨Λ, hΛ, hΛnorm, hΛone⟩ := exists_extension_characterSpace A hA χ
  obtain ⟨μ, hμ, hrep⟩ :=
    ContinuousMap.exists_isProbabilityMeasure_integral_eq_of_norm_le_one Λ hΛnorm.le hΛone
  exact ⟨μ, hμ, fun f ↦ (hrep f).trans (hΛ f)⟩

end Subalgebra

/-! ### Stone–Weierstrass consequences -/

namespace ContinuousMap

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]

/-- A closed subalgebra of `C(X, ℂ)` (for compact `X`) which is closed under conjugation and
separates points is all of `C(X, ℂ)`. -/
theorem subalgebra_eq_top_of_star_mem (A : Subalgebra ℂ C(X, ℂ))
    (hA : IsClosed (A : Set C(X, ℂ))) (hstar : ∀ f ∈ A, star f ∈ A) (hsep : A.SeparatesPoints) :
    A = ⊤ := by
  let Astar : StarSubalgebra ℂ C(X, ℂ) := { A with star_mem' := fun hf ↦ hstar _ hf }
  have hdense : Astar.topologicalClosure = ⊤ :=
    ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints Astar hsep
  have hle : Astar.topologicalClosure ≤ Astar :=
    StarSubalgebra.topologicalClosure_minimal le_rfl hA
  have hAstar : Astar = ⊤ := top_unique (hdense ▸ hle)
  refine eq_top_iff.2 fun f _ ↦ ?_
  have : f ∈ Astar := hAstar ▸ StarSubalgebra.mem_top
  exact this

/-- If the conjugates of a set `s` of generators lie in the uniform closure `A` of the algebra
generated by `s`, then `A` is closed under conjugation. -/
theorem star_mem_topologicalClosure_adjoin {s : Set C(X, ℂ)}
    (hs : ∀ g ∈ s, star g ∈ (Algebra.adjoin ℂ s).topologicalClosure) {f : C(X, ℂ)}
    (hf : f ∈ (Algebra.adjoin ℂ s).topologicalClosure) :
    star f ∈ (Algebra.adjoin ℂ s).topologicalClosure := by
  set A := (Algebra.adjoin ℂ s).topologicalClosure
  have hpoly : ∀ p ∈ Algebra.adjoin ℂ s, star p ∈ A := by
    intro p hp
    induction hp using Algebra.adjoin_induction with
    | mem g hg => exact hs g hg
    | algebraMap c =>
        rw [← algebraMap_star_comm]
        exact A.algebraMap_mem _
    | add x y _ _ hx hy => rw [star_add]; exact A.add_mem hx hy
    | mul x y _ _ hx hy => rw [star_mul]; exact A.mul_mem hy hx
  exact (Subalgebra.isClosed_topologicalClosure _).closure_subset
    (map_mem_closure continuous_star hf hpoly)

end ContinuousMap

/-! ### Probability measures on the circle -/

namespace AddCircle

variable {T : ℝ} [Fact (0 < T)]

/-- Integration against a finite measure, as a continuous linear functional on `C(X, ℂ)`. -/
private def integralCLM {X : Type*} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X]
    [BorelSpace X] (μ : Measure X) [IsFiniteMeasure μ] : C(X, ℂ) →L[ℂ] ℂ :=
  (L1.integralCLM' ℂ).comp (ContinuousMap.toLp 1 μ ℂ)

private theorem integralCLM_apply {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsFiniteMeasure μ] (f : C(X, ℂ)) :
    integralCLM μ f = ∫ x, f x ∂μ := by
  rw [integralCLM, ContinuousLinearMap.comp_apply, ← L1.integral_eq' ℂ, L1.integral_eq_integral]
  exact integral_congr_ae (ContinuousMap.coeFn_toLp (p := 1) μ f)

/-- Finite measures on the additive circle are determined by their Fourier coefficients. -/
theorem measure_eq_of_integral_fourier_eq {μ ν : Measure (AddCircle T)} [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (h : ∀ n : ℤ, ∫ x, fourier n x ∂μ = ∫ x, fourier n x ∂ν) : μ = ν := by
  have hdense : Dense (Submodule.span ℂ (range (fourier (T := T))) : Set C(AddCircle T, ℂ)) :=
    Submodule.dense_iff_topologicalClosure_eq_top.mpr span_fourier_closure_eq_top
  have hI : integralCLM μ = integralCLM ν := by
    apply ContinuousLinearMap.ext_on hdense
    rintro f ⟨n, rfl⟩
    simpa [integralCLM_apply] using h n
  refine ext_of_forall_integral_eq_of_IsFiniteMeasure fun f ↦ ?_
  let fℂ : C(AddCircle T, ℂ) := ⟨fun x ↦ (f x : ℂ), Complex.continuous_ofReal.comp f.continuous⟩
  have hf := DFunLike.congr_fun hI fℂ
  simp only [integralCLM_apply, fℂ, ContinuousMap.coe_mk] at hf
  rw [integral_complex_ofReal, integral_complex_ofReal] at hf
  exact_mod_cast hf

/-- The Fourier coefficients of normalized Haar measure. -/
theorem integral_fourier_haarAddCircle (n : ℤ) :
    ∫ x, fourier n x ∂(haarAddCircle : Measure (AddCircle T)) = if n = 0 then 1 else 0 := by
  have h := congrFun (fourierCoeff_fourier (T := T) n) 0
  simpa [fourierCoeff, fourier_zero, Pi.single_apply, eq_comm] using h

/-- A probability measure on the additive circle whose positive Fourier coefficients vanish is
normalized Haar measure (the negative coefficients vanish by conjugation). -/
theorem eq_haarAddCircle_of_integral_fourier_eq_zero (ν : Measure (AddCircle T))
    [IsProbabilityMeasure ν] (h : ∀ n : ℕ, 0 < n → ∫ x, fourier n x ∂ν = 0) :
    ν = haarAddCircle := by
  apply measure_eq_of_integral_fourier_eq
  intro n
  rw [integral_fourier_haarAddCircle]
  rcases lt_trichotomy n 0 with hn | rfl | hn
  · rw [ite_eq_right hn.ne]
    obtain ⟨k, hk⟩ : ∃ k : ℕ, n = -(k : ℤ) := ⟨n.natAbs, by omega⟩
    subst hk
    have hk0 : 0 < k := by omega
    calc ∫ x, fourier (-(k : ℤ)) x ∂ν = ∫ x, conj (fourier (k : ℤ) x) ∂ν := by
          congr 1
          ext x
          exact fourier_neg
      _ = conj (∫ x, fourier (k : ℤ) x ∂ν) := integral_conj
      _ = 0 := by rw [h k hk0, map_zero]
  · simp
  · rw [ite_eq_right hn.ne']
    obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = (k : ℤ) := ⟨n.toNat, by omega⟩
    exact h k (by omega)

end AddCircle
