import LeanestEllipse.Analysis.InnerProductSpace.ApproxEigenvalue
import LeanestEllipse.Analysis.InnerProductSpace.Wold
import LeanestEllipse.MeasureTheory.ComplexMeasure
import LeanestEllipse.Topology.ContinuousMap.UniformAlgebra
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Topology.Metrizable.Urysohn

/-!
# The Hardy-model reduction [Hägg, Lemma 7]

Let `X ⊆ Σ = {(q, z) ∈ 𝕋 × ℂ | z = q z̄}` be compact and let `η ≠ 0` be a complex measure on `X`
annihilating all monomials `z^j q^ℓ` with `ℓ ≥ 1`.  Then there are a nonzero Hilbert space `𝓔`
and an operator `A` on `𝓔` such that for every `θ`,
`σ(e^{-iθ} A + e^{iθ} A†) ⊆ {p ∈ ℝ | (e^{2iθ}, p e^{iθ}) ∈ X}`
(`LeanestEllipse.hardy_model_reduction`).

## Structure of the proof

1. *Möbius pairs* (abstract operator theory).  A pair `(T, S)` of operators on a Hilbert space
   with `T` an isometry, `TS = ST` and `T† S = S†` is a `LeanestEllipse.IsMobiusPair`.  On the
   wandering subspace `𝓔 = ker T†` the compression `A = P_𝓔 S|_𝓔` (`LeanestEllipse.mobiusSymbol`)
   satisfies `S e = A e + T A† e` (`IsMobiusPair.apply_eq_mobiusSymbol_add`), i.e. `S ≃ M_{A+qA†}`
   in the Wold model.  Finite *wave packets* `Σ_{k ≤ N} w̄ᵏ Tᵏ e` turn approximate eigenvectors of
   the normal operator `A + w A†` (`|w| = 1`) into joint approximate eigenvectors of `(T, S)`
   (`IsMobiusPair.exists_seq_joint_approx_eigenvector`).
2. *Multiplication operators* on `L²(μ)` for a finite measure on a compact space, and the joint
   spectral localization: joint approximate eigenvalues of `(M_q, M_z)` are values of `(q, z)`.
3. *The uniform algebra* `𝒜 = closure ℂ[q, z]`: the moment conditions and `η ≠ 0` show that `q`
   is not invertible in `𝒜`, hence is killed by a character, which has a representing
   probability measure `μ`; its `q`-marginal is Haar measure.
4. *The Hardy premodel*: `H = closure 𝒜` in `L²(μ)`, `T = M_q|_H`, `S = M_z|_H` form a Möbius
   pair, `T` is a pure isometry, and `1 ∈ ker T†`, so `𝓔 ≠ 0`.

## Main results

* `LeanestEllipse.hardy_model_reduction`: [Hägg, Lemma 7] for compact `X ⊆ Σ ⊆ ℂ × ℂ`.
* `LeanestEllipse.hardy_model_reduction_of_continuousMap`: the same for a compact metrizable
  space `X` with continuous coordinates `q, z` (`|q| = 1`, `z = q z̄`, `(q, z)` injective).
* Intermediate results: `exists_characterSpace_isProbabilityMeasure` (the killed character and
  its representing probability measure), `map_circleLift_eq_haarAddCircle_of_characterSpace`
  (the `q`-marginal is Haar), `isMobiusPair_hardy` (`T† S = S†`, hence `S† T = S`),
  `isPureIsometry_hardyShift`, `isHilbertSum_hardy` (Wold decomposition),
  `wanderingSubspace_hardyShift_ne_bot` (`𝓔 ≠ 0`), `IsMobiusPair.apply_eq_mobiusSymbol_add` and
  `IsMobiusPair.apply_woldEquiv_symm_single` (`S ≃ M_{A + qA†}`),
  `exists_eq_of_mem_spectrum_rotated_mobiusSymbol` (the fiber-spectrum inclusion).
-/

noncomputable section

universe u

open Filter Topology Set ContinuousLinearMap
open scoped ENNReal ComplexConjugate InnerProductSpace

namespace LeanestEllipse

/-! ### Möbius pairs -/

section MobiusPair

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A *Möbius pair* `(T, S)` of operators on a complex Hilbert space: `T` is an isometry commuting
with `S`, and `T† S = S†`.  These are the relations [Hägg, (15)] satisfied by multiplication by
the coordinates `q` and `z` on the `L²`-closure of `ℂ[q, z]` for a measure carried by the Möbius
bundle `z = q z̄`, `|q| = 1`. -/
structure IsMobiusPair (T S : H →L[ℂ] H) : Prop where
  isometry : Isometry T
  commute : T * S = S * T
  adjoint_mul : adjoint T * S = adjoint S

/-- The *symbol* `A = P_𝓔 S|_𝓔` of `S` relative to `T`: the compression of `S` to the wandering
subspace `𝓔 = ker T†` [Hägg, (16)]. -/
def mobiusSymbol (T S : H →L[ℂ] H) : T.wanderingSubspace →L[ℂ] T.wanderingSubspace :=
  T.wanderingSubspace.orthogonalProjectionOnto ∘L S ∘L T.wanderingSubspace.subtypeL

theorem mobiusSymbol_apply (T S : H →L[ℂ] H) (e : T.wanderingSubspace) :
    mobiusSymbol T S e = T.wanderingSubspace.orthogonalProjectionOnto (S e) :=
  rfl

/-- The finite wave packet `Σ_{k ≤ N} w̄ᵏ Tᵏ e`. -/
def wavePacket (T : H →L[ℂ] H) (w : ℂ) (N : ℕ) (e : H) : H :=
  ∑ k ∈ Finset.range (N + 1), (star w) ^ k • (T ^ k) e

/-! #### Wave packets -/

omit [CompleteSpace H] in
theorem wavePacket_add (T : H →L[ℂ] H) (w : ℂ) (N : ℕ) (e f : H) :
    wavePacket T w N (e + f) = wavePacket T w N e + wavePacket T w N f := by
  simp only [wavePacket, map_add, smul_add, Finset.sum_add_distrib]

omit [CompleteSpace H] in
theorem wavePacket_smul (T : H →L[ℂ] H) (w c : ℂ) (N : ℕ) (e : H) :
    wavePacket T w N (c • e) = c • wavePacket T w N e := by
  simp only [wavePacket, map_smul, Finset.smul_sum, smul_comm c]

omit [CompleteSpace H] in
theorem wavePacket_sub (T : H →L[ℂ] H) (w : ℂ) (N : ℕ) (e f : H) :
    wavePacket T w N (e - f) = wavePacket T w N e - wavePacket T w N f := by
  simp only [wavePacket, map_sub, smul_sub, Finset.sum_sub_distrib]

omit [CompleteSpace H] in
/-- The shift defect of a wave packet: `T u - w u = w̄ᴺ Tᴺ⁺¹ e - w e` if `w̄ w = 1`. -/
theorem wavePacket_shift_defect (T : H →L[ℂ] H) {w : ℂ} (hw : star w * w = 1) (N : ℕ)
    (e : H) : T (wavePacket T w N e) - w • wavePacket T w N e =
      (star w) ^ N • (T ^ (N + 1)) e - w • e := by
  induction N with
  | zero => simp [wavePacket]
  | succ N ih =>
      have hpacket : wavePacket T w (N + 1) e =
          wavePacket T w N e + (star w) ^ (N + 1) • (T ^ (N + 1)) e := by
        simp [wavePacket, Finset.sum_range_succ]
      have hcoef : w * (star w) ^ (N + 1) = (star w) ^ N :=
        calc w * (star w) ^ (N + 1) = (star w * w) * (star w) ^ N := by ring
          _ = (star w) ^ N := by rw [hw, one_mul]
      rw [hpacket, map_add, map_smul, ← pow_succ_apply' T (N + 1), smul_add, smul_smul, hcoef]
      calc T (wavePacket T w N e) + (star w) ^ (N + 1) • (T ^ (N + 1 + 1)) e -
            (w • wavePacket T w N e + (star w) ^ N • (T ^ (N + 1)) e)
          = (T (wavePacket T w N e) - w • wavePacket T w N e) +
              (star w) ^ (N + 1) • (T ^ (N + 1 + 1)) e - (star w) ^ N • (T ^ (N + 1)) e := by
            abel
        _ = (star w) ^ (N + 1) • (T ^ (N + 1 + 1)) e - w • e := by
            rw [ih]; abel

omit [CompleteSpace H] in
theorem norm_wavePacket_shift_defect_le {T : H →L[ℂ] H} {w : ℂ} (hw : ‖w‖ = 1) (hT : Isometry T)
    (N : ℕ) (e : H) : ‖T (wavePacket T w N e) - w • wavePacket T w N e‖ ≤ 2 * ‖e‖ := by
  have hww : star w * w = 1 := by
    rw [RCLike.star_def, RCLike.conj_mul, hw]
    simp
  rw [wavePacket_shift_defect T hww]
  calc ‖(star w) ^ N • (T ^ (N + 1)) e - w • e‖
      ≤ ‖(star w) ^ N • (T ^ (N + 1)) e‖ + ‖w • e‖ := norm_sub_le _ _
    _ = 2 * ‖e‖ := by
        rw [norm_smul, norm_smul, norm_pow, norm_star, hw, one_pow, one_mul, one_mul,
          norm_pow_apply_of_isometry hT]
        ring

/-- For `e ∈ ker T†`, the wave packet has norm `√(N+1) ‖e‖`. -/
theorem norm_sq_wavePacket {T : H →L[ℂ] H} {w : ℂ} (hw : ‖w‖ = 1) (hT : Isometry T) (N : ℕ)
    (e : T.wanderingSubspace) : ‖wavePacket T w N e‖ ^ 2 = ((N : ℝ) + 1) * ‖e‖ ^ 2 := by
  have h := (orthogonalFamily_woldEmbedding hT).norm_sum (fun k : ℕ ↦ (star w) ^ k • e)
    (Finset.range (N + 1))
  have hterm : ∀ k : ℕ, ‖(star w) ^ k • e‖ ^ 2 = ‖e‖ ^ 2 := fun k ↦ by
    rw [norm_smul, norm_pow, norm_star, hw, one_pow, one_mul]
  simp only [woldEmbedding_apply, map_smul, hterm] at h
  rw [wavePacket, h]
  simp

theorem norm_wavePacket {T : H →L[ℂ] H} {w : ℂ} (hw : ‖w‖ = 1) (hT : Isometry T) (N : ℕ)
    (e : T.wanderingSubspace) : ‖wavePacket T w N e‖ = Real.sqrt ((N : ℝ) + 1) * ‖e‖ := by
  have hpos : (0 : ℝ) ≤ (N : ℝ) + 1 := by positivity
  rw [← Real.sqrt_sq (norm_nonneg _), norm_sq_wavePacket hw hT, Real.sqrt_mul hpos,
    Real.sqrt_sq (norm_nonneg _)]

namespace IsMobiusPair

variable {T S : H →L[ℂ] H} (h : IsMobiusPair T S)
include h

/-- The adjoint relation `S† T = S` [Hägg, (15)]. -/
theorem adjoint_mul' : adjoint S * T = S := by
  have := congrArg star h.adjoint_mul
  rwa [star_mul, star_eq_adjoint, star_eq_adjoint, adjoint_adjoint, star_eq_adjoint,
    adjoint_adjoint] at this

theorem adjoint_commute : adjoint T * adjoint S = adjoint S * adjoint T := by
  have := congrArg star h.commute
  rwa [star_mul, star_mul, star_eq_adjoint, star_eq_adjoint, eq_comm] at this

theorem adjoint_apply_apply (x : H) : adjoint T (S x) = adjoint S x :=
  congrArg (fun L : H →L[ℂ] H ↦ L x) h.adjoint_mul

theorem apply_apply_comm (x : H) : T (S x) = S (T x) :=
  congrArg (fun L : H →L[ℂ] H ↦ L x) h.commute

theorem pow_apply_apply_comm (n : ℕ) (x : H) : (T ^ n) (S x) = S ((T ^ n) x) := by
  induction n generalizing x with
  | zero => simp
  | succ n ih => rw [pow_succ_apply', pow_succ_apply', ih, h.apply_apply_comm]

theorem adjoint_apply_adjoint_apply_comm (x : H) :
    adjoint T (adjoint S x) = adjoint S (adjoint T x) :=
  congrArg (fun L : H →L[ℂ] H ↦ L x) h.adjoint_commute

theorem adjoint_pow_apply_adjoint_apply_comm (n : ℕ) (x : H) :
    (adjoint T ^ n) (adjoint S x) = adjoint S ((adjoint T ^ n) x) := by
  induction n generalizing x with
  | zero => simp
  | succ n ih => rw [pow_succ_apply', pow_succ_apply', ih, h.adjoint_apply_adjoint_apply_comm]

/-- **Purity criterion for Möbius pairs.**  If `v ∈ ker T†` and the vectors `Tᵐ Sⁿ v` span a dense
subspace, then `T` is a pure isometry: all these vectors are killed by a power of `T†`. -/
theorem isPureIsometry_of_dense_span {v : H} (hv : v ∈ T.wanderingSubspace)
    (hdense : Dense (Submodule.span ℂ (range fun p : ℕ × ℕ ↦ (T ^ p.1) ((S ^ p.2) v)) : Set H)) :
    IsPureIsometry T := by
  let L : Submodule ℂ H :=
    { carrier := {x | ∃ n, (adjoint T ^ n) x = 0}
      add_mem' := by
        rintro x y ⟨m, hm⟩ ⟨n, hn⟩
        refine ⟨m + n, ?_⟩
        rw [map_add, pow_apply_eq_zero_of_le _ hm (Nat.le_add_right m n),
          pow_apply_eq_zero_of_le _ hn (Nat.le_add_left n m), add_zero]
      zero_mem' := ⟨0, map_zero _⟩
      smul_mem' := by
        rintro c x ⟨n, hn⟩
        exact ⟨n, by rw [map_smul, hn, smul_zero]⟩ }
  have hLT : ∀ x ∈ L, T x ∈ L := by
    rintro x ⟨n, hn⟩
    exact ⟨n + 1, by rw [pow_succ_apply, adjoint_apply_apply_of_isometry h.isometry, hn]⟩
  have hLS : ∀ x ∈ L, S x ∈ L := by
    rintro x ⟨n, hn⟩
    exact ⟨n + 1, by
      rw [pow_succ_apply, h.adjoint_apply_apply, h.adjoint_pow_apply_adjoint_apply_comm, hn,
        map_zero]⟩
  have hLpow : ∀ (A : H →L[ℂ] H), (∀ x ∈ L, A x ∈ L) → ∀ (n : ℕ), ∀ x ∈ L, (A ^ n) x ∈ L := by
    intro A hA n
    induction n with
    | zero => intro x hx; simpa using hx
    | succ n ih => intro x hx; rw [pow_succ_apply']; exact hA _ (ih x hx)
  have hvL : v ∈ L := ⟨1, by simpa using mem_wanderingSubspace.1 hv⟩
  have hspan : Submodule.span ℂ (range fun p : ℕ × ℕ ↦ (T ^ p.1) ((S ^ p.2) v)) ≤ L := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨⟨m, n⟩, rfl⟩
    exact hLpow T hLT m _ (hLpow S hLS n v hvL)
  exact isPureIsometry_of_dense h.isometry (hdense.mono hspan)

/-- `S†` leaves the wandering subspace `ker T†` invariant. -/
theorem adjoint_apply_mem_wanderingSubspace {e : H} (he : e ∈ T.wanderingSubspace) :
    adjoint S e ∈ T.wanderingSubspace := by
  rw [mem_wanderingSubspace] at he ⊢
  calc adjoint T (adjoint S e) = (adjoint T * adjoint S) e := rfl
    _ = (adjoint S * adjoint T) e := by rw [h.adjoint_commute]
    _ = 0 := by
        change adjoint S (adjoint T e) = 0
        rw [he, map_zero]

/-- The explicit form `A e = S e - T S† e` of the symbol. -/
theorem coe_mobiusSymbol_apply (e : T.wanderingSubspace) :
    (mobiusSymbol T S e : H) = S e - T (adjoint S e) := by
  rw [mobiusSymbol_apply, ← Submodule.starProjection_apply,
    starProjection_wanderingSubspace_apply h.isometry, h.adjoint_apply_apply]

/-- The restriction of `S†` to the wandering subspace. -/
def adjointRestrict : T.wanderingSubspace →L[ℂ] T.wanderingSubspace :=
  (adjoint S ∘L T.wanderingSubspace.subtypeL).codRestrict T.wanderingSubspace fun e ↦
    h.adjoint_apply_mem_wanderingSubspace e.2

theorem coe_adjointRestrict_apply (e : T.wanderingSubspace) :
    (h.adjointRestrict e : H) = adjoint S e :=
  rfl

/-- The adjoint of the symbol is the restriction of `S†` to `ker T†`. -/
theorem adjoint_mobiusSymbol : adjoint (mobiusSymbol T S) = h.adjointRestrict := by
  refine ContinuousLinearMap.ext fun e ↦ ext_inner_right ℂ fun f ↦ ?_
  rw [adjoint_inner_left, mobiusSymbol_apply,
    Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left,
    Submodule.coe_inner, coe_adjointRestrict_apply, adjoint_inner_left]

theorem coe_adjoint_mobiusSymbol_apply (e : T.wanderingSubspace) :
    (adjoint (mobiusSymbol T S) e : H) = adjoint S e := by
  rw [h.adjoint_mobiusSymbol, coe_adjointRestrict_apply]

/-- **The symbol form of `S`** [Hägg, (17)]: on `𝓔 = ker T†`, `S e = A e + T A† e`. -/
theorem apply_eq_mobiusSymbol_add (e : T.wanderingSubspace) :
    S e = mobiusSymbol T S e + T (adjoint (mobiusSymbol T S) e) := by
  rw [h.coe_mobiusSymbol_apply, h.coe_adjoint_mobiusSymbol_apply, sub_add_cancel]

/-- In the Wold model, `S` acts on the summand `Tⁿ 𝓔` by the symbol `A + q A†`:
`S Tⁿ e = Tⁿ A e + Tⁿ⁺¹ A† e`. -/
theorem apply_pow_apply_eq (n : ℕ) (e : T.wanderingSubspace) :
    S ((T ^ n) e) = (T ^ n) (mobiusSymbol T S e) +
      (T ^ (n + 1)) (adjoint (mobiusSymbol T S) e) := by
  rw [← h.pow_apply_apply_comm, h.apply_eq_mobiusSymbol_add, map_add, pow_succ_apply]

/-- **The Hardy symbol** [Hägg, (17)]: if `T` is pure, then in the Wold coordinates
`H ≃ ℓ²(ℕ, 𝓔)` (i.e. `H²(𝕋, 𝓔)`), `T` is the shift and `S` is multiplication by the symbol
`A + q A†`: `S (δₙ ⊗ e) = δₙ ⊗ A e + δₙ₊₁ ⊗ A† e`. -/
theorem apply_woldEquiv_symm_single (hT : IsPureIsometry T) (n : ℕ) (e : T.wanderingSubspace) :
    S (hT.woldEquiv.symm (lp.single 2 n e)) =
      hT.woldEquiv.symm (lp.single 2 n (mobiusSymbol T S e) +
        lp.single 2 (n + 1) (adjoint (mobiusSymbol T S) e)) := by
  rw [map_add, IsPureIsometry.woldEquiv_symm_single, IsPureIsometry.woldEquiv_symm_single,
    IsPureIsometry.woldEquiv_symm_single, h.apply_pow_apply_eq]

/-- `S` maps a wave packet of `e ∈ ker T†` to the wave packet of `A e` plus `T` applied to the
wave packet of `A† e`. -/
theorem apply_wavePacket (w : ℂ) (N : ℕ) (e : T.wanderingSubspace) :
    S (wavePacket T w N e) = wavePacket T w N (mobiusSymbol T S e) +
      T (wavePacket T w N (adjoint (mobiusSymbol T S) e)) := by
  simp only [wavePacket, map_sum, map_smul, h.apply_pow_apply_eq, smul_add,
    Finset.sum_add_distrib, pow_succ_apply']

/-- The residual of `S - a` on a wave packet. -/
theorem apply_wavePacket_sub_smul (w a : ℂ) (N : ℕ) (e : T.wanderingSubspace) :
    S (wavePacket T w N e) - a • wavePacket T w N e =
      wavePacket T w N (((mobiusSymbol T S + w • adjoint (mobiusSymbol T S)) e : H) - a • e) +
      (T (wavePacket T w N (adjoint (mobiusSymbol T S) e)) -
        w • wavePacket T w N (adjoint (mobiusSymbol T S) e)) := by
  rw [h.apply_wavePacket, wavePacket_sub, add_apply, Submodule.coe_add,
    smul_apply, Submodule.coe_smul, wavePacket_add, wavePacket_smul,
    wavePacket_smul]
  abel

theorem norm_apply_wavePacket_sub_smul_le {w : ℂ} (hw : ‖w‖ = 1) (a : ℂ) (N : ℕ)
    (e : T.wanderingSubspace) :
    ‖S (wavePacket T w N e) - a • wavePacket T w N e‖ ≤
      Real.sqrt ((N : ℝ) + 1) * ‖(mobiusSymbol T S + w • adjoint (mobiusSymbol T S)) e - a • e‖ +
        2 * ‖adjoint (mobiusSymbol T S) e‖ := by
  rw [h.apply_wavePacket_sub_smul]
  refine (norm_add_le _ _).trans (add_le_add (le_of_eq ?_)
    (norm_wavePacket_shift_defect_le hw h.isometry N _))
  have := norm_wavePacket hw h.isometry N
    ((mobiusSymbol T S + w • adjoint (mobiusSymbol T S)) e - a • e)
  simpa using this

/-- **Joint approximate eigenvectors** [Hägg, proof of Lemma 7].  Let `(T, S)` be a Möbius pair
with symbol `A`, `|w| = 1`, and let `a` be a spectral value of the normal operator `A + w A†`.
Then `(w, a)` is a joint approximate eigenvalue of `(T, S)`. -/
theorem exists_seq_joint_approx_eigenvector {w a : ℂ} (hw : ‖w‖ = 1)
    (ha : a ∈ spectrum ℂ (mobiusSymbol T S + w • adjoint (mobiusSymbol T S))) :
    ∃ u : ℕ → H, (∀ n, ‖u n‖ = 1) ∧
      Tendsto (fun n ↦ ‖T (u n) - w • u n‖) atTop (𝓝 0) ∧
      Tendsto (fun n ↦ ‖S (u n) - a • u n‖) atTop (𝓝 0) := by
  set A := mobiusSymbol T S
  obtain ⟨e, he, hlim⟩ :=
    ContinuousLinearMap.IsStarNormal.exists_seq_tendsto_norm_sub_smul_of_mem_spectrum
      (isStarNormal_add_smul_adjoint A hw) ha
  let c : ℕ → ℝ := fun n ↦ (Real.sqrt ((n : ℝ) + 1))⁻¹
  have hsqrt : ∀ n : ℕ, 0 < Real.sqrt ((n : ℝ) + 1) := fun n ↦ Real.sqrt_pos.2 (by positivity)
  let u : ℕ → H := fun n ↦ (c n : ℂ) • wavePacket T w n (e n)
  have hc : ∀ n : ℕ, ‖(c n : ℂ)‖ = (Real.sqrt ((n : ℝ) + 1))⁻¹ := fun n ↦ by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.2 (hsqrt n))]
  have hinv : Tendsto c atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp
      (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop))
  refine ⟨u, fun n ↦ ?_, ?_, ?_⟩
  · rw [norm_smul, hc, norm_wavePacket hw h.isometry, he, mul_one,
      inv_mul_cancel₀ (hsqrt n).ne']
  · have hg : Tendsto (fun n ↦ 2 * c n) atTop (𝓝 0) := by
      have := hinv.const_mul 2
      rwa [mul_zero] at this
    refine squeeze_zero (fun n ↦ norm_nonneg _) (fun n ↦ ?_) hg
    calc ‖T (u n) - w • u n‖ = c n * ‖T (wavePacket T w n (e n)) - w • wavePacket T w n (e n)‖ := by
          rw [map_smul, smul_comm, ← smul_sub, norm_smul, hc]
      _ ≤ c n * (2 * ‖e n‖) := by
          gcongr
          exact norm_wavePacket_shift_defect_le hw h.isometry n _
      _ = 2 * c n := by rw [he]; ring
  · have hbound : ∀ n, ‖adjoint A (e n)‖ ≤ ‖adjoint A‖ := fun n ↦
      ((adjoint A).le_opNorm _).trans (by rw [he, mul_one])
    have hg : Tendsto (fun n ↦ ‖(A + w • adjoint A) (e n) - a • e n‖ + 2 * ‖adjoint A‖ * c n)
        atTop (𝓝 0) := by
      have := hlim.add (hinv.const_mul (2 * ‖adjoint A‖))
      rwa [mul_zero, add_zero] at this
    refine squeeze_zero (fun n ↦ norm_nonneg _) (fun n ↦ ?_) hg
    calc ‖S (u n) - a • u n‖ = c n * ‖S (wavePacket T w n (e n)) - a • wavePacket T w n (e n)‖ := by
          rw [map_smul, smul_comm, ← smul_sub, norm_smul, hc]
      _ ≤ c n * (Real.sqrt ((n : ℝ) + 1) * ‖(A + w • adjoint A) (e n) - a • e n‖ +
            2 * ‖adjoint A (e n)‖) := by
          gcongr
          exact h.norm_apply_wavePacket_sub_smul_le hw a n (e n)
      _ ≤ c n * (Real.sqrt ((n : ℝ) + 1) * ‖(A + w • adjoint A) (e n) - a • e n‖ +
            2 * ‖adjoint A‖) := by
          gcongr
          exact hbound n
      _ = ‖(A + w • adjoint A) (e n) - a • e n‖ + 2 * ‖adjoint A‖ * c n := by
          simp only [c]
          rw [mul_add, ← mul_assoc, inv_mul_cancel₀ (hsqrt n).ne', one_mul]
          ring

end IsMobiusPair

end MobiusPair

/-! ### Multiplication operators on `L²` -/

section Multiplication

open MeasureTheory

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  (μ : Measure X) [IsFiniteMeasure μ]

/-- Multiplication by a continuous function, as a bounded operator on `L²(μ)`. -/
def mulL2 (f : C(X, ℂ)) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  (ContinuousLinearMap.mul ℂ ℂ).holderL μ ∞ 2 2 (ContinuousMap.toLp ∞ μ ℂ f)

theorem mulL2_ae (f : C(X, ℂ)) (u : Lp ℂ 2 μ) :
    (mulL2 μ f u : X → ℂ) =ᵐ[μ] fun x ↦ f x * u x := by
  have hmul := (ContinuousLinearMap.mul ℂ ℂ).coeFn_holder (r := 2)
    (ContinuousMap.toLp ∞ μ ℂ f) u
  filter_upwards [hmul, ContinuousMap.coeFn_toLp (p := ∞) (𝕜 := ℂ) μ f] with x hx hfx
  rw [mulL2, holderL_apply_apply, hx, hfx, ContinuousLinearMap.mul_apply']

theorem mulL2_toLp (f g : C(X, ℂ)) :
    mulL2 μ f (ContinuousMap.toLp 2 μ ℂ g) = ContinuousMap.toLp 2 μ ℂ (f * g) := by
  apply Lp.ext
  filter_upwards [mulL2_ae μ f (ContinuousMap.toLp 2 μ ℂ g),
    ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) μ g,
    ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) μ (f * g)] with x h1 h2 h3
  rw [h1, h2, h3, ContinuousMap.mul_apply]

theorem mulL2_mul_apply (f g : C(X, ℂ)) (u : Lp ℂ 2 μ) :
    mulL2 μ f (mulL2 μ g u) = mulL2 μ (f * g) u := by
  apply Lp.ext
  filter_upwards [mulL2_ae μ f (mulL2 μ g u), mulL2_ae μ g u, mulL2_ae μ (f * g) u]
    with x h1 h2 h3
  rw [h1, h2, h3, ContinuousMap.mul_apply, mul_assoc]

theorem mulL2_mul (f g : C(X, ℂ)) : mulL2 μ (f * g) = mulL2 μ f * mulL2 μ g :=
  ContinuousLinearMap.ext fun u ↦ (mulL2_mul_apply μ f g u).symm

theorem mulL2_one : mulL2 μ 1 = 1 := by
  refine ContinuousLinearMap.ext fun u ↦ ?_
  change mulL2 μ 1 u = u
  refine Lp.ext ?_
  filter_upwards [mulL2_ae μ 1 u] with x hx
  rw [hx, ContinuousMap.one_apply, one_mul]

theorem mulL2_commute (f g : C(X, ℂ)) : mulL2 μ f * mulL2 μ g = mulL2 μ g * mulL2 μ f := by
  rw [← mulL2_mul, ← mulL2_mul, mul_comm]

theorem inner_mulL2_left (f : C(X, ℂ)) (u v : Lp ℂ 2 μ) :
    ⟪mulL2 μ f u, v⟫_ℂ = ⟪u, mulL2 μ (star f) v⟫_ℂ := by
  rw [L2.inner_def, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [mulL2_ae μ f u, mulL2_ae μ (star f) v] with x hfu hfv
  rw [hfu, hfv, RCLike.inner_apply, RCLike.inner_apply, ContinuousMap.star_apply, map_mul,
    RCLike.star_def]
  ring

/-- The adjoint of multiplication by `f` is multiplication by `f̄`. -/
theorem adjoint_mulL2 (f : C(X, ℂ)) : adjoint (mulL2 μ f) = mulL2 μ (star f) := by
  refine ContinuousLinearMap.ext fun u ↦ ext_inner_right ℂ fun v ↦ ?_
  rw [adjoint_inner_left, inner_mulL2_left, star_star]

/-- Multiplication by a unimodular function is an isometry of `L²`. -/
theorem isometry_mulL2 {f : C(X, ℂ)} (hf : star f * f = 1) : Isometry (mulL2 μ f) := by
  rw [isometry_iff_adjoint_comp_self, adjoint_mulL2]
  change mulL2 μ (star f) * mulL2 μ f = 1
  rw [← mulL2_mul, hf, mulL2_one]

omit [TopologicalSpace X] [CompactSpace X] [BorelSpace X] [IsFiniteMeasure μ] in
theorem norm_sq_eq_integral_norm_sq (u : Lp ℂ 2 μ) : ‖u‖ ^ 2 = ∫ x, ‖u x‖ ^ 2 ∂μ := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), L2.inner_def, ← integral_re (L2.integrable_inner u u)]
  exact integral_congr_ae (ae_of_all _ fun x ↦ inner_self_eq_norm_sq (u x))

/-- A uniform pointwise gap `δ ≤ |q - q₀|² + |z - z₀|²` gives the joint lower bound
`δ ‖u‖² ≤ ‖(M_q - q₀) u‖² + ‖(M_z - z₀) u‖²`. -/
theorem mul_norm_sq_le_norm_mulL2_sub_smul_sq_add (q z : C(X, ℂ)) (q₀ z₀ : ℂ) {δ : ℝ}
    (hgap : ∀ x, δ ≤ ‖q x - q₀‖ ^ 2 + ‖z x - z₀‖ ^ 2) (u : Lp ℂ 2 μ) :
    δ * ‖u‖ ^ 2 ≤ ‖mulL2 μ q u - q₀ • u‖ ^ 2 + ‖mulL2 μ z u - z₀ • u‖ ^ 2 := by
  set uq : Lp ℂ 2 μ := mulL2 μ q u - q₀ • u
  set uz : Lp ℂ 2 μ := mulL2 μ z u - z₀ • u
  have hpoint : ∀ᵐ x ∂μ, δ * ‖u x‖ ^ 2 ≤ ‖uq x‖ ^ 2 + ‖uz x‖ ^ 2 := by
    filter_upwards [Lp.coeFn_sub (mulL2 μ q u) (q₀ • u), mulL2_ae μ q u, Lp.coeFn_smul q₀ u,
      Lp.coeFn_sub (mulL2 μ z u) (z₀ • u), mulL2_ae μ z u, Lp.coeFn_smul z₀ u]
      with x hqsub hqmul hqsmul hzsub hzmul hzsmul
    have hqu : uq x = (q x - q₀) * u x := by
      rw [hqsub, Pi.sub_apply, hqmul, hqsmul, Pi.smul_apply, smul_eq_mul, sub_mul]
    have hzu : uz x = (z x - z₀) * u x := by
      rw [hzsub, Pi.sub_apply, hzmul, hzsmul, Pi.smul_apply, smul_eq_mul, sub_mul]
    calc δ * ‖u x‖ ^ 2 ≤ (‖q x - q₀‖ ^ 2 + ‖z x - z₀‖ ^ 2) * ‖u x‖ ^ 2 :=
          mul_le_mul_of_nonneg_right (hgap x) (sq_nonneg _)
      _ = ‖uq x‖ ^ 2 + ‖uz x‖ ^ 2 := by
          rw [hqu, hzu, norm_mul, norm_mul, mul_pow, mul_pow, add_mul]
  have hint : ∀ v : Lp ℂ 2 μ, Integrable (fun x ↦ ‖v x‖ ^ 2) μ := fun v ↦
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable v)).mp (Lp.memLp v)
  calc δ * ‖u‖ ^ 2 = ∫ x, δ * ‖u x‖ ^ 2 ∂μ := by
        rw [integral_const_mul, norm_sq_eq_integral_norm_sq]
    _ ≤ ∫ x, (‖uq x‖ ^ 2 + ‖uz x‖ ^ 2) ∂μ :=
        integral_mono_ae ((hint u).const_mul δ) ((hint uq).add (hint uz)) hpoint
    _ = ‖uq‖ ^ 2 + ‖uz‖ ^ 2 := by
        rw [integral_add (hint uq) (hint uz), norm_sq_eq_integral_norm_sq,
          norm_sq_eq_integral_norm_sq]

omit [MeasurableSpace X] [BorelSpace X] in
/-- Away from the (compact) joint range of `(q, z)`, the squared distance to `(q₀, z₀)` is bounded
below by a positive constant. -/
theorem exists_pos_forall_le_norm_sub_sq_add (q z : C(X, ℂ)) (q₀ z₀ : ℂ)
    (hnot : ¬ ∃ x, q x = q₀ ∧ z x = z₀) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x, δ ≤ ‖q x - q₀‖ ^ 2 + ‖z x - z₀‖ ^ 2 := by
  rcases isEmpty_or_nonempty X with hX | hX
  · exact ⟨1, one_pos, fun x ↦ isEmptyElim x⟩
  let r : X → ℝ := fun x ↦ ‖q x - q₀‖ ^ 2 + ‖z x - z₀‖ ^ 2
  obtain ⟨x, -, hmin⟩ := isCompact_univ.exists_isMinOn univ_nonempty
    (by fun_prop : Continuous r).continuousOn
  have hrne : r x ≠ 0 := by
    intro hr0
    change ‖q x - q₀‖ ^ 2 + ‖z x - z₀‖ ^ 2 = 0 at hr0
    have h1 : ‖q x - q₀‖ ^ 2 = 0 :=
      le_antisymm (by linarith [sq_nonneg (‖z x - z₀‖)]) (sq_nonneg _)
    have h2 : ‖z x - z₀‖ ^ 2 = 0 :=
      le_antisymm (by linarith [sq_nonneg (‖q x - q₀‖)]) (sq_nonneg _)
    rw [pow_eq_zero_iff two_ne_zero, norm_eq_zero, sub_eq_zero] at h1 h2
    exact hnot ⟨x, h1, h2⟩
  exact ⟨r x, lt_of_le_of_ne (by positivity) (Ne.symm hrne), fun y ↦ hmin (mem_univ y)⟩

/-- **Joint spectral localization.**  If `(q₀, z₀)` is a joint approximate eigenvalue of the
multiplication operators `(M_q, M_z)` on `L²(μ)`, then `(q₀, z₀) = (q x, z x)` for some `x`. -/
theorem exists_eq_of_tendsto_mulL2 (q z : C(X, ℂ)) (q₀ z₀ : ℂ) (u : ℕ → Lp ℂ 2 μ)
    (hu : ∀ n, ‖u n‖ = 1)
    (hq : Tendsto (fun n ↦ ‖mulL2 μ q (u n) - q₀ • u n‖) atTop (𝓝 0))
    (hz : Tendsto (fun n ↦ ‖mulL2 μ z (u n) - z₀ • u n‖) atTop (𝓝 0)) :
    ∃ x, q x = q₀ ∧ z x = z₀ := by
  by_contra hnot
  obtain ⟨δ, hδ, hgap⟩ := exists_pos_forall_le_norm_sub_sq_add q z q₀ z₀ hnot
  have hlower : ∀ n, δ ≤ ‖mulL2 μ q (u n) - q₀ • u n‖ ^ 2 + ‖mulL2 μ z (u n) - z₀ • u n‖ ^ 2 :=
    fun n ↦ by simpa [hu n] using mul_norm_sq_le_norm_mulL2_sub_smul_sq_add μ q z q₀ z₀ hgap (u n)
  have hzero : Tendsto (fun n ↦ ‖mulL2 μ q (u n) - q₀ • u n‖ ^ 2 +
      ‖mulL2 μ z (u n) - z₀ • u n‖ ^ 2) atTop (𝓝 0) := by
    simpa using (hq.pow 2).add (hz.pow 2)
  exact (not_le_of_gt hδ) (ge_of_tendsto' hzero hlower)

end Multiplication

/-! ### The coordinate algebra `𝒜 = closure ℂ[q, z]` -/

section CoordinateAlgebra

open MeasureTheory

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]

/-- The uniform algebra `𝒜 = closure ℂ[q, z] ⊆ C(X, ℂ)` generated by two continuous
functions. -/
def coordinateAlgebra (q z : C(X, ℂ)) : Subalgebra ℂ C(X, ℂ) :=
  (Algebra.adjoin ℂ {q, z}).topologicalClosure

theorem isClosed_coordinateAlgebra (q z : C(X, ℂ)) :
    IsClosed (coordinateAlgebra q z : Set C(X, ℂ)) :=
  Subalgebra.isClosed_topologicalClosure _

theorem adjoin_le_coordinateAlgebra (q z : C(X, ℂ)) :
    Algebra.adjoin ℂ {q, z} ≤ coordinateAlgebra q z :=
  Subalgebra.le_topologicalClosure _

omit [CompactSpace X] in
theorem left_mem_adjoin (q z : C(X, ℂ)) : q ∈ Algebra.adjoin ℂ {q, z} :=
  Algebra.subset_adjoin (mem_insert _ _)

omit [CompactSpace X] in
theorem right_mem_adjoin (q z : C(X, ℂ)) : z ∈ Algebra.adjoin ℂ {q, z} :=
  Algebra.subset_adjoin (mem_insert_of_mem _ (mem_singleton _))

theorem left_mem_coordinateAlgebra (q z : C(X, ℂ)) : q ∈ coordinateAlgebra q z :=
  adjoin_le_coordinateAlgebra q z (left_mem_adjoin q z)

theorem right_mem_coordinateAlgebra (q z : C(X, ℂ)) : z ∈ coordinateAlgebra q z :=
  adjoin_le_coordinateAlgebra q z (right_mem_adjoin q z)

omit [CompactSpace X] in
/-- `ℂ[q, z]` is spanned by the monomials `q^m z^n`. -/
theorem mem_span_monomials {q z p : C(X, ℂ)} (hp : p ∈ Algebra.adjoin ℂ {q, z}) :
    p ∈ Submodule.span ℂ {f | ∃ m n : ℕ, q ^ m * z ^ n = f} := by
  rw [← Subalgebra.mem_toSubmodule, Algebra.adjoin_eq_span] at hp
  exact Submodule.span_mono (fun f hf ↦ (Submonoid.mem_closure_pair q z f).1 hf) hp

/-- If `q` is invertible in `𝒜`, `|q| = 1` and `z = q z̄`, then `𝒜` is closed under
conjugation: `q̄ = q⁻¹` and `z̄ = q̄ z`. -/
theorem star_mem_coordinateAlgebra_of_isUnit {q z : C(X, ℂ)} (hq : star q * q = 1)
    (hz : z = q * star z)
    (hunit : IsUnit (⟨q, left_mem_coordinateAlgebra q z⟩ : coordinateAlgebra q z))
    {f : C(X, ℂ)} (hf : f ∈ coordinateAlgebra q z) : star f ∈ coordinateAlgebra q z := by
  set A := coordinateAlgebra q z
  obtain ⟨u, hu⟩ := hunit.exists_right_inv
  have hu' : q * (u : C(X, ℂ)) = 1 := congrArg Subtype.val hu
  have hqstar : star q ∈ A := by
    have : (u : C(X, ℂ)) = star q :=
      calc (u : C(X, ℂ)) = (star q * q) * u := by rw [hq, one_mul]
        _ = star q := by rw [mul_assoc, hu', mul_one]
    exact this ▸ u.2
  have hzstar : star z ∈ A := by
    have : star z = star q * z :=
      calc star z = (star q * q) * star z := by rw [hq, one_mul]
        _ = star q * z := by rw [mul_assoc, ← hz]
    exact this ▸ A.mul_mem hqstar (right_mem_coordinateAlgebra q z)
  refine ContinuousMap.star_mem_topologicalClosure_adjoin (fun g hg ↦ ?_) hf
  rcases hg with hg | hg
  · rw [hg]
    exact hqstar
  · rw [mem_singleton_iff] at hg
    rw [hg]
    exact hzstar

/-- If `x ↦ (q x, z x)` is injective, then `𝒜` separates points. -/
theorem separatesPoints_coordinateAlgebra {q z : C(X, ℂ)}
    (hinj : Function.Injective fun x ↦ (q x, z x)) : (coordinateAlgebra q z).SeparatesPoints := by
  intro x y hxy
  by_cases hqxy : q x = q y
  · refine ⟨z, ⟨z, right_mem_coordinateAlgebra q z, rfl⟩, fun hzxy ↦ hxy (hinj ?_)⟩
    exact Prod.ext hqxy hzxy
  · exact ⟨q, ⟨q, left_mem_coordinateAlgebra q z, rfl⟩, hqxy⟩

/-- If `q` were invertible in `𝒜`, Stone–Weierstrass would give `𝒜 = C(X, ℂ)`. -/
theorem coordinateAlgebra_eq_top_of_isUnit {q z : C(X, ℂ)} (hq : star q * q = 1)
    (hz : z = q * star z) (hinj : Function.Injective fun x ↦ (q x, z x))
    (hunit : IsUnit (⟨q, left_mem_coordinateAlgebra q z⟩ : coordinateAlgebra q z)) :
    coordinateAlgebra q z = ⊤ :=
  ContinuousMap.subalgebra_eq_top_of_star_mem _ (isClosed_coordinateAlgebra q z)
    (fun _ hf ↦ star_mem_coordinateAlgebra_of_isUnit hq hz hunit hf)
    (separatesPoints_coordinateAlgebra hinj)

variable [MeasurableSpace X] [BorelSpace X]

/-- The moment conditions [Hägg, (13)] say that `η` annihilates `q 𝒜`. -/
theorem integral_mul_eq_zero_of_mem_coordinateAlgebra {q z : C(X, ℂ)} {η : ComplexMeasure X}
    (hmom : ∀ j ℓ : ℕ, 1 ≤ ℓ →
      ∫ᵛ x, z x ^ j * q x ^ ℓ ∂[ContinuousLinearMap.mul ℝ ℂ; η] = 0)
    {f : C(X, ℂ)} (hf : f ∈ coordinateAlgebra q z) :
    ∫ᵛ x, q x * f x ∂[ContinuousLinearMap.mul ℝ ℂ; η] = 0 := by
  let L : C(X, ℂ) →L[ℂ] ℂ := η.integralCLM ∘L ContinuousLinearMap.mul ℂ C(X, ℂ) q
  have hL : ∀ g : C(X, ℂ), L g = ∫ᵛ x, q x * g x ∂[ContinuousLinearMap.mul ℝ ℂ; η] :=
    fun g ↦ rfl
  have hpoly : (Algebra.adjoin ℂ {q, z} : Set C(X, ℂ)) ⊆ (L.ker : Set C(X, ℂ)) := by
    intro p hp
    have hspan : Submodule.span ℂ {f | ∃ m n : ℕ, q ^ m * z ^ n = f} ≤ L.ker := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨m, n, rfl⟩
      change L (q ^ m * z ^ n) = 0
      rw [hL, ← hmom n (m + 1) (by omega)]
      congr 1
      ext x
      simp only [ContinuousMap.mul_apply, ContinuousMap.coe_pow, Pi.pow_apply]
      ring
    exact hspan (mem_span_monomials hp)
  have hf' : f ∈ closure (Algebra.adjoin ℂ {q, z} : Set C(X, ℂ)) := by
    rwa [← Subalgebra.topologicalClosure_coe]
  exact (hL f).symm.trans (closure_minimal hpoly L.isClosed_ker hf')

/-- **`q` is not invertible in `𝒜`** [Hägg, proof of Lemma 7]: otherwise `𝒜 = C(X, ℂ) = q 𝒜`
would be annihilated by `η ≠ 0`. -/
theorem not_isUnit_coordinateAlgebra [HasOuterApproxClosed X] {q z : C(X, ℂ)}
    (hq : star q * q = 1) (hz : z = q * star z) (hinj : Function.Injective fun x ↦ (q x, z x))
    {η : ComplexMeasure X} (hη : η ≠ 0)
    (hmom : ∀ j ℓ : ℕ, 1 ≤ ℓ →
      ∫ᵛ x, z x ^ j * q x ^ ℓ ∂[ContinuousLinearMap.mul ℝ ℂ; η] = 0) :
    ¬ IsUnit (⟨q, left_mem_coordinateAlgebra q z⟩ : coordinateAlgebra q z) := by
  intro hunit
  have htop := coordinateAlgebra_eq_top_of_isUnit hq hz hinj hunit
  obtain ⟨u, hu⟩ := hunit.exists_right_inv
  have hu' : q * (u : C(X, ℂ)) = 1 := congrArg Subtype.val hu
  refine hη (ComplexMeasure.eq_zero_of_forall_continuousMap_integral_eq_zero fun f ↦ ?_)
  have hall : ∀ g : C(X, ℂ), g ∈ coordinateAlgebra q z := fun g ↦ by
    rw [htop]
    exact Algebra.mem_top
  have hmem : (u : C(X, ℂ)) * f ∈ coordinateAlgebra q z := hall _
  have := integral_mul_eq_zero_of_mem_coordinateAlgebra hmom hmem
  have hfun : (fun x ↦ q x * ((u : C(X, ℂ)) * f) x) = fun x ↦ f x := by
    ext x
    rw [ContinuousMap.mul_apply, ← mul_assoc, ← ContinuousMap.mul_apply q, hu',
      ContinuousMap.one_apply, one_mul]
  rwa [hfun] at this

/-- **The killed character and its representing measure** [Hägg, proof of Lemma 7].  Under the
hypotheses of Lemma 7 there are a character `χ` of `𝒜 = closure ℂ[q, z]` with `χ(q) = 0` and a
probability measure `μ` on `X` representing it: `χ f = ∫ f dμ` for `f ∈ 𝒜`. -/
theorem exists_characterSpace_isProbabilityMeasure [T2Space X] [HasOuterApproxClosed X]
    {q z : C(X, ℂ)} (hq : star q * q = 1) (hz : z = q * star z)
    (hinj : Function.Injective fun x ↦ (q x, z x)) {η : ComplexMeasure X} (hη : η ≠ 0)
    (hmom : ∀ j ℓ : ℕ, 1 ≤ ℓ →
      ∫ᵛ x, z x ^ j * q x ^ ℓ ∂[ContinuousLinearMap.mul ℝ ℂ; η] = 0) :
    ∃ (χ : WeakDual.characterSpace ℂ (coordinateAlgebra q z)) (μ : Measure X),
      IsProbabilityMeasure μ ∧ χ ⟨q, left_mem_coordinateAlgebra q z⟩ = 0 ∧
      ∀ f : coordinateAlgebra q z, ∫ x, (f : C(X, ℂ)) x ∂μ = χ f := by
  obtain ⟨χ, hχ⟩ := Subalgebra.exists_characterSpace_apply_eq_zero _
    (isClosed_coordinateAlgebra q z) (not_isUnit_coordinateAlgebra hq hz hinj hη hmom)
  obtain ⟨μ, hμ, hrep⟩ := Subalgebra.exists_isProbabilityMeasure_integral_eq_characterSpace _
    (isClosed_coordinateAlgebra q z) χ
  exact ⟨χ, μ, hμ, hχ, hrep⟩

omit [BorelSpace X] in
/-- The representing measure of a character killing `q` annihilates `q 𝒜`. -/
theorem integral_mul_eq_zero_of_characterSpace {q z : C(X, ℂ)}
    {χ : WeakDual.characterSpace ℂ (coordinateAlgebra q z)}
    (hχ : χ ⟨q, left_mem_coordinateAlgebra q z⟩ = 0) {μ : Measure X}
    (hrep : ∀ f : coordinateAlgebra q z, ∫ x, (f : C(X, ℂ)) x ∂μ = χ f)
    {f : C(X, ℂ)} (hf : f ∈ coordinateAlgebra q z) : ∫ x, q x * f x ∂μ = 0 := by
  have := hrep (⟨q, left_mem_coordinateAlgebra q z⟩ * ⟨f, hf⟩)
  rwa [map_mul, hχ, zero_mul] at this

/-! #### The `q`-marginal -/

omit [BorelSpace X] in
/-- The representing measure of a character killing `q` annihilates the powers `qⁿ`, `n ≥ 1`. -/
theorem integral_pow_eq_zero_of_characterSpace {q z : C(X, ℂ)}
    {χ : WeakDual.characterSpace ℂ (coordinateAlgebra q z)}
    (hχ : χ ⟨q, left_mem_coordinateAlgebra q z⟩ = 0) {μ : Measure X}
    (hrep : ∀ f : coordinateAlgebra q z, ∫ x, (f : C(X, ℂ)) x ∂μ = χ f) {n : ℕ} (hn : 0 < n) :
    ∫ x, q x ^ n ∂μ = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hn
  have := integral_mul_eq_zero_of_characterSpace hχ hrep
    ((coordinateAlgebra q z).pow_mem (left_mem_coordinateAlgebra q z) k)
  simpa [ContinuousMap.coe_pow, pow_succ', add_comm] using this

omit [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in
theorem norm_eq_one_of_star_mul_self_eq_one {q : C(X, ℂ)} (hq : star q * q = 1) (x : X) :
    ‖q x‖ = 1 := by
  have h := congrArg (fun f : C(X, ℂ) ↦ f x) hq
  simp only [ContinuousMap.mul_apply, ContinuousMap.star_apply, ContinuousMap.one_apply] at h
  have h2 : (Complex.normSq (q x) : ℂ) = 1 := by
    rw [Complex.normSq_eq_conj_mul_self]
    exact h
  have h3 : Complex.normSq (q x) = 1 := by exact_mod_cast h2
  rw [Complex.normSq_eq_norm_sq] at h3
  nlinarith [norm_nonneg (q x)]

/-- The angle `arg q ∈ ℝ ⧸ 2πℤ` of a continuous function `q`. -/
def circleLift (q : C(X, ℂ)) (x : X) : AddCircle (2 * Real.pi) :=
  ((q x).arg : AddCircle (2 * Real.pi))

omit [CompactSpace X] in
theorem measurable_circleLift (q : C(X, ℂ)) : Measurable (circleLift q) :=
  (AddCircle.measurable_mk').comp (Complex.measurable_arg.comp q.continuous.measurable)

omit [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in
theorem fourier_circleLift {q : C(X, ℂ)} (hq : star q * q = 1) (n : ℕ) (x : X) :
    fourier (n : ℤ) (circleLift q x) = q x ^ n := by
  rw [circleLift, fourier_coe_apply]
  have h2π : (2 * Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.two_pi_pos.ne'
  have hexp : Complex.exp ((q x).arg * Complex.I) = q x := by
    have := Complex.norm_mul_exp_arg_mul_I (q x)
    rwa [norm_eq_one_of_star_mul_self_eq_one hq x, Complex.ofReal_one, one_mul] at this
  calc Complex.exp (2 * Real.pi * Complex.I * (n : ℤ) * (q x).arg / (2 * Real.pi : ℝ))
      = Complex.exp (n * ((q x).arg * Complex.I)) := by
        congr 1
        push_cast
        field_simp
    _ = q x ^ n := by rw [Complex.exp_nat_mul, hexp]

/-- `0 < 2π`, as a `Fact` (needed for `AddCircle (2π)`). -/
theorem fact_zero_lt_two_pi : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩

omit [CompactSpace X] in
attribute [local instance] fact_zero_lt_two_pi in
/-- **The `q`-marginal of a representing measure is Haar measure** [Hägg, proof of Lemma 7]: if
`μ` is a probability measure with `∫ qⁿ dμ = 0` for `n ≥ 1` and `|q| = 1`, then the push-forward
of `μ` under the angle of `q` is normalized Haar measure on `ℝ ⧸ 2πℤ`. -/
theorem map_circleLift_eq_haarAddCircle {q : C(X, ℂ)} (hq : star q * q = 1) {μ : Measure X}
    [IsProbabilityMeasure μ] (h : ∀ n : ℕ, 0 < n → ∫ x, q x ^ n ∂μ = 0) :
    μ.map (circleLift q) = AddCircle.haarAddCircle := by
  refine AddCircle.eq_haarAddCircle_of_integral_fourier_eq_zero _ fun n hn ↦ ?_
  rw [integral_map (measurable_circleLift q).aemeasurable
    (fourier (n : ℤ)).continuous.aestronglyMeasurable]
  simp_rw [fourier_circleLift hq]
  exact h n hn

attribute [local instance] fact_zero_lt_two_pi in
/-- The `q`-marginal of the representing measure of a character of `𝒜` killing `q` is Haar
measure [Hägg, proof of Lemma 7]. -/
theorem map_circleLift_eq_haarAddCircle_of_characterSpace {q z : C(X, ℂ)}
    (hq : star q * q = 1) {χ : WeakDual.characterSpace ℂ (coordinateAlgebra q z)}
    (hχ : χ ⟨q, left_mem_coordinateAlgebra q z⟩ = 0) {μ : Measure X} [IsProbabilityMeasure μ]
    (hrep : ∀ f : coordinateAlgebra q z, ∫ x, (f : C(X, ℂ)) x ∂μ = χ f) :
    μ.map (circleLift q) = AddCircle.haarAddCircle :=
  map_circleLift_eq_haarAddCircle hq fun _ hn ↦ integral_pow_eq_zero_of_characterSpace hχ hrep hn

end CoordinateAlgebra

/-! ### The Hardy premodel -/

section HardyPremodel

open MeasureTheory

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  (μ : Measure X) [IsFiniteMeasure μ] (q z : C(X, ℂ))

/-- The *Hardy space* of the premodel: the closure of `ℂ[q, z]` in `L²(μ)` [Hägg, proof of
Lemma 7]. -/
def hardySpace : Submodule ℂ (Lp ℂ 2 μ) :=
  ((Algebra.adjoin ℂ {q, z}).toSubmodule.map
    (ContinuousMap.toLp 2 μ ℂ : C(X, ℂ) →L[ℂ] Lp ℂ 2 μ).toLinearMap).topologicalClosure

/-- The Hardy space is closed, hence complete. -/
instance : CompleteSpace (hardySpace μ q z) := by
  unfold hardySpace
  infer_instance

variable {μ q z}

theorem coe_hardySpace : (hardySpace μ q z : Set (Lp ℂ 2 μ)) =
    closure ((ContinuousMap.toLp 2 μ ℂ : C(X, ℂ) →L[ℂ] Lp ℂ 2 μ) ''
      (Algebra.adjoin ℂ {q, z} : Set C(X, ℂ))) := by
  unfold hardySpace
  rw [Submodule.topologicalClosure_coe, Submodule.map_coe]
  rfl

theorem toLp_mem_hardySpace {f : C(X, ℂ)} (hf : f ∈ Algebra.adjoin ℂ {q, z}) :
    ContinuousMap.toLp 2 μ ℂ f ∈ hardySpace μ q z :=
  Submodule.le_topologicalClosure _ ⟨f, hf, rfl⟩

theorem hardySpace_le {K : Submodule ℂ (Lp ℂ 2 μ)} (hK : IsClosed (K : Set (Lp ℂ 2 μ)))
    (h : ∀ f ∈ Algebra.adjoin ℂ {q, z}, ContinuousMap.toLp 2 μ ℂ f ∈ K) :
    hardySpace μ q z ≤ K :=
  Submodule.topologicalClosure_minimal _ (by rintro _ ⟨f, hf, rfl⟩; exact h f hf) hK

theorem mulL2_mem_hardySpace {f : C(X, ℂ)} (hf : f ∈ Algebra.adjoin ℂ {q, z})
    {u : Lp ℂ 2 μ} (hu : u ∈ hardySpace μ q z) : mulL2 μ f u ∈ hardySpace μ q z := by
  refine hardySpace_le (K := (hardySpace μ q z).comap (mulL2 μ f).toLinearMap)
    ((Submodule.isClosed_topologicalClosure _).preimage (mulL2 μ f).continuous)
    (fun g hg ↦ ?_) hu
  change mulL2 μ f (ContinuousMap.toLp 2 μ ℂ g) ∈ hardySpace μ q z
  rw [mulL2_toLp]
  exact toLp_mem_hardySpace ((Algebra.adjoin ℂ {q, z}).mul_mem hf hg)

variable (μ q z)

/-- Multiplication by `f ∈ ℂ[q, z]`, restricted to the Hardy space. -/
def hardyMul {f : C(X, ℂ)} (hf : f ∈ Algebra.adjoin ℂ {q, z}) :
    hardySpace μ q z →L[ℂ] hardySpace μ q z :=
  (mulL2 μ f ∘L (hardySpace μ q z).subtypeL).codRestrict _ fun u ↦
    mulL2_mem_hardySpace hf u.2

/-- The *Hardy shift* `T = M_q|_H`. -/
def hardyShift : hardySpace μ q z →L[ℂ] hardySpace μ q z :=
  hardyMul μ q z (left_mem_adjoin q z)

/-- The operator `S = M_z|_H`. -/
def hardyCoordinate : hardySpace μ q z →L[ℂ] hardySpace μ q z :=
  hardyMul μ q z (right_mem_adjoin q z)

variable {μ q z}

@[simp]
theorem coe_hardyShift_apply (u : hardySpace μ q z) :
    (hardyShift μ q z u : Lp ℂ 2 μ) = mulL2 μ q u :=
  rfl

@[simp]
theorem coe_hardyCoordinate_apply (u : hardySpace μ q z) :
    (hardyCoordinate μ q z u : Lp ℂ 2 μ) = mulL2 μ z u :=
  rfl

/-- `T` is an isometry. -/
theorem isometry_hardyShift (hq : star q * q = 1) : Isometry (hardyShift μ q z) := by
  refine AddMonoidHomClass.isometry_of_norm _ fun u ↦ ?_
  change ‖mulL2 μ q u‖ = ‖(u : Lp ℂ 2 μ)‖
  exact (isometry_mulL2 μ hq).norm_map_of_map_zero (map_zero _) _

theorem hardyShift_mul_hardyCoordinate :
    hardyShift μ q z * hardyCoordinate μ q z = hardyCoordinate μ q z * hardyShift μ q z := by
  refine ContinuousLinearMap.ext fun u ↦ Subtype.ext ?_
  exact congrArg (fun L : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ ↦ L u) (mulL2_commute μ q z)

/-- The relation `T† S = S†` [Hägg, (15)]. -/
theorem adjoint_hardyShift_mul_hardyCoordinate (hz : z = q * star z) :
    adjoint (hardyShift μ q z) * hardyCoordinate μ q z = adjoint (hardyCoordinate μ q z) := by
  refine ContinuousLinearMap.ext fun u ↦ ext_inner_right ℂ fun v ↦ ?_
  change ⟪adjoint (hardyShift μ q z) (hardyCoordinate μ q z u), v⟫_ℂ = _
  rw [adjoint_inner_left, adjoint_inner_left, Submodule.coe_inner, Submodule.coe_inner,
    coe_hardyShift_apply, coe_hardyCoordinate_apply, inner_mulL2_left, mulL2_mul_apply,
    coe_hardyCoordinate_apply]
  congr 3
  rw [mul_comm, ← hz]

/-- **`(T, S)` is a Möbius pair** [Hägg, (15)]: `T` is an isometry, `TS = ST`, `T† S = S†`, and
hence `S† T = S`. -/
theorem isMobiusPair_hardy (hq : star q * q = 1) (hz : z = q * star z) :
    IsMobiusPair (hardyShift μ q z) (hardyCoordinate μ q z) :=
  ⟨isometry_hardyShift hq, hardyShift_mul_hardyCoordinate,
    adjoint_hardyShift_mul_hardyCoordinate hz⟩

/-- **Fiber-spectrum inclusion** [Hägg, proof of Lemma 7].  Let `A` be the symbol of the Hardy
premodel of any finite measure `μ`, and `|w| = 1`.  Every spectral value `a` of `A + w A†` is a
value of the coordinates: `(w, a) = (q x, z x)` for some `x`. -/
theorem exists_eq_of_mem_spectrum_mobiusSymbol (hq : star q * q = 1) (hz : z = q * star z)
    {w a : ℂ} (hw : ‖w‖ = 1)
    (ha : a ∈ spectrum ℂ (mobiusSymbol (hardyShift μ q z) (hardyCoordinate μ q z) +
      w • adjoint (mobiusSymbol (hardyShift μ q z) (hardyCoordinate μ q z)))) :
    ∃ x, q x = w ∧ z x = a := by
  obtain ⟨u, hu, hT, hS⟩ := (isMobiusPair_hardy (μ := μ) hq hz).exists_seq_joint_approx_eigenvector
    hw ha
  exact exists_eq_of_tendsto_mulL2 μ q z w a (fun n ↦ (u n : Lp ℂ 2 μ)) hu hT hS

/-! #### The wandering vector `1` -/

variable (μ q z) in
/-- The constant function `1` in the Hardy space. -/
def hardyOne : hardySpace μ q z :=
  ⟨ContinuousMap.toLp 2 μ ℂ 1, toLp_mem_hardySpace (Algebra.adjoin ℂ {q, z}).one_mem⟩

theorem norm_hardyOne [IsProbabilityMeasure μ] : ‖hardyOne μ q z‖ = 1 := by
  have h : ‖hardyOne μ q z‖ ^ 2 = 1 := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ), Submodule.coe_inner]
    change RCLike.re ⟪ContinuousMap.toLp 2 μ ℂ 1, ContinuousMap.toLp 2 μ ℂ 1⟫_ℂ = 1
    rw [ContinuousMap.inner_toLp]
    simp
  nlinarith [norm_nonneg (hardyOne μ q z)]

/-- If `μ` annihilates `q ℂ[q, z]`, then `1 ∈ ker T†` [Hägg, proof of Lemma 7]. -/
theorem hardyOne_mem_wanderingSubspace
    (hrep : ∀ f ∈ Algebra.adjoin ℂ {q, z}, ∫ x, q x * f x ∂μ = 0) :
    hardyOne μ q z ∈ (hardyShift μ q z).wanderingSubspace := by
  rw [mem_wanderingSubspace]
  let Φ : Lp ℂ 2 μ →L[ℂ] ℂ := innerSL ℂ (ContinuousMap.toLp 2 μ ℂ 1) ∘L mulL2 μ q
  have hH : hardySpace μ q z ≤ Φ.ker := by
    refine hardySpace_le Φ.isClosed_ker fun f hf ↦ ?_
    change ⟪ContinuousMap.toLp 2 μ ℂ 1, mulL2 μ q (ContinuousMap.toLp 2 μ ℂ f)⟫_ℂ = 0
    rw [mulL2_toLp, ContinuousMap.inner_toLp]
    simpa using hrep f hf
  refine ext_inner_right ℂ fun u ↦ ?_
  rw [adjoint_inner_left, inner_zero_left, Submodule.coe_inner, coe_hardyShift_apply]
  exact hH u.2

/-- The wandering subspace `𝓔 = ker T†` of the Hardy shift is nonzero, since it contains the
unit vector `1`. -/
theorem wanderingSubspace_hardyShift_ne_bot [IsProbabilityMeasure μ]
    (hrep : ∀ f ∈ Algebra.adjoin ℂ {q, z}, ∫ x, q x * f x ∂μ = 0) :
    (hardyShift μ q z).wanderingSubspace ≠ ⊥ := by
  intro hbot
  have h1 := hardyOne_mem_wanderingSubspace hrep
  rw [hbot, Submodule.mem_bot] at h1
  have := norm_hardyOne (μ := μ) (q := q) (z := z)
  rw [h1, norm_zero] at this
  exact zero_ne_one this

/-! #### Purity -/

theorem coe_hardyCoordinate_pow_hardyOne (n : ℕ) :
    ((hardyCoordinate μ q z ^ n) (hardyOne μ q z) : Lp ℂ 2 μ) =
      ContinuousMap.toLp 2 μ ℂ (z ^ n) := by
  induction n with
  | zero => simp [hardyOne]
  | succ n ih => rw [pow_succ_apply', coe_hardyCoordinate_apply, ih, mulL2_toLp, pow_succ']

theorem coe_hardyShift_pow_apply (m : ℕ) {x : hardySpace μ q z} {g : C(X, ℂ)}
    (hx : (x : Lp ℂ 2 μ) = ContinuousMap.toLp 2 μ ℂ g) :
    ((hardyShift μ q z ^ m) x : Lp ℂ 2 μ) = ContinuousMap.toLp 2 μ ℂ (q ^ m * g) := by
  induction m with
  | zero => simpa using hx
  | succ m ih => rw [pow_succ_apply', coe_hardyShift_apply, ih, mulL2_toLp, pow_succ', mul_assoc]

/-- The vectors `Tᵐ Sⁿ 1 = qᵐ zⁿ` span a dense subspace of the Hardy space. -/
theorem dense_span_hardyShift_pow_hardyCoordinate_pow :
    Dense (Submodule.span ℂ (range fun p : ℕ × ℕ ↦
      (hardyShift μ q z ^ p.1) ((hardyCoordinate μ q z ^ p.2) (hardyOne μ q z))) :
        Set (hardySpace μ q z)) := by
  set D := Submodule.span ℂ (range fun p : ℕ × ℕ ↦
    (hardyShift μ q z ^ p.1) ((hardyCoordinate μ q z ^ p.2) (hardyOne μ q z)))
  have hspan : Submodule.span ℂ {f | ∃ m n : ℕ, q ^ m * z ^ n = f} ≤
      (D.map (hardySpace μ q z).subtype).comap
        (ContinuousMap.toLp 2 μ ℂ : C(X, ℂ) →L[ℂ] Lp ℂ 2 μ).toLinearMap := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨m, n, rfl⟩
    exact ⟨_, Submodule.subset_span ⟨(m, n), rfl⟩,
      coe_hardyShift_pow_apply m (coe_hardyCoordinate_pow_hardyOne n)⟩
  rw [dense_iff_closure_eq, eq_univ_iff_forall]
  intro u
  rw [closure_subtype]
  have hu : (u : Lp ℂ 2 μ) ∈ closure ((ContinuousMap.toLp 2 μ ℂ : C(X, ℂ) →L[ℂ] Lp ℂ 2 μ) ''
      (Algebra.adjoin ℂ {q, z} : Set C(X, ℂ))) := by
    have h : (u : Lp ℂ 2 μ) ∈ (hardySpace μ q z : Set (Lp ℂ 2 μ)) := u.2
    rwa [coe_hardySpace] at h
  refine closure_mono ?_ hu
  rintro _ ⟨p, hp, rfl⟩
  obtain ⟨v, hvD, hv⟩ := hspan (mem_span_monomials hp)
  exact ⟨v, hvD, hv⟩

/-- **The Hardy shift is a pure isometry** [Hägg, proof of Lemma 7]: if `μ` annihilates
`q ℂ[q, z]`, then every polynomial vector is killed by a power of `T†`, and polynomial vectors
are dense. -/
theorem isPureIsometry_hardyShift (hq : star q * q = 1) (hz : z = q * star z)
    (hrep : ∀ f ∈ Algebra.adjoin ℂ {q, z}, ∫ x, q x * f x ∂μ = 0) :
    IsPureIsometry (hardyShift μ q z) :=
  (isMobiusPair_hardy hq hz).isPureIsometry_of_dense_span (hardyOne_mem_wanderingSubspace hrep)
    dense_span_hardyShift_pow_hardyCoordinate_pow

/-- **Wold decomposition of the Hardy premodel**: `H = ⨁ₙ Tⁿ 𝓔` with `𝓔 = ker T†`, i.e.
`H ≃ H²(𝕋, 𝓔)` with `T ≃ M_q` [Hägg, proof of Lemma 7]. -/
theorem isHilbertSum_hardy (hq : star q * q = 1) (hz : z = q * star z)
    (hrep : ∀ f ∈ Algebra.adjoin ℂ {q, z}, ∫ x, q x * f x ∂μ = 0) :
    IsHilbertSum ℂ (fun _ : ℕ ↦ (hardyShift μ q z).wanderingSubspace)
      (woldEmbedding (isometry_hardyShift (μ := μ) (z := z) hq)) :=
  (isPureIsometry_hardyShift hq hz hrep).isHilbertSum

end HardyPremodel

/-! ### The Hardy-model reduction -/

section Reduction

open MeasureTheory

private theorem exp_mul_exp_neg (θ : ℝ) :
    Complex.exp (θ * Complex.I) * Complex.exp (-(θ * Complex.I)) = 1 := by
  rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]

private theorem exp_mul_exp_eq_exp_two_mul (θ : ℝ) :
    Complex.exp (θ * Complex.I) * Complex.exp (θ * Complex.I) =
      Complex.exp (2 * θ * Complex.I) := by
  rw [← Complex.exp_add]
  ring_nf

theorem norm_exp_two_mul_mul_I (θ : ℝ) : ‖Complex.exp (2 * θ * Complex.I)‖ = 1 := by
  have := Complex.norm_exp_ofReal_mul_I (2 * θ)
  push_cast at this
  exact this

/-- For `A` on a complex Hilbert space, `p ∈ σ(e^{-iθ} A + e^{iθ} A†)` iff
`e^{iθ} p ∈ σ(A + e^{2iθ} A†)`. -/
theorem mem_spectrum_add_smul_adjoint_of_mem_spectrum_real {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] (A : E →L[ℂ] E) (θ : ℝ) {p : ℝ}
    (hp : p ∈ spectrum ℝ (Complex.exp (-(θ * Complex.I)) • A +
      Complex.exp (θ * Complex.I) • adjoint A)) :
    Complex.exp (θ * Complex.I) * p ∈
      spectrum ℂ (A + Complex.exp (2 * θ * Complex.I) • adjoint A) := by
  have hpC : (p : ℂ) ∈ spectrum ℂ (Complex.exp (-(θ * Complex.I)) • A +
      Complex.exp (θ * Complex.I) • adjoint A) := by
    have := (spectrum.algebraMap_mem_iff ℂ (a := Complex.exp (-(θ * Complex.I)) • A +
      Complex.exp (θ * Complex.I) • adjoint A) (r := p)).2 hp
    simpa using this
  let r : ℂˣ := Units.mk0 (Complex.exp (θ * Complex.I)) (Complex.exp_ne_zero _)
  have h := (spectrum.smul_mem_smul_iff (r := r)).2 hpC
  have hsmul : r • (Complex.exp (-(θ * Complex.I)) • A +
      Complex.exp (θ * Complex.I) • adjoint A) =
      A + Complex.exp (2 * θ * Complex.I) • adjoint A := by
    rw [Units.smul_def, smul_add, smul_smul, smul_smul, Units.val_mk0, exp_mul_exp_neg,
      exp_mul_exp_eq_exp_two_mul, one_smul]
  rwa [hsmul, Units.smul_def, Units.val_mk0, smul_eq_mul] at h

/-- **Fiber-spectrum inclusion** [Hägg, (14)], for the Hardy premodel of any finite measure:
if `A` is the symbol of `(M_q|_H, M_z|_H)`, then every point `p` of the spectrum of the
self-adjoint operator `e^{-iθ} A + e^{iθ} A†` satisfies `(e^{2iθ}, p e^{iθ}) = (q x, z x)` for
some `x`. -/
theorem exists_eq_of_mem_spectrum_rotated_mobiusSymbol {X : Type*} [TopologicalSpace X]
    [CompactSpace X] [MeasurableSpace X] [BorelSpace X] {μ : Measure X} [IsFiniteMeasure μ]
    {q z : C(X, ℂ)} (hq : star q * q = 1) (hz : z = q * star z) (θ : ℝ) {p : ℝ}
    (hp : p ∈ spectrum ℝ
      (Complex.exp (-(θ * Complex.I)) • mobiusSymbol (hardyShift μ q z) (hardyCoordinate μ q z) +
        Complex.exp (θ * Complex.I) •
          adjoint (mobiusSymbol (hardyShift μ q z) (hardyCoordinate μ q z)))) :
    ∃ x, q x = Complex.exp (2 * θ * Complex.I) ∧ z x = p * Complex.exp (θ * Complex.I) := by
  obtain ⟨x, hx1, hx2⟩ := exists_eq_of_mem_spectrum_mobiusSymbol hq hz
    (norm_exp_two_mul_mul_I θ) (mem_spectrum_add_smul_adjoint_of_mem_spectrum_real _ θ hp)
  exact ⟨x, hx1, hx2.trans (mul_comm _ _)⟩

/-- **The Hardy-model reduction**, abstract form [Hägg, Lemma 7].  Let `X` be a compact
metrizable space and `q z : C(X, ℂ)` with `|q| = 1`, `z = q z̄`, and `x ↦ (q x, z x)` injective.
If a nonzero complex Borel measure `η` on `X` annihilates all monomials `z^j q^ℓ` with `ℓ ≥ 1`,
then there are a nonzero complex Hilbert space `𝓔` and an operator `A` on `𝓔` such that every
point `p` of the spectrum of `e^{-iθ} A + e^{iθ} A†` is realized as `q x = e^{2iθ}`,
`z x = p e^{iθ}` for some `x ∈ X`.

One can take `𝓔 = ker T†` and `A = P_𝓔 S|_𝓔`, where `T = M_q`, `S = M_z` on the `L²(μ)`-closure
of `ℂ[q, z]` and `μ` is a representing probability measure of a character of
`closure ℂ[q, z]` killing `q`.  Compact Hausdorff second-countable spaces are metrizable
(Urysohn, `TopologicalSpace.metrizableSpace_of_t3_secondCountable`), so the theorem applies to
them as well. -/
theorem hardy_model_reduction_of_continuousMap {X : Type u} [TopologicalSpace X] [CompactSpace X]
    [TopologicalSpace.MetrizableSpace X] [MeasurableSpace X] [BorelSpace X]
    (q z : C(X, ℂ)) (hq : star q * q = 1) (hz : z = q * star z)
    (hinj : Function.Injective fun x ↦ (q x, z x))
    (η : ComplexMeasure X) (hη : η ≠ 0)
    (hmom : ∀ j ℓ : ℕ, 1 ≤ ℓ →
      ∫ᵛ x, z x ^ j * q x ^ ℓ ∂[ContinuousLinearMap.mul ℝ ℂ; η] = 0) :
    ∃ (𝓔 : Type u) (_ : NormedAddCommGroup 𝓔) (_ : InnerProductSpace ℂ 𝓔) (_ : CompleteSpace 𝓔),
      Nontrivial 𝓔 ∧ ∃ A : 𝓔 →L[ℂ] 𝓔, ∀ θ : ℝ,
        ∀ p ∈ spectrum ℝ (Complex.exp (-(θ * Complex.I)) • A +
            Complex.exp (θ * Complex.I) • ContinuousLinearMap.adjoint A),
          ∃ x, q x = Complex.exp (2 * θ * Complex.I) ∧ z x = p * Complex.exp (θ * Complex.I) := by
  obtain ⟨χ, μ, hμ, hχ, hrep⟩ := exists_characterSpace_isProbabilityMeasure hq hz hinj hη hmom
  have hrep' : ∀ f ∈ Algebra.adjoin ℂ {q, z}, ∫ x, q x * f x ∂μ = 0 := fun f hf ↦
    integral_mul_eq_zero_of_characterSpace hχ hrep (adjoin_le_coordinateAlgebra q z hf)
  exact ⟨(hardyShift μ q z).wanderingSubspace, inferInstance, inferInstance, inferInstance,
    Submodule.nontrivial_iff_ne_bot.2 (wanderingSubspace_hardyShift_ne_bot hrep'),
    mobiusSymbol (hardyShift μ q z) (hardyCoordinate μ q z),
    fun θ _ hp ↦ exists_eq_of_mem_spectrum_rotated_mobiusSymbol hq hz θ hp⟩

/-- [Hägg, Lemma 7] for a compact Hausdorff second-countable space. -/
example {X : Type u} [TopologicalSpace X] [CompactSpace X] [T2Space X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X] (q z : C(X, ℂ)) (hq : star q * q = 1)
    (hz : z = q * star z) (hinj : Function.Injective fun x ↦ (q x, z x))
    (η : ComplexMeasure X) (hη : η ≠ 0)
    (hmom : ∀ j ℓ : ℕ, 1 ≤ ℓ →
      ∫ᵛ x, z x ^ j * q x ^ ℓ ∂[ContinuousLinearMap.mul ℝ ℂ; η] = 0) :
    ∃ (𝓔 : Type u) (_ : NormedAddCommGroup 𝓔) (_ : InnerProductSpace ℂ 𝓔) (_ : CompleteSpace 𝓔),
      Nontrivial 𝓔 ∧ ∃ A : 𝓔 →L[ℂ] 𝓔, ∀ θ : ℝ,
        ∀ p ∈ spectrum ℝ (Complex.exp (-(θ * Complex.I)) • A +
            Complex.exp (θ * Complex.I) • ContinuousLinearMap.adjoint A),
          ∃ x, q x = Complex.exp (2 * θ * Complex.I) ∧ z x = p * Complex.exp (θ * Complex.I) :=
  hardy_model_reduction_of_continuousMap q z hq hz hinj η hη hmom

/-- The Möbius real line bundle `Σ = {(q, z) ∈ 𝕋 × ℂ | z = q z̄}` over the unit circle [Hägg, §2];
its points parametrize unoriented lines. -/
def mobiusBundle : Set (ℂ × ℂ) := {w | ‖w.1‖ = 1 ∧ w.2 = w.1 * (starRingEnd ℂ) w.2}

/-- **The Hardy-model reduction** [Hägg, Lemma 7].  Let `X ⊆ Σ` be compact and let `η ≠ 0` be a
complex Borel measure on `X` with `∫_X z^j q^ℓ dη = 0` for all `j ≥ 0`, `ℓ ≥ 1`.  Then there are a
nonzero complex Hilbert space `𝓔` and an operator `A` on `𝓔` such that for every `θ`,
`σ(e^{-iθ} A + e^{iθ} A†) ⊆ {p ∈ ℝ | (e^{2iθ}, p e^{iθ}) ∈ X}`. -/
theorem hardy_model_reduction {X : Set (ℂ × ℂ)} (hXc : IsCompact X) (hXM : X ⊆ mobiusBundle)
    (η : MeasureTheory.ComplexMeasure X) (hη : η ≠ 0)
    (hmom : ∀ j ℓ : ℕ, 1 ≤ ℓ →
      ∫ᵛ w, ((w : ℂ × ℂ).2 ^ j * (w : ℂ × ℂ).1 ^ ℓ) ∂[ContinuousLinearMap.mul ℝ ℂ; η] = 0) :
    ∃ (𝓔 : Type) (_ : NormedAddCommGroup 𝓔) (_ : InnerProductSpace ℂ 𝓔) (_ : CompleteSpace 𝓔),
      Nontrivial 𝓔 ∧ ∃ A : 𝓔 →L[ℂ] 𝓔, ∀ θ : ℝ,
        spectrum ℝ (Complex.exp (-(θ * Complex.I)) • A +
            Complex.exp (θ * Complex.I) • ContinuousLinearMap.adjoint A) ⊆
          {p : ℝ | (Complex.exp (2 * θ * Complex.I), (p : ℂ) * Complex.exp (θ * Complex.I)) ∈
            X} := by
  have : CompactSpace X := isCompact_iff_compactSpace.1 hXc
  let q : C(X, ℂ) := ⟨fun w ↦ (w : ℂ × ℂ).1, continuous_fst.comp continuous_subtype_val⟩
  let z : C(X, ℂ) := ⟨fun w ↦ (w : ℂ × ℂ).2, continuous_snd.comp continuous_subtype_val⟩
  have hq : star q * q = 1 := by
    ext w
    have h1 : ‖(w : ℂ × ℂ).1‖ = 1 := (hXM w.2).1
    change star (w : ℂ × ℂ).1 * (w : ℂ × ℂ).1 = 1
    rw [RCLike.star_def, RCLike.conj_mul, h1]
    simp
  have hz : z = q * star z := by
    ext w
    exact (hXM w.2).2
  have hinj : Function.Injective fun x ↦ (q x, z x) := fun x y hxy ↦ Subtype.ext hxy
  obtain ⟨𝓔, i₁, i₂, i₃, hnt, A, hA⟩ :=
    hardy_model_reduction_of_continuousMap q z hq hz hinj η hη hmom
  refine ⟨𝓔, i₁, i₂, i₃, hnt, A, fun θ p hp ↦ ?_⟩
  obtain ⟨x, hx₁, hx₂⟩ := hA θ p hp
  have hx : (x : ℂ × ℂ) =
      (Complex.exp (2 * θ * Complex.I), (p : ℂ) * Complex.exp (θ * Complex.I)) :=
    Prod.ext hx₁ hx₂
  rw [mem_ofPred_eq, ← hx]
  exact x.2

/-- **The Hardy-model reduction** [Hägg, Lemma 7], for a complex measure `η` on `ℂ × ℂ` whose
variation is carried by the compact set `X ⊆ Σ` (the measure on `X` is `η.comap Subtype.val`). -/
theorem hardy_model_reduction_of_variation_compl_eq_zero {X : Set (ℂ × ℂ)} (hXc : IsCompact X)
    (hXM : X ⊆ mobiusBundle) (η : MeasureTheory.ComplexMeasure (ℂ × ℂ)) (hη : η ≠ 0)
    (hηX : η.variation Xᶜ = 0)
    (hmom : ∀ j ℓ : ℕ, 1 ≤ ℓ →
      ∫ᵛ w, (w.2 ^ j * w.1 ^ ℓ) ∂[ContinuousLinearMap.mul ℝ ℂ; η] = 0) :
    ∃ (𝓔 : Type) (_ : NormedAddCommGroup 𝓔) (_ : InnerProductSpace ℂ 𝓔) (_ : CompleteSpace 𝓔),
      Nontrivial 𝓔 ∧ ∃ A : 𝓔 →L[ℂ] 𝓔, ∀ θ : ℝ,
        spectrum ℝ (Complex.exp (-(θ * Complex.I)) • A +
            Complex.exp (θ * Complex.I) • ContinuousLinearMap.adjoint A) ⊆
          {p : ℝ | (Complex.exp (2 * θ * Complex.I), (p : ℂ) * Complex.exp (θ * Complex.I)) ∈
            X} := by
  have hf : MeasurableEmbedding (Subtype.val : X → ℂ × ℂ) :=
    MeasurableEmbedding.subtype_coe hXc.isClosed.measurableSet
  have hv : η.variation (range (Subtype.val : X → ℂ × ℂ))ᶜ = 0 := by
    rwa [Subtype.range_coe]
  refine hardy_model_reduction hXc hXM (η.comap Subtype.val)
    (fun h0 ↦ hη ((VectorMeasure.comap_eq_zero_iff_of_variation_compl_range_eq_zero hf hv).1 h0))
    fun j ℓ hℓ ↦ ?_
  rw [VectorMeasure.integral_comap hf hv (ContinuousLinearMap.mul ℝ ℂ)
    (fun w : ℂ × ℂ ↦ w.2 ^ j * w.1 ^ ℓ)]
  exact hmom j ℓ hℓ

end Reduction

end LeanestEllipse
