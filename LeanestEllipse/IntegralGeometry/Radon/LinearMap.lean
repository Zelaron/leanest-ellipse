import LeanestEllipse.IntegralGeometry.Radon.Basic

/-!
# The Radon transform commutes with linear maps

For a continuous linear map `L : F →L[ℝ] G`, `radonTransform (L ∘ f) ω p = L (radonTransform f ω p)`
whenever `f` is integrable on the hyperplane (`ContinuousLinearMap.radonTransform_comp`); for linear
isometries and continuous linear equivalences no integrability is needed.  In particular the Radon
transform of a real-valued function, viewed as a complex-valued one, is the real Radon transform
viewed as a complex number (`radonTransform_ofReal`, `radonTransform_complex_ofReal`).
-/

open MeasureTheory Submodule

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- A continuous linear map commutes with the Radon transform on hyperplanes on which the function
is integrable. -/
theorem ContinuousLinearMap.radonTransform_comp [CompleteSpace F] [CompleteSpace G]
    (L : F →L[ℝ] G) {f : E → F}
    {ω : E} {p : ℝ} (hf : Integrable fun y : (ℝ ∙ ω)ᗮ ↦ f (p • ω + y)) :
    radonTransform (fun x ↦ L (f x)) ω p = L (radonTransform f ω p) :=
  L.integral_comp_comm hf

/-- A linear isometry commutes with the Radon transform. -/
theorem LinearIsometry.radonTransform_comp [CompleteSpace F] [CompleteSpace G] (L : F →ₗᵢ[ℝ] G)
    (f : E → F) (ω : E) (p : ℝ) :
    radonTransform (fun x ↦ L (f x)) ω p = L (radonTransform f ω p) :=
  L.integral_comp_comm _

/-- A continuous linear equivalence commutes with the Radon transform. -/
theorem ContinuousLinearEquiv.radonTransform_comp (L : F ≃L[ℝ] G) (f : E → F) (ω : E) (p : ℝ) :
    radonTransform (fun x ↦ L (f x)) ω p = L (radonTransform f ω p) :=
  L.integral_comp_comm _

/-- The Radon transform of a real function viewed as an `RCLike`-valued (e.g. complex-valued)
function is the real Radon transform. -/
@[simp, norm_cast]
theorem radonTransform_ofReal {𝕜 : Type*} [RCLike 𝕜] (f : E → ℝ) (ω : E) (p : ℝ) :
    radonTransform (fun x ↦ (f x : 𝕜)) ω p = ((radonTransform f ω p : ℝ) : 𝕜) :=
  integral_ofReal

/-- The Radon transform of a real function viewed as a complex-valued function is the real Radon
transform. -/
@[simp, norm_cast]
theorem radonTransform_complex_ofReal (f : E → ℝ) (ω : E) (p : ℝ) :
    radonTransform (fun x ↦ (f x : ℂ)) ω p = ((radonTransform f ω p : ℝ) : ℂ) :=
  integral_complex_ofReal

end
