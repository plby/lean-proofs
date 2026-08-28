import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationFourierBasic
import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationFourierDerivativeBasic
import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Continuous parameter dependence of the actual torus Fourier coefficients

A jointly continuous function on a parameter space times the unit torus gives
a continuous family in the genuine sup-norm space of torus functions. Composing
with the already proved Haar Fourier coefficient functional gives continuous
coefficients. Compact parameter sets provide a common bound for all fibre
values and all Fourier modes. No local compactness, separation, or countability
assumption is imposed on the parameter space.
-/

noncomputable section

open MeasureTheory UnitAddTorus

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.FourierParameter

open PeriodTorusLineBundleClassification

variable {B d : Type*} [TopologicalSpace B] [Fintype d]

/-- The original continuous torus function at a fixed parameter. -/
def slice (f : C(B × UnitAddTorus d, ℂ)) (b : B) : C(UnitAddTorus d, ℂ) :=
  f.curry b

omit [Fintype d] in
@[simp] theorem slice_apply (f : C(B × UnitAddTorus d, ℂ))
    (b : B) (t : UnitAddTorus d) : slice f b t = f (b, t) := rfl

omit [Fintype d] in
/-- Joint continuity gives continuity into the actual sup-norm function space. -/
theorem slice_continuous (f : C(B × UnitAddTorus d, ℂ)) : Continuous (slice f) :=
  f.curry.continuous

/-- The original Haar Fourier coefficient, bundled as a continuous parameter function. -/
def coefficientMap (f : C(B × UnitAddTorus d, ℂ)) (k : d → ℤ) : C(B, ℂ) where
  toFun b := mFourierCoeff (fun t => f (b, t)) k
  continuous_toFun := (torusFourierCoeffCLM k).continuous.comp (slice_continuous f)

@[simp] theorem coefficientMap_apply (f : C(B × UnitAddTorus d, ℂ))
    (k : d → ℤ) (b : B) :
    coefficientMap f k b = mFourierCoeff (fun t => f (b, t)) k := rfl

/-- The literal parameterized `mFourierCoeff` is continuous. -/
theorem coefficient_continuous (f : C(B × UnitAddTorus d, ℂ)) (k : d → ℤ) :
    Continuous (fun b => mFourierCoeff (fun t => f (b, t)) k) :=
  (coefficientMap f k).continuous

/-- The coefficient uses exactly the product of the normalized circle Haar measures. -/
theorem coefficientMap_eq_integral (f : C(B × UnitAddTorus d, ℂ))
    (k : d → ℤ) (b : B) :
    coefficientMap f k b =
      ∫ t : UnitAddTorus d, mFourier (-k) t * f (b, t)
        ∂Measure.pi (fun _ : d => AddCircle.haarAddCircle) := rfl

omit [Fintype d] in
/-- The genuine sup norm of the original fibre function is continuous in the parameter. -/
theorem sliceNorm_continuous (f : C(B × UnitAddTorus d, ℂ)) :
    Continuous (fun b => ‖slice f b‖) :=
  continuous_norm.comp (slice_continuous f)

omit [Fintype d] in
/-- Every original fibre value is bounded by that fibre's genuine sup norm. -/
theorem norm_apply_le_sliceNorm (f : C(B × UnitAddTorus d, ℂ))
    (b : B) (t : UnitAddTorus d) : ‖f (b, t)‖ ≤ ‖slice f b‖ :=
  (slice f b).norm_coe_le_norm t

/-- The bound for every actual Fourier mode is the same genuine fibre norm. -/
theorem coefficient_norm_le_sliceNorm (f : C(B × UnitAddTorus d, ℂ))
    (b : B) (k : d → ℤ) :
    ‖mFourierCoeff (fun t => f (b, t)) k‖ ≤ ‖slice f b‖ :=
  torusFourierCoeff_norm_le (slice f b) k

/-- Parameter differences obey the uniform-in-mode bound from the actual Fourier functional. -/
theorem coefficient_sub_norm_le (f : C(B × UnitAddTorus d, ℂ))
    (b c : B) (k : d → ℤ) :
    ‖coefficientMap f k b - coefficientMap f k c‖ ≤ ‖slice f b - slice f c‖ := by
  change ‖mFourierCoeff (slice f b) k - mFourierCoeff (slice f c) k‖ ≤ _
  rw [← torusFourierCoeff_sub]
  exact torusFourierCoeff_norm_le (slice f b - slice f c) k

omit [Fintype d] in
/-- Compact parameter sets have a common positive bound for their fibre sup norms. -/
theorem exists_pos_uniform_slice_bound (f : C(B × UnitAddTorus d, ℂ))
    {K : Set B} (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ b ∈ K, ‖slice f b‖ ≤ C := by
  obtain ⟨C, hC, hbound⟩ :=
    (hK.image (slice_continuous f)).isBounded.exists_pos_norm_le
  exact ⟨C, hC, fun b hb => hbound _ ⟨b, hb, rfl⟩⟩

omit [Fintype d] in
/-- The same compact-parameter argument bounds all original fibre values at once. -/
theorem exists_pos_uniform_value_bound (f : C(B × UnitAddTorus d, ℂ))
    {K : Set B} (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ b ∈ K, ∀ t : UnitAddTorus d, ‖f (b, t)‖ ≤ C := by
  obtain ⟨C, hC, hbound⟩ := exists_pos_uniform_slice_bound f hK
  exact ⟨C, hC, fun b hb t => (norm_apply_le_sliceNorm f b t).trans (hbound b hb)⟩

/-- On a compact parameter set one constant bounds every actual Fourier coefficient. -/
theorem exists_pos_uniform_coefficient_bound (f : C(B × UnitAddTorus d, ℂ))
    {K : Set B} (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ b ∈ K, ∀ k : d → ℤ,
      ‖mFourierCoeff (fun t => f (b, t)) k‖ ≤ C := by
  obtain ⟨C, hC, hbound⟩ := exists_pos_uniform_slice_bound f hK
  exact ⟨C, hC, fun b hb k => (coefficient_norm_le_sliceNorm f b k).trans (hbound b hb)⟩

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.FourierParameter
