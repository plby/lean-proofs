import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyFourierParameter
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Differentiating the Haar Fourier integral with derived local domination

A jointly continuous genuine differential on the original open base times
the compact unit torus has a uniform bound on a compact base neighborhood.
The unit-norm Fourier character preserves that bound. This supplies all
domination needed for real Fréchet differentiation under the actual Haar
integral; no bound is a premise of the differentiation theorem.
-/

noncomputable section

open MeasureTheory Filter TopologicalSpace UnitAddTorus
open scoped ContDiff Topology

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.FourierParameter.Derivative

open PeriodTorusLineBundleClassification

local instance derivativeIntegralMeasureSpaceUnitAddCircle : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance derivativeIntegralIsProbabilityMeasure :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
local instance derivativeIntegralIsAddHaarMeasure :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

variable {U : Opens ℂ} {d : Type*}

/-- Extension used only to write a derivative on the ambient original base chart. -/
def extendedDifferential (D : C(U × UnitAddTorus d, ℂ →L[ℝ] ℂ))
    (x : ℂ × UnitAddTorus d) : ℂ →L[ℝ] ℂ := by
  classical
  exact if hx : x.1 ∈ U then D (⟨x.1, hx⟩, x.2) else 0

@[simp] theorem extendedDifferential_apply (D : C(U × UnitAddTorus d, ℂ →L[ℝ] ℂ))
    (b : U) (t : UnitAddTorus d) :
    extendedDifferential D ((b : ℂ), t) = D (b, t) := by
  simp only [extendedDifferential, dif_pos b.property]

/-- Compactness derives the actual differential bound on a common base neighborhood. -/
theorem exists_compact_differential_bound (D : C(U × UnitAddTorus d, ℂ →L[ℝ] ℂ))
    (b : U) :
    ∃ K : Set U, IsCompact K ∧ K ∈ 𝓝 b ∧
      ∃ C : ℝ, 0 < C ∧ ∀ z ∈ K, ∀ t : UnitAddTorus d, ‖D (z, t)‖ ≤ C := by
  let : LocallyCompactSpace U := U.isOpen.locallyCompactSpace
  obtain ⟨K, hK, hbK⟩ := exists_compact_mem_nhds b
  obtain ⟨C, hC, hbound⟩ :=
    ((hK.prod (isCompact_univ : IsCompact (Set.univ : Set (UnitAddTorus d)))).image
      D.continuous).isBounded.exists_pos_norm_le
  exact ⟨K, hK, hbK, C, hC, fun z hz t => hbound _ ⟨(z, t), ⟨hz, Set.mem_univ t⟩, rfl⟩⟩

variable [Fintype d]

/-- The Fourier-weighted genuine differential is integrable on the actual compact torus. -/
theorem weightedDifferential_integrable (D : C(U × UnitAddTorus d, ℂ →L[ℝ] ℂ))
    (k : d → ℤ) (b : U) :
    Integrable (fun t : UnitAddTorus d => mFourier (-k) t • D (b, t)) :=
  ((mFourier (-k)).continuous.smul
    (D.continuous.comp (continuous_const.prodMk continuous_id))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

/-- The actual normalized Haar integral of the Fourier-weighted differential. -/
def fourierDifferential (D : C(U × UnitAddTorus d, ℂ →L[ℝ] ℂ))
    (k : d → ℤ) (b : U) : ℂ →L[ℝ] ℂ :=
  ∫ t : UnitAddTorus d, mFourier (-k) t • D (b, t)

/-- Evaluation of the integrated differential is the genuine Fourier coefficient. -/
theorem fourierDifferential_apply (D : C(U × UnitAddTorus d, ℂ →L[ℝ] ℂ))
    (k : d → ℤ) (b : U) (v : ℂ) :
    fourierDifferential D k b v = mFourierCoeff (fun t => D (b, t) v) k := by
  rw [fourierDifferential,
    ContinuousLinearMap.integral_apply (weightedDifferential_integrable D k b)]
  rfl

/-- Full real Fréchet differentiation of the actual Haar Fourier coefficient.
The common local domination is proved from the genuine continuous differential. -/
theorem hasFDerivAt_fourier_of_continuous_differential
    (F : ℂ × UnitAddTorus d → ℂ) (D : C(U × UnitAddTorus d, ℂ →L[ℝ] ℂ))
    (hF : ∀ b : U, Continuous (fun t : UnitAddTorus d => F ((b : ℂ), t)))
    (hDiff : ∀ (b : U) (t : UnitAddTorus d),
      HasFDerivAt (fun z : ℂ => F (z, t)) (D (b, t)) (b : ℂ))
    (k : d → ℤ) (b : U) :
    HasFDerivAt (fun z : ℂ => mFourierCoeff (fun t => F (z, t)) k)
      (fourierDifferential D k b) (b : ℂ) := by
  obtain ⟨K, _, hKb, C, _, hbound⟩ := exists_compact_differential_bound D b
  let G : ℂ → UnitAddTorus d → ℂ := fun z t => mFourier (-k) t • F (z, t)
  let G' : ℂ → UnitAddTorus d → ℂ →L[ℝ] ℂ :=
    fun z t => mFourier (-k) t • extendedDifferential D (z, t)
  have hcont (z : U) : Continuous (G (z : ℂ)) :=
    (mFourier (-k)).continuous.smul (hF z)
  have hcont' : Continuous (G' (b : ℂ)) := by
    simpa only [G', extendedDifferential_apply, Pi.smul_def', Function.comp_def, id] using
      (mFourier (-k)).continuous.smul
        (D.continuous.comp (continuous_const.prodMk continuous_id))
  have hmeas : ∀ᶠ z in 𝓝 (b : ℂ), AEStronglyMeasurable (G z) := by
    filter_upwards [U.isOpen.mem_nhds b.property] with z hz
    exact (hcont ⟨z, hz⟩).aestronglyMeasurable
  have hderiv (z : U) (t : UnitAddTorus d) :
      HasFDerivAt (fun a : ℂ => G a t) (G' (z : ℂ) t) (z : ℂ) := by
    simpa only [G, G', extendedDifferential_apply, Pi.smul_def] using
      (hDiff z t).const_smul (mFourier (-k) t)
  have hd := hasFDerivAt_integral_of_dominated_of_fderiv_le
    (𝕜 := ℝ) (μ := (volume : Measure (UnitAddTorus d)))
    (F := G) (F' := G') (x₀ := (b : ℂ)) (s := Subtype.val '' K)
    (bound := fun _ => C) (U.isOpen.isOpenMap_subtype_val.image_mem_nhds hKb)
    hmeas ((hcont b).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    hcont'.aestronglyMeasurable
    (ae_of_all _ (fun t z hz => by
      obtain ⟨w, hw, rfl⟩ := hz
      simpa only [G', extendedDifferential_apply, norm_smul, torusMonomial_norm, one_mul] using
        hbound w hw t))
    (integrable_const C)
    (ae_of_all _ (fun t z hz => by
      obtain ⟨w, _, rfl⟩ := hz
      exact hderiv w t))
  simpa only [G, G', extendedDifferential_apply, fourierDifferential, mFourierCoeff] using hd

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.FourierParameter.Derivative
