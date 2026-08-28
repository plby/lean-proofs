import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationFourierDerivativeBasic
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Differentiation of actual translated torus integrals

The directional derivative is continuous on the compact torus.  Its actual
supremum norm supplies an integrable bound, so differentiation under the
Haar integral is proved from the smooth lift, with no domination assumption.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassification

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

variable {d : Type*} [Fintype d]

/-- Translated smooth torus functions may be differentiated under the actual
Haar integral against every continuous multiplier. -/
theorem hasDerivAt_integral_torus_translate (f : SmoothTorusFunction d)
    (h : C(UnitAddTorus d, ℂ)) (v : d → ℝ) (s : ℝ) :
    HasDerivAt
      (fun r : ℝ => ∫ t : UnitAddTorus d, h t * f (t + torusQuotient (r • v)))
      (∫ t : UnitAddTorus d, h t *
        torusDirectionalDerivative f v (t + torusQuotient (s • v))) s := by
  let D := torusDirectionalDerivative f v
  let F : ℝ → UnitAddTorus d → ℂ :=
    fun r t => h t * f (t + torusQuotient (r • v))
  let F' : ℝ → UnitAddTorus d → ℂ :=
    fun r t => h t * D (t + torusQuotient (r • v))
  have hcont (r : ℝ) : Continuous (F r) :=
    h.continuous.mul (f.toContinuousMap.continuous.comp
      (continuous_id.add continuous_const))
  have hcont' (r : ℝ) : Continuous (F' r) :=
    h.continuous.mul (D.toContinuousMap.continuous.comp
      (continuous_id.add continuous_const))
  have hbound (t : UnitAddTorus d) (r : ℝ) :
      ‖F' r t‖ ≤ ‖h‖ * ‖D.toContinuousMap‖ := by
    dsimp only [F']
    rw [norm_mul]
    exact mul_le_mul (h.norm_coe_le_norm t)
      (D.toContinuousMap.norm_coe_le_norm (t + torusQuotient (r • v)))
      (norm_nonneg _) (norm_nonneg _)
  have hdiff (t : UnitAddTorus d) (r : ℝ) : HasDerivAt (fun a => F a t) (F' r t) r :=
    (hasDerivAt_torus_translate f v t r).const_mul (h t)
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := (volume : Measure (UnitAddTorus d)))
    (F := F) (F' := F') (x₀ := s) (s := Set.univ)
    (bound := fun _ => ‖h‖ * ‖D.toContinuousMap‖) Filter.univ_mem
    (Eventually.of_forall fun r => (hcont r).aestronglyMeasurable)
    ((hcont s).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    (hcont' s).aestronglyMeasurable
    (ae_of_all _ fun t r _ => hbound t r)
    (integrable_const _) (ae_of_all _ fun t r _ => hdiff t r)
  exact h.2

end Wikipedia.HopfProblem.PeriodTorusLineBundleClassification
