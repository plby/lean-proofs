/- leanprover/lean4:v4.32.0  mathlib v4.32.0 -/
import ErdosProblems.Erdos390.PoissonDickmanExponentialSpacings
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Kernel.Composition.MeasureCompProd

namespace Erdos390

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

noncomputable section

/-- Total mass of a labelled configuration. -/
def poissonDickmanTotalMass
    (π : PoissonDickmanConfiguration) : ℝ :=
  ∑' n : ℕ, π n

theorem measurable_poissonDickmanTotalMass :
    Measurable poissonDickmanTotalMass := by
  exact Measurable.tsum fun n ↦
    measurable_pi_apply n

/-- Distribution of the total mass of the unconditioned process. -/
def poissonDickmanTotalMassLaw : Measure ℝ :=
  poissonDickmanUnconditionedLaw.map
    poissonDickmanTotalMass

instance : IsProbabilityMeasure poissonDickmanTotalMassLaw := by
  unfold poissonDickmanTotalMassLaw
  exact Measure.isProbabilityMeasure_map
    measurable_poissonDickmanTotalMass.aemeasurable

/--
The regular conditional distribution of the exponential-spacing
configuration given its total mass.

The generic disintegration theorem determines this kernel only for
`poissonDickmanTotalMassLaw`-almost every mass.  Later the Dickman
density and Campbell identities select the continuous version needed
at the paper's particular value `U = 9/2`.
-/
def poissonDickmanConditionedKernel :
    Kernel ℝ PoissonDickmanConfiguration :=
  condDistrib id poissonDickmanTotalMass
    poissonDickmanUnconditionedLaw

instance : IsMarkovKernel poissonDickmanConditionedKernel := by
  unfold poissonDickmanConditionedKernel
  infer_instance

/--
The defining disintegration identity for the conditional family.
-/
theorem poissonDickmanTotalMassLaw_compProd_conditionedKernel :
    poissonDickmanTotalMassLaw ⊗ₘ
        poissonDickmanConditionedKernel =
      poissonDickmanUnconditionedLaw.map
        (fun π ↦
          (poissonDickmanTotalMass π, π)) := by
  unfold poissonDickmanTotalMassLaw
  unfold poissonDickmanConditionedKernel
  exact compProd_map_condDistrib
    (X := poissonDickmanTotalMass)
    (Y := id)
    (μ := poissonDickmanUnconditionedLaw)
    measurable_id.aemeasurable

theorem measurableSet_poissonDickmanTotalMass_eq_fst :
    MeasurableSet
      {q : ℝ × PoissonDickmanConfiguration |
        poissonDickmanTotalMass q.2 = q.1} :=
  measurableSet_eq_fun
    (measurable_poissonDickmanTotalMass.comp measurable_snd)
    measurable_fst

/--
For almost every mass, its conditional law is concentrated on
configurations having exactly that mass.
-/
theorem ae_conditionedKernel_totalMass_eq :
    ∀ᵐ u : ℝ ∂poissonDickmanTotalMassLaw,
      ∀ᵐ π : PoissonDickmanConfiguration
        ∂poissonDickmanConditionedKernel u,
        poissonDickmanTotalMass π = u := by
  refine
    Measure.ae_ae_of_ae_compProd
      (p := fun q : ℝ × PoissonDickmanConfiguration ↦
        poissonDickmanTotalMass q.2 = q.1) ?_
  rw [poissonDickmanTotalMassLaw_compProd_conditionedKernel]
  apply
    (ae_map_iff
      (measurable_poissonDickmanTotalMass.prodMk
        measurable_id).aemeasurable
      measurableSet_poissonDickmanTotalMass_eq_fst).2
  exact ae_of_all _ fun π ↦ rfl

/--
For almost every mass, the conditional law has the summable
`[0,1]`-valued support asserted in the paper.
-/
theorem ae_conditionedKernel_support :
    ∀ᵐ u : ℝ ∂poissonDickmanTotalMassLaw,
      ∀ᵐ π : PoissonDickmanConfiguration
        ∂poissonDickmanConditionedKernel u,
        IsPoissonDickmanSummableConfiguration π := by
  have hjoint :
      ∀ᵐ q : ℝ × PoissonDickmanConfiguration
        ∂poissonDickmanUnconditionedLaw.map
          (fun π ↦
            (poissonDickmanTotalMass π, π)),
        IsPoissonDickmanAbsolutelySummableConfiguration q.2 := by
    apply
      (ae_map_iff
        (measurable_poissonDickmanTotalMass.prodMk
          measurable_id).aemeasurable
        (measurable_snd
          measurableSet_isPoissonDickmanAbsolutelySummableConfiguration)).2
    have hsupport :
        ∀ᵐ π : PoissonDickmanConfiguration
          ∂poissonDickmanUnconditionedLaw,
          IsPoissonDickmanAbsolutelySummableConfiguration π := by
      unfold poissonDickmanUnconditionedLaw
      exact
        (ae_map_iff
          measurable_poissonDickmanSpacingConfiguration.aemeasurable
          measurableSet_isPoissonDickmanAbsolutelySummableConfiguration).2
          (by
            filter_upwards
              [ae_poissonDickmanSpacingTotal_lt_top] with e he
            constructor
            · intro n
              exact
                ⟨(poissonDickmanSpacingConfiguration_mem_Ioc e n).1.le,
                  (poissonDickmanSpacingConfiguration_mem_Ioc e n).2⟩
            · simpa only [
                abs_of_pos
                  (poissonDickmanSpacingConfiguration_mem_Ioc e _).1] using he)
    exact hsupport
  rw [←
    poissonDickmanTotalMassLaw_compProd_conditionedKernel] at hjoint
  exact
    (Measure.ae_ae_of_ae_compProd hjoint).mono
      fun _ hu ↦ hu.mono fun _ hπ ↦
        hπ.toSummableConfiguration

end

end Erdos390
