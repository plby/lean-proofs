import ErdosProblems.Erdos1002.MarkedCountLaws
import ErdosProblems.Erdos1002.CompoundPoisson

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Continuous images of finite count vectors

After a marked region has been divided into finitely many cells, a simple
shot functional is a weighted sum of the cell counts.  This file supplies
the exact continuous-mapping step from the independent-Poisson count-vector
limit to the law of that weighted sum.
-/

open Filter MeasureTheory
open scoped BigOperators Topology

namespace Erdos1002

noncomputable section

open MultivariateFactorialMomentMethod
open ProbabilityTheory

variable {ι : Type*} [Fintype ι]

/-- A finite weighted sum of a vector of natural-valued counts. -/
def weightedCountSum (w : ι → ℝ) (x : ι → ℕ) : ℝ :=
  ∑ i, (x i : ℝ) * w i

/-- A finite product of discrete spaces is discrete, so every weighted
count functional is continuous. -/
theorem continuous_weightedCountSum (w : ι → ℝ) :
    Continuous (weightedCountSum w) := by
  exact continuous_of_discreteTopology

/-- Law of the weighted marked-resonance cell counts. -/
def weightedMarkedCountLaw (N P : ℕ)
    (B : ι → Set (ℝ × ℝ × ℝ))
    (hB : ∀ i, MeasurableSet (B i)) (w : ι → ℝ) :
    ProbabilityMeasure ℝ :=
  (markedResonanceCountVectorLaw N P B hB).map
    (continuous_weightedCountSum w).measurable.aemeasurable

/-- The corresponding weighted sum of independent Poisson counts. -/
def weightedIndependentPoissonLaw (r : ι → NNReal) (w : ι → ℝ) :
    ProbabilityMeasure ℝ :=
  (independentPoissonProbabilityMeasure r).map
    (continuous_weightedCountSum w).measurable.aemeasurable

/-- Mixed factorial convergence of the actual marked counts implies weak
convergence of every finite simple shot functional. -/
theorem tendsto_weightedMarkedCountLaw_of_mixedFactorialMoments
    (Ns Ps : ℕ → ℕ) (B : ι → Set (ℝ × ℝ × ℝ))
    (hB : ∀ i, MeasurableSet (B i)) (r : ι → NNReal)
    (w : ι → ℝ)
    (hFac : ∀ k : ι → ℕ,
      Tendsto
        (fun n ↦ mixedFactorialMoment
          (markedResonanceCountVectorLaw (Ns n) (Ps n) B hB) k)
        atTop (nhds (∏ i, (r i : ℝ) ^ (k i)))) :
    Tendsto
      (fun n ↦ weightedMarkedCountLaw (Ns n) (Ps n) B hB w)
      atTop (nhds (weightedIndependentPoissonLaw r w)) := by
  have hcounts :=
    tendsto_markedResonanceCountVectorLaw_of_mixedFactorialMoments
      Ns Ps B hB r hFac
  simpa only [weightedMarkedCountLaw, weightedIndependentPoissonLaw] using!
    ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
      (fun n ↦ markedResonanceCountVectorLaw (Ns n) (Ps n) B hB)
      (independentPoissonProbabilityMeasure r) hcounts
      (continuous_weightedCountSum w)

/-- The limiting simple-shot law has the expected finite compound-Poisson
characteristic exponent.  This is proved on the actual finite product
measure, not inserted as an assumed formula. -/
theorem charFun_weightedIndependentPoissonLaw
    (r : ι → NNReal) (w : ι → ℝ) (t : ℝ) :
    charFun (weightedIndependentPoissonLaw r w : Measure ℝ) t =
      Complex.exp (∑ i, (r i : ℂ) *
        (Complex.exp (t * w i * Complex.I) - 1)) := by
  classical
  let μ : ι → Measure ℕ := fun i ↦ poissonMeasure (r i)
  let P : Measure (ι → ℕ) := Measure.pi μ
  let X : ι → (ι → ℕ) → ℝ := fun i x ↦ (x i : ℝ) * w i
  have hX : ∀ i, Measurable (X i) := by
    intro i
    exact measurable_of_countable _
  have hIndep : iIndepFun X P := by
    dsimp [X, P, μ]
    exact iIndepFun_pi
      (μ := fun i : ι ↦ poissonMeasure (r i))
      (X := fun i (n : ℕ) ↦ (n : ℝ) * w i)
      (fun _i ↦ (measurable_of_countable _).aemeasurable)
  have hLaw : ∀ i,
      HasLaw (X i) (fixedJumpPoissonMeasure (r i) (w i)) P := by
    intro i
    have heval : HasLaw (fun x : ι → ℕ ↦ x i) (poissonMeasure (r i)) P := by
      exact (measurePreserving_eval μ i).hasLaw
    have hjump : HasLaw (fun n : ℕ ↦ (n : ℝ) * w i)
        (fixedJumpPoissonMeasure (r i) (w i)) (poissonMeasure (r i)) := by
      refine ⟨(measurable_of_countable _).aemeasurable, ?_⟩
      rfl
    simpa only [X, Function.comp_apply] using! hjump.comp heval
  have hcf := charFun_independent_fixedJumpPoisson_sum_exp
    P X hX hIndep r w hLaw Finset.univ t
  simpa only [weightedIndependentPoissonLaw,
    independentPoissonProbabilityMeasure, weightedCountSum,
    ProbabilityMeasure.toMeasure_map, ProbabilityMeasure.toMeasure_pi,
    Finset.mem_univ, P, μ, X] using! hcf

end

end Erdos1002
