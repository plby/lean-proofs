import Arxiv.Arxiv2411_18291.FiniteHistoryAgreement
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Finite laws of outputs read from actual trajectories

An output is accepted only when its observed coordinates agree with the
sampled finite history. Failure is represented by none. This preserves
the exact failure probability and permits later stages to depend on the
earlier output through probability-mass-function composition.
-/

open Finset MeasureTheory Preorder

noncomputable section

namespace Arxiv2411_18291.FiniteHistoryProcess

variable {S I O : Type*} [Fintype S] [Fintype I] [Finite O]
variable [MeasurableSpace S] [MeasurableSingletonClass S]

def observedOutputEvent (observe : O → I → S) : Set (ℕ → S) :=
  {ω | ∃ o : O, ∀ i : I, ω ((Fintype.equivFin I i : ℕ) + 1) = observe o i}

def chooseObservedOutput (observe : O → I → S) (h : History S (Fintype.card I)) :
    Option O := by
  classical
  exact if hp : ∃ o : O, ∀ i : I,
      h ⟨(Fintype.equivFin I i : ℕ) + 1,
        mem_Iic.mpr (Nat.succ_le_of_lt (Fintype.equivFin I i).isLt)⟩ = observe o i then
    some hp.choose
  else none

omit [Fintype S] [Finite O] [MeasurableSpace S] [MeasurableSingletonClass S] in
theorem chooseObservedOutput_eq_none_iff (observe : O → I → S)
    (h : History S (Fintype.card I)) :
    chooseObservedOutput observe h = none ↔ ¬ ∃ o : O, ∀ i : I,
      h ⟨(Fintype.equivFin I i : ℕ) + 1,
        mem_Iic.mpr (Nat.succ_le_of_lt (Fintype.equivFin I i).isLt)⟩ = observe o i := by
  classical
  unfold chooseObservedOutput
  split_ifs with hp <;> simp [hp]

omit [Fintype S] [Finite O] [MeasurableSpace S] [MeasurableSingletonClass S] in
theorem chooseObservedOutput_eq_some_imp (observe : O → I → S)
    (h : History S (Fintype.card I)) {o : O} (ho : chooseObservedOutput observe h = some o) :
    ∀ i : I, h ⟨(Fintype.equivFin I i : ℕ) + 1,
      mem_Iic.mpr (Nat.succ_le_of_lt (Fintype.equivFin I i).isLt)⟩ = observe o i := by
  classical
  unfold chooseObservedOutput at ho
  split_ifs at ho with hp
  · cases Option.some.inj ho
    exact hp.choose_spec

omit [Fintype S] [Finite O] [MeasurableSpace S] [MeasurableSingletonClass S] in
theorem chooseObservedOutput_prefix_eq_none (observe : O → I → S) (ω : ℕ → S) :
    chooseObservedOutput observe (frestrictLe (Fintype.card I) ω) = none ↔
      ω ∉ observedOutputEvent observe := by
  rw [chooseObservedOutput_eq_none_iff]
  rfl

omit [Fintype S] in
theorem measurableSet_observedOutputEvent (observe : O → I → S) :
    MeasurableSet (observedOutputEvent observe) := by
  unfold observedOutputEvent
  simp only [Set.ofPred_exists, Set.ofPred_forall]
  apply MeasurableSet.iUnion
  intro o
  apply MeasurableSet.iInter
  intro i
  exact (measurableSet_singleton (observe o i)).preimage
    (measurable_pi_apply ((Fintype.equivFin I i : ℕ) + 1))

def observedOutputLaw (μ : Measure (ℕ → S)) [IsProbabilityMeasure μ]
    (observe : O → I → S) : PMF (Option O) := by
  let ν := μ.map (frestrictLe (Fintype.card I))
  letI : IsProbabilityMeasure ν :=
    μ.isProbabilityMeasure_map (measurable_frestrictLe (Fintype.card I)).aemeasurable
  exact ν.toPMF.map (chooseObservedOutput observe)

theorem observedOutputLaw_failure (μ : Measure (ℕ → S)) [IsProbabilityMeasure μ]
    (observe : O → I → S) :
    observedOutputLaw μ observe none = μ (observedOutputEvent observe)ᶜ := by
  classical
  let : MeasurableSpace (Option O) := ⊤
  rw [← (observedOutputLaw μ observe).toMeasure_apply_singleton none (measurableSet_singleton _)]
  unfold observedOutputLaw
  rw [PMF.toMeasure_map_apply _ _ _ (measurable_of_finite _) (measurableSet_singleton _),
    Measure.toPMF_toMeasure,
    Measure.map_apply (measurable_frestrictLe (Fintype.card I))
      ((measurableSet_singleton none).preimage (measurable_of_finite _))]
  congr 1
  ext ω
  exact chooseObservedOutput_prefix_eq_none observe ω

theorem observedOutputLaw_failure_real (μ : Measure (ℕ → S)) [IsProbabilityMeasure μ]
    (observe : O → I → S) :
    (observedOutputLaw μ observe none).toReal = 1 - μ.real (observedOutputEvent observe) := by
  rw [observedOutputLaw_failure]
  change μ.real (observedOutputEvent observe)ᶜ = _
  rw [measureReal_compl (measurableSet_observedOutputEvent observe), probReal_univ]

theorem observedOutputLaw_failure_lt (μ : Measure (ℕ → S)) [IsProbabilityMeasure μ]
    (observe : O → I → S) {ε : ℝ}
    (hprob : 1 - ε < μ.real (observedOutputEvent observe)) :
    (observedOutputLaw μ observe none).toReal < ε := by
  rw [observedOutputLaw_failure_real]
  linarith only [hprob]

end Arxiv2411_18291.FiniteHistoryProcess
