import Arxiv.Arxiv2411_18291.IndependentPermutationEvents

/-!
# Independent repetitions of a finite family of tests

Each test can use its own successful trial. Independence is required between
trials, but no independence is assumed between the tests in one trial.
-/

open Finset MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

noncomputable section

namespace Arxiv2411_18291.IndependentTrials

variable {Ω R : Type*} [MeasurableSpace Ω]

theorem exists_of_failure_lt_one (μ : Measure Ω) [IsProbabilityMeasure μ]
    {P : Ω → Prop} (h : μ.real {ω | ¬ P ω} < 1) : ∃ ω, P ω := by
  by_contra! hP
  have heq : {ω | ¬ P ω} = Set.univ := Set.eq_univ_of_forall hP
  rw [heq, probReal_univ] at h
  exact lt_irrefl 1 h

def probability (μ : Measure Ω) [IsProbabilityMeasure μ] (L : ℕ) : Measure (Fin L → Ω) :=
  Measure.infinitePi fun _ => μ

instance (μ : Measure Ω) [IsProbabilityMeasure μ] (L : ℕ) :
    IsProbabilityMeasure (probability μ L) := by
  unfold probability
  infer_instance

def allBad (L : ℕ) (B : Set Ω) : Set (Fin L → Ω) := {ω | ∀ j, ω j ∈ B}

omit [MeasurableSpace Ω] in
theorem allBad_eq_iInter (L : ℕ) (B : Set Ω) :
    allBad L B = ⋂ j ∈ (univ : Finset (Fin L)), (fun ω : Fin L → Ω => ω j) ⁻¹' B := by
  ext ω
  simp only [allBad, Set.mem_ofPred_eq, Set.mem_iInter, mem_univ, forall_const, Set.mem_preimage]

theorem allBad_measurable (L : ℕ) {B : Set Ω} (hB : MeasurableSet B) :
    MeasurableSet (allBad L B) := by
  rw [allBad_eq_iInter]
  exact MeasurableSet.biInter univ.countable_toSet (fun j _ => (measurable_pi_apply j) hB)

theorem probability_allBad (μ : Measure Ω) [IsProbabilityMeasure μ] (L : ℕ)
    {B : Set Ω} (hB : MeasurableSet B) : probability μ L (allBad L B) = (μ B) ^ L := by
  have hInd : iIndepFun (fun j (ω : Fin L → Ω) => ω j) (probability μ L) :=
    iIndepFun_infinitePi (X := fun _ => id) (fun _ => measurable_id)
  have hcoord (j : Fin L) :
      probability μ L ((fun ω : Fin L → Ω => ω j) ⁻¹' B) = μ B := by
    rw [← Measure.map_apply (measurable_pi_apply j) hB]
    exact congrArg (fun ν : Measure Ω => ν B) (Measure.infinitePi_map_eval (fun _ => μ) j)
  rw [allBad_eq_iInter, hInd.measure_inter_preimage_eq_mul univ (fun _ _ => hB)]
  simp only [hcoord, prod_const, card_univ, Fintype.card_fin]

theorem probabilityReal_allBad (μ : Measure Ω) [IsProbabilityMeasure μ] (L : ℕ)
    {B : Set Ω} (hB : MeasurableSet B) : (probability μ L).real (allBad L B) = (μ.real B) ^ L := by
  simp only [measureReal_def, probability_allBad μ L hB, ENNReal.toReal_pow]

theorem probability_some_allBad_le (μ : Measure Ω) [IsProbabilityMeasure μ] (L : ℕ)
    (s : Finset R) (B : R → Set Ω) {δ : ℝ}
    (hB : ∀ r ∈ s, MeasurableSet (B r)) (hprob : ∀ r ∈ s, μ.real (B r) ≤ δ) :
    (probability μ L).real (⋃ r ∈ s, allBad L (B r)) ≤ s.card * δ ^ L := by
  calc
    _ ≤ ∑ r ∈ s, (probability μ L).real (allBad L (B r)) :=
      measureReal_biUnion_finset_le s _
    _ ≤ ∑ _r ∈ s, δ ^ L := by
      apply sum_le_sum
      intro r hr
      rw [probabilityReal_allBad μ L (hB r hr)]
      exact pow_le_pow_left₀ measureReal_nonneg (hprob r hr) L
    _ = _ := by simp only [sum_const, nsmul_eq_mul]

theorem exists_trials_avoiding_each (μ : Measure Ω) [IsProbabilityMeasure μ] (L : ℕ)
    (s : Finset R) (B : R → Set Ω) {δ : ℝ}
    (hB : ∀ r ∈ s, MeasurableSet (B r)) (hprob : ∀ r ∈ s, μ.real (B r) ≤ δ)
    (hsmall : s.card * δ ^ L < 1) : ∃ ω : Fin L → Ω, ∀ r ∈ s, ∃ j, ω j ∉ B r := by
  classical
  by_contra h
  push Not at h
  have heq : (⋃ r ∈ s, allBad L (B r)) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro ω
    obtain ⟨r, hr, hω⟩ := h ω
    exact Set.mem_iUnion.mpr ⟨r, Set.mem_iUnion.mpr ⟨hr, hω⟩⟩
  have hbnd := probability_some_allBad_le μ L s B hB hprob
  rw [heq, probReal_univ] at hbnd
  linarith only [hbnd, hsmall]

end Arxiv2411_18291.IndependentTrials
