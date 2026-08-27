import Arxiv.Arxiv2411_18291.BernoulliSubset

/-! # Exact probabilities of prescribed present and absent coordinates -/

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators ENNReal

noncomputable section

namespace Arxiv2411_18291.BernoulliSubset

open Classical in
theorem probabilityReal_pattern {ι : Type*} (p : unitInterval) (s : Finset ι) (v : ι → Prop) :
    (probability ι p).real {ω | ∀ i ∈ s, ω i = v i} =
      ∏ i ∈ s, if v i then (p : ℝ) else 1 - p := by
  classical
  have hInd : iIndepFun (fun i (ω : Sample ι) => ω i) (probability ι p) :=
    iIndepFun_infinitePi (X := fun _ => id) (fun _ => measurable_id)
  have heq : {ω : Sample ι | ∀ i ∈ s, ω i = v i} =
      ⋂ i ∈ s, (fun ω : Sample ι => ω i) ⁻¹' {v i} := by
    ext ω
    simp
  rw [measureReal_def, heq,
    hInd.measure_inter_preimage_eq_mul s (fun _ _ => MeasurableSet.singleton _),
    ENNReal.toReal_prod]
  apply prod_congr rfl
  intro i _
  rw [← Measure.map_apply (measurable_pi_apply i) (.singleton (v i)), coordinate_law]
  by_cases hi : v i <;> simp [coin, hi]

theorem probabilityReal_present_absent {ι : Type*} (p : unitInterval)
    (s t : Finset ι) (hdis : Disjoint s t) :
    (probability ι p).real {ω | (∀ i ∈ s, ω i) ∧ ∀ i ∈ t, ¬ω i} =
      (p : ℝ) ^ s.card * (1 - p) ^ t.card := by
  classical
  have hnot (i : ι) (hi : i ∈ t) : i ∉ s := fun hs => disjoint_left.mp hdis hs hi
  have heq : {ω : Sample ι | (∀ i ∈ s, ω i) ∧ ∀ i ∈ t, ¬ω i} =
      {ω | ∀ i ∈ s ∪ t, ω i = (i ∈ s)} := by
    ext ω
    constructor
    · intro h i hi
      rcases mem_union.mp hi with hs | ht
      · simp [hs, h.1 i hs]
      · simp [hnot i ht, h.2 i ht]
    · intro h
      constructor
      · intro i hi
        exact (h i (mem_union_left _ hi)).mpr hi
      · intro i hi hω
        exact hnot i hi ((h i (mem_union_right _ hi)).mp hω)
  rw [heq, probabilityReal_pattern, prod_union hdis]
  congr 1
  · calc
      _ = ∏ _i ∈ s, (p : ℝ) := by
        apply prod_congr rfl
        intro i hi
        simp [hi]
      _ = _ := by simp
  · calc
      _ = ∏ _i ∈ t, (1 - p : ℝ) := by
        apply prod_congr rfl
        intro i hi
        simp [hnot i hi]
      _ = _ := by simp

end Arxiv2411_18291.BernoulliSubset
