import ErdosProblems.Erdos747.AllDensityRegularity

open Filter Real
open scoped BigOperators Topology

namespace Erdos747

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ## Materialized finite unions of all-density tails -/

noncomputable def allDensityDegreeUpperFailureSet
    (n M : ℕ) (B : ℝ) : Finset (Finset (Edge n)) :=
  (Finset.univ : Finset (Vertex n)).biUnion fun v ↦
    (sample n M).filter fun H ↦
      B * ((M : ℝ) / n) ≤ vertexDegree H v

lemma mem_allDensityDegreeUpperFailureSet_iff
    (n M : ℕ) (B : ℝ) (H : Finset (Edge n)) :
    H ∈ allDensityDegreeUpperFailureSet n M B ↔
      H ∈ sample n M ∧ ∃ v : Vertex n,
        B * ((M : ℝ) / n) ≤ vertexDegree H v := by
  classical
  simp [allDensityDegreeUpperFailureSet]

noncomputable def allDensityDegreeLowerFailureSet
    (n M : ℕ) (a : ℝ) : Finset (Finset (Edge n)) :=
  (Finset.univ : Finset (Vertex n)).biUnion fun v ↦
    (sample n M).filter fun H ↦
      (vertexDegree H v : ℝ) ≤ a * ((M : ℝ) / n)

lemma mem_allDensityDegreeLowerFailureSet_iff
    (n M : ℕ) (a : ℝ) (H : Finset (Edge n)) :
    H ∈ allDensityDegreeLowerFailureSet n M a ↔
      H ∈ sample n M ∧ ∃ v : Vertex n,
        (vertexDegree H v : ℝ) ≤ a * ((M : ℝ) / n) := by
  classical
  simp [allDensityDegreeLowerFailureSet]

noncomputable def allDensityCodegreeSixFailureSet
    (n M : ℕ) : Finset (Finset (Edge n)) :=
  ((Finset.univ : Finset (Vertex n)).product
      (Finset.univ : Finset (Vertex n))).biUnion fun p ↦
    (sample n M).filter fun H ↦
      p.1 ≠ p.2 ∧ 6 ≤ vertexCodegree H p.1 p.2

lemma mem_allDensityCodegreeSixFailureSet_iff
    (n M : ℕ) (H : Finset (Edge n)) :
    H ∈ allDensityCodegreeSixFailureSet n M ↔
      H ∈ sample n M ∧ ∃ u v : Vertex n, u ≠ v ∧
        6 ≤ vertexCodegree H u v := by
  classical
  simp only [allDensityCodegreeSixFailureSet, Finset.mem_biUnion,
    Finset.mem_product, Finset.mem_univ, and_self,
    Finset.mem_filter, true_and]
  constructor
  · rintro ⟨⟨u, v⟩, -, hHs, huv, hcodeg⟩
    exact ⟨hHs, u, v, huv, hcodeg⟩
  · rintro ⟨hHs, u, v, huv, hcodeg⟩
    exact ⟨(u, v), by simp, hHs, huv, hcodeg⟩

/-- Cardinal union bound phrased for a materialized union of finite
events. -/
lemma finsetProbability_mem_biUnion_le_sum {α ι : Type*}
    (s : Finset α) (I : Finset ι) (F : ι → Finset α)
    (hsub : ∀ i ∈ I, F i ⊆ s) :
    finsetProbability s (fun x ↦ x ∈ I.biUnion F) ≤
      ∑ i ∈ I, finsetProbability s (fun x ↦ x ∈ F i) := by
  have hunionSub : I.biUnion F ⊆ s := by
    intro x hx
    rcases Finset.mem_biUnion.mp hx with ⟨i, hi, hxi⟩
    exact hsub i hi hxi
  have hfilter : s.filter (fun x ↦ x ∈ I.biUnion F) = I.biUnion F := by
    ext x
    simp only [Finset.mem_filter]
    exact and_iff_right_of_imp (fun hx ↦ hunionSub hx)
  have hfilterEach : ∀ i ∈ I,
      s.filter (fun x ↦ x ∈ F i) = F i := by
    intro i hi
    ext x
    simp only [Finset.mem_filter]
    exact and_iff_right_of_imp (fun hx ↦ hsub i hi hx)
  have hcard : (I.biUnion F).card ≤ ∑ i ∈ I, (F i).card :=
    Finset.card_biUnion_le
  have hcardR : ((I.biUnion F).card : ℝ) ≤
      ∑ i ∈ I, ((s.filter fun x ↦ x ∈ F i).card : ℝ) := by
    have hcast : ((I.biUnion F).card : ℝ) ≤
        ∑ i ∈ I, ((F i).card : ℝ) := by exact_mod_cast hcard
    apply hcast.trans_eq
    apply Finset.sum_congr rfl
    intro i hi
    rw [hfilterEach i hi]
  unfold finsetProbability
  rw [hfilter, ← Finset.sum_div]
  apply div_le_div_of_nonneg_right hcardR
  positivity

lemma allDensityDegreeUpperFailureSet_probability_le
    (n M : ℕ) (B : ℝ)
    (hn : 0 < n) (hM : M ≤ (allEdges n).card) (hB : 1 ≤ B) :
    finsetProbability (sample n M)
        (fun H ↦ H ∈ allDensityDegreeUpperFailureSet n M B) ≤
      (3 * n : ℝ) * (((allEdges n).card + 1 : ℝ) *
        Real.exp (((M : ℝ) / n) *
          (B - 1 - B * Real.log B))) := by
  let F : Vertex n → Finset (Finset (Edge n)) := fun v ↦
    (sample n M).filter fun H ↦
      B * ((M : ℝ) / n) ≤ vertexDegree H v
  have hbase := finsetProbability_mem_biUnion_le_sum
    (sample n M) (Finset.univ : Finset (Vertex n)) F
    (fun v _ ↦ Finset.filter_subset _ _)
  have hdec :
      (fun A B : Finset (Edge n) ↦ Classical.propDecidable (A = B)) =
        (Finset.decidableEq : DecidableEq (Finset (Edge n))) :=
    Subsingleton.elim _ _
  rw [hdec] at hbase
  have hdef : (Finset.univ : Finset (Vertex n)).biUnion F =
      allDensityDegreeUpperFailureSet n M B := by
    rfl
  have hbase' : finsetProbability (sample n M)
      (fun H ↦ H ∈ allDensityDegreeUpperFailureSet n M B) ≤
        ∑ v : Vertex n,
          finsetProbability (sample n M) (fun H ↦ H ∈ F v) := by
    simpa only [hdef.symm] using hbase
  calc
    finsetProbability (sample n M)
        (fun H ↦ H ∈ allDensityDegreeUpperFailureSet n M B) ≤
      ∑ v : Vertex n,
        finsetProbability (sample n M) (fun H ↦ H ∈ F v) := hbase'
    _ = ∑ v : Vertex n,
        finsetProbability (sample n M)
          (fun H ↦ B * ((M : ℝ) / n) ≤ vertexDegree H v) := by
      apply Finset.sum_congr rfl
      intro v _
      apply finsetProbability_congr_event
      intro H hHs
      simp [F, hHs]
    _ ≤ ∑ _v : Vertex n,
        (((allEdges n).card + 1 : ℝ) *
          Real.exp (((M : ℝ) / n) *
            (B - 1 - B * Real.log B))) :=
      Finset.sum_le_sum fun v _ ↦
        sampledVertexDegree_upper_factor_allDensity_le
          n M v B hn hM hB
    _ = _ := by simp

lemma allDensityDegreeLowerFailureSet_probability_le
    (n M : ℕ) (a : ℝ)
    (hn : 0 < n) (hM : M ≤ (allEdges n).card)
    (ha0 : 0 < a) (ha1 : a ≤ 1) :
    finsetProbability (sample n M)
        (fun H ↦ H ∈ allDensityDegreeLowerFailureSet n M a) ≤
      (3 * n : ℝ) * (((allEdges n).card + 1 : ℝ) *
        Real.exp (((M : ℝ) / n) *
          (a - 1 - a * Real.log a))) := by
  let F : Vertex n → Finset (Finset (Edge n)) := fun v ↦
    (sample n M).filter fun H ↦
      (vertexDegree H v : ℝ) ≤ a * ((M : ℝ) / n)
  have hbase := finsetProbability_mem_biUnion_le_sum
    (sample n M) (Finset.univ : Finset (Vertex n)) F
    (fun v _ ↦ Finset.filter_subset _ _)
  have hdec :
      (fun A B : Finset (Edge n) ↦ Classical.propDecidable (A = B)) =
        (Finset.decidableEq : DecidableEq (Finset (Edge n))) :=
    Subsingleton.elim _ _
  rw [hdec] at hbase
  have hdef : (Finset.univ : Finset (Vertex n)).biUnion F =
      allDensityDegreeLowerFailureSet n M a := by
    rfl
  have hbase' : finsetProbability (sample n M)
      (fun H ↦ H ∈ allDensityDegreeLowerFailureSet n M a) ≤
        ∑ v : Vertex n,
          finsetProbability (sample n M) (fun H ↦ H ∈ F v) := by
    simpa only [hdef.symm] using hbase
  calc
    finsetProbability (sample n M)
        (fun H ↦ H ∈ allDensityDegreeLowerFailureSet n M a) ≤
      ∑ v : Vertex n,
        finsetProbability (sample n M) (fun H ↦ H ∈ F v) := hbase'
    _ = ∑ v : Vertex n,
        finsetProbability (sample n M)
          (fun H ↦ (vertexDegree H v : ℝ) ≤
            a * ((M : ℝ) / n)) := by
      apply Finset.sum_congr rfl
      intro v _
      apply finsetProbability_congr_event
      intro H hHs
      simp [F, hHs]
    _ ≤ ∑ _v : Vertex n,
        (((allEdges n).card + 1 : ℝ) *
          Real.exp (((M : ℝ) / n) *
            (a - 1 - a * Real.log a))) :=
      Finset.sum_le_sum fun v _ ↦
        sampledVertexDegree_lower_factor_allDensity_le
          n M v a hn hM ha0 ha1
    _ = _ := by simp

lemma allDensityCodegreeSixFailureSet_probability_le
    (n M : ℕ) (hn : 0 < n) (hM : M ≤ (allEdges n).card) :
    finsetProbability (sample n M)
        (fun H ↦ H ∈ allDensityCodegreeSixFailureSet n M) ≤
      ((3 * n : ℝ)^2) * (((allEdges n).card + 1 : ℝ) *
        Real.exp ((M : ℝ) *
            (2 / ((n : ℝ) * (3 * n - 1))) * ((n : ℝ) - 1) -
          Real.log (n : ℝ) * 6)) := by
  let I := (Finset.univ : Finset (Vertex n)).product
    (Finset.univ : Finset (Vertex n))
  let F : Vertex n × Vertex n → Finset (Finset (Edge n)) := fun p ↦
    (sample n M).filter fun H ↦
      p.1 ≠ p.2 ∧ 6 ≤ vertexCodegree H p.1 p.2
  have hbase := finsetProbability_mem_biUnion_le_sum
    (sample n M) I F (fun p _ ↦ Finset.filter_subset _ _)
  have hdec :
      (fun A B : Finset (Edge n) ↦ Classical.propDecidable (A = B)) =
        (Finset.decidableEq : DecidableEq (Finset (Edge n))) :=
    Subsingleton.elim _ _
  rw [hdec] at hbase
  have hdef : I.biUnion F = allDensityCodegreeSixFailureSet n M := by
    rfl
  have hIcard : I.card = (3 * n)^2 := by
    simp [I, pow_two]
  have hbase' : finsetProbability (sample n M)
      (fun H ↦ H ∈ allDensityCodegreeSixFailureSet n M) ≤
        ∑ p ∈ I, finsetProbability (sample n M)
          (fun H ↦ H ∈ F p) := by
    simpa only [hdef.symm] using hbase
  calc
    finsetProbability (sample n M)
        (fun H ↦ H ∈ allDensityCodegreeSixFailureSet n M) ≤
      ∑ p ∈ I, finsetProbability (sample n M)
        (fun H ↦ H ∈ F p) := hbase'
    _ ≤ ∑ _p ∈ I, (((allEdges n).card + 1 : ℝ) *
        Real.exp ((M : ℝ) *
            (2 / ((n : ℝ) * (3 * n - 1))) * ((n : ℝ) - 1) -
          Real.log (n : ℝ) * 6)) := by
      apply Finset.sum_le_sum
      intro p hp
      by_cases huv : p.1 = p.2
      · have hzero : finsetProbability (sample n M)
            (fun H ↦ H ∈ F p) = 0 := by
          unfold finsetProbability
          have hempty : (sample n M).filter (fun H ↦ H ∈ F p) = ∅ := by
            ext H
            simp [F, huv]
          rw [hempty]
          simp
        rw [hzero]
        exact mul_nonneg (by positivity) (Real.exp_pos _).le
      · calc
          finsetProbability (sample n M) (fun H ↦ H ∈ F p) =
              finsetProbability (sample n M)
                (fun H ↦ (6 : ℝ) ≤ vertexCodegree H p.1 p.2) := by
            apply finsetProbability_congr_event
            intro H hHs
            simp [F, hHs, huv]
          _ ≤ _ := sampledVertexCodegree_six_allDensity_le
            n M huv hn hM
    _ = _ := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      rw [hIcard]
      norm_num only [Nat.cast_pow, Nat.cast_mul, Nat.cast_ofNat]

end

end Erdos747
