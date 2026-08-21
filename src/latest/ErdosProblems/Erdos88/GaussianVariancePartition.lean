import ErdosProblems.Erdos88.GaussianUniformRankTwo

open MeasureTheory ProbabilityTheory Set Complex
open scoped ENNReal NNReal BigOperators

namespace Erdos88.GaussianQuadratic

lemma exists_four_balanced_weight_blocks
    {ι : Type*} [DecidableEq ι]
    (w : ι → ℝ) (S : Finset ι) {M : ℝ} (hM : 0 ≤ M)
    (hw0 : ∀ i ∈ S, 0 ≤ w i) (hwM : ∀ i ∈ S, w i ≤ M) :
    ∃ B : Fin 4 → Finset ι,
      (∀ i j, i ≠ j → Disjoint (B i) (B j)) ∧
      (Finset.univ.biUnion B = S) ∧
      (∀ i j, ∑ x ∈ B i, w x ≤ (∑ x ∈ B j, w x) + M) := by
  induction S using Finset.induction_on with
  | empty =>
      refine ⟨fun _ ↦ ∅, ?_, ?_, ?_⟩
      · intro i j hij
        change Disjoint (∅ : Finset ι) ∅
        simp
      · ext x
        simp
      · simp [hM]
  | @insert x S hx ih =>
      have hw0S : ∀ i ∈ S, 0 ≤ w i := fun i hi ↦ hw0 i (by simp [hi])
      have hwMS : ∀ i ∈ S, w i ≤ M := fun i hi ↦ hwM i (by simp [hi])
      obtain ⟨B, hdisj, hcover, hbal⟩ := ih hw0S hwMS
      let L : Fin 4 → ℝ := fun i ↦ ∑ y ∈ B i, w y
      obtain ⟨k, hk, hkmin⟩ := Finset.exists_min_image
        (Finset.univ : Finset (Fin 4)) L Finset.univ_nonempty
      have hkmin' : ∀ i, L k ≤ L i := fun i ↦ hkmin i (Finset.mem_univ i)
      have hxB : ∀ i, x ∉ B i := by
        intro i hxi
        apply hx
        rw [← hcover]
        exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hxi⟩
      let B' : Fin 4 → Finset ι := fun i ↦ if i = k then insert x (B i) else B i
      have hload (i : Fin 4) :
          (∑ y ∈ B' i, w y) = if i = k then w x + L i else L i := by
        by_cases hik : i = k
        · subst i
          simp [B', L, hxB]
        · simp [B', L, hik]
      refine ⟨B', ?_, ?_, ?_⟩
      · intro i j hij
        by_cases hik : i = k
        · subst i
          have hjk : j ≠ k := by exact fun hj ↦ hij hj.symm
          simp only [B', ↓reduceIte, if_neg hjk]
          rw [Finset.disjoint_insert_left]
          exact ⟨hxB j, hdisj k j (Ne.symm hjk)⟩
        · by_cases hjk : j = k
          · subst j
            simp only [B', if_neg hik, ↓reduceIte]
            rw [Finset.disjoint_insert_right]
            exact ⟨hxB i, hdisj i k hik⟩
          · simp only [B', if_neg hik, if_neg hjk]
            exact hdisj i j hij
      · ext y
        constructor
        · intro hy
          obtain ⟨i, hi, hyi⟩ := Finset.mem_biUnion.mp hy
          by_cases hik : i = k
          · subst i
            simp only [B', ↓reduceIte, Finset.mem_insert] at hyi
            rcases hyi with rfl | hyB
            · simp
            · simp [show y ∈ S by
                rw [← hcover]
                exact Finset.mem_biUnion.mpr ⟨k, Finset.mem_univ k, hyB⟩]
          · have hyB : y ∈ B i := by simpa only [B', if_neg hik] using hyi
            simp [show y ∈ S by
              rw [← hcover]
              exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hyB⟩]
        · intro hy
          simp only [Finset.mem_insert] at hy
          rcases hy with rfl | hyS
          · exact Finset.mem_biUnion.mpr ⟨k, Finset.mem_univ k, by simp [B']⟩
          · rw [← hcover] at hyS
            obtain ⟨i, hi, hyB⟩ := Finset.mem_biUnion.mp hyS
            refine Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, ?_⟩
            by_cases hik : i = k
            · subst i
              simp [B', hyB]
            · simpa only [B', if_neg hik] using hyB
      · intro i j
        rw [hload, hload]
        by_cases hik : i = k
        · subst i
          by_cases hjk : j = k
          · subst j
            simp only [↓reduceIte]
            exact le_add_of_nonneg_right hM
          · simp only [↓reduceIte, if_neg hjk]
            have hkLj := hkmin' j
            have hwxM := hwM x (by simp)
            linarith
        · by_cases hjk : j = k
          · subst j
            simp only [if_neg hik, ↓reduceIte]
            have hiLk := hbal i k
            have hwx0 := hw0 x (by simp)
            linarith
          · simp only [if_neg hik, if_neg hjk]
            exact hbal i j

lemma sum_fin_four (f : Fin 4 → ℝ) :
    (∑ i, f i) = f 0 + f 1 + f 2 + f 3 := by
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ,
    Fin.sum_univ_succ]
  simp
  ring

lemma four_balanced_block_weight_le
    {ι : Type*} [DecidableEq ι]
    (w : ι → ℝ) (S : Finset ι) {M : ℝ}
    (B : Fin 4 → Finset ι)
    (hdisj : ∀ i j, i ≠ j → Disjoint (B i) (B j))
    (hcover : Finset.univ.biUnion B = S)
    (hbal : ∀ i j, ∑ x ∈ B i, w x ≤ (∑ x ∈ B j, w x) + M)
    (h : Fin 4) :
    4 * (∑ x ∈ B h, w x) ≤ (∑ x ∈ S, w x) + 3 * M := by
  have hsum : (∑ k : Fin 4, ∑ x ∈ B k, w x) = ∑ x ∈ S, w x := by
    rw [← hcover, Finset.sum_biUnion]
    intro i hi j hj hij
    exact hdisj i j hij
  rw [sum_fin_four] at hsum
  fin_cases h
  · change 4 * (∑ x ∈ B 0, w x) ≤ (∑ x ∈ S, w x) + 3 * M
    have h1 := hbal 0 1
    have h2 := hbal 0 2
    have h3 := hbal 0 3
    nlinarith
  · change 4 * (∑ x ∈ B 1, w x) ≤ (∑ x ∈ S, w x) + 3 * M
    have h0 := hbal 1 0
    have h2 := hbal 1 2
    have h3 := hbal 1 3
    nlinarith
  · change 4 * (∑ x ∈ B 2, w x) ≤ (∑ x ∈ S, w x) + 3 * M
    have h0 := hbal 2 0
    have h1 := hbal 2 1
    have h3 := hbal 2 3
    nlinarith
  · change 4 * (∑ x ∈ B 3, w x) ≤ (∑ x ∈ S, w x) + 3 * M
    have h0 := hbal 3 0
    have h1 := hbal 3 1
    have h2 := hbal 3 2
    nlinarith

end Erdos88.GaussianQuadratic
