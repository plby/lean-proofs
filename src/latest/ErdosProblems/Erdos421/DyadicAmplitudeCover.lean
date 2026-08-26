import ErdosProblems.Erdos421.WeightedUnions

/-! # Dyadic amplitude classes and products of two sampled functions -/

namespace Erdos421

theorem exists_dyadic_amplitude {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) {J : ℕ}
    (hlo : (1 / 2 : ℝ) ^ J < x) :
    ∃ j < J, (1 / 2 : ℝ) ^ (j + 1) < x ∧ x ≤ 2 * (1 / 2 : ℝ) ^ (j + 1) := by
  obtain ⟨j, hjlo, hjhi⟩ := exists_nat_pow_near_of_lt_one hx hx1
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
  have hjJ : j < J := by
    by_contra h
    have hp := pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) ≤ 1) (le_of_not_gt h)
    exact hlo.not_ge (hjhi.trans hp)
  refine ⟨j, hjJ, hjlo, hjhi.trans_eq ?_⟩
  rw [pow_succ]
  ring

theorem dyadic_two_function_square_sum (S : Finset ℕ) (f g : ℕ → ℝ)
    (hf : ∀ i ∈ S, 0 ≤ f i ∧ f i ≤ 1) (hg : ∀ i ∈ S, 0 ≤ g i ∧ g i ≤ 1)
    (J : ℕ) {B : ℝ}
    (hlarge : ∀ T : Finset ℕ, T ⊆ S → ∀ V W : ℝ, 0 < V → 0 < W →
      (∀ i ∈ T, V ≤ f i) → (∀ i ∈ T, W ≤ g i) → (T.card : ℝ) * V ^ 2 * W ^ 2 ≤ B) :
    (∑ i ∈ S, (f i) ^ 2 * (g i) ^ 2) ≤
      16 * (J : ℝ) ^ 2 * B + S.card * ((1 / 2 : ℝ) ^ J) ^ 2 := by
  classical
  let Good := S.filter (fun i ↦ (1 / 2 : ℝ) ^ J < f i ∧ (1 / 2 : ℝ) ^ J < g i)
  let Bad := S.filter (fun i ↦ ¬((1 / 2 : ℝ) ^ J < f i ∧ (1 / 2 : ℝ) ^ J < g i))
  let E : ℕ × ℕ → Finset ℕ := fun a ↦ S.filter (fun i ↦
    ((1 / 2 : ℝ) ^ (a.1 + 1) < f i ∧ f i ≤ 2 * (1 / 2 : ℝ) ^ (a.1 + 1)) ∧
    ((1 / 2 : ℝ) ^ (a.2 + 1) < g i ∧ g i ≤ 2 * (1 / 2 : ℝ) ^ (a.2 + 1)))
  let P := (Finset.range J) ×ˢ (Finset.range J)
  have hsub : Good ⊆ P.biUnion E := by
    intro i hi
    obtain ⟨hiS, hiF, hiG⟩ := Finset.mem_filter.mp hi
    obtain ⟨j, hj, hjlo, hjhi⟩ := exists_dyadic_amplitude
      ((pow_pos (by norm_num : (0 : ℝ) < 1 / 2) J).trans hiF) (hf i hiS).2 hiF
    obtain ⟨l, hl, hllo, hlhi⟩ := exists_dyadic_amplitude
      ((pow_pos (by norm_num : (0 : ℝ) < 1 / 2) J).trans hiG) (hg i hiS).2 hiG
    exact Finset.mem_biUnion.mpr ⟨(j, l), Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr hj, Finset.mem_range.mpr hl⟩,
      Finset.mem_filter.mpr ⟨hiS, ⟨hjlo, hjhi⟩, ⟨hllo, hlhi⟩⟩⟩
  have hclass : ∀ a ∈ P, (∑ i ∈ E a, (f i) ^ 2 * (g i) ^ 2) ≤ 16 * B := by
    intro a _
    let V : ℝ := (1 / 2 : ℝ) ^ (a.1 + 1)
    let W : ℝ := (1 / 2 : ℝ) ^ (a.2 + 1)
    have hV : 0 < V := by dsimp only [V]; positivity
    have hW : 0 < W := by dsimp only [W]; positivity
    have hES : E a ⊆ S := Finset.filter_subset _ _
    have hb := hlarge (E a) hES V W hV hW
      (fun i hi ↦ (Finset.mem_filter.mp hi).2.1.1.le)
      (fun i hi ↦ (Finset.mem_filter.mp hi).2.2.1.le)
    have hpoint : ∀ i ∈ E a, (f i) ^ 2 * (g i) ^ 2 ≤ 16 * V ^ 2 * W ^ 2 := by
      intro i hi
      obtain ⟨hiS, hiF, hiG⟩ := Finset.mem_filter.mp hi
      have hfp := pow_le_pow_left₀ (hf i hiS).1 hiF.2 2
      have hgp := pow_le_pow_left₀ (hg i hiS).1 hiG.2 2
      have hm := mul_le_mul hfp hgp (sq_nonneg _) (sq_nonneg _)
      exact hm.trans_eq (by dsimp only [V, W]; ring)
    calc
      _ ≤ ∑ _i ∈ E a, 16 * V ^ 2 * W ^ 2 := Finset.sum_le_sum hpoint
      _ = 16 * ((E a).card * V ^ 2 * W ^ 2) := by
        rw [Finset.sum_const, nsmul_eq_mul]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hb (by norm_num)
  have hgood : (∑ i ∈ Good, (f i) ^ 2 * (g i) ^ 2) ≤ 16 * (J : ℝ) ^ 2 * B := by
    calc
      _ ≤ ∑ i ∈ P.biUnion E, (f i) ^ 2 * (g i) ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun i _ _ ↦ mul_nonneg (sq_nonneg _) (sq_nonneg _))
      _ ≤ ∑ a ∈ P, ∑ i ∈ E a, (f i) ^ 2 * (g i) ^ 2 :=
        sum_biUnion_weight_le P E _ (fun i ↦ mul_nonneg (sq_nonneg _) (sq_nonneg _))
      _ ≤ ∑ _a ∈ P, 16 * B := Finset.sum_le_sum hclass
      _ = _ := by
        simp only [P, Finset.sum_const, Finset.card_product, Finset.card_range, nsmul_eq_mul,
          Nat.cast_mul]
        ring
  have hbad : (∑ i ∈ Bad, (f i) ^ 2 * (g i) ^ 2) ≤
      S.card * ((1 / 2 : ℝ) ^ J) ^ 2 := by
    have hpoint : ∀ i ∈ Bad, (f i) ^ 2 * (g i) ^ 2 ≤ ((1 / 2 : ℝ) ^ J) ^ 2 := by
      intro i hi
      obtain ⟨hiS, hnot⟩ := Finset.mem_filter.mp hi
      rcases not_and_or.mp hnot with hF | hG
      · have hb := mul_le_mul (pow_le_pow_left₀ (hf i hiS).1 (le_of_not_gt hF) 2)
          (pow_le_pow_left₀ (hg i hiS).1 (hg i hiS).2 2) (sq_nonneg _) (sq_nonneg _)
        simpa only [one_pow, mul_one] using hb
      · have hb := mul_le_mul (pow_le_pow_left₀ (hf i hiS).1 (hf i hiS).2 2)
          (pow_le_pow_left₀ (hg i hiS).1 (le_of_not_gt hG) 2) (sq_nonneg _) (by norm_num)
        simpa only [one_pow, one_mul] using hb
    calc
      _ ≤ ∑ _i ∈ Bad, ((1 / 2 : ℝ) ^ J) ^ 2 := Finset.sum_le_sum hpoint
      _ = Bad.card * ((1 / 2 : ℝ) ^ J) ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (by exact_mod_cast Finset.card_filter_le S (fun i ↦
          ¬((1 / 2 : ℝ) ^ J < f i ∧ (1 / 2 : ℝ) ^ J < g i))) (sq_nonneg _)
  have hsplit : (∑ i ∈ Good, (f i) ^ 2 * (g i) ^ 2) +
      (∑ i ∈ Bad, (f i) ^ 2 * (g i) ^ 2) = ∑ i ∈ S, (f i) ^ 2 * (g i) ^ 2 := by
    exact Finset.sum_filter_add_sum_filter_not _ _ _
  rw [← hsplit]
  exact add_le_add hgood hbad

end Erdos421
