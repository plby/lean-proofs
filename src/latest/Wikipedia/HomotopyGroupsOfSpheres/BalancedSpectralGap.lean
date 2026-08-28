import Wikipedia.HomotopyGroupsOfSpheres.BalancedRealInvolutions
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Fintype.EquivFin

/-!
# A balanced signed spectrum has a large separated block

For a trace-zero spectrum with entries in the odd-speed ranges, any entry
outside the minimal signs forces a spectral gap of at least four against
at least half of the entries. This is the counting input for constrained
negative variations; no Hessian or path-deformation theorem is assumed.
-/

noncomputable section

namespace Wikipedia.HomotopyGroupsOfSpheres.BalancedRealInvolutions

def negativeBlock (n : ℕ) (μ : Index n → ℝ) : Finset (Index n) := by
  classical
  exact Finset.univ.filter (fun a ↦ μ a ≤ -1)

theorem mem_negativeBlock (n : ℕ) (μ : Index n → ℝ) (a : Index n) :
    a ∈ negativeBlock n μ ↔ μ a ≤ -1 := by
  classical
  simp [negativeBlock]

private theorem positive_block_bound (n : ℕ) (μ : Index n → ℝ)
    (hμ : ∀ a, μ a = 1 ∨ μ a = -1 ∨ 3 ≤ μ a ∨ μ a ≤ -3)
    (a : Index n) (ha : a ∈ (negativeBlock n μ)ᶜ) : 1 ≤ μ a := by
  have hn : ¬μ a ≤ -1 := by
    simpa only [Finset.mem_compl, mem_negativeBlock] using ha
  rcases hμ a with h | h | h | h <;> linarith

private theorem fast_negative_of_small_block (n : ℕ) (μ : Index n → ℝ)
    (hμ : ∀ a, μ a = 1 ∨ μ a = -1 ∨ 3 ≤ μ a ∨ μ a ≤ -3)
    (hsum : ∑ a, μ a = 0) (hsmall : (negativeBlock n μ).card < n) :
    ∃ a, μ a ≤ -3 := by
  classical
  by_contra hnone
  push Not at hnone
  have hneg (a : Index n) (ha : a ∈ negativeBlock n μ) : μ a = -1 := by
    have hle := (mem_negativeBlock n μ a).mp ha
    rcases hμ a with h | h | h | h <;> linarith [hnone a]
  have hnegSum : (∑ a ∈ negativeBlock n μ, μ a) = -((negativeBlock n μ).card : ℝ) := by
    calc
      (∑ a ∈ negativeBlock n μ, μ a) = ∑ a ∈ negativeBlock n μ, (-1 : ℝ) :=
        Finset.sum_congr rfl hneg
      _ = _ := by simp
  have hposSum : (((negativeBlock n μ)ᶜ).card : ℝ) ≤
      ∑ a ∈ (negativeBlock n μ)ᶜ, μ a := by
    calc
      (((negativeBlock n μ)ᶜ).card : ℝ) = ∑ a ∈ (negativeBlock n μ)ᶜ, (1 : ℝ) := by simp
      _ ≤ _ := Finset.sum_le_sum (positive_block_bound n μ hμ)
  have htotal := Finset.sum_compl_add_sum (negativeBlock n μ) μ
  rw [hsum, hnegSum] at htotal
  have hcard := Finset.card_compl_add_card (negativeBlock n μ)
  simp only [Fintype.card_sum, Fintype.card_fin] at hcard
  have hc : (negativeBlock n μ).card < ((negativeBlock n μ)ᶜ).card := by omega
  have hcR : ((negativeBlock n μ).card : ℝ) < (((negativeBlock n μ)ᶜ).card : ℝ) := by
    exact_mod_cast hc
  linarith

private theorem separated_block_of_positive_fast (n : ℕ) (μ : Index n → ℝ)
    (hμ : ∀ a, μ a = 1 ∨ μ a = -1 ∨ 3 ≤ μ a ∨ μ a ≤ -3)
    (hsum : ∑ a, μ a = 0) (a : Index n) (ha : 3 ≤ μ a) :
    ∃ (b : Index n) (S : Finset (Index n)), n ≤ S.card ∧ ∀ j ∈ S, 4 ≤ |μ b - μ j| := by
  by_cases hn : n ≤ (negativeBlock n μ).card
  · refine ⟨a, negativeBlock n μ, hn, ?_⟩
    intro j hj
    have hj' := (mem_negativeBlock n μ j).mp hj
    linarith [le_abs_self (μ a - μ j)]
  · obtain ⟨b, hb⟩ := fast_negative_of_small_block n μ hμ hsum (by omega)
    have hcard := Finset.card_compl_add_card (negativeBlock n μ)
    simp only [Fintype.card_sum, Fintype.card_fin] at hcard
    refine ⟨b, (negativeBlock n μ)ᶜ, by omega, ?_⟩
    intro j hj
    have hj' := positive_block_bound n μ hμ j hj
    linarith [neg_le_abs (μ b - μ j)]

theorem exists_separated_block (n : ℕ) (μ : Index n → ℝ)
    (hμ : ∀ a, μ a = 1 ∨ μ a = -1 ∨ 3 ≤ μ a ∨ μ a ≤ -3)
    (hsum : ∑ a, μ a = 0) (hfast : ∃ a, 3 ≤ μ a ∨ μ a ≤ -3) :
    ∃ (b : Index n) (S : Finset (Index n)), n ≤ S.card ∧ ∀ j ∈ S, 4 ≤ |μ b - μ j| := by
  obtain ⟨a, ha | ha⟩ := hfast
  · exact separated_block_of_positive_fast n μ hμ hsum a ha
  · have hneg : ∀ a, -μ a = 1 ∨ -μ a = -1 ∨ 3 ≤ -μ a ∨ -μ a ≤ -3 := by
      intro j
      rcases hμ j with h | h | h | h
      · exact Or.inr (Or.inl (by linarith))
      · exact Or.inl (by linarith)
      · exact Or.inr (Or.inr (Or.inr (by linarith)))
      · exact Or.inr (Or.inr (Or.inl (by linarith)))
    have hsumNeg : ∑ j, -μ j = 0 := by rw [Finset.sum_neg_distrib, hsum, neg_zero]
    obtain ⟨b, S, hc, hS⟩ := separated_block_of_positive_fast n (fun j ↦ -μ j)
      hneg hsumNeg a (by linarith)
    refine ⟨b, S, hc, ?_⟩
    intro j hj
    simpa only [neg_sub_neg, abs_sub_comm] using hS j hj

theorem exists_separated_embedding (n : ℕ) (μ : Index n → ℝ)
    (hμ : ∀ a, μ a = 1 ∨ μ a = -1 ∨ 3 ≤ μ a ∨ μ a ≤ -3)
    (hsum : ∑ a, μ a = 0) (hfast : ∃ a, 3 ≤ μ a ∨ μ a ≤ -3) :
    ∃ (b : Index n) (e : Fin n ↪ Index n), ∀ j, 4 ≤ |μ b - μ (e j)| := by
  obtain ⟨b, S, hc, hS⟩ := exists_separated_block n μ hμ hsum hfast
  let e : Fin n ↪ Index n :=
    ((Fin.castLEEmb hc).trans S.equivFin.symm.toEmbedding).trans
      ⟨Subtype.val, Subtype.val_injective⟩
  refine ⟨b, e, ?_⟩
  intro j
  exact hS (e j) (S.equivFin.symm (Fin.castLE hc j)).property

theorem exists_pi_separated_embedding (n : ℕ) (μ : Index n → ℝ)
    (hμ : ∀ a, μ a = 1 ∨ μ a = -1 ∨ 3 ≤ μ a ∨ μ a ≤ -3)
    (hsum : ∑ a, μ a = 0) (hfast : ∃ a, 3 ≤ μ a ∨ μ a ≤ -3) :
    ∃ (b : Index n) (e : Fin n ↪ Index n),
      ∀ j, b ≠ e j ∧ 4 * Real.pi ≤ |Real.pi * μ b - Real.pi * μ (e j)| := by
  obtain ⟨b, e, he⟩ := exists_separated_embedding n μ hμ hsum hfast
  refine ⟨b, e, ?_⟩
  intro j
  constructor
  · intro hb
    have h := he j
    rw [hb, sub_self, abs_zero] at h
    norm_num at h
  · rw [← mul_sub, abs_mul, abs_of_pos Real.pi_pos]
    nlinarith [he j, Real.pi_pos]

theorem integer_odd_speed_range (m : ℤ) :
    2 * (m : ℝ) + 1 = 1 ∨ 2 * (m : ℝ) + 1 = -1 ∨
      3 ≤ 2 * (m : ℝ) + 1 ∨ 2 * (m : ℝ) + 1 ≤ -3 := by
  have hm : m = 0 ∨ m = -1 ∨ 1 ≤ m ∨ m ≤ -2 := by omega
  rcases hm with h | h | h | h
  · exact Or.inl (by norm_num [h])
  · exact Or.inr (Or.inl (by norm_num [h]))
  · exact Or.inr (Or.inr (Or.inl (by exact_mod_cast (show (3 : ℤ) ≤ 2 * m + 1 by omega))))
  · exact Or.inr (Or.inr (Or.inr (by exact_mod_cast (show 2 * m + 1 ≤ (-3 : ℤ) by omega))))

theorem exists_odd_speed_separated_embedding (n : ℕ) (m : Index n → ℤ)
    (hsum : ∑ a, (2 * (m a : ℝ) + 1) = 0)
    (hfast : ∃ a, m a ≠ 0 ∧ m a ≠ -1) :
    ∃ (b : Index n) (e : Fin n ↪ Index n), ∀ j,
      b ≠ e j ∧ 4 * Real.pi ≤
        |Real.pi * (2 * (m b : ℝ) + 1) - Real.pi * (2 * (m (e j) : ℝ) + 1)| := by
  apply exists_pi_separated_embedding n (fun a ↦ 2 * (m a : ℝ) + 1)
    (fun a ↦ integer_odd_speed_range (m a)) hsum
  obtain ⟨a, ha₀, ha₁⟩ := hfast
  refine ⟨a, ?_⟩
  have ha : 1 ≤ m a ∨ m a ≤ -2 := by omega
  rcases ha with h | h
  · exact Or.inl (by exact_mod_cast (show (3 : ℤ) ≤ 2 * m a + 1 by omega))
  · exact Or.inr (by exact_mod_cast (show 2 * m a + 1 ≤ (-3 : ℤ) by omega))

end Wikipedia.HomotopyGroupsOfSpheres.BalancedRealInvolutions
