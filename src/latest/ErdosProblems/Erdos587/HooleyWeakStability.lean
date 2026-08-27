import ErdosProblems.Erdos587.HighFoldStability

/-! # Weak multiplicative stability with a constant deletion loss -/

namespace Erdos587.CFP

theorem delta_exists_weakly_stable_subset {α : Type*} (V : Finset α → ℕ)
    (A : Finset α) (r K n : ℕ)
    (hpos : ∀ B ⊆ A, 0 < V B) (hinit : V A < K ^ (n + 1)) :
    ∃ B ⊆ A, A.card ≤ B.card + n * r ∧
      ∀ D ⊆ B, B.card ≤ D.card + r → V B < K * V D := by
  classical
  induction n generalizing A with
  | zero =>
      refine ⟨A, Finset.Subset.refl A, by simp, ?_⟩
      intro D hDA _hcost
      calc
        V A < K := by simpa only [zero_add, pow_one] using hinit
        _ ≤ K * V D := by
          have hVD : 1 ≤ V D := hpos D hDA
          simpa only [mul_one] using Nat.mul_le_mul_left K hVD
  | succ n ih =>
      by_cases hstable : ∀ D ⊆ A, A.card ≤ D.card + r → V A < K * V D
      · exact ⟨A, Finset.Subset.refl A, Nat.le_add_right _ _, hstable⟩
      · push Not at hstable
        obtain ⟨D, hDA, hremove, hdrop⟩ := hstable
        have hnext : V D < K ^ (n + 1) := by
          apply Nat.lt_of_mul_lt_mul_left (a := K)
          calc
            K * V D ≤ V A := hdrop
            _ < K ^ (n + 1 + 1) := hinit
            _ = K * K ^ (n + 1) := pow_succ' _ _
        obtain ⟨B, hBD, hcost, hgood⟩ := ih D (fun E hED => hpos E (hED.trans hDA)) hnext
        refine ⟨B, hBD.trans hDA, ?_, hgood⟩
        have hh : A.card ≤ (B.card + n * r) + r := hremove.trans (Nat.add_le_add_right hcost r)
        simpa only [Nat.succ_mul, Nat.add_assoc] using hh

theorem delta_exists_weakly_stable_highFold_subset (A : Finset ℤ) (L k t b r : ℕ)
    (hA : A ⊆ Finset.Icc 0 ((2 ^ L : ℕ) : ℤ)) (hk : k ≤ L)
    (ht : 0 < t) (hscale : L ≤ t * b) :
    ∃ B ⊆ A, A.card ≤ B.card + (2 * b + 2) * r ∧
      ∀ D ⊆ B, B.card ≤ D.card + r →
        (dyadicSumsetWithZero B k).card < 2 ^ t * (dyadicSumsetWithZero D k).card := by
  let V := fun B : Finset ℤ => (dyadicSumsetWithZero B k).card
  have hpos : ∀ B ⊆ A, 0 < V B := fun B _ =>
    Finset.card_pos.mpr (dyadicSumsetWithZero_nonempty B k)
  have hinit : V A < (2 ^ t) ^ ((2 * b + 2) + 1) := by
    calc
      V A ≤ 2 ^ (2 * L + 1) := dyadicSumsetWithZero_card_le A L k hA hk
      _ < 2 ^ (t * ((2 * b + 2) + 1)) := by
        apply Nat.pow_lt_pow_right (by norm_num)
        nlinarith
      _ = _ := pow_mul _ _ _
  exact delta_exists_weakly_stable_subset V A r (2 ^ t) (2 * b + 2) hpos hinit

theorem delta_exists_relatively_weakly_stable_subset {α : Type*} (V : Finset α → ℕ)
    (A : Finset α) (K n : ℕ)
    (hpos : ∀ B ⊆ A, 0 < V B) (hinit : V A < K ^ (n + 1)) :
    ∃ B ⊆ A, A.card ≤ 3 ^ n * B.card ∧
      ∀ D ⊆ B, B.card ≤ 3 * D.card → V B < K * V D := by
  classical
  induction n generalizing A with
  | zero =>
    refine ⟨A, Finset.Subset.refl A, by simp, ?_⟩
    intro D hDA _
    calc
      V A < K := by simpa only [zero_add, pow_one] using hinit
      _ ≤ K * V D := by
        have hVD : 1 ≤ V D := hpos D hDA
        simpa only [mul_one] using Nat.mul_le_mul_left K hVD
  | succ n ih =>
    by_cases hstable : ∀ D ⊆ A, A.card ≤ 3 * D.card → V A < K * V D
    · refine ⟨A, Finset.Subset.refl A, ?_, hstable⟩
      simpa only [one_mul] using Nat.mul_le_mul_right A.card
        (one_le_pow₀ (by norm_num : 1 ≤ (3 : ℕ)))
    · push Not at hstable
      obtain ⟨D, hDA, hcard, hdrop⟩ := hstable
      have hnext : V D < K ^ (n + 1) := by
        apply Nat.lt_of_mul_lt_mul_left (a := K)
        calc
          K * V D ≤ V A := hdrop
          _ < K ^ (n + 1 + 1) := hinit
          _ = K * K ^ (n + 1) := pow_succ' _ _
      obtain ⟨B, hBD, hretain, hgood⟩ :=
        ih D (fun E hED => hpos E (hED.trans hDA)) hnext
      refine ⟨B, hBD.trans hDA, ?_, hgood⟩
      calc
        A.card ≤ 3 * D.card := hcard
        _ ≤ 3 * (3 ^ n * B.card) := Nat.mul_le_mul_left 3 hretain
        _ = 3 ^ (n + 1) * B.card := by rw [pow_succ]; ring

theorem delta_exists_relative_highFold_subset (A : Finset ℤ) (L k t b : ℕ)
    (hA : A ⊆ Finset.Icc 0 ((2 ^ L : ℕ) : ℤ)) (hk : k ≤ L)
    (ht : 0 < t) (hscale : L ≤ t * b) :
    ∃ B ⊆ A, A.card ≤ 3 ^ (2 * b + 2) * B.card ∧
      ∀ D ⊆ B, B.card ≤ 3 * D.card →
        (dyadicSumsetWithZero B k).card < 2 ^ t * (dyadicSumsetWithZero D k).card := by
  let V := fun B : Finset ℤ => (dyadicSumsetWithZero B k).card
  have hpos : ∀ B ⊆ A, 0 < V B := fun B _ =>
    Finset.card_pos.mpr (dyadicSumsetWithZero_nonempty B k)
  have hinit : V A < (2 ^ t) ^ ((2 * b + 2) + 1) := by
    calc
      V A ≤ 2 ^ (2 * L + 1) := dyadicSumsetWithZero_card_le A L k hA hk
      _ < 2 ^ (t * ((2 * b + 2) + 1)) := by
        apply Nat.pow_lt_pow_right (by norm_num)
        nlinarith
      _ = _ := pow_mul _ _ _
  exact delta_exists_relatively_weakly_stable_subset V A (2 ^ t) (2 * b + 2) hpos hinit

end Erdos587.CFP
