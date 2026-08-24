import ErdosProblems.Erdos587.GreedyGrowthBounds

/-!
Robust high-fold density forces a small actual subset to have many subset
sums. The number of selected elements is linear in the fold count and
logarithmic in the target volume.
-/

open scoped Pointwise

namespace Erdos587.CFP

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

theorem card_greedyStep_le (A B : Finset G) : (greedyStep A B).card ≤ B.card + 1 := by
  by_cases h : (A \ B).Nonempty
  · rw [card_greedyStep h]
  · simp [greedyStep, h]

theorem card_greedySubset_le (A : Finset G) (n : ℕ) : (greedySubset A n).card ≤ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [greedySubset_succ]
    exact (card_greedyStep_le A _).trans (Nat.add_le_add_right ih 1)

theorem greedySubset_pow_two_growth (A : Finset G) {h : ℕ} (hh : 0 < h) (n : ℕ)
    (hlarge : ∀ j < (2 * h) * n,
      2 * (greedySubset A j).subsetSum.card ≤
        (h • insert 0 (A \ greedySubset A j)).card) :
    2 ^ n ≤ (greedySubset A ((2 * h) * n)).subsetSum.card := by
  have hsteps (j : ℕ) (hj : j < (2 * h) * n) :
      (((2 * h : ℕ) : ℝ) + 1) * ((greedySubset A j).subsetSum.card : ℝ) ≤
        ((2 * h : ℕ) : ℝ) * ((greedySubset A (j + 1)).subsetSum.card : ℝ) := by
    exact_mod_cast greedySubset_growth A j h (hlarge j hj)
  have hg := growth_interval_pow_two (greedySubset_real_card_mono A)
    (Nat.mul_pos (by omega : 0 < 2) hh) 0 n (fun j hj => by
      simpa only [Nat.zero_add] using hsteps j hj)
  have hzero : (greedySubset A 0).subsetSum.card = 1 := by simp [Finset.subsetSum]
  rw [hzero] at hg
  norm_num only [Nat.cast_one, mul_one, Nat.zero_add] at hg
  exact_mod_cast hg

theorem greedySubset_reaches_density (A : Finset G) (h M T r : ℕ)
    (hh : 0 < h) (hM : 1 ≤ M)
    (hbudget : (2 * h) * (Nat.log 2 T + 1) ≤ r)
    (hdense : ∀ D ⊆ A, A.card ≤ D.card + r →
      2 * T < M * (h • insert 0 D).card) :
    T < M * (greedySubset A ((2 * h) * (Nat.log 2 T + 1))).subsetSum.card := by
  let n := (2 * h) * (Nat.log 2 T + 1)
  by_contra hnot
  have hlast : M * (greedySubset A n).subsetSum.card ≤ T := le_of_not_gt hnot
  have hlarge (j : ℕ) (hj : j < n) :
      2 * (greedySubset A j).subsetSum.card ≤
        (h • insert 0 (A \ greedySubset A j)).card := by
    have hsub := greedySubset_subset A j
    have hcard := card_greedySubset_le A j
    have hcardA := Finset.card_le_card hsub
    have hcost : A.card ≤ (A \ greedySubset A j).card + r := by
      rw [Finset.card_sdiff_of_subset hsub]
      omega
    have hd := hdense (A \ greedySubset A j) Finset.sdiff_subset hcost
    have hmono := Nat.mul_le_mul_left M (greedySubset_card_mono A hj.le)
    have hm : M * (2 * (greedySubset A j).subsetSum.card) ≤ 2 * T := by
      nlinarith
    exact (Nat.lt_of_mul_lt_mul_left (hm.trans_lt hd)).le
  have hpow := greedySubset_pow_two_growth A hh (Nat.log 2 T + 1) hlarge
  have ht := Nat.lt_pow_succ_log_self Nat.one_lt_two T
  have hm : (greedySubset A n).subsetSum.card ≤ M * (greedySubset A n).subsetSum.card := by
    simpa only [one_mul] using Nat.mul_le_mul_right (greedySubset A n).subsetSum.card hM
  exact (not_lt_of_ge hlast) ((ht.trans_le hpow).trans_le hm)

/-- The output consists of distinct elements of the original set, not
unrestricted repeated summands. -/
theorem exists_small_subset_with_dense_subsetSums (A : Finset G) (h M T r : ℕ)
    (hh : 0 < h) (hM : 1 ≤ M)
    (hbudget : (2 * h) * (Nat.log 2 T + 1) ≤ r)
    (hdense : ∀ D ⊆ A, A.card ≤ D.card + r →
      2 * T < M * (h • insert 0 D).card) :
    ∃ S ⊆ A, S.card ≤ (2 * h) * (Nat.log 2 T + 1) ∧ T < M * S.subsetSum.card := by
  refine ⟨greedySubset A ((2 * h) * (Nat.log 2 T + 1)), greedySubset_subset A _,
    card_greedySubset_le A _, ?_⟩
  exact greedySubset_reaches_density A h M T r hh hM hbudget hdense

end Erdos587.CFP
