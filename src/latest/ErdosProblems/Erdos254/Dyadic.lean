/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos254.Syndetic

namespace Erdos254

open Filter Set
open scoped BigOperators

private lemma initialSegment_dyadic_union (A : Set ℕ) (k : ℕ) :
    initialSegment A (2 ^ (k + 1) + 1) =
      initialSegment A (2 ^ k + 1) ∪ dyadicBlock A k := by
  classical
  have hp : 2 ^ k ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by omega) (by omega)
  ext n
  simp only [mem_initialSegment, Finset.mem_union, mem_dyadicBlock]
  constructor
  · rintro ⟨hn, hA⟩
    by_cases h : n ≤ 2 ^ k
    · exact Or.inl ⟨by omega, hA⟩
    · exact Or.inr ⟨by omega, by omega, hA⟩
  · rintro (⟨hn, hA⟩ | ⟨hn, hm, hA⟩)
    · exact ⟨by omega, hA⟩
    · exact ⟨by omega, hA⟩

private lemma initialSegment_disjoint_dyadic (A : Set ℕ) (k : ℕ) :
    Disjoint (initialSegment A (2 ^ k + 1)) (dyadicBlock A k) := by
  apply Finset.disjoint_left.mpr
  intro n hn hm
  have := mem_initialSegment.mp hn
  have := mem_dyadicBlock.mp hm
  omega

/-- Two elements in each dyadic block already force bounded defect
(Fan, Lemma 3.3, specialized to base two). -/
theorem boundedDefect_of_two_per_dyadic {A : Set ℕ} {k₀ : ℕ}
    (hA : ∀ k, k₀ ≤ k → 2 ≤ (dyadicBlock A k).card) : HasBoundedDefect A := by
  classical
  have hmass : ∀ k, k₀ ≤ k →
      2 ^ (k + 1) ≤ (∑ b ∈ initialSegment A (2 ^ k + 1), b) + 2 ^ (k₀ + 1) := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => omega
    | succ k hk ih =>
        have hblock : 2 * 2 ^ k ≤ ∑ b ∈ dyadicBlock A k, b := by
          calc
            2 * 2 ^ k ≤ (dyadicBlock A k).card * 2 ^ k := Nat.mul_le_mul_right _ (hA k hk)
            _ ≤ ∑ b ∈ dyadicBlock A k, b := by
              simpa only [nsmul_eq_mul, Nat.cast_id, id_eq] using
                (dyadicBlock A k).card_nsmul_le_sum id (2 ^ k)
                  (fun b hb ↦ (mem_dyadicBlock.mp hb).1.le)
        rw [initialSegment_dyadic_union, Finset.sum_union (initialSegment_disjoint_dyadic A k)]
        simp only [pow_succ] at ih ⊢
        nlinarith
  refine ⟨2 ^ (k₀ + 1), ?_⟩
  intro a ha
  by_cases hsmall : a ≤ 2 ^ (k₀ + 1)
  · omega
  · have haone : 1 < a := by
      have hp : 0 < 2 ^ (k₀ + 1) := pow_pos (by omega) _
      omega
    let k := Nat.log 2 (a - 1)
    have hlo : 2 ^ k < a := by
      have h := Nat.pow_log_le_self 2 (show a - 1 ≠ 0 by omega)
      dsimp [k]
      omega
    have hhi : a ≤ 2 ^ (k + 1) := by
      have h := Nat.lt_pow_succ_log_self (by omega : 1 < 2) (a - 1)
      change a - 1 < 2 ^ (k + 1) at h
      omega
    have hk : k₀ ≤ k := by
      by_contra h
      have hp : 2 ^ (k + 1) ≤ 2 ^ (k₀ + 1) :=
        Nat.pow_le_pow_right (by omega) (show k + 1 ≤ k₀ + 1 by omega)
      omega
    have hsub : initialSegment A (2 ^ k + 1) ⊆ initialSegment A a := by
      intro b hb
      rcases mem_initialSegment.mp hb with ⟨hblt, hbA⟩
      exact mem_initialSegment.mpr ⟨by omega, hbA⟩
    have hsum : (∑ b ∈ initialSegment A (2 ^ k + 1), b) ≤
        ∑ b ∈ initialSegment A a, b := Finset.sum_le_sum_of_subset hsub
    exact hhi.trans ((hmass k hk).trans (Nat.add_le_add_right hsum _))

/-- The original counting-function difference is exactly a dyadic-interval count. -/
lemma count_difference_eq (A : Set ℕ) (x : ℕ) :
    (A ∩ Icc 1 (2 * x)).ncard - (A ∩ Icc 1 x).ncard =
      (A ∩ Ioc x (2 * x)).ncard := by
  have hsub : A ∩ Icc 1 x ⊆ A ∩ Icc 1 (2 * x) := by
    intro n hn
    exact ⟨hn.1, hn.2.1, by have := hn.2.2; omega⟩
  have heq : (A ∩ Icc 1 (2 * x)) \ (A ∩ Icc 1 x) = A ∩ Ioc x (2 * x) := by
    ext n
    constructor
    · rintro ⟨⟨hnA, hn1, hn2⟩, hn⟩
      refine ⟨hnA, ?_, hn2⟩
      by_contra h
      exact hn ⟨hnA, hn1, by omega⟩
    · rintro ⟨hnA, hn1, hn2⟩
      refine ⟨⟨hnA, by omega, hn2⟩, ?_⟩
      rintro ⟨_, _, hn⟩
      omega
  rw [← Set.ncard_sdiff hsub, heq]

lemma dyadicBlock_card (A : Set ℕ) (k : ℕ) :
    (dyadicBlock A k).card = (A ∩ Ioc (2 ^ k) (2 ^ (k + 1))).ncard := by
  have heq : (dyadicBlock A k : Set ℕ) = A ∩ Ioc (2 ^ k) (2 ^ (k + 1)) := by
    ext n
    simp only [Finset.mem_coe, mem_dyadicBlock, mem_inter_iff, mem_Ioc]
    tauto
  rw [← Set.ncard_coe_finset, heq]

/-- The original unbounded block-count hypothesis implies every fixed eventual
lower bound, in particular the bound six in Fan's Corollary 1.2. -/
theorem eventually_dyadic_count_ge {A : Set ℕ}
    (hA : Tendsto (fun x : ℕ ↦
      (A ∩ Icc 1 (2 * x)).ncard - (A ∩ Icc 1 x).ncard) atTop atTop) (M : ℕ) :
    ∀ᶠ k in atTop, M ≤ (dyadicBlock A k).card := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hA.eventually (eventually_ge_atTop M))
  apply eventually_atTop.mpr
  refine ⟨N, fun k hk ↦ ?_⟩
  have hx : N ≤ 2 ^ k := hk.trans (Nat.lt_two_pow_self.le)
  have h := hN (2 ^ k) hx
  rw [count_difference_eq] at h
  simpa only [dyadicBlock_card, pow_succ, Nat.mul_comm] using h

lemma dyadicBlock_pairwiseDisjoint (A : Set ℕ) :
    Pairwise (fun i j ↦ Disjoint (dyadicBlock A i) (dyadicBlock A j)) := by
  intro i j hij
  apply Finset.disjoint_left.mpr
  intro a hai haj
  have hi := mem_dyadicBlock.mp hai
  have hj := mem_dyadicBlock.mp haj
  rcases lt_or_gt_of_ne hij with h | h
  · have hp : 2 ^ (i + 1) ≤ 2 ^ j := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  · have hp : 2 ^ (j + 1) ≤ 2 ^ i := Nat.pow_le_pow_right (by omega) (by omega)
    omega

lemma mem_dyadic_tail_iff (A : Set ℕ) (k₀ a : ℕ) :
    (∃ k, a ∈ dyadicBlock A (k₀ + k)) ↔ a ∈ A ∧ 2 ^ k₀ < a := by
  constructor
  · rintro ⟨k, hk⟩
    rcases mem_dyadicBlock.mp hk with ⟨hlo, _, hA⟩
    have hp : 2 ^ k₀ ≤ 2 ^ (k₀ + k) := Nat.pow_le_pow_right (by omega) (by omega)
    exact ⟨hA, hp.trans_lt hlo⟩
  · rintro ⟨ha, hlarge⟩
    have hp : 0 < 2 ^ k₀ := pow_pos (by omega) _
    have hane : a - 1 ≠ 0 := by omega
    let j := Nat.log 2 (a - 1)
    have hj : k₀ ≤ j := Nat.le_log_of_pow_le (by omega) (show 2 ^ k₀ ≤ a - 1 by omega)
    refine ⟨j - k₀, ?_⟩
    rw [Nat.add_sub_of_le hj]
    apply mem_dyadicBlock.mpr
    have hlo : 2 ^ j ≤ a - 1 := Nat.pow_log_le_self 2 hane
    have hhi : a - 1 < 2 ^ (j + 1) := Nat.lt_pow_succ_log_self (by omega) _
    exact ⟨by omega, by omega, ha⟩

lemma infinite_of_dyadic_count {A : Set ℕ} {k₀ : ℕ}
    (hA : ∀ k, k₀ ≤ k → 1 ≤ (dyadicBlock A k).card) : A.Infinite := by
  apply Set.infinite_of_not_bddAbove
  rintro ⟨M, hM⟩
  obtain ⟨a, ha⟩ := Finset.card_pos.mp (hA (k₀ + M) (by omega))
  have hm := hM (mem_dyadicBlock.mp ha).2.2
  have hlo := (mem_dyadicBlock.mp ha).1
  have hp : M ≤ 2 ^ (k₀ + M) := (Nat.lt_two_pow_self (n := M)).le.trans
    (Nat.pow_le_pow_right (by omega) (by omega))
  omega

end Erdos254
