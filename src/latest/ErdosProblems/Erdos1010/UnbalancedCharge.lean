import ErdosProblems.Erdos1010.SparseCharge
import ErdosProblems.Erdos1010.UnbalancedArithmetic

/-! # The charge correction for an unbalanced cut -/

open Finset

namespace Erdos1010

open Bipartite

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

def unbalancedCharge (HA : SimpleGraph A) (HB : SimpleGraph B)
    [DecidableRel HA.Adj] [DecidableRel HB.Adj] (M : Finset (A × B)) (s : ℤ) : ℤ :=
  cutCharge HA HB M + s * (HB.edgeFinset.card - (HA.edgeFinset.card : ℤ))

lemma unbalancedCharge_le_add (HA : SimpleGraph A) (HB : SimpleGraph B)
    [DecidableRel HA.Adj] [DecidableRel HB.Adj] (M : Finset (A × B)) (s : ℤ) (hs : 0 ≤ s) :
    unbalancedCharge HA HB M s ≤ cutCharge HA HB M +
      s * (HA.edgeFinset.card + (HB.edgeFinset.card : ℤ)) := by
  unfold unbalancedCharge
  have := mul_nonneg hs (Nat.cast_nonneg (α := ℤ) HA.edgeFinset.card)
  nlinarith

lemma nonstar_charge_add_s2_of_left_max (HA : SimpleGraph A) (HB : SimpleGraph B)
    [DecidableRel HA.Adj] [DecidableRel HB.Adj] (M : Finset (A × B)) (u : A) (r s k : ℤ)
    (hs : 2 ≤ s) (hk : 1 ≤ k) (hu : (leftDegree M u : ℤ) = k) (hstar : k < M.card)
    (hA : ∀ a, (leftDegree M a : ℤ) ≤ k) (hB : ∀ b, (rightDegree M b : ℤ) ≤ k)
    (hr : (M.card : ℤ) + s ^ 2 + 2 ≤ r)
    (hq : HA.edgeFinset.card + (HB.edgeFinset.card : ℤ) ≤ r + M.card + s ^ 2 - 1)
    (hcapA : ∀ a, (HA.degree a : ℤ) + leftDegree M a ≤ r + s)
    (hcapAB : ∀ a b, (HA.degree a : ℤ) + leftDegree M a + HB.degree b + rightDegree M b ≤ 2 * r - 1) :
    cutCharge HA HB M + s * (HA.edgeFinset.card + (HB.edgeFinset.card : ℤ)) ≤
      r * (M.card + s ^ 2) := by
  let q : ℤ := HA.edgeFinset.card + (HB.edgeFinset.card : ℤ)
  let W := cutCharge HA HB M + s * q
  change W ≤ r * (M.card + s ^ 2)
  by_cases hlarge : 2 * k + 1 ≤ M.card
  · have hc := cutCharge_quadratic HA HB M k (by omega) hA hB
    apply ChargeArithmetic.unbalanced_large_s2 hs hk hlarge hr hq
    dsimp [W, q]
    nlinarith only [hc]
  by_cases hequal : (M.card : ℤ) = 2 * k
  · have hc := cutCharge_pair_bound HA HB M k 0 (by omega) le_rfl (by omega) hA hB (by omega)
    rw [hequal] at hr hq ⊢
    apply ChargeArithmetic.unbalanced_equal_s2 hs hk hr hq
    dsimp [W, q]
    nlinarith only [hc]
  by_cases hgap : (M.card : ℤ) = 2 * k - 1
  · have hk2 : 2 ≤ k := by omega
    by_cases hv : ∃ v, (rightDegree M v : ℤ) = k
    · obtain ⟨v, hv⟩ := hv
      have hp : (HA.degree u : ℤ) + HB.degree v ≤ 2 * r - 2 * k - 1 := by
        have := hcapAB u v
        omega
      by_cases hk_eq : k = 2
      · have hD3 : (M.card : ℤ) = 3 := by omega
        have hc := cutCharge_double_two_bound HA HB M u v (hu.trans hk_eq) (hv.trans hk_eq) hD3
        rw [hD3] at hr hq ⊢
        apply ChargeArithmetic.unbalanced_gap_double_two_s2 hs hr hq
        dsimp [W, q]
        nlinarith only [hc, hp, hk_eq]
      · have hc := cutCharge_double_bound HA HB M u v k hu hv hgap
        have hp' := mul_le_mul_of_nonneg_left hp (show 0 ≤ k - 2 by omega)
        rw [hgap] at hr hq ⊢
        apply ChargeArithmetic.unbalanced_gap_double_s2 hs (by omega) hr hq
        dsimp [W, q]
        nlinarith only [hc, hp']
    · have hB' : ∀ b, (rightDegree M b : ℤ) ≤ k - 1 := by
        intro b
        have := hB b
        have : (rightDegree M b : ℤ) ≠ k := fun h ↦ hv ⟨b, h⟩
        omega
      have hc := cutCharge_gap_single_bound HA HB M u k hk2 hu hgap hB'
      have hp := hcapA u
      rw [hgap] at hr hq ⊢
      apply ChargeArithmetic.unbalanced_gap_single_s2 hs hk2 hr hq
      dsimp [W, q]
      nlinarith only [hc, hp, hu, hk2]
  · let h : ℤ := M.card - k
    have hh : 1 ≤ h := by dsimp [h]; omega
    have hhk : h ≤ k - 2 := by dsimp [h]; omega
    have hD : (M.card : ℤ) = k + h := by dsimp [h]; ring
    have hc := cutCharge_dominant_bound HA HB M u k h hk hh hu hD
    have hp : (HA.degree u : ℤ) ≤ r + s - k := by have := hcapA u; omega
    have hp' := mul_le_mul_of_nonneg_left hp (show 0 ≤ k - h - 1 by omega)
    rw [hD] at hr hq ⊢
    apply ChargeArithmetic.unbalanced_dominant_s2 hs hh hhk
      (by linarith : k + h + s ^ 2 + 2 ≤ r)
      (by linarith : q ≤ r + k + h + s ^ 2 - 1)
    dsimp [W, q]
    nlinarith only [hc, hp']

/-- For nonstar missing-edge graphs, the stronger symmetric charge bound
suffices whenever the imbalance is at least two. -/
theorem nonstar_charge_add_s2 (HA : SimpleGraph A) (HB : SimpleGraph B)
    [DecidableRel HA.Adj] [DecidableRel HB.Adj] (M : Finset (A × B)) (r s : ℤ)
    (hs : 2 ≤ s) (hM : M.Nonempty)
    (hstarA : ∀ a, leftDegree M a < M.card) (hstarB : ∀ b, rightDegree M b < M.card)
    (hr : (M.card : ℤ) + s ^ 2 + 2 ≤ r)
    (hq : HA.edgeFinset.card + (HB.edgeFinset.card : ℤ) ≤ r + M.card + s ^ 2 - 1)
    (hcapA : ∀ a, (HA.degree a : ℤ) + leftDegree M a ≤ r + s)
    (hcapB : ∀ b, (HB.degree b : ℤ) + rightDegree M b ≤ r + s)
    (hcapAB : ∀ a b, (HA.degree a : ℤ) + leftDegree M a + HB.degree b + rightDegree M b ≤ 2 * r - 1) :
    cutCharge HA HB M + s * (HA.edgeFinset.card + (HB.edgeFinset.card : ℤ)) ≤
      r * (M.card + s ^ 2) := by
  obtain ⟨k, hk, hA, hB, hmax⟩ := exists_max_degree M hM
  have hk' : (1 : ℤ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
  have hA' : ∀ a, (leftDegree M a : ℤ) ≤ k := fun a ↦ by exact_mod_cast hA a
  have hB' : ∀ b, (rightDegree M b : ℤ) ≤ k := fun b ↦ by exact_mod_cast hB b
  rcases hmax with ⟨u, hu⟩ | ⟨v, hv⟩
  · exact nonstar_charge_add_s2_of_left_max HA HB M u r s k hs hk'
      (by exact_mod_cast hu) (by have := hstarA u; omega) hA' hB' hr hq hcapA hcapAB
  · have h := nonstar_charge_add_s2_of_left_max HB HA (transpose M) v r s k hs hk'
      (by simpa [leftDegree_transpose] using (show (rightDegree M v : ℤ) = k by exact_mod_cast hv))
      (by rw [card_transpose]; have := hstarB v; omega)
      (fun b ↦ by simpa [leftDegree_transpose] using hB' b)
      (fun a ↦ by simpa [rightDegree_transpose] using hA' a)
      (by simpa [card_transpose] using hr)
      (by simpa [card_transpose, add_comm] using hq)
      (fun b ↦ by simpa [leftDegree_transpose] using hcapB b)
      (fun b a ↦ by
        simp only [leftDegree_transpose, rightDegree_transpose]
        have := hcapAB a b
        linarith)
    simpa [cutCharge_transpose, card_transpose, add_comm] using h

lemma unbalanced_charge_star_right (HA : SimpleGraph A) (HB : SimpleGraph B)
    [DecidableRel HA.Adj] [DecidableRel HB.Adj] (M : Finset (A × B)) (v : B) (r s : ℤ)
    (hs : 1 ≤ s) (hv : rightDegree M v = M.card)
    (hr : (M.card : ℤ) + s ^ 2 + 2 ≤ r)
    (hq : HA.edgeFinset.card + (HB.edgeFinset.card : ℤ) ≤ r + M.card + s ^ 2 - 1)
    (hcap : (HB.degree v : ℤ) + M.card ≤ r - s - 1) :
    unbalancedCharge HA HB M s ≤ r * (M.card + s ^ 2) := by
  have hv' : leftDegree (transpose M) v = (transpose M).card := by
    simpa [leftDegree_transpose, card_transpose] using hv
  have hc := cutCharge_star_le_twice_edges HB HA (transpose M) v hv'
  simp only [cutCharge_transpose, card_transpose] at hc
  have hx : 0 ≤ (s - 1) * (HA.edgeFinset.card : ℤ) :=
    mul_nonneg (by omega) (Nat.cast_nonneg _)
  apply ChargeArithmetic.unbalanced_star_right hs (Nat.cast_nonneg _) hr hq
    (show (HB.degree v : ℤ) ≤ r - s - 1 - M.card by omega)
  unfold unbalancedCharge
  nlinarith only [hc, hx]

lemma unbalanced_charge_star_left (HA : SimpleGraph A) (HB : SimpleGraph B)
    [DecidableRel HA.Adj] [DecidableRel HB.Adj] (M : Finset (A × B)) (u : A) (r s : ℤ)
    (hs : 1 ≤ s) (hu : leftDegree M u = M.card)
    (hr : (M.card : ℤ) + s ^ 2 + 2 ≤ r)
    (hq : HA.edgeFinset.card + (HB.edgeFinset.card : ℤ) ≤ r + M.card + s ^ 2 - 1)
    (hcapA : (HA.degree u : ℤ) + M.card ≤ r + s)
    (hcapB : ∀ b, (HB.degree b : ℤ) + rightDegree M b ≤ r - s - 1) :
    unbalancedCharge HA HB M s ≤ r * (M.card + s ^ 2) := by
  let q : ℤ := HA.edgeFinset.card + (HB.edgeFinset.card : ℤ)
  have hp : (HA.degree u : ℤ) ≤ HA.edgeFinset.card := by exact_mod_cast HA.degree_le_card_edgeFinset u
  have hp0 : (0 : ℤ) ≤ HA.degree u := Nat.cast_nonneg _
  have hc1 := cutCharge_star_le_edges_pairs HA HB M u hu
  have hc2 := cutCharge_star_le_twice_edges HA HB M u hu
  have hraw : unbalancedCharge HA HB M s ≤
      (s + 2) * q + (M.card - 2 * s - 2) * HA.degree u := by
    have hslack := mul_nonneg (show 0 ≤ 2 * s + 2 by omega) (sub_nonneg.mpr hp)
    dsimp [unbalancedCharge, q]
    nlinarith only [hc2, hslack]
  by_cases hlarge : 2 * s + 2 ≤ M.card
  · exact ChargeArithmetic.unbalanced_star_left_large hs hlarge hr hq
      (show (HA.degree u : ℤ) ≤ r + s - M.card by omega) hraw
  have hsmall : unbalancedCharge HA HB M s ≤ (s + 2) * q := by
    have hneg := mul_nonpos_of_nonpos_of_nonneg (show (M.card : ℤ) - 2 * s - 2 ≤ 0 by omega) hp0
    linarith
  by_cases hD0 : M.card = 0
  · have hM := card_eq_zero.mp hD0
    subst M
    simp only [card_empty, Nat.cast_zero, zero_add] at hr hq ⊢
    have hcut := unbalancedCharge_le_add HA HB ∅ s (by omega)
    rw [cutCharge_empty, zero_add] at hcut
    have hq' := mul_le_mul_of_nonneg_left hq (show 0 ≤ s by omega)
    have hrs : 0 ≤ r - s - 1 := by nlinarith
    have hgap : 0 ≤ s * (s - 1) * (r - s - 1) := by
      have : 0 ≤ s - 1 := by omega
      positivity
    nlinarith
  have hDpos : (1 : ℤ) ≤ M.card := by omega
  by_cases hD1 : M.card = 1
  · have hLcard : (univ.filter fun b ↦ (u, b) ∈ M).card = 1 := by
      rw [card_right_neighbors, hu, hD1]
    obtain ⟨b, hL⟩ := card_eq_one.mp hLcard
    have hb : (u, b) ∈ M := by
      have hmem : b ∈ univ.filter (fun b ↦ (u, b) ∈ M) := by rw [hL]; simp
      exact (mem_filter.mp hmem).2
    have hdeg : rightDegree M b = 1 := by rw [rightDegree_of_star M u b hu, if_pos hb]
    have hleaf := hcapB b
    have hC := cutCharge_star_eq HA HB M u hu
    rw [hL, sum_singleton, hD1] at hC
    norm_num at hC
    rw [hD1] at hr hq ⊢
    norm_num at hr hq ⊢
    apply ChargeArithmetic.unbalanced_star_one hs (by linarith)
      (by linarith : q ≤ r + s ^ 2)
    have hx := mul_nonneg (show 0 ≤ s - 1 by omega) (Nat.cast_nonneg (α := ℤ) HA.edgeFinset.card)
    dsimp [unbalancedCharge, q]
    rw [hdeg] at hleaf
    norm_num at hleaf
    nlinarith only [hC, hleaf, hp, hx]
  by_cases hD2 : M.card = 2
  · rw [hD2] at hr hq hc1 ⊢
    norm_num at hr hq hc1 ⊢
    apply ChargeArithmetic.unbalanced_star_two hs (by linarith)
      (by linarith : q ≤ r + s ^ 2 + 1)
    have hslack := mul_nonneg (show 0 ≤ 2 * s + 1 by omega) (sub_nonneg.mpr hp)
    have hneg := mul_nonneg (show 0 ≤ 2 * s - 1 by omega) hp0
    dsimp [unbalancedCharge, q]
    nlinarith only [hc1, hslack, hneg]
  by_cases hs3 : 3 ≤ s
  · exact ChargeArithmetic.unbalanced_star_left_small_s3 hs3 hDpos hr hq hsmall
  by_cases hs2 : s = 2
  · have hD3 : (3 : ℤ) ≤ M.card := by omega
    rw [hs2] at hr hq hsmall ⊢
    norm_num at hr hq hsmall ⊢
    exact ChargeArithmetic.unbalanced_star_left_small_s2 hD3 (by linarith)
      (by linarith : q ≤ r + M.card + 3) hsmall
  · have hs1 : s = 1 := by omega
    have hD3 : M.card = 3 := by omega
    rw [hs1, hD3] at hr hq ⊢
    rw [hD3] at hc1
    norm_num at hr hq hc1 ⊢
    unfold unbalancedCharge
    norm_num
    nlinarith only [hc1, hp, hr, hq]

lemma unbalanced_charge_empty (HA : SimpleGraph A) (HB : SimpleGraph B)
    [DecidableRel HA.Adj] [DecidableRel HB.Adj] (r s : ℤ) (hs : 1 ≤ s)
    (hr : s ^ 2 + 2 ≤ r)
    (hq : HA.edgeFinset.card + (HB.edgeFinset.card : ℤ) ≤ r + s ^ 2 - 1) :
    unbalancedCharge HA HB ∅ s ≤ r * s ^ 2 := by
  have hcut := unbalancedCharge_le_add HA HB ∅ s (by omega)
  rw [cutCharge_empty, zero_add] at hcut
  have hq' := mul_le_mul_of_nonneg_left hq (show 0 ≤ s by omega)
  have hrs : 0 ≤ r - s - 1 := by nlinarith
  have hgap : 0 ≤ s * (s - 1) * (r - s - 1) := by
    have : 0 ≤ s - 1 := by omega
    positivity
  nlinarith

/-- The complete unbalanced sparse-cut lemma for imbalance at least two. -/
theorem unbalanced_sparse_charge_s2 (HA : SimpleGraph A) (HB : SimpleGraph B)
    [DecidableRel HA.Adj] [DecidableRel HB.Adj] (M : Finset (A × B)) (r s : ℤ)
    (hs : 2 ≤ s) (hr : (M.card : ℤ) + s ^ 2 + 2 ≤ r)
    (hq : HA.edgeFinset.card + (HB.edgeFinset.card : ℤ) ≤ r + M.card + s ^ 2 - 1)
    (hcapA : ∀ a, (HA.degree a : ℤ) + leftDegree M a ≤ r + s)
    (hcapB : ∀ b, (HB.degree b : ℤ) + rightDegree M b ≤ r - s - 1) :
    unbalancedCharge HA HB M s ≤ r * (M.card + s ^ 2) := by
  by_cases hM : M.Nonempty
  · by_cases hstarA : ∃ u, leftDegree M u = M.card
    · obtain ⟨u, hu⟩ := hstarA
      exact unbalanced_charge_star_left HA HB M u r s (by omega) hu hr hq
        (by simpa [hu] using hcapA u) hcapB
    by_cases hstarB : ∃ v, rightDegree M v = M.card
    · obtain ⟨v, hv⟩ := hstarB
      exact unbalanced_charge_star_right HA HB M v r s (by omega) hv hr hq
        (by simpa [hv] using hcapB v)
    have hnA : ∀ a, leftDegree M a < M.card := by
      intro a
      have := leftDegree_le_card M a
      have : leftDegree M a ≠ M.card := fun h ↦ hstarA ⟨a, h⟩
      omega
    have hnB : ∀ b, rightDegree M b < M.card := by
      intro b
      have := rightDegree_le_card M b
      have : rightDegree M b ≠ M.card := fun h ↦ hstarB ⟨b, h⟩
      omega
    have h := nonstar_charge_add_s2 HA HB M r s hs hM hnA hnB hr hq hcapA
      (fun b ↦ by have := hcapB b; omega)
      (fun a b ↦ by have := hcapA a; have := hcapB b; omega)
    exact (unbalancedCharge_le_add HA HB M s (by omega)).trans h
  · have hzero : M = ∅ := not_nonempty_iff_eq_empty.mp hM
    subst M
    simp only [card_empty, Nat.cast_zero, zero_add, add_zero] at hr hq ⊢
    exact unbalanced_charge_empty HA HB r s (by omega) hr hq

end Erdos1010
