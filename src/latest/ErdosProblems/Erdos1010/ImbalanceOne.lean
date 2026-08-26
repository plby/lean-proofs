import ErdosProblems.Erdos1010.UnbalancedCharge
import ErdosProblems.Erdos1010.MissingPairs
import ErdosProblems.Erdos1010.AsymmetricPairs

/-! # The imbalance-one charge cases -/

open Finset

namespace Erdos1010

open Bipartite

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

lemma unbalancedCharge_one_le_pairs (HA : SimpleGraph A) (HB : SimpleGraph B)
    [DecidableRel HA.Adj] [DecidableRel HB.Adj] (M : Finset (A × B)) (k : ℤ) :
    unbalancedCharge HA HB M 1 ≤ k * (HA.edgeFinset.card + (HB.edgeFinset.card : ℤ)) +
      pairExcess univ (fun a ↦ (leftDegree M a : ℤ)) (k + 1) +
      pairExcess univ (fun b ↦ (rightDegree M b : ℤ)) (k - 1) := by
  have hA := graph_weighted_degree_le HA (fun a ↦ (leftDegree M a : ℤ)) (k + 1)
  have hB := graph_weighted_degree_le HB (fun b ↦ (rightDegree M b : ℤ)) (k - 1)
  unfold unbalancedCharge cutCharge
  nlinarith

lemma charge_s1_large (HA : SimpleGraph A) (HB : SimpleGraph B)
    [DecidableRel HA.Adj] [DecidableRel HB.Adj] (M : Finset (A × B)) (r k : ℤ)
    (hk : 1 ≤ k) (hD : 2 * k + 2 ≤ M.card) (hr : (M.card : ℤ) + 3 ≤ r)
    (hq : HA.edgeFinset.card + (HB.edgeFinset.card : ℤ) ≤ r + M.card)
    (hA : ∀ a, (leftDegree M a : ℤ) ≤ k) (hB : ∀ b, (rightDegree M b : ℤ) ≤ k) :
    unbalancedCharge HA HB M 1 ≤ r * (M.card + 1) := by
  have hc := cutCharge_quadratic HA HB M k (by omega) hA hB
  have hw := mul_le_mul_of_nonneg_left (unbalancedCharge_le_add HA HB M 1 (by omega))
    (show 0 ≤ k by omega)
  apply ChargeArithmetic.unbalanced_large_s1 hk hD hr hq
  nlinarith only [hc, hw]

lemma charge_s1_near_large (HA : SimpleGraph A) (HB : SimpleGraph B)
    [DecidableRel HA.Adj] [DecidableRel HB.Adj] (M : Finset (A × B)) (r k : ℤ)
    (hk : 1 ≤ k) (hD : (M.card : ℤ) = 2 * k + 1) (hr : (M.card : ℤ) + 3 ≤ r)
    (hq : HA.edgeFinset.card + (HB.edgeFinset.card : ℤ) ≤ r + M.card)
    (hA : ∀ a, (leftDegree M a : ℤ) ≤ k) (hB : ∀ b, (rightDegree M b : ℤ) ≤ k) :
    unbalancedCharge HA HB M 1 ≤ r * (M.card + 1) := by
  have hc := cutCharge_pair_bound HA HB M k 1 (by omega) (by omega) le_rfl hA hB (by omega)
  have hw := unbalancedCharge_le_add HA HB M 1 (by omega)
  have heq : (M.card : ℤ) + 1 = 2 * k + 2 := by omega
  rw [heq]
  apply ChargeArithmetic.unbalanced_near_large_s1 hk (by omega)
    (by linarith : HA.edgeFinset.card + (HB.edgeFinset.card : ℤ) ≤ r + 2 * k + 1)
  nlinarith only [hc, hw]

lemma charge_s1_gap_left (HA : SimpleGraph A) (HB : SimpleGraph B)
    [DecidableRel HA.Adj] [DecidableRel HB.Adj] (M : Finset (A × B)) (u : A) (r k : ℤ)
    (hk : 2 ≤ k) (hu : (leftDegree M u : ℤ) = k) (hD : (M.card : ℤ) = 2 * k - 1)
    (hr : (M.card : ℤ) + 3 ≤ r)
    (hq : HA.edgeFinset.card + (HB.edgeFinset.card : ℤ) ≤ r + M.card)
    (hB : ∀ b, (rightDegree M b : ℤ) ≤ k - 1) :
    unbalancedCharge HA HB M 1 ≤ r * (M.card + 1) := by
  have hsum := missing_left_sum_erase M u k (k - 1) hu (by omega)
  have hpa := pairExcess_above_hub_le univ (fun a ↦ (leftDegree M a : ℤ)) k (k - 1) u
    (mem_univ _) hu (fun _ _ ↦ Nat.cast_nonneg _) hsum (by omega) (by omega)
  have hpb := pairExcess_le_add_two univ (fun b ↦ (rightDegree M b : ℤ)) (k - 1)
    (by omega) (fun b _ ↦ ⟨Nat.cast_nonneg _, hB b⟩) (by rw [missing_right_sum, hD]; omega)
  have hw := unbalancedCharge_one_le_pairs HA HB M k
  have heq : (M.card : ℤ) + 1 = 2 * k := by omega
  rw [heq]
  apply ChargeArithmetic.unbalanced_gap_left_s1 (by omega) (by omega)
    (by linarith : HA.edgeFinset.card + (HB.edgeFinset.card : ℤ) ≤ r + 2 * k - 1)
  linarith

lemma charge_s1_gap_right (HA : SimpleGraph A) (HB : SimpleGraph B)
    [DecidableRel HA.Adj] [DecidableRel HB.Adj] (M : Finset (A × B)) (v : B) (r k : ℤ)
    (hk : 2 ≤ k) (hv : (rightDegree M v : ℤ) = k) (hD : (M.card : ℤ) = 2 * k - 1)
    (hr : (M.card : ℤ) + 3 ≤ r)
    (hq : HA.edgeFinset.card + (HB.edgeFinset.card : ℤ) ≤ r + M.card)
    (hA : ∀ a, (leftDegree M a : ℤ) ≤ k) (hcap : (HB.degree v : ℤ) + k ≤ r - 2) :
    unbalancedCharge HA HB M 1 ≤ r * (M.card + 1) := by
  have hpa := pairExcess_le univ (fun a ↦ (leftDegree M a : ℤ)) k
    (by omega) (fun a _ ↦ ⟨Nat.cast_nonneg _, hA a⟩) (by rw [missing_left_sum, hD]; omega)
  have hmono := pairExcess_threshold_antitone univ (fun a ↦ (leftDegree M a : ℤ))
    (show k ≤ k + 1 by omega)
  have hca := graph_weighted_degree_le HA (fun a ↦ (leftDegree M a : ℤ)) (k + 1)
  have hsum := missing_right_sum_erase M v k (k - 1) hv (by omega)
  have hcb := graph_weighted_degree_hub_sum_le HB (fun b ↦ (rightDegree M b : ℤ))
    k (k - 1) (k - 1) v hv (fun _ _ ↦ Nat.cast_nonneg _) hsum le_rfl
  have heq : (M.card : ℤ) + 1 = 2 * k := by omega
  rw [heq]
  apply ChargeArithmetic.unbalanced_gap_right_s1 hk (by omega)
    (by linarith : HA.edgeFinset.card + (HB.edgeFinset.card : ℤ) ≤ r + 2 * k - 1)
    (show (HB.degree v : ℤ) ≤ r - k - 2 by omega)
  unfold unbalancedCharge cutCharge
  nlinarith

lemma charge_s1_dominant_left (HA : SimpleGraph A) (HB : SimpleGraph B)
    [DecidableRel HA.Adj] [DecidableRel HB.Adj] (M : Finset (A × B)) (u : A) (r k h : ℤ)
    (hh : 1 ≤ h) (hhk : h + 3 ≤ k) (hu : (leftDegree M u : ℤ) = k)
    (hD : (M.card : ℤ) = k + h) (hr : (M.card : ℤ) + 3 ≤ r)
    (hq : HA.edgeFinset.card + (HB.edgeFinset.card : ℤ) ≤ r + M.card)
    (hcap : (HA.degree u : ℤ) + k ≤ r + 1) :
    unbalancedCharge HA HB M 1 ≤ r * (M.card + 1) := by
  have hc := cutCharge_dominant_bound HA HB M u k h (by omega) hh hu hD
  have hp : (HA.degree u : ℤ) ≤ HA.edgeFinset.card := by exact_mod_cast HA.degree_le_card_edgeFinset u
  rw [hD]
  apply ChargeArithmetic.unbalanced_dominant_left_s1 hh hhk (by omega)
    (by linarith : HA.edgeFinset.card + (HB.edgeFinset.card : ℤ) ≤ r + k + h)
    (show (HA.degree u : ℤ) ≤ r + 1 - k by omega)
  unfold unbalancedCharge
  nlinarith only [hc, hp]

lemma charge_s1_dominant_right (HA : SimpleGraph A) (HB : SimpleGraph B)
    [DecidableRel HA.Adj] [DecidableRel HB.Adj] (M : Finset (A × B)) (v : B) (r k h : ℤ)
    (hh : 1 ≤ h) (hhk : h + 2 ≤ k) (hv : (rightDegree M v : ℤ) = k)
    (hD : (M.card : ℤ) = k + h) (hr : (M.card : ℤ) + 3 ≤ r)
    (hq : HA.edgeFinset.card + (HB.edgeFinset.card : ℤ) ≤ r + M.card)
    (hcap : (HB.degree v : ℤ) + k ≤ r - 2) :
    unbalancedCharge HA HB M 1 ≤ r * (M.card + 1) := by
  have hv' : (leftDegree (transpose M) v : ℤ) = k := by simpa [leftDegree_transpose] using hv
  have hpa := missing_right_pairExcess_zero (transpose M) v k h hv' (by simpa [card_transpose] using hD)
  simp only [rightDegree_transpose] at hpa
  have hca := graph_weighted_degree_le HA (fun a ↦ (leftDegree M a : ℤ)) (h + 2)
  rw [hpa] at hca
  have hsum := missing_right_sum_erase M v k h hv hD
  have hcb := graph_weighted_degree_hub_sum_le HB (fun b ↦ (rightDegree M b : ℤ))
    k h h v hv (fun _ _ ↦ Nat.cast_nonneg _) hsum le_rfl
  rw [hD]
  apply ChargeArithmetic.unbalanced_dominant_right_s1 hh hhk (by omega)
    (by linarith : HA.edgeFinset.card + (HB.edgeFinset.card : ℤ) ≤ r + k + h)
    (show (HB.degree v : ℤ) ≤ r - k - 2 by omega)
  unfold unbalancedCharge cutCharge
  nlinarith

lemma charge_s1_dominant_edge (HA : SimpleGraph A) (HB : SimpleGraph B)
    [DecidableRel HA.Adj] [DecidableRel HB.Adj] (M : Finset (A × B)) (u : A) (r k : ℤ)
    (hk : 3 ≤ k) (hu : (leftDegree M u : ℤ) = k) (hD : (M.card : ℤ) = 2 * k - 2)
    (hr : (M.card : ℤ) + 3 ≤ r)
    (hq : HA.edgeFinset.card + (HB.edgeFinset.card : ℤ) ≤ r + M.card) :
    unbalancedCharge HA HB M 1 ≤ r * (M.card + 1) := by
  have hp := missing_dominant_edge_pair_bound M u k hk hu hD
  have hw := unbalancedCharge_one_le_pairs HA HB M k
  have heq : (M.card : ℤ) + 1 = 2 * k - 1 := by omega
  rw [heq]
  apply ChargeArithmetic.unbalanced_dominant_edge_s1 (by omega) (by omega)
    (by linarith : HA.edgeFinset.card + (HB.edgeFinset.card : ℤ) ≤ r + 2 * k - 2)
  linarith

lemma charge_s1_double (HA : SimpleGraph A) (HB : SimpleGraph B)
    [DecidableRel HA.Adj] [DecidableRel HB.Adj] (M : Finset (A × B)) (u : A) (v : B) (r k : ℤ)
    (hk : 2 ≤ k) (hu : (leftDegree M u : ℤ) = k) (hv : (rightDegree M v : ℤ) = k)
    (hD : (M.card : ℤ) = 2 * k - 1) (hr : (M.card : ℤ) + 3 ≤ r)
    (hq : HA.edgeFinset.card + (HB.edgeFinset.card : ℤ) ≤ r + M.card)
    (hcapA : (HA.degree u : ℤ) + k ≤ r + 1) (hcapB : (HB.degree v : ℤ) + k ≤ r - 2) :
    unbalancedCharge HA HB M 1 ≤ r * (M.card + 1) := by
  have hp : (HA.degree u : ℤ) ≤ HA.edgeFinset.card := by exact_mod_cast HA.degree_le_card_edgeFinset u
  have hx0 : (0 : ℤ) ≤ HA.edgeFinset.card := Nat.cast_nonneg _
  have heq : (M.card : ℤ) + 1 = 2 * k := by omega
  rw [heq]
  by_cases hk2 : k = 2
  · have hc := cutCharge_double_two_bound HA HB M u v (hu.trans hk2) (hv.trans hk2) (by omega)
    unfold unbalancedCharge
    nlinarith
  by_cases hk3 : k = 3
  · have hc := cutCharge_double_bound HA HB M u v k hu hv hD
    rw [hk3] at hc ⊢
    norm_num at hc ⊢
    unfold unbalancedCharge
    nlinarith
  · have hc := cutCharge_double_bound HA HB M u v k hu hv hD
    apply ChargeArithmetic.unbalanced_double_s1 (by omega) (by omega)
      (by linarith : HA.edgeFinset.card + (HB.edgeFinset.card : ℤ) ≤ r + 2 * k - 1)
      (show (HA.degree u : ℤ) ≤ r + 1 - k by omega)
      (show (HB.degree v : ℤ) ≤ r - k - 2 by omega)
    unfold unbalancedCharge
    nlinarith only [hc, hp]

lemma charge_s1_equal (HA : SimpleGraph A) (HB : SimpleGraph B)
    [DecidableRel HA.Adj] [DecidableRel HB.Adj] (M : Finset (A × B)) (r k : ℤ)
    (hk : 1 ≤ k) (hD : (M.card : ℤ) = 2 * k) (hr : (M.card : ℤ) + 3 ≤ r)
    (hq : HA.edgeFinset.card + (HB.edgeFinset.card : ℤ) ≤ r + M.card)
    (hA : ∀ a, (leftDegree M a : ℤ) ≤ k) (hB : ∀ b, (rightDegree M b : ℤ) ≤ k) :
    unbalancedCharge HA HB M 1 ≤ r * (M.card + 1) := by
  by_cases hk3 : k = 3
  · have hD6 : (M.card : ℤ) = 6 := by omega
    by_cases hz : pairExcess univ (fun a ↦ (leftDegree M a : ℤ)) 5 = 0
    · have hp := pairExcess_le univ (fun b ↦ (rightDegree M b : ℤ)) 3 (by omega)
        (fun b _ ↦ ⟨Nat.cast_nonneg _, by have := hB b; omega⟩) (by rw [missing_right_sum, hD6]; omega)
      have hw := unbalancedCharge_one_le_pairs HA HB M 4
      norm_num at hw
      rw [hz] at hw
      rw [hD6]
      norm_num
      apply ChargeArithmetic.unbalanced_equal_s1 (k := 3) (by omega) (by omega)
        (by linarith : HA.edgeFinset.card + (HB.edgeFinset.card : ℤ) ≤ r + 6)
      linarith
    · have hp := asymmetric_three_coarse M hD6 (fun a ↦ by have := hA a; omega) hz
      have hw := unbalancedCharge_one_le_pairs HA HB M 3
      norm_num at hw
      rw [hD6]
      norm_num
      nlinarith
  · have hp : pairExcess univ (fun a ↦ (leftDegree M a : ℤ)) (k + 2) +
        pairExcess univ (fun b ↦ (rightDegree M b : ℤ)) k ≤ k := by
      by_cases hk4 : 4 ≤ k
      · exact asymmetric_pair_bound_large M k hk4 hD hA hB
      · exact asymmetric_pair_bound_small M k (by omega) (by omega) hD hA hB
    have hw := unbalancedCharge_one_le_pairs HA HB M (k + 1)
    have heqA : k + 1 + 1 = k + 2 := by ring
    have heqB : k + 1 - 1 = k := by ring
    rw [heqA, heqB] at hw
    rw [hD]
    apply ChargeArithmetic.unbalanced_equal_s1 (by omega) (by omega)
      (by linarith : HA.edgeFinset.card + (HB.edgeFinset.card : ℤ) ≤ r + 2 * k)
    linarith

/-- The complete sparse-cut charge theorem at imbalance one. -/
theorem unbalanced_sparse_charge_s1 (HA : SimpleGraph A) (HB : SimpleGraph B)
    [DecidableRel HA.Adj] [DecidableRel HB.Adj] (M : Finset (A × B)) (r : ℤ)
    (hr : (M.card : ℤ) + 3 ≤ r)
    (hq : HA.edgeFinset.card + (HB.edgeFinset.card : ℤ) ≤ r + M.card)
    (hcapA : ∀ a, (HA.degree a : ℤ) + leftDegree M a ≤ r + 1)
    (hcapB : ∀ b, (HB.degree b : ℤ) + rightDegree M b ≤ r - 2) :
    unbalancedCharge HA HB M 1 ≤ r * (M.card + 1) := by
  by_cases hM : M.Nonempty
  · by_cases hstarA : ∃ u, leftDegree M u = M.card
    · obtain ⟨u, hu⟩ := hstarA
      have h := unbalanced_charge_star_left HA HB M u r 1 le_rfl hu
        (by norm_num; exact hr) (by norm_num; exact hq)
        (by simpa [hu] using hcapA u) (fun b ↦ by have := hcapB b; omega)
      simpa using h
    by_cases hstarB : ∃ v, rightDegree M v = M.card
    · obtain ⟨v, hv⟩ := hstarB
      have h := unbalanced_charge_star_right HA HB M v r 1 le_rfl hv
        (by norm_num; exact hr) (by norm_num; exact hq) (by have := hcapB v; omega)
      simpa using h
    obtain ⟨k, hk, hA, hB, hmax⟩ := exists_max_degree M hM
    have hk' : (1 : ℤ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
    have hA' : ∀ a, (leftDegree M a : ℤ) ≤ k := fun a ↦ by exact_mod_cast hA a
    have hB' : ∀ b, (rightDegree M b : ℤ) ≤ k := fun b ↦ by exact_mod_cast hB b
    have hkD : (k : ℤ) < M.card := by
      rcases hmax with ⟨u, hu⟩ | ⟨v, hv⟩
      · have := leftDegree_le_card M u
        have : leftDegree M u ≠ M.card := fun h ↦ hstarA ⟨u, h⟩
        omega
      · have := rightDegree_le_card M v
        have : rightDegree M v ≠ M.card := fun h ↦ hstarB ⟨v, h⟩
        omega
    by_cases hlarge : 2 * (k : ℤ) + 2 ≤ M.card
    · exact charge_s1_large HA HB M r k hk' hlarge hr hq hA' hB'
    by_cases hnear : (M.card : ℤ) = 2 * k + 1
    · exact charge_s1_near_large HA HB M r k hk' hnear hr hq hA' hB'
    by_cases hequal : (M.card : ℤ) = 2 * k
    · exact charge_s1_equal HA HB M r k hk' hequal hr hq hA' hB'
    by_cases hgap : (M.card : ℤ) = 2 * k - 1
    · have hk2 : (2 : ℤ) ≤ k := by omega
      by_cases hu : ∃ u, leftDegree M u = k
      · obtain ⟨u, hu⟩ := hu
        have hu' : (leftDegree M u : ℤ) = k := by exact_mod_cast hu
        by_cases hv : ∃ v, rightDegree M v = k
        · obtain ⟨v, hv⟩ := hv
          have hv' : (rightDegree M v : ℤ) = k := by exact_mod_cast hv
          exact charge_s1_double HA HB M u v r k hk2 hu' hv' hgap hr hq
            (by simpa [hu] using hcapA u) (by simpa [hv] using hcapB v)
        · have hb : ∀ b, (rightDegree M b : ℤ) ≤ k - 1 := by
            intro b
            have := hB b
            have : rightDegree M b ≠ k := fun h ↦ hv ⟨b, h⟩
            omega
          exact charge_s1_gap_left HA HB M u r k hk2 hu' hgap hr hq hb
      · obtain ⟨v, hv⟩ := hmax.resolve_left hu
        exact charge_s1_gap_right HA HB M v r k hk2 (by exact_mod_cast hv) hgap hr hq hA'
          (by simpa [hv] using hcapB v)
    · let h : ℤ := M.card - k
      have hh : 1 ≤ h := by dsimp [h]; omega
      have hhk : h + 2 ≤ k := by dsimp [h]; omega
      have hD : (M.card : ℤ) = k + h := by dsimp [h]; ring
      by_cases hu : ∃ u, leftDegree M u = k
      · obtain ⟨u, hu⟩ := hu
        have hu' : (leftDegree M u : ℤ) = k := by exact_mod_cast hu
        by_cases hhk3 : h + 3 ≤ k
        · exact charge_s1_dominant_left HA HB M u r k h hh hhk3 hu' hD hr hq
            (by simpa [hu] using hcapA u)
        · have hD' : (M.card : ℤ) = 2 * k - 2 := by omega
          exact charge_s1_dominant_edge HA HB M u r k (by omega) hu' hD' hr hq
      · obtain ⟨v, hv⟩ := hmax.resolve_left hu
        exact charge_s1_dominant_right HA HB M v r k h hh hhk (by exact_mod_cast hv) hD hr hq
          (by simpa [hv] using hcapB v)
  · have hzero : M = ∅ := not_nonempty_iff_eq_empty.mp hM
    subst M
    simp only [card_empty, Nat.cast_zero, zero_add, add_zero] at hr hq ⊢
    simpa using unbalanced_charge_empty HA HB r 1 le_rfl (by norm_num; exact hr) (by simpa using hq)

/-- The full unbalanced sparse-cut charge inequality for every positive imbalance. -/
theorem unbalanced_sparse_charge (HA : SimpleGraph A) (HB : SimpleGraph B)
    [DecidableRel HA.Adj] [DecidableRel HB.Adj] (M : Finset (A × B)) (r s : ℤ)
    (hs : 1 ≤ s) (hr : (M.card : ℤ) + s ^ 2 + 2 ≤ r)
    (hq : HA.edgeFinset.card + (HB.edgeFinset.card : ℤ) ≤ r + M.card + s ^ 2 - 1)
    (hcapA : ∀ a, (HA.degree a : ℤ) + leftDegree M a ≤ r + s)
    (hcapB : ∀ b, (HB.degree b : ℤ) + rightDegree M b ≤ r - s - 1) :
    unbalancedCharge HA HB M s ≤ r * (M.card + s ^ 2) := by
  by_cases hs1 : s = 1
  · subst s
    norm_num at hr hq ⊢
    exact unbalanced_sparse_charge_s1 HA HB M r hr hq hcapA (fun b ↦ by have := hcapB b; omega)
  · exact unbalanced_sparse_charge_s2 HA HB M r s (by omega) hr hq hcapA hcapB

end Erdos1010
