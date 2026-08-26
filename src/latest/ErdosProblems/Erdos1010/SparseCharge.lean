import ErdosProblems.Erdos1010.GraphPairs
import ErdosProblems.Erdos1010.Bipartite
import ErdosProblems.Erdos1010.ChargeArithmetic

/-! # Charges from missing cross edges

`HA` and `HB` are the two internal graphs. `M` is the set of missing
cross edges. This module keeps the two vertex classes as separate types.
-/

open Finset

namespace Erdos1010

open Bipartite

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

def cutCharge (HA : SimpleGraph A) (HB : SimpleGraph B)
    [DecidableRel HA.Adj] [DecidableRel HB.Adj] (M : Finset (A × B)) : ℤ :=
  (∑ a, (HA.degree a : ℤ) * leftDegree M a) +
    ∑ b, (HB.degree b : ℤ) * rightDegree M b

lemma cutCharge_transpose (HA : SimpleGraph A) (HB : SimpleGraph B)
    [DecidableRel HA.Adj] [DecidableRel HB.Adj] (M : Finset (A × B)) :
    cutCharge HB HA (transpose M) = cutCharge HA HB M := by
  simp only [cutCharge, leftDegree_transpose, rightDegree_transpose, add_comm]

lemma cutCharge_empty (HA : SimpleGraph A) (HB : SimpleGraph B)
    [DecidableRel HA.Adj] [DecidableRel HB.Adj] : cutCharge HA HB ∅ = 0 := by
  simp [cutCharge, leftDegree, rightDegree]

lemma missing_left_sum (M : Finset (A × B)) :
    (∑ a, (leftDegree M a : ℤ)) = M.card := by
  exact_mod_cast sum_leftDegree_univ M

lemma missing_right_sum (M : Finset (A × B)) :
    (∑ b, (rightDegree M b : ℤ)) = M.card := by
  exact_mod_cast sum_rightDegree_univ M

lemma cutCharge_le_pairExcess (HA : SimpleGraph A) (HB : SimpleGraph B)
    [DecidableRel HA.Adj] [DecidableRel HB.Adj] (M : Finset (A × B)) (k : ℤ) :
    cutCharge HA HB M ≤ k * (HA.edgeFinset.card + (HB.edgeFinset.card : ℤ)) +
      pairExcess univ (fun a ↦ (leftDegree M a : ℤ)) k +
      pairExcess univ (fun b ↦ (rightDegree M b : ℤ)) k := by
  have hA := graph_weighted_degree_le HA (fun a ↦ (leftDegree M a : ℤ)) k
  have hB := graph_weighted_degree_le HB (fun b ↦ (rightDegree M b : ℤ)) k
  unfold cutCharge
  linarith

lemma missing_pairExcess_quadratic (M : Finset (A × B)) (k : ℤ)
    (hA : ∀ a, (leftDegree M a : ℤ) ≤ k) (hB : ∀ b, (rightDegree M b : ℤ) ≤ k) :
    k * (pairExcess univ (fun a ↦ (leftDegree M a : ℤ)) k +
      pairExcess univ (fun b ↦ (rightDegree M b : ℤ)) k) ≤
      (M.card : ℤ) * (M.card - 1) := by
  have hqa := pairExcess_quadratic_bound univ (fun a ↦ (leftDegree M a : ℤ)) k
    (fun a _ ↦ ⟨Nat.cast_nonneg _, hA a⟩)
  have hqb := pairExcess_quadratic_bound univ (fun b ↦ (rightDegree M b : ℤ)) k
    (fun b _ ↦ ⟨Nat.cast_nonneg _, hB b⟩)
  have hsqa : (M.card : ℤ) ≤ ∑ a, (leftDegree M a : ℤ) ^ 2 := by
    rw [← missing_left_sum M]
    exact sum_le_sum fun a _ ↦ Int.le_self_sq _
  have hsqb : (M.card : ℤ) ≤ ∑ b, (rightDegree M b : ℤ) ^ 2 := by
    rw [← missing_right_sum M]
    exact sum_le_sum fun b _ ↦ Int.le_self_sq _
  rw [missing_left_sum] at hqa
  rw [missing_right_sum] at hqb
  nlinarith

lemma cutCharge_quadratic (HA : SimpleGraph A) (HB : SimpleGraph B)
    [DecidableRel HA.Adj] [DecidableRel HB.Adj] (M : Finset (A × B)) (k : ℤ)
    (hk : 0 ≤ k) (hA : ∀ a, (leftDegree M a : ℤ) ≤ k)
    (hB : ∀ b, (rightDegree M b : ℤ) ≤ k) :
    k * cutCharge HA HB M ≤ k ^ 2 * (HA.edgeFinset.card + (HB.edgeFinset.card : ℤ)) +
      (M.card : ℤ) * (M.card - 1) := by
  have hp := missing_pairExcess_quadratic M k hA hB
  have hc := mul_le_mul_of_nonneg_left (cutCharge_le_pairExcess HA HB M k) hk
  nlinarith

lemma cutCharge_pair_bound (HA : SimpleGraph A) (HB : SimpleGraph B)
    [DecidableRel HA.Adj] [DecidableRel HB.Adj] (M : Finset (A × B)) (k e : ℤ)
    (hk : 0 ≤ k) (he : 0 ≤ e) (he1 : e ≤ 1)
    (hA : ∀ a, (leftDegree M a : ℤ) ≤ k) (hB : ∀ b, (rightDegree M b : ℤ) ≤ k)
    (hD : (M.card : ℤ) ≤ 2 * k + e) :
    cutCharge HA HB M ≤ k * (HA.edgeFinset.card + (HB.edgeFinset.card : ℤ)) +
      2 * k + 4 * e := by
  have hpa := pairExcess_bound univ (fun a ↦ (leftDegree M a : ℤ)) k e hk he he1
    (fun a _ ↦ ⟨Nat.cast_nonneg _, hA a⟩) (by rwa [missing_left_sum])
  have hpb := pairExcess_bound univ (fun b ↦ (rightDegree M b : ℤ)) k e hk he he1
    (fun b _ ↦ ⟨Nat.cast_nonneg _, hB b⟩) (by rwa [missing_right_sum])
  have hc := cutCharge_le_pairExcess HA HB M k
  linarith

/-- The large-defect case of the balanced sparse-cut lemma. -/
lemma balanced_charge_large (HA : SimpleGraph A) (HB : SimpleGraph B)
    [DecidableRel HA.Adj] [DecidableRel HB.Adj] (M : Finset (A × B)) (r k : ℤ)
    (hk : 1 ≤ k) (hD : 2 * k + 1 ≤ M.card) (hr : (M.card : ℤ) + 2 ≤ r)
    (hq : HA.edgeFinset.card + (HB.edgeFinset.card : ℤ) ≤ r + M.card - 1)
    (hA : ∀ a, (leftDegree M a : ℤ) ≤ k) (hB : ∀ b, (rightDegree M b : ℤ) ≤ k) :
    cutCharge HA HB M ≤ r * M.card := by
  exact ChargeArithmetic.balanced_large hk hD hr hq
    (cutCharge_quadratic HA HB M k (by omega) hA hB)

/-- The twice-maximum-degree case of the balanced sparse-cut lemma. -/
lemma balanced_charge_equal (HA : SimpleGraph A) (HB : SimpleGraph B)
    [DecidableRel HA.Adj] [DecidableRel HB.Adj] (M : Finset (A × B)) (r k : ℤ)
    (hk : 0 ≤ k) (hD : (M.card : ℤ) = 2 * k) (hr : (M.card : ℤ) + 2 ≤ r)
    (hq : HA.edgeFinset.card + (HB.edgeFinset.card : ℤ) ≤ r + M.card - 1)
    (hA : ∀ a, (leftDegree M a : ℤ) ≤ k) (hB : ∀ b, (rightDegree M b : ℤ) ≤ k) :
    cutCharge HA HB M ≤ r * M.card := by
  have hc := cutCharge_pair_bound HA HB M k 0 hk le_rfl (by omega) hA hB (by omega)
  rw [hD] at hr hq ⊢
  apply ChargeArithmetic.balanced_equal hk hr hq
  simpa using hc

lemma cutCharge_star_eq (HA : SimpleGraph A) (HB : SimpleGraph B)
    [DecidableRel HA.Adj] [DecidableRel HB.Adj] (M : Finset (A × B)) (u : A)
    (hu : leftDegree M u = M.card) :
    cutCharge HA HB M = (M.card : ℤ) * HA.degree u +
      ∑ b ∈ univ.filter (fun b ↦ (u, b) ∈ M), (HB.degree b : ℤ) := by
  unfold cutCharge
  simp_rw [leftDegree_of_star M u _ hu, rightDegree_of_star M u _ hu]
  simp [Nat.cast_ite, mul_ite, sum_filter, mul_comm]

lemma cutCharge_star_le_edges_pairs (HA : SimpleGraph A) (HB : SimpleGraph B)
    [DecidableRel HA.Adj] [DecidableRel HB.Adj] (M : Finset (A × B)) (u : A)
    (hu : leftDegree M u = M.card) :
    cutCharge HA HB M ≤ (M.card : ℤ) * HA.degree u + HB.edgeFinset.card +
      (M.card.choose 2 : ℤ) := by
  rw [cutCharge_star_eq HA HB M u hu]
  have hb := degree_sum_subset_le_edges_add_pairs HB (univ.filter fun b ↦ (u, b) ∈ M)
  rw [card_right_neighbors, hu] at hb
  linarith

lemma cutCharge_star_le_twice_edges (HA : SimpleGraph A) (HB : SimpleGraph B)
    [DecidableRel HA.Adj] [DecidableRel HB.Adj] (M : Finset (A × B)) (u : A)
    (hu : leftDegree M u = M.card) :
    cutCharge HA HB M ≤ (M.card : ℤ) * HA.degree u + 2 * HB.edgeFinset.card := by
  rw [cutCharge_star_eq HA HB M u hu]
  have hb := degree_sum_subset_le_twice_edges HB (univ.filter fun b ↦ (u, b) ∈ M)
  linarith

/-- Every star missing-edge graph satisfies the balanced charge estimate. -/
lemma balanced_charge_star (HA : SimpleGraph A) (HB : SimpleGraph B)
    [DecidableRel HA.Adj] [DecidableRel HB.Adj] (M : Finset (A × B)) (u : A) (r : ℤ)
    (hu : leftDegree M u = M.card)
    (hcap : (HA.degree u : ℤ) + M.card ≤ r)
    (hq : HA.edgeFinset.card + (HB.edgeFinset.card : ℤ) ≤ r + M.card - 1) :
    cutCharge HA HB M ≤ r * M.card := by
  by_cases hzero : M.card = 0
  · have hM := card_eq_zero.mp hzero
    subst M
    simp [cutCharge_empty]
  have hp : (HA.degree u : ℤ) ≤ HA.edgeFinset.card := by
    exact_mod_cast HA.degree_le_card_edgeFinset u
  have hleaf := cutCharge_star_le_edges_pairs HA HB M u hu
  have hdouble := cutCharge_star_le_twice_edges HA HB M u hu
  by_cases hD : M.card < 4
  · interval_cases hdc : M.card <;> norm_num [hdc] at hleaf hdouble hcap hq ⊢ <;> omega
  · have hD' : (4 : ℤ) ≤ M.card := by exact_mod_cast (show 4 ≤ M.card by omega)
    apply ChargeArithmetic.balanced_star_large hD' hq (show (HA.degree u : ℤ) ≤ r - M.card by omega)
    nlinarith

lemma cutCharge_gap_single_bound (HA : SimpleGraph A) (HB : SimpleGraph B)
    [DecidableRel HA.Adj] [DecidableRel HB.Adj] (M : Finset (A × B)) (u : A) (k : ℤ)
    (hk : 2 ≤ k) (hu : (leftDegree M u : ℤ) = k) (hD : (M.card : ℤ) = 2 * k - 1)
    (hB : ∀ b, (rightDegree M b : ℤ) ≤ k - 1) :
    cutCharge HA HB M ≤ (k - 1) * (HA.edgeFinset.card + (HB.edgeFinset.card : ℤ)) +
      HA.degree u + 2 * k := by
  have hs : (∑ a ∈ univ.erase u, (leftDegree M a : ℤ)) = k - 1 := by
    have hsum := sum_erase_add (univ : Finset A) (fun a ↦ (leftDegree M a : ℤ)) (mem_univ u)
    rw [missing_left_sum, hu, hD] at hsum
    omega
  have hca := graph_weighted_degree_hub_sum_le HA (fun a ↦ (leftDegree M a : ℤ))
    k (k - 1) (k - 1) u hu (fun _ _ ↦ Nat.cast_nonneg _) hs le_rfl
  have hpb := pairExcess_le_add_two univ (fun b ↦ (rightDegree M b : ℤ)) (k - 1)
    (by omega) (fun b _ ↦ ⟨Nat.cast_nonneg _, hB b⟩) (by rw [missing_right_sum, hD]; omega)
  have hcb := graph_weighted_degree_le HB (fun b ↦ (rightDegree M b : ℤ)) (k - 1)
  unfold cutCharge
  nlinarith

/-- The one-sided maximum-degree case with `D = 2*k-1`. -/
lemma balanced_charge_gap_single (HA : SimpleGraph A) (HB : SimpleGraph B)
    [DecidableRel HA.Adj] [DecidableRel HB.Adj] (M : Finset (A × B)) (u : A) (r k : ℤ)
    (hk : 2 ≤ k) (hu : (leftDegree M u : ℤ) = k) (hD : (M.card : ℤ) = 2 * k - 1)
    (hr : (M.card : ℤ) + 2 ≤ r)
    (hq : HA.edgeFinset.card + (HB.edgeFinset.card : ℤ) ≤ r + M.card - 1)
    (hcap : (HA.degree u : ℤ) + k ≤ r) (hB : ∀ b, (rightDegree M b : ℤ) ≤ k - 1) :
    cutCharge HA HB M ≤ r * M.card := by
  have hc := cutCharge_gap_single_bound HA HB M u k hk hu hD hB
  rw [hD] at hr hq ⊢
  apply ChargeArithmetic.balanced_gap_single
    (q := HA.edgeFinset.card + (HB.edgeFinset.card : ℤ)) hk (by omega) (by linarith)
    (show (HA.degree u : ℤ) ≤ r - k by omega)
  linarith

lemma missing_right_pairExcess_residual (M : Finset (A × B)) (u : A) (k h : ℤ)
    (hk : 1 ≤ k) (hh : 1 ≤ h) (hu : (leftDegree M u : ℤ) = k)
    (hD : (M.card : ℤ) = k + h) :
    pairExcess univ (fun b ↦ (rightDegree M b : ℤ)) (h + 1) ≤ k - 1 := by
  let e : B → ℤ := fun b ↦ if (u, b) ∈ M then 1 else 0
  let g : B → ℤ := fun b ↦ rightDegree (eraseLeft M u) b
  have he : ∀ b ∈ (univ : Finset B), 0 ≤ e b ∧ e b ≤ 1 := by
    intro b hb
    dsimp [e]
    split_ifs <;> omega
  have hes : (∑ b, e b) = k := by
    calc
      _ = ∑ _b ∈ univ.filter (fun b ↦ (u, b) ∈ M), (1 : ℤ) := by rw [sum_filter]
      _ = ((univ.filter fun b ↦ (u, b) ∈ M).card : ℤ) := by simp
      _ = k := by rw [card_right_neighbors, hu]
  have hgs : (∑ b, g b) = h := by
    dsimp [g]
    rw [missing_right_sum]
    have hd : (leftDegree M u : ℤ) + (eraseLeft M u).card = M.card := by
      exact_mod_cast leftDegree_add_card_eraseLeft M u
    omega
  have hz : (fun b ↦ e b + g b) = (fun b ↦ (rightDegree M b : ℤ)) := by
    funext b
    dsimp [e, g]
    have hd := rightDegree_eraseLeft M u b
    exact_mod_cast hd.symm
  have hp := pairExcess_unit_residual univ e g k h he (fun _ _ ↦ Nat.cast_nonneg _) hes hgs hk hh
  rwa [hz] at hp

lemma cutCharge_dominant_bound (HA : SimpleGraph A) (HB : SimpleGraph B)
    [DecidableRel HA.Adj] [DecidableRel HB.Adj] (M : Finset (A × B)) (u : A) (k h : ℤ)
    (hk : 1 ≤ k) (hh : 1 ≤ h) (hu : (leftDegree M u : ℤ) = k)
    (hD : (M.card : ℤ) = k + h) :
    cutCharge HA HB M ≤ (h + 1) * (HA.edgeFinset.card + (HB.edgeFinset.card : ℤ)) +
      (k - h - 1) * HA.degree u + h + k - 1 := by
  have hs : (∑ a ∈ univ.erase u, (leftDegree M a : ℤ)) = h := by
    have hsum := sum_erase_add (univ : Finset A) (fun a ↦ (leftDegree M a : ℤ)) (mem_univ u)
    rw [missing_left_sum, hu, hD] at hsum
    omega
  have hca := graph_weighted_degree_hub_sum_le HA (fun a ↦ (leftDegree M a : ℤ))
    k (h + 1) h u hu (fun _ _ ↦ Nat.cast_nonneg _) hs (by omega)
  have hpb := missing_right_pairExcess_residual M u k h hk hh hu hD
  have hcb := graph_weighted_degree_le HB (fun b ↦ (rightDegree M b : ℤ)) (h + 1)
  unfold cutCharge
  nlinarith

lemma balanced_charge_dominant (HA : SimpleGraph A) (HB : SimpleGraph B)
    [DecidableRel HA.Adj] [DecidableRel HB.Adj] (M : Finset (A × B)) (u : A) (r k h : ℤ)
    (hk : 1 ≤ k) (hh : 1 ≤ h) (hhk : h ≤ k - 2) (hu : (leftDegree M u : ℤ) = k)
    (hD : (M.card : ℤ) = k + h) (hr : (M.card : ℤ) + 2 ≤ r)
    (hq : HA.edgeFinset.card + (HB.edgeFinset.card : ℤ) ≤ r + M.card - 1)
    (hcap : (HA.degree u : ℤ) + k ≤ r) : cutCharge HA HB M ≤ r * M.card := by
  have hc := cutCharge_dominant_bound HA HB M u k h hk hh hu hD
  have hmul := mul_le_mul_of_nonneg_left (show (HA.degree u : ℤ) ≤ r - k by omega)
    (show 0 ≤ k - h - 1 by omega)
  rw [hD] at hr hq ⊢
  apply ChargeArithmetic.balanced_dominant
    (q := HA.edgeFinset.card + (HB.edgeFinset.card : ℤ)) hk hh hhk hr (by linarith)
  linarith

lemma missing_left_sum_erase (M : Finset (A × B)) (u : A) (k h : ℤ)
    (hu : (leftDegree M u : ℤ) = k) (hD : (M.card : ℤ) = k + h) :
    (∑ a ∈ univ.erase u, (leftDegree M a : ℤ)) = h := by
  have hs := sum_erase_add (univ : Finset A) (fun a ↦ (leftDegree M a : ℤ)) (mem_univ u)
  rw [missing_left_sum, hu, hD] at hs
  omega

lemma missing_right_sum_erase (M : Finset (A × B)) (v : B) (k h : ℤ)
    (hv : (rightDegree M v : ℤ) = k) (hD : (M.card : ℤ) = k + h) :
    (∑ b ∈ univ.erase v, (rightDegree M b : ℤ)) = h := by
  have hs := sum_erase_add (univ : Finset B) (fun b ↦ (rightDegree M b : ℤ)) (mem_univ v)
  rw [missing_right_sum, hv, hD] at hs
  omega

lemma cutCharge_double_bound (HA : SimpleGraph A) (HB : SimpleGraph B)
    [DecidableRel HA.Adj] [DecidableRel HB.Adj] (M : Finset (A × B)) (u : A) (v : B) (k : ℤ)
    (hu : (leftDegree M u : ℤ) = k) (hv : (rightDegree M v : ℤ) = k)
    (hD : (M.card : ℤ) = 2 * k - 1) :
    cutCharge HA HB M ≤ 2 * (HA.edgeFinset.card + (HB.edgeFinset.card : ℤ)) +
      (k - 2) * (HA.degree u + (HB.degree v : ℤ)) + 2 * k - 2 := by
  have hadd : leftDegree M u + rightDegree M v = M.card + 1 := by omega
  have hA : ∀ a, a ≠ u → 0 ≤ (leftDegree M a : ℤ) ∧ (leftDegree M a : ℤ) ≤ 1 := by
    intro a ha
    exact ⟨Nat.cast_nonneg _, by exact_mod_cast double_hubs_left_le_one M u v hadd a ha⟩
  have hB : ∀ b, b ≠ v → 0 ≤ (rightDegree M b : ℤ) ∧ (rightDegree M b : ℤ) ≤ 1 := by
    intro b hb
    exact ⟨Nat.cast_nonneg _, by exact_mod_cast double_hubs_right_le_one M u v hadd b hb⟩
  have hsa := missing_left_sum_erase M u k (k - 1) hu (by omega)
  have hsb := missing_right_sum_erase M v k (k - 1) hv (by omega)
  have hca := graph_weighted_degree_hub_unit_le HA (fun a ↦ (leftDegree M a : ℤ))
    k 2 (k - 1) u hu le_rfl hA hsa
  have hcb := graph_weighted_degree_hub_unit_le HB (fun b ↦ (rightDegree M b : ℤ))
    k 2 (k - 1) v hv le_rfl hB hsb
  unfold cutCharge
  nlinarith

lemma cutCharge_double_two_bound (HA : SimpleGraph A) (HB : SimpleGraph B)
    [DecidableRel HA.Adj] [DecidableRel HB.Adj] (M : Finset (A × B)) (u : A) (v : B)
    (hu : (leftDegree M u : ℤ) = 2) (hv : (rightDegree M v : ℤ) = 2)
    (hD : (M.card : ℤ) = 3) :
    cutCharge HA HB M ≤ HA.edgeFinset.card + (HB.edgeFinset.card : ℤ) +
      HA.degree u + HB.degree v + 2 := by
  have hsa := missing_left_sum_erase M u 2 1 hu (by omega)
  have hsb := missing_right_sum_erase M v 2 1 hv (by omega)
  have hca := graph_weighted_degree_hub_sum_le HA (fun a ↦ (leftDegree M a : ℤ))
    2 1 1 u hu (fun _ _ ↦ Nat.cast_nonneg _) hsa le_rfl
  have hcb := graph_weighted_degree_hub_sum_le HB (fun b ↦ (rightDegree M b : ℤ))
    2 1 1 v hv (fun _ _ ↦ Nat.cast_nonneg _) hsb le_rfl
  unfold cutCharge
  linarith

lemma balanced_charge_double (HA : SimpleGraph A) (HB : SimpleGraph B)
    [DecidableRel HA.Adj] [DecidableRel HB.Adj] (M : Finset (A × B)) (u : A) (v : B) (r k : ℤ)
    (hk : 2 ≤ k) (hu : (leftDegree M u : ℤ) = k) (hv : (rightDegree M v : ℤ) = k)
    (hD : (M.card : ℤ) = 2 * k - 1) (hr : (M.card : ℤ) + 2 ≤ r)
    (hq : HA.edgeFinset.card + (HB.edgeFinset.card : ℤ) ≤ r + M.card - 1)
    (hcapA : (HA.degree u : ℤ) + k ≤ r) (hcapB : (HB.degree v : ℤ) + k ≤ r) :
    cutCharge HA HB M ≤ r * M.card := by
  by_cases hk2 : k = 2
  · have hD3 : (M.card : ℤ) = 3 := by omega
    have hc := cutCharge_double_two_bound HA HB M u v (hu.trans hk2) (hv.trans hk2) hD3
    rw [hD3]
    exact ChargeArithmetic.balanced_gap_double_two (by linarith :
      HA.edgeFinset.card + (HB.edgeFinset.card : ℤ) ≤ r + 2)
      (by omega : (HA.degree u : ℤ) ≤ r - 2) (by omega : (HB.degree v : ℤ) ≤ r - 2) hc
  · have hc := cutCharge_double_bound HA HB M u v k hu hv hD
    rw [hD]
    exact ChargeArithmetic.balanced_gap_double (by omega) (by omega)
      (by linarith : HA.edgeFinset.card + (HB.edgeFinset.card : ℤ) ≤ r + 2 * k - 2)
      (by omega : (HA.degree u : ℤ) + HB.degree v ≤ 2 * (r - k)) hc

/-- Exhaustion of the balanced charge cases when a maximum hub lies on the left. -/
lemma balanced_charge_of_left_max (HA : SimpleGraph A) (HB : SimpleGraph B)
    [DecidableRel HA.Adj] [DecidableRel HB.Adj] (M : Finset (A × B)) (u : A) (r k : ℤ)
    (hk : 1 ≤ k) (hu : (leftDegree M u : ℤ) = k)
    (hA : ∀ a, (leftDegree M a : ℤ) ≤ k) (hB : ∀ b, (rightDegree M b : ℤ) ≤ k)
    (hr : (M.card : ℤ) + 2 ≤ r)
    (hq : HA.edgeFinset.card + (HB.edgeFinset.card : ℤ) ≤ r + M.card - 1)
    (hcapA : ∀ a, (HA.degree a : ℤ) + leftDegree M a ≤ r)
    (hcapB : ∀ b, (HB.degree b : ℤ) + rightDegree M b ≤ r) :
    cutCharge HA HB M ≤ r * M.card := by
  have hkD : k ≤ (M.card : ℤ) := by
    rw [← hu]
    exact_mod_cast leftDegree_le_card M u
  by_cases hstar : (M.card : ℤ) = k
  · have hus : leftDegree M u = M.card := by omega
    exact balanced_charge_star HA HB M u r hus (by simpa [← hus] using hcapA u) hq
  by_cases hlarge : 2 * k + 1 ≤ M.card
  · exact balanced_charge_large HA HB M r k hk hlarge hr hq hA hB
  by_cases hequal : (M.card : ℤ) = 2 * k
  · exact balanced_charge_equal HA HB M r k (by omega) hequal hr hq hA hB
  by_cases hgap : (M.card : ℤ) = 2 * k - 1
  · have hk2 : 2 ≤ k := by omega
    by_cases hv : ∃ v, (rightDegree M v : ℤ) = k
    · obtain ⟨v, hv⟩ := hv
      exact balanced_charge_double HA HB M u v r k hk2 hu hv hgap hr hq
        (by simpa [hu] using hcapA u) (by simpa [hv] using hcapB v)
    · have hB' : ∀ b, (rightDegree M b : ℤ) ≤ k - 1 := by
        intro b
        have hb := hB b
        have hn : (rightDegree M b : ℤ) ≠ k := fun h ↦ hv ⟨b, h⟩
        omega
      exact balanced_charge_gap_single HA HB M u r k hk2 hu hgap hr hq
        (by simpa [hu] using hcapA u) hB'
  · exact balanced_charge_dominant HA HB M u r k (M.card - k) hk (by omega) (by omega)
      hu (by omega) hr hq (by simpa [hu] using hcapA u)

/-- The full balanced sparse-cut charge lemma, without assumptions on class sizes. -/
theorem balanced_sparse_charge (HA : SimpleGraph A) (HB : SimpleGraph B)
    [DecidableRel HA.Adj] [DecidableRel HB.Adj] (M : Finset (A × B)) (r : ℤ)
    (hr : (M.card : ℤ) + 2 ≤ r)
    (hq : HA.edgeFinset.card + (HB.edgeFinset.card : ℤ) ≤ r + M.card - 1)
    (hcapA : ∀ a, (HA.degree a : ℤ) + leftDegree M a ≤ r)
    (hcapB : ∀ b, (HB.degree b : ℤ) + rightDegree M b ≤ r) :
    cutCharge HA HB M ≤ r * M.card := by
  by_cases hM : M.Nonempty
  · obtain ⟨k, hk, hA, hB, hmax⟩ := exists_max_degree M hM
    have hk' : (1 : ℤ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
    have hA' : ∀ a, (leftDegree M a : ℤ) ≤ k := fun a ↦ by exact_mod_cast hA a
    have hB' : ∀ b, (rightDegree M b : ℤ) ≤ k := fun b ↦ by exact_mod_cast hB b
    rcases hmax with ⟨u, hu⟩ | ⟨v, hv⟩
    · exact balanced_charge_of_left_max HA HB M u r k hk' (by exact_mod_cast hu)
        hA' hB' hr hq hcapA hcapB
    · have h := balanced_charge_of_left_max HB HA (transpose M) v r k hk'
        (by simpa [leftDegree_transpose] using (show (rightDegree M v : ℤ) = k by exact_mod_cast hv))
        (fun b ↦ by simpa [leftDegree_transpose] using hB' b)
        (fun a ↦ by simpa [rightDegree_transpose] using hA' a)
        (by simpa [card_transpose] using hr)
        (by simpa [card_transpose, add_comm] using hq)
        (fun b ↦ by simpa [leftDegree_transpose] using hcapB b)
        (fun a ↦ by simpa [rightDegree_transpose] using hcapA a)
      simpa [cutCharge_transpose, card_transpose] using h
  · have hzero : M = ∅ := not_nonempty_iff_eq_empty.mp hM
    subst M
    simp [cutCharge_empty]

end Erdos1010
