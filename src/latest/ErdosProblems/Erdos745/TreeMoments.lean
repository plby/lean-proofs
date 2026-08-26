import ErdosProblems.Erdos745.ComponentLaw
import ErdosProblems.Erdos745.PairRatio
import ErdosProblems.Erdos745.ComponentPair
import ErdosProblems.Erdos745.VertexSetSums

/-!
# Exact tree-component moments
-/

open scoped BigOperators

namespace Erdos745

noncomputable section

attribute [local instance] Classical.propDecidable

/-- Exact mean number of tree components of a specified order. -/
def treeMean (lam : ℝ) (n k : ℕ) : ℝ :=
  (n.choose k : ℝ) * labelledTreeCount k * (edgeProbability lam n : ℝ) ^ (k - 1) *
    (1 - (edgeProbability lam n : ℝ)) ^ (n.choose 2 - (n - k).choose 2 - (k - 1))

/-- The probability mass of all tree shapes on one prescribed `k`-set. -/
def treeSetMass (lam : ℝ) (n k : ℕ) : ℝ :=
  (labelledTreeCount k : ℝ) * treeShapeWeight lam n k

theorem treeMean_eq_choose_mul (lam : ℝ) (n k : ℕ) :
    treeMean lam n k = (n.choose k : ℝ) * treeSetMass lam n k := by
  unfold treeMean treeSetMass treeShapeWeight
  ring

theorem probability_treeSetMass (lam : ℝ) (n : ℕ) (S : Finset (Fin n)) :
    probability lam n (fun G ↦ IsTreeComponentSet G S) = treeSetMass lam n S.card := by
  rw [probability_isTreeComponentSet, treeSetMass, treeShapeWeight, mul_assoc]

theorem treeSetMass_nonneg (lam : ℝ) (n k : ℕ) : 0 ≤ treeSetMass lam n k := by
  have hp := (edgeProbability lam n).property
  have hq : 0 ≤ 1 - (edgeProbability lam n : ℝ) := sub_nonneg.mpr hp.2
  unfold treeSetMass treeShapeWeight
  exact mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (pow_nonneg hp.1 _) (pow_nonneg hq _))

theorem expectation_treeComponentCount_singleton (lam : ℝ) (n k : ℕ) :
    expectation lam n (fun G ↦ (treeComponentCount G {k} : ℝ)) = treeMean lam n k := by
  simp_rw [treeComponentCount_singleton_eq]
  rw [expectation_card_filter]
  have hterm (S : Finset (Fin n)) (hS : S ∈ Finset.univ.powersetCard k) :
      probability lam n (fun G ↦ IsTreeComponentSet G S) =
      (labelledTreeCount k : ℝ) * (edgeProbability lam n : ℝ) ^ (k - 1) *
        (1 - (edgeProbability lam n : ℝ)) ^
          (n.choose 2 - (n - k).choose 2 - (k - 1)) := by
    rw [probability_isTreeComponentSet, (Finset.mem_powersetCard.mp hS).2]
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul,
    Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  unfold treeMean
  ring

theorem treeMean_nonneg (lam : ℝ) (n k : ℕ) : 0 ≤ treeMean lam n k := by
  rw [← expectation_treeComponentCount_singleton]
  exact expectation_nonneg fun _ ↦ Nat.cast_nonneg _

theorem sum_treeComponentSet_probabilities (lam : ℝ) (n k : ℕ) :
    (∑ S ∈ Finset.univ.powersetCard k,
      probability lam n (fun G ↦ IsTreeComponentSet G S)) = treeMean lam n k := by
  rw [← expectation_treeComponentCount_singleton]
  simp_rw [treeComponentCount_singleton_eq]
  exact (expectation_card_filter lam n (Finset.univ.powersetCard k)
    (fun S G ↦ IsTreeComponentSet G S)).symm

theorem expectation_treeComponentCount (lam : ℝ) (n : ℕ) (I : Finset ℕ) :
    expectation lam n (fun G ↦ (treeComponentCount G I : ℝ)) = ∑ k ∈ I, treeMean lam n k := by
  simp_rw [treeComponentCount_eq_window]
  rw [expectation_card_filter, sum_vertexWindow]
  simp_rw [sum_treeComponentSet_probabilities]

theorem critical_absence_pos {n : ℕ} (hn : 2 ≤ n) :
    0 < 1 - (edgeProbability 1 n : ℝ) := by
  rw [edgeProbability_one, coe_criticalEdgeProbability (by omega)]
  have hnR : (1 : ℝ) < n := by exact_mod_cast hn
  rw [sub_pos, div_lt_one (by positivity)]
  exact hnR

theorem critical_choose_pair_div_le {n k l : ℕ} (hn : 2 ≤ n) (hk : k ≤ n) :
    ((n - k).choose l : ℝ) / (1 - (edgeProbability 1 n : ℝ)) ^ (k * l) ≤ n.choose l := by
  rw [div_le_iff₀ (pow_pos (critical_absence_pos hn) _)]
  rw [edgeProbability_one, coe_criticalEdgeProbability (by omega)]
  exact critical_choose_pair_bound hn hk

theorem sum_distinct_treePairs_eq_disjoint (lam : ℝ) (n : ℕ)
    (S : Finset (Fin n)) (hS : S.Nonempty) (l : ℕ) :
    (∑ U ∈ Finset.univ.powersetCard l, if S ≠ U then
      probability lam n (fun G ↦ IsTreeComponentSet G S ∧ IsTreeComponentSet G U) else 0) =
    ∑ U ∈ (Finset.univ.powersetCard l).filter (Disjoint S),
      probability lam n (fun G ↦ IsTreeComponentSet G S ∧ IsTreeComponentSet G U) := by
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro U _
  by_cases hSU : Disjoint S U
  · have hne : S ≠ U := by
      intro h
      subst U
      obtain ⟨u, hu⟩ := hS
      exact Finset.disjoint_left.mp hSU hu hu
    rw [if_pos hne, if_pos hSU]
  · by_cases hne : S ≠ U
    · rw [if_pos hne, if_neg hSU, probability_two_treeComponents_eq_zero lam n hne hSU]
    · rw [if_neg hne, if_neg hSU]

/-- At criticality, summing over all possible disjoint partners of a fixed
component cancels the positive dependence of the shared absent cut. -/
theorem critical_treePair_row_le {n : ℕ} (hn : 2 ≤ n)
    (S : Finset (Fin n)) (hS : S.Nonempty) (l : ℕ) :
    (∑ U ∈ Finset.univ.powersetCard l, if S ≠ U then
      probability 1 n (fun G ↦ IsTreeComponentSet G S ∧ IsTreeComponentSet G U) else 0) ≤
      probability 1 n (fun G ↦ IsTreeComponentSet G S) * treeMean 1 n l := by
  rw [sum_distinct_treePairs_eq_disjoint 1 n S hS l]
  let pS := probability 1 n (fun G ↦ IsTreeComponentSet G S)
  let q := 1 - (edgeProbability 1 n : ℝ)
  have hq : 0 < q := critical_absence_pos hn
  have hterm (U : Finset (Fin n))
      (hU : U ∈ (Finset.univ.powersetCard l).filter (Disjoint S)) :
      probability 1 n (fun G ↦ IsTreeComponentSet G S ∧ IsTreeComponentSet G U) =
        pS * treeSetMass 1 n l / q ^ (S.card * l) := by
    obtain ⟨hcard, hSU⟩ := Finset.mem_filter.mp hU
    have hsize := (Finset.mem_powersetCard.mp hcard).2
    rw [probability_two_treeComponents_div 1 n hSU (ne_of_gt hq),
      probability_treeSetMass 1 n U, hsize]
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul,
    card_powersetCard_disjoint]
  have hk : S.card ≤ n := by simpa only [Fintype.card_fin] using Finset.card_le_univ S
  calc
    _ = (((n - S.card).choose l : ℝ) / q ^ (S.card * l)) *
        (pS * treeSetMass 1 n l) := by ring
    _ ≤ (n.choose l : ℝ) * (pS * treeSetMass 1 n l) :=
      mul_le_mul_of_nonneg_right (critical_choose_pair_div_le hn hk)
        (mul_nonneg (probability_nonneg _ _ _) (treeSetMass_nonneg _ _ _))
    _ = _ := by rw [treeMean_eq_choose_mul]; ring

theorem critical_treePair_window_row_le {n : ℕ} (hn : 2 ≤ n)
    (S : Finset (Fin n)) (hS : S.Nonempty) (I : Finset ℕ) :
    (∑ U ∈ vertexWindow n I, if S ≠ U then
      probability 1 n (fun G ↦ IsTreeComponentSet G S ∧ IsTreeComponentSet G U) else 0) ≤
      probability 1 n (fun G ↦ IsTreeComponentSet G S) * ∑ l ∈ I, treeMean 1 n l := by
  rw [sum_vertexWindow, Finset.mul_sum]
  exact Finset.sum_le_sum fun l _ ↦ critical_treePair_row_le hn S hS l

/-- Finite-window critical factorial moment bound, with no asymptotic premise. -/
theorem critical_treeCount_factorial_le {n : ℕ} (hn : 2 ≤ n)
    (I : Finset ℕ) (hI : ∀ k ∈ I, 0 < k) :
    expectation 1 n (fun G ↦ (treeComponentCount G I : ℝ) *
      ((treeComponentCount G I : ℝ) - 1)) ≤ (∑ k ∈ I, treeMean 1 n k) ^ 2 := by
  simp_rw [treeComponentCount_eq_window]
  rw [expectation_card_filter_factorial, sum_offDiag_eq]
  calc
    _ ≤ ∑ S ∈ vertexWindow n I,
        probability 1 n (fun G ↦ IsTreeComponentSet G S) * ∑ k ∈ I, treeMean 1 n k := by
      apply Finset.sum_le_sum
      intro S hS
      have hpos : 0 < S.card := hI _ (Finset.mem_filter.mp hS).2
      exact critical_treePair_window_row_le hn S (Finset.card_pos.mp hpos) I
    _ = (∑ S ∈ vertexWindow n I, probability 1 n (fun G ↦ IsTreeComponentSet G S)) *
        (∑ k ∈ I, treeMean 1 n k) := (Finset.sum_mul ..).symm
    _ = _ := by
      rw [sum_vertexWindow]
      simp_rw [sum_treeComponentSet_probabilities]
      ring

/-- A finite critical graph has two window-sized tree components except with
the explicit second-moment error. -/
theorem critical_treeCount_lt_two_le {n : ℕ} (hn : 2 ≤ n)
    (I : Finset ℕ) (hI : ∀ k ∈ I, 0 < k) (hm : 1 < ∑ k ∈ I, treeMean 1 n k) :
    probability 1 n (fun G ↦ treeComponentCount G I < 2) ≤
      (∑ k ∈ I, treeMean 1 n k) / ((∑ k ∈ I, treeMean 1 n k) - 1) ^ 2 := by
  have hm' : 1 < expectation 1 n (fun G ↦ (treeComponentCount G I : ℝ)) := by
    rw [expectation_treeComponentCount]
    exact hm
  have hf : expectation 1 n (fun G ↦ (treeComponentCount G I : ℝ) *
      ((treeComponentCount G I : ℝ) - 1)) ≤
      expectation 1 n (fun G ↦ (treeComponentCount G I : ℝ)) ^ 2 := by
    rw [expectation_treeComponentCount]
    exact critical_treeCount_factorial_le hn I hI
  simpa only [expectation_treeComponentCount] using
    probability_count_lt_two_le (fun G ↦ treeComponentCount G I) hm' hf

theorem critical_secondLargest_lt_le {n k : ℕ} (hn : 2 ≤ n) (hk : 0 < k)
    (I : Finset ℕ) (hI : ∀ j ∈ I, k ≤ j) (hm : 1 < ∑ j ∈ I, treeMean 1 n j) :
    probability 1 n (fun G ↦ secondLargestComponentOrder G < k) ≤
      (∑ j ∈ I, treeMean 1 n j) / ((∑ j ∈ I, treeMean 1 n j) - 1) ^ 2 := by
  calc
    _ ≤ probability 1 n (fun G ↦ treeComponentCount G I < 2) := by
      apply probability_mono
      intro G hG
      by_contra h
      have hlarge := le_secondLargestComponentOrder_of_two_trees G I hk hI (by omega)
      omega
    _ ≤ _ := critical_treeCount_lt_two_le hn I (fun j hj ↦ hk.trans_le (hI j hj)) hm

theorem second_moment_ratio_le {m : ℝ} (hm : 2 ≤ m) : m / (m - 1) ^ 2 ≤ 4 / m := by
  have hm0 : 0 < m := by linarith
  have hm1 : 0 < m - 1 := by linarith
  rw [div_le_div_iff₀ (sq_pos_of_pos hm1) hm0]
  nlinarith [sq_nonneg (m - 2)]

/-- Explicit lower probability bound for the second-largest critical component. -/
theorem critical_secondLargest_ge_probability {n k : ℕ} (hn : 2 ≤ n) (hk : 0 < k)
    (I : Finset ℕ) (hI : ∀ j ∈ I, k ≤ j) (hm : 2 ≤ ∑ j ∈ I, treeMean 1 n j) :
    1 - 4 / (∑ j ∈ I, treeMean 1 n j) ≤
      probability 1 n (fun G ↦ k ≤ secondLargestComponentOrder G) := by
  have hfail := (critical_secondLargest_lt_le hn hk I hI (by linarith)).trans
    (second_moment_ratio_le hm)
  have hnot := probability_not 1 n (fun G ↦ k ≤ secondLargestComponentOrder G)
  simp only [not_le] at hnot
  rw [hnot] at hfail
  linarith

end

end Erdos745
