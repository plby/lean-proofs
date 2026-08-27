import ErdosProblems.Erdos745.TreeMoments

/-! # Tree-component second moments at an arbitrary edge density -/

open scoped BigOperators

namespace Erdos745

noncomputable section

attribute [local instance] Classical.propDecidable

theorem treePair_row_le {lam : ℝ} {n k : ℕ}
    (hq : 0 < 1 - (edgeProbability lam n : ℝ))
    (S : Finset (Fin n)) (hS : S.Nonempty) (hSk : S.card = k) :
    (∑ U ∈ Finset.univ.powersetCard k, if S ≠ U then
      probability lam n (fun G ↦ IsTreeComponentSet G S ∧ IsTreeComponentSet G U) else 0) ≤
      probability lam n (fun G ↦ IsTreeComponentSet G S) * treeMean lam n k /
        (1 - (edgeProbability lam n : ℝ)) ^ (k * k) := by
  rw [sum_distinct_treePairs_eq_disjoint lam n S hS k]
  let pS := probability lam n (fun G ↦ IsTreeComponentSet G S)
  let q := 1 - (edgeProbability lam n : ℝ)
  have hterm (U : Finset (Fin n))
      (hU : U ∈ (Finset.univ.powersetCard k).filter (Disjoint S)) :
      probability lam n (fun G ↦ IsTreeComponentSet G S ∧ IsTreeComponentSet G U) =
        pS * treeSetMass lam n k / q ^ (k * k) := by
    obtain ⟨hcard, hSU⟩ := Finset.mem_filter.mp hU
    rw [probability_two_treeComponents_div lam n hSU (ne_of_gt hq),
      probability_treeSetMass lam n U, (Finset.mem_powersetCard.mp hcard).2, hSk]
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul,
    card_powersetCard_disjoint, hSk]
  calc
    _ ≤ (n.choose k : ℝ) * (pS * treeSetMass lam n k / q ^ (k * k)) := by
      apply mul_le_mul_of_nonneg_right _
        (div_nonneg (mul_nonneg (probability_nonneg _ _ _) (treeSetMass_nonneg _ _ _))
          (pow_nonneg hq.le _))
      exact_mod_cast Nat.choose_le_choose k (Nat.sub_le n k)
    _ = _ := by rw [treeMean_eq_choose_mul]; ring

theorem treeCount_factorial_le {lam : ℝ} {n k : ℕ} (hk : 0 < k)
    (hq : 0 < 1 - (edgeProbability lam n : ℝ)) :
    expectation lam n (fun G ↦ (treeComponentCount G {k} : ℝ) *
      ((treeComponentCount G {k} : ℝ) - 1)) ≤
        (treeMean lam n k) ^ 2 / (1 - (edgeProbability lam n : ℝ)) ^ (k * k) := by
  simp_rw [treeComponentCount_singleton_eq]
  rw [expectation_card_filter_factorial, sum_offDiag_eq]
  calc
    _ ≤ ∑ S ∈ Finset.univ.powersetCard k,
        probability lam n (fun G ↦ IsTreeComponentSet G S) * treeMean lam n k /
          (1 - (edgeProbability lam n : ℝ)) ^ (k * k) := by
      apply Finset.sum_le_sum
      intro S hS
      have hSk := (Finset.mem_powersetCard.mp hS).2
      exact treePair_row_le hq S (Finset.card_pos.mp (hSk ▸ hk)) hSk
    _ = _ := by
      rw [← Finset.sum_div, ← Finset.sum_mul, sum_treeComponentSet_probabilities]
      ring

theorem second_moment_error_bound {m R : ℝ} (hm : 2 ≤ m) (hR : 1 ≤ R) :
    (m + (R - 1) * m ^ 2) / (m - 1) ^ 2 ≤ 4 / m + 4 * (R - 1) := by
  have hd : 0 < (m - 1) ^ 2 := sq_pos_of_pos (by linarith)
  have hratio : m ^ 2 / (m - 1) ^ 2 ≤ 4 := by
    rw [div_le_iff₀ hd]
    nlinarith [sq_nonneg (m - 2)]
  calc
    _ = m / (m - 1) ^ 2 + (R - 1) * (m ^ 2 / (m - 1) ^ 2) := by ring
    _ ≤ 4 / m + (R - 1) * 4 :=
      add_le_add (second_moment_ratio_le hm)
        (mul_le_mul_of_nonneg_left hratio (by linarith))
    _ = _ := by ring

theorem treeCount_lt_two_le {lam : ℝ} {n k : ℕ} (hk : 0 < k)
    (hq : 0 < 1 - (edgeProbability lam n : ℝ)) (hm : 2 ≤ treeMean lam n k) :
    probability lam n (fun G ↦ treeComponentCount G {k} < 2) ≤
      4 / treeMean lam n k +
        4 * (1 / (1 - (edgeProbability lam n : ℝ)) ^ (k * k) - 1) := by
  let X := fun G : SimpleGraph (Fin n) ↦ (treeComponentCount G {k} : ℝ)
  let m := treeMean lam n k
  let R := 1 / (1 - (edgeProbability lam n : ℝ)) ^ (k * k)
  have hmean : expectation lam n X = m := expectation_treeComponentCount_singleton lam n k
  have hR : 1 ≤ R := by
    apply (one_le_div (pow_pos hq _)).mpr
    exact pow_le_one₀ hq.le (by linarith [(edgeProbability lam n).property.1])
  have hvar : variance lam n X ≤ m + (R - 1) * m ^ 2 := by
    have hf := treeCount_factorial_le hk hq
    have heq : (fun G : SimpleGraph (Fin n) ↦ X G * (X G - 1)) =
        (fun G ↦ X G ^ 2 - X G) := by funext G; ring
    change expectation lam n (fun G ↦ X G * (X G - 1)) ≤ m ^ 2 / _ at hf
    rw [heq, expectation_sub, hmean] at hf
    rw [variance_eq_second_moment_sub, hmean]
    have hr : m ^ 2 / (1 - (edgeProbability lam n : ℝ)) ^ (k * k) = R * m ^ 2 := by
      dsimp [R]; ring
    rw [hr] at hf
    linarith
  calc
    _ ≤ probability lam n (fun G ↦ X G ≤ 1) := by
      apply probability_mono
      intro G hG
      dsimp [X]
      exact_mod_cast (show treeComponentCount G {k} ≤ 1 by omega)
    _ ≤ variance lam n X / (m - 1) ^ 2 := by
      have hc := probability_le_one_le_variance (lam := lam) X (by rw [hmean]; linarith)
      rw [hmean] at hc
      exact hc
    _ ≤ (m + (R - 1) * m ^ 2) / (m - 1) ^ 2 :=
      div_le_div_of_nonneg_right hvar (sq_nonneg _)
    _ ≤ _ := second_moment_error_bound hm hR

theorem secondLargest_lt_tree_bound {lam : ℝ} {n k : ℕ} (hk : 0 < k)
    (hq : 0 < 1 - (edgeProbability lam n : ℝ)) (hm : 2 ≤ treeMean lam n k) :
    probability lam n (fun G ↦ secondLargestComponentOrder G < k) ≤
      4 / treeMean lam n k +
        4 * (1 / (1 - (edgeProbability lam n : ℝ)) ^ (k * k) - 1) := by
  apply (probability_mono (fun G hG ↦ ?_)).trans (treeCount_lt_two_le hk hq hm)
  by_contra h
  have hh := le_secondLargestComponentOrder_of_two_trees G {k} hk
    (by intro j hj; have hj' : j = k := Finset.mem_singleton.mp hj; omega) (by omega)
  omega

end

end Erdos745
