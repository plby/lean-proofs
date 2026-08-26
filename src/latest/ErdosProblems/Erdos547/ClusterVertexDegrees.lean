import ErdosProblems.Erdos547.ClusterUpperTypical

/-!
# Bounding a typical host vertex's degree by cluster densities
-/

noncomputable section

namespace Erdos547

open Finset SimpleGraph
open scoped BigOperators

theorem sum_coe_indicator_eq_card_filter {A : Type*} [DecidableEq A]
    (S : Finset A) (Q : A → Prop) [DecidablePred Q] :
    (∑ x : ↥S, if Q x.val then (1 : ℝ) else 0) = ((S.filter Q).card : ℝ) := by
  rw [Finset.sum_coe_sort S (fun x ↦ if Q x then (1 : ℝ) else 0)]
  simp only [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter, apply_ite,
    Nat.cast_one, Nat.cast_zero]

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj] {ε : ℝ}

theorem degreeIn_le_density_with_exceptions (hε : 0 ≤ ε) (X Y : Finset V) (v : V) :
    (degreeIn G Y v : ℝ) ≤ (Y.card : ℝ) *
      ((G.edgeDensity X Y : ℝ) + ε + (if ¬ G.IsUniform ε X Y then 1 else 0) +
        (if G.IsUniform ε X Y ∧
          ((G.edgeDensity X Y : ℝ) + ε) * Y.card < (degreeIn G Y v : ℝ)
          then 1 else 0)) := by
  classical
  have hd : 0 ≤ (G.edgeDensity X Y : ℝ) := by exact_mod_cast G.edgeDensity_nonneg X Y
  have hcard : (degreeIn G Y v : ℝ) ≤ Y.card := by exact_mod_cast degreeIn_le_card G Y v
  have hprod := mul_nonneg (Nat.cast_nonneg Y.card : (0 : ℝ) ≤ Y.card) (add_nonneg hd hε)
  by_cases hr : G.IsUniform ε X Y
  · by_cases hu : ((G.edgeDensity X Y : ℝ) + ε) * Y.card < (degreeIn G Y v : ℝ)
    · simp only [hr, hu, not_true_eq_false, if_false, true_and, if_true, add_zero]
      nlinarith only [hcard, hprod]
    · simp only [hr, hu, not_true_eq_false, if_false, and_false, add_zero]
      nlinarith only [le_of_not_gt hu]
  · simp only [hr, not_false_eq_true, if_true, false_and, if_false, add_zero]
    nlinarith only [hcard, hprod]

namespace EquitableRegularPartition

variable {G} (P : EquitableRegularPartition G ε)

theorem card_nonregular_partners_le (X : ↥P.clusters) :
    ((P.clusters.filter (fun Y ↦ ¬ G.IsUniform ε X.val Y)).card : ℝ) ≤
      1 + ε * P.clusters.card := by
  classical
  have hsub : P.clusters.filter (fun Y ↦ ¬ G.IsUniform ε X.val Y) ⊆
      insert X.val (P.clusters.filter (fun Y ↦ X.val ≠ Y ∧ ¬ G.IsUniform ε X.val Y)) := by
    intro Y hY
    obtain ⟨hYP, hr⟩ := Finset.mem_filter.mp hY
    by_cases he : X.val = Y
    · exact Finset.mem_insert.mpr (Or.inl he.symm)
    · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_filter.mpr ⟨hYP, he, hr⟩))
  have hh := (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)
  have hh' : ((P.clusters.filter (fun Y ↦ ¬ G.IsUniform ε X.val Y)).card : ℝ) ≤
      ((P.clusters.filter (fun Y ↦ X.val ≠ Y ∧ ¬ G.IsUniform ε X.val Y)).card : ℝ) + 1 := by
    exact_mod_cast hh
  linarith only [hh', P.irregular_bound X.val X.property]

theorem typical_vertex_degree_le (hε : 0 ≤ ε) (δ : ℝ) (X : ↥P.clusters) (v : V)
    (hv : ((P.upperExceptionalPairs X.val v).card : ℝ) ≤ δ * P.clusters.card) :
    (G.degree v : ℝ) ≤
      (P.clusterSize : ℝ) *
        ((∑ Y : ↥P.clusters, (G.edgeDensity X.val Y.val : ℝ)) +
          1 + (2 * ε + δ) * P.clusters.card) + ε * Fintype.card V := by
  classical
  have hsum : (∑ Y : ↥P.clusters, (degreeIn G Y.val v : ℝ)) ≤
      ∑ Y : ↥P.clusters, (P.clusterSize : ℝ) *
        ((G.edgeDensity X.val Y.val : ℝ) + ε +
          (if ¬ G.IsUniform ε X.val Y.val then 1 else 0) +
          (if G.IsUniform ε X.val Y.val ∧
            ((G.edgeDensity X.val Y.val : ℝ) + ε) * Y.val.card <
              (degreeIn G Y.val v : ℝ) then 1 else 0)) := by
    apply Finset.sum_le_sum
    intro Y _
    have hh := degreeIn_le_density_with_exceptions G hε X.val Y.val v
    nth_rw 1 [P.equal_size Y.val Y.property] at hh
    exact hh
  simp only [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_coe, nsmul_eq_mul] at hsum
  rw [sum_coe_indicator_eq_card_filter P.clusters (fun Y ↦ ¬ G.IsUniform ε X.val Y),
    sum_coe_indicator_eq_card_filter P.clusters (fun Y ↦ G.IsUniform ε X.val Y ∧
      ((G.edgeDensity X.val Y : ℝ) + ε) * Y.card < (degreeIn G Y v : ℝ))] at hsum
  have hbad := P.card_nonregular_partners_le X
  have hlow := P.degree_le_cluster_sum v
  have hm : 0 ≤ (P.clusterSize : ℝ) := Nat.cast_nonneg _
  have hbmul := mul_le_mul_of_nonneg_left hbad hm
  have hvmul := mul_le_mul_of_nonneg_left hv hm
  change ((P.clusters.filter (fun Y ↦ G.IsUniform ε X.val Y ∧
    ((G.edgeDensity X.val Y : ℝ) + ε) * Y.card < (degreeIn G Y v : ℝ))).card : ℝ) ≤
      δ * P.clusters.card at hv
  dsimp only [upperExceptionalPairs] at hvmul
  nlinarith only [hsum, hlow, hbmul, hvmul]

end EquitableRegularPartition

end Erdos547

#print axioms Erdos547.EquitableRegularPartition.typical_vertex_degree_le
