import ErdosProblems.Erdos547.EquitableRegularPartition

/-!
# Degree averaging over equal clusters
-/

namespace Erdos547

open Finset SimpleGraph
open scoped BigOperators

variable {V I : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem degreeIn_biUnion_le (J : Finset I) (C : I → Finset V) (v : V) :
    degreeIn G (J.biUnion C) v ≤ ∑ i ∈ J, degreeIn G (C i) v := by
  unfold degreeIn
  rw [Finset.filter_biUnion]
  exact Finset.card_biUnion_le

theorem sum_degreeIn_eq_density_mul {X Y : Finset V} (hX : X.Nonempty) (hY : Y.Nonempty) :
    (∑ v ∈ X, (degreeIn G Y v : ℝ)) =
      (G.edgeDensity X Y : ℝ) * ((X.card : ℝ) * Y.card) := by
  have hp : (X.card : ℝ) * Y.card ≠ 0 := ne_of_gt
    (mul_pos (by exact_mod_cast hX.card_pos) (by exact_mod_cast hY.card_pos))
  exact ((eq_div_iff hp).mp (edgeDensity_eq_sum_degreeIn_div G X Y)).symm

namespace EquitableRegularPartition

variable {G} {ε : ℝ} (P : EquitableRegularPartition G ε)

theorem cluster_nonempty (X : ↥P.clusters) : X.val.Nonempty :=
  Finset.card_pos.mp (by rw [P.equal_size X.val X.property]; exact P.positive_size)

theorem cluster_volume : (P.clusters.biUnion id).card = P.clusterSize * P.clusters.card := by
  classical
  rw [Finset.card_biUnion (show (P.clusters : Set (Finset V)).PairwiseDisjoint id from
    fun X hX Y hY hne ↦ P.disjoint X hX Y hY hne)]
  calc
    (∑ X ∈ P.clusters, (id X).card) = ∑ _X ∈ P.clusters, P.clusterSize :=
      Finset.sum_congr rfl (fun X hX ↦ P.equal_size X hX)
    _ = _ := by simp [Nat.mul_comm]

theorem cluster_volume_le : P.clusterSize * P.clusters.card ≤ Fintype.card V := by
  rw [← P.cluster_volume]
  exact Finset.card_le_univ _

theorem degree_le_cluster_sum (v : V) : (G.degree v : ℝ) ≤
    (∑ Y : ↥P.clusters, (degreeIn G Y.val v : ℝ)) + ε * Fintype.card V := by
  classical
  have h := degreeIn_le_add_removed G Finset.univ (P.clusters.biUnion id) v
  rw [degreeIn_univ] at h
  have hsum := degreeIn_biUnion_le G P.clusters id v
  have hn : G.degree v ≤ (∑ Y ∈ P.clusters, degreeIn G Y v) +
      (Finset.univ \ P.clusters.biUnion id).card := by
    simpa only [id_eq] using h.trans (Nat.add_le_add_right hsum _)
  have hn' : (G.degree v : ℝ) ≤ (∑ Y ∈ P.clusters, (degreeIn G Y v : ℝ)) +
      (Finset.univ \ P.clusters.biUnion id).card := by exact_mod_cast hn
  rw [Finset.sum_coe_sort P.clusters (fun Y ↦ (degreeIn G Y v : ℝ))]
  exact hn'.trans (add_le_add_right P.discarded_bound _)

theorem density_lower_of_min_degree (D : ℝ) (hD : ∀ v, D ≤ (G.degree v : ℝ))
    (X : ↥P.clusters) : D ≤
      (P.clusterSize : ℝ) * (∑ Y : ↥P.clusters, (G.edgeDensity X.val Y.val : ℝ)) +
        ε * Fintype.card V := by
  classical
  have hm : 0 < (P.clusterSize : ℝ) := by exact_mod_cast P.positive_size
  have hmass (Y : ↥P.clusters) : (∑ v ∈ X.val, (degreeIn G Y.val v : ℝ)) =
      (G.edgeDensity X.val Y.val : ℝ) * ((P.clusterSize : ℝ) * P.clusterSize) := by
    rw [sum_degreeIn_eq_density_mul G (P.cluster_nonempty X) (P.cluster_nonempty Y),
      P.equal_size X.val X.property, P.equal_size Y.val Y.property]
  have htotal : (P.clusterSize : ℝ) * D ≤
      (P.clusterSize : ℝ) *
        ((P.clusterSize : ℝ) * (∑ Y : ↥P.clusters, (G.edgeDensity X.val Y.val : ℝ)) +
          ε * Fintype.card V) := by
    calc
      _ = ∑ _v ∈ X.val, D := by simp [P.equal_size X.val X.property]
      _ ≤ ∑ v ∈ X.val, (G.degree v : ℝ) := Finset.sum_le_sum fun v _ ↦ hD v
      _ ≤ ∑ v ∈ X.val,
          ((∑ Y : ↥P.clusters, (degreeIn G Y.val v : ℝ)) + ε * Fintype.card V) :=
        Finset.sum_le_sum fun v _ ↦ P.degree_le_cluster_sum v
      _ = (∑ Y : ↥P.clusters, (∑ v ∈ X.val, (degreeIn G Y.val v : ℝ))) +
          (P.clusterSize : ℝ) * (ε * Fintype.card V) := by
        rw [Finset.sum_add_distrib, Finset.sum_comm]
        simp only [Finset.sum_const, P.equal_size X.val X.property, nsmul_eq_mul]
      _ = _ := by
        simp only [hmass, ← Finset.sum_mul]
        ring
  exact (mul_le_mul_iff_of_pos_left hm).mp htotal

end EquitableRegularPartition

end Erdos547

#print axioms Erdos547.EquitableRegularPartition.density_lower_of_min_degree
