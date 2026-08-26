import ErdosProblems.Erdos547.RegularityRowCleaning

/-!
# Counting equal disjoint clusters and the discarded vertices
-/

namespace Erdos547

open Finset
open scoped BigOperators

theorem card_cluster_union {V I : Type*} [DecidableEq V] [Fintype I]
    (C : I → Finset V) (hdis : Pairwise (fun i j ↦ Disjoint (C i) (C j)))
    (m : ℕ) (hsize : ∀ i, (C i).card = m) :
    ((Finset.univ : Finset I).biUnion C).card = m * Fintype.card I := by
  classical
  have hd : (↑(Finset.univ : Finset I) : Set I).PairwiseDisjoint C :=
    fun _ _ _ _ hij ↦ hdis hij
  rw [Finset.card_biUnion hd]
  simp only [hsize, Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.mul_comm]

theorem card_outside_clusters {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I]
    (C : I → Finset V) (hdis : Pairwise (fun i j ↦ Disjoint (C i) (C j)))
    (m : ℕ) (hsize : ∀ i, (C i).card = m) :
    (Finset.univ \ (Finset.univ.biUnion C)).card + m * Fintype.card I = Fintype.card V := by
  classical
  have hh := Finset.card_sdiff_add_card_eq_card
    (Finset.subset_univ ((Finset.univ : Finset I).biUnion C))
  rw [card_cluster_union C hdis m hsize, Finset.card_univ] at hh
  exact hh

theorem discarded_vertices_bound (δ : ℝ) (hδ : 0 ≤ δ) (n m t j g : ℕ)
    (hmn : m * t ≤ n) (hnm : n ≤ (m + 1) * t) (hjt : j ≤ t)
    (hcount : g + m * j = n) (hdrop : ((t - j : ℕ) : ℝ) ≤ δ * t)
    (hsmall : (t : ℝ) ≤ δ * n) : (g : ℝ) ≤ 2 * δ * n := by
  have hbase : g ≤ m * (t - j) + t := by
    have hh := Nat.sub_add_cancel hjt
    nlinarith only [hnm, hcount, hh]
  have hbase' : (g : ℝ) ≤ (m : ℝ) * (t - j : ℕ) + t := by exact_mod_cast hbase
  have hmn' : (m : ℝ) * t ≤ n := by exact_mod_cast hmn
  have hd := mul_le_mul_of_nonneg_left hdrop (Nat.cast_nonneg m)
  have hm := mul_le_mul_of_nonneg_left hmn' hδ
  nlinarith only [hbase', hd, hm, hsmall]

end Erdos547

#print axioms Erdos547.card_outside_clusters
#print axioms Erdos547.discarded_vertices_bound
