import ErdosProblems.Erdos547.EquitableRegularPartition

/-!
# Equal reservoir and buffer sets in every cluster

The anchor clusters are included. Seed images are accounted for separately
when available vertices are counted.
-/

namespace Erdos547

open Finset SimpleGraph

theorem exists_reservoir_and_buffer {V : Type*} [DecidableEq V] (X : Finset V) (q : ℕ)
    (hq : 2 * q ≤ X.card) :
    ∃ Q U : Finset V, Q ⊆ X ∧ U ⊆ X ∧ Q.card = q ∧ U.card = q ∧ Disjoint Q U ∧
      (X \ (Q ∪ U)).card + 2 * q = X.card := by
  obtain ⟨Q, hQ, hQcard⟩ := Finset.exists_subset_card_eq (show q ≤ X.card by omega)
  have hremaining := Finset.card_sdiff_add_card_eq_card hQ
  have hqrem : q ≤ (X \ Q).card := by omega
  obtain ⟨U, hU, hUcard⟩ := Finset.exists_subset_card_eq hqrem
  have hUX : U ⊆ X := hU.trans Finset.sdiff_subset
  have hdis : Disjoint Q U := by
    apply Finset.disjoint_left.mpr
    intro v hvQ hvU
    exact (Finset.mem_sdiff.mp (hU hvU)).2 hvQ
  refine ⟨Q, U, hQ, hUX, hQcard, hUcard, hdis, ?_⟩
  have hQU : Q ∪ U ⊆ X := Finset.union_subset hQ hUX
  have hc := Finset.card_sdiff_add_card_eq_card hQU
  rw [Finset.card_union_of_disjoint hdis, hQcard, hUcard] at hc
  omega

namespace EquitableRegularPartition

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {ε : ℝ}

theorem exists_cluster_reservoirs (P : EquitableRegularPartition G ε) (q : ℕ)
    (hq : 2 * q ≤ P.clusterSize) :
    ∃ Q U : ↥P.clusters → Finset V, ∀ i,
      Q i ⊆ i.val ∧ U i ⊆ i.val ∧ (Q i).card = q ∧ (U i).card = q ∧ Disjoint (Q i) (U i) ∧
      (i.val \ (Q i ∪ U i)).card = P.clusterSize - 2 * q := by
  have hchoose (i : ↥P.clusters) := exists_reservoir_and_buffer i.val q
    (by rw [P.equal_size i.val i.property]; exact hq)
  choose Q U hQ hU hQc hUc hdis hrest using hchoose
  refine ⟨Q, U, fun i ↦ ⟨hQ i, hU i, hQc i, hUc i, hdis i, ?_⟩⟩
  have hh := hrest i
  rw [P.equal_size i.val i.property] at hh
  omega

end EquitableRegularPartition

end Erdos547

#print axioms Erdos547.EquitableRegularPartition.exists_cluster_reservoirs
