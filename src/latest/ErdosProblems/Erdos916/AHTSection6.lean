/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos916.CoreAHT

/-!
# A common-neighbour rigidity lemma from the AHT route

The Section 6 argument of Aboulker--Havet--Trotignon repeatedly uses the
following elementary obstruction.  If two vertices have three common
neighbours and two of those common neighbours are adjacent, the five
displayed vertices already contain a wheel.  Hence a wheel-free graph makes
every common neighbourhood of cardinality at least three a stable set.

This formulation does not assume that the two vertices are twins or have
degree three.  It is therefore the unconditional local rigidity statement
needed before the Watkins--Mesner case analysis in the three-connected proof.
-/

namespace Erdos916

open SimpleGraph

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Three distinct common neighbours of two distinct vertices, with an edge
between the first two, explicitly give a wheel. -/
theorem hasWheelWitness_of_three_common_neighbors_of_adj
    {u v a b c : V} (huv : u ≠ v)
    (hua : G.Adj u a) (hub : G.Adj u b) (huc : G.Adj u c)
    (hva : G.Adj v a) (hvb : G.Adj v b) (hvc : G.Adj v c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (habAdj : G.Adj a b) :
    HasWheelWitness G := by
  exact hasWheelWitness_of_fourCycle_threeSpokes
    huc hvc.symm hvb hub.symm
    hua.symm hva.symm habAdj
    huv hub.ne hbc.symm hua.ne.symm hac hva.ne.symm hab

/-- In a wheel-free graph, any three displayed common neighbours are pairwise
nonadjacent.  This is the pointwise form used inside the AHT Section 6 case
analysis. -/
theorem not_adj_of_three_common_neighbors_of_noWheel
    {u v a b c : V} (hno : ¬HasWheelWitness G) (huv : u ≠ v)
    (hua : G.Adj u a) (hub : G.Adj u b) (huc : G.Adj u c)
    (hva : G.Adj v a) (hvb : G.Adj v b) (hvc : G.Adj v c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ¬G.Adj a b := by
  intro habAdj
  exact hno (hasWheelWitness_of_three_common_neighbors_of_adj
    huv hua hub huc hva hvb hvc hab hac hbc habAdj)

/-- A common neighbourhood of size at least three is a stable set in a
wheel-free graph.  Unlike the false-twin special case, this needs neither
equality of neighbourhoods nor degree assumptions. -/
theorem commonNeighbors_isIndepSet_of_three_le_of_noWheel
    {u v : V} (hno : ¬HasWheelWitness G) (huv : u ≠ v)
    (hcard : 3 ≤ Fintype.card (G.commonNeighbors u v)) :
    G.IsIndepSet (G.commonNeighbors u v) := by
  rw [G.isIndepSet_iff]
  intro a ha b hb hab
  have hua : G.Adj u a := (G.mem_commonNeighbors.mp ha).1
  have hva : G.Adj v a := (G.mem_commonNeighbors.mp ha).2
  have hub : G.Adj u b := (G.mem_commonNeighbors.mp hb).1
  have hvb : G.Adj v b := (G.mem_commonNeighbors.mp hb).2
  let S : Finset V := (G.commonNeighbors u v).toFinset
  have hScard : 3 ≤ S.card := by
    simpa only [S, Set.toFinset_card] using hcard
  have habSub : ({a, b} : Finset V) ⊆ S := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact Set.mem_toFinset.mpr ha
    · exact Set.mem_toFinset.mpr hb
  have hpairCard : ({a, b} : Finset V).card = 2 := by simp [hab]
  have hpairProper : ({a, b} : Finset V) ⊂ S := by
    exact (Finset.ssubset_iff_subset_ne.mpr ⟨habSub, by
      intro heq
      have := congrArg Finset.card heq
      omega⟩)
  obtain ⟨c, hcS, hcPair⟩ := Finset.exists_of_ssubset hpairProper
  have hc : c ∈ G.commonNeighbors u v := Set.mem_toFinset.mp hcS
  have huc : G.Adj u c := (G.mem_commonNeighbors.mp hc).1
  have hvc : G.Adj v c := (G.mem_commonNeighbors.mp hc).2
  have hca : c ≠ a := by
    intro h
    apply hcPair
    simp [h]
  have hcb : c ≠ b := by
    intro h
    apply hcPair
    simp [h]
  exact not_adj_of_three_common_neighbors_of_noWheel
    hno huv hua hub huc hva hvb hvc hab hca.symm hcb.symm

/-- Two distinct degree-three vertices with at least three common neighbours
are false twins.  This is the exact terminal conversion used when the
Watkins--Mesner analysis produces a three-common-neighbour pair. -/
theorem areFalseTwins_of_three_le_commonNeighbors_of_degree_three
    {u v : V} (huv : u ≠ v)
    (hdegu : G.degree u = 3) (hdegv : G.degree v = 3)
    (hcard : 3 ≤ Fintype.card (G.commonNeighbors u v)) :
    AreFalseTwins G u v := by
  have hUcard : Fintype.card (G.neighborSet u) = 3 := by
    rw [G.card_neighborSet_eq_degree, hdegu]
  have hVcard : Fintype.card (G.neighborSet v) = 3 := by
    rw [G.card_neighborSet_eq_degree, hdegv]
  have hCommonU : G.commonNeighbors u v = G.neighborSet u := by
    apply Set.eq_of_subset_of_card_le
      (G.commonNeighbors_subset_neighborSet_left u v)
    rw [hUcard]
    exact hcard
  have hCommonV : G.commonNeighbors u v = G.neighborSet v := by
    apply Set.eq_of_subset_of_card_le
      (G.commonNeighbors_subset_neighborSet_right u v)
    rw [hVcard]
    exact hcard
  exact ⟨huv, hCommonU.symm.trans hCommonV⟩

end Erdos916
