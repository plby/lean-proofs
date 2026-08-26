import ErdosProblems.Erdos19.NonadjacentPairs
import ErdosProblems.Erdos19.ColorCoverCounting

/-! # Converting common-neighbor bounds into missing neighbor pairs -/

namespace Erdos19

open Finset
open _root_.SimpleGraph

attribute [local instance] Classical.propDecidable

theorem nonadjacentNeighborPairs_lower_bound {V : Type*} [Fintype V]
    (G : _root_.SimpleGraph V) (v : V) (c : ℕ)
    (hcommon : ∀ w, G.Adj v w → (G.neighborSet v ∩ G.neighborSet w).ncard ≤ c) :
    (G.neighborSet v).ncard * ((G.neighborSet v).ncard - c - 1) ≤
      2 * (nonadjacentNeighborPairGraph G v).edgeSet.ncard := by
  classical
  let B := nonadjacentNeighborPairGraph G v
  have hper (w : V) (hw : w ∈ G.neighborSet v) :
      (G.neighborSet v).ncard - c - 1 ≤ (B.neighborSet w).ncard := by
    have hsub : G.neighborSet v ⊆ B.neighborSet w ∪ (G.neighborSet v ∩ G.neighborSet w) ∪ {w} := by
      intro x hx
      by_cases hxw : x = w
      · exact Or.inr hxw
      · left
        by_cases hwx : G.Adj w x
        · exact Or.inr ⟨hx, hwx⟩
        · exact Or.inl ⟨Ne.symm hxw, hw, hx, hwx⟩
    have hcard := Set.ncard_le_ncard hsub
    have hunion := Set.ncard_union_le (B.neighborSet w ∪ (G.neighborSet v ∩ G.neighborSet w)) {w}
    have hunion' := Set.ncard_union_le (B.neighborSet w) (G.neighborSet v ∩ G.neighborSet w)
    have hc := hcommon w hw
    rw [Set.ncard_singleton] at hunion
    omega
  have hhand : (∑ w : V, (B.neighborSet w).ncard) = 2 * B.edgeSet.ncard := by
    have h := B.sum_degrees_eq_twice_card_edges
    simpa only [← card_neighborSet_eq_degree, Set.fintypeCard_eq_ncard,
      ← Set.ncard_coe_finset, B.coe_edgeFinset] using h
  rw [← hhand]
  nth_rw 1 [ncard_eq_sum_indicator (G.neighborSet v)]
  rw [sum_mul]
  apply sum_le_sum
  intro w _
  by_cases hw : w ∈ G.neighborSet v
  · rw [if_pos hw, one_mul]
    exact hper w hw
  · rw [if_neg hw, zero_mul]
    exact Nat.zero_le _

theorem common_neighbor_gap_saving (h q D d c B : ℕ) (hh : 1 ≤ h)
    (hq : 8 * h ≤ q) (hD : 8 * h ≤ D) (hd : D - D / q ≤ d)
    (hc : c + D / h ≤ D) (hpairs : d * (d - c - 1) ≤ 2 * B) :
    D ^ 2 ≤ (8 * h) * B := by
  have hqpos : 0 < q := by omega
  have hhpos : 0 < h := by omega
  have hq8 : 8 ≤ q := by omega
  have hdiv : 8 * h * (D / q) ≤ D :=
    (Nat.mul_le_mul_right _ hq).trans (Nat.mul_div_le D q)
  have hdiv8 : 8 * (D / q) ≤ D :=
    (Nat.mul_le_mul_right _ hq8).trans (Nat.mul_div_le D q)
  have hhalf : D ≤ 2 * d := by omega
  have hfloor := Nat.lt_mul_div_succ D hhpos
  have hdegree : D ≤ d + D / q := by omega
  have hdegree' := Nat.mul_le_mul_left h hdegree
  have hcommon := Nat.mul_le_mul_left h hc
  have hsub : d ≤ (d - c - 1) + c + 1 := by omega
  have hsub' := Nat.mul_le_mul_left h hsub
  have hsaving : D ≤ 2 * h * (d - c - 1) := by
    nlinarith only [hdiv, hfloor, hD, hdegree', hcommon, hsub']
  have hproduct := Nat.mul_le_mul hhalf hsaving
  have hpairsmul := Nat.mul_le_mul_left (4 * h) hpairs
  nlinarith only [hproduct, hpairsmul]

#print axioms nonadjacentNeighborPairs_lower_bound
#print axioms common_neighbor_gap_saving

end Erdos19
