import ErdosProblems.Erdos19.LocallySparseColoring
import ErdosProblems.Erdos19.CommonNeighborSavings
import ErdosProblems.Erdos19.InducedCounting

/-! # A fractional coloring saving from a common-neighbor gap -/

namespace Erdos19

open Finset

attribute [local instance] Classical.propDecidable

theorem eventually_colorable_of_common_neighbor_gap (h : ℕ) (hh : 1 ≤ h) :
    ∃ q : ℕ, 0 < q ∧ ∃ N : ℕ, q ≤ N ∧ ∀ D : ℕ, N ≤ D →
      ∀ (V : Type*) [Fintype V], ∀ G : _root_.SimpleGraph V,
      (∀ v, (G.neighborSet v).ncard ≤ D) →
      (∀ v w, G.Adj v w → (G.neighborSet v ∩ G.neighborSet w).ncard + D / h ≤ D) →
      G.Colorable (D - D / q) := by
  classical
  obtain ⟨q₀, hq₀, N₀, hN₀, hcolor⟩ :=
    eventually_colorable_with_fractional_saving (8 * h) (by omega)
  let q := max q₀ (8 * h)
  have hq8 : 8 * h ≤ q := le_max_right _ _
  have hqq : q₀ ≤ q := le_max_left _ _
  have hqpos : 0 < q := hq₀.trans_le hqq
  refine ⟨q, hqpos, max N₀ q, le_max_right _ _, ?_⟩
  intro D hD V _ G hdegree hcommon
  have hD₀ : N₀ ≤ D := (le_max_left _ _).trans hD
  have hqD : q ≤ D := (le_max_right _ _).trans hD
  have hD8 : 8 * h ≤ D := hq8.trans hqD
  let k := D - D / q
  have hq2 : 2 ≤ q := by omega
  have hDpos : 0 < D := hqpos.trans_le hqD
  have hkpos : 0 < k := Nat.sub_pos_of_lt (Nat.div_lt_self hDpos (by omega))
  obtain ⟨S, _, hdense, hpeel⟩ := exists_dense_core_with_peelable_remainder G univ k
  let H := G.induce (S : Set V)
  have hdegreeH (v : (S : Set V)) : (H.neighborSet v).ncard ≤ D :=
    (induced_neighbor_ncard_le G _ v).trans (hdegree v.1)
  have hmin (v : (S : Set V)) : D - D / q ≤ (H.neighborSet v).ncard := by
    rw [induced_finset_neighbor_ncard]
    exact hdense v.1 v.2
  have hcommonH (v w : (S : Set V)) (hadj : H.Adj v w) :
      (H.neighborSet v ∩ H.neighborSet w).ncard ≤ D - D / h := by
    have hle := induced_common_neighbor_ncard_le G (S : Set V) v w
    change (H.neighborSet v ∩ H.neighborSet w).ncard ≤
      (G.neighborSet v.1 ∩ G.neighborSet w.1).ncard at hle
    have hbase := hcommon v.1 w.1 hadj
    omega
  have hpairs (v : (S : Set V)) : D ^ 2 ≤
      (8 * h) * (nonadjacentNeighborPairGraph H v).edgeSet.ncard := by
    apply common_neighbor_gap_saving h q D (H.neighborSet v).ncard (D - D / h)
      _ hh hq8 hD8 (hmin v)
    · exact Nat.sub_add_cancel (Nat.div_le_self D h) |>.le
    · exact nonadjacentNeighborPairs_lower_bound H v (D - D / h) (hcommonH v)
  have hcore := hcolor D hD₀ (S : Set V) H hdegreeH hpairs
  have hpalette : D - D / q₀ ≤ k := by
    have hdiv : D / q ≤ D / q₀ := Nat.div_le_div_left hqq hq₀
    exact Nat.sub_le_sub_left hdiv D
  apply colorable_of_colorable_peelable_core G S k hkpos hpeel
  exact _root_.SimpleGraph.Colorable.mono hpalette hcore

#print axioms eventually_colorable_of_common_neighbor_gap

end Erdos19
