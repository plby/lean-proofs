import ErdosProblems.Erdos556.BipartiteCycles
import ErdosProblems.Erdos556.Separation

/-!
# Connectivity forced by a complementary cycle exclusion

If the complement has no cycle of length `2L`, a minimum-degree core
cannot split after a small vertex deletion: the two sides would contain
a complete bipartite graph in the complement.
-/

namespace Erdos556

open SimpleGraph Finset

theorem connectedAfterDeleting_of_complement_cycle_free {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (L b : ℕ) (hL : 2 ≤ L)
    (hdegree : ∀ v, L + b ≤ G.degree v) (hno : ¬ cycleGraph (2 * L) ⊑ Gᶜ) :
    ConnectedAfterDeleting G b := by
  classical
  intro S hS
  by_contra hdisc
  obtain ⟨A, B, hA, hB, hAB, _, _, hcover, hcross⟩ :=
    exists_separation_of_not_preconnected G S hdisc
  obtain ⟨a, ha⟩ := hA
  obtain ⟨b₀, hb₀⟩ := hB
  have hAcard : L ≤ A.card := by
    have hd := degree_le_parts_of_separation G A B S hcover hcross a ha
    have hmin := hdegree a
    omega
  have hBcard : L ≤ B.card := by
    have hcover' : B ∪ A ∪ S = univ := by rw [union_comm B A]; exact hcover
    have hcross' : ∀ u ∈ B, ∀ v ∈ A, ¬ G.Adj u v :=
      fun u hu v hv huv => hcross v hv u hu huv.symm
    have hd := degree_le_parts_of_separation G B A S hcover' hcross' b₀ hb₀
    have hmin := hdegree b₀
    omega
  have hcomplete (u : V) (hu : u ∈ A) (v : V) (hv : v ∈ B) : Gᶜ.Adj u v := by
    rw [compl_adj]
    refine ⟨?_, hcross u hu v hv⟩
    intro h
    exact Finset.disjoint_left.mp hAB hu (h ▸ hv)
  obtain ⟨u, c, hc, hlen, _⟩ := exists_even_cycle_of_complete_bipartite Gᶜ L hL A B hAB
    hcomplete hAcard hBcard
  exact hno ((cycleGraph_isContained_iff (by omega)).mpr ⟨u, c, hc, hlen⟩)

#print axioms connectedAfterDeleting_of_complement_cycle_free

end Erdos556
