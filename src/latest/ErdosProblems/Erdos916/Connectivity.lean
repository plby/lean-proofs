/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos916.Blocks
import ErdosProblems.Erdos223.SphericalEuler.ComponentSum

namespace Erdos916

open SimpleGraph

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable local instance componentFintype (C : G.ConnectedComponent) : Fintype C :=
  Fintype.ofFinite C

noncomputable local instance componentAdjDecidable (C : G.ConnectedComponent) :
    DecidableRel C.toSimpleGraph.Adj := Classical.decRel _

/-- Passing to a connected component preserves the degree of each of its vertices. -/
def connectedComponentNeighborEquiv (C : G.ConnectedComponent) (u : C) :
    C.toSimpleGraph.neighborSet u ≃ G.neighborSet u.1 where
  toFun w := ⟨w.1.1, by
    have hw : C.toSimpleGraph.Adj u w.1 := w.2
    simpa [SimpleGraph.ConnectedComponent.toSimpleGraph] using hw⟩
  invFun w :=
    have hw : G.Adj u.1 w.1 := w.2
    ⟨⟨w.1, C.mem_supp_of_adj_mem_supp u.2 hw⟩,
      by simpa [SimpleGraph.ConnectedComponent.toSimpleGraph] using hw⟩
  left_inv w := by apply Subtype.ext; apply Subtype.ext; rfl
  right_inv w := by apply Subtype.ext; rfl

theorem degree_connectedComponent (C : G.ConnectedComponent) (u : C) :
    C.toSimpleGraph.degree u = G.degree u.1 := by
  rw [← C.toSimpleGraph.card_neighborSet_eq_degree,
    ← G.card_neighborSet_eq_degree]
  exact Fintype.card_congr (connectedComponentNeighborEquiv G C u)

/-- A nonempty graph at density `2n-2` has a connected component at the same density. -/
theorem exists_dense_connectedComponent
    (hV : Nonempty V)
    (hdense : 2 * Fintype.card V ≤ G.edgeFinset.card + 2) :
    ∃ C : G.ConnectedComponent,
      2 * Fintype.card C ≤ C.toSimpleGraph.edgeFinset.card + 2 := by
  classical
  by_contra h
  push Not at h
  have hC (C : G.ConnectedComponent) :
      C.toSimpleGraph.edgeFinset.card + 3 ≤ 2 * Fintype.card C := by
    have := h C
    omega
  have hsum := Finset.sum_le_sum fun C (_ : C ∈ (Finset.univ : Finset G.ConnectedComponent)) => hC C
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul] at hsum
  rw [← Finset.mul_sum, G.sum_card_edgeFinset_connectedComponents,
    G.sum_card_connectedComponents] at hsum
  have hcomp0 : 0 < Fintype.card G.ConnectedComponent :=
    Fintype.card_pos_iff.mpr ⟨G.connectedComponentMk (Classical.choice hV)⟩
  have hthree : 3 ≤ Fintype.card G.ConnectedComponent * 3 := by omega
  have hstrict : G.edgeFinset.card + 3 ≤ 2 * Fintype.card V :=
    le_trans (Nat.add_le_add_left hthree _) hsum
  omega

/-- In a non-preconnected graph, every connected component is a proper vertex subset. -/
theorem connectedComponent_card_lt_of_not_preconnected
    (hG : ¬G.Preconnected) (C : G.ConnectedComponent) :
    Fintype.card C < Fintype.card V := by
  classical
  simp only [SimpleGraph.Preconnected] at hG
  push Not at hG
  obtain ⟨u, v, huv⟩ := hG
  have hne : G.connectedComponentMk u ≠ G.connectedComponentMk v := by
    exact fun h => huv (ConnectedComponent.exact h)
  let D : G.ConnectedComponent := if C = G.connectedComponentMk u
    then G.connectedComponentMk v else G.connectedComponentMk u
  have hDC : D ≠ C := by
    by_cases h : C = G.connectedComponentMk u
    · simp only [D, if_pos h]
      intro hvC
      exact hne (h.symm.trans hvC.symm)
    · simp only [D, if_neg h]
      exact fun huC => h huC.symm
  obtain ⟨w, hwD⟩ := D.nonempty_supp
  have hwC : w ∉ C.supp := by
    intro hwC
    exact hDC (ConnectedComponent.eq_of_common_vertex hwD hwC)
  exact Fintype.card_subtype_lt hwC

end Erdos916
