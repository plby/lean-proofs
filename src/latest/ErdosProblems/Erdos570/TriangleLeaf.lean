/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos570.TriangleHost

/-!
# The degree-one branch for triangles
-/

open scoped SimpleGraph

noncomputable section

namespace Erdos570

open Erdos79

/-- In a connected target, deleting a leaf leaves at least `p` unused host
vertices.  If the leaf cannot be restored in blue, all of them lie in one
red neighbourhood, which is a blue clique of order at least `p`. -/
theorem triangle_degree_one_contradiction
    {H : GraphCode} {N : ℕ} (C : SimpleGraph (Fin N))
    [DecidableRel C.Adj] [DecidableRel H.graph.Adj]
    (hH : NoIsolated H) (hconn : H.graph.Connected)
    (hN : 2 * H.edgeCount + 1 ≤ N)
    (v : Fin H.vertexCount) (hv : H.graph.degree v = 1)
    (hdelete : RamseyAt (cycleCode 3)
      (supportCode (deleteVertexCode H v)) N)
    (hnoCycle : ¬ (cycleCode 3).graph ⊑ C)
    (hnoH : ¬ H.graph ⊑ Cᶜ) : False := by
  classical
  let p := H.vertexCount
  let m := H.edgeCount
  have hp2m : p ≤ 2 * m := by
    simpa [p, m] using NoIsolated.vertexCount_le_twice_edgeCount hH
  have hroom : H.vertexCount - 1 ≤ N := by
    dsimp only [p] at hp2m
    omega
  have hobs := deletion_obstruction_le_compl_cliqueNum
    C v (by rw [hv]; omega) hroom hdelete hnoCycle hnoH
  rw [hv, one_mul] at hobs
  have hcliqueLt : Cᶜ.cliqueNum < p := by
    obtain ⟨T, hTclique, hTcard⟩ := Cᶜ.exists_isNClique_cliqueNum
    by_contra hnot
    apply hnoH
    exact isContained_of_isClique_card_le H.graph Cᶜ T hTclique
      (by rw [hTcard]; simpa [p] using Nat.le_of_not_gt hnot)
  have hpEdge : p ≤ m + 1 := by
    simpa [p, m, GraphCode.edgeCount] using
      hconn.card_vert_le_card_edgeSet_add_one
  omega

end Erdos570
