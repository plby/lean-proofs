/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos570.SparseLeafNumeric
import ErdosProblems.Erdos570.SparseLongPath
import ErdosProblems.Erdos570.LeafObstructionEndgame

/-!
# The sparse connected-target theorem

This is the full sparse branch.  A long suspended path is handled by
compression.  Otherwise the explicit contraction estimate supplies two
batches of leaves; the smaller batch pays for repeated path-Ramsey copies,
and the larger batch is reinserted in the final blue-complete pair.
-/

open scoped SimpleGraph

noncomputable section

namespace Erdos570

open Erdos79

theorem ramseyAt_oddBudget_of_sparse_connected
    {r B : ℕ} (hB : r + 1 ≤ B)
    (H : GraphCode) [DecidableRel H.graph.Adj]
    (hH : NoIsolated H) (hconn : H.graph.Connected)
    (hm : oddSparseEdgeThreshold r ≤ H.edgeCount)
    (hdensity : (oddSparseD r - 1) * H.edgeCount <
      oddSparseD r * H.vertexCount)
    (hIH : ∀ Q : GraphCode, NoIsolated Q → Q.edgeCount < H.edgeCount →
      graphRamseyNumber (cycleCode (2 * r + 3)) Q ≤
        oddBudget B (r + 1) Q.edgeCount) :
    RamseyAt (cycleCode (2 * r + 3)) H
      (oddBudget B (r + 1) H.edgeCount) := by
  classical
  by_cases hlong : ∃ t : ℕ, oddSparsePathLength r ≤ t ∧
      ∃ p : Fin (t + 2) → Fin H.vertexCount,
        IsSuspendedPath H.graph p
  · obtain ⟨t, ht, p, hp⟩ := hlong
    apply ramseyAt_oddBudget_of_long_suspendedPath H hH hconn hp
    · simpa [oddSparsePathLength] using ht
    · exact hIH
  · have hleaf := twice_oddLeafBatch_le_leafVertices r H hH hconn
      hm hdensity hlong
    let q := oddLeafBatch r (sparseExcess H)
    have hqpos : 2 ≤ q := by
      dsimp only [q]
      unfold oddLeafBatch oddLeafRamseyCost
      have hcost : 1 ≤ (2 * r + 2) * (1 + 2 * sparseExcess H) :=
        Nat.mul_pos (by omega) (by omega)
      omega
    obtain ⟨L₂, hL₂leaf, hL₂card⟩ :=
      Finset.exists_subset_card_eq hleaf
    have hqL₂ : q ≤ L₂.card := by omega
    obtain ⟨L, hLL₂, hLcard⟩ := Finset.exists_subset_card_eq hqL₂
    have hLleaf : L ⊆ leafVertices H := hLL₂.trans hL₂leaf
    have hLeaves (v : Fin H.vertexCount) (hv : v ∈ L) :
        H.graph.degree v = 1 :=
      (mem_leafVertices H v).mp (hLleaf hv)
    have hLeaves₂ (v : Fin H.vertexCount) (hv : v ∈ L₂) :
        H.graph.degree v = 1 :=
      (mem_leafVertices H v).mp (hL₂leaf hv)
    have hL₂le : L₂.card ≤ H.vertexCount := by
      simpa using Finset.card_le_card (Finset.subset_univ L₂)
    have hn : 3 ≤ H.vertexCount := by omega
    have hremain : 2 ≤ H.vertexCount - L.card := by omega
    let Q := deleteLeavesCode H L
    have hQno : NoIsolated Q :=
      deleteLeavesCode_noIsolated H hconn L hLeaves hremain
    have hdeleteEdges :=
      deleteLeavesCode_edgeCount_add_card_le H hconn hn L hLeaves
    have hQlt : Q.edgeCount < H.edgeCount := by
      dsimp only [Q]
      omega
    have hQram : graphRamseyNumber (cycleCode (2 * r + 3)) Q ≤
        oddBudget B (r + 1) H.edgeCount :=
      (hIH Q hQno hQlt).trans (oddBudget_mono hQlt.le)
    have hQat : RamseyAt (cycleCode (2 * r + 3)) Q
        (oddBudget B (r + 1) H.edgeCount) :=
      ramseyAt_of_graphRamseyNumber_le hQram
    intro C
    let : DecidableRel C.Adj := Classical.decRel _
    by_cases hred : (cycleCode (2 * r + 3)).graph ⊑ C
    · exact Or.inl hred
    by_cases hblueFull : H.graph ⊑ Cᶜ
    · exact Or.inr hblueFull
    have hblueQ : Q.graph ⊑ Cᶜ := (hQat C).resolve_left hred
    let e := inducedCodeIso H (Finset.univ \ L)
    let copy : SimpleGraph.Copy
        (H.graph.induce
          ((Finset.univ \ L : Finset (Fin H.vertexCount)) : Set _)) Cᶜ :=
      hblueQ.some.comp e.toCopy
    rcases isContained_or_leaf_obstruction H hconn hn L Cᶜ hLeaves copy with
      hblueH | ⟨d, U₀, hU₀global, hU₀neighbor, _hU₀outside⟩
    · exact Or.inr hblueH
    · have hnEdge : H.vertexCount ≤ H.edgeCount + 1 := by
        simpa [GraphCode.edgeCount] using
          hconn.card_vert_le_card_edgeSet_add_one
      have hhost : 2 * H.edgeCount + (r + 1) ≤
          oddBudget B (r + 1) H.edgeCount := by
        unfold oddBudget
        omega
      have hnU₀ : H.vertexCount ≤ U₀.card := by
        apply (show H.vertexCount ≤
            oddBudget B (r + 1) H.edgeCount -
              (H.vertexCount - 1) by omega).trans
        simpa using hU₀global
      obtain ⟨S, hSU₀, hScard⟩ := Finset.exists_subset_card_eq hnU₀
      let T : Finset (Fin (oddBudget B (r + 1) H.edgeCount)) := Sᶜ
      let z := copy d
      have hzS : ∀ x ∈ S, C.Adj z x := by
        intro x hx
        have h := hU₀neighbor x (hSU₀ hx)
        simpa [z] using h
      have hcycleRaw : ¬SimpleGraph.cycleGraph (2 * r + 3) ⊑ C := by
        simpa [cycleCode] using hred
      have hfamilyRoom : (r + 1) + ((2 * r + 3) - 1) *
          (1 + 2 * (H.edgeCount + 1 - H.vertexCount)) ≤ L.card := by
        rw [hLcard]
        dsimp only [q]
        simp [oddLeafBatch, oddLeafRamseyCost, sparseExcess]
      obtain ⟨F⟩ := exists_leafObstructionFamily H hconn hn L hLeaves
        C S T z (k := 2 * r + 3) (t := r + 1) (by omega)
        hScard rfl hremain hzS hcycleRaw hblueFull hfamilyRoom
      have hTcard : T.card =
          oddBudget B (r + 1) H.edgeCount - H.vertexCount := by
        dsimp only [T]
        rw [Finset.card_compl, hScard]
        simp
      have hcommonRoom : (r + 1) * (L.card - 1) + (r + 2) ≤ T.card := by
        rw [hTcard, hLcard]
        exact oddLeafBatch_common_room
          (connected_edge_add_one_eq_vertex_add_excess H hconn)
          hm hdensity hhost
      have hblueFinal := isContained_compl_of_leafObstructionFamily
        H hconn hn L L₂ hLeaves₂ (C := C) (S := S) (T := T)
        (r := r) rfl hScard (by omega) (by omega) (by simpa using hhost)
        hcommonRoom F hcycleRaw
      exact Or.inr hblueFinal

end Erdos570
