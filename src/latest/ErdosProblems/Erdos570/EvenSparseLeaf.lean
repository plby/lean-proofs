/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos570.SparseLeafNumeric
import ErdosProblems.Erdos570.EvenSparseLongPath
import ErdosProblems.Erdos570.EvenLeafObstruction

/-!
# The sparse connected-target theorem for even cycles

This follows the same suspended-path/leaf-rich dichotomy as the odd branch.
In the leaf-rich branch, `r+2` repeated obstructions and `r+2` common unused
neighbors already form the forbidden `C_(2r+4)`.
-/

open scoped SimpleGraph

noncomputable section

namespace Erdos570

open Erdos79

theorem ramseyAt_evenBudget_of_sparse_connected
    {r B : ℕ} (H : GraphCode) [DecidableRel H.graph.Adj]
    (hH : NoIsolated H) (hconn : H.graph.Connected)
    (hm : oddSparseEdgeThreshold (r + 1) ≤ H.edgeCount)
    (hdensity : (oddSparseD (r + 1) - 1) * H.edgeCount <
      oddSparseD (r + 1) * H.vertexCount)
    (hIH : ∀ Q : GraphCode, NoIsolated Q → Q.edgeCount < H.edgeCount →
      graphRamseyNumber (cycleCode (2 * r + 4)) Q ≤
        oddBudget B (r + 1) Q.edgeCount) :
    RamseyAt (cycleCode (2 * r + 4)) H
      (oddBudget B (r + 1) H.edgeCount) := by
  classical
  by_cases hlong : ∃ t : ℕ, oddSparsePathLength (r + 1) ≤ t ∧
      ∃ p : Fin (t + 2) → Fin H.vertexCount,
        IsSuspendedPath H.graph p
  · obtain ⟨t, ht, p, hp⟩ := hlong
    apply ramseyAt_evenBudget_of_long_suspendedPath H hH hconn hp
    · simpa [oddSparsePathLength] using ht
    · exact hIH
  · have hleaf := twice_oddLeafBatch_le_leafVertices (r + 1) H hH hconn
      hm hdensity hlong
    let q := oddLeafBatch (r + 1) (sparseExcess H)
    have hqpos : 2 ≤ q := by
      dsimp only [q]
      unfold oddLeafBatch oddLeafRamseyCost
      have hcost : 1 ≤ (2 * (r + 1) + 2) *
          (1 + 2 * sparseExcess H) :=
        Nat.mul_pos (by omega) (by omega)
      omega
    have hqLeaf : q ≤ (leafVertices H).card := by omega
    obtain ⟨L, hLleaf, hLcard⟩ := Finset.exists_subset_card_eq hqLeaf
    have hLeaves (v : Fin H.vertexCount) (hv : v ∈ L) :
        H.graph.degree v = 1 :=
      (mem_leafVertices H v).mp (hLleaf hv)
    have hleafLe : (leafVertices H).card ≤ H.vertexCount := by
      simpa using Finset.card_le_card (Finset.subset_univ (leafVertices H))
    have htwoq : 2 * q ≤ H.vertexCount := hleaf.trans hleafLe
    have hLle : L.card ≤ H.vertexCount := by
      simpa using Finset.card_le_card (Finset.subset_univ L)
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
    have hQram : graphRamseyNumber (cycleCode (2 * r + 4)) Q ≤
        oddBudget B (r + 1) H.edgeCount :=
      (hIH Q hQno hQlt).trans (oddBudget_mono hQlt.le)
    have hQat : RamseyAt (cycleCode (2 * r + 4)) Q
        (oddBudget B (r + 1) H.edgeCount) :=
      ramseyAt_of_graphRamseyNumber_le hQram
    intro C
    letI : DecidableRel C.Adj := Classical.decRel _
    by_cases hred : (cycleCode (2 * r + 4)).graph ⊑ C
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
        simpa [z] using hU₀neighbor x (hSU₀ hx)
      have hcycleRaw : ¬SimpleGraph.cycleGraph (2 * r + 4) ⊑ C := by
        simpa [cycleCode] using hred
      have hfamilyRoom : (r + 2) + ((2 * r + 4) - 1) *
          (1 + 2 * (H.edgeCount + 1 - H.vertexCount)) ≤ L.card := by
        rw [hLcard]
        dsimp only [q]
        unfold oddLeafBatch oddLeafRamseyCost sparseExcess
        let c := 1 + 2 * (H.edgeCount + 1 - H.vertexCount)
        have hcoef : (2 * r + 4 - 1) * c ≤
            (2 * (r + 1) + 2) * c := by
          exact Nat.mul_le_mul_right c (by omega)
        calc
          r + 2 + (2 * r + 4 - 1) *
                (1 + 2 * (H.edgeCount + 1 - H.vertexCount)) ≤
              r + 2 + (2 * (r + 1) + 2) *
                (1 + 2 * (H.edgeCount + 1 - H.vertexCount)) := by
            exact Nat.add_le_add_left (by simpa [c] using hcoef) _
          _ = r + 1 + 1 + (2 * (r + 1) + 2) *
                (1 + 2 * (H.edgeCount + 1 - H.vertexCount)) := by omega
      obtain ⟨F⟩ := exists_leafObstructionFamily H hconn hn L hLeaves
        C S T z (k := 2 * r + 4) (t := r + 2) (by omega)
        hScard rfl hremain hzS hcycleRaw hblueFull hfamilyRoom
      have hTcard : T.card =
          oddBudget B (r + 1) H.edgeCount - H.vertexCount := by
        dsimp only [T]
        rw [Finset.card_compl, hScard]
        simp
      have hcommonRoom : (r + 2) * (L.card - 1) + (r + 2) ≤ T.card := by
        rw [hTcard, hLcard]
        have hhostSucc : 2 * H.edgeCount + ((r + 1) + 1) ≤
            oddBudget B (r + 1) H.edgeCount + 1 := by omega
        have hc := oddLeafBatch_common_room
          (r := r + 1)
          (m := H.edgeCount) (n := H.vertexCount)
          (N := oddBudget B (r + 1) H.edgeCount + 1)
          (x := sparseExcess H)
          (connected_edge_add_one_eq_vertex_add_excess H hconn)
          hm hdensity hhostSucc
        have hnHost : H.vertexCount ≤
            oddBudget B (r + 1) H.edgeCount := by omega
        have hsubSucc :
            oddBudget B (r + 1) H.edgeCount + 1 - H.vertexCount =
              (oddBudget B (r + 1) H.edgeCount - H.vertexCount) + 1 := by
          omega
        rw [hsubSucc] at hc
        have hcoefEq : r + 1 + 1 = r + 2 := by omega
        rw [hcoefEq] at hc
        dsimp only [q]
        omega
      have hcommonCard : r + 2 ≤ (commonPart F.unused T).card := by
        have hbase := commonPart_card_ge F.unused T F.outside_large
        have hsub : r + 2 ≤ T.card - (r + 2) * (L.card - 1) :=
          Nat.le_sub_of_add_le (by
            simpa [add_comm] using hcommonRoom)
        exact hsub.trans hbase
      exact (hcycleRaw
        (by
          have hc := leafObstructionFamily_contains_even_cycle
            (h := r + 2) (by omega) F hcommonCard
          have hlen : 2 * (r + 2) = 2 * r + 4 := by omega
          rw [hlen] at hc
          exact hc)).elim

end Erdos570
