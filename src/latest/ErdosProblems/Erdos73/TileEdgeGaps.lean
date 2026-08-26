import ErdosProblems.Erdos73.TileGapPaths
import ErdosProblems.Erdos73.TileGapArmIntersection
import ErdosProblems.Erdos73.BrickEdgeCoordinates

/-! Normalize each pattern edge to one gap region and an endpoint-correct simple gap path. -/

namespace Erdos73
noncomputable section
open scoped Classical

open SimpleGraph Finset Erdos73Infrastructure.SimpleGraph

theorem brickWallPort_horizontal_forward {c r : ℕ} {u v : ElementaryWallVertex c r}
    (hrow : u.val.1 = v.val.1) (hcol : u.val.2.val + 1 = v.val.2.val) :
    brickWallPort u.val v.val = 1 ∧ brickWallPort v.val u.val = 0 := by
  have hlt : u.val.2.val < v.val.2.val := by omega
  have hn : ¬ v.val.2.val < u.val.2.val := by omega
  simp only [brickWallPort, if_pos hrow, if_pos hrow.symm, if_neg hn, if_pos hlt]
  exact ⟨trivial, trivial⟩

theorem brickWallPort_vertical {c r : ℕ} {u v : ElementaryWallVertex c r}
    (hrow : u.val.1 ≠ v.val.1) : brickWallPort u.val v.val = 2 := by
  simp only [brickWallPort, if_neg hrow]

namespace BrickTileArray

variable {c r C R : ℕ} (A : BrickTileArray c r C R)

def edgeGap (u v : ElementaryWallVertex c r) : Finset (ElementaryWallVertex C R) :=
  if u.val.1 = v.val.1 then
    A.horizontalGap u.val.1 (min u.val.2 v.val.2) (max u.val.2 v.val.2)
  else A.verticalGap (min u.val.1 v.val.1) (max u.val.1 v.val.1) u.val.2

theorem edgeGap_eq_horizontal {u v : ElementaryWallVertex c r}
    (hrow : u.val.1 = v.val.1) (hcol : u.val.2.val + 1 = v.val.2.val) :
    A.edgeGap u v = A.horizontalGap u.val.1 u.val.2 v.val.2 := by
  have hle : u.val.2 ≤ v.val.2 := by change u.val.2.val ≤ v.val.2.val; omega
  simp only [edgeGap, if_pos hrow, min_eq_left hle, max_eq_right hle]

theorem edgeGap_eq_vertical {u v : ElementaryWallVertex c r}
    (hrow : u.val.1.val + 1 = v.val.1.val) :
    A.edgeGap u v = A.verticalGap u.val.1 v.val.1 u.val.2 := by
  have hne : u.val.1 ≠ v.val.1 := by intro he; have hh := congrArg Fin.val he; omega
  have hle : u.val.1 ≤ v.val.1 := by change u.val.1.val ≤ v.val.1.val; omega
  simp only [edgeGap, if_neg hne, min_eq_left hle, max_eq_right hle]

theorem edgeGap_symm {u v : ElementaryWallVertex c r}
    (huv : (elementaryWall c r).Adj u v) : A.edgeGap u v = A.edgeGap v u := by
  by_cases hrow : u.val.1 = v.val.1
  · simp only [edgeGap, hrow, ite_true, min_comm, max_comm]
  · have hcol : u.val.2 = v.val.2 := by
      rcases huv with ⟨hr, _⟩ | ⟨hc, _⟩
      · exact (hrow hr).elim
      · exact hc
    simp only [edgeGap, if_neg hrow, if_neg (Ne.symm hrow), min_comm, max_comm, hcol]

theorem exists_edge_gap_path {u v : ElementaryWallVertex c r}
    (huv : (elementaryWall c r).Adj u v) :
    ∃ P : GraphPath (elementaryWall C R),
      P.source = (A.arm u (brickWallPort u.val v.val)).target ∧
      P.target = (A.arm v (brickWallPort v.val u.val)).target ∧ P.vertexSet ⊆ A.edgeGap u v := by
  have hsym := A.edgeGap_symm huv
  change (rawBrickWall c r).Adj u.val v.val at huv
  rcases huv with ⟨hr, hc⟩ | ⟨hc, hr⟩
  · rcases pathGraph_adj.mp hc with hcol | hcol
    · obtain ⟨P, hs, ht, hP⟩ := A.exists_horizontal_gap_path u v hr hcol
      have hp := brickWallPort_horizontal_forward hr hcol
      refine ⟨P, by simpa only [hp.1] using hs, by simpa only [hp.2] using ht, ?_⟩
      rw [A.edgeGap_eq_horizontal hr hcol]
      exact hP
    · obtain ⟨P, hs, ht, hP⟩ := A.exists_horizontal_gap_path v u hr.symm hcol
      have hp := brickWallPort_horizontal_forward hr.symm hcol
      refine ⟨P.reverse, by simpa only [hp.2, GraphPath.reverse_source] using ht,
        by simpa only [hp.1, GraphPath.reverse_target] using hs, ?_⟩
      rw [hsym, A.edgeGap_eq_horizontal hr.symm hcol, GraphPath.reverse_vertexSet]
      exact hP
  · rcases hr with ⟨hrow, hpar⟩ | ⟨hrow, hpar⟩
    · have hn : u.val.1 ≠ v.val.1 := by intro he; have hh := congrArg Fin.val he; omega
      obtain ⟨P, hs, ht, hP⟩ := A.exists_vertical_gap_path u v hrow hc hpar
      refine ⟨P, by simpa only [brickWallPort_vertical hn] using hs,
        by simpa only [brickWallPort_vertical (Ne.symm hn)] using ht, ?_⟩
      rw [A.edgeGap_eq_vertical hrow]
      exact hP
    · have hn : u.val.1 ≠ v.val.1 := by intro he; have hh := congrArg Fin.val he; omega
      obtain ⟨P, hs, ht, hP⟩ := A.exists_vertical_gap_path v u hrow hc.symm hpar
      refine ⟨P.reverse, by simpa only [brickWallPort_vertical hn, GraphPath.reverse_source] using ht,
        by simpa only [brickWallPort_vertical (Ne.symm hn), GraphPath.reverse_target] using hs, ?_⟩
      rw [hsym, A.edgeGap_eq_vertical hrow, GraphPath.reverse_vertexSet]
      exact hP

end BrickTileArray
end
end Erdos73
