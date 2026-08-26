import ErdosProblems.Erdos73.TileGapRegions
import ErdosProblems.Erdos73.BrickColumnPathsClipped

/-! Actual simple paths across the reserved horizontal and vertical tile gaps. -/

namespace Erdos73.BrickTileArray
noncomputable section
open scoped Classical

open SimpleGraph Finset Erdos73Infrastructure.SimpleGraph

variable {c r C R : ℕ} (A : BrickTileArray c r C R)

theorem exists_horizontal_gap_path (u v : ElementaryWallVertex c r)
    (hrow : u.val.1 = v.val.1) (hcol : u.val.2.val + 1 = v.val.2.val) :
    ∃ P : GraphPath (elementaryWall C R),
      P.source = (A.arm u 1).target ∧ P.target = (A.arm v 0).target ∧
      P.vertexSet ⊆ A.horizontalGap u.val.1 u.val.2 v.val.2 := by
  have hu := A.arm_one_target_coordinates u
  have hv := A.arm_zero_target_coordinates v
  have hcols := A.column_strictMono (show u.val.2 < v.val.2 by change u.val.2.val < v.val.2.val; omega)
  have hrows := congrArg A.row hrow
  have hportrow : (A.arm u 1).target.val.1 = (A.arm v 0).target.val.1 := Fin.ext (by omega)
  obtain ⟨P, hs, ht, hP⟩ := exists_brick_horizontal_path_bounded
    (A.arm u 1).target (A.arm v 0).target hportrow
    (16 * A.column u.val.2 + 10) (16 * A.column v.val.2 + 2) (by omega) (by omega)
  refine ⟨P, hs, ht, ?_⟩
  intro w hw
  obtain ⟨hr, hl, hh⟩ := hP w hw
  exact A.mem_horizontalGap.mpr ⟨(congrArg Fin.val hr).trans hu.1, hl, hh⟩

theorem exists_vertical_gap_path (u v : ElementaryWallVertex c r)
    (hrow : u.val.1.val + 1 = v.val.1.val) (hcol : u.val.2 = v.val.2)
    (hdown : (u.val.2.val + u.val.1.val) % 2 = 1) :
    ∃ P : GraphPath (elementaryWall C R),
      P.source = (A.arm u 2).target ∧ P.target = (A.arm v 2).target ∧
      P.vertexSet ⊆ A.verticalGap u.val.1 v.val.1 u.val.2 := by
  have hup : (v.val.2.val + v.val.1.val) % 2 ≠ 1 := by
    have hh := congrArg Fin.val hcol
    omega
  have hu := A.arm_two_target_coordinates u
  have hv := A.arm_two_target_coordinates v
  simp only [if_pos hdown] at hu
  simp only [if_neg hup, Nat.add_zero] at hv
  have hrows := A.row_strictMono (show u.val.1 < v.val.1 by change u.val.1.val < v.val.1.val; omega)
  have hcols := congrArg A.column hcol
  have hboundr := A.row_bound v.val.1
  have hboundc := A.column_bound u.val.2
  obtain ⟨P, hPs, hPsc, hPt, hPtc, hP⟩ := exists_brick_column_path_clipped
    (c := C) (r := R) (12 * A.row u.val.1 + 8) (12 * A.row v.val.1)
    (8 * A.column u.val.2 + 3) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega)
  refine ⟨P, ?_, ?_, ?_⟩
  · exact Subtype.ext (Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega)))
  · exact Subtype.ext (Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega)))
  · intro w hw
    have hh := hP w hw
    apply A.mem_verticalGap.mpr
    omega

end
end Erdos73.BrickTileArray
