import ErdosProblems.Erdos633.TriangleUpperModel
import ErdosProblems.Erdos633.SectorCornerCounts

/-!
# Actual corner-angle equations from congruent tilings

The unit local-sector area at every triangle vertex is half its Euclidean
angle. Substituting this identity into the geometric sector partition gives
the outer-corner angle sums with the corner counts extracted from the tiles.
-/

namespace Erdos633

open scoped BigOperators

theorem Triangle.localSectorArea_a (P : Triangle) :
    P.localSectorArea P.a = P.angleA / 2 := by
  have harea := P.localSectorArea_mapIsometry P.upperIsometry P.a (P.vertex_mem_carrier 0)
  rw [P.upperIsometry_a, P.map_upperIsometry] at harea
  calc
    P.localSectorArea P.a = P.upperModel.localSectorArea 0 := harea.symm
    _ = P.upperModel.angleA / 2 := upperTriangle_sectorArea _ _ _ _
    _ = P.angleA / 2 := by rw [P.upperModel_angleA]

theorem Triangle.localSectorArea_b (P : Triangle) :
    P.localSectorArea P.b = P.angleB / 2 := by
  calc
    P.localSectorArea P.b = P.rotate.localSectorArea P.rotate.a :=
      (P.rotate.localSectorArea_eq_of_carrier_eq P P.rotate_carrier P.rotate.a
        (P.rotate.vertex_mem_carrier 0)).symm
    _ = P.rotate.angleA / 2 := P.rotate.localSectorArea_a
    _ = P.angleB / 2 := by rw [P.angleA_rotate]

theorem Triangle.localSectorArea_c (P : Triangle) :
    P.localSectorArea P.c = P.angleC / 2 := by
  calc
    P.localSectorArea P.c = P.rotate.localSectorArea P.rotate.b :=
      (P.rotate.localSectorArea_eq_of_carrier_eq P P.rotate_carrier P.rotate.b
        (P.rotate.vertex_mem_carrier 1)).symm
    _ = P.rotate.angleB / 2 := P.rotate.localSectorArea_b
    _ = P.angleC / 2 := by rw [P.angleB_rotate]

theorem Triangle.localSectorArea_vertex (P : Triangle) (k : Fin 3) :
    P.localSectorArea (P.vertex k) = P.cornerAngle k / 2 := by
  fin_cases k
  · exact P.localSectorArea_a
  · exact P.localSectorArea_b
  · exact P.localSectorArea_c

theorem CongruentTiling.outer_angle_count_identity {P R : Triangle} {N : ℕ}
    (T : CongruentTiling P R N) (j : Fin 3) :
    ∑ k : Fin 3, (T.cornerCount (P.vertex j) k : ℝ) * R.cornerAngle k = P.cornerAngle j := by
  have h := T.outer_sector_count_identity j
  simp_rw [Triangle.localSectorArea_vertex, ← mul_div_assoc, ← Finset.sum_div] at h
  linarith

theorem CongruentTiling.outer_angleSumAt {P R : Triangle} {N : ℕ}
    (T : CongruentTiling P R N) (j : Fin 3) : T.angleSumAt (P.vertex j) = P.cornerAngle j :=
  T.outer_angle_count_identity j

theorem CongruentTiling.outer_angle_total {P R : Triangle} {N : ℕ}
    (T : CongruentTiling P R N) :
    ∑ k : Fin 3, (T.outerCornerCount k : ℝ) * R.cornerAngle k = Real.pi := by
  have h := T.outer_sector_total
  simp_rw [Triangle.localSectorArea_vertex, ← mul_div_assoc, ← Finset.sum_div] at h
  rw [P.sum_cornerAngle] at h
  linarith

end Erdos633
