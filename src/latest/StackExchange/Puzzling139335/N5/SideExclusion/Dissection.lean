import StackExchange.Puzzling139335.N5.SideExclusion.Generic

/-!
# Unique ownership of open bottom and left sides
-/

open Set

namespace Puzzling139335.N5

/-- A full bottom side in one piece excludes every other piece from the
open bottom side. -/
theorem bottom_open_not_mem_of_bottom_segment (d : SquareDissection)
    {i j : Fin 4} (hij : i ≠ j)
    (hseg : segment ℝ (corner 0) (corner 1) ⊆ d.piece i) {x : Plane}
    (hx : x ∈ segment ℝ (corner 0) (corner 1) \ {corner 0, corner 1}) :
    x ∉ d.piece j := by
  have hne : corner 0 ≠ corner 1 := by
    intro h
    have hcoord := congrArg (fun y : Plane => y 0) h
    norm_num [corner, Fin.ext_iff] at hcoord
  apply segment_interior_not_mem_of_same_supporting_halfspace
    (d.jordan i) (d.jordan j) (EuclideanSpace.proj (1 : Fin 2)) (c := 0)
    _ _ _ (d.disjoint_interiors hij) hne hseg rfl rfl hx
  · intro t
    exact ⟨Schoenflies.Plane.mk 0 t, rfl⟩
  · intro y hy
    exact (d.piece_subset i hy).2.1
  · intro y hy
    exact (d.piece_subset j hy).2.1

/-- A full left side in one piece excludes every other piece from the
open left side. -/
theorem left_open_not_mem_of_left_segment (d : SquareDissection)
    {i j : Fin 4} (hij : i ≠ j)
    (hseg : segment ℝ (corner 0) (corner 3) ⊆ d.piece i) {x : Plane}
    (hx : x ∈ segment ℝ (corner 0) (corner 3) \ {corner 0, corner 3}) :
    x ∉ d.piece j := by
  have hne : corner 0 ≠ corner 3 := by
    intro h
    have hcoord := congrArg (fun y : Plane => y 1) h
    norm_num [corner, Fin.ext_iff] at hcoord
  apply segment_interior_not_mem_of_same_supporting_halfspace
    (d.jordan i) (d.jordan j) (EuclideanSpace.proj (0 : Fin 2)) (c := 0)
    _ _ _ (d.disjoint_interiors hij) hne hseg rfl rfl hx
  · intro t
    exact ⟨Schoenflies.Plane.mk t 0, rfl⟩
  · intro y hy
    exact (d.piece_subset i hy).1.1
  · intro y hy
    exact (d.piece_subset j hy).1.1

/-- Every open bottom-side point has exactly the owner of the whole side. -/
theorem bottom_open_owner_iff (d : SquareDissection) (i : Fin 4)
    (hseg : segment ℝ (corner 0) (corner 1) ⊆ d.piece i) {x : Plane}
    (hx : x ∈ segment ℝ (corner 0) (corner 1) \ {corner 0, corner 1}) (j : Fin 4) :
    x ∈ d.piece j ↔ j = i := by
  constructor
  · intro hxj
    by_contra hji
    exact bottom_open_not_mem_of_bottom_segment d (Ne.symm hji) hseg hx hxj
  · rintro rfl
    exact hseg hx.1

end Puzzling139335.N5
