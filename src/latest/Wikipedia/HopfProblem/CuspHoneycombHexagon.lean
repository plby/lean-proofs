import Wikipedia.HopfProblem.CuspHoneycombHexagonSquares
import Wikipedia.HopfProblem.CuspHoneycombHexagonPolygon
import Wikipedia.HopfProblem.CuspHoneycombHexagonGluing

/-!
# The actual positive zero component is a closed hexagon

The homeomorphism is obtained from the six compact squares of the actual
toric component. Both its continuity and its inverse continuity use their
proved quotient topology, and injectivity uses the exact monomial overlap
relations. The six sides correspond to the literal intersections with
the six neighboring components.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.CuspHoneycombHexagon

/-- The explicit planar tiling, with values in the literal closed hexagon. -/
def polygonProjection (p : TileSpace) : Hexagon :=
  ⟨tile p.1 p.2, tile_mem_hexagon p.1 p.2⟩

theorem polygonProjection_continuous : Continuous polygonProjection :=
  (continuous_prod_of_discrete_left.mpr tile_continuous).subtype_mk _

theorem polygonProjection_surjective : Function.Surjective polygonProjection := by
  intro x
  obtain ⟨i, p, hp⟩ := tile_jointly_surjective x
  exact ⟨(i, p), Subtype.ext hp⟩

/-- The identifications of actual toric points are precisely those of the
displayed planar quadrilateral tiles. -/
theorem squareProjection_eq_iff_polygonProjection_eq (a b : TileSpace) :
    squareProjection a = squareProjection b ↔ polygonProjection a = polygonProjection b := by
  change squarePoint a.1 a.2 = squarePoint b.1 b.2 ↔ _
  rw [squarePoint_eq_iff, Subtype.ext_iff]
  exact (tile_eq_iff a.1 b.1 a.2 b.2).symm

/-- The positive fixed locus in the actual zero component, with its original
subspace topology, is homeomorphic to an explicit closed planar hexagon. -/
def positiveE0HexagonHomeomorph : PositiveE0 ≃ₜ Hexagon :=
  CommonFibres.homeomorph squareProjection polygonProjection
    squareProjection_surjective squareProjection_continuous
    polygonProjection_continuous polygonProjection_surjective
    squareProjection_eq_iff_polygonProjection_eq

/-- This homeomorphism has the displayed piecewise-linear formula on each
of the six actual positive toric coordinate squares. -/
@[simp] theorem positiveE0HexagonHomeomorph_squarePoint (i : Fin 6) (p : Square) :
    (positiveE0HexagonHomeomorph (squarePoint i p) : Plane) = tile i p := by
  exact congrArg Subtype.val (CommonFibres.homeomorph_apply
    squareProjection polygonProjection squareProjection_surjective
    squareProjection_continuous polygonProjection_continuous
    polygonProjection_surjective squareProjection_eq_iff_polygonProjection_eq (i, p))

@[simp] theorem positiveE0HexagonHomeomorph_cornerZero (i : Fin 6) :
    (positiveE0HexagonHomeomorph (squarePoint i cornerZero) : Plane) = vertex i := by
  simp

@[simp] theorem positiveE0HexagonHomeomorph_cornerOne (i : Fin 6) :
    (positiveE0HexagonHomeomorph (squarePoint i cornerOne) : Plane) = 0 := by
  simp

/-- The six polygon vertices are the actual all-zero toric triple points. -/
@[simp] theorem squarePoint_cornerZero_coe (i : Fin 6) :
    ((squarePoint i cornerZero : ToricSpace.rayDivisor 0) : ToricSpace.Space) =
      ToricSpace.inclusion (ToricComponent.zeroTriangle i) 0 := by
  rw [squarePoint_coe, chartPoint_coe]
  congr 1
  ext k
  rcases coordinates_exhaustive i k with rfl | rfl | rfl <;> simp [cornerZero]

theorem squarePoint_cornerZero_mem_positiveBoundary_iff (i k : Fin 6) :
    squarePoint i cornerZero ∈ positiveBoundary k ↔ k = i ∨ k = i + 1 := by
  rw [squarePoint_mem_positiveBoundary_iff]
  simp [cornerZero]

theorem squarePoint_cornerOne_not_mem_positiveBoundary (i k : Fin 6) :
    squarePoint i cornerOne ∉ positiveBoundary k := by
  rw [squarePoint_mem_positiveBoundary_iff]
  simp [cornerOne]

/-- Side membership is exactly the original neighboring-component condition,
not a newly assigned boundary of an abstract disk. -/
theorem positiveE0HexagonHomeomorph_mem_side_iff (x : PositiveE0) (k : Fin 6) :
    (positiveE0HexagonHomeomorph x : Plane) ∈ side k ↔ x ∈ positiveBoundary k := by
  obtain ⟨i, p, rfl⟩ := squarePoint_jointly_surjective x
  rw [positiveE0HexagonHomeomorph_squarePoint, tile_mem_side_iff,
    squarePoint_mem_positiveBoundary_iff]

theorem positiveE0HexagonHomeomorph_mem_boundary_iff (x : PositiveE0) :
    (positiveE0HexagonHomeomorph x : Plane) ∈ ⋃ k, side k ↔
      x ∈ ⋃ k, positiveBoundary k := by
  simp only [Set.mem_iUnion]
  exact exists_congr (fun k => positiveE0HexagonHomeomorph_mem_side_iff x k)

/-- Restriction to one of the six literal neighboring-component intersections. -/
def positiveBoundaryHexagonHomeomorph (k : Fin 6) : positiveBoundary k ≃ₜ side k where
  toFun x := ⟨(positiveE0HexagonHomeomorph x.1 : Plane),
    (positiveE0HexagonHomeomorph_mem_side_iff x.1 k).mpr x.2⟩
  invFun y := ⟨positiveE0HexagonHomeomorph.symm ⟨y.1, y.2.1⟩, by
    apply (positiveE0HexagonHomeomorph_mem_side_iff _ k).mp
    simpa only [Homeomorph.apply_symm_apply] using y.2⟩
  left_inv x := Subtype.ext (positiveE0HexagonHomeomorph.symm_apply_apply x.1)
  right_inv y := by
    apply Subtype.ext
    change (positiveE0HexagonHomeomorph
      (positiveE0HexagonHomeomorph.symm ⟨y.1, y.2.1⟩) : Plane) = y.1
    rw [Homeomorph.apply_symm_apply]
  continuous_toFun := (continuous_subtype_val.comp
    (positiveE0HexagonHomeomorph.continuous.comp continuous_subtype_val)).subtype_mk _
  continuous_invFun := (positiveE0HexagonHomeomorph.symm.continuous.comp
    (continuous_subtype_val.subtype_mk _)).subtype_mk _

@[simp] theorem positiveBoundaryHexagonHomeomorph_apply (k : Fin 6)
    (x : positiveBoundary k) :
    (positiveBoundaryHexagonHomeomorph k x : Plane) =
      (positiveE0HexagonHomeomorph x.1 : Plane) := rfl

end Wikipedia.HopfProblem.CuspHoneycombHexagon
