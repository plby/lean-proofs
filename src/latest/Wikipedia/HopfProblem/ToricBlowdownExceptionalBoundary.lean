import Wikipedia.HopfProblem.ToricBlowdownLocal
import Wikipedia.HopfProblem.ProjectivePlanePunctured
import Wikipedia.HopfProblem.CuspBoundaryIdentifications

/-!
# The exceptional fibres are the odd hexagon boundary curves

The three exceptional rays are the odd rays of the hexagonal star.  The
six affine formulae for the blow-down identify its fibres over the three
projective coordinate points with the corresponding actual boundary
subspaces of the central component.
-/

noncomputable section

open Set Topology
open scoped ContDiff Matrix

namespace Wikipedia.HopfProblem.ToricComponent

open ToricCharts ToricFan ToricSpace Triangle

/-- The rays subdividing the three cones of the projective-plane fan. -/
def exceptionalRay (k : Fin 3) : Fin 2 → ℤ := hexagonRay (blowupIndex k true)

theorem exceptionalRay_ne_zero (k : Fin 3) : exceptionalRay k ≠ 0 :=
  hexagonRay_ne_zero _

theorem exceptionalRay_injective : Function.Injective exceptionalRay := by decide

/-- On each of the six affine charts, the exceptional-fibre equation is
exactly the equation of the indicated boundary curve. -/
theorem zeroChartBlowdown_eq_coordinatePoint_iff_boundary
    (k : Fin 3) (i : Fin 6) (z : CoordinateSpace 2) :
    zeroChartBlowdown i z = ProjectivePlane.coordinatePoint k ↔
      inclusion (zeroTriangle i) (insertZero (zeroCoordinate i) z) ∈
        rayDivisor (exceptionalRay k) := by
  change ProjectivePlane.affineMap (blowdownIndex i) (blowdownCoordinates i z) = _ ↔ _
  rw [ProjectivePlane.affineMap_eq_coordinatePoint_iff, mem_rayDivisor_inclusion,
    zeroChartVector]
  fin_cases k <;> fin_cases i <;>
    norm_num [blowdownIndex, blowdownCoordinates, exceptionalRay, blowupIndex,
      hexagonRay, zeroTriangle, vertex, rays, Fin.exists_fin_succ, funext_iff,
      Fin.forall_fin_succ, Matrix.cons_val, mul_eq_zero] <;> aesop

/-- The complete fibre of the global blow-down over a coordinate point
is the boundary component indexed by the corresponding odd hexagon ray. -/
theorem blowdown_fibre_eq_componentBoundary (k : Fin 3) :
    blowdown ⁻¹' {ProjectivePlane.coordinatePoint k} =
      CuspQuotient.componentBoundary (exceptionalRay k) := by
  ext x
  obtain ⟨c, z, rfl⟩ := affineInclusion_jointly_surjective x
  obtain ⟨i, rfl⟩ := zeroChart_surjective c
  change blowdown (affineInclusion (zeroChart i) z) = ProjectivePlane.coordinatePoint k ↔
    inclusion (zeroTriangle i) (insertZero (zeroCoordinate i) z) ∈
      rayDivisor (exceptionalRay k)
  rw [blowdown_zeroChart]
  exact zeroChartBlowdown_eq_coordinatePoint_iff_boundary k i z

theorem blowdown_eq_coordinatePoint_iff_mem_boundary (k : Fin 3) (x : rayDivisor 0) :
    blowdown x = ProjectivePlane.coordinatePoint k ↔
      x ∈ CuspQuotient.componentBoundary (exceptionalRay k) := by
  change x ∈ blowdown ⁻¹' {ProjectivePlane.coordinatePoint k} ↔ _
  rw [blowdown_fibre_eq_componentBoundary]

/-- The inverse image of the three centers is precisely the union of
the three odd boundary curves. -/
theorem blowdown_preimage_coordinatePoints :
    blowdown ⁻¹' ProjectivePlane.coordinatePoints =
      ⋃ k : Fin 3, CuspQuotient.componentBoundary (exceptionalRay k) := by
  ext x
  constructor
  · rintro ⟨k, hk⟩
    exact mem_iUnion.mpr ⟨k, (blowdown_eq_coordinatePoint_iff_mem_boundary k x).mp hk.symm⟩
  · intro hx
    obtain ⟨k, hk⟩ := mem_iUnion.mp hx
    exact ⟨k, ((blowdown_eq_coordinatePoint_iff_mem_boundary k x).mpr hk).symm⟩

/-- Distinct exceptional boundary curves are disjoint. -/
theorem exceptional_componentBoundary_pairwiseDisjoint :
    Pairwise (fun k l : Fin 3 =>
      Disjoint (CuspQuotient.componentBoundary (exceptionalRay k))
        (CuspQuotient.componentBoundary (exceptionalRay l))) := by
  intro k l hkl
  apply Set.disjoint_left.mpr
  intro x hxk hxl
  apply hkl
  apply ProjectivePlane.coordinatePoint_injective
  exact ((blowdown_eq_coordinatePoint_iff_mem_boundary k x).mpr hxk).symm.trans
    ((blowdown_eq_coordinatePoint_iff_mem_boundary l x).mpr hxl)

end Wikipedia.HopfProblem.ToricComponent
