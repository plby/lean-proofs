import Wikipedia.HopfProblem.CuspComplementOuterBoundaryLevel
import Wikipedia.HopfProblem.CuspComplementOuterBoundaryAttachment
import Wikipedia.HopfProblem.CuspComplementOuterBoundaryFrontier

/-!
# The marked outer boundary of the actual carved cusp cap

The full original cusp mapping torus parametrizes the genuine frontier
of the actual compact cap. Its map is exactly the original cusp inclusion
at half the filling radius and exactly the original regular attachment
at that same height. The cylinder keeps all four period coordinates,
including the delta shear. The image is disjoint from the fixed closed
normal disk and lies in the actual compact carved cap.
-/

noncomputable section

open Set Topology
open scoped Matrix

namespace Wikipedia.HopfProblem.CuspComplement.OuterBoundary

open SpecialPeriods SpecialPeriods.Threefold SpecialPeriods.CuspFamily
open ThreefoldOverlapMappingTorus ThreefoldOverlapMappingTorus.Cusp CuspUniformization

local notation "CD" => CuspGeometry.data

/-- The logarithmic height of the specified actual outer cap radius. -/
def capHeight : Height (CD).radius :=
  heightAtRadius (CD) capRadius capRadius_pos capRadius_lt_cuspRadius

theorem capHeight_exp : Real.exp (-2 * Real.pi * (capHeight : ℝ)) = capRadius :=
  heightAtRadius_exp (CD) capRadius capRadius_pos capRadius_lt_cuspRadius

/-- The full-monodromy boundary is homeomorphic to the actual outer level in the threefold. -/
def outerBoundaryHomeomorph : ThreefoldOverlapMappingTorus.Cusp.Boundary ≃ₜ outerBoundary :=
  (levelHomeomorph (CD) capRadius capRadius_pos capRadius_lt_cuspRadius).trans
    (CuspGeometry.inclusion_openEmbedding.isEmbedding.homeomorphImage
      {q : CuspGeometry.LocalSpace | ‖CuspGeometry.parameter q‖ = capRadius})

/-- The forward map is the preexisting native boundary inclusion, with the same actual height. -/
@[simp] theorem outerBoundaryHomeomorph_coe (q : ThreefoldOverlapMappingTorus.Cusp.Boundary) :
    (outerBoundaryHomeomorph q : Threefold.Space) =
      CuspGeometry.inclusion (CuspBoundaryToricExtension.boundaryToFull (CD) capHeight q) := rfl

/-- The unchanged map from the full rank-four mapping torus into the original threefold. -/
def outerBoundaryMap (q : ThreefoldOverlapMappingTorus.Cusp.Boundary) : Threefold.Space :=
  CuspGeometry.inclusion (CuspBoundaryToricExtension.boundaryToFull (CD) capHeight q)

@[simp] theorem outerBoundaryMap_range : range outerBoundaryMap = outerBoundary :=
  outerBoundaryHomeomorph.surjective.range_comp
    (Subtype.val : outerBoundary → Threefold.Space) |>.trans Subtype.range_val

theorem outerBoundaryMap_isClosedEmbedding : IsClosedEmbedding outerBoundaryMap :=
  outerBoundary_isClosed.isClosedEmbedding_subtypeVal.comp outerBoundaryHomeomorph.isClosedEmbedding

/-- The same homeomorphism with the literal topological frontier as target. -/
def capFrontierHomeomorph : ThreefoldOverlapMappingTorus.Cusp.Boundary ≃ₜ frontier cap :=
  outerBoundaryHomeomorph.trans (Homeomorph.setCongr frontier_cap.symm)

@[simp] theorem capFrontierHomeomorph_coe (q : ThreefoldOverlapMappingTorus.Cusp.Boundary) :
    (capFrontierHomeomorph q : Threefold.Space) = outerBoundaryMap q := rfl

theorem outerBoundaryMap_time (q : ThreefoldOverlapMappingTorus.Cusp.Boundary) :
    ‖CuspGeometry.cuspCoordinate (outerBoundaryMap q)‖ = capRadius :=
  outerBoundary_time (outerBoundaryHomeomorph q).property

theorem outerBoundaryMap_mem_capComplement (q : ThreefoldOverlapMappingTorus.Cusp.Boundary) :
    outerBoundaryMap q ∈ capComplement :=
  outerBoundary_subset_capComplement (outerBoundaryHomeomorph q).property

theorem outerBoundaryMap_not_mem_closedDiskNeighborhood
    (q : ThreefoldOverlapMappingTorus.Cusp.Boundary) :
    outerBoundaryMap q ∉ CuspCircleNormalTrivialization.closedDiskNeighborhood :=
  outerBoundary_not_mem_closedDiskNeighborhood (outerBoundaryHomeomorph q).property

/-- The original cusp and regular attachments agree at the actual selected outer level. -/
theorem outerBoundaryMap_eq_regular (q : ThreefoldOverlapMappingTorus.Cusp.Boundary) :
    outerBoundaryMap q = inclusion none (TrianglePeriodFamily.Boundary.Cusp.heightBoundaryMap
      capHeight q) :=
  boundaryToFull_ambient_eq_regular capHeight q

/-- Every real-cylinder point has exactly its original full rank-four regular-fibre coordinate. -/
theorem outerBoundaryMap_mk_eq_regular (t : ℝ) (x : RealTorus₄) :
    outerBoundaryMap (MappingTorus.mk monodromy (t, x)) =
      inclusion none (boundaryRegularData.quotient
        (TrianglePeriodFamily.Boundary.Cusp.baseLift capHeight t, x)) :=
  boundaryToFull_ambient_mk capHeight t x

/-- The whole native toric exponential formula, with the actual varying real period matrix. -/
theorem outerBoundaryMap_realCoordinates (t : ℝ) (x : RealPlane₄) :
    outerBoundaryMap (MappingTorus.mk monodromy (t, standardLattice.mkQ x)) =
      CuspGeometry.inclusion
        ((puncturedCuspCover (CD).correction (CD).radius
          ⟨((logPoint (CD).radius (CD).radius_pos t capHeight : ℂ),
            (CD).periods.periodEquiv (logPoint (CD).radius (CD).radius_pos t capHeight) x),
            (logPoint (CD).radius (CD).radius_pos t capHeight).property⟩).val) :=
  congrArg CuspGeometry.inclusion
    (levelHomeomorph_realCoordinates (CD) capRadius capRadius_pos capRadius_lt_cuspRadius t x)

/-- The full original `M₀` endpoint gluing remains on the actual outer boundary. -/
theorem outerBoundaryMap_endpoint (t : ℝ) (x : RealTorus₄) :
    outerBoundaryMap (MappingTorus.mk monodromy (t + 1, x)) =
      outerBoundaryMap (MappingTorus.mk monodromy (t, monodromy x)) :=
  congrArg outerBoundaryMap (MappingTorus.mk_add_one monodromy t x)

/-- In the original order `(γ,u,w,δ)`, the last coordinate changes by `−γ`. -/
theorem outerBoundaryMap_endpoint_realCoordinates (t : ℝ) (x : RealPlane₄) :
    outerBoundaryMap (MappingTorus.mk monodromy (t + 1, standardLattice.mkQ x)) =
      outerBoundaryMap (MappingTorus.mk monodromy
        (t, standardLattice.mkQ ![x 0, x 1, x 2 + x 1, x 3 - x 0])) := by
  rw [outerBoundaryMap_endpoint]
  change outerBoundaryMap (MappingTorus.mk monodromy
    (t, cuspTorusHomeomorph 1 (standardLattice.mkQ x))) = _
  rw [cuspTorusHomeomorph_mkQ, cuspRealEquiv_coordinates]
  simp only [Int.cast_one, one_mul]

theorem outerBoundaryMap_parameter (t : ℝ) (x : RealTorus₄) :
    CuspGeometry.cuspCoordinate (outerBoundaryMap (MappingTorus.mk monodromy (t, x))) =
      exponential ((t : ℂ) + (capHeight : ℝ) * Complex.I) := by
  exact (CuspGeometry.cuspCoordinate_inclusion
    (CuspBoundaryToricExtension.boundaryToFull (CD) capHeight
      (MappingTorus.mk monodromy (t, x)))).trans (boundaryCylinder_base (CD) capHeight t x)

end Wikipedia.HopfProblem.CuspComplement.OuterBoundary
