import Wikipedia.HopfProblem.EllipticHigherHomologyCoverIndicesCore

/-!
# Actual degree-two and degree-three period-cover images

The actual covering's Wang boundary is the actual finite homology norm.
Its primitive invariant coordinate therefore has image `ℤ` for the
order-three twist and `2ℤ` for the order-four twist.  The already proved
primitive first-axis classes determine the full image in the marked
surface homology.  Transport back to the original homology object gives
the actual covering cokernel and index, not only a matrix surrogate.
-/

noncomputable section

namespace Wikipedia.HopfProblem.Elliptic.HigherHomology

open SingularMayerVietoris PeriodTorusHigherHomology MappingTorusHomology

/-- The actual second-homology covering coordinate is the primitive
coordinate of the norm of its actual split-circle boundary. -/
theorem surfacePeriodCoverH2Coordinates_secondMap (j : Kind) (p : FixedPeriod j) :
    CoverAlgebra.secondMap (surfacePeriodCoverH2Coordinates j p) =
      (fibreHomologyNormOneCoordinate j).comp (surfacePeriodCoverCircleBoundary j p 1) := by
  ext a
  change mappingTorusH2Equiv j
    (surfaceMappingTorusHomologyEquiv j p 2
      (singularHomologyMap (periodCover j p j.twist (mainTwist_admissible j)) 2 a)) 1 = _
  rw [mappingTorusH2Equiv_boundary, surfacePeriodCover_wangBoundary]
  rfl

/-- The actual third-homology covering coordinate is the corresponding
primitive second-exterior-degree norm coordinate. -/
theorem surfacePeriodCoverH3Coordinates_secondMap (j : Kind) (p : FixedPeriod j) :
    CoverAlgebra.secondMap (surfacePeriodCoverH3Coordinates j p) =
      (fibreHomologyNormTwoCoordinate j).comp (surfacePeriodCoverCircleBoundary j p 2) := by
  ext a
  change mappingTorusH3Equiv j
    (surfaceMappingTorusHomologyEquiv j p 3
      (singularHomologyMap (periodCover j p j.twist (mainTwist_admissible j)) 3 a)) 1 = _
  rw [mappingTorusH3Equiv_boundary, surfacePeriodCover_wangBoundary]
  rfl

/-- The exact second-coordinate image is obtained from a genuinely surjective boundary. -/
theorem surfacePeriodCoverH2Coordinates_secondMap_range (j : Kind) (p : FixedPeriod j) :
    LinearMap.range (CoverAlgebra.secondMap (surfacePeriodCoverH2Coordinates j p)) =
      Submodule.span ℤ {(fibreNormIndex j : ℤ)} := by
  rw [surfacePeriodCoverH2Coordinates_secondMap,
    cover_range_comp_of_surjective _ _ (surfacePeriodCoverCircleBoundary_surjective j p 1),
    fibreHomologyNormOneCoordinate_range]

theorem surfacePeriodCoverH3Coordinates_secondMap_range (j : Kind) (p : FixedPeriod j) :
    LinearMap.range (CoverAlgebra.secondMap (surfacePeriodCoverH3Coordinates j p)) =
      Submodule.span ℤ {(fibreNormIndex j : ℤ)} := by
  rw [surfacePeriodCoverH3Coordinates_secondMap,
    cover_range_comp_of_surjective _ _ (surfacePeriodCoverCircleBoundary_surjective j p 2),
    fibreHomologyNormTwoCoordinate_range]

/-- The complete actual degree-two image in the proved surface marking. -/
theorem surfacePeriodCoverH2Coordinates_range (j : Kind) (p : FixedPeriod j) :
    LinearMap.range (surfacePeriodCoverH2Coordinates j p) =
      CoverAlgebra.divisibleSecond (fibreNormIndex j) :=
  CoverAlgebra.range_eq_divisibleSecond _ (surfacePeriodCoverH2Coordinates_firstAxis j p) _
    (surfacePeriodCoverH2Coordinates_secondMap_range j p)

/-- The complete actual degree-three image in the proved surface marking. -/
theorem surfacePeriodCoverH3Coordinates_range (j : Kind) (p : FixedPeriod j) :
    LinearMap.range (surfacePeriodCoverH3Coordinates j p) =
      CoverAlgebra.divisibleSecond (fibreNormIndex j) :=
  CoverAlgebra.range_eq_divisibleSecond _ (surfacePeriodCoverH3Coordinates_firstAxis j p) _
    (surfacePeriodCoverH3Coordinates_secondMap_range j p)

theorem surfacePeriodCoverH2Coordinates_range_iff (j : Kind) (p : FixedPeriod j)
    (v : Fin 2 → ℤ) :
    v ∈ LinearMap.range (surfacePeriodCoverH2Coordinates j p) ↔
      (fibreNormIndex j : ℤ) ∣ v 1 := by
  rw [surfacePeriodCoverH2Coordinates_range, CoverAlgebra.mem_divisibleSecond_iff]

theorem surfacePeriodCoverH3Coordinates_range_iff (j : Kind) (p : FixedPeriod j)
    (v : Fin 2 → ℤ) :
    v ∈ LinearMap.range (surfacePeriodCoverH3Coordinates j p) ↔
      (fibreNormIndex j : ℤ) ∣ v 1 := by
  rw [surfacePeriodCoverH3Coordinates_range, CoverAlgebra.mem_divisibleSecond_iff]

/-- The marked actual second-homology cokernel is reduction of the
second coordinate modulo the calculated one-or-two index. -/
def surfacePeriodCoverH2CoordinatesCokernelEquivZMod (j : Kind) (p : FixedPeriod j) :
    ((Fin 2 → ℤ) ⧸ LinearMap.range (surfacePeriodCoverH2Coordinates j p)) ≃ₗ[ℤ]
      ZMod (fibreNormIndex j) :=
  CoverAlgebra.cokernelEquivZMod _ (surfacePeriodCoverH2Coordinates_firstAxis j p) _
    (surfacePeriodCoverH2Coordinates_secondMap_range j p)

def surfacePeriodCoverH3CoordinatesCokernelEquivZMod (j : Kind) (p : FixedPeriod j) :
    ((Fin 2 → ℤ) ⧸ LinearMap.range (surfacePeriodCoverH3Coordinates j p)) ≃ₗ[ℤ]
      ZMod (fibreNormIndex j) :=
  CoverAlgebra.cokernelEquivZMod _ (surfacePeriodCoverH3Coordinates_firstAxis j p) _
    (surfacePeriodCoverH3Coordinates_secondMap_range j p)

@[simp] theorem surfacePeriodCoverH2CoordinatesCokernelEquivZMod_mk
    (j : Kind) (p : FixedPeriod j) (v : Fin 2 → ℤ) :
    surfacePeriodCoverH2CoordinatesCokernelEquivZMod j p (Submodule.Quotient.mk v) =
      (v 1 : ZMod (fibreNormIndex j)) := rfl

@[simp] theorem surfacePeriodCoverH3CoordinatesCokernelEquivZMod_mk
    (j : Kind) (p : FixedPeriod j) (v : Fin 2 → ℤ) :
    surfacePeriodCoverH3CoordinatesCokernelEquivZMod j p (Submodule.Quotient.mk v) =
      (v 1 : ZMod (fibreNormIndex j)) := rfl

theorem surfacePeriodCoverH2Coordinates_range_index (j : Kind) (p : FixedPeriod j) :
    (LinearMap.range (surfacePeriodCoverH2Coordinates j p)).toAddSubgroup.index =
      fibreNormIndex j :=
  CoverAlgebra.range_index _ (surfacePeriodCoverH2Coordinates_firstAxis j p) _
    (surfacePeriodCoverH2Coordinates_secondMap_range j p)

theorem surfacePeriodCoverH3Coordinates_range_index (j : Kind) (p : FixedPeriod j) :
    (LinearMap.range (surfacePeriodCoverH3Coordinates j p)).toAddSubgroup.index =
      fibreNormIndex j :=
  CoverAlgebra.range_index _ (surfacePeriodCoverH3Coordinates_firstAxis j p) _
    (surfacePeriodCoverH3Coordinates_secondMap_range j p)

/-- The quotient of the actual second surface homology by the actual
period-cover image is the indicated finite residue module. -/
def surfacePeriodCoverH2CokernelEquivZMod (j : Kind) (p : FixedPeriod j) :
    (SingularHomology (Surface j p j.twist (mainTwist_admissible j)) 2 ⧸
      LinearMap.range (singularHomologyMap
        (periodCover j p j.twist (mainTwist_admissible j)) 2)) ≃ₗ[ℤ]
      ZMod (fibreNormIndex j) :=
  (coverCokernelCoordinatesEquiv
    (singularHomologyMap (periodCover j p j.twist (mainTwist_admissible j)) 2)
    (surfaceH2Equiv j p)).trans (surfacePeriodCoverH2CoordinatesCokernelEquivZMod j p)

/-- The same actual cokernel description holds in degree three. -/
def surfacePeriodCoverH3CokernelEquivZMod (j : Kind) (p : FixedPeriod j) :
    (SingularHomology (Surface j p j.twist (mainTwist_admissible j)) 3 ⧸
      LinearMap.range (singularHomologyMap
        (periodCover j p j.twist (mainTwist_admissible j)) 3)) ≃ₗ[ℤ]
      ZMod (fibreNormIndex j) :=
  (coverCokernelCoordinatesEquiv
    (singularHomologyMap (periodCover j p j.twist (mainTwist_admissible j)) 3)
    (surfaceH3Equiv j p)).trans (surfacePeriodCoverH3CoordinatesCokernelEquivZMod j p)

@[simp] theorem surfacePeriodCoverH2CokernelEquivZMod_mk (j : Kind) (p : FixedPeriod j)
    (a : SingularHomology (Surface j p j.twist (mainTwist_admissible j)) 2) :
    surfacePeriodCoverH2CokernelEquivZMod j p (Submodule.Quotient.mk a) =
      (surfaceH2Equiv j p a 1 : ZMod (fibreNormIndex j)) := rfl

@[simp] theorem surfacePeriodCoverH3CokernelEquivZMod_mk (j : Kind) (p : FixedPeriod j)
    (a : SingularHomology (Surface j p j.twist (mainTwist_admissible j)) 3) :
    surfacePeriodCoverH3CokernelEquivZMod j p (Submodule.Quotient.mk a) =
      (surfaceH3Equiv j p a 1 : ZMod (fibreNormIndex j)) := rfl

/-- The actual degree-two covering image has index one or two. -/
theorem surfacePeriodCover_h2_range_index (j : Kind) (p : FixedPeriod j) :
    (LinearMap.range (singularHomologyMap
      (periodCover j p j.twist (mainTwist_admissible j)) 2)).toAddSubgroup.index =
      fibreNormIndex j := by
  rw [cover_range_index_coordinates _ (surfaceH2Equiv j p)]
  exact surfacePeriodCoverH2Coordinates_range_index j p

/-- The actual degree-three covering image has the same index. -/
theorem surfacePeriodCover_h3_range_index (j : Kind) (p : FixedPeriod j) :
    (LinearMap.range (singularHomologyMap
      (periodCover j p j.twist (mainTwist_admissible j)) 3)).toAddSubgroup.index =
      fibreNormIndex j := by
  rw [cover_range_index_coordinates _ (surfaceH3Equiv j p)]
  exact surfacePeriodCoverH3Coordinates_range_index j p

theorem surfacePeriodCover_h2_range_finiteIndex (j : Kind) (p : FixedPeriod j) :
    (LinearMap.range (singularHomologyMap
      (periodCover j p j.twist (mainTwist_admissible j)) 2)).toAddSubgroup.FiniteIndex := by
  refine ⟨?_⟩
  rw [surfacePeriodCover_h2_range_index]
  exact (fibreNormIndex_pos j).ne'

theorem surfacePeriodCover_h3_range_finiteIndex (j : Kind) (p : FixedPeriod j) :
    (LinearMap.range (singularHomologyMap
      (periodCover j p j.twist (mainTwist_admissible j)) 3)).toAddSubgroup.FiniteIndex := by
  refine ⟨?_⟩
  rw [surfacePeriodCover_h3_range_index]
  exact (fibreNormIndex_pos j).ne'

/-- For the order-three surface, the genuine covering is onto in degree two. -/
theorem surfacePeriodCover_h2_surjective_three (p : FixedPeriod .three) :
    Function.Surjective (singularHomologyMap
      (periodCover .three p Kind.three.twist (mainTwist_admissible .three)) 2) := by
  have h : Function.Surjective (surfacePeriodCoverH2Coordinates .three p) := by
    apply LinearMap.range_eq_top.mp
    rw [surfacePeriodCoverH2Coordinates_range, fibreNormIndex_three,
      CoverAlgebra.divisibleSecond_one]
  intro a
  obtain ⟨b, hb⟩ := h (surfaceH2Equiv .three p a)
  exact ⟨b, (surfaceH2Equiv .three p).injective hb⟩

/-- The genuine order-three covering is also onto in degree three. -/
theorem surfacePeriodCover_h3_surjective_three (p : FixedPeriod .three) :
    Function.Surjective (singularHomologyMap
      (periodCover .three p Kind.three.twist (mainTwist_admissible .three)) 3) := by
  have h : Function.Surjective (surfacePeriodCoverH3Coordinates .three p) := by
    apply LinearMap.range_eq_top.mp
    rw [surfacePeriodCoverH3Coordinates_range, fibreNormIndex_three,
      CoverAlgebra.divisibleSecond_one]
  intro a
  obtain ⟨b, hb⟩ := h (surfaceH3Equiv .three p a)
  exact ⟨b, (surfaceH3Equiv .three p).injective hb⟩

end Wikipedia.HopfProblem.Elliptic.HigherHomology
