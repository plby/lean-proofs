import Wikipedia.HopfProblem.EllipticHigherHomologyCoverIndicesLowDegrees
import Wikipedia.HopfProblem.EllipticHigherHomologySpecialCoverIndices

/-!
# The complete actual image-index profile for the special period covers

The actual degree-zero covering map is onto.  In degree one its native
cokernel is cyclic of the elliptic order.  Together with the proved
higher-degree covering results, this gives the full image-index vectors
`(1, 3, 1, 1, 3)` and `(1, 4, 2, 2, 4)`, both for the central surface
and for the entire special filling.  All maps use the constructed
special period family; no period or homology comparison is supplied.
-/

noncomputable section

namespace Wikipedia.HopfProblem.SpecialPeriods.EllipticFilling

open Elliptic Elliptic.HigherHomology
open SingularMayerVietoris PeriodTorusHigherHomology

/-- The actual marked first homology of the special central surface. -/
def specialCentralSurfaceH1Equiv (j : Kind) :
    SingularHomology (SpecialCentralSurface j) 1 ≃ₗ[ℤ] (Fin 2 → ℤ) :=
  surfaceH1Equiv j (specialLocalData j).centralPeriod

/-- The same marking on the actual full filling, through its retraction. -/
def specialFullFillingH1Equiv (j : Kind) :
    SingularHomology (SpecialFullFilling j) 1 ≃ₗ[ℤ] (Fin 2 → ℤ) :=
  fillingH1Equiv (specialLocalData j)

/-- The native actual first-homology covering cokernel is reduction
modulo the elliptic order. -/
def specialCentralPeriodCoverH1CokernelEquivZMod (j : Kind) :
    (SingularHomology (SpecialCentralSurface j) 1 ⧸
      LinearMap.range (singularHomologyMap (specialCentralPeriodCover j) 1)) ≃ₗ[ℤ] ZMod j.order :=
  surfacePeriodCoverH1CokernelEquivZMod j (specialLocalData j).centralPeriod

@[simp] theorem specialCentralPeriodCoverH1CokernelEquivZMod_mk (j : Kind)
    (a : SingularHomology (SpecialCentralSurface j) 1) :
    specialCentralPeriodCoverH1CokernelEquivZMod j (Submodule.Quotient.mk a) =
      (specialCentralSurfaceH1Equiv j a 1 : ZMod j.order) :=
  surfacePeriodCoverH1CokernelEquivZMod_mk j (specialLocalData j).centralPeriod a

/-- The actual degree-zero covering map is onto. -/
theorem specialCentralPeriodCover_h0_surjective (j : Kind) :
    Function.Surjective (singularHomologyMap (specialCentralPeriodCover j) 0) :=
  surfacePeriodCover_h0_surjective j (specialLocalData j).centralPeriod

theorem specialCentralPeriodCover_h0_range_index (j : Kind) :
    (LinearMap.range (singularHomologyMap
      (specialCentralPeriodCover j) 0)).toAddSubgroup.index = 1 :=
  surfacePeriodCover_h0_range_index j (specialLocalData j).centralPeriod

theorem specialCentralPeriodCover_h0_range_finiteIndex (j : Kind) :
    (LinearMap.range (singularHomologyMap
      (specialCentralPeriodCover j) 0)).toAddSubgroup.FiniteIndex := by
  refine ⟨?_⟩
  rw [specialCentralPeriodCover_h0_range_index]
  exact Nat.one_ne_zero

/-- In the first homology of the actual target, the covering image has
index equal to the elliptic order. -/
theorem specialCentralPeriodCover_h1_range_index (j : Kind) :
    (LinearMap.range (singularHomologyMap
      (specialCentralPeriodCover j) 1)).toAddSubgroup.index = j.order :=
  surfacePeriodCover_h1_range_index j (specialLocalData j).centralPeriod

theorem specialCentralPeriodCover_h1_range_finiteIndex (j : Kind) :
    (LinearMap.range (singularHomologyMap
      (specialCentralPeriodCover j) 1)).toAddSubgroup.FiniteIndex :=
  surfacePeriodCover_h1_range_finiteIndex j (specialLocalData j).centralPeriod

/-- The native actual first-homology covering cokernel is reduction
modulo the elliptic order. -/
def specialPeriodTorusIntoFillingH1CokernelEquivZMod (j : Kind) :
    (SingularHomology (SpecialFullFilling j) 1 ⧸
      LinearMap.range (singularHomologyMap
        (specialPeriodTorusIntoFilling j) 1)) ≃ₗ[ℤ] ZMod j.order :=
  fillingPeriodCoverH1CokernelEquivZMod (specialLocalData j)

@[simp] theorem specialPeriodTorusIntoFillingH1CokernelEquivZMod_mk (j : Kind)
    (a : SingularHomology (SpecialFullFilling j) 1) :
    specialPeriodTorusIntoFillingH1CokernelEquivZMod j (Submodule.Quotient.mk a) =
      (specialFullFillingH1Equiv j a 1 : ZMod j.order) :=
  fillingPeriodCoverH1CokernelEquivZMod_mk (specialLocalData j) a

/-- The actual degree-zero covering map is onto. -/
theorem specialPeriodTorusIntoFilling_h0_surjective (j : Kind) :
    Function.Surjective (singularHomologyMap (specialPeriodTorusIntoFilling j) 0) :=
  periodTorusIntoFilling_h0_surjective (specialLocalData j)

theorem specialPeriodTorusIntoFilling_h0_range_index (j : Kind) :
    (LinearMap.range (singularHomologyMap
      (specialPeriodTorusIntoFilling j) 0)).toAddSubgroup.index = 1 :=
  periodTorusIntoFilling_h0_range_index (specialLocalData j)

theorem specialPeriodTorusIntoFilling_h0_range_finiteIndex (j : Kind) :
    (LinearMap.range (singularHomologyMap
      (specialPeriodTorusIntoFilling j) 0)).toAddSubgroup.FiniteIndex := by
  refine ⟨?_⟩
  rw [specialPeriodTorusIntoFilling_h0_range_index]
  exact Nat.one_ne_zero

/-- In the first homology of the actual target, the covering image has
index equal to the elliptic order. -/
theorem specialPeriodTorusIntoFilling_h1_range_index (j : Kind) :
    (LinearMap.range (singularHomologyMap
      (specialPeriodTorusIntoFilling j) 1)).toAddSubgroup.index = j.order :=
  periodTorusIntoFilling_h1_range_index (specialLocalData j)

theorem specialPeriodTorusIntoFilling_h1_range_finiteIndex (j : Kind) :
    (LinearMap.range (singularHomologyMap
      (specialPeriodTorusIntoFilling j) 1)).toAddSubgroup.FiniteIndex :=
  periodTorusIntoFilling_h1_range_finiteIndex (specialLocalData j)

/-- The complete actual covering image-index profile in degrees zero
through four. -/
theorem specialCentralPeriodCover_range_index_vector (j : Kind) :
    (fun n : Fin 5 => (LinearMap.range
      (singularHomologyMap (specialCentralPeriodCover j) n)).toAddSubgroup.index) =
      ![1, j.order, fibreNormIndex j, fibreNormIndex j, j.order] := by
  funext n
  fin_cases n
  · exact specialCentralPeriodCover_h0_range_index j
  · exact specialCentralPeriodCover_h1_range_index j
  · exact specialCentralPeriodCover_h2_range_index j
  · exact specialCentralPeriodCover_h3_range_index j
  · exact specialCentralPeriodCover_h4_range_index j

/-- The literal complete image-index vector for the order-three special filling. -/
theorem specialCentralPeriodCover_range_index_vector_three :
    (fun n : Fin 5 => (LinearMap.range
      (singularHomologyMap (specialCentralPeriodCover .three) n)).toAddSubgroup.index) =
      ![1, 3, 1, 1, 3] :=
  specialCentralPeriodCover_range_index_vector .three

/-- The literal complete image-index vector for the order-four special filling. -/
theorem specialCentralPeriodCover_range_index_vector_four :
    (fun n : Fin 5 => (LinearMap.range
      (singularHomologyMap (specialCentralPeriodCover .four) n)).toAddSubgroup.index) =
      ![1, 4, 2, 2, 4] :=
  specialCentralPeriodCover_range_index_vector .four

/-- The complete actual covering image-index profile in degrees zero
through four. -/
theorem specialPeriodTorusIntoFilling_range_index_vector (j : Kind) :
    (fun n : Fin 5 => (LinearMap.range
      (singularHomologyMap (specialPeriodTorusIntoFilling j) n)).toAddSubgroup.index) =
      ![1, j.order, fibreNormIndex j, fibreNormIndex j, j.order] := by
  funext n
  fin_cases n
  · exact specialPeriodTorusIntoFilling_h0_range_index j
  · exact specialPeriodTorusIntoFilling_h1_range_index j
  · exact specialPeriodTorusIntoFilling_h2_range_index j
  · exact specialPeriodTorusIntoFilling_h3_range_index j
  · exact specialPeriodTorusIntoFilling_h4_range_index j

/-- The literal complete image-index vector for the order-three special filling. -/
theorem specialPeriodTorusIntoFilling_range_index_vector_three :
    (fun n : Fin 5 => (LinearMap.range
      (singularHomologyMap (specialPeriodTorusIntoFilling .three) n)).toAddSubgroup.index) =
      ![1, 3, 1, 1, 3] :=
  specialPeriodTorusIntoFilling_range_index_vector .three

/-- The literal complete image-index vector for the order-four special filling. -/
theorem specialPeriodTorusIntoFilling_range_index_vector_four :
    (fun n : Fin 5 => (LinearMap.range
      (singularHomologyMap (specialPeriodTorusIntoFilling .four) n)).toAddSubgroup.index) =
      ![1, 4, 2, 2, 4] :=
  specialPeriodTorusIntoFilling_range_index_vector .four

end Wikipedia.HopfProblem.SpecialPeriods.EllipticFilling
