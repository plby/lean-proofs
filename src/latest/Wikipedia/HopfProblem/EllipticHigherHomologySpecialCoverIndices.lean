import Wikipedia.HopfProblem.EllipticHigherHomologyCoverIndicesFilling
import Wikipedia.HopfProblem.EllipticHigherHomologySpecial

/-!
# Actual covering cokernels for the special elliptic fillings

The source's constructed special period families instantiate the proved
covering calculations.  In degrees two and three the actual image has
index one or two; in degree four its index is the elliptic order.  The
cokernel maps are literal reduction of the indicated homology coordinate,
both for the central surface and for the entire actual filling.
-/

noncomputable section

namespace Wikipedia.HopfProblem.SpecialPeriods.EllipticFilling

open Elliptic Elliptic.HigherHomology
open SingularMayerVietoris PeriodTorusHigherHomology

/-- The actual degree-2 special central-surface covering cokernel. -/
def specialCentralPeriodCoverH2CokernelEquivZMod (j : Kind) :
    (SingularHomology (SpecialCentralSurface j) 2 ⧸
      LinearMap.range (singularHomologyMap (specialCentralPeriodCover j) 2)) ≃ₗ[ℤ]
      ZMod (fibreNormIndex j) :=
  surfacePeriodCoverH2CokernelEquivZMod j (specialLocalData j).centralPeriod

@[simp] theorem specialCentralPeriodCoverH2CokernelEquivZMod_mk (j : Kind)
    (a : SingularHomology (SpecialCentralSurface j) 2) :
    specialCentralPeriodCoverH2CokernelEquivZMod j (Submodule.Quotient.mk a) =
      (specialCentralSurfaceH2Equiv j a 1 : ZMod (fibreNormIndex j)) :=
  surfacePeriodCoverH2CokernelEquivZMod_mk j (specialLocalData j).centralPeriod a

theorem specialCentralPeriodCover_h2_range_index (j : Kind) :
    (LinearMap.range (singularHomologyMap (specialCentralPeriodCover j) 2)).toAddSubgroup.index =
      fibreNormIndex j :=
  surfacePeriodCover_h2_range_index j (specialLocalData j).centralPeriod

theorem specialCentralPeriodCover_h2_range_finiteIndex (j : Kind) :
    (LinearMap.range (singularHomologyMap
      (specialCentralPeriodCover j) 2)).toAddSubgroup.FiniteIndex :=
  surfacePeriodCover_h2_range_finiteIndex j (specialLocalData j).centralPeriod

/-- The actual degree-3 special central-surface covering cokernel. -/
def specialCentralPeriodCoverH3CokernelEquivZMod (j : Kind) :
    (SingularHomology (SpecialCentralSurface j) 3 ⧸
      LinearMap.range (singularHomologyMap (specialCentralPeriodCover j) 3)) ≃ₗ[ℤ]
      ZMod (fibreNormIndex j) :=
  surfacePeriodCoverH3CokernelEquivZMod j (specialLocalData j).centralPeriod

@[simp] theorem specialCentralPeriodCoverH3CokernelEquivZMod_mk (j : Kind)
    (a : SingularHomology (SpecialCentralSurface j) 3) :
    specialCentralPeriodCoverH3CokernelEquivZMod j (Submodule.Quotient.mk a) =
      (specialCentralSurfaceH3Equiv j a 1 : ZMod (fibreNormIndex j)) :=
  surfacePeriodCoverH3CokernelEquivZMod_mk j (specialLocalData j).centralPeriod a

theorem specialCentralPeriodCover_h3_range_index (j : Kind) :
    (LinearMap.range (singularHomologyMap (specialCentralPeriodCover j) 3)).toAddSubgroup.index =
      fibreNormIndex j :=
  surfacePeriodCover_h3_range_index j (specialLocalData j).centralPeriod

theorem specialCentralPeriodCover_h3_range_finiteIndex (j : Kind) :
    (LinearMap.range (singularHomologyMap
      (specialCentralPeriodCover j) 3)).toAddSubgroup.FiniteIndex :=
  surfacePeriodCover_h3_range_finiteIndex j (specialLocalData j).centralPeriod

/-- The actual degree-4 special central-surface covering cokernel. -/
def specialCentralPeriodCoverH4CokernelEquivZMod (j : Kind) :
    (SingularHomology (SpecialCentralSurface j) 4 ⧸
      LinearMap.range (singularHomologyMap (specialCentralPeriodCover j) 4)) ≃ₗ[ℤ]
      ZMod j.order :=
  surfacePeriodCoverH4CokernelEquivZMod j (specialLocalData j).centralPeriod

@[simp] theorem specialCentralPeriodCoverH4CokernelEquivZMod_mk (j : Kind)
    (a : SingularHomology (SpecialCentralSurface j) 4) :
    specialCentralPeriodCoverH4CokernelEquivZMod j (Submodule.Quotient.mk a) =
      (specialCentralSurfaceH4Equiv j a : ZMod j.order) :=
  surfacePeriodCoverH4CokernelEquivZMod_apply_mk j (specialLocalData j).centralPeriod a

theorem specialCentralPeriodCover_h4_range_index (j : Kind) :
    (LinearMap.range (singularHomologyMap (specialCentralPeriodCover j) 4)).toAddSubgroup.index =
      j.order :=
  surfacePeriodCover_h4_range_index j (specialLocalData j).centralPeriod

theorem specialCentralPeriodCover_h4_range_finiteIndex (j : Kind) :
    (LinearMap.range (singularHomologyMap
      (specialCentralPeriodCover j) 4)).toAddSubgroup.FiniteIndex :=
  surfacePeriodCover_h4_range_finiteIndex j (specialLocalData j).centralPeriod

/-- The actual degree-2 torus-to-full-filling covering cokernel. -/
def specialPeriodTorusIntoFillingH2CokernelEquivZMod (j : Kind) :
    (SingularHomology (SpecialFullFilling j) 2 ⧸
      LinearMap.range (singularHomologyMap (specialPeriodTorusIntoFilling j) 2)) ≃ₗ[ℤ]
      ZMod (fibreNormIndex j) :=
  fillingPeriodCoverH2CokernelEquivZMod (specialLocalData j)

@[simp] theorem specialPeriodTorusIntoFillingH2CokernelEquivZMod_mk (j : Kind)
    (a : SingularHomology (SpecialFullFilling j) 2) :
    specialPeriodTorusIntoFillingH2CokernelEquivZMod j (Submodule.Quotient.mk a) =
      (specialFullFillingH2Equiv j a 1 : ZMod (fibreNormIndex j)) :=
  fillingPeriodCoverH2CokernelEquivZMod_mk (specialLocalData j) a

theorem specialPeriodTorusIntoFilling_h2_range_index (j : Kind) :
    (LinearMap.range (singularHomologyMap
      (specialPeriodTorusIntoFilling j) 2)).toAddSubgroup.index =
      fibreNormIndex j :=
  periodTorusIntoFilling_h2_range_index (specialLocalData j)

theorem specialPeriodTorusIntoFilling_h2_range_finiteIndex (j : Kind) :
    (LinearMap.range (singularHomologyMap
      (specialPeriodTorusIntoFilling j) 2)).toAddSubgroup.FiniteIndex :=
  periodTorusIntoFilling_h2_range_finiteIndex (specialLocalData j)

/-- The actual degree-3 torus-to-full-filling covering cokernel. -/
def specialPeriodTorusIntoFillingH3CokernelEquivZMod (j : Kind) :
    (SingularHomology (SpecialFullFilling j) 3 ⧸
      LinearMap.range (singularHomologyMap (specialPeriodTorusIntoFilling j) 3)) ≃ₗ[ℤ]
      ZMod (fibreNormIndex j) :=
  fillingPeriodCoverH3CokernelEquivZMod (specialLocalData j)

@[simp] theorem specialPeriodTorusIntoFillingH3CokernelEquivZMod_mk (j : Kind)
    (a : SingularHomology (SpecialFullFilling j) 3) :
    specialPeriodTorusIntoFillingH3CokernelEquivZMod j (Submodule.Quotient.mk a) =
      (specialFullFillingH3Equiv j a 1 : ZMod (fibreNormIndex j)) :=
  fillingPeriodCoverH3CokernelEquivZMod_mk (specialLocalData j) a

theorem specialPeriodTorusIntoFilling_h3_range_index (j : Kind) :
    (LinearMap.range (singularHomologyMap
      (specialPeriodTorusIntoFilling j) 3)).toAddSubgroup.index =
      fibreNormIndex j :=
  periodTorusIntoFilling_h3_range_index (specialLocalData j)

theorem specialPeriodTorusIntoFilling_h3_range_finiteIndex (j : Kind) :
    (LinearMap.range (singularHomologyMap
      (specialPeriodTorusIntoFilling j) 3)).toAddSubgroup.FiniteIndex :=
  periodTorusIntoFilling_h3_range_finiteIndex (specialLocalData j)

/-- The actual degree-4 torus-to-full-filling covering cokernel. -/
def specialPeriodTorusIntoFillingH4CokernelEquivZMod (j : Kind) :
    (SingularHomology (SpecialFullFilling j) 4 ⧸
      LinearMap.range (singularHomologyMap (specialPeriodTorusIntoFilling j) 4)) ≃ₗ[ℤ]
      ZMod j.order :=
  fillingPeriodCoverH4CokernelEquivZMod (specialLocalData j)

@[simp] theorem specialPeriodTorusIntoFillingH4CokernelEquivZMod_mk (j : Kind)
    (a : SingularHomology (SpecialFullFilling j) 4) :
    specialPeriodTorusIntoFillingH4CokernelEquivZMod j (Submodule.Quotient.mk a) =
      (specialFullFillingH4Equiv j a : ZMod j.order) :=
  fillingPeriodCoverH4CokernelEquivZMod_mk (specialLocalData j) a

theorem specialPeriodTorusIntoFilling_h4_range_index (j : Kind) :
    (LinearMap.range (singularHomologyMap
      (specialPeriodTorusIntoFilling j) 4)).toAddSubgroup.index =
      j.order :=
  periodTorusIntoFilling_h4_range_index (specialLocalData j)

theorem specialPeriodTorusIntoFilling_h4_range_finiteIndex (j : Kind) :
    (LinearMap.range (singularHomologyMap
      (specialPeriodTorusIntoFilling j) 4)).toAddSubgroup.FiniteIndex :=
  periodTorusIntoFilling_h4_range_finiteIndex (specialLocalData j)

/-- The actual central-surface image-index triple for the order-three special filling. -/
theorem specialCentralPeriodCover_range_indices_three :
    ((LinearMap.range (singularHomologyMap
        (specialCentralPeriodCover .three) 2)).toAddSubgroup.index,
      (LinearMap.range (singularHomologyMap
        (specialCentralPeriodCover .three) 3)).toAddSubgroup.index,
      (LinearMap.range (singularHomologyMap
        (specialCentralPeriodCover .three) 4)).toAddSubgroup.index) =
      (1, 1, 3) := by
  rw [specialCentralPeriodCover_h2_range_index, specialCentralPeriodCover_h3_range_index,
    specialCentralPeriodCover_h4_range_index]
  rfl

/-- The actual central-surface image-index triple for the order-four special filling. -/
theorem specialCentralPeriodCover_range_indices_four :
    ((LinearMap.range (singularHomologyMap
        (specialCentralPeriodCover .four) 2)).toAddSubgroup.index,
      (LinearMap.range (singularHomologyMap
        (specialCentralPeriodCover .four) 3)).toAddSubgroup.index,
      (LinearMap.range (singularHomologyMap
        (specialCentralPeriodCover .four) 4)).toAddSubgroup.index) =
      (2, 2, 4) := by
  rw [specialCentralPeriodCover_h2_range_index, specialCentralPeriodCover_h3_range_index,
    specialCentralPeriodCover_h4_range_index]
  rfl

/-- The actual full-filling image-index triple for the order-three special filling. -/
theorem specialPeriodTorusIntoFilling_range_indices_three :
    ((LinearMap.range (singularHomologyMap
        (specialPeriodTorusIntoFilling .three) 2)).toAddSubgroup.index,
      (LinearMap.range (singularHomologyMap
        (specialPeriodTorusIntoFilling .three) 3)).toAddSubgroup.index,
      (LinearMap.range (singularHomologyMap
        (specialPeriodTorusIntoFilling .three) 4)).toAddSubgroup.index) =
      (1, 1, 3) := by
  rw [specialPeriodTorusIntoFilling_h2_range_index, specialPeriodTorusIntoFilling_h3_range_index,
    specialPeriodTorusIntoFilling_h4_range_index]
  rfl

/-- The actual full-filling image-index triple for the order-four special filling. -/
theorem specialPeriodTorusIntoFilling_range_indices_four :
    ((LinearMap.range (singularHomologyMap
        (specialPeriodTorusIntoFilling .four) 2)).toAddSubgroup.index,
      (LinearMap.range (singularHomologyMap
        (specialPeriodTorusIntoFilling .four) 3)).toAddSubgroup.index,
      (LinearMap.range (singularHomologyMap
        (specialPeriodTorusIntoFilling .four) 4)).toAddSubgroup.index) =
      (2, 2, 4) := by
  rw [specialPeriodTorusIntoFilling_h2_range_index, specialPeriodTorusIntoFilling_h3_range_index,
    specialPeriodTorusIntoFilling_h4_range_index]
  rfl

/-- The order-three special period cover is onto in degree 2. -/
theorem specialCentralPeriodCover_h2_surjective_three :
    Function.Surjective (singularHomologyMap (specialCentralPeriodCover .three) 2) :=
  surfacePeriodCover_h2_surjective_three (specialLocalData .three).centralPeriod

/-- The actual central inclusion carries this surjectivity to the full filling. -/
theorem specialPeriodTorusIntoFilling_h2_surjective_three :
    Function.Surjective (singularHomologyMap (specialPeriodTorusIntoFilling .three) 2) := by
  intro a
  obtain ⟨b, hb⟩ := specialCentralPeriodCover_h2_surjective_three
    ((specialCentralSurfaceHomologyEquiv .three 2).symm a)
  refine ⟨b, ?_⟩
  rw [← specialCentralSurfaceHomologyEquiv_periodCover .three 2 b, hb,
    LinearEquiv.apply_symm_apply]

/-- The order-three special period cover is onto in degree 3. -/
theorem specialCentralPeriodCover_h3_surjective_three :
    Function.Surjective (singularHomologyMap (specialCentralPeriodCover .three) 3) :=
  surfacePeriodCover_h3_surjective_three (specialLocalData .three).centralPeriod

/-- The actual central inclusion carries this surjectivity to the full filling. -/
theorem specialPeriodTorusIntoFilling_h3_surjective_three :
    Function.Surjective (singularHomologyMap (specialPeriodTorusIntoFilling .three) 3) := by
  intro a
  obtain ⟨b, hb⟩ := specialCentralPeriodCover_h3_surjective_three
    ((specialCentralSurfaceHomologyEquiv .three 3).symm a)
  refine ⟨b, ?_⟩
  rw [← specialCentralSurfaceHomologyEquiv_periodCover .three 3 b, hb,
    LinearEquiv.apply_symm_apply]

end Wikipedia.HopfProblem.SpecialPeriods.EllipticFilling
