import Wikipedia.HopfProblem.EllipticHigherHomologySpecialCohomologyInvariant
import Wikipedia.HopfProblem.EllipticHigherHomologyCohomologyInvariantIndices

/-!
# Exact invariant-cohomology image indices for the special elliptic fillings

The actual special central-cover and full-filling pullbacks have integral
image indices `(1, 3, 1, 1, 3)` and `(1, 4, 2, 2, 4)` in all deck invariants.
The cokernel equivalences preserve actual invariant cohomology classes.
The degree-one through degree-three formulas retain the genuine shear
of the original covering map, and the top-degree formula retains its
actual integral invariant coordinate.
-/

noncomputable section

namespace Wikipedia.HopfProblem.SpecialPeriods.EllipticFilling

open Elliptic Elliptic.HigherHomology SingularCohomologyFree

/-- The actual special central-cover image index in degree 0, inside all deck invariants. -/
theorem specialCentralPeriodCoverCohomologyToInvariants_h0_range_index (j : Kind) :
    (LinearMap.range (specialCentralPeriodCoverCohomologyToInvariants j 0)).toAddSubgroup.index =
      1 :=
  periodCoverCohomologyToInvariants_h0_range_index j (specialLocalData j).centralPeriod

theorem specialCentralPeriodCoverCohomologyToInvariants_h0_range_finiteIndex (j : Kind) :
    (LinearMap.range
      (specialCentralPeriodCoverCohomologyToInvariants j 0)).toAddSubgroup.FiniteIndex :=
  periodCoverCohomologyToInvariants_h0_range_finiteIndex j (specialLocalData j).centralPeriod

/-- The actual special central-cover image index in degree 1, inside all deck invariants. -/
theorem specialCentralPeriodCoverCohomologyToInvariants_h1_range_index (j : Kind) :
    (LinearMap.range (specialCentralPeriodCoverCohomologyToInvariants j 1)).toAddSubgroup.index =
      j.order :=
  periodCoverCohomologyToInvariants_h1_range_index j (specialLocalData j).centralPeriod

theorem specialCentralPeriodCoverCohomologyToInvariants_h1_range_finiteIndex (j : Kind) :
    (LinearMap.range
      (specialCentralPeriodCoverCohomologyToInvariants j 1)).toAddSubgroup.FiniteIndex :=
  periodCoverCohomologyToInvariants_h1_range_finiteIndex j (specialLocalData j).centralPeriod

/-- The actual special central-cover image index in degree 2, inside all deck invariants. -/
theorem specialCentralPeriodCoverCohomologyToInvariants_h2_range_index (j : Kind) :
    (LinearMap.range (specialCentralPeriodCoverCohomologyToInvariants j 2)).toAddSubgroup.index =
      fibreNormIndex j :=
  periodCoverCohomologyToInvariants_h2_range_index j (specialLocalData j).centralPeriod

theorem specialCentralPeriodCoverCohomologyToInvariants_h2_range_finiteIndex (j : Kind) :
    (LinearMap.range
      (specialCentralPeriodCoverCohomologyToInvariants j 2)).toAddSubgroup.FiniteIndex :=
  periodCoverCohomologyToInvariants_h2_range_finiteIndex j (specialLocalData j).centralPeriod

/-- The actual special central-cover image index in degree 3, inside all deck invariants. -/
theorem specialCentralPeriodCoverCohomologyToInvariants_h3_range_index (j : Kind) :
    (LinearMap.range (specialCentralPeriodCoverCohomologyToInvariants j 3)).toAddSubgroup.index =
      fibreNormIndex j :=
  periodCoverCohomologyToInvariants_h3_range_index j (specialLocalData j).centralPeriod

theorem specialCentralPeriodCoverCohomologyToInvariants_h3_range_finiteIndex (j : Kind) :
    (LinearMap.range
      (specialCentralPeriodCoverCohomologyToInvariants j 3)).toAddSubgroup.FiniteIndex :=
  periodCoverCohomologyToInvariants_h3_range_finiteIndex j (specialLocalData j).centralPeriod

/-- The actual special central-cover image index in degree 4, inside all deck invariants. -/
theorem specialCentralPeriodCoverCohomologyToInvariants_h4_range_index (j : Kind) :
    (LinearMap.range (specialCentralPeriodCoverCohomologyToInvariants j 4)).toAddSubgroup.index =
      j.order :=
  periodCoverCohomologyToInvariants_h4_range_index j (specialLocalData j).centralPeriod

theorem specialCentralPeriodCoverCohomologyToInvariants_h4_range_finiteIndex (j : Kind) :
    (LinearMap.range
      (specialCentralPeriodCoverCohomologyToInvariants j 4)).toAddSubgroup.FiniteIndex :=
  periodCoverCohomologyToInvariants_h4_range_finiteIndex j (specialLocalData j).centralPeriod

/-- The actual special full-filling image index in degree 0, inside all deck invariants. -/
theorem specialPeriodTorusIntoFillingCohomologyToInvariants_h0_range_index (j : Kind) :
    (LinearMap.range
      (specialPeriodTorusIntoFillingCohomologyToInvariants j 0)).toAddSubgroup.index =
      1 :=
  periodTorusIntoFillingCohomologyToInvariants_h0_range_index (specialLocalData j)

theorem specialPeriodTorusIntoFillingCohomologyToInvariants_h0_range_finiteIndex (j : Kind) :
    (LinearMap.range
      (specialPeriodTorusIntoFillingCohomologyToInvariants j 0)).toAddSubgroup.FiniteIndex :=
  periodTorusIntoFillingCohomologyToInvariants_h0_range_finiteIndex (specialLocalData j)

/-- The actual special full-filling image index in degree 1, inside all deck invariants. -/
theorem specialPeriodTorusIntoFillingCohomologyToInvariants_h1_range_index (j : Kind) :
    (LinearMap.range
      (specialPeriodTorusIntoFillingCohomologyToInvariants j 1)).toAddSubgroup.index =
      j.order :=
  periodTorusIntoFillingCohomologyToInvariants_h1_range_index (specialLocalData j)

theorem specialPeriodTorusIntoFillingCohomologyToInvariants_h1_range_finiteIndex (j : Kind) :
    (LinearMap.range
      (specialPeriodTorusIntoFillingCohomologyToInvariants j 1)).toAddSubgroup.FiniteIndex :=
  periodTorusIntoFillingCohomologyToInvariants_h1_range_finiteIndex (specialLocalData j)

/-- The actual special full-filling image index in degree 2, inside all deck invariants. -/
theorem specialPeriodTorusIntoFillingCohomologyToInvariants_h2_range_index (j : Kind) :
    (LinearMap.range
      (specialPeriodTorusIntoFillingCohomologyToInvariants j 2)).toAddSubgroup.index =
      fibreNormIndex j :=
  periodTorusIntoFillingCohomologyToInvariants_h2_range_index (specialLocalData j)

theorem specialPeriodTorusIntoFillingCohomologyToInvariants_h2_range_finiteIndex (j : Kind) :
    (LinearMap.range
      (specialPeriodTorusIntoFillingCohomologyToInvariants j 2)).toAddSubgroup.FiniteIndex :=
  periodTorusIntoFillingCohomologyToInvariants_h2_range_finiteIndex (specialLocalData j)

/-- The actual special full-filling image index in degree 3, inside all deck invariants. -/
theorem specialPeriodTorusIntoFillingCohomologyToInvariants_h3_range_index (j : Kind) :
    (LinearMap.range
      (specialPeriodTorusIntoFillingCohomologyToInvariants j 3)).toAddSubgroup.index =
      fibreNormIndex j :=
  periodTorusIntoFillingCohomologyToInvariants_h3_range_index (specialLocalData j)

theorem specialPeriodTorusIntoFillingCohomologyToInvariants_h3_range_finiteIndex (j : Kind) :
    (LinearMap.range
      (specialPeriodTorusIntoFillingCohomologyToInvariants j 3)).toAddSubgroup.FiniteIndex :=
  periodTorusIntoFillingCohomologyToInvariants_h3_range_finiteIndex (specialLocalData j)

/-- The actual special full-filling image index in degree 4, inside all deck invariants. -/
theorem specialPeriodTorusIntoFillingCohomologyToInvariants_h4_range_index (j : Kind) :
    (LinearMap.range
      (specialPeriodTorusIntoFillingCohomologyToInvariants j 4)).toAddSubgroup.index =
      j.order :=
  periodTorusIntoFillingCohomologyToInvariants_h4_range_index (specialLocalData j)

theorem specialPeriodTorusIntoFillingCohomologyToInvariants_h4_range_finiteIndex (j : Kind) :
    (LinearMap.range
      (specialPeriodTorusIntoFillingCohomologyToInvariants j 4)).toAddSubgroup.FiniteIndex :=
  periodTorusIntoFillingCohomologyToInvariants_h4_range_finiteIndex (specialLocalData j)

/-- The actual degree-0 special central-cover invariant-cohomology cokernel. -/
def specialCentralPeriodCoverInvariantCohomologyH0CokernelEquivZMod (j : Kind) :
    SpecialCentralPeriodCoverInvariantCohomologyCokernel j 0 ≃ₗ[ℤ] ZMod 1 :=
  periodCoverInvariantCohomologyH0CokernelEquivZMod j (specialLocalData j).centralPeriod

@[simp] theorem specialCentralPeriodCoverInvariantCohomologyH0CokernelEquivZMod_apply_mk (j : Kind)
    (a : periodCohomologyInvariants j (specialLocalData j).centralPeriod
      j.twist (mainTwist_admissible j) 0) :
    specialCentralPeriodCoverInvariantCohomologyH0CokernelEquivZMod j (Submodule.Quotient.mk a) =
      (0 : ZMod 1) :=
  periodCoverInvariantCohomologyH0CokernelEquivZMod_apply_mk j (specialLocalData j).centralPeriod a

/-- The actual degree-1 special central-cover invariant-cohomology cokernel. -/
def specialCentralPeriodCoverInvariantCohomologyH1CokernelEquivZMod (j : Kind) :
    SpecialCentralPeriodCoverInvariantCohomologyCokernel j 1 ≃ₗ[ℤ] ZMod j.order :=
  periodCoverInvariantCohomologyH1CokernelEquivZMod j (specialLocalData j).centralPeriod

@[simp] theorem specialCentralPeriodCoverInvariantCohomologyH1CokernelEquivZMod_apply_mk (j : Kind)
    (a : periodCohomologyInvariants j (specialLocalData j).centralPeriod
      j.twist (mainTwist_admissible j) 1) :
    specialCentralPeriodCoverInvariantCohomologyH1CokernelEquivZMod j (Submodule.Quotient.mk a) =
      ((periodInvariantCohomologyH1Coordinates j (specialLocalData j).centralPeriod a 1 -
        periodCoverDeckDualH1Shear j (specialLocalData j).centralPeriod *
          periodInvariantCohomologyH1Coordinates j
            (specialLocalData j).centralPeriod a 0 : ℤ) : ZMod j.order) :=
  periodCoverInvariantCohomologyH1CokernelEquivZMod_apply_mk j (specialLocalData j).centralPeriod a

/-- The actual degree-2 special central-cover invariant-cohomology cokernel. -/
def specialCentralPeriodCoverInvariantCohomologyH2CokernelEquivZMod (j : Kind) :
    SpecialCentralPeriodCoverInvariantCohomologyCokernel j 2 ≃ₗ[ℤ] ZMod (fibreNormIndex j) :=
  periodCoverInvariantCohomologyH2CokernelEquivZMod j (specialLocalData j).centralPeriod

@[simp] theorem specialCentralPeriodCoverInvariantCohomologyH2CokernelEquivZMod_apply_mk (j : Kind)
    (a : periodCohomologyInvariants j (specialLocalData j).centralPeriod
      j.twist (mainTwist_admissible j) 2) :
    specialCentralPeriodCoverInvariantCohomologyH2CokernelEquivZMod j (Submodule.Quotient.mk a) =
      ((periodInvariantCohomologyH2Coordinates j (specialLocalData j).centralPeriod a 1 -
        periodCoverDeckDualH2Shear j (specialLocalData j).centralPeriod *
          periodInvariantCohomologyH2Coordinates j
            (specialLocalData j).centralPeriod a 0 : ℤ) : ZMod (fibreNormIndex j)) :=
  periodCoverInvariantCohomologyH2CokernelEquivZMod_apply_mk j (specialLocalData j).centralPeriod a

/-- The actual degree-3 special central-cover invariant-cohomology cokernel. -/
def specialCentralPeriodCoverInvariantCohomologyH3CokernelEquivZMod (j : Kind) :
    SpecialCentralPeriodCoverInvariantCohomologyCokernel j 3 ≃ₗ[ℤ] ZMod (fibreNormIndex j) :=
  periodCoverInvariantCohomologyH3CokernelEquivZMod j (specialLocalData j).centralPeriod

@[simp] theorem specialCentralPeriodCoverInvariantCohomologyH3CokernelEquivZMod_apply_mk (j : Kind)
    (a : periodCohomologyInvariants j (specialLocalData j).centralPeriod
      j.twist (mainTwist_admissible j) 3) :
    specialCentralPeriodCoverInvariantCohomologyH3CokernelEquivZMod j (Submodule.Quotient.mk a) =
      ((periodInvariantCohomologyH3Coordinates j (specialLocalData j).centralPeriod a 1 -
        periodCoverDeckDualH3Shear j (specialLocalData j).centralPeriod *
          periodInvariantCohomologyH3Coordinates j
            (specialLocalData j).centralPeriod a 0 : ℤ) : ZMod (fibreNormIndex j)) :=
  periodCoverInvariantCohomologyH3CokernelEquivZMod_apply_mk j (specialLocalData j).centralPeriod a

/-- The actual degree-4 special central-cover invariant-cohomology cokernel. -/
def specialCentralPeriodCoverInvariantCohomologyH4CokernelEquivZMod (j : Kind) :
    SpecialCentralPeriodCoverInvariantCohomologyCokernel j 4 ≃ₗ[ℤ] ZMod j.order :=
  periodCoverInvariantCohomologyH4CokernelEquivZMod j (specialLocalData j).centralPeriod

@[simp] theorem specialCentralPeriodCoverInvariantCohomologyH4CokernelEquivZMod_apply_mk (j : Kind)
    (a : periodCohomologyInvariants j (specialLocalData j).centralPeriod
      j.twist (mainTwist_admissible j) 4) :
    specialCentralPeriodCoverInvariantCohomologyH4CokernelEquivZMod j (Submodule.Quotient.mk a) =
      (periodInvariantCohomologyH4Coordinates j
        (specialLocalData j).centralPeriod a : ZMod j.order) :=
  periodCoverInvariantCohomologyH4CokernelEquivZMod_apply_mk j (specialLocalData j).centralPeriod a

/-- The actual degree-0 special full-filling invariant-cohomology cokernel. -/
def specialPeriodTorusIntoFillingInvariantCohomologyH0CokernelEquivZMod (j : Kind) :
    SpecialPeriodTorusIntoFillingInvariantCohomologyCokernel j 0 ≃ₗ[ℤ] ZMod 1 :=
  periodTorusIntoFillingInvariantCohomologyH0CokernelEquivZMod (specialLocalData j)

@[simp] theorem specialPeriodTorusIntoFillingInvariantCohomologyH0CokernelEquivZMod_apply_mk
    (j : Kind)
    (a : periodCohomologyInvariants j (specialLocalData j).centralPeriod
      j.twist (mainTwist_admissible j) 0) :
    specialPeriodTorusIntoFillingInvariantCohomologyH0CokernelEquivZMod j
        (Submodule.Quotient.mk a) =
      (0 : ZMod 1) :=
  periodTorusIntoFillingInvariantCohomologyH0CokernelEquivZMod_apply_mk (specialLocalData j) a

/-- The actual degree-1 special full-filling invariant-cohomology cokernel. -/
def specialPeriodTorusIntoFillingInvariantCohomologyH1CokernelEquivZMod (j : Kind) :
    SpecialPeriodTorusIntoFillingInvariantCohomologyCokernel j 1 ≃ₗ[ℤ] ZMod j.order :=
  periodTorusIntoFillingInvariantCohomologyH1CokernelEquivZMod (specialLocalData j)

@[simp] theorem specialPeriodTorusIntoFillingInvariantCohomologyH1CokernelEquivZMod_apply_mk
    (j : Kind)
    (a : periodCohomologyInvariants j (specialLocalData j).centralPeriod
      j.twist (mainTwist_admissible j) 1) :
    specialPeriodTorusIntoFillingInvariantCohomologyH1CokernelEquivZMod j
        (Submodule.Quotient.mk a) =
      ((periodInvariantCohomologyH1Coordinates j (specialLocalData j).centralPeriod a 1 -
        periodCoverDeckDualH1Shear j (specialLocalData j).centralPeriod *
          periodInvariantCohomologyH1Coordinates j
            (specialLocalData j).centralPeriod a 0 : ℤ) : ZMod j.order) :=
  periodTorusIntoFillingInvariantCohomologyH1CokernelEquivZMod_apply_mk (specialLocalData j) a

/-- The actual degree-2 special full-filling invariant-cohomology cokernel. -/
def specialPeriodTorusIntoFillingInvariantCohomologyH2CokernelEquivZMod (j : Kind) :
    SpecialPeriodTorusIntoFillingInvariantCohomologyCokernel j 2 ≃ₗ[ℤ] ZMod (fibreNormIndex j) :=
  periodTorusIntoFillingInvariantCohomologyH2CokernelEquivZMod (specialLocalData j)

@[simp] theorem specialPeriodTorusIntoFillingInvariantCohomologyH2CokernelEquivZMod_apply_mk
    (j : Kind)
    (a : periodCohomologyInvariants j (specialLocalData j).centralPeriod
      j.twist (mainTwist_admissible j) 2) :
    specialPeriodTorusIntoFillingInvariantCohomologyH2CokernelEquivZMod j
        (Submodule.Quotient.mk a) =
      ((periodInvariantCohomologyH2Coordinates j (specialLocalData j).centralPeriod a 1 -
        periodCoverDeckDualH2Shear j (specialLocalData j).centralPeriod *
          periodInvariantCohomologyH2Coordinates j
            (specialLocalData j).centralPeriod a 0 : ℤ) : ZMod (fibreNormIndex j)) :=
  periodTorusIntoFillingInvariantCohomologyH2CokernelEquivZMod_apply_mk (specialLocalData j) a

/-- The actual degree-3 special full-filling invariant-cohomology cokernel. -/
def specialPeriodTorusIntoFillingInvariantCohomologyH3CokernelEquivZMod (j : Kind) :
    SpecialPeriodTorusIntoFillingInvariantCohomologyCokernel j 3 ≃ₗ[ℤ] ZMod (fibreNormIndex j) :=
  periodTorusIntoFillingInvariantCohomologyH3CokernelEquivZMod (specialLocalData j)

@[simp] theorem specialPeriodTorusIntoFillingInvariantCohomologyH3CokernelEquivZMod_apply_mk
    (j : Kind)
    (a : periodCohomologyInvariants j (specialLocalData j).centralPeriod
      j.twist (mainTwist_admissible j) 3) :
    specialPeriodTorusIntoFillingInvariantCohomologyH3CokernelEquivZMod j
        (Submodule.Quotient.mk a) =
      ((periodInvariantCohomologyH3Coordinates j (specialLocalData j).centralPeriod a 1 -
        periodCoverDeckDualH3Shear j (specialLocalData j).centralPeriod *
          periodInvariantCohomologyH3Coordinates j
            (specialLocalData j).centralPeriod a 0 : ℤ) : ZMod (fibreNormIndex j)) :=
  periodTorusIntoFillingInvariantCohomologyH3CokernelEquivZMod_apply_mk (specialLocalData j) a

/-- The actual degree-4 special full-filling invariant-cohomology cokernel. -/
def specialPeriodTorusIntoFillingInvariantCohomologyH4CokernelEquivZMod (j : Kind) :
    SpecialPeriodTorusIntoFillingInvariantCohomologyCokernel j 4 ≃ₗ[ℤ] ZMod j.order :=
  periodTorusIntoFillingInvariantCohomologyH4CokernelEquivZMod (specialLocalData j)

@[simp] theorem specialPeriodTorusIntoFillingInvariantCohomologyH4CokernelEquivZMod_apply_mk
    (j : Kind)
    (a : periodCohomologyInvariants j (specialLocalData j).centralPeriod
      j.twist (mainTwist_admissible j) 4) :
    specialPeriodTorusIntoFillingInvariantCohomologyH4CokernelEquivZMod j
        (Submodule.Quotient.mk a) =
      (periodInvariantCohomologyH4Coordinates j
        (specialLocalData j).centralPeriod a : ZMod j.order) :=
  periodTorusIntoFillingInvariantCohomologyH4CokernelEquivZMod_apply_mk (specialLocalData j) a

/-- The five genuine central-cover indices, on the actual invariant-valued cohomology map. -/
theorem specialCentralPeriodCoverCohomologyToInvariants_range_index_vector (j : Kind) :
    (fun n : Fin 5 =>
      (LinearMap.range
        (specialCentralPeriodCoverCohomologyToInvariants j n)).toAddSubgroup.index) =
        ![1, j.order, fibreNormIndex j, fibreNormIndex j, j.order] := by
  funext n
  fin_cases n
  · exact specialCentralPeriodCoverCohomologyToInvariants_h0_range_index j
  · exact specialCentralPeriodCoverCohomologyToInvariants_h1_range_index j
  · exact specialCentralPeriodCoverCohomologyToInvariants_h2_range_index j
  · exact specialCentralPeriodCoverCohomologyToInvariants_h3_range_index j
  · exact specialCentralPeriodCoverCohomologyToInvariants_h4_range_index j

theorem specialCentralPeriodCoverCohomologyToInvariants_range_index_vector_three :
    (fun n : Fin 5 =>
      (LinearMap.range
        (specialCentralPeriodCoverCohomologyToInvariants .three n)).toAddSubgroup.index) =
        ![1, 3, 1, 1, 3] :=
  specialCentralPeriodCoverCohomologyToInvariants_range_index_vector .three

theorem specialCentralPeriodCoverCohomologyToInvariants_range_index_vector_four :
    (fun n : Fin 5 =>
      (LinearMap.range
        (specialCentralPeriodCoverCohomologyToInvariants .four n)).toAddSubgroup.index) =
        ![1, 4, 2, 2, 4] :=
  specialCentralPeriodCoverCohomologyToInvariants_range_index_vector .four

/-- The five genuine full-filling indices, on the actual invariant-valued cohomology map. -/
theorem specialPeriodTorusIntoFillingCohomologyToInvariants_range_index_vector (j : Kind) :
    (fun n : Fin 5 =>
      (LinearMap.range
        (specialPeriodTorusIntoFillingCohomologyToInvariants j n)).toAddSubgroup.index) =
        ![1, j.order, fibreNormIndex j, fibreNormIndex j, j.order] := by
  funext n
  fin_cases n
  · exact specialPeriodTorusIntoFillingCohomologyToInvariants_h0_range_index j
  · exact specialPeriodTorusIntoFillingCohomologyToInvariants_h1_range_index j
  · exact specialPeriodTorusIntoFillingCohomologyToInvariants_h2_range_index j
  · exact specialPeriodTorusIntoFillingCohomologyToInvariants_h3_range_index j
  · exact specialPeriodTorusIntoFillingCohomologyToInvariants_h4_range_index j

theorem specialPeriodTorusIntoFillingCohomologyToInvariants_range_index_vector_three :
    (fun n : Fin 5 =>
      (LinearMap.range
        (specialPeriodTorusIntoFillingCohomologyToInvariants .three n)).toAddSubgroup.index) =
        ![1, 3, 1, 1, 3] :=
  specialPeriodTorusIntoFillingCohomologyToInvariants_range_index_vector .three

theorem specialPeriodTorusIntoFillingCohomologyToInvariants_range_index_vector_four :
    (fun n : Fin 5 =>
      (LinearMap.range
        (specialPeriodTorusIntoFillingCohomologyToInvariants .four n)).toAddSubgroup.index) =
        ![1, 4, 2, 2, 4] :=
  specialPeriodTorusIntoFillingCohomologyToInvariants_range_index_vector .four

end Wikipedia.HopfProblem.SpecialPeriods.EllipticFilling
