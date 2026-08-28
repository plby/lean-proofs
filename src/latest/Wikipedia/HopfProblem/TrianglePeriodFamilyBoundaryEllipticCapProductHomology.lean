import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryEllipticCapProductHomologyFilling

/-!
# The degree-four elliptic filling coefficient on actual integral homology

The original surface markings identify boundary fourth homology with
`ℤ × ℤ²`.  In these genuine cap-section/positive-circle coordinates the
literal filling coefficient is the first coordinate.  Its rank-two kernel
is the actual positive-circle cross product of the original surface's
third homology.  No compatibility with an independently marked Wang
sequence is assumed here.
-/

noncomputable section

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.EllipticCapProduct

open Elliptic Elliptic.HigherHomology SingularMayerVietoris PeriodTorusHigherHomology
open SpecialPeriods SpecialPeriods.EllipticFilling SpecialPeriods.Threefold
open SpecialPeriods.Threefold.Homology.Finiteness ThreefoldOverlapMappingTorus

local notation "B" => ThreefoldOverlapMappingTorus.Elliptic.SpecialBoundary
local notation "S" => ThreefoldOverlapMappingTorus.Elliptic.BoundaryCentralSurface

/-- The native boundary's fourth homology in the original surface markings,
with the actual cap component first and the actual circle component second. -/
def boundaryCapH4Equiv (j : Kind) :
    SingularHomology (B j) 4 ≃ₗ[ℤ] (ℤ × (Fin 2 → ℤ)) :=
  ((boundaryCapHomologyEquiv j 3).toAddEquiv.trans
    ((surfaceH4Equiv j (specialLocalData j).centralPeriod).toAddEquiv.prodCongr
      (surfaceH3Equiv j (specialLocalData j).centralPeriod).toAddEquiv)).toIntLinearEquiv

@[simp] theorem boundaryCapH4Equiv_apply (j : Kind) (a : SingularHomology (B j) 4) :
    boundaryCapH4Equiv j a =
      (surfaceH4Equiv j (specialLocalData j).centralPeriod
        (boundaryCapHomologyEquiv j 3 a).1,
      surfaceH3Equiv j (specialLocalData j).centralPeriod
        (boundaryCapHomologyEquiv j 3 a).2) := rfl

/-- The literal filling coefficient is exactly the first integral coordinate,
using the unchanged original surface orientation-group marking. -/
theorem boundaryFillingHomologyMap_H4_first (j : Kind) (a : SingularHomology (B j) 4) :
    surfaceH4Equiv j (specialLocalData j).centralPeriod
      (ellipticPieceRetractionHomologyEquiv j 4 (boundaryFillingHomologyMap (some j) 4 a)) =
        (boundaryCapH4Equiv j a).1 := by
  rw [boundaryFillingHomologyMap_first]
  rfl

/-- Section classes have no positive-circle coordinate. -/
@[simp] theorem boundaryCapH4Equiv_section (j : Kind) (a : SingularHomology (S j) 4) :
    boundaryCapH4Equiv j (singularHomologyMap (capSection j) 4 a) =
      (surfaceH4Equiv j (specialLocalData j).centralPeriod a, 0) := by
  rw [boundaryCapH4Equiv_apply, boundaryCapHomologyEquiv_section]
  simp only [map_zero]

/-- The kernel marking is the genuine positive-circle cross product, with
the original third-homology coordinates on the central surface. -/
@[simp] theorem boundaryCapH4Equiv_positiveCircleCross (j : Kind)
    (a : SingularHomology (S j) 3) :
    boundaryCapH4Equiv j (boundaryPositiveCircleCross j 3 a) =
      (0, surfaceH3Equiv j (specialLocalData j).centralPeriod a) := by
  rw [boundaryCapH4Equiv_apply, boundaryCapHomologyEquiv_positiveCircleCross]
  simp only [map_zero]

/-- The numerical inverse retains the actual section and actual positive-circle maps. -/
theorem boundaryCapH4Equiv_symm_eq_section_add_cross (j : Kind) (a : ℤ × (Fin 2 → ℤ)) :
    (boundaryCapH4Equiv j).symm a =
      singularHomologyMap (capSection j) 4
        ((surfaceH4Equiv j (specialLocalData j).centralPeriod).symm a.1) +
      boundaryPositiveCircleCross j 3
        ((surfaceH3Equiv j (specialLocalData j).centralPeriod).symm a.2) :=
  boundaryCapHomologyEquiv_symm_eq_section_add_cross j 3 _

/-- The full original filling class, not merely its rank or an abstract image. -/
theorem boundaryFillingHomologyMap_H4_symm (j : Kind) (a : ℤ × (Fin 2 → ℤ)) :
    boundaryFillingHomologyMap (some j) 4 ((boundaryCapH4Equiv j).symm a) =
      (ellipticPieceRetractionHomologyEquiv j 4).symm
        ((surfaceH4Equiv j (specialLocalData j).centralPeriod).symm a.1) := by
  have hcoords : boundaryCapHomologyEquiv j 3 ((boundaryCapH4Equiv j).symm a) =
      ((surfaceH4Equiv j (specialLocalData j).centralPeriod).symm a.1,
        (surfaceH3Equiv j (specialLocalData j).centralPeriod).symm a.2) :=
    (boundaryCapHomologyEquiv j 3).apply_symm_apply _
  exact (boundaryFillingHomologyMap_eq_retraction_symm j 3 _).trans
    (congrArg (ellipticPieceRetractionHomologyEquiv j 4).symm (congrArg Prod.fst hcoords))

/-- The actual filling coefficient written between the proved degree-four coordinates. -/
def boundaryCapH4CoordinatesMap (j : Kind) : (ℤ × (Fin 2 → ℤ)) →ₗ[ℤ] ℤ :=
  (surfaceH4Equiv j (specialLocalData j).centralPeriod).toLinearMap.comp
    ((ellipticPieceRetractionHomologyEquiv j 4).toLinearMap.comp
      ((boundaryFillingHomologyMap (some j) 4).comp (boundaryCapH4Equiv j).symm.toLinearMap))

/-- Its matrix is precisely the first-coordinate projection `[1, 0, 0]`. -/
theorem boundaryCapH4CoordinatesMap_eq_fst (j : Kind) :
    boundaryCapH4CoordinatesMap j = LinearMap.fst ℤ ℤ (Fin 2 → ℤ) := by
  apply LinearMap.ext
  intro a
  change surfaceH4Equiv j (specialLocalData j).centralPeriod
    (ellipticPieceRetractionHomologyEquiv j 4
      (boundaryFillingHomologyMap (some j) 4 ((boundaryCapH4Equiv j).symm a))) = a.1
  rw [boundaryFillingHomologyMap_H4_first, LinearEquiv.apply_symm_apply]

/-- The kernel of the literal degree-four filling coefficient is the marked
third homology of the actual original central surface. -/
def boundaryCapH4KernelEquiv (j : Kind) :
    LinearMap.ker (boundaryFillingHomologyMap (some j) 4) ≃ₗ[ℤ] (Fin 2 → ℤ) :=
  (boundaryCapKernelEquiv j 3).trans
    (surfaceH3Equiv j (specialLocalData j).centralPeriod)

@[simp] theorem boundaryCapH4KernelEquiv_symm_val (j : Kind) (a : Fin 2 → ℤ) :
    ((boundaryCapH4KernelEquiv j).symm a).val =
      boundaryPositiveCircleCross j 3
        ((surfaceH3Equiv j (specialLocalData j).centralPeriod).symm a) := rfl

theorem boundaryCapH4Kernel_finrank (j : Kind) :
    Module.finrank ℤ (LinearMap.ker (boundaryFillingHomologyMap (some j) 4)) = 2 := by
  rw [(boundaryCapH4KernelEquiv j).finrank_eq]
  simp

end Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.EllipticCapProduct
