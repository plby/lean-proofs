import Wikipedia.HopfProblem.ThreefoldOverlapMappingTorusSpaces
import Wikipedia.HopfProblem.ThreefoldHomologyGluingInitial

/-!
# Actual boundary models in the integral attachment sequence

The homotopy equivalences induce maps on genuine singular homology.  The
two attachment coefficients are still the literal regular and filling
inclusions; no matrix marking or abstract group identification is assumed.
-/

noncomputable section

open scoped ContinuousMap

namespace Wikipedia.HopfProblem.ThreefoldOverlapMappingTorus

open SpecialPeriods SpecialPeriods.Threefold SpecialPeriods.Threefold.Homology
open SingularMayerVietoris PeriodTorusHigherHomology

/-- Integral homology of a literal global overlap, identified through its actual deformation. -/
def overlapHomologyEquiv (i : Puncture) (n : ℕ) :
    SingularHomology (RegularOverlap i) n ≃ₗ[ℤ] SingularHomology (Boundary i) n :=
  homotopyEquivHomologyEquiv (overlapMappingTorusHomotopyEquiv i) n

@[simp] theorem overlapHomologyEquiv_toLinearMap (i : Puncture) (n : ℕ) :
    (overlapHomologyEquiv i n).toLinearMap = singularHomologyMap (overlapRetraction i) n := rfl

@[simp] theorem overlapHomologyEquiv_symm_toLinearMap (i : Puncture) (n : ℕ) :
    (overlapHomologyEquiv i n).symm.toLinearMap =
      singularHomologyMap (boundaryToOverlap i) n := rfl

/-- The actual boundary-to-regular coefficient in every degree. -/
def boundaryRegularHomologyMap (i : Puncture) (n : ℕ) :
    SingularHomology (Boundary i) n →ₗ[ℤ] SingularHomology SpecialRegularFamily n :=
  singularHomologyMap (boundaryToRegularFamily i) n

/-- The actual boundary-to-original-filling coefficient in every degree. -/
def boundaryFillingHomologyMap (i : Puncture) (n : ℕ) :
    SingularHomology (Boundary i) n →ₗ[ℤ] SingularHomology (localPiece (some i)) n :=
  singularHomologyMap (boundaryToFilling i) n

theorem boundaryRegularHomologyMap_eq (i : Puncture) (n : ℕ) :
    boundaryRegularHomologyMap i n = (singularHomologyMap (overlapToRegularFamily i) n).comp
      (overlapHomologyEquiv i n).symm.toLinearMap :=
  singularHomologyMap_comp (boundaryToOverlap i) (overlapToRegularFamily i) n

theorem boundaryFillingHomologyMap_eq (i : Puncture) (n : ℕ) :
    boundaryFillingHomologyMap i n = (singularHomologyMap (overlapToFilling i) n).comp
      (overlapHomologyEquiv i n).symm.toLinearMap :=
  singularHomologyMap_comp (boundaryToOverlap i) (overlapToFilling i) n

theorem boundaryRegularHomologyMap_retraction (i : Puncture) (n : ℕ) :
    (boundaryRegularHomologyMap i n).comp (overlapHomologyEquiv i n).toLinearMap =
      singularHomologyMap (overlapToRegularFamily i) n := by
  rw [overlapHomologyEquiv_toLinearMap]
  change (singularHomologyMap (boundaryToRegularFamily i) n).comp
    (singularHomologyMap (overlapRetraction i) n) = _
  rw [← singularHomologyMap_comp]
  exact homotopic_homologyMap (boundary_regular_retraction_homotopic i) n

theorem boundaryFillingHomologyMap_retraction (i : Puncture) (n : ℕ) :
    (boundaryFillingHomologyMap i n).comp (overlapHomologyEquiv i n).toLinearMap =
      singularHomologyMap (overlapToFilling i) n := by
  rw [overlapHomologyEquiv_toLinearMap]
  change (singularHomologyMap (boundaryToFilling i) n).comp
    (singularHomologyMap (overlapRetraction i) n) = _
  rw [← singularHomologyMap_comp]
  exact homotopic_homologyMap (boundary_filling_retraction_homotopic i) n

/-- The signed original Mayer--Vietoris coefficient on genuine boundary homology. -/
theorem initialAttachmentLeftHomologyMap_boundary (i : Puncture) (n : ℕ)
    (a : SingularHomology (Boundary i) n) :
    initialAttachmentLeftHomologyMap i n ((overlapHomologyEquiv i n).symm a) =
      (boundaryRegularHomologyMap i n a, -boundaryFillingHomologyMap i n a) := by
  rw [initialAttachmentLeftHomologyMap_apply]
  have hreg := LinearMap.congr_fun (boundaryRegularHomologyMap_eq i n) a
  have hfill := LinearMap.congr_fun (boundaryFillingHomologyMap_eq i n) a
  exact Prod.ext hreg.symm (congrArg Neg.neg hfill.symm)

/-- The boundary fibre coefficient is induced by the literal original fibre map. -/
theorem boundaryRegularHomologyMap_fibre (i : Puncture) (n : ℕ) :
    (boundaryRegularHomologyMap i n).comp
        (singularHomologyMap (MappingTorus.HomologyCover.fibreInclusion (monodromy i)) n) =
      singularHomologyMap (fibreToRegularFamily i) n :=
  (singularHomologyMap_comp (MappingTorus.HomologyCover.fibreInclusion (monodromy i))
    (boundaryToRegularFamily i) n).symm

theorem boundaryFillingHomologyMap_fibre (i : Puncture) (n : ℕ) :
    (boundaryFillingHomologyMap i n).comp
        (singularHomologyMap (MappingTorus.HomologyCover.fibreInclusion (monodromy i)) n) =
      singularHomologyMap (fibreToFilling i) n :=
  (singularHomologyMap_comp (MappingTorus.HomologyCover.fibreInclusion (monodromy i))
    (boundaryToFilling i) n).symm

end Wikipedia.HopfProblem.ThreefoldOverlapMappingTorus
