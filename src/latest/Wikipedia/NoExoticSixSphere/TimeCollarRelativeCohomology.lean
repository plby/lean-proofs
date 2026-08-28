import Wikipedia.NoExoticSixSphere.TimeCollarBoundaryRetraction
import Wikipedia.NoExoticSixSphere.RelativeModTwoHomologyComparison
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCircleHomotopy

/-!
# Relative cohomology of the literal zero boundary and its time collar

The actual collar deformation proves that the identity pair pullback
from collar-relative to boundary-relative cohomology is an equivalence.
Excision then uses the actual strict-interior and collar open cover.
Every forward map is the original pair pullback.
-/

noncomputable section

open Set Function CategoryTheory ContinuousMap

namespace NoExoticSixSphere.TimeCollarDuality

open Wikipedia.HopfProblem.DegreeCollapse Wikipedia.HopfProblem.DegreeCollapse.TimeCollar
open Wikipedia.HopfProblem.SingularMayerVietoris Wikipedia.HopfProblem.PeriodTorusHigherHomology

variable {M B : Type} [TopologicalSpace M] [TopologicalSpace B]
  {t : M → ℝ} (C : TimeCollar t B) (δ : ℝ) (hδ : 0 < δ) (hδw : δ ≤ C.width)

def boundaryPullbackMap :
    RelativeModTwoCochains.complex (collarRegion C δ : Set (NonnegativeHalf t)) ⟶
      RelativeModTwoCochains.complex (boundary t) :=
  RelativeModTwoCochains.pullbackMap (ContinuousMap.id (NonnegativeHalf t))
    (boundary_subset_collar C δ hδ)

include hδw in
theorem boundaryPullbackMap_quasiIso : QuasiIso (boundaryPullbackMap C δ hδ) := by
  apply RelativeModTwoCochains.pullbackMap_quasiIso_of_absolute
  · intro n
    rw [singularHomologyMap_id]
    exact Function.bijective_id
  · intro n
    exact (homotopyEquivHomologyEquiv (boundaryCollarHomotopyEquiv C δ hδw hδ) n).bijective

def collarRelativeEquiv (p : ℕ) :
    RelativeModTwoCochains.Cohomology (collarRegion C δ : Set (NonnegativeHalf t)) p ≃ₗ[ℤ]
      RelativeModTwoCochains.Cohomology (boundary t) p := by
  let := boundaryPullbackMap_quasiIso C δ hδ hδw
  exact (isoOfQuasiIsoAt (boundaryPullbackMap C δ hδ) p).toLinearEquiv

theorem collarRelativeEquiv_toLinearMap (p : ℕ) :
    (collarRelativeEquiv C δ hδ hδw p).toLinearMap =
      RelativeModTwoCochains.cohomologyPullback (ContinuousMap.id (NonnegativeHalf t))
        (boundary_subset_collar C δ hδ) p := rfl

def interiorExcisionEquiv (p : ℕ) :
    RelativeModTwoCochains.Cohomology (collarRegion C δ : Set (NonnegativeHalf t)) p ≃ₗ[ℤ]
      RelativeModTwoCochains.Cohomology
        (RelativeSingularHomology.overlapIn (interiorDomain C : Set (NonnegativeHalf t))
          (collarRegion C δ : Set (NonnegativeHalf t))) p :=
  RelativeModTwoCochains.excisionEquiv _ _ (interiorDomain C).isOpen (collarRegion C δ).isOpen
    (interior_collar_cover C δ hδ) p

def boundaryToInteriorRelativeEquiv (p : ℕ) :
    RelativeModTwoCochains.Cohomology (boundary t) p ≃ₗ[ℤ]
      RelativeModTwoCochains.Cohomology
        (RelativeSingularHomology.overlapIn (interiorDomain C : Set (NonnegativeHalf t))
          (collarRegion C δ : Set (NonnegativeHalf t))) p :=
  (collarRelativeEquiv C δ hδ hδw p).symm.trans (interiorExcisionEquiv C δ hδ p)

theorem boundaryToInteriorRelativeEquiv_collar (p : ℕ)
    (c : RelativeModTwoCochains.Cohomology (collarRegion C δ : Set (NonnegativeHalf t)) p) :
    boundaryToInteriorRelativeEquiv C δ hδ hδw p (collarRelativeEquiv C δ hδ hδw p c) =
      interiorExcisionEquiv C δ hδ p c := by
  change interiorExcisionEquiv C δ hδ p
    ((collarRelativeEquiv C δ hδ hδw p).symm (collarRelativeEquiv C δ hδ hδw p c)) = _
  rw [LinearEquiv.symm_apply_apply]

end NoExoticSixSphere.TimeCollarDuality
