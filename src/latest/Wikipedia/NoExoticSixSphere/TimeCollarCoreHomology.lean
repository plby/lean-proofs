import Wikipedia.NoExoticSixSphere.TimeCollarCoreCohomology
import Wikipedia.NoExoticSixSphere.RelativeModExcision

/-!
# Actual relative homology maps from the compact cores to the boundary pair

The interior coordinate homeomorphism and actual open-cover excision give
the original core-to-collar inclusion map. The collar deformation gives
the original boundary-to-collar identity pair map. Their finite-coefficient
homology equivalences transport genuine supported fundamental classes.
-/

noncomputable section

open Set Function CategoryTheory ContinuousMap

namespace NoExoticSixSphere.TimeCollarDuality

open Wikipedia.HopfProblem.DegreeCollapse Wikipedia.HopfProblem.DegreeCollapse.TimeCollar
open Wikipedia.HopfProblem.SingularMayerVietoris Wikipedia.HopfProblem.PeriodTorusHigherHomology

variable {M B : Type} [TopologicalSpace M] [TopologicalSpace B] [CompactSpace M]
  {t : M → ℝ} (C : TimeCollar t B) (δ : ℝ) (hδ : 0 < δ)

def coreModPairMap (p : ℕ) :
    RelativeCoefficients.complex (ModuleCat.of ℤ (ZMod p))
      (compactCore C δ hδ : Set C.positiveInterior)ᶜ ⟶
    RelativeCoefficients.complex (ModuleCat.of ℤ (ZMod p))
      (collarRegion C δ : Set (NonnegativeHalf t)) :=
  RelativeCoefficients.mapChain (ModuleCat.of ℤ (ZMod p)) C.interiorToHalf
    (coreComplement_mapsTo_collar C δ hδ)

theorem coreModPairMap_quasiIso (p : ℕ) (hp : p ≠ 0) :
    QuasiIso (coreModPairMap C δ hδ p) := by
  let U : Set (NonnegativeHalf t) := interiorDomain C
  let V : Set (NonnegativeHalf t) := collarRegion C δ
  have hcoord := RelativeSingularHomology.mapChain_quasiIso_of_absolute
    (interiorCoordinateMap C) (coreComplement_mapsTo_overlap C δ hδ)
    (fun n ↦ (homotopyEquivHomologyEquiv (interiorHomeomorph C).toHomotopyEquiv n).bijective)
    (fun n ↦ (homotopyEquivHomologyEquiv
      (coreComplementHomeomorph C δ hδ).toHomotopyEquiv n).bijective)
  let := RelativeCoefficients.mapChain_mod_quasiIso_of_integral p hp
    (interiorCoordinateMap C) (coreComplement_mapsTo_overlap C δ hδ) hcoord
  let := RelativeCoefficients.modExcisionChainMap_quasiIso p hp U V
    (interiorDomain C).isOpen (collarRegion C δ).isOpen (interior_collar_cover C δ hδ)
  have hcomp : QuasiIso
      (RelativeCoefficients.mapChain (ModuleCat.of ℤ (ZMod p)) (interiorCoordinateMap C)
        (coreComplement_mapsTo_overlap C δ hδ) ≫ RelativeCoefficients.modExcisionChainMap p U V) :=
    inferInstance
  have he := RelativeCoefficients.mapChain_comp (ModuleCat.of ℤ (ZMod p))
    (interiorCoordinateMap C) (coreComplement_mapsTo_overlap C δ hδ)
    (subtypeInclusion U) (show MapsTo (subtypeInclusion U)
      (RelativeSingularHomology.overlapIn U V) V from fun _ hv ↦ hv)
  change QuasiIso (RelativeCoefficients.mapChain (ModuleCat.of ℤ (ZMod p))
    ((subtypeInclusion U).comp (interiorCoordinateMap C)) _)
  rw [he]
  exact hcomp

def coreModHomologyEquiv (p : ℕ) (hp : p ≠ 0) (q : ℕ) :
    RelativeCoefficients.ModHomology p (compactCore C δ hδ : Set C.positiveInterior)ᶜ q ≃ₗ[ℤ]
      RelativeCoefficients.ModHomology p (collarRegion C δ : Set (NonnegativeHalf t)) q := by
  let := coreModPairMap_quasiIso C δ hδ p hp
  exact (isoOfQuasiIsoAt (coreModPairMap C δ hδ p) q).toLinearEquiv

theorem coreModHomologyEquiv_toLinearMap (p : ℕ) (hp : p ≠ 0) (q : ℕ) :
    (coreModHomologyEquiv C δ hδ p hp q).toLinearMap =
      RelativeCoefficients.modMap p C.interiorToHalf (coreComplement_mapsTo_collar C δ hδ) q := rfl

variable (hδw : δ ≤ C.width)

include hδw in
theorem boundaryPairMap_quasiIso : QuasiIso
    (RelativeSingularHomology.mapChain (ContinuousMap.id (NonnegativeHalf t))
      (boundary_subset_collar C δ hδ)) := by
  apply RelativeSingularHomology.mapChain_quasiIso_of_absolute
  · intro q
    rw [singularHomologyMap_id]
    exact Function.bijective_id
  · intro q
    exact (homotopyEquivHomologyEquiv (boundaryCollarHomotopyEquiv C δ hδw hδ) q).bijective

include hδw in
theorem boundaryModPairMap_quasiIso (p : ℕ) (hp : p ≠ 0) : QuasiIso
    (RelativeCoefficients.mapChain (ModuleCat.of ℤ (ZMod p))
      (ContinuousMap.id (NonnegativeHalf t)) (boundary_subset_collar C δ hδ)) :=
  RelativeCoefficients.mapChain_mod_quasiIso_of_integral p hp _ _
    (boundaryPairMap_quasiIso C δ hδ hδw)

def boundaryToCollarModEquiv (p : ℕ) (hp : p ≠ 0) (q : ℕ) :
    RelativeCoefficients.ModHomology p (boundary t) q ≃ₗ[ℤ]
      RelativeCoefficients.ModHomology p (collarRegion C δ : Set (NonnegativeHalf t)) q := by
  let := boundaryModPairMap_quasiIso C δ hδ hδw p hp
  exact (isoOfQuasiIsoAt (RelativeCoefficients.mapChain (ModuleCat.of ℤ (ZMod p))
    (ContinuousMap.id (NonnegativeHalf t)) (boundary_subset_collar C δ hδ)) q).toLinearEquiv

theorem boundaryToCollarModEquiv_toLinearMap (p : ℕ) (hp : p ≠ 0) (q : ℕ) :
    (boundaryToCollarModEquiv C δ hδ hδw p hp q).toLinearMap =
      RelativeCoefficients.modMap p (ContinuousMap.id (NonnegativeHalf t))
        (boundary_subset_collar C δ hδ) q := rfl

def coreToBoundaryModEquiv (p : ℕ) (hp : p ≠ 0) (q : ℕ) :
    RelativeCoefficients.ModHomology p (compactCore C δ hδ : Set C.positiveInterior)ᶜ q ≃ₗ[ℤ]
      RelativeCoefficients.ModHomology p (boundary t) q :=
  (coreModHomologyEquiv C δ hδ p hp q).trans (boundaryToCollarModEquiv C δ hδ hδw p hp q).symm

theorem coreToBoundaryModEquiv_collar (p : ℕ) (hp : p ≠ 0) (q : ℕ)
    (c : RelativeCoefficients.ModHomology p (compactCore C δ hδ : Set C.positiveInterior)ᶜ q) :
    boundaryToCollarModEquiv C δ hδ hδw p hp q (coreToBoundaryModEquiv C δ hδ hδw p hp q c) =
      coreModHomologyEquiv C δ hδ p hp q c := LinearEquiv.apply_symm_apply _ _

end NoExoticSixSphere.TimeCollarDuality
