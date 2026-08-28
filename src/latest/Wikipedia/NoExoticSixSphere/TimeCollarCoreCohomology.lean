import Wikipedia.NoExoticSixSphere.TimeCollarRelativeCohomology
import Wikipedia.NoExoticSixSphere.SupportedModTwoCohomology
import Wikipedia.NoExoticSixSphere.RelativeModTwoPullbackFunctor

/-!
# Boundary-relative cohomology on each actual positive compact core

Excision first uses the literal interior subset of the half. Its identity
homeomorphism with the original positive open submanifold preserves the
actual core complement. Their pair pullbacks identify boundary-relative
cohomology with supported cohomology on that original interior, with the
specified inclusion map as the forward map.
-/

noncomputable section

open Set Function CategoryTheory ContinuousMap

namespace NoExoticSixSphere.TimeCollarDuality

open Wikipedia.HopfProblem.DegreeCollapse Wikipedia.HopfProblem.DegreeCollapse.TimeCollar
open Wikipedia.HopfProblem.SingularMayerVietoris Wikipedia.HopfProblem.PeriodTorusHigherHomology
open RelativeModTwoCochains

variable {M B : Type} [TopologicalSpace M] [TopologicalSpace B]
  {t : M → ℝ} (C : TimeCollar t B)

def interiorCoordinateMap : C(C.positiveInterior, interiorDomain C) :=
  ⟨interiorHomeomorph C, (interiorHomeomorph C).continuous⟩

variable [CompactSpace M] (δ : ℝ) (hδ : 0 < δ)

theorem coreComplement_mapsTo_overlap : MapsTo (interiorCoordinateMap C)
    (compactCore C δ hδ : Set C.positiveInterior)ᶜ
    (RelativeSingularHomology.overlapIn (interiorDomain C : Set (NonnegativeHalf t))
      (collarRegion C δ : Set (NonnegativeHalf t))) :=
  fun _ hp ↦ coreComplement_mapsTo_collar C δ hδ hp

theorem overlap_mapsTo_coreComplement : MapsTo (interiorHomeomorph C).symm
    (RelativeSingularHomology.overlapIn (interiorDomain C : Set (NonnegativeHalf t))
      (collarRegion C δ : Set (NonnegativeHalf t)))
    (compactCore C δ hδ : Set C.positiveInterior)ᶜ := by
  intro p hp hmem
  exact not_lt_of_ge ((mem_compactCore_iff C δ hδ _).mp hmem) hp

def coreComplementHomeomorph :
    ↥((compactCore C δ hδ : Set C.positiveInterior)ᶜ) ≃ₜ
      RelativeSingularHomology.overlapIn (interiorDomain C : Set (NonnegativeHalf t))
        (collarRegion C δ : Set (NonnegativeHalf t)) where
  toFun p := ⟨interiorHomeomorph C p.val, coreComplement_mapsTo_overlap C δ hδ p.property⟩
  invFun p := ⟨(interiorHomeomorph C).symm p.val, overlap_mapsTo_coreComplement C δ hδ p.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := ((interiorHomeomorph C).continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun :=
    ((interiorHomeomorph C).symm.continuous.comp continuous_subtype_val).subtype_mk _

def coreCoordinateEquiv (p : ℕ) :
    Cohomology (RelativeSingularHomology.overlapIn
      (interiorDomain C : Set (NonnegativeHalf t))
      (collarRegion C δ : Set (NonnegativeHalf t))) p ≃ₗ[ℤ]
      SupportedModTwoCohomology.Cohomology (compactCore C δ hδ : Set C.positiveInterior) p :=
  equivalenceOfAbsolute (interiorCoordinateMap C) (coreComplement_mapsTo_overlap C δ hδ)
    (fun n ↦ (homotopyEquivHomologyEquiv (interiorHomeomorph C).toHomotopyEquiv n).bijective)
    (fun n ↦ (homotopyEquivHomologyEquiv
      (coreComplementHomeomorph C δ hδ).toHomotopyEquiv n).bijective) p

theorem coreCoordinateEquiv_toLinearMap (p : ℕ) :
    (coreCoordinateEquiv C δ hδ p).toLinearMap =
      cohomologyPullback (interiorCoordinateMap C) (coreComplement_mapsTo_overlap C δ hδ) p := rfl

def coreExcisionEquiv (p : ℕ) :
    Cohomology (collarRegion C δ : Set (NonnegativeHalf t)) p ≃ₗ[ℤ]
      SupportedModTwoCohomology.Cohomology (compactCore C δ hδ : Set C.positiveInterior) p :=
  (interiorExcisionEquiv C δ hδ p).trans (coreCoordinateEquiv C δ hδ p)

theorem coreExcisionEquiv_toLinearMap (p : ℕ) :
    (coreExcisionEquiv C δ hδ p).toLinearMap =
      cohomologyPullback C.interiorToHalf (coreComplement_mapsTo_collar C δ hδ) p := by
  change (coreCoordinateEquiv C δ hδ p).toLinearMap.comp
    (interiorExcisionEquiv C δ hδ p).toLinearMap = _
  rw [coreCoordinateEquiv_toLinearMap]
  unfold interiorExcisionEquiv
  rw [excisionEquiv_toLinearMap]
  exact (cohomologyPullback_comp (interiorCoordinateMap C) (coreComplement_mapsTo_overlap C δ hδ)
    (subtypeInclusion (interiorDomain C : Set (NonnegativeHalf t))) (fun _ hp ↦ hp) p).symm

variable (hδw : δ ≤ C.width)

def boundaryCoreEquiv (p : ℕ) :
    Cohomology (boundary t) p ≃ₗ[ℤ]
      SupportedModTwoCohomology.Cohomology (compactCore C δ hδ : Set C.positiveInterior) p :=
  (collarRelativeEquiv C δ hδ hδw p).symm.trans (coreExcisionEquiv C δ hδ p)

theorem boundaryCoreEquiv_collar (p : ℕ)
    (c : Cohomology (collarRegion C δ : Set (NonnegativeHalf t)) p) :
    boundaryCoreEquiv C δ hδ hδw p (collarRelativeEquiv C δ hδ hδw p c) =
      coreExcisionEquiv C δ hδ p c := by
  change coreExcisionEquiv C δ hδ p
    ((collarRelativeEquiv C δ hδ hδw p).symm (collarRelativeEquiv C δ hδ hδw p c)) = _
  rw [LinearEquiv.symm_apply_apply]

end NoExoticSixSphere.TimeCollarDuality
