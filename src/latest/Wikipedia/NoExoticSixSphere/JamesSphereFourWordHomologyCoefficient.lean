import Wikipedia.NoExoticSixSphere.JamesSphereHopfPairTerms
import Wikipedia.NoExoticSixSphere.JamesSphereFirstStageHomologyRange

/-!
# The actual four-letter commutator word has sixth-homology coefficient two

The original Hopf map induces an H6 isomorphism from J(S3) to J(S6):
its composite with the original two-letter product is the actual S6
one-letter inclusion after the actual sphere pairing, and both factors
have proved H6 isomorphisms. Cancellation of this genuine map transfers
the evaluated six-term Hopf word to twice the original second-cell class.
-/

noncomputable section

open scoped Topology
open Wikipedia.HopfProblem SingularMayerVietoris SphereHomology PeriodTorusHigherHomology

namespace NoExoticSixSphere.JamesSphere.HopfPairTerms

theorem inclusion_six_bijective :
    Function.Bijective (singularHomologyMap (inclusion 6) 6) := by
  have he : inclusion 6 = (subtypeInclusion (James.stage (spherePole 6) 1)).comp
      (FirstStage.homeomorph 6 : C(Sphere 6, James.stage (spherePole 6) 1)) := by
    apply ContinuousMap.ext
    intro x
    rfl
  rw [he, singularHomologyMap_comp]
  exact (FirstStage.inclusion_homology_bijective 6 6 (by decide) (by decide) (by decide)).comp
    (homeomorphHomologyEquiv (FirstStage.homeomorph 6) 6).bijective

theorem hopf_two_word_square :
    (hopf 3).comp (TwoLetterHomology.wordMap 3) =
      (inclusion 6).comp (SecondStage.arrayPairing 3) := by
  apply ContinuousMap.ext
  intro v
  change hopf 3 (TwoLetterHomology.wordMap 3 v) = _
  rw [TwoLetterHomology.wordMap_apply]
  exact hopf_two_letters 3 (v 0) (v 1)

theorem hopf_six_bijective : Function.Bijective (singularHomologyMap (hopf 3) 6) := by
  have h : Function.Bijective (singularHomologyMap
      ((hopf 3).comp (TwoLetterHomology.wordMap 3)) 6) := by
    rw [hopf_two_word_square, singularHomologyMap_comp]
    exact inclusion_six_bijective.comp TwoLetterHomology.pairing_six_bijective
  rw [singularHomologyMap_comp] at h
  exact (Function.Bijective.of_comp_iff (singularHomologyMap (hopf 3) 6)
    TwoLetterHomology.wordMap_six_bijective).mp h

theorem hopf_secondCell_generator :
    singularHomologyMap (hopf 3) 6 SphereFourHopfHomology.SecondCell.generator =
      singularHomologyMap (inclusion 6) 6 (unitSphereTopClass 5) := by
  have h := congrArg (fun f ↦ singularHomologyMap f 6) hopf_two_word_square
  simp only [singularHomologyMap_comp] at h
  have he := LinearMap.congr_fun h TwoLetterHomology.productGenerator
  simpa only [LinearMap.comp_apply, TwoLetterHomology.wordMap_productGenerator,
    TwoLetterHomology.pairing_productGenerator] using he

theorem fourWord_productGenerator :
    singularHomologyMap (MeridianCommutator.fourWordMap 3 (by decide) 0) 6
      TwoLetterHomology.productGenerator =
        (2 : ℤ) • SphereFourHopfHomology.SecondCell.generator := by
  apply hopf_six_bijective.injective
  rw [map_zsmul, hopf_secondCell_generator]
  exact (LinearMap.congr_fun (singularHomologyMap_comp
    (MeridianCommutator.fourWordMap 3 (by decide) 0) (hopf 3) 6)
      TwoLetterHomology.productGenerator).symm.trans hopf_word_productGenerator

end NoExoticSixSphere.JamesSphere.HopfPairTerms
