import Wikipedia.NoExoticSixSphere.JamesSphereFourWordHomologyCoefficient
import Wikipedia.NoExoticSixSphere.JamesSphereAttachingHopfComparison

/-!
# The original S4 attaching relation has absolute Hopf coordinate two

The evaluated four-letter word, actual loop-space homology comparison,
and primitive native S6 cube identify the meridian adjoint class up to
sign as twice the original second-cell generator. The already proved
comparison with the ORIGINAL attaching relation then gives absolute
integer coefficient two. Its torsion coordinate is not evaluated here.
-/

noncomputable section

open scoped Topology
open Wikipedia.HopfProblem SingularMayerVietoris SphereHomology PeriodTorusHigherHomology

namespace NoExoticSixSphere.JamesSphere.AttachingSquare

theorem normalizedSmashSphere_secondCell :
    singularHomologyMap (normalizedSmashSphere 3) 6 (unitSphereTopClass 5) =
      singularHomologyMap (orderedLoopComparison 3) 6
        ((2 : ℤ) • SphereFourHopfHomology.SecondCell.generator) := by
  calc
    _ = singularHomologyMap (correctedSmashSphere 3 (by decide)) 6 (unitSphereTopClass 5) :=
      (LinearMap.congr_fun correctedSmashSphere_homology (unitSphereTopClass 5)).symm
    _ = singularHomologyMap (normalizedSphereCommutator 3) 6
        TwoLetterHomology.productGenerator := correctedSmashSphere_topClass
    _ = singularHomologyMap ((orderedLoopComparison 3).comp
        (MeridianCommutator.fourWordMap 3 (by decide) 0)) 6
          TwoLetterHomology.productGenerator :=
      LinearMap.congr_fun (commutator_fourWord_homology 3 (by decide) 0 6) _
    _ = _ := by
      rw [singularHomologyMap_comp, LinearMap.comp_apply, HopfPairTerms.fourWord_productGenerator]

theorem meridian_adjoint_cube_generator :
    singularHomologyMap (orderedLoopComparison 3) 6
      (SphereFourHopfHomology.adjointClass MeridianCommutator.fourClass) =
        singularHomologyMap (normalizedSmashSphere 3) 6 SphereSixCube.generator := by
  have h := orderedLoopComparison_adjointClass normalizedSmashCube
  rw [normalizedSmashCube_uncurry] at h
  have hn := SixthHurewiczNative.natural (normalizedSmashSphere 3)
    (spherePole 6) (Path.refl (spherePole 4)) (normalizedSmashSphere_pole 3)
    SphereSixCube.identityClass
  exact h.trans hn.symm

theorem meridian_adjoint_eq_two_or_neg :
    SphereFourHopfHomology.adjointClass MeridianCommutator.fourClass =
        (2 : ℤ) • SphereFourHopfHomology.SecondCell.generator ∨
      SphereFourHopfHomology.adjointClass MeridianCommutator.fourClass =
        -((2 : ℤ) • SphereFourHopfHomology.SecondCell.generator) := by
  rcases SphereSixCube.generator_eq_top_or_neg with h | h
  · left
    apply (orderedLoopComparison_homology_bijective 3 6 (by decide)).injective
    rw [meridian_adjoint_cube_generator, h]
    exact normalizedSmashSphere_secondCell
  · right
    apply (orderedLoopComparison_homology_bijective 3 6 (by decide)).injective
    rw [meridian_adjoint_cube_generator, h, map_neg, map_neg,
      normalizedSmashSphere_secondCell]

theorem originalAttachingClass_hopf_natAbs_two :
    Int.natAbs SphereFiveEighth.relation.1.toAdd = 2 := by
  rw [originalAttachingClass_hopf_natAbs, SphereFourHopfHomology.coordinate_hurewicz]
  rcases meridian_adjoint_eq_two_or_neg with h | h
  · rw [h, SphereFourHopfHomology.SecondCell.multiple_coordinate_natAbs]
    rfl
  · rw [h, map_neg, Int.natAbs_neg, SphereFourHopfHomology.SecondCell.multiple_coordinate_natAbs]
    rfl

end NoExoticSixSphere.JamesSphere.AttachingSquare
