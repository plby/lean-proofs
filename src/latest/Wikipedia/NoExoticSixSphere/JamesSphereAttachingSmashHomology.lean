import Wikipedia.NoExoticSixSphere.JamesSphereAttachingCommutatorHomology
import Wikipedia.NoExoticSixSphere.JamesSphereTwoLetterHomology

/-!
# The corrected source and Moore smash maps agree on sixth homology

The terminal corrected family descends through the ORIGINAL sphere
pairing because it is constant on the actual fat wedge. That pairing
is now proved surjective on H6. Consequently the checked product-family
homotopy compares the two actual smash maps on H6 itself. The genuine
S6 top class corresponds to the previously constructed product generator.
This is a homology equality, not a native homotopy-class equality.
-/

noncomputable section

open Topology
open scoped unitInterval
open Wikipedia.HopfProblem SingularMayerVietoris PeriodTorusHigherHomology SphereHomology

namespace NoExoticSixSphere.JamesSphere.AttachingSquare

theorem correctedSphereLoops_respects_pairing (n : ℕ) (hn : 0 < n)
    (v w : SphereMooreCommutator.Parameter n)
    (h : SecondStage.arrayPairing n v = SecondStage.arrayPairing n w) :
    correctedSphereLoops n hn v = correctedSphereLoops n hn w := by
  rcases pairing_fiber_condition n (v 0, v 1) (w 0, w 1) h with hp | hp
  · have hv := (SphereMooreCommutator.arrayPairing_pole_iff n v).mp hp
    have hw := (SphereMooreCommutator.arrayPairing_pole_iff n w).mp (h.symm.trans hp)
    exact (correctedSphereLoops_boundary n hn v hv).trans
      (correctedSphereLoops_boundary n hn w hw).symm
  · have hvw : v = w := by
      funext i
      fin_cases i
      · exact congrArg Prod.fst hp
      · exact congrArg Prod.snd hp
    exact congrArg (correctedSphereLoops n hn) hvw

def correctedSmashSphere (n : ℕ) (hn : 0 < n) :
    C(Sphere (n + n), Path (spherePole (n + 1)) (spherePole (n + 1))) :=
  IsQuotientMap.lift (f := SecondStage.arrayPairing n)
    (SphereMooreCommutator.isQuotientMap_arrayPairing n) (correctedSphereLoops n hn)
    (correctedSphereLoops_respects_pairing n hn)

theorem correctedSmashSphere_pairing (n : ℕ) (hn : 0 < n)
    (v : SphereMooreCommutator.Parameter n) :
    correctedSmashSphere n hn (SecondStage.arrayPairing n v) = correctedSphereLoops n hn v :=
  ContinuousMap.congr_fun (IsQuotientMap.lift_comp
    (SphereMooreCommutator.isQuotientMap_arrayPairing n) (correctedSphereLoops n hn)
    (correctedSphereLoops_respects_pairing n hn)) v

theorem correctedSmashSphere_pole (n : ℕ) (hn : 0 < n) :
    correctedSmashSphere n hn (spherePole (n + n)) = Path.refl (spherePole (n + 1)) := by
  have hp := (SphereMooreCommutator.arrayPairing_pole_iff n (SphereMooreCommutator.point n)).mpr
    (SphereMooreCommutator.boundaryPoint n).property
  rw [← hp, correctedSmashSphere_pairing]
  exact correctedSphereLoops_boundary n hn _ (SphereMooreCommutator.boundaryPoint n).property

theorem correctedSmashSphere_homology :
    singularHomologyMap (correctedSmashSphere 3 (by decide)) 6 =
      singularHomologyMap (normalizedSmashSphere 3) 6 := by
  apply TwoLetterHomology.homology_ext_of_pairing
  have hf : (correctedSmashSphere 3 (by decide)).comp (SecondStage.arrayPairing 3) =
      correctedSphereLoops 3 (by decide) :=
    ContinuousMap.ext (correctedSmashSphere_pairing 3 (by decide))
  rw [hf]
  exact corrected_homology_eq_smash 3 (by decide) 6

theorem correctedSmashSphere_topClass :
    singularHomologyMap (correctedSmashSphere 3 (by decide)) 6 (unitSphereTopClass 5) =
      singularHomologyMap (normalizedSphereCommutator 3) 6 TwoLetterHomology.productGenerator := by
  have hf : (correctedSmashSphere 3 (by decide)).comp (SecondStage.arrayPairing 3) =
      correctedSphereLoops 3 (by decide) :=
    ContinuousMap.ext (correctedSmashSphere_pairing 3 (by decide))
  have h := congrArg (fun f ↦ singularHomologyMap f 6) hf
  rw [singularHomologyMap_comp, corrected_homology_eq_commutator 3 (by decide) 6] at h
  have he := LinearMap.congr_fun h TwoLetterHomology.productGenerator
  change singularHomologyMap (correctedSmashSphere 3 (by decide)) 6
    (singularHomologyMap (SecondStage.arrayPairing 3) 6
      TwoLetterHomology.productGenerator) = _ at he
  rwa [TwoLetterHomology.pairing_productGenerator] at he

end NoExoticSixSphere.JamesSphere.AttachingSquare
