import Wikipedia.NoExoticSixSphere.JamesSphereStageHomology
import Wikipedia.NoExoticSixSphere.JamesSphereSecondStageHomologyRange
import Wikipedia.NoExoticSixSphere.JamesSphereSecondCellHomologyGenerator

/-!
# The actual two-letter product generates sixth homology

The finite-stage projection/action splitting identifies the sixth
homology of the two-sphere product with that of the second James stage:
the other summand is H6(S3), which vanishes. The proved stage and
quotient comparisons then show that the ORIGINAL sphere pairing
induces an isomorphism on H6. Its inverse carries the genuine S6 top
class to a product class whose two-letter word image is precisely the
primitive second-cell generator already used for the Hopf coordinate.
-/

noncomputable section

open Wikipedia.HopfProblem SingularMayerVietoris PeriodTorusHigherHomology SphereHomology

namespace NoExoticSixSphere.JamesSphere.TwoLetterHomology

def arrayToFirst (n : ℕ) :
    (Fin 2 → Sphere n) ≃ₜ Sphere n × James.stage (spherePole n) 1 :=
  (Homeomorph.finTwoArrow : (Fin 2 → Sphere n) ≃ₜ Sphere n × Sphere n).trans
    ((Homeomorph.refl (Sphere n)).prodCongr (FirstStage.homeomorph n))

theorem presentation_eq_action (n : ℕ) :
    stagePresentation n 2 = (stageAction n 1).comp (arrayToFirst n : C(_, _)) := by
  apply ContinuousMap.ext
  intro v
  apply Subtype.ext
  change James.word (spherePole n) (List.ofFn v) =
    James.letter (spherePole n) (v 0) * James.letter (spherePole n) (v 1)
  simp only [List.ofFn_succ, List.ofFn_zero, James.word_cons, James.word_nil, mul_one]
  rfl

theorem stageAction_six_bijective :
    Function.Bijective (singularHomologyMap (stageAction 3 1) 6) := by
  let : Subsingleton (SingularHomology (James.stage (spherePole 3) 1) 6) :=
    subsingleton_singularHomology_of_homeomorph_sphere
      (by decide) (by decide) (by decide) (FirstStage.homeomorph 3).symm
  have h := StageHomology.projection_action_bijective 3 1 6 (by decide)
  constructor
  · intro a b hab
    exact h.injective (Prod.ext (Subsingleton.elim _ _) hab)
  · intro b
    obtain ⟨a, ha⟩ := h.surjective (0, b)
    exact ⟨a, congrArg Prod.snd ha⟩

theorem presentation_six_bijective :
    Function.Bijective (singularHomologyMap (stagePresentation 3 2) 6) := by
  rw [presentation_eq_action, singularHomologyMap_comp]
  exact stageAction_six_bijective.comp (homeomorphHomologyEquiv (arrayToFirst 3) 6).bijective

def wordMap (n : ℕ) : C((Fin 2 → Sphere n), WordHomology.Words n) :=
  (James.HomologyStages.inclusion (spherePole n) 2).comp (stagePresentation n 2)

theorem wordMap_apply (n : ℕ) (v : Fin 2 → Sphere n) :
    wordMap n v = inclusion n (v 0) * inclusion n (v 1) := by
  change James.word (spherePole n) (List.ofFn v) =
    James.letter (spherePole n) (v 0) * James.letter (spherePole n) (v 1)
  simp only [List.ofFn_succ, List.ofFn_zero, James.word_cons, James.word_nil, mul_one]
  rfl

theorem wordMap_six_bijective : Function.Bijective (singularHomologyMap (wordMap 3) 6) := by
  change Function.Bijective (singularHomologyMap
    ((James.HomologyStages.inclusion (spherePole 3) 2).comp (stagePresentation 3 2)) 6)
  rw [singularHomologyMap_comp]
  exact (SecondStageHomologyRange.fullMap_bijective 3 (by decide) 6
    (by decide) (by decide)).comp presentation_six_bijective

theorem pairing_quotient_square (n : ℕ) :
    (FirstStageQuotient.bottomSphere n).comp (SecondStage.arrayPairing n) =
      (FirstStageQuotient.quotientMap n).comp (wordMap n) := by
  apply ContinuousMap.ext
  intro v
  change FirstStageQuotient.bottomSphere n (SecondStage.arrayPairing n v) = _
  rw [← SecondStage.collapse_presentation, FirstStageQuotient.bottomSphere_collapse]
  rfl

theorem pairing_six_bijective :
    Function.Bijective (singularHomologyMap (SecondStage.arrayPairing 3) 6) := by
  have hb : Function.Bijective (singularHomologyMap
      ((FirstStageQuotient.bottomSphere 3).comp (SecondStage.arrayPairing 3)) 6) := by
    rw [pairing_quotient_square, singularHomologyMap_comp]
    exact (FirstStageQuotient.quotient_homology_bijective_above 3 5 (by decide) (by decide)).comp
      wordMap_six_bijective
  rw [singularHomologyMap_comp] at hb
  exact (Function.Bijective.of_comp_iff'
    (FirstStageQuotient.bottomSphere_homology_bijective_range 3 (by decide) 6
      (by decide) (by decide)) _).mp hb

def pairingHomologyEquiv :
    SingularHomology (Fin 2 → Sphere 3) 6 ≃ₗ[ℤ] SingularHomology (Sphere 6) 6 :=
  LinearEquiv.ofBijective (singularHomologyMap (SecondStage.arrayPairing 3) 6) pairing_six_bijective

def productGenerator : SingularHomology (Fin 2 → Sphere 3) 6 :=
  pairingHomologyEquiv.symm (unitSphereTopClass 5)

theorem pairing_productGenerator :
    singularHomologyMap (SecondStage.arrayPairing 3) 6 productGenerator = unitSphereTopClass 5 :=
  pairingHomologyEquiv.apply_symm_apply _

theorem productGenerator_generates :
    Function.Surjective (fun k : ℤ ↦ k • productGenerator) := by
  intro a
  obtain ⟨k, hk⟩ := unitSphereTopClass_generates 5 (pairingHomologyEquiv a)
  refine ⟨k, pairingHomologyEquiv.injective ?_⟩
  rw [map_zsmul]
  change k • pairingHomologyEquiv (pairingHomologyEquiv.symm (unitSphereTopClass 5)) = _
  rw [LinearEquiv.apply_symm_apply]
  exact hk

theorem wordMap_productGenerator : singularHomologyMap (wordMap 3) 6 productGenerator =
    SphereFourHopfHomology.SecondCell.generator := by
  apply (FirstStageQuotient.quotient_homology_bijective_above 3 5 (by decide) (by decide)).injective
  have he := congrArg (fun f ↦ singularHomologyMap f 6) (pairing_quotient_square 3)
  rw [singularHomologyMap_comp, singularHomologyMap_comp] at he
  calc
    _ = singularHomologyMap (FirstStageQuotient.bottomSphere 3) 6
        (singularHomologyMap (SecondStage.arrayPairing 3) 6 productGenerator) :=
      (LinearMap.congr_fun he productGenerator).symm
    _ = singularHomologyMap (FirstStageQuotient.bottomSphere 3) 6 (unitSphereTopClass 5) := by
      rw [pairing_productGenerator]
    _ = _ := SphereFourHopfHomology.SecondCell.quotient_generator.symm

theorem homology_ext_of_pairing {X : Type} [TopologicalSpace X] (f g : C(Sphere 6, X))
    (h : singularHomologyMap (f.comp (SecondStage.arrayPairing 3)) 6 =
      singularHomologyMap (g.comp (SecondStage.arrayPairing 3)) 6) :
    singularHomologyMap f 6 = singularHomologyMap g 6 := by
  rw [singularHomologyMap_comp, singularHomologyMap_comp] at h
  apply LinearMap.ext
  intro a
  obtain ⟨b, rfl⟩ := pairing_six_bijective.surjective a
  exact LinearMap.congr_fun h b

end NoExoticSixSphere.JamesSphere.TwoLetterHomology
