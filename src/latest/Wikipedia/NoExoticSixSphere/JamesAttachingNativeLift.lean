import Wikipedia.NoExoticSixSphere.JamesComparisonHomotopyReflection
import Wikipedia.NoExoticSixSphere.JamesSphereAttachingSmashCube
import Wikipedia.NoExoticSixSphere.JamesSphereCommutatorFourLetters
import Wikipedia.NoExoticSixSphere.JamesSphereThreeRetraction

/-!
# The original corrected attaching class lifted to the James space

Choose a based sphere representative of the inverse original ordered
comparison. Its ordered loop image is based-homotopic to the original
corrected smash map, by equality of their native classes. The actual
product-sphere homotopies and finite-domain homotopy reflection then
compare this representative with the four-letter James word itself.
No homology-to-homotopy inference is used.
-/

noncomputable section

open scoped Topology unitInterval
open Wikipedia.HopfProblem

namespace NoExoticSixSphere.JamesSphere.ThreeRetraction

open AttachingSquare

def correctedAdjoint : π_ 6 (WordHomology.Words 3) 1 :=
  (InclusionRange.orderedComparison 3 (by decide) 6).symm correctedSevenClass

def correctedRepresentative : SmoothCube.BasedMap 6 (WordHomology.Words 3) 1 :=
  (SmoothCube.sphereClass_surjective (by decide : 0 < 6) correctedAdjoint).choose

theorem correctedRepresentative_class :
    SmoothCube.sphereClass correctedRepresentative = correctedAdjoint :=
  (SmoothCube.sphereClass_surjective (by decide : 0 < 6) correctedAdjoint).choose_spec

theorem correctedRepresentative_comparison :
    ((orderedLoopComparison 3).comp correctedRepresentative.val).HomotopicRel
      (correctedSmashSphere 3 (by decide)) {spherePole 6} := by
  let f : SmoothCube.BasedMap 6 (Path (spherePole 4) (spherePole 4))
      (Path.refl (spherePole 4)) :=
    ⟨(orderedLoopComparison 3).comp correctedRepresentative.val,
      (congrArg (orderedLoopComparison 3) correctedRepresentative.property).trans
        (orderedLoopComparison_one 3)⟩
  have he : SmoothCube.sphereClass f = Quotient.mk' (correctedCube 3) := by
    apply (GeneralizedLoopCurrying.homotopyMulEquiv 6 (spherePole 4)).injective
    calc
      GeneralizedLoopCurrying.homotopyMulEquiv 6 (spherePole 4)
          (SmoothCube.sphereClass f) =
          InclusionRange.orderedComparison 3 (by decide) 6
            (SmoothCube.sphereClass correctedRepresentative) :=
        (orderedComparison_loopMap 3 (by decide) 6
          (SmoothCube.sphereClass correctedRepresentative)).symm
      _ = correctedSevenClass := by
        rw [correctedRepresentative_class]
        exact MulEquiv.apply_symm_apply _ _
      _ = _ := rfl
  have hg : SmoothCube.sphereClass ⟨correctedSmashSphere 3 (by decide),
      correctedSmashSphere_pole 3 (by decide)⟩ = Quotient.mk' (correctedCube 3) := by
    change Quotient.mk' (SmoothCube.toGenLoop _) = _
    rw [correctedSmashSphere_toGenLoop]
  exact (SmoothCube.sphereClass_eq_iff (by decide) f
    ⟨correctedSmashSphere 3 (by decide), correctedSmashSphere_pole 3 (by decide)⟩).mp
      (he.trans hg.symm)

theorem orderedComparison_array_homotopic_reflect (n : ℕ) (hn : 2 ≤ n)
    (u v : C((Fin 2 → Sphere 3), WordHomology.Words n))
    (H : ((orderedLoopComparison n).comp u).Homotopic
      ((orderedLoopComparison n).comp v)) : u.Homotopic v := by
  let e : (Fin 2 → Sphere 3) ≃ₜ Sphere 3 × Sphere 3 := Homeomorph.finTwoArrow
  let back : C(Sphere 3 × Sphere 3, (Fin 2 → Sphere 3)) := e.symm
  let forward : C((Fin 2 → Sphere 3), Sphere 3 × Sphere 3) := e
  have h := HomotopyComparison.orderedComparison_threeSphereProduct_homotopic_reflect n hn
    (u.comp back) (v.comp back) (H.comp (ContinuousMap.Homotopic.refl back))
  have h' := h.comp (ContinuousMap.Homotopic.refl forward)
  have hc (w : C((Fin 2 → Sphere 3), WordHomology.Words n)) :
      (w.comp back).comp forward = w := by
    apply ContinuousMap.ext
    intro z
    exact congrArg w (e.symm_apply_apply z)
  rw [hc u, hc v] at h'
  exact h'

theorem correctedRepresentative_fourWord_comparison :
    ((orderedLoopComparison 3).comp
      (correctedRepresentative.val.comp (SecondStage.arrayPairing 3))).Homotopic
      ((orderedLoopComparison 3).comp (MeridianCommutator.fourWordMap 3 (by decide) 0)) := by
  have h₁ := correctedRepresentative_comparison.some.toHomotopy.compContinuousMap
    (SecondStage.arrayPairing 3)
  have hc : (correctedSmashSphere 3 (by decide)).comp (SecondStage.arrayPairing 3) =
      correctedSphereLoops 3 (by decide) :=
    ContinuousMap.ext (correctedSmashSphere_pairing 3 (by decide))
  have h₂ := (normalizedToCorrectedHomotopy 3 (by decide)).toHomotopy.symm
  have h₃ := (ContinuousMap.Homotopic.refl
    ((reorderPaths 3).comp Moore.Loop.normalizationMap)).comp
      (MeridianCommutator.commutator_fourWord_homotopic 3 (by decide) 0)
  have h₁' : ((orderedLoopComparison 3).comp
      (correctedRepresentative.val.comp (SecondStage.arrayPairing 3))).Homotopic
      (correctedSphereLoops 3 (by decide)) := by
    rw [← hc]
    exact ⟨h₁⟩
  exact h₁'.trans ((show (correctedSphereLoops 3 (by decide)).Homotopic
    (normalizedSphereCommutator 3) from ⟨h₂⟩).trans h₃)

theorem correctedRepresentative_fourWord :
    (correctedRepresentative.val.comp (SecondStage.arrayPairing 3)).Homotopic
      (MeridianCommutator.fourWordMap 3 (by decide) 0) :=
  orderedComparison_array_homotopic_reflect 3 (by decide) _ _
    correctedRepresentative_fourWord_comparison

theorem correctedRepresentative_retraction_class :
    SmoothCube.sphereClass ⟨retraction.comp correctedRepresentative.val,
      (congrArg retraction correctedRepresentative.property).trans retraction_one⟩ =
      sectionHom 6 correctedSevenClass := by
  change retractionHom 6 (SmoothCube.sphereClass correctedRepresentative) = _
  rw [correctedRepresentative_class]
  rfl

end NoExoticSixSphere.JamesSphere.ThreeRetraction
