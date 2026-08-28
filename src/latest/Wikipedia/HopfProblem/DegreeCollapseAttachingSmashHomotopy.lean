import Wikipedia.HopfProblem.DegreeCollapseSmashLoopHomotopy
import Wikipedia.NoExoticSixSphere.JamesSphereAttachingSmashCube
import Wikipedia.NoExoticSixSphere.SpherePairingCubeCoordinates

/-!
# The original attaching correction equals the meridian smash map in homotopy

The existing comparison on the product fixed only its common pole.
Straightening it on the fat wedge now gives an actual based homotopy
of the two original smash-sphere maps in every positive letter dimension.
For four-dimensional letters, the literal eight cube and its uncurrying
identify the original source-corrected attaching map into the five-sphere.
No nonvanishing of its composite with the first-stem generator is asserted.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.DegreeCollapse.AttachingSmashHomotopy

open NoExoticSixSphere JamesSphere AttachingSquare

theorem correctedSmashSphere_homotopic (n : ℕ) (hn : 0 < n) :
    (correctedSmashSphere n hn).HomotopicRel (normalizedSmashSphere n)
      {spherePole (n + n)} := by
  apply SmashLoopHomotopy.exists_based n
    (correctedSmashSphere_pole n hn) (normalizedSmashSphere_pole n)
  exact ((normalizedToCorrectedHomotopy n hn).symm.trans
    (normalizedToSmashHomotopy n)).cast
      (ContinuousMap.ext (correctedSmashSphere_pairing n hn)).symm rfl

theorem correctedSmashSphere_class (n : ℕ) (hn : 0 < n) :
    SmoothCube.sphereClass ⟨correctedSmashSphere n hn, correctedSmashSphere_pole n hn⟩ =
      SmoothCube.sphereClass ⟨normalizedSmashSphere n, normalizedSmashSphere_pole n⟩ :=
  (SmoothCube.sphereClass_eq_iff (by omega : 0 < n + n) _ _).mpr
    (correctedSmashSphere_homotopic n hn)

theorem pairing_tail_cube_four (v : Parameter 4) :
    SecondStage.arrayPairing 4 (sphereParameters 4 v) =
      SmoothCube.quotient 8 (tailCoordinates 4 v) := by
  change pairing 4 (SmoothCube.quotient 4 (v 0), SmoothCube.quotient 4 (v 1)) = _
  rw [PairingCoordinates.pairing_cubes]
  apply congrArg (SmoothCube.quotient 8)
  funext i
  fin_cases i <;> rfl

theorem correctedSmashSphere_cube_four (u : Fin 8 → I) :
    correctedSmashSphere 4 (by decide) (SmoothCube.quotient 8 u) = correctedCube 4 u := by
  have hp := pairing_tail_cube_four ((tailCoordinates 4).symm u)
  rw [Homeomorph.apply_symm_apply] at hp
  rw [← hp, correctedSmashSphere_pairing, correctedSphereLoops_parameters]
  rfl

theorem correctedSmashSphere_toGenLoop_four :
    SmoothCube.toGenLoop ⟨correctedSmashSphere 4 (by decide),
      correctedSmashSphere_pole 4 (by decide)⟩ = correctedCube 4 := by
  apply Subtype.ext
  apply ContinuousMap.ext
  exact correctedSmashSphere_cube_four

def normalizedEightCube : GenLoop (Fin 8) (Path (spherePole 5) (spherePole 5))
    (Path.refl (spherePole 5)) :=
  SmoothCube.toGenLoop ⟨normalizedSmashSphere 4, normalizedSmashSphere_pole 4⟩

theorem correctedEightClass :
    (Quotient.mk' (correctedCube 4) : π_ 8 (Path (spherePole 5) (spherePole 5))
      (Path.refl (spherePole 5))) = Quotient.mk' normalizedEightCube := by
  have h := correctedSmashSphere_class 4 (by decide)
  change Quotient.mk' (SmoothCube.toGenLoop ⟨correctedSmashSphere 4 (by decide),
    correctedSmashSphere_pole 4 (by decide)⟩) = Quotient.mk' normalizedEightCube at h
  rwa [correctedSmashSphere_toGenLoop_four] at h

theorem sourceFiveClass_eq_meridian :
    SmoothCube.sphereClass ⟨sourceSphereAttaching 4, sourceSphereAttaching_pole 4⟩ =
      (Quotient.mk' (GeneralizedLoopCurrying.uncurry normalizedEightCube) :
        π_ 9 (Sphere 5) (spherePole 5)) := by
  have h := congrArg (GeneralizedLoopCurrying.homotopyEquiv 8 (spherePole 5)) correctedEightClass
  change Quotient.mk' (GeneralizedLoopCurrying.uncurry (correctedCube 4)) =
    Quotient.mk' (GeneralizedLoopCurrying.uncurry normalizedEightCube) at h
  rw [correctedCube_uncurry] at h
  exact h

def meridianFiveMap : SmoothCube.BasedMap 9 (Sphere 5) (spherePole 5) :=
  (SmoothCube.basedEquiv (by decide : 0 < 9)).symm
    (GeneralizedLoopCurrying.uncurry normalizedEightCube)

theorem meridianFiveMap_class : SmoothCube.sphereClass meridianFiveMap =
    (Quotient.mk' (GeneralizedLoopCurrying.uncurry normalizedEightCube) :
      π_ 9 (Sphere 5) (spherePole 5)) :=
  congrArg Quotient.mk' ((SmoothCube.basedEquiv (by decide : 0 < 9)).apply_symm_apply _)

theorem sourceFive_homotopic : (sourceSphereAttaching 4).HomotopicRel meridianFiveMap.val
    {spherePole 9} :=
  (SmoothCube.sphereClass_eq_iff (by decide : 0 < 9) _ _).mp
    (sourceFiveClass_eq_meridian.trans meridianFiveMap_class.symm)

theorem sourceFiveHom_comparison (d : ℕ) [NeZero d]
    (c : π_ d (Sphere 9) (spherePole 9)) :
    sourceSphereAttachingHom 4 d c =
      HigherHomotopy.map meridianFiveMap.val meridianFiveMap.property c :=
  HigherHomotopy.map_eq_of_based_homotopy _ _ (sourceSphereAttaching_pole 4)
    meridianFiveMap.property sourceFive_homotopic.some c

end Wikipedia.HopfProblem.DegreeCollapse.AttachingSmashHomotopy
