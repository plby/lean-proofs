import Wikipedia.HopfProblem.ThirdHurewiczCubeSubdivisionNativeChamberComparison
import Wikipedia.HopfProblem.ThirdHurewiczCubeSubdivisionNativeCutSpecializationLoops
import Wikipedia.HopfProblem.ThirdHurewiczCubeSubdivisionRecoveryPermutationSum

/-!
# The five nonidentity chamber classes with their native orientation signs

Every formula is obtained from the actual common-face relative homotopy,
the native input-permutation sign, and the actual Duffy-to-simplex homotopy.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.ThirdHurewicz

variable {X : Type} [TopologicalSpace X] {x : X}

theorem nativeMiddleChamberLoop_class (p : GenLoop (Fin 3) X x)
    (hp : NativeCubeInternalBased p) :
    nativeCubeClass (nativeMiddleChamberLoop p hp) =
      -basedThreeSimplexClass (nativeBasedCubeTetrahedron p hp (Equiv.swap 1 2)) := by
  simpa [nativeMiddleChamberLoop, Geometry.cubeOrientation, Equiv.Perm.sign_swap'] using
    nativeCubeClass_commonOrderedTetrahedron p hp nativeMiddleChamberMap (Equiv.swap 1 2)
      (nativeCubeMap_based_of_commonLeft p hp nativeMiddleChamber_flats)
      nativeMiddleChamber_flats

theorem nativeHighChamberLoop_class (p : GenLoop (Fin 3) X x)
    (hp : NativeCubeInternalBased p) :
    nativeCubeClass (nativeHighChamberLoop p hp) =
      basedThreeSimplexClass (nativeBasedCubeTetrahedron p hp nativeCubeCycle201) := by
  simpa [nativeHighChamberLoop] using
    nativeCubeClass_commonOrderedTetrahedron p hp nativeHighChamberMap nativeCubeCycle201
      (nativeCubeMap_based_of_commonLeft p hp nativeHighChamber_flats)
      nativeHighChamber_flats

theorem nativeUpperLowChamberLoop_class (p : GenLoop (Fin 3) X x)
    (hp : NativeCubeInternalBased p) :
    nativeCubeClass (nativeUpperLowChamberLoop p hp) =
      -basedThreeSimplexClass (nativeBasedCubeTetrahedron p hp (Equiv.swap 0 1)) := by
  simpa [nativeUpperLowChamberLoop, Geometry.cubeOrientation, Equiv.Perm.sign_swap'] using
    nativeCubeClass_commonOrderedTetrahedron p hp nativeUpperLowChamberMap (Equiv.swap 0 1)
      (nativeCubeMap_based_of_commonLeft p hp nativeUpperLowChamber_flats)
      nativeUpperLowChamber_flats

theorem nativeUpperMiddleChamberLoop_class (p : GenLoop (Fin 3) X x)
    (hp : NativeCubeInternalBased p) :
    nativeCubeClass (nativeUpperMiddleChamberLoop p hp) =
      basedThreeSimplexClass (nativeBasedCubeTetrahedron p hp nativeCubeCycle120) := by
  simpa [nativeUpperMiddleChamberLoop] using
    nativeCubeClass_commonOrderedTetrahedron p hp nativeUpperMiddleChamberMap nativeCubeCycle120
      (nativeCubeMap_based_of_commonLeft p hp nativeUpperMiddleChamber_flats)
      nativeUpperMiddleChamber_flats

theorem nativeUpperHighChamberLoop_class (p : GenLoop (Fin 3) X x)
    (hp : NativeCubeInternalBased p) :
    nativeCubeClass (nativeUpperHighChamberLoop p hp) =
      -basedThreeSimplexClass (nativeBasedCubeTetrahedron p hp (Equiv.swap 0 2)) := by
  simpa [nativeUpperHighChamberLoop, Geometry.cubeOrientation, Equiv.Perm.sign_swap'] using
    nativeCubeClass_commonOrderedTetrahedron p hp nativeUpperHighChamberMap (Equiv.swap 0 2)
      (nativeCubeMap_based_of_commonLeft p hp nativeUpperHighChamber_flats)
      nativeUpperHighChamber_flats

end Wikipedia.HopfProblem.ThirdHurewicz
