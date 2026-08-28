import Wikipedia.HopfProblem.ThirdHurewiczCubeSubdivisionNativeChamberFlats
import Wikipedia.HopfProblem.ThirdHurewiczCubeSubdivisionRecoveryTetrahedra

/-!
# Native comparison with an oriented tetrahedron chamber

The common-face interpolation is an actual relative cube homotopy to an
input-permuted Duffy loop. The already-proved native permutation sign and
Duffy-to-simplex homotopy then give the signed actual tetrahedron class.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.ThirdHurewicz

variable {X : Type*} [TopologicalSpace X] {x : X}

/-- The literal common-face homotopy to the correctly input-permuted Duffy loop. -/
def nativeCubeOrderedDuffyHomotopy (p : GenLoop (Fin 3) X x)
    (hp : NativeCubeInternalBased p) (f : C(NativeCube, NativeCube))
    (e : Equiv.Perm (Fin 3))
    (hf : ∀ u ∈ Cube.boundary (Fin 3), p (f u) = x)
    (hfg : ∀ u ∈ Cube.boundary (Fin 3),
      NativeCubeSameFlat (f u) (nativeOrderedDuffyMap e u)) :
    (nativeCubePullbackLoop p f hf).val.HomotopyRel
      (permuteCubeLoop (nativeDuffyCubeLoop p hp e) e).val (Cube.boundary (Fin 3)) :=
  nativeCubeLinearHomotopy p hp f (nativeOrderedDuffyMap e) hf
    (fun u hu => nativeDuffyCube_based p hp e _ (permuteCubeCoordinates_boundary e u hu)) hfg

theorem nativeCubeClass_commonOrderedDuffy (p : GenLoop (Fin 3) X x)
    (hp : NativeCubeInternalBased p) (f : C(NativeCube, NativeCube))
    (e : Equiv.Perm (Fin 3))
    (hf : ∀ u ∈ Cube.boundary (Fin 3), p (f u) = x)
    (hfg : ∀ u ∈ Cube.boundary (Fin 3),
      NativeCubeSameFlat (f u) (nativeOrderedDuffyMap e u)) :
    nativeCubeClass (nativeCubePullbackLoop p f hf) =
      ((Equiv.Perm.sign e : ℤˣ) : ℤ) • nativeCubeClass (nativeDuffyCubeLoop p hp e) :=
  (nativeCubeClass_homotopic ⟨nativeCubeOrderedDuffyHomotopy p hp f e hf hfg⟩).trans
    (permuteCubeLoop_additiveClass (nativeDuffyCubeLoop p hp e) e)

variable {Y : Type} [TopologicalSpace Y] {y : Y}

/-- The comparison ends at the original based singular tetrahedron, not at
an abstract presentation or only at its singular homology image. -/
theorem nativeCubeClass_commonOrderedTetrahedron (p : GenLoop (Fin 3) Y y)
    (hp : NativeCubeInternalBased p) (f : C(NativeCube, NativeCube))
    (e : Equiv.Perm (Fin 3))
    (hf : ∀ u ∈ Cube.boundary (Fin 3), p (f u) = y)
    (hfg : ∀ u ∈ Cube.boundary (Fin 3),
      NativeCubeSameFlat (f u) (nativeOrderedDuffyMap e u)) :
    nativeCubeClass (nativeCubePullbackLoop p f hf) =
      Geometry.cubeOrientation e • basedThreeSimplexClass (nativeBasedCubeTetrahedron p hp e) := by
  simpa only [nativeDuffyCubeClass_eq_basedThreeSimplexClass, Geometry.cubeOrientation] using
    nativeCubeClass_commonOrderedDuffy p hp f e hf hfg

end Wikipedia.HopfProblem.ThirdHurewicz
