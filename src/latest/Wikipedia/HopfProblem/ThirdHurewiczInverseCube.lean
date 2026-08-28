import Wikipedia.HopfProblem.ThirdHurewiczChainClasses
import Wikipedia.HopfProblem.ThirdHurewiczCubeNormalization
import Wikipedia.HopfProblem.ThirdHurewiczCubeSubdivisionChains
import Wikipedia.HopfProblem.ThirdHurewiczCubeSubdivisionRecovery

/-!
# The native chain assignment on the original fundamental cube

The actual cubical fundamental chain has the six original affine
tetrahedra with their genuine permutation signs. Applying the constructed
native homotopy assignment retains precisely those signed normalized
three-simplex classes.
-/

noncomputable section

open scoped Topology

namespace Wikipedia.HopfProblem.ThirdHurewicz

open FirstHurewicz Geometry

variable {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
variable (x : X) [Subsingleton (π_ 2 X x)]

/-- Exact evaluation of the native assignment on the original cube chain. -/
theorem threeSimplexClassOperator_cubeChain_sum (p : GenLoop (Fin 3) X x) :
    threeSimplexClassOperator x (cubeChain p) =
      ∑ e : Equiv.Perm (Fin 3), cubeOrientation e •
        basedThreeSimplexClass (normalizedThreeSimplex x (p.val.comp (cubeTetrahedron e))) := by
  rw [CubeSubdivision.cubeChain_eq_sum_tetrahedra]
  simp only [map_sum, map_zsmul, threeSimplexClassOperator_simplex]

/-- The literal six restrictions of the normalized cube are exactly the
three-simplices used in the original chain assignment. -/
theorem normalizedCube_tetrahedron (p : GenLoop (Fin 3) X x) (e : Equiv.Perm (Fin 3)) :
    nativeBasedCubeTetrahedron (normalizedCube x p) (normalizedCube_internalBased x p) e =
      normalizedThreeSimplex x (p.val.comp (cubeTetrahedron e)) := by
  apply Subtype.ext
  exact normalizedCube_cell x p e

/-- The chain assignment on the genuine original fundamental cube cycle
recovers the actual native third-homotopy class, before any homology descent. -/
theorem threeSimplexClassOperator_cubeChain (p : GenLoop (Fin 3) X x) :
    threeSimplexClassOperator x (cubeChain p) = Additive.ofMul (⟦p⟧ : π_ 3 X x) := by
  have h := nativeCubeSubdivision_homotopy_class p (normalizedCube x p)
    (normalizationCubeHomotopy x p) (normalizedCube_internalBased x p)
  simp only [normalizedCube_tetrahedron] at h
  exact (threeSimplexClassOperator_cubeChain_sum x p).trans h.symm

end Wikipedia.HopfProblem.ThirdHurewicz
