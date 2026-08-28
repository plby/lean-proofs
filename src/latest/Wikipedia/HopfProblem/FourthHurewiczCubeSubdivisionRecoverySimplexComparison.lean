import Wikipedia.HopfProblem.FourthHurewiczCubeSubdivisionNativeDuffyOrdered
import Wikipedia.HopfProblem.FourthHurewiczCubeSubdivisionRecoverySimplex

/-!
# Recovering oriented actual simplex classes from compatible cube charts

Common-face affine interpolation, native permutation parity, and the actual
Duffy-to-simplex homotopy together recover the signed original simplex class.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.HigherHurewicz.NativeSubdivision

open SimplexGeometry CubeTriangulation

variable {X : Type*} [TopologicalSpace X] {x : X}

/-- Every face-compatible ordered chart has the signed class of the actual affine cell. -/
theorem nativeClass_commonOrderedSimplex {n : ℕ} [Nontrivial (Fin n)]
    (p : GenLoop (Fin n) X x) (hp : NativeCubeInternalBased p)
    (e : Equiv.Perm (Fin n)) (f : C(NativeCube (Fin n), NativeCube (Fin n)))
    (hf : ∀ u ∈ Cube.boundary (Fin n), p (f u) = x)
    (hfg : ∀ u ∈ Cube.boundary (Fin n), NativeCubeSameFlat (f u) (nativeOrderedDuffyMap e u)) :
    nativeClass (nativeCubePullbackLoop p f hf) =
      cubeOrientation e • basedSimplexClass (nativeBasedCubeSimplex p hp e) := by
  rw [nativeClass_commonOrderedDuffy p hp e f hf hfg,
    nativeDuffyCubeClass_eq_basedSimplexClass]
  rfl

end Wikipedia.HopfProblem.HigherHurewicz.NativeSubdivision
