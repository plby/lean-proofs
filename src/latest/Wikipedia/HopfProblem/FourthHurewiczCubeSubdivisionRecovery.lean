import Wikipedia.HopfProblem.FourthHurewiczCubeSubdivisionNativeInduction
import Wikipedia.HopfProblem.FourthHurewiczCubeSubdivisionRecoveryChambers

/-!
# The oriented simplex subdivision of an actual native cube

For every dimension at least two, coordinate insertion recovers the native
class as the signed sum of the actual affine simplex restrictions. In
dimension four this is the sum over the twenty-four ordered four-simplices.
The proof uses native concatenation, coordinate permutations, and literal
boundary-relative homotopies throughout.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.HigherHurewicz.NativeSubdivision

variable {n : ℕ} [Nontrivial (Fin n)]
variable {X : Type*} [TopologicalSpace X] {x : X}

/-- Native recovery by the actual signed simplex restrictions, in every dimension. -/
theorem nativeClass_eq_sum_simplices (p : GenLoop (Fin n) X x)
    (hp : NativeCubeInternalBased p) :
    nativeClass p = ∑ e : Equiv.Perm (Fin n),
      CubeTriangulation.cubeOrientation e •
        SimplexGeometry.basedSimplexClass (nativeBasedCubeSimplex p hp e) := by
  calc
    nativeClass p = ∑ e : Equiv.Perm (Fin n),
        nativeClass (extendedChamberLoop p hp (le_refl n) (orderedDuffyChart e)) :=
      nativeClass_eq_sum_partialChambers p hp n (le_refl n)
    _ = _ := Finset.sum_congr rfl fun e _ =>
      nativeClass_chamber_eq_orientedSimplex p hp e (orderedDuffyChart e)

/-- The subdivision identity for Mathlib's original generalized-loop quotient. -/
theorem nativeCubeSubdivision_class (p : GenLoop (Fin n) X x)
    (hp : NativeCubeInternalBased p) :
    Additive.ofMul (⟦p⟧ : π_ n X x) = ∑ e : Equiv.Perm (Fin n),
      CubeTriangulation.cubeOrientation e •
        SimplexGeometry.basedSimplexClass (nativeBasedCubeSimplex p hp e) :=
  nativeClass_eq_sum_simplices p hp

/-- A genuine relative homotopy to a normalized cube gives the same recovery
for the class of the original cube. -/
theorem nativeCubeSubdivision_homotopy_class (p q : GenLoop (Fin n) X x)
    (H : p.val.HomotopyRel q.val (Cube.boundary (Fin n)))
    (hq : NativeCubeInternalBased q) :
    nativeClass p = ∑ e : Equiv.Perm (Fin n),
      CubeTriangulation.cubeOrientation e •
        SimplexGeometry.basedSimplexClass (nativeBasedCubeSimplex q hq e) :=
  (nativeClass_homotopic ⟨H⟩).trans (nativeClass_eq_sum_simplices q hq)

end Wikipedia.HopfProblem.HigherHurewicz.NativeSubdivision
