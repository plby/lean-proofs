import Wikipedia.HopfProblem.ThirdHurewiczCubeSubdivisionNativeChamberClasses
import Wikipedia.HopfProblem.ThirdHurewiczCubeSubdivisionNativeCutSpecialization

/-!
# Genuine native third-homotopy recovery from the six cube tetrahedra

Two successive actual coordinate cuts produce the six product chambers.
Their boundary-relative common-face homotopies identify them with the six
original affine tetrahedra, with precisely the geometric permutation signs.
The result is in Mathlib's native third homotopy group, without a Hurewicz
injectivity, degree, or combinatorial-presentation assumption.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.ThirdHurewicz

variable {X : Type} [TopologicalSpace X] {x : X}

/-- Native cubical subdivision into the six original oriented affine tetrahedra. -/
theorem nativeCubeClass_eq_sum_tetrahedra (p : GenLoop (Fin 3) X x)
    (hp : NativeCubeInternalBased p) :
    nativeCubeClass p = ∑ e : Equiv.Perm (Fin 3),
      Geometry.cubeOrientation e • basedThreeSimplexClass (nativeBasedCubeTetrahedron p hp e) := by
  rw [sum_oriented_nativeCubeRecoveryPermutations,
    nativeCubeClass_prisms p hp, nativeLowerPrismClass_eq, nativeUpperPrismClass_eq,
    nativeDuffyCubeClass_eq_basedThreeSimplexClass,
    nativeMiddleChamberLoop_class, nativeHighChamberLoop_class,
    nativeUpperLowChamberLoop_class, nativeUpperMiddleChamberLoop_class,
    nativeUpperHighChamberLoop_class]
  simp only [sub_eq_add_neg, add_assoc]

/-- The same recovery formula displays the literal quotient class of the original cube. -/
theorem nativeCubeSubdivision_class (p : GenLoop (Fin 3) X x)
    (hp : NativeCubeInternalBased p) :
    Additive.ofMul (⟦p⟧ : π_ 3 X x) = ∑ e : Equiv.Perm (Fin 3),
      Geometry.cubeOrientation e • basedThreeSimplexClass (nativeBasedCubeTetrahedron p hp e) :=
  nativeCubeClass_eq_sum_tetrahedra p hp

/-- Recovery after an actual boundary-relative normalization homotopy.
The input class remains that of the original cube; the six tetrahedra are
the literal restrictions of the normalized cube. -/
theorem nativeCubeSubdivision_homotopy_class (p q : GenLoop (Fin 3) X x)
    (H : p.val.HomotopyRel q.val (Cube.boundary (Fin 3)))
    (hq : NativeCubeInternalBased q) :
    nativeCubeClass p = ∑ e : Equiv.Perm (Fin 3),
      Geometry.cubeOrientation e • basedThreeSimplexClass (nativeBasedCubeTetrahedron q hq e) :=
  (nativeCubeClass_homotopic ⟨H⟩).trans (nativeCubeClass_eq_sum_tetrahedra q hq)

end Wikipedia.HopfProblem.ThirdHurewicz
