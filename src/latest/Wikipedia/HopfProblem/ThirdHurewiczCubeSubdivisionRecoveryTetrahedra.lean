import Wikipedia.HopfProblem.ThirdHurewiczCubeSubdivisionNativeDuffy
import Wikipedia.HopfProblem.ThirdHurewiczCubeSubdivisionRecoveryTetrahedraBasic

/-!
# Recovery of the actual tetrahedron classes from Duffy cube maps

The Duffy and nested-minimum parametrizations send each parameter-boundary
face into one common affine plane: a cube boundary plane or an internal
coordinate-equality plane. Their literal linear interpolation is therefore
a homotopy of native generalized loops relative to the entire boundary.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.ThirdHurewicz

/-- Corresponding boundary points lie in one common based affine plane. -/
theorem nativeDuffyCube_tetrahedron_sameFlat (e : Equiv.Perm (Fin 3)) (u : NativeCube)
    (hu : u ∈ Cube.boundary (Fin 3)) :
    NativeCubeSameFlat (nativeDuffyCube e u) (nativeCubeTetrahedronQuotient e u) := by
  rcases hu with ⟨i, hi | hi⟩
  · fin_cases i
    · change u 0 = 0 at hi
      exact .zero (e 0) (by simp [hi]) (by simp [hi])
    · change u 1 = 0 at hi
      refine .zero (e 1) (by simp [hi]) ?_
      simp [hi]
    · change u 2 = 0 at hi
      refine .zero (e 2) (by simp [hi]) ?_
      simp [hi]
  · fin_cases i
    · change u 0 = 1 at hi
      exact .one (e 0) (by simp [hi]) (by simp [hi])
    · change u 1 = 1 at hi
      refine .equal (e 0) (e 1) (e.injective.ne (by decide)) (by simp [hi]) ?_
      simp [hi, min_eq_left (show u 0 ≤ (1 : I) from (u 0).property.2)]
    · change u 2 = 1 at hi
      refine .equal (e 1) (e 2) (e.injective.ne (by decide)) (by simp [hi]) ?_
      simp [hi, min_eq_left (show u 1 ≤ (1 : I) from (u 1).property.2)]

variable {X : Type} [TopologicalSpace X] {x : X}

/-- The actual boundary-relative affine homotopy from the Duffy loop to the
native loop of its original singular tetrahedron. -/
def nativeDuffyCubeTetrahedronHomotopy (p : GenLoop (Fin 3) X x)
    (hp : NativeCubeInternalBased p) (e : Equiv.Perm (Fin 3)) :
    (nativeDuffyCubeLoop p hp e).val.HomotopyRel
      (basedThreeSimplexLoop (nativeBasedCubeTetrahedron p hp e)).val
      (Cube.boundary (Fin 3)) :=
  nativeCubeLinearHomotopy p hp (nativeDuffyCube e) (nativeCubeTetrahedronQuotient e)
    (nativeDuffyCube_based p hp e) (nativeCubeTetrahedronQuotient_based p hp e)
    (nativeDuffyCube_tetrahedron_sameFlat e)

theorem nativeDuffyCube_homotopic_basedThreeSimplexLoop (p : GenLoop (Fin 3) X x)
    (hp : NativeCubeInternalBased p) (e : Equiv.Perm (Fin 3)) :
    GenLoop.Homotopic (nativeDuffyCubeLoop p hp e)
      (basedThreeSimplexLoop (nativeBasedCubeTetrahedron p hp e)) :=
  ⟨nativeDuffyCubeTetrahedronHomotopy p hp e⟩

/-- Equality in Mathlib's actual third homotopy group, for every coordinate
permutation, with no orientation sign or combinatorial quotient substituted. -/
theorem nativeDuffyCubeClass_eq_basedThreeSimplexClass (p : GenLoop (Fin 3) X x)
    (hp : NativeCubeInternalBased p) (e : Equiv.Perm (Fin 3)) :
    nativeCubeClass (nativeDuffyCubeLoop p hp e) =
      basedThreeSimplexClass (nativeBasedCubeTetrahedron p hp e) :=
  nativeCubeClass_homotopic (nativeDuffyCube_homotopic_basedThreeSimplexLoop p hp e)

end Wikipedia.HopfProblem.ThirdHurewicz
