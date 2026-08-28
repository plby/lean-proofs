import Wikipedia.HopfProblem.ThirdHurewiczCubeSubdivisionNativeBasic
import Wikipedia.HopfProblem.ThirdHurewiczThreeSimplexBasic
import Wikipedia.HopfProblem.ThirdHurewiczCubeSubdivisionGeometry

/-!
# Based ordered tetrahedra and their native cube quotients

A cube based on every internal equality plane restricts to a genuine based
singular three-simplex on each ordered tetrahedron. Composing that actual
tetrahedron with the native simplex quotient gives explicit nested-minimum
coordinates on the cube.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.ThirdHurewicz

open FirstHurewicz

/-- The actual ordered tetrahedron composed with the native simplex quotient. -/
def nativeCubeTetrahedronQuotient (e : Equiv.Perm (Fin 3)) : C(NativeCube, NativeCube) :=
  (Geometry.cubeTetrahedron e).comp threeSimplexQuotient

theorem nativeCubeTetrahedronQuotient_apply (e : Equiv.Perm (Fin 3)) (u : NativeCube) :
    nativeCubeTetrahedronQuotient e u = Geometry.cubeTetrahedron e (threeSimplexQuotient u) :=
  rfl

@[simp] theorem nativeCubeTetrahedronQuotient_coordinate_zero
    (e : Equiv.Perm (Fin 3)) (u : NativeCube) :
    nativeCubeTetrahedronQuotient e u (e 0) = u 0 := by
  apply Subtype.ext
  change (Geometry.cubeTetrahedron e (threeSimplexQuotient u) (e 0) : ℝ) = (u 0 : ℝ)
  rw [Geometry.cubeTetrahedron_coordinate_zero, threeSimplexQuotient_one,
    threeSimplexQuotient_two, threeSimplexQuotient_three]
  ring

@[simp] theorem nativeCubeTetrahedronQuotient_coordinate_one
    (e : Equiv.Perm (Fin 3)) (u : NativeCube) :
    nativeCubeTetrahedronQuotient e u (e 1) = min (u 0) (u 1) := by
  apply Subtype.ext
  change (Geometry.cubeTetrahedron e (threeSimplexQuotient u) (e 1) : ℝ) =
    min (u 0 : ℝ) (u 1 : ℝ)
  rw [Geometry.cubeTetrahedron_coordinate_one, threeSimplexQuotient_two,
    threeSimplexQuotient_three]
  exact sub_add_cancel _ _

@[simp] theorem nativeCubeTetrahedronQuotient_coordinate_two
    (e : Equiv.Perm (Fin 3)) (u : NativeCube) :
    nativeCubeTetrahedronQuotient e u (e 2) = min (u 0) (min (u 1) (u 2)) := by
  apply Subtype.ext
  change (Geometry.cubeTetrahedron e (threeSimplexQuotient u) (e 2) : ℝ) =
    min (u 0 : ℝ) (min (u 1 : ℝ) (u 2 : ℝ))
  rw [Geometry.cubeTetrahedron_coordinate_two, threeSimplexQuotient_three]

theorem nativeCubeTetrahedron_coordinate_sum (s : Simplex 3) :
    s 0 + s 1 + s 2 + s 3 = 1 := by
  have hs := stdSimplex.sum_eq_one s
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hs
  change s 0 + (s 1 + (s 2 + s 3)) = 1 at hs
  linarith

variable {X : Type} [TopologicalSpace X] {x : X}

theorem nativeCubeTetrahedron_based (p : GenLoop (Fin 3) X x)
    (hp : NativeCubeInternalBased p) (e : Equiv.Perm (Fin 3))
    (s : Simplex 3) (hs : s ∈ threeSimplexBoundary) :
    p (Geometry.cubeTetrahedron e s) = x := by
  rcases hs with ⟨i, hi⟩
  fin_cases i
  · change s 0 = 0 at hi
    apply p.property
    refine ⟨e 0, Or.inr ?_⟩
    apply Subtype.ext
    change (Geometry.cubeTetrahedron e s (e 0) : ℝ) = 1
    rw [Geometry.cubeTetrahedron_coordinate_zero]
    linarith [nativeCubeTetrahedron_coordinate_sum s]
  · change s 1 = 0 at hi
    apply hp _ (e 0) (e 1) (e.injective.ne (by decide))
    apply Subtype.ext
    simp [hi]
  · change s 2 = 0 at hi
    apply hp _ (e 1) (e 2) (e.injective.ne (by decide))
    apply Subtype.ext
    simp [hi]
  · change s 3 = 0 at hi
    apply p.property
    refine ⟨e 2, Or.inl ?_⟩
    apply Subtype.ext
    simpa using hi

/-- The literal restriction to the ordered singular tetrahedron. -/
def nativeBasedCubeTetrahedron (p : GenLoop (Fin 3) X x)
    (hp : NativeCubeInternalBased p) (e : Equiv.Perm (Fin 3)) : BasedThreeSimplex x :=
  ⟨p.val.comp (Geometry.cubeTetrahedron e), nativeCubeTetrahedron_based p hp e⟩

@[simp] theorem nativeBasedCubeTetrahedron_val (p : GenLoop (Fin 3) X x)
    (hp : NativeCubeInternalBased p) (e : Equiv.Perm (Fin 3)) :
    (nativeBasedCubeTetrahedron p hp e).val = p.val.comp (Geometry.cubeTetrahedron e) :=
  rfl

@[simp] theorem nativeBasedCubeTetrahedron_loop_apply (p : GenLoop (Fin 3) X x)
    (hp : NativeCubeInternalBased p) (e : Equiv.Perm (Fin 3)) (u : NativeCube) :
    basedThreeSimplexLoop (nativeBasedCubeTetrahedron p hp e) u =
      p (nativeCubeTetrahedronQuotient e u) := rfl

theorem nativeCubeTetrahedronQuotient_based (p : GenLoop (Fin 3) X x)
    (hp : NativeCubeInternalBased p) (e : Equiv.Perm (Fin 3)) (u : NativeCube)
    (hu : u ∈ Cube.boundary (Fin 3)) : p (nativeCubeTetrahedronQuotient e u) = x :=
  nativeCubeTetrahedron_based p hp e _ (threeSimplexQuotient_boundary u hu)

theorem nativeCubeTetrahedronQuotientLoop_eq_basedThreeSimplexLoop
    (p : GenLoop (Fin 3) X x) (hp : NativeCubeInternalBased p) (e : Equiv.Perm (Fin 3)) :
    nativeCubePullbackLoop p (nativeCubeTetrahedronQuotient e)
        (nativeCubeTetrahedronQuotient_based p hp e) =
      basedThreeSimplexLoop (nativeBasedCubeTetrahedron p hp e) := rfl

end Wikipedia.HopfProblem.ThirdHurewicz
