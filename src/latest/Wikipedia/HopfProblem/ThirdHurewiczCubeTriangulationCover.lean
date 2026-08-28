import Wikipedia.HopfProblem.ThirdHurewiczCubeTriangulationCoverCoordinates

/-!
# The finite tetrahedral quotient cover of the actual cube

Sorting the three coordinates supplies an actual simplex preimage for
every cube point. Compactness of the finite union of simplices proves
the quotient-map property, also after adjoining the homotopy interval.
-/

noncomputable section

open Topology
open scoped unitInterval

namespace Wikipedia.HopfProblem.ThirdHurewicz.CubeTriangulation

open FirstHurewicz Geometry

/-- Every cube point belongs to one of the actual affine tetrahedra. -/
theorem exists_cubeTetrahedron (u : Cube3) :
    ∃ e : Equiv.Perm (Fin 3), ∃ s : Simplex 3, cubeTetrahedron e s = u := by
  obtain ⟨e, he⟩ := exists_sortedPermutation u
  exact ⟨e, cubeTetrahedronInverse e ⟨u, he⟩, cubeTetrahedron_inverse e ⟨u, he⟩⟩

/-- The actual map from the finite disjoint union of tetrahedra onto the cube. -/
def cubeSimplexCover : C((Σ _e : Equiv.Perm (Fin 3), Simplex 3), Cube3) where
  toFun a := cubeTetrahedron a.fst a.snd
  continuous_toFun := continuous_sigma fun e => (cubeTetrahedron e).continuous

@[simp] theorem cubeSimplexCover_apply (e : Equiv.Perm (Fin 3)) (s : Simplex 3) :
    cubeSimplexCover ⟨e, s⟩ = cubeTetrahedron e s := rfl

theorem cubeSimplexCover_surjective : Function.Surjective cubeSimplexCover := by
  intro u
  obtain ⟨e, s, hs⟩ := exists_cubeTetrahedron u
  exact ⟨⟨e, s⟩, hs⟩

theorem cubeSimplexCover_isQuotientMap : IsQuotientMap cubeSimplexCover :=
  IsQuotientMap.of_surjective_continuous cubeSimplexCover_surjective cubeSimplexCover.continuous

/-- One actual tetrahedral cylinder in the cube cylinder. -/
def cubeTetrahedronCylinder (e : Equiv.Perm (Fin 3)) : C(I × Simplex 3, I × Cube3) :=
  (ContinuousMap.id I).prodMap (cubeTetrahedron e)

@[simp] theorem cubeTetrahedronCylinder_apply (e : Equiv.Perm (Fin 3))
    (r : I) (s : Simplex 3) :
    cubeTetrahedronCylinder e (r, s) = (r, cubeTetrahedron e s) := rfl

/-- The finite disjoint union of tetrahedral cylinders covers the entire cube cylinder. -/
def cubeCylinderCover : C((Σ _e : Equiv.Perm (Fin 3), I × Simplex 3), I × Cube3) where
  toFun a := cubeTetrahedronCylinder a.fst a.snd
  continuous_toFun := continuous_sigma fun e => (cubeTetrahedronCylinder e).continuous

@[simp] theorem cubeCylinderCover_apply (e : Equiv.Perm (Fin 3))
    (r : I) (s : Simplex 3) :
    cubeCylinderCover ⟨e, (r, s)⟩ = (r, cubeTetrahedron e s) := rfl

theorem cubeCylinderCover_surjective : Function.Surjective cubeCylinderCover := by
  rintro ⟨r, u⟩
  obtain ⟨e, s, rfl⟩ := exists_cubeTetrahedron u
  exact ⟨⟨e, (r, s)⟩, rfl⟩

/-- A genuine quotient map; no separation assumption on a later pasted target is needed. -/
theorem cubeCylinderCover_isQuotientMap : IsQuotientMap cubeCylinderCover :=
  IsQuotientMap.of_surjective_continuous cubeCylinderCover_surjective cubeCylinderCover.continuous

end Wikipedia.HopfProblem.ThirdHurewicz.CubeTriangulation
