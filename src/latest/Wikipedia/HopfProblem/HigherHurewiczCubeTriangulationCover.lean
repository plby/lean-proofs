import Wikipedia.HopfProblem.HigherHurewiczCubeTriangulationCoordinates

/-!
# The finite permutation-simplex quotient cover of a cube

Sorting the coordinates gives an actual simplex preimage of every cube
point. The finite disjoint union of these compact simplices is a quotient
cover, also after taking the product with the homotopy interval.
-/

noncomputable section

open Topology
open scoped unitInterval

namespace Wikipedia.HopfProblem.HigherHurewicz.CubeTriangulation

open FirstHurewicz

variable {n : ℕ}

/-- Every cube point is in an actual affine permutation simplex. -/
theorem exists_cubeSimplex (u : CubeN n) :
    ∃ e : Equiv.Perm (Fin n), ∃ s : Simplex n, cubeSimplex e s = u := by
  obtain ⟨e, he⟩ := exists_sortedPermutation u
  exact ⟨e, cubeSimplexInverse e ⟨u, he⟩, cubeSimplex_inverse e ⟨u, he⟩⟩

/-- The actual map from the finite disjoint union of simplices onto the cube. -/
def cubeSimplexCover (n : ℕ) : C((Σ _e : Equiv.Perm (Fin n), Simplex n), CubeN n) where
  toFun a := cubeSimplex a.fst a.snd
  continuous_toFun := continuous_sigma fun e => (cubeSimplex e).continuous

@[simp] theorem cubeSimplexCover_apply (e : Equiv.Perm (Fin n)) (s : Simplex n) :
    cubeSimplexCover n ⟨e, s⟩ = cubeSimplex e s := rfl

theorem cubeSimplexCover_surjective (n : ℕ) : Function.Surjective (cubeSimplexCover n) := by
  intro u
  obtain ⟨e, s, hs⟩ := exists_cubeSimplex u
  exact ⟨⟨e, s⟩, hs⟩

theorem cubeSimplexCover_isQuotientMap (n : ℕ) : IsQuotientMap (cubeSimplexCover n) :=
  IsQuotientMap.of_surjective_continuous (cubeSimplexCover_surjective n)
    (cubeSimplexCover n).continuous

/-- One actual permutation-simplex cylinder in the cube cylinder. -/
def cubeSimplexCylinder (e : Equiv.Perm (Fin n)) : C(I × Simplex n, I × CubeN n) :=
  (ContinuousMap.id I).prodMap (cubeSimplex e)

@[simp] theorem cubeSimplexCylinder_apply (e : Equiv.Perm (Fin n))
    (r : I) (s : Simplex n) :
    cubeSimplexCylinder e (r, s) = (r, cubeSimplex e s) := rfl

/-- The finite disjoint union of simplex cylinders covers the whole cube cylinder. -/
def cubeCylinderCover (n : ℕ) :
    C((Σ _e : Equiv.Perm (Fin n), I × Simplex n), I × CubeN n) where
  toFun a := cubeSimplexCylinder a.fst a.snd
  continuous_toFun := continuous_sigma fun e => (cubeSimplexCylinder e).continuous

@[simp] theorem cubeCylinderCover_apply (e : Equiv.Perm (Fin n)) (r : I) (s : Simplex n) :
    cubeCylinderCover n ⟨e, (r, s)⟩ = (r, cubeSimplex e s) := rfl

theorem cubeCylinderCover_surjective (n : ℕ) : Function.Surjective (cubeCylinderCover n) := by
  rintro ⟨r, u⟩
  obtain ⟨e, s, rfl⟩ := exists_cubeSimplex u
  exact ⟨⟨e, (r, s)⟩, rfl⟩

/-- A quotient cover independent of any separation property of a later target. -/
theorem cubeCylinderCover_isQuotientMap (n : ℕ) : IsQuotientMap (cubeCylinderCover n) :=
  IsQuotientMap.of_surjective_continuous (cubeCylinderCover_surjective n)
    (cubeCylinderCover n).continuous

end Wikipedia.HopfProblem.HigherHurewicz.CubeTriangulation
