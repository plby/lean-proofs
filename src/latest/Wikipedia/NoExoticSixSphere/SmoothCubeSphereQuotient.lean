import Wikipedia.NoExoticSixSphere.SmoothCubeCoordinates
import Wikipedia.HopfProblem.SixSphereCubeCollapseTopology
import Wikipedia.HopfProblem.SixSphereCubeInterior

/-!
# An actual native cube-boundary quotient with smooth interior charts

The source is Mathlib's original finite cube and its original boundary.
Coordinatewise tangent compactification collapses precisely that boundary
to the chosen stereographic pole. Its restriction to the interior is exactly
the inverse of the constructed smooth open-cube chart of the original sphere.
-/

noncomputable section

open Set Function Topology
open scoped unitInterval OnePoint

namespace NoExoticSixSphere.SmoothCube

open GLOrthonormalization Wikipedia.HopfProblem.SixSphereCube

def vectorOfCube (n : ℕ) (u : Fin n → I) : Vector n :=
  WithLp.toLp 2 (fun i ↦ (u i : ℝ))

theorem vectorOfCube_injective (n : ℕ) : Injective (vectorOfCube n) := by
  intro u v h
  funext i
  apply Subtype.ext
  exact congrArg (fun x : Vector n ↦ x i) h

theorem vectorOfCube_mem_openCube (n : ℕ) (u : Fin n → I) :
    vectorOfCube n u ∈ openCube n ↔ u ∉ Cube.boundary (Fin n) :=
  (not_mem_cubeBoundary_iff u).symm

def cubeOfVector (n : ℕ) (x : Vector n) (hx : x ∈ openCube n) : Fin n → I :=
  fun i ↦ ⟨x i, ⟨(hx i).1.le, (hx i).2.le⟩⟩

theorem vector_cubeOfVector (n : ℕ) (x : Vector n) (hx : x ∈ openCube n) :
    vectorOfCube n (cubeOfVector n x hx) = x := by
  ext i
  rfl

theorem cubeOfVector_not_boundary (n : ℕ) (x : Vector n) (hx : x ∈ openCube n) :
    cubeOfVector n x hx ∉ Cube.boundary (Fin n) :=
  (not_mem_cubeBoundary_iff _).mpr hx

def interiorHomeomorph (n : ℕ) : CubeInteriorN n ≃ₜ Vector n :=
  (cubeInteriorCoordinates n).trans
    ((Homeomorph.piCongrRight fun _ : Fin n ↦ SmoothInterval.homeomorph).trans
      (PiLp.homeomorph 2 (fun _ : Fin n ↦ ℝ)).symm)

theorem interiorHomeomorph_apply (n : ℕ) (u : CubeInteriorN n) :
    interiorHomeomorph n u = coordinate n (vectorOfCube n u.val) := rfl

def compactification (n : ℕ) : OnePoint (CubeInteriorN n) ≃ₜ Sphere n :=
  (interiorHomeomorph n).onePointCongr.trans (euclideanOnePointSphere n)

theorem compactification_infty (n : ℕ) : compactification n ∞ = spherePole n :=
  euclideanOnePointSphere_infty n

def quotient (n : ℕ) : C(Fin n → I, Sphere n) :=
  (compactification n : C(OnePoint (CubeInteriorN n), Sphere n)).comp
    (collapseMap (Cube.boundary (Fin n)) (isClosed_cubeBoundaryN n))

theorem quotient_boundary (n : ℕ) (u : Fin n → I) (hu : u ∈ Cube.boundary (Fin n)) :
    quotient n u = spherePole n := by
  change compactification n (collapse (Cube.boundary (Fin n)) u) = _
  rw [collapse_of_mem _ hu, compactification_infty]

theorem quotient_eq_pole_iff (n : ℕ) (u : Fin n → I) :
    quotient n u = spherePole n ↔ u ∈ Cube.boundary (Fin n) := by
  rw [← compactification_infty n]
  change compactification n (collapse (Cube.boundary (Fin n)) u) =
    compactification n ∞ ↔ _
  rw [(compactification n).injective.eq_iff, collapse_eq_infty_iff]

theorem quotient_eq_iff (n : ℕ) (u w : Fin n → I) :
    quotient n u = quotient n w ↔
      u = w ∨ u ∈ Cube.boundary (Fin n) ∧ w ∈ Cube.boundary (Fin n) := by
  change compactification n (collapse (Cube.boundary (Fin n)) u) =
    compactification n (collapse (Cube.boundary (Fin n)) w) ↔ _
  rw [(compactification n).injective.eq_iff, collapse_eq_iff]

theorem zero_boundary {n : ℕ} (hn : 0 < n) :
    (0 : Fin n → I) ∈ Cube.boundary (Fin n) := ⟨⟨0, hn⟩, Or.inl rfl⟩

theorem quotient_surjective {n : ℕ} (hn : 0 < n) : Surjective (quotient n) :=
  (compactification n).surjective.comp
    (collapse_surjective (Cube.boundary (Fin n)) ⟨0, zero_boundary hn⟩)

theorem quotient_isQuotientMap {n : ℕ} (hn : 0 < n) : IsQuotientMap (quotient n) :=
  .of_surjective_continuous (quotient_surjective hn) (quotient n).continuous

theorem quotient_interior (n : ℕ) (u : CubeInteriorN n) :
    quotient n u.val = (sphereChart n).symm (vectorOfCube n u.val) := by
  change compactification n (collapse (Cube.boundary (Fin n)) u.val) = _
  rw [collapse_of_not_mem _ u.property]
  change euclideanOnePointSphere n (↑(interiorHomeomorph n u) : OnePoint (Vector n)) = _
  rw [euclideanOnePointSphere_coe, interiorHomeomorph_apply]
  rfl

theorem sphereChart_quotient (n : ℕ) (u : Fin n → I)
    (hu : u ∉ Cube.boundary (Fin n)) : sphereChart n (quotient n u) = vectorOfCube n u := by
  rw [quotient_interior n ⟨u, hu⟩]
  exact (sphereChart n).right_inv ((vectorOfCube_mem_openCube n u).mpr hu)

theorem quotient_cubeOfVector (n : ℕ) (x : Vector n) (hx : x ∈ openCube n) :
    quotient n (cubeOfVector n x hx) = (sphereChart n).symm x := by
  rw [quotient_interior n ⟨_, cubeOfVector_not_boundary n x hx⟩, vector_cubeOfVector]

end NoExoticSixSphere.SmoothCube
