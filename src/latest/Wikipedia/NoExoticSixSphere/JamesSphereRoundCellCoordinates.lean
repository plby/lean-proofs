import Wikipedia.NoExoticSixSphere.NormedDiskBoundaryCoordinates
import Wikipedia.NoExoticSixSphere.JamesSphereCellQuotientCoordinates
import Wikipedia.HomotopyGroupsOfSpheres.SphereCoordinateIsometries
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection

/-!
# Round coordinates for the original second James characteristic disk

The genuine boundary-preserving disk homeomorphism is retained. A proved
reflection moves the standard sphere pole to the preimage of the original
cube corner. The round characteristic quotient therefore uses exactly
the same basepoint as the already constructed James boundary lift.
-/

noncomputable section

open Set Metric
open scoped Topology unitInterval
open Wikipedia.HopfProblem.DegreeCollapse
open Wikipedia.HomotopyGroupsOfSpheres

namespace NoExoticSixSphere.JamesSphere.RoundCell

abbrev sphereDimension (n : ℕ) := 2 * n - 1
abbrev Coordinates (n : ℕ) := EuclideanSpace ℝ (Fin (sphereDimension n + 1))

def linearCoordinates (n : ℕ) (hn : 0 < n) : Coordinates n ≃L[ℝ] CellBoundary.Coordinates n := by
  have he : sphereDimension n + 1 = 2 * n := by unfold sphereDimension; omega
  change EuclideanSpace ℝ (Fin (sphereDimension n + 1)) ≃L[ℝ] (Fin (2 * n) → ℝ)
  rw [he]
  exact EuclideanSpace.equiv (Fin (2 * n)) ℝ

def diskCoordinates (n : ℕ) (hn : 0 < n) :
    DiskCylinder.Disk (E := Coordinates n) ≃ₜ DiskCylinder.Disk (E := CellBoundary.Coordinates n) :=
  NormedDiskBoundaryCoordinates.diskHomeomorph (linearCoordinates n hn)

theorem diskCoordinates_boundary (n : ℕ) (hn : 0 < n)
    (x : DiskCylinder.Disk (E := Coordinates n)) :
    (diskCoordinates n hn x).val ∈ sphere (0 : CellBoundary.Coordinates n) 1 ↔
      x.val ∈ sphere (0 : Coordinates n) 1 :=
  NormedDiskBoundaryCoordinates.diskHomeomorph_boundary (linearCoordinates n hn) x

def boundaryCoordinates (n : ℕ) (hn : 0 < n) :
    Sphere (sphereDimension n) ≃ₜ CellBoundary.Boundary n :=
  NormedDiskBoundaryCoordinates.boundaryHomeomorph
    (diskCoordinates n hn) (diskCoordinates_boundary n hn)

def corner (n : ℕ) (hn : 0 < n) : Sphere (sphereDimension n) :=
  (boundaryCoordinates n hn).symm (CellBoundary.corner n hn)

def parameterHomeomorph (n : ℕ) (hn : 0 < n) :
    Sphere (sphereDimension n) ≃ₜ Sphere (sphereDimension n) :=
  SphereCenteredCoordinates.sphereIsometry
    ((ℝ ∙ ((spherePole (sphereDimension n)).val - (corner n hn).val))ᗮ.reflection)

theorem parameterHomeomorph_pole (n : ℕ) (hn : 0 < n) :
    parameterHomeomorph n hn (spherePole (sphereDimension n)) = corner n hn := by
  apply Subtype.ext
  apply Submodule.reflection_sub
  rw [mem_sphere_zero_iff_norm.mp (spherePole (sphereDimension n)).property,
    mem_sphere_zero_iff_norm.mp (corner n hn).property]

def boundaryHomeomorph (n : ℕ) (hn : 0 < n) :
    Sphere (sphereDimension n) ≃ₜ CellBoundary.Boundary n :=
  (parameterHomeomorph n hn).trans (boundaryCoordinates n hn)

theorem boundaryHomeomorph_pole (n : ℕ) (hn : 0 < n) :
    boundaryHomeomorph n hn (spherePole (sphereDimension n)) = CellBoundary.corner n hn := by
  change boundaryCoordinates n hn
    (parameterHomeomorph n hn (spherePole (sphereDimension n))) = _
  rw [parameterHomeomorph_pole]
  exact (boundaryCoordinates n hn).apply_symm_apply _

theorem disk_boundary_parameter (n : ℕ) (hn : 0 < n) (s : Sphere (sphereDimension n)) :
    diskCoordinates n hn (DiskCylinder.boundaryToDisk (parameterHomeomorph n hn s)) =
      DiskCylinder.boundaryToDisk (boundaryHomeomorph n hn s) := rfl

theorem disk_corner (n : ℕ) (hn : 0 < n) :
    diskCoordinates n hn (DiskCylinder.boundaryToDisk (corner n hn)) =
      CellBoundary.cornerDisk n := by
  have h := NormedDiskBoundaryCoordinates.boundaryHomeomorph_disk
    (diskCoordinates n hn) (diskCoordinates_boundary n hn) (corner n hn)
  change DiskCylinder.boundaryToDisk (boundaryCoordinates n hn (corner n hn)) = _ at h
  have hc : boundaryCoordinates n hn (corner n hn) = CellBoundary.corner n hn :=
    (boundaryCoordinates n hn).apply_symm_apply _
  rw [hc, CellBoundary.boundary_corner] at h
  exact h.symm

def maxQuotient (n : ℕ) : C(DiskCylinder.Disk (E := CellBoundary.Coordinates n), Sphere (n + n)) :=
  (SecondStage.collapse n).comp (Cell.closedPresentation n 2)

theorem maxQuotient_base (n : ℕ) (x : DiskCylinder.Disk (E := CellBoundary.Coordinates n)) :
    maxQuotient n x = spherePole (n + n) ↔ x.val ∈ sphere (0 : CellBoundary.Coordinates n) 1 := by
  rw [maxQuotient, ContinuousMap.comp_apply, SecondStage.collapse_eq_pole_iff]
  exact PuncturedStage.boundary_iff n 1 x

theorem maxQuotient_fiber (n : ℕ)
    (x y : DiskCylinder.Disk (E := CellBoundary.Coordinates n))
    (he : maxQuotient n x = maxQuotient n y) :
    maxQuotient n x = spherePole (n + n) ∨ x = y := by
  rcases SecondStage.collapse_fiber_condition n
      (Cell.closedPresentation n 2 x) (Cell.closedPresentation n 2 y) he with hx | hxy
  · exact Or.inl ((SecondStage.collapse_eq_pole_iff n _).mpr hx)
  · rcases PuncturedStage.fiber_condition n 1 x y hxy with hx | hxy
    · exact Or.inl ((SecondStage.collapse_eq_pole_iff n _).mpr hx)
    · exact Or.inr hxy

theorem maxQuotient_surjective (n : ℕ) (hn : 0 < n) : Function.Surjective (maxQuotient n) :=
  (SecondStage.collapse_surjective n).comp (Cell.closedPresentation_surjective n 2 hn)

def quotient (n : ℕ) (hn : 0 < n) : C(DiskCylinder.Disk (E := Coordinates n), Sphere (n + n)) :=
  (maxQuotient n).comp (diskCoordinates n hn : C(_, _))

theorem quotient_base (n : ℕ) (hn : 0 < n) (x : DiskCylinder.Disk (E := Coordinates n)) :
    quotient n hn x = spherePole (n + n) ↔ x.val ∈ sphere (0 : Coordinates n) 1 :=
  (maxQuotient_base n (diskCoordinates n hn x)).trans (diskCoordinates_boundary n hn x)

theorem quotient_fiber (n : ℕ) (hn : 0 < n) (x y : DiskCylinder.Disk (E := Coordinates n))
    (he : quotient n hn x = quotient n hn y) :
    quotient n hn x = spherePole (n + n) ∨ x = y := by
  rcases maxQuotient_fiber n (diskCoordinates n hn x) (diskCoordinates n hn y) he with hx | hxy
  · exact Or.inl hx
  · exact Or.inr ((diskCoordinates n hn).injective hxy)

theorem quotient_surjective (n : ℕ) (hn : 0 < n) : Function.Surjective (quotient n hn) :=
  (maxQuotient_surjective n hn).comp (diskCoordinates n hn).surjective

end NoExoticSixSphere.JamesSphere.RoundCell
