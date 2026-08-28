import Wikipedia.NoExoticSixSphere.JamesSphereAttachingBoundaryCoordinates
import Wikipedia.NoExoticSixSphere.ClockCornerCofibration
import Wikipedia.NoExoticSixSphere.CubeBoundaryCofibration
import Wikipedia.NoExoticSixSphere.RestrictedSubspaceCofibration

/-!
# Homotopy extension for the faces collapsed in the source comparison

The discarded set is the union of the tail-boundary faces and the
zero-clock face. Product neighborhood data restricts to the actual full
attaching boundary because the corner motion preserves its perimeter.
Thus the literal discarded subspace is a closed cofibration. Its chosen
point is the original characteristic corner, not a changed basepoint.
-/

noncomputable section

open Set
open scoped Topology unitInterval
open Wikipedia.HopfProblem.OrbitPair

namespace NoExoticSixSphere.JamesSphere.AttachingSquare

def tailCoordinates (n : ℕ) : Parameter n ≃ₜ (Fin (2 * n) → I) where
  toFun := JamesCellCube.pack n 2
  invFun := JamesCellCube.block n 2
  left_inv v := funext (JamesCellCube.block_pack n 2 v)
  right_inv := JamesCellCube.pack_block n 2
  continuous_toFun := continuous_pi (fun _ ↦ (continuous_apply _).comp (continuous_apply _))
  continuous_invFun := continuous_pi (fun _ ↦ continuous_pi (fun _ ↦ continuous_apply _))

def tailBoundary (n : ℕ) : Set (Parameter n) := {v | ∃ i, v i ∈ Cube.boundary (Fin n)}

theorem tailCoordinates_boundary (n : ℕ) (v : Parameter n) :
    v ∈ tailBoundary n ↔ tailCoordinates n v ∈ Cube.boundary (Fin (2 * n)) := by
  classical
  have h := JamesCellCube.block_not_boundary_iff n 2 (JamesCellCube.pack n 2 v)
  simp only [JamesCellCube.block_pack] at h
  change (∃ i, v i ∈ Cube.boundary (Fin n)) ↔
    JamesCellCube.pack n 2 v ∈ Cube.boundary (Fin (2 * n))
  simpa only [not_forall, not_not] using not_congr h

def tailData (n : ℕ) : NeighborhoodDeformation.Data
    (SubspaceCofibration.inclusion (tailBoundary n)) :=
  SubspaceCofibration.transport (tailCoordinates n).symm
    (fun u ↦ by simpa only [Homeomorph.apply_symm_apply] using
      (tailCoordinates_boundary n ((tailCoordinates n).symm u)).symm)
    (CubeBoundaryCofibration.data (2 * n))

def deletedAmbient (n : ℕ) : Set ((Fin 2 → I) × Parameter n) :=
  {p | p.1 = 0 ∨ p.2 ∈ tailBoundary n}

theorem deleted_subset_full (n : ℕ) : deletedAmbient n ⊆ fullBoundary n := by
  intro p hp
  rcases hp with hp | hp
  · exact Or.inl ⟨0, Or.inl (congrFun hp 0)⟩
  · exact Or.inr hp

def deletedAmbientData (n : ℕ) : NeighborhoodDeformation.Data
    (SubspaceCofibration.inclusion (deletedAmbient n)) :=
  SubspaceCofibration.transport (Homeomorph.refl _) (fun p ↦ by
    change (p.1 ∈ Set.range (SubspaceCofibration.inclusion ({0} : Set ClockCorner.Square)) ∨
      p.2 ∈ Set.range (SubspaceCofibration.inclusion (tailBoundary n))) ↔ _
    rw [SubspaceCofibration.mem_range, SubspaceCofibration.mem_range]
    rfl) (NeighborhoodProduct.data ClockCorner.data (tailData n))

theorem deletedAmbientData_preserves (n : ℕ) (s : I)
    (p : (Fin 2 → I) × Parameter n) (hp : p ∈ fullBoundary n) :
    (deletedAmbientData n).deformation (s, p) ∈ fullBoundary n := by
  rcases hp with hp | hp
  · left
    change ClockCorner.motion
      (NeighborhoodProduct.leftTime ClockCorner.data (tailData n) (s, p), p.1) ∈ _
    exact ClockCorner.motion_boundary _ p.1 hp
  · change NeighborhoodProduct.deformation ClockCorner.data (tailData n) (s, p) ∈ _
    have hz : (tailData n).height p.2 = 0 :=
      ((tailData n).zero_iff p.2).mpr ((SubspaceCofibration.mem_range _ _).mpr hp)
    rw [NeighborhoodProduct.deformation_fixed_right ClockCorner.data (tailData n) s p.1 p.2 hz]
    exact Or.inr hp

def collapsedFaces (n : ℕ) : Set (fullBoundary n) := {p | p.val ∈ deletedAmbient n}

def collapsedFacesData (n : ℕ) : NeighborhoodDeformation.Data
    (SubspaceCofibration.inclusion (collapsedFaces n)) :=
  SubspaceCofibration.restrictedData (deletedAmbient n) (fullBoundary n)
    (deletedAmbientData n) (deletedAmbientData_preserves n)

theorem collapsedFaces_hasHomotopyExtension (n : ℕ) :
    HomotopyExtension.HasHomotopyExtension (SubspaceCofibration.inclusion (collapsedFaces n)) :=
  SubspaceCofibration.hasHomotopyExtension (collapsedFacesData n)

theorem isClosed_collapsedFaces (n : ℕ) : IsClosed (collapsedFaces n) := by
  have h := NeighborhoodDeformation.range_isClosed (collapsedFacesData n)
  have he : Set.range (SubspaceCofibration.inclusion (collapsedFaces n)) = collapsedFaces n := by
    ext p
    exact SubspaceCofibration.mem_range _ p
  rwa [he] at h

def fullPoint (n : ℕ) : fullBoundary n := ⟨(0, 0), Or.inl ⟨0, Or.inl rfl⟩⟩

def collapsedPoint (n : ℕ) : collapsedFaces n := ⟨fullPoint n, Or.inl rfl⟩

theorem packedCube_zero (n : ℕ) : packedCube n (0, 0) = 0 := by
  funext l
  change Fin.cons (α := fun _ : Fin (n + 1) ↦ I) 0 (fun _ ↦ 0)
    (finProdFinEquiv.symm l).2 = 0
  generalize (finProdFinEquiv.symm l).2 = j
  cases j using Fin.cases with
  | zero => rfl
  | succ j => rfl

theorem fullBoundaryHomeomorph_point (n : ℕ) :
    fullBoundaryHomeomorph n (fullPoint n) = CellBoundary.corner (n + 1) (Nat.succ_pos n) := by
  apply Subtype.ext
  change JamesCellCube.unscale _ (packedCube n (0, 0)) = JamesCellCube.unscale _ 0
  rw [packedCube_zero]

theorem fullAttaching_point (n : ℕ) : fullAttaching n (fullPoint n) = spherePole (n + 1) := by
  change CellBoundary.attaching (n + 1) (fullBoundaryHomeomorph n (fullPoint n)) = _
  rw [fullBoundaryHomeomorph_point, CellBoundary.attaching_corner]

end NoExoticSixSphere.JamesSphere.AttachingSquare
