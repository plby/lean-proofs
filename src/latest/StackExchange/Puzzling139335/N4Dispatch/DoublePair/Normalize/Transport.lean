import StackExchange.Puzzling139335.Transform
import StackExchange.Puzzling139335.SquareSymmetry.CornerPermutation

/-!
# Transport used in the two-double-corner normalization

Only actual physical memberships and actual congruences are transported.
No assertion about a new choice of intrinsic placements is needed.
-/

open Set

namespace Puzzling139335.N4Dispatch.DoublePair.Normalize

noncomputable section

/-- Express an actual plane congruence after a common change of coordinates. -/
def conjugate (f e : Plane ≃ᵃⁱ[ℝ] Plane) : Plane ≃ᵃⁱ[ℝ] Plane :=
  (f.symm.trans e).trans f

@[simp] theorem conjugate_apply (f e : Plane ≃ᵃⁱ[ℝ] Plane) (p : Plane) :
    conjugate f e p = f (e (f.symm p)) := rfl

theorem conjugate_image_image (f e : Plane ≃ᵃⁱ[ℝ] Plane) (P : Set Plane) :
    conjugate f e '' (f '' P) = f '' (e '' P) := by
  simp only [Set.image_image]
  congr 1
  funext p
  simp

theorem conjugate_preserves_square (f e : Plane ≃ᵃⁱ[ℝ] Plane)
    (hf : f '' unitSquare = unitSquare) (he : e '' unitSquare = unitSquare) :
    conjugate f e '' unitSquare = unitSquare := by
  calc
    conjugate f e '' unitSquare = conjugate f e '' (f '' unitSquare) := by rw [hf]
    _ = f '' (e '' unitSquare) := conjugate_image_image f e unitSquare
    _ = unitSquare := by rw [he, hf]

theorem conjugate_image_piece (d : SquareDissection) (f e : Plane ≃ᵃⁱ[ℝ] Plane)
    (hf : f '' unitSquare = unitSquare) {i j : Fin 4}
    (he : e '' d.piece i = d.piece j) :
    conjugate f e '' (d.map f hf).piece i = (d.map f hf).piece j := by
  change conjugate f e '' (f '' d.piece i) = f '' d.piece j
  rw [conjugate_image_image, he]

theorem corner_mem_map_iff (d : SquareDissection) (f : Plane ≃ᵃⁱ[ℝ] Plane)
    (hf : f '' unitSquare = unitSquare) {a b : Fin 4}
    (hab : f (corner a) = corner b) (i : Fin 4) :
    corner b ∈ (d.map f hf).piece i ↔ corner a ∈ d.piece i := by
  change corner b ∈ f '' d.piece i ↔ corner a ∈ d.piece i
  rw [← hab]
  exact f.injective.mem_set_image

theorem unique_corner_owners_map (d : SquareDissection) (f : Plane ≃ᵃⁱ[ℝ] Plane)
    (hf : f '' unitSquare = unitSquare)
    (hu : ∀ (i j a : Fin 4), corner a ∈ d.piece i → corner a ∈ d.piece j → i = j) :
    ∀ (i j a : Fin 4), corner a ∈ (d.map f hf).piece i →
      corner a ∈ (d.map f hf).piece j → i = j := by
  obtain ⟨σ, hσ⟩ := SquareSymmetry.exists_corner_permutation_of_preserves_square f hf
  intro i j a hi hj
  have ha : f (corner (σ.symm a)) = corner a := by simpa using hσ (σ.symm a)
  exact hu i j (σ.symm a) ((corner_mem_map_iff d f hf ha i).mp hi)
    ((corner_mem_map_iff d f hf ha j).mp hj)

theorem map_commutes_center_reflection (f : Plane ≃ᵃⁱ[ℝ] Plane)
    (hf : f '' unitSquare = unitSquare) (p : Plane) :
    f (AffineIsometryEquiv.pointReflection ℝ squareCenter p) =
      AffineIsometryEquiv.pointReflection ℝ squareCenter (f p) := by
  have hfix := SquareSymmetry.center_fixed_of_preserves_square f hf
  rw [AffineIsometryEquiv.pointReflection_apply, f.map_vadd, f.map_vsub,
    hfix, AffineIsometryEquiv.pointReflection_apply]

theorem center_reflection_image_map (f : Plane ≃ᵃⁱ[ℝ] Plane)
    (hf : f '' unitSquare = unitSquare) (P : Set Plane) :
    AffineIsometryEquiv.pointReflection ℝ squareCenter '' (f '' P) =
      f '' (AffineIsometryEquiv.pointReflection ℝ squareCenter '' P) := by
  simp only [Set.image_image]
  congr 1
  funext p
  exact (map_commutes_center_reflection f hf p).symm

theorem no_center_reflection_pair_map (d : SquareDissection) (f : Plane ≃ᵃⁱ[ℝ] Plane)
    (hf : f '' unitSquare = unitSquare) {i j : Fin 4}
    (hno : AffineIsometryEquiv.pointReflection ℝ squareCenter '' d.piece i ≠ d.piece j) :
    AffineIsometryEquiv.pointReflection ℝ squareCenter '' (d.map f hf).piece i ≠
      (d.map f hf).piece j := by
  intro h
  apply hno
  apply f.injective.image_injective
  change AffineIsometryEquiv.pointReflection ℝ squareCenter '' (f '' d.piece i) =
    f '' d.piece j at h
  rwa [center_reflection_image_map f hf] at h

end

end Puzzling139335.N4Dispatch.DoublePair.Normalize
