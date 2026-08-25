import StackExchange.Puzzling139335.SquareGeometry
import Mathlib.Data.Fintype.EquivFin

/-!
# The corner permutation of a square isometry

An isometry taking the square into itself takes each diameter pair to a
diameter pair. Equality in the coordinate diameter bounds forces both
coordinates of each endpoint to be either zero or one. Thus the four
corners map injectively into themselves and hence are permuted.
-/

open Set

namespace Puzzling139335.SquareSymmetry

noncomputable section

/-- A point with both coordinates at interval endpoints is a square corner. -/
theorem exists_corner_of_endpoint_coordinates {p : Plane}
    (h₀ : p 0 = 0 ∨ p 0 = 1) (h₁ : p 1 = 0 ∨ p 1 = 1) :
    ∃ a : Fin 4, p = corner a := by
  rcases h₀ with h₀ | h₀ <;> rcases h₁ with h₁ | h₁
  · refine ⟨0, ?_⟩
    ext i
    fin_cases i <;> simp [corner, Fin.ext_iff, h₀, h₁]
  · refine ⟨3, ?_⟩
    ext i
    fin_cases i <;> simp [corner, Fin.ext_iff, h₀, h₁]
  · refine ⟨1, ?_⟩
    ext i
    fin_cases i <;> simp [corner, Fin.ext_iff, h₀, h₁]
  · refine ⟨2, ?_⟩
    ext i
    fin_cases i <;> simp [corner, Fin.ext_iff, h₀, h₁]

/-- Inclusion of the isometric square image already forces each corner
to map to a corner. -/
theorem maps_corner_of_maps_square_into_square
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (he : e '' unitSquare ⊆ unitSquare) (a : Fin 4) :
    ∃ b : Fin 4, e (corner a) = corner b := by
  have hp : e (corner a) ∈ unitSquare :=
    he (mem_image_of_mem e (corner_mem_unitSquare a))
  have hq : e (corner (a + 2)) ∈ unitSquare :=
    he (mem_image_of_mem e (corner_mem_unitSquare (a + 2)))
  have hdiam : dist (e (corner a)) (e (corner (a + 2))) ^ 2 = 2 := by
    rw [e.isometry.dist_eq]
    exact corner_opposite_dist_sq a
  obtain ⟨h₀, h₁⟩ := coord_sub_sq_eq_one_of_dist_sq_eq_two hp hq hdiam
  have hend₀ := endpoints_of_mem_Icc_of_sub_sq_eq_one hp.1 hq.1 h₀
  have hend₁ := endpoints_of_mem_Icc_of_sub_sq_eq_one hp.2 hq.2 h₁
  apply exists_corner_of_endpoint_coordinates
  · exact hend₀.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)
  · exact hend₁.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)

/-- The induced corner map is a permutation, even when only inclusion
of the square image was assumed. -/
theorem exists_corner_permutation_of_maps_square_into_square
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (he : e '' unitSquare ⊆ unitSquare) :
    ∃ σ : Equiv.Perm (Fin 4), ∀ a, e (corner a) = corner (σ a) := by
  classical
  choose f hf using maps_corner_of_maps_square_into_square e he
  have hinj : Function.Injective f := by
    intro a b hab
    apply corner_injective
    apply e.injective
    rw [hf a, hf b, hab]
  exact ⟨Equiv.ofBijective f hinj.bijective_of_finite, hf⟩

/-- The corner permutation induced by an affine isometry whose square
image is contained in the square. -/
def cornerPermutation (e : Plane ≃ᵃⁱ[ℝ] Plane)
    (he : e '' unitSquare ⊆ unitSquare) : Equiv.Perm (Fin 4) :=
  Classical.choose (exists_corner_permutation_of_maps_square_into_square e he)

/-- Applying the induced permutation agrees with applying the isometry
to the corresponding square corner. -/
theorem cornerPermutation_apply (e : Plane ≃ᵃⁱ[ℝ] Plane)
    (he : e '' unitSquare ⊆ unitSquare) (a : Fin 4) :
    e (corner a) = corner (cornerPermutation e he a) :=
  Classical.choose_spec (exists_corner_permutation_of_maps_square_into_square e he) a

/-- The set of all four square corners is preserved. -/
theorem image_corners_of_maps_square_into_square
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (he : e '' unitSquare ⊆ unitSquare) :
    e '' range corner = range corner := by
  obtain ⟨σ, hσ⟩ := exists_corner_permutation_of_maps_square_into_square e he
  apply Subset.antisymm
  · rintro _ ⟨_, ⟨a, rfl⟩, rfl⟩
    exact ⟨σ a, (hσ a).symm⟩
  · rintro _ ⟨b, rfl⟩
    refine ⟨corner (σ.symm b), ⟨σ.symm b, rfl⟩, ?_⟩
    simpa only [σ.apply_symm_apply] using hσ (σ.symm b)

/-- Equality formulation of the corner-permutation theorem. -/
theorem exists_corner_permutation_of_preserves_square
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (he : e '' unitSquare = unitSquare) :
    ∃ σ : Equiv.Perm (Fin 4), ∀ a, e (corner a) = corner (σ a) :=
  exists_corner_permutation_of_maps_square_into_square e he.subset

theorem image_corners_of_preserves_square
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (he : e '' unitSquare = unitSquare) :
    e '' range corner = range corner :=
  image_corners_of_maps_square_into_square e he.subset

end

end Puzzling139335.SquareSymmetry
