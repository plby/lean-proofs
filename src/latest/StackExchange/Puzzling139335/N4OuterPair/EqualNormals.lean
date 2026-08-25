import StackExchange.Puzzling139335.N4OuterPair.EqualNormals.ActualPlacement
import StackExchange.Puzzling139335.N4OuterPair.EqualNormals.AxialForms
import StackExchange.Puzzling139335.N4Axial.Dihedral

/-!
# The opposite-side owners cannot use equal intrinsic source normals

Actual source-face memberships identify the support levels and hence the
relative axial congruence.  Compactness handles the proper form.  The
reversed form either fixes the center immediately or has a nonzero
translation square; weighted-density cancellation then gives an actual
horizontal-reflection pair.  No symmetry of the partition is assumed.
-/

open Set

namespace Puzzling139335.N4OuterPair.Configuration

open SourceFaceBridge EqualNormals EqualNormals.AxialForms

variable {d : SquareDissection}

private theorem false_of_middle_owner_pair_fixed
    (h : Configuration d) (hc : d.HasProtectedCenter)
    {iR iL : Fin 4} (howners : (iR = 2 ∧ iL = 3) ∨ (iR = 3 ∧ iL = 2))
    (g : Plane ≃ᵃⁱ[ℝ] Plane) (himage : g '' d.piece iR = d.piece iL)
    (hfixed : g squareCenter = squareCenter) : False := by
  have hij : iR ≠ iL := by
    rcases howners with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  have hnot := d.center_not_mem_fixed_pair hij g himage hfixed
  rcases howners with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact (h.center_in_middle hc).elim hnot.1 hnot.2
  · exact (h.center_in_middle hc).elim hnot.2 hnot.1

private theorem middle_owner_union_reflected
    (h : Configuration d) {iR iL : Fin 4}
    (howners : (iR = 2 ∧ iL = 3) ∨ (iR = 3 ∧ iL = 2)) :
    ReflectionSeparation.horizontal '' (d.piece iR ∪ d.piece iL) =
      d.piece iR ∪ d.piece iL := by
  rcases howners with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact h.middle_union_reflected
  · simpa only [union_comm] using h.middle_union_reflected

/-- Equal opposite-side normals in proper parity force the actual relative
half-turn to fix the square center.  The common normalization reflection
and both orders of the middle labels are included. -/
theorem false_of_proper_equal_source_normals
    (h : Configuration d) (hc : d.HasProtectedCenter)
    {iR iL : Fin 4} (howners : (iR = 2 ∧ iL = 3) ∨ (iR = 3 ∧ iL = 2))
    (u : UpperFaceData) (σ : Bool)
    (hsource : UpperSupportedSource u false (d.piece 0))
    (heq : u.φ = u.ψ)
    (hR : u.right '' d.piece 0 = postReflect σ '' d.piece iR)
    (hL : u.left false '' d.piece 0 = postReflect σ '' d.piece iL) : False := by
  let g := actualRelative u false σ
  have himage : g '' d.piece iR = d.piece iL :=
    actualRelative_image u false σ hR hL
  obtain ⟨δ, hcoords⟩ := actualRelative_proper_coordinates hsource heq σ
  have hcompact : IsCompact (d.piece iR ∪ d.piece iL) :=
    (d.jordan iR).isCompact.union (d.jordan iL).isCompact
  have hne : (d.piece iR ∪ d.piece iL).Nonempty := by
    obtain ⟨p, hp⟩ := (d.jordan iR).interior_nonempty
    exact ⟨p, Or.inl (interior_subset hp)⟩
  have hfixed : g squareCenter = squareCenter :=
    direct_center_fixed g δ hcoords hcompact hne himage
      (middle_owner_union_reflected h howners)
  exact false_of_middle_owner_pair_fixed h hc howners g himage hfixed

private theorem false_of_reversed_middle_owner_coordinates
    (h : Configuration d) (hc : d.HasProtectedCenter)
    {iR iL : Fin 4} (howners : (iR = 2 ∧ iL = 3) ∨ (iR = 3 ∧ iL = 2))
    (g : Plane ≃ᵃⁱ[ℝ] Plane) (δ : ℝ)
    (hcoords : ∀ p, g p 0 = 1 - p 0 ∧ g p 1 = p 1 + δ)
    (himage : g '' d.piece iR = d.piece iL) : False := by
  by_cases hδ : δ = 0
  · exact false_of_middle_owner_pair_fixed h hc howners g himage
      (reversed_center_fixed_of_zero g δ hcoords hδ)
  rcases howners with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact h.false_of_middle_dihedral_translation_square hc g !₂[0, 2 * δ]
      (vertical_double_ne_zero δ hδ) (reversed_square g δ hcoords)
      (horizontal_conjugates_reversed g δ hcoords) himage
  · have hback : g.symm '' d.piece 2 = d.piece 3 := by
      rw [← himage, image_image]
      simp only [g.symm_apply_apply, image_id']
    have hinv := reversed_inverse_coordinates_neg g δ hcoords
    exact h.false_of_middle_dihedral_translation_square hc g.symm !₂[0, 2 * (-δ)]
      (vertical_double_ne_zero (-δ) (neg_ne_zero.mpr hδ))
      (reversed_square g.symm (-δ) hinv)
      (horizontal_conjugates_reversed g.symm (-δ) hinv) hback

/-- Equal opposite-side normals in reversed parity give a vertical reflection
or glide.  The nonzero glide is excluded using the actual dissection's
weighted densities, without a finite-contact or Jordan-union premise. -/
theorem false_of_glide_equal_source_normals
    (h : Configuration d) (hc : d.HasProtectedCenter)
    {iR iL : Fin 4} (howners : (iR = 2 ∧ iL = 3) ∨ (iR = 3 ∧ iL = 2))
    (u : UpperFaceData) (σ : Bool)
    (hsource : UpperSupportedSource u true (d.piece 0))
    (heq : u.φ = u.ψ)
    (hR : u.right '' d.piece 0 = postReflect σ '' d.piece iR)
    (hL : u.left true '' d.piece 0 = postReflect σ '' d.piece iL) : False := by
  obtain ⟨δ, hcoords⟩ := actualRelative_glide_coordinates hsource heq σ
  exact false_of_reversed_middle_owner_coordinates h hc howners
    (actualRelative u true σ) δ hcoords (actualRelative_image u true σ hR hL)

/-- The source extraction interface with both placement parities and either
middle-owner order.  Equal normals cannot occur in a protected-center
configuration. -/
theorem false_of_equal_source_normals
    (h : Configuration d) (hc : d.HasProtectedCenter)
    {iR iL : Fin 4} (howners : (iR = 2 ∧ iL = 3) ∨ (iR = 3 ∧ iL = 2))
    (u : UpperFaceData) (reversed σ : Bool)
    (hsource : UpperSupportedSource u reversed (d.piece 0))
    (heq : u.φ = u.ψ)
    (hR : u.right '' d.piece 0 = postReflect σ '' d.piece iR)
    (hL : u.left reversed '' d.piece 0 = postReflect σ '' d.piece iL) : False := by
  cases reversed
  · exact h.false_of_proper_equal_source_normals hc howners u σ hsource heq hR hL
  · exact h.false_of_glide_equal_source_normals hc howners u σ hsource heq hR hL

/-- A convenient non-equality form for the subsequent unequal-normal
source-face obstruction. -/
theorem source_normals_ne
    (h : Configuration d) (hc : d.HasProtectedCenter)
    {iR iL : Fin 4} (howners : (iR = 2 ∧ iL = 3) ∨ (iR = 3 ∧ iL = 2))
    (u : UpperFaceData) (reversed σ : Bool)
    (hsource : UpperSupportedSource u reversed (d.piece 0))
    (hR : u.right '' d.piece 0 = postReflect σ '' d.piece iR)
    (hL : u.left reversed '' d.piece 0 = postReflect σ '' d.piece iL) : u.φ ≠ u.ψ :=
  fun heq => h.false_of_equal_source_normals hc howners u reversed σ hsource heq hR hL

end Puzzling139335.N4OuterPair.Configuration
