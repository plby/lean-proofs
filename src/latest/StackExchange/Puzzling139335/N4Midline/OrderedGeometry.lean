import StackExchange.Puzzling139335.ThreeCorners
import StackExchange.Puzzling139335.N4Midline.Contacts
import StackExchange.Puzzling139335.N4Midline.FrameCoordinates
import StackExchange.Puzzling139335.N4Midline.BottomCoverage
import StackExchange.Puzzling139335.N4Midline.Endpoint

/-!
# The geometric endpoint forced by an ordered midline configuration

All support-coordinate bounds here are derived from actual congruences
placing the whole piece in the square. Finite bottom contacts and actual
coverage then force the middle intrinsic corner to be the bottom midpoint.
-/

open Set

namespace Puzzling139335.N4Midline

open ThreeCorners

noncomputable section

theorem frameCenter_maps_to_squareCenter {P : Set Plane} {v : Plane} {θ : ℝ}
    (hfull : UnitPairs.IsFullSquareCorner P v) (h : SupportCorner P v)
    (hθ : h.bisector = outwardBisector θ)
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (j : Fin 4)
    (hsub : e '' P ⊆ unitSquare) (hv : e v = corner j) :
    e (frameCenter v θ) = squareCenter := by
  have hsymm := symm_center_eq_of_bisector hfull h hθ e j hsub hv
  change e (v + (1 / 2 : ℝ) • (ray θ + perpRay θ)) = squareCenter
  rw [← hsymm, e.apply_symm_apply]

theorem frameCenter_mem_interior_of_image {P Q : Set Plane} {v : Plane} {θ : ℝ}
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (he : e '' P = Q)
    (hc : e (frameCenter v θ) = squareCenter)
    (hcenter : squareCenter ∈ interior Q) : frameCenter v θ ∈ interior P := by
  apply (mem_interior_image_affineIsometry e).mp
  rw [he, hc]
  exact hcenter

/-- The middle ordered corner cannot place the center inside a copy of
a piece that is confined to the left half-square. -/
theorem middle_placement_center_not_interior {P Q : Set Plane} {v : Plane} {θ : ℝ}
    (hP : P ⊆ leftHalfSquare) (hvP : v ∈ P)
    (hθ : θ ∈ Icc (Real.pi / 2) Real.pi)
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (he : e '' P = Q)
    (hc : e (frameCenter v θ) = squareCenter) : squareCenter ∉ interior Q := by
  intro hcenter
  exact frameCenter_not_mem_interior_left hP (hP hvP) hθ
    (frameCenter_mem_interior_of_image e he hc hcenter)

/-- Geometry alone forces the endpoint configuration under the assumption
that the last ordered upper placement contains the center. -/
theorem ordered_midpoint_forced (d : SquareDissection)
    (hmirror : midlineReflection '' d.piece 0 = d.piece 1)
    (hzero : (0 : Plane) ∈ d.piece 0) (hleft : d.piece 0 ⊆ leftHalfSquare)
    (b c : Fin 4) (hindices : (b = 2 ∧ c = 3) ∨ (b = 3 ∧ c = 2))
    (B C : Plane) (θ φ : ℝ)
    (eB eC : Plane ≃ᵃⁱ[ℝ] Plane)
    (himageB : eB '' d.piece 0 = d.piece b)
    (himageC : eC '' d.piece 0 = d.piece c)
    (hcornerB : eB B = corner b) (hcornerC : eC C = corner c)
    (hfullB : UnitPairs.IsFullSquareCorner (d.piece 0) B)
    (hfullC : UnitPairs.IsFullSquareCorner (d.piece 0) C)
    (hB : SupportCorner (d.piece 0) B) (hC : SupportCorner (d.piece 0) C)
    (hbisectorB : hB.bisector = outwardBisector θ)
    (hbisectorC : hC.bisector = outwardBisector φ)
    (hconeB : d.piece 0 ⊆ supportCone B θ)
    (hconeC : d.piece 0 ⊆ supportCone C φ)
    (hθ : θ ∈ Icc (Real.pi / 2) Real.pi)
    (hφ : φ ∈ Icc (θ + Real.pi / 2) (3 * Real.pi / 2))
    (hc : squareCenter ∈ interior (d.piece c)) :
    θ = Real.pi / 2 ∧ B = bottomMidpoint := by
  have hsubB : eB '' d.piece 0 ⊆ unitSquare := by
    rw [himageB]
    exact d.piece_subset b
  have hsubC : eC '' d.piece 0 ⊆ unitSquare := by
    rw [himageC]
    exact d.piece_subset c
  have hcenterB := frameCenter_maps_to_squareCenter hfullB hB hbisectorB
    eB b hsubB hcornerB
  have hcenterC := frameCenter_maps_to_squareCenter hfullC hC hbisectorC
    eC c hsubC hcornerC
  have hcenterSource := frameCenter_mem_interior_of_image eC himageC hcenterC hc
  have hBbounds (p : Plane) (hp : p ∈ d.piece 0) :
      inner ℝ (ray θ) (p - B) ≤ 1 ∧ inner ℝ (perpRay θ) (p - B) ≤ 1 := by
    have h := inward_coordinates_mem_Icc eB B θ b hcornerB hcenterB
      (hsubB (mem_image_of_mem eB hp))
    exact ⟨h.1.2, h.2.2⟩
  have hCbounds (p : Plane) (hp : p ∈ d.piece 0) :
      inner ℝ (ray φ) (p - C) ≤ 1 ∧ inner ℝ (perpRay φ) (p - C) ≤ 1 := by
    have h := inward_coordinates_mem_Icc eC C φ c hcornerC hcenterC
      (hsubC (mem_image_of_mem eC hp))
    exact ⟨h.1.2, h.2.2⟩
  obtain ⟨hBr, hBp, hCr, hCp⟩ := four_contacts_subsingleton hleft hzero hB.mem hC.mem
    hconeB hconeC hθ hφ.1 hφ.2 hBbounds hCbounds hcenterSource
  have hbtop : b = 2 ∨ b = 3 := hindices.elim
    (fun h => Or.inl h.1) (fun h => Or.inr h.1)
  have hctop : c = 2 ∨ c = 3 := hindices.elim
    (fun h => Or.inr h.2) (fun h => Or.inl h.2)
  have hfiniteB : (d.piece b ∩ {p : Plane | p 1 = 0}).Finite := by
    rw [← himageB]
    exact bottom_contact_finite_of_coordinate_faces eB B θ b hbtop hcornerB hcenterB
      hBr.finite hBp.finite
  have hfiniteC : (d.piece c ∩ {p : Plane | p 1 = 0}).Finite := by
    rw [← himageC]
    exact bottom_contact_finite_of_coordinate_faces eC C φ c hctop hcornerC hcenterC
      hCr.finite hCp.finite
  have hright : d.piece 1 ⊆ {p : Plane | (1 / 2 : ℝ) ≤ p 0} := by
    rw [← hmirror]
    exact reflected_image_subset_right hleft
  have henum (m : Fin 4) : m = 0 ∨ m = 1 ∨ m = b ∨ m = c := by
    rcases hindices with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> fin_cases m <;> simp
  have hbottom := d.bottom_left_subset_piece_of_finite_contacts
    0 1 b c henum hright hfiniteB hfiniteC
  have hM : bottomMidpoint ∈ d.piece 0 :=
    hbottom (by norm_num [bottomMidpoint])
  obtain ⟨_, hθstrict, _⟩ := ordered_angles_of_frameCenter_mem_interior hleft hC.mem
    hθ hφ.1 hφ.2 hcenterSource
  exact endpoint_of_bottomMidpoint_mem hleft hB.mem ⟨hθ.1, hθstrict⟩ hconeB hM
    (exists_ball_inter_supportCone_subset hfullB hB hbisectorB)

end

end Puzzling139335.N4Midline
