import StackExchange.Puzzling139335.PackingMass
import StackExchange.Puzzling139335.SquareSymmetry.Basic
import StackExchange.Puzzling139335.JordanTransport

/-!
# Saturation by copies fixing the square center

Four interior-disjoint copies of an original piece fill the square. If
their placement maps fix the center, a protected center must already be
interior to the original piece. A second original piece related by a
center-fixing congruence rules this out.
-/

open Set

namespace Puzzling139335.SquareDissection

/-- A four-copy packing whose placement maps fix the square center forces
the prototype to own a protected center whenever the original dissection
has one. No symmetry of the original tiling is assumed. -/
theorem center_mem_interior_of_fixed_piece_packing (d : SquareDissection)
    (i : Fin 4) (g : Fin 4 → Plane ≃ᵃⁱ[ℝ] Plane)
    (hfix : ∀ n, g n squareCenter = squareCenter)
    (hsub : ∀ n, g n '' d.piece i ⊆ unitSquare)
    (hdis : Pairwise fun n m =>
      Disjoint (interior (g n '' d.piece i)) (interior (g m '' d.piece i)))
    (hc : d.HasProtectedCenter) : squareCenter ∈ interior (d.piece i) := by
  let P : Fin 4 → Set Plane := fun n => g n '' d.piece i
  have hP (n : Fin 4) : IsJordanRegion (P n) :=
    (d.jordan i).image_homeomorph (g n).toHomeomorph
  have hcongr (n : Fin 4) : Congruent (P n) (d.piece i) :=
    Congruent.symm ⟨g n, rfl⟩
  have hcover := d.congruent_piece_packing_covers i P hP hdis hsub hcongr
  by_contra hnoti
  obtain ⟨k, hk⟩ := hc
  have hki : k ≠ i := by
    rintro rfl
    exact hnoti hk
  have hnot : squareCenter ∉ d.piece i := d.not_mem_other_piece hki hk
  have hcunion : squareCenter ∈ ⋃ n, P n :=
    hcover.symm ▸ squareCenter_mem_unitSquare
  obtain ⟨n, x, hx, hxeq⟩ := mem_iUnion.mp hcunion
  have hxcenter : x = squareCenter :=
    (g n).injective (hxeq.trans (hfix n).symm)
  exact hnot (hxcenter ▸ hx)

/-- A distinct original copy fixing the center, together with a four-copy
packing by square symmetries, excludes a protected center. -/
theorem not_hasProtectedCenter_of_square_symmetry_packing (d : SquareDissection)
    {i j : Fin 4} (hij : i ≠ j) (e : Plane ≃ᵃⁱ[ℝ] Plane)
    (he : e '' d.piece i = d.piece j)
    (hefix : e squareCenter = squareCenter)
    (g : Fin 4 → Plane ≃ᵃⁱ[ℝ] Plane)
    (hg : ∀ n, g n '' unitSquare ⊆ unitSquare)
    (hdis : Pairwise fun n m =>
      Disjoint (interior (g n '' d.piece i)) (interior (g m '' d.piece i))) :
    ¬ d.HasProtectedCenter := by
  intro hc
  have hcenter := d.center_mem_interior_of_fixed_piece_packing i g
    (fun n => SquareSymmetry.center_fixed_of_maps_square_into_square (g n) (hg n))
    (fun n => (image_mono (d.piece_subset i)).trans (hg n)) hdis hc
  exact (d.center_not_mem_fixed_pair hij e he hefix).1 hcenter

end Puzzling139335.SquareDissection
