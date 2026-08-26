import ErdosProblems.Erdos19.MediumExtension
import ErdosProblems.Erdos19.MediumPaletteControl
import ErdosProblems.Erdos19.ReservedPaletteEmbedding
import ErdosProblems.Erdos19.ReservedPaletteParameters

/-! # Large and medium edges in the branch with a palette saving -/

namespace Erdos19.SetHypergraph

open Finset

theorem eventually_medium_coloring_of_large_edge_saving (R b a u : ℕ)
    (hb : 0 < b) (ha : 0 < a) (hu : 0 < u)
    (hR : u ^ 2 * (2 * b ^ 4) + 1 ≤ R) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ H : SetHypergraph (Fin n), H.IsLinear →
      (∀ e : H, 16 * a * (16 * b ^ 4) + 1 ≤ e.1.ncard) →
      (H.rankAtLeast R).EdgeColorable (n - n / b ^ 4) →
      ∃ color : H.EdgeColoring (Fin (n - n / (4 * b ^ 4))),
        ∃ palette : Finset (Fin (n - n / (4 * b ^ 4))),
          palette.card = n / (4 * b ^ 4) ∧
          H.HasControlledMediumPalette color palette R (16 * (n / u)) (n / a) := by
  have hb4 : 0 < b ^ 4 := pow_pos hb _
  have hs : 0 < 16 * b ^ 4 := by omega
  obtain ⟨N₀, hN₀⟩ := eventually_extend_medium_edges_palette R (16 * b ^ 4) a
    (by omega) hs ha
  refine ⟨max N₀ 1, ?_⟩
  intro n hn H hlinear hmin hsave
  have hn₀ : N₀ ≤ n := (le_max_left _ _).trans hn
  have hnpos : 0 < n := (le_max_right _ _).trans hn
  let L := H.rankAtLeast R
  let M := H.rankBelow R
  have hL := H.rankAtLeast_linear hlinear R
  have hM := H.rankBelow_linear hlinear R
  have hLmin (e : L) : u ^ 2 * (2 * b ^ 4) + 1 ≤ e.1.ncard := hR.trans e.2.2
  obtain ⟨cL, hcL⟩ := L.exists_cover_bounded_coloring_of_saving hL n u (b ^ 4)
    (Fintype.card_fin n) hnpos hu hb4 hLmin hsave
  obtain ⟨cL', palette, hcL', hcard, hunused⟩ := L.exists_coloring_with_unused_palette
    (n - n / (2 * b ^ 4)) (n / (4 * b ^ 4)) (n - n / (4 * b ^ 4)) (16 * (n / u))
    cL hcL (saving_reserved_palette_room n (b ^ 4) hb4)
  have hMmin (e : M) : 16 * a * (16 * b ^ 4) + 1 ≤ e.1.ncard := hmin ⟨e.1, e.2.1⟩
  have hMmax (e : M) : e.1.ncard ≤ R := e.2.2.le
  have hpalette : 2 * (n / (16 * b ^ 4)) ≤ palette.card := by
    rw [hcard]
    exact medium_reserved_palette_room n (b ^ 4) hb4
  obtain ⟨c, _, hnew, hcover, hrest⟩ := hN₀ n hn₀ L M hL hM
    (n - n / (4 * b ^ 4)) cL' (16 * (n / u)) hcL' palette 2 (by norm_num)
    (fun e he ↦ (hunused e he).elim) hMmin hMmax hpalette
  have hpalCover : ∀ x ∈ palette,
      ((L ∪ M).coveredVertices {e | c.color e = x}).ncard ≤ n / a := by
    intro x hx
    have hempty := L.coveredVertices_eq_empty_of_unused_color cL' x
      (fun e he ↦ hunused e (he.symm ▸ hx))
    have h := hcover x
    rw [hempty, Set.ncard_empty, Nat.zero_add] at h
    exact h
  obtain ⟨color, hcontrol⟩ := H.controlled_medium_palette_of_partition R (16 * (n / u))
    (n / a) palette ⟨c, hnew, hpalCover, hrest⟩
  exact ⟨color, palette, hcard, hcontrol⟩

#print axioms eventually_medium_coloring_of_large_edge_saving

end Erdos19.SetHypergraph
