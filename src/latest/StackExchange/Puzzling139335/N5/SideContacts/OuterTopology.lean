import StackExchange.Puzzling139335.N5.SideContacts.ConnectedInterior
import StackExchange.Puzzling139335.N5.SideContacts.CornerCollars
import StackExchange.Puzzling139335.N5.Remainder

/-!
# Connected diagonal contact of the actual outer pair

The split bottom-left corner gives an actual interior contact of the
diagonal pair, hence connected interior of its union.  The connected
middle remainder reaches the exterior at the uniquely owned top-right
corner, so the outer union has connected complement as well.  The proved
two-region Jordan-union theorem then gives a connected common set.
-/

open Set

namespace Puzzling139335.N5

variable {d : SquareDissection}

/-- The reflected piece is above the main diagonal. -/
theorem Normalized.above_diagonal (h : Normalized d) :
    d.piece 1 ⊆ {p | p 0 ≤ p 1} := by
  intro p hp
  rw [← h.diagonal_image] at hp
  obtain ⟨q, hq, rfl⟩ := hp
  change q 1 ≤ q 0
  exact h.below_diagonal hq

/-- The whole common set of the diagonal pair lies on its reflection axis. -/
theorem Normalized.outer_inter_diagonal (h : Normalized d) :
    ∀ p ∈ d.piece 0 ∩ d.piece 1, p 0 = p 1 := by
  intro p hp
  exact le_antisymm (h.above_diagonal hp.2) (h.below_diagonal hp.1)

/-- Local coverage near the split corner connects the outer union's interior. -/
theorem Normalized.outer_union_isConnected_interior (h : Normalized d) :
    IsConnected (interior (d.piece 0 ∪ d.piece 1)) := by
  obtain ⟨a, _, _, ha, ha0, ha1⟩ := h.exists_common_diagonal_interior
  exact SideContacts.isConnected_interior_union_of_common_interior_point
    (d.jordan 0) (d.jordan 1) ha ha0 ha1

/-- The protected center belongs to neither closed outer piece. -/
theorem Normalized.center_not_mem_outer_pair (h : Normalized d)
    (hc : d.HasProtectedCenter) : squareCenter ∉ d.piece 0 ∪ d.piece 1 := by
  obtain ⟨i, hi⟩ := hc
  rcases h.center_owner_cases hi with rfl | rfl
  · rintro (h0 | h1)
    · exact d.not_mem_other_piece (by decide : (2 : Fin 4) ≠ 0) hi h0
    · exact d.not_mem_other_piece (by decide : (2 : Fin 4) ≠ 1) hi h1
  · rintro (h0 | h1)
    · exact d.not_mem_other_piece (by decide : (3 : Fin 4) ≠ 0) hi h0
    · exact d.not_mem_other_piece (by decide : (3 : Fin 4) ≠ 1) hi h1

/-- The outer pair has connected complement because the actual connected
middle interior joins the square exterior at the top-right corner. -/
theorem Normalized.outer_union_isConnected_compl (h : Normalized d)
    (hc : d.HasProtectedCenter) : IsConnected (d.piece 0 ∪ d.piece 1)ᶜ := by
  let U := d.piece 2 ∪ d.piece 3
  have hU : IsJordanRegion U := h.remainder_jordan hc
  let K := insert (corner 2) (interior U)
  have hTRclosure : corner 2 ∈ closure (interior U) := by
    rw [hU.closure_interior]
    exact Or.inl h.top_right
  have hK : IsConnected K :=
    Remainder.isConnected_insert_of_mem_closure hU.isConnected_interior hTRclosure
  have h0U : Disjoint (interior (d.piece 0)) U := disjoint_union_right.mpr
    ⟨d.disjoint_interior_piece (by decide), d.disjoint_interior_piece (by decide)⟩
  have h1U : Disjoint (interior (d.piece 1)) U := disjoint_union_right.mpr
    ⟨d.disjoint_interior_piece (by decide), d.disjoint_interior_piece (by decide)⟩
  have hU0 : Disjoint (interior U) (d.piece 0) :=
    (d.jordan 0).disjoint_interior_left (h0U.symm.mono_left interior_subset)
  have hU1 : Disjoint (interior U) (d.piece 1) :=
    (d.jordan 1).disjoint_interior_left (h1U.symm.mono_left interior_subset)
  have hKU : K ⊆ (d.piece 0 ∪ d.piece 1)ᶜ := by
    rintro p (rfl | hp)
    · rintro (h0 | h1)
      · exact h.unique_top_right 0 (by decide) h0
      · exact h.unique_top_right 1 (by decide) h1
    · rintro (h0 | h1)
      · exact Set.disjoint_left.mp hU0 hp h0
      · exact Set.disjoint_left.mp hU1 hp h1
  have hdense : U ⊆ closure K := by
    rw [← hU.closure_interior]
    exact closure_mono (subset_insert _ _)
  have hcover : U ∪ (d.piece 0 ∪ d.piece 1) = unitSquare := by
    rw [union_comm]
    exact d.four_piece_pair_union
  have hTRexterior : corner 2 ∈ closure unitSquareᶜ := by
    rw [closure_compl]
    exact corner_not_mem_interior_unitSquare 2
  exact Remainder.isConnected_compl_of_connected_omitted_core
    hK hKU hdense hcover isConnected_compl_unitSquare (mem_insert _ _) hTRexterior

/-- Connectedness of the entire common set is a consequence of the actual
dissection, not an assumed interval or arc property. -/
theorem Normalized.outer_inter_isConnected (h : Normalized d)
    (hc : d.HasProtectedCenter) : IsConnected (d.piece 0 ∩ d.piece 1) :=
  HalfTurnRemainder.isConnected_inter_of_connected_interior_compl_union
    (d.jordan 0) (d.jordan 1) (d.disjoint_interiors (by decide))
    h.outer_union_isConnected_interior (h.outer_union_isConnected_compl hc)

end Puzzling139335.N5
