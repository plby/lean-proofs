import StackExchange.Puzzling139335.N5.Remainder.Symmetry
import StackExchange.Puzzling139335.HalfTurnRemainder.Holes.SquareExterior

/-!
# Connected complement from the two actual removed pieces

The common bottom-left corner is absent from the retained pieces.  Adding it
to each removed interior and to the square exterior gives connected sets
with a common point.  Regular closedness makes their union dense in the
entire complement of the retained pieces.
-/

open Set

namespace Puzzling139335.N5.Remainder

/-- Adding a point of the closure to a connected set preserves connectedness. -/
theorem isConnected_insert_of_mem_closure {X : Type*} [TopologicalSpace X]
    {K : Set X} {c : X} (hK : IsConnected K) (hc : c ∈ closure K) :
    IsConnected (insert c K) := by
  apply hK.subset_closure (subset_insert c K)
  rintro x (rfl | hx)
  · exact hc
  · exact subset_closure hx

/-- A connected core of the removed set joins the connected outer exterior
at one of its closure points.  If the core is dense in the removed set, the
whole complement of the retained set is connected. -/
theorem isConnected_compl_of_connected_omitted_core
    {X : Type*} [TopologicalSpace X] {K R U Q : Set X} {c : X}
    (hK : IsConnected K) (hKU : K ⊆ Uᶜ) (hR : R ⊆ closure K)
    (hcover : R ∪ U = Q) (hQ : IsConnected Qᶜ)
    (hcK : c ∈ K) (hcQ : c ∈ closure Qᶜ) : IsConnected Uᶜ := by
  have hUQ : U ⊆ Q := by
    intro x hx
    rw [← hcover]
    exact Or.inr hx
  have hE := isConnected_insert_of_mem_closure hQ hcQ
  have hT : IsConnected (K ∪ insert c Qᶜ) :=
    IsConnected.union ⟨c, hcK, mem_insert c Qᶜ⟩ hK hE
  apply hT.subset_closure
  · rintro x (hxK | rfl | hxQ)
    · exact hKU hxK
    · exact hKU hcK
    · exact fun hxU => hxQ (hUQ hxU)
  · intro x hxU
    by_cases hxQ : x ∈ Q
    · have hxR : x ∈ R := by
        rw [← hcover] at hxQ
        exact hxQ.resolve_right hxU
      exact closure_mono (show K ⊆ K ∪ insert c Qᶜ from subset_union_left) (hR hxR)
    · exact subset_closure (Or.inr (Or.inr hxQ))

end Puzzling139335.N5.Remainder

namespace Puzzling139335.N5

/-- The split bottom-left corner belongs to neither retained piece. -/
theorem Normalized.bottom_left_not_mem_remainder {d : SquareDissection}
    (h : Normalized d) : corner 0 ∉ d.piece 2 ∪ d.piece 3 := by
  have howners := split_membership_iff_of_two_owners d h.split_count
    (by decide : (0 : Fin 4) ≠ 1) h.bottom_left h.left_bottom
  rintro (h2 | h3)
  · have hbad := (howners 2).mp h2
    simpa using hbad
  · have hbad := (howners 3).mp h3
    simpa using hbad

/-- Connectedness of the complement is obtained from physical corner
ownership; it does not assume any Jordan property of the remainder. -/
theorem Normalized.remainder_isConnected_compl {d : SquareDissection}
    (h : Normalized d) : IsConnected (d.piece 2 ∪ d.piece 3)ᶜ := by
  let K := insert (corner 0) (interior (d.piece 0)) ∪
    insert (corner 0) (interior (d.piece 1))
  have h0cl : corner 0 ∈ closure (interior (d.piece 0)) := by
    rw [(d.jordan 0).closure_interior]
    exact h.bottom_left
  have h1cl : corner 0 ∈ closure (interior (d.piece 1)) := by
    rw [(d.jordan 1).closure_interior]
    exact h.left_bottom
  have hK : IsConnected K := IsConnected.union
    ⟨corner 0, mem_insert _ _, mem_insert _ _⟩
    (Remainder.isConnected_insert_of_mem_closure (d.jordan 0).isConnected_interior h0cl)
    (Remainder.isConnected_insert_of_mem_closure (d.jordan 1).isConnected_interior h1cl)
  have hKU : K ⊆ (d.piece 2 ∪ d.piece 3)ᶜ := by
    rintro x ((rfl | hx0) | rfl | hx1)
    · exact h.bottom_left_not_mem_remainder
    · rintro (hx2 | hx3)
      · exact d.not_mem_other_piece (by decide : (0 : Fin 4) ≠ 2) hx0 hx2
      · exact d.not_mem_other_piece (by decide : (0 : Fin 4) ≠ 3) hx0 hx3
    · exact h.bottom_left_not_mem_remainder
    · rintro (hx2 | hx3)
      · exact d.not_mem_other_piece (by decide : (1 : Fin 4) ≠ 2) hx1 hx2
      · exact d.not_mem_other_piece (by decide : (1 : Fin 4) ≠ 3) hx1 hx3
  have hR : d.piece 0 ∪ d.piece 1 ⊆ closure K := by
    apply union_subset
    · rw [← (d.jordan 0).closure_interior]
      exact closure_mono (fun x hx => Or.inl (Or.inr hx))
    · rw [← (d.jordan 1).closure_interior]
      exact closure_mono (fun x hx => Or.inr (Or.inr hx))
  have hcorner : corner 0 ∈ closure unitSquareᶜ := by
    rw [closure_compl]
    exact corner_not_mem_interior_unitSquare 0
  exact Remainder.isConnected_compl_of_connected_omitted_core hK hKU hR
    d.four_piece_pair_union isConnected_compl_unitSquare
    (Or.inl (mem_insert _ _)) hcorner

end Puzzling139335.N5
