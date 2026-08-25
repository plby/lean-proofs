import StackExchange.Puzzling139335.JordanRegion
import StackExchange.Puzzling139335.JordanSubarc

/-!
# The outer curve of two Jordan regions sharing an arc

The complementary arcs on the two piece boundaries meet only at their common
endpoints.  Their union is a Jordan curve contained in the frontier of the union
of the pieces.  This construction uses no connectedness hypothesis on the union.
-/

open Set Schoenflies

namespace Puzzling139335.HalfTurnRemainder.JordanUnion

variable {A D M N : Set Plane} {p q x : Plane}

/-- For regular closed pieces, disjoint interiors put every intersection point
on both boundaries. -/
theorem inter_subset_frontier_left (hA : IsJordanRegion A) (hD : IsJordanRegion D)
    (hdis : Disjoint (interior A) (interior D)) : A ∩ D ⊆ frontier A := by
  intro x hx
  rw [hA.isClosed.frontier_eq]
  exact ⟨hx.1, fun hxi =>
    Set.disjoint_left.mp (hD.disjoint_interior_left hdis) hxi hx.2⟩

/-- A boundary point away from the other closed piece remains a boundary point
of the union. -/
theorem mem_frontier_union_of_notMem_right (hA : IsClosed A) (hD : IsClosed D)
    (hx : x ∈ frontier A) (hxD : x ∉ D) : x ∈ frontier (A ∪ D) := by
  refine ⟨subset_closure (Or.inl (hA.frontier_subset hx)), ?_⟩
  intro hxint
  have hsub : interior (A ∪ D) ∩ Dᶜ ⊆ A := by
    rintro y ⟨hy, hyD⟩
    exact (interior_subset hy).elim id (fun h => False.elim (hyD h))
  have hxA : x ∈ interior A :=
    (isOpen_interior.inter hD.isOpen_compl).subset_interior_iff.mpr hsub ⟨hxint, hxD⟩
  exact hx.2 hxA

/-- A closed set containing all nonendpoint points of an arc contains the
whole arc, since each endpoint is a limit of those points. -/
theorem arc_subset_closed_of_diff_subset {F : Set Plane} (hM : IsArcBetween M p q)
    (hF : IsClosed F) (hsub : M \ {p, q} ⊆ F) : M ⊆ F := by
  have hcl : closure (M \ {p, q}) ⊆ F := hF.closure_subset_iff.mpr hsub
  intro x hx
  by_cases hxp : x = p
  · subst x
    exact hcl hM.left_mem_closure_diff
  by_cases hxq : x = q
  · subst x
    exact hcl hM.right_mem_closure_diff
  exact hsub ⟨hx, by simpa only [mem_insert_iff, mem_singleton_iff] using not_or.mpr ⟨hxp, hxq⟩⟩

/-- The complementary arc of the first boundary stays on the union boundary,
including its endpoints. -/
theorem outer_arc_subset_frontier_union (hA : IsJordanRegion A)
    (hD : IsJordanRegion D) (hcut : IsCutPair (frontier A) p q (A ∩ D) M) :
    M ⊆ frontier (A ∪ D) := by
  apply arc_subset_closed_of_diff_subset hcut.snd isClosed_frontier
  rintro x ⟨hxM, hxends⟩
  apply mem_frontier_union_of_notMem_right hA.isClosed hD.isClosed (hcut.snd_subset hxM)
  intro hxD
  have hxI : x ∈ A ∩ D := ⟨hA.isClosed.frontier_subset (hcut.snd_subset hxM), hxD⟩
  exact hxends (hcut.inter_eq ▸ (show x ∈ (A ∩ D) ∩ M from ⟨hxI, hxM⟩))

/-- The two remaining arcs meet exactly at their shared endpoints. -/
theorem outer_arcs_inter_eq (hA : IsJordanRegion A) (hD : IsJordanRegion D)
    (hcutA : IsCutPair (frontier A) p q (A ∩ D) M)
    (hcutD : IsCutPair (frontier D) p q (A ∩ D) N) : M ∩ N = {p, q} := by
  apply Subset.antisymm
  · rintro x ⟨hxM, hxN⟩
    have hxI : x ∈ A ∩ D :=
      ⟨hA.isClosed.frontier_subset (hcutA.snd_subset hxM),
        hD.isClosed.frontier_subset (hcutD.snd_subset hxN)⟩
    exact hcutA.inter_eq ▸ (show x ∈ (A ∩ D) ∩ M from ⟨hxI, hxM⟩)
  · exact pair_subset ⟨hcutA.snd.left_mem, hcutD.snd.left_mem⟩
      ⟨hcutA.snd.right_mem, hcutD.snd.right_mem⟩

/-- Two Jordan regions sharing a whole nondegenerate boundary arc have a
canonically described outer Jordan curve. -/
theorem exists_outer_arcs (hA : IsJordanRegion A) (hD : IsJordanRegion D)
    (hdis : Disjoint (interior A) (interior D))
    (hI : IsArcBetween (A ∩ D) p q) :
    ∃ M N, IsCutPair (frontier A) p q (A ∩ D) M ∧
      IsCutPair (frontier D) p q (A ∩ D) N ∧
      IsCutPair (M ∪ N) p q M N ∧ IsJordanCurve (M ∪ N) ∧
      M ∪ N ⊆ frontier (A ∪ D) := by
  obtain ⟨M, hM⟩ := hA.frontier_isJordanCurve.exists_cutPair_of_subset_arc hI
    (inter_subset_frontier_left hA hD hdis)
  have hID : A ∩ D ⊆ frontier D := by
    simpa only [inter_comm] using inter_subset_frontier_left hD hA hdis.symm
  obtain ⟨N, hN⟩ := hD.frontier_isJordanCurve.exists_cutPair_of_subset_arc hI hID
  have hmeet := outer_arcs_inter_eq hA hD hM hN
  refine ⟨M, N, hM, hN, ⟨hM.snd, hN.snd, rfl, hmeet⟩, ?_, ?_⟩
  · apply IsJordanCurve.of_two_arcs hM.snd hN.snd.reverse
    intro x hxM hxN
    have hx : x ∈ ({p, q} : Set Plane) := hmeet ▸ (show x ∈ M ∩ N from ⟨hxM, hxN⟩)
    simpa only [mem_insert_iff, mem_singleton_iff] using hx
  · apply union_subset (outer_arc_subset_frontier_union hA hD hM)
    have hN' : IsCutPair (frontier D) p q (D ∩ A) N := by
      simpa only [inter_comm] using hN
    simpa only [union_comm] using outer_arc_subset_frontier_union hD hA hN'

end Puzzling139335.HalfTurnRemainder.JordanUnion
