import ErdosProblems.Erdos73.StripSelectionState
import ErdosProblems.Erdos73.BrickTerminalCounts
import ErdosProblems.Erdos73.UnusedTerminalPath

/-! Find a fresh breaking segment and its small available strip network. -/

namespace Erdos73
noncomputable section
open scoped Classical

open SimpleGraph Finset Erdos73Infrastructure.SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {c r m i : ℕ}

theorem BrickStripSelectionState.exists_next_segment
    (S : GraphSubdivisionModel (elementaryWall c r) G) (color : V → Bool)
    (P : Fin m → GraphPath G) (N : Finset V) (b : Bool)
    (hc : 2 ≤ c) (hr : 2 ≤ r)
    (hN : ∀ x ∈ N, ∃ w : ElementaryWallVertex c r,
      x = S.branchVertex w ∧ 0 < w.val.2.val ∧ w.val.2.val + 1 < 2 * c)
    (hcolor : ∀ x ∈ N, color x = b)
    (hP : ∀ j, IsOddTerminalPath N (P j))
    (hdis : Pairwise (fun j k => Disjoint (P j).vertexSet (P k).vertexSet))
    (st : BrickStripSelectionState S color P i)
    (hrows : 2 * i < r - 1) (hcols : 6 * i < c - 1) (hsize : 72 * i * i + i < m) :
    ∃ t : SelectedBrickSegment S color P,
      t.origin ∉ st.used ∧ t.rows ⊆ Finset.univ \ st.forbiddenRows ∧
      t.columns ⊆ Finset.univ \ st.forbiddenColumns ∧
      ∀ j, j ∉ st.forbiddenColumns → j ∉ endpointBrickColumns S t.path.source t.path.target →
        Disjoint t.path.vertexSet (brickFaceColumnStrip S j) := by
  let A := Finset.univ \ st.forbiddenRows
  let B := Finset.univ \ st.forbiddenColumns
  let D := brickStripNetwork S A B
  have hA : A.Nonempty := sdiff_nonempty_of_card_lt_card (by
    simpa only [card_univ, Fintype.card_fin] using st.rows_card.trans_lt hrows)
  have hB : B.Nonempty := sdiff_nonempty_of_card_lt_card (by
    simpa only [card_univ, Fintype.card_fin] using st.columns_card.trans_lt hcols)
  have hbad : (N \ D).card ≤ 72 * i * i := by
    calc
      (N \ D).card ≤ 6 * st.forbiddenRows.card * st.forbiddenColumns.card :=
        interior_terminals_outside_available_strips_card S hc hr N hN _ _
      _ ≤ 6 * (2 * i) * (6 * i) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left 6 st.rows_card) st.columns_card
      _ = 72 * i * i := by ring
  obtain ⟨j, hj, hs, ht⟩ := exists_unused_terminal_path P N D
    (fun j => ⟨(hP j).source_mem, (hP j).target_mem⟩) hdis st.used (by
      rw [Fintype.card_fin]
      exact (Nat.add_le_add hbad st.used_card).trans_lt hsize)
  have hbP : ParityBreaking color (P j) := parityBreaking_of_odd_of_sameColor color (P j)
    (hP j).odd_length ((hcolor _ (hP j).source_mem).trans (hcolor _ (hP j).target_mem).symm)
  obtain ⟨U, hU, hUP⟩ := exists_parityBreaking_segment color D (P j) hs ht hbP
  obtain ⟨A', B', hA'A, hB'B, hA'ne, hB'ne, hA'card, hB'card, hs', ht'⟩ :=
    exists_small_brickStripNetwork S A B hA hB U.source U.target hU.source_mem hU.target_mem
  have hsmall : IsParityBreakingPath color (brickStripNetwork S A' B') U :=
    ⟨hs', ht', hU.breaking, fun x hx hxD =>
      hU.internal_disjoint x hx (brickStripNetwork_mono S hA'A hB'B hxD)⟩
  let t : SelectedBrickSegment S color P :=
    ⟨U, A', B', hA'ne, hB'ne, hA'card, hB'card, hsmall, j, hUP⟩
  refine ⟨t, hj, hA'A, hB'B, ?_⟩
  intro a ha he
  exact parityBreaking_segment_avoids_unflagged_columns S color A B U hU a
    (mem_sdiff.mpr ⟨mem_univ _, ha⟩) he

end
end Erdos73
