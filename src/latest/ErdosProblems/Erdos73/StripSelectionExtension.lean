import ErdosProblems.Erdos73.StripSelectionState

/-! Extend the selection state while retaining all disjointness and avoidance invariants. -/

namespace Erdos73
noncomputable section
open scoped Classical

open SimpleGraph Finset Erdos73Infrastructure.SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {c r m i : ℕ}
variable {S : GraphSubdivisionModel (elementaryWall c r) G} {color : V → Bool}
variable {P : Fin m → GraphPath G}

def BrickStripSelectionState.extend (st : BrickStripSelectionState S color P i)
    (hdis : Pairwise (fun j k => Disjoint (P j).vertexSet (P k).vertexSet))
    (t : SelectedBrickSegment S color P) (ht : t.origin ∉ st.used)
    (hrow : t.rows ⊆ Finset.univ \ st.forbiddenRows)
    (hcol : t.columns ⊆ Finset.univ \ st.forbiddenColumns)
    (havoid : ∀ j, j ∉ st.forbiddenColumns →
      j ∉ endpointBrickColumns S t.path.source t.path.target →
        Disjoint t.path.vertexSet (brickFaceColumnStrip S j)) :
    BrickStripSelectionState S color P (i + 1) := by
  let R := st.forbiddenRows ∪ t.rows
  let E := endpointBrickColumns S t.path.source t.path.target
  let C := (st.forbiddenColumns ∪ t.columns) ∪ E
  have hrows (j : Fin i) : Disjoint t.rows (st.segment j).rows := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    exact (mem_sdiff.mp (hrow hx)).2 (st.rows_subset j hy)
  have hcols (j : Fin i) : Disjoint t.columns (st.segment j).columns := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    exact (mem_sdiff.mp (hcol hx)).2 (st.columns_subset j hy)
  have hpaths (j : Fin i) : Disjoint t.path.vertexSet (st.segment j).path.vertexSet := by
    have hne : t.origin ≠ (st.segment j).origin := by
      intro he
      apply ht
      rw [he]
      exact st.origin_used j
    exact (hdis hne).mono t.support_subset (st.segment j).support_subset
  have holdC : st.forbiddenColumns ⊆ C := fun x hx =>
    mem_union_left _ (mem_union_left _ hx)
  refine {
    used := insert t.origin st.used
    used_card := ?_
    forbiddenRows := R
    forbiddenColumns := C
    rows_card := ?_
    columns_card := ?_
    segment := Fin.cases t st.segment
    origin_used := ?_
    rows_subset := ?_
    columns_subset := ?_
    rows_disjoint := ?_
    columns_disjoint := ?_
    paths_disjoint := ?_
    avoids_available_columns := ?_ }
  · exact (card_insert_le _ _).trans (Nat.add_le_add_right st.used_card 1)
  · have hh := (card_union_le st.forbiddenRows t.rows).trans
      (Nat.add_le_add st.rows_card t.rows_card)
    change R.card ≤ 2 * (i + 1)
    dsimp only [R]
    omega
  · have hh := card_union_le (st.forbiddenColumns ∪ t.columns) E
    have hh' := card_union_le st.forbiddenColumns t.columns
    have hE := endpointBrickColumns_card_le_four S t.path.source t.path.target
    have hs := st.columns_card
    have ht := t.columns_card
    change C.card ≤ 6 * (i + 1)
    dsimp only [C, E] at *
    omega
  · exact Fin.cases (mem_insert_self _ _)
      (fun j => mem_insert_of_mem (st.origin_used j))
  · refine Fin.cases ?_ (fun j => ?_)
    · exact subset_union_right
    · exact (st.rows_subset j).trans subset_union_left
  · refine Fin.cases ?_ (fun j => ?_)
    · exact fun x hx => mem_union_left _ (mem_union_right _ hx)
    · exact (st.columns_subset j).trans holdC
  · exact pairwise_fin_succ_iff.mpr ⟨fun j => (hrows j).symm, hrows, st.rows_disjoint⟩
  · exact pairwise_fin_succ_iff.mpr ⟨fun j => (hcols j).symm, hcols, st.columns_disjoint⟩
  · exact pairwise_fin_succ_iff.mpr ⟨fun j => (hpaths j).symm, hpaths, st.paths_disjoint⟩
  · refine Fin.cases ?_ (fun j => ?_)
    · intro a ha
      exact havoid a (fun hh => ha (holdC hh)) (fun hh => ha (mem_union_right _ hh))
    · intro a ha
      exact st.avoids_available_columns j a (fun hh => ha (holdC hh))

end
end Erdos73
