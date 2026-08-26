import ErdosProblems.Erdos73.ColumnHandleFamilies
import ErdosProblems.Erdos73.DisjointSetSelection

/-! At most four disjoint column handles touch a row, so many have disjoint row sets. -/

namespace Erdos73.ColumnHandleFamily
noncomputable section
open scoped Classical

open SimpleGraph Finset

variable {V I : Type*} {G : SimpleGraph V} {c r : ℕ}
variable {S : GraphSubdivisionModel (elementaryWall c r) G}
variable {col : BipartiteColoringOn G S.vertexSet}

def rows (F : ColumnHandleFamily S col I) (i : I) : Finset (Fin r) :=
  {(F.sourceNail i).val.1, (F.targetNail i).val.1}

theorem rows_nonempty (F : ColumnHandleFamily S col I) (i : I) : (F.rows i).Nonempty := by
  exact ⟨(F.sourceNail i).val.1, mem_insert_self _ _⟩

theorem rows_card_le_two (F : ColumnHandleFamily S col I) (i : I) : (F.rows i).card ≤ 2 :=
  (card_insert_le _ _).trans (by simp)

theorem exists_endpoint_at_row (F : ColumnHandleFamily S col I) (i : I) (b : Fin r)
    (hb : b ∈ F.rows i) : ∃ e : Bool, (F.endpoint i e).val.1 = b := by
  rcases mem_insert.mp hb with hb | hb
  · exact ⟨false, hb.symm⟩
  · exact ⟨true, (mem_singleton.mp hb).symm⟩

theorem row_membership_card_le_four (F : ColumnHandleFamily S col I) (hc : 2 ≤ c)
    (s : Finset I) (b : Fin r) : (s.filter (fun i => b ∈ F.rows i)).card ≤ 4 := by
  let A := s.filter (fun i => b ∈ F.rows i)
  have hex (i : A) : ∃ e : Bool, (F.endpoint i.val e).val.1 = b :=
    F.exists_endpoint_at_row i.val b (mem_filter.mp i.property).2
  let f : A → Fin 4 := fun i => brickBoundaryColumnCode (F.endpoint i.val (hex i).choose)
  have hf : Function.Injective f := by
    intro i j hij
    have hrow : (F.endpoint i.val (hex i).choose).val.1 =
        (F.endpoint j.val (hex j).choose).val.1 := (hex i).choose_spec.trans (hex j).choose_spec.symm
    have he := brickBoundaryColumnCode_injective_at_row
      (F.endpoint_boundary i.val (hex i).choose) (F.endpoint_boundary j.val (hex j).choose) hrow hij
    apply Subtype.ext
    by_contra hn
    exact F.endpoint_rank_ne_of_ne_index hc hn _ _ (congrArg brickBoundaryRank he)
  have hh := Fintype.card_le_of_injective f hf
  simpa only [Fintype.card_coe, Fintype.card_fin] using hh

theorem exists_row_disjoint_subfamily (F : ColumnHandleFamily S col I) (hc : 2 ≤ c)
    (s : Finset I) (k : ℕ) (hsize : 8 * (k - 1) < s.card) :
    ∃ t : Finset I, t ⊆ s ∧ k ≤ t.card ∧ (t : Set I).PairwiseDisjoint F.rows :=
  exists_disjoint_subfamily_of_bounded_congestion s F.rows 2 4 k
    (fun i _ => F.rows_nonempty i) (fun i _ => F.rows_card_le_two i)
    (F.row_membership_card_le_four hc s) hsize

end
end Erdos73.ColumnHandleFamily
