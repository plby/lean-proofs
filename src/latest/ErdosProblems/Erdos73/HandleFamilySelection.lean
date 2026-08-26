import ErdosProblems.Erdos73.HandleRowSelection
import ErdosProblems.Erdos73.HandleReindexing
import ErdosProblems.Erdos73.OrderedFiniteSelection

/-! Simultaneous row separation and homogeneous attachment sides. -/

namespace Erdos73.ColumnHandleFamily
noncomputable section
open scoped Classical

open SimpleGraph Finset

variable {V I J : Type*} {G : SimpleGraph V} {c r : ℕ}
variable {S : GraphSubdivisionModel (elementaryWall c r) G}
variable {col : BipartiteColoringOn G S.vertexSet}

theorem reindex_rows (F : ColumnHandleFamily S col I) (f : J → I)
    (hf : Function.Injective f) (i : J) : (F.reindex f hf).rows i = F.rows (f i) := rfl

theorem reverseWhere_rows (F : ColumnHandleFamily S col I) (flip : I → Bool) (i : I) :
    (F.reverseWhere flip).rows i = F.rows i := by
  ext b
  dsimp only [rows, reverseWhere]
  split_ifs <;> simp only [mem_insert, mem_singleton] <;> tauto

theorem orientByRow_rows (F : ColumnHandleFamily S col I) (i : I) :
    F.orientByRow.rows i = F.rows i := F.reverseWhere_rows _ i

theorem endpoint_row_mem (F : ColumnHandleFamily S col I) (i : I) (b : Bool) :
    (F.endpoint i b).val.1 ∈ F.rows i := by
  cases b
  · exact mem_insert_self _ _
  · exact mem_insert_of_mem (mem_singleton_self _)

theorem endpoint_row_ne (F : ColumnHandleFamily S col I)
    (hdis : Pairwise (fun i j => Disjoint (F.rows i) (F.rows j)))
    {i j : I} (hij : i ≠ j) (b e : Bool) :
    (F.endpoint i b).val.1.val ≠ (F.endpoint j e).val.1.val := by
  intro he
  have hh := Fin.ext he
  apply Finset.disjoint_left.mp (hdis hij) (F.endpoint_row_mem i b)
  rw [hh]
  exact F.endpoint_row_mem j e

theorem sourceRow_injective (F : ColumnHandleFamily S col I)
    (hdis : Pairwise (fun i j => Disjoint (F.rows i) (F.rows j))) :
    Function.Injective (fun i => (F.sourceNail i).val.1.val) := by
  intro i j he
  by_contra hn
  exact F.endpoint_row_ne hdis hn false false he

theorem lowerRank_injOn (F : ColumnHandleFamily S col I) (hc : 2 ≤ c) (s : Finset I) :
    Set.InjOn F.lowerRank (s : Set I) := by
  intro i _ j _ he
  by_contra hn
  exact (F.sorted_ranks_separate hc hn).1 he

def attachmentSides (F : ColumnHandleFamily S col I) (i : I) : Bool × Bool :=
  (decide ((F.sourceNail i).val.2.val ≤ 1), decide ((F.targetNail i).val.2.val ≤ 1))

theorem exists_homogeneous_row_disjoint_subfamily (F : ColumnHandleFamily S col I)
    (hc : 2 ≤ c) (s : Finset I) (k : ℕ) (hsize : 8 * (4 * k - 1) < s.card) :
    ∃ E : ColumnHandleFamily S col (Fin k),
      Pairwise (fun i j => Disjoint (E.rows i) (E.rows j)) ∧
      ∃ sides : Bool × Bool, ∀ i, E.attachmentSides i = sides := by
  obtain ⟨t, hts, htcard, htdis⟩ := F.exists_row_disjoint_subfamily hc s (4 * k) hsize
  obtain ⟨sides, u, hut, hucard, husides⟩ := exists_large_finite_fiber t F.attachmentSides k
    (by simpa only [Fintype.card_prod, Fintype.card_bool] using htcard)
  obtain ⟨f, hf, hfu, _⟩ := exists_rank_ordered_selection u F.lowerRank
    (F.lowerRank_injOn hc u) k hucard
  refine ⟨F.reindex f hf, ?_, sides, ?_⟩
  · intro i j hij
    exact htdis (hut (hfu i)) (hut (hfu j)) (hf.ne hij)
  · intro i
    exact husides (f i) (hfu i)

theorem orientByRow_left (F : ColumnHandleFamily S col I)
    (hs : ∀ i, (F.sourceNail i).val.2.val ≤ 1)
    (ht : ∀ i, (F.targetNail i).val.2.val ≤ 1) (i : I) :
    (F.orientByRow.sourceNail i).val.2.val ≤ 1 ∧
      (F.orientByRow.targetNail i).val.2.val ≤ 1 := by
  dsimp only [orientByRow, reverseWhere]
  split_ifs
  · exact ⟨ht i, hs i⟩
  · exact ⟨hs i, ht i⟩

theorem orientByRow_right (F : ColumnHandleFamily S col I)
    (hs : ∀ i, 2 * (c - 1) ≤ (F.sourceNail i).val.2.val)
    (ht : ∀ i, 2 * (c - 1) ≤ (F.targetNail i).val.2.val) (i : I) :
    2 * (c - 1) ≤ (F.orientByRow.sourceNail i).val.2.val ∧
      2 * (c - 1) ≤ (F.orientByRow.targetNail i).val.2.val := by
  dsimp only [orientByRow, reverseWhere]
  split_ifs
  · exact ⟨ht i, hs i⟩
  · exact ⟨hs i, ht i⟩

end
end Erdos73.ColumnHandleFamily
