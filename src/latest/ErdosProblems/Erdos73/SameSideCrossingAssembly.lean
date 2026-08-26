import ErdosProblems.Erdos73.SameSideCrossingSelection
import ErdosProblems.Erdos73.EqualRowElimination

/-! Full same-side crossing extraction, including arbitrary original path orientations. -/

namespace Erdos73.ColumnHandleFamily
noncomputable section
open scoped Classical

open SimpleGraph Finset

variable {V I : Type*} [Fintype V] {G : SimpleGraph V} {c r : ℕ}
variable {S : GraphSubdivisionModel (elementaryWall c r) G}
variable {col : BipartiteColoringOn G S.vertexSet}

theorem oddPacking_or_sameSide_crossing_any_rows (F : ColumnHandleFamily S col I)
    (leftSide : Bool) (k : ℕ) (hc : k + 2 ≤ c)
    (hdis : Pairwise (fun i j => Disjoint (F.rows i) (F.rows j)))
    (hs : ∀ i, if leftSide then (F.sourceNail i).val.2.val ≤ 1
      else 2 * (c - 1) ≤ (F.sourceNail i).val.2.val)
    (ht : ∀ i, if leftSide then (F.targetNail i).val.2.val ≤ 1
      else 2 * (c - 1) ≤ (F.targetNail i).val.2.val)
    (s : Finset I) (hsize : k - 1 + pureEndpointPairBound k ≤ s.card) :
    HasOddCyclePacking k G ∨ HasSameSideCrossingHandles (S := S) (col := col) leftSide k := by
  let E := F.orientByRow
  have hEdis : Pairwise (fun i j => Disjoint (E.rows i) (E.rows j)) := by
    intro i j hij
    simpa only [E, orientByRow_rows] using hdis hij
  have hEs (i : I) : if leftSide then (E.sourceNail i).val.2.val ≤ 1
      else 2 * (c - 1) ≤ (E.sourceNail i).val.2.val := by
    cases leftSide
    · exact (F.orientByRow_right hs ht i).1
    · exact (F.orientByRow_left hs ht i).1
  have hEt (i : I) : if leftSide then (E.targetNail i).val.2.val ≤ 1
      else 2 * (c - 1) ≤ (E.targetNail i).val.2.val := by
    cases leftSide
    · exact (F.orientByRow_right hs ht i).2
    · exact (F.orientByRow_left hs ht i).2
  obtain hpack | ⟨f, hf, _, hstrict⟩ := E.oddPacking_or_strict_row_selection hEdis
    F.orientByRow_ordered s k (pureEndpointPairBound k) hsize
  · exact Or.inl hpack
  exact (E.reindex f hf).oddPacking_or_sameSide_crossing leftSide k hc
    (fun _ _ hij => hEdis (hf.ne hij)) hstrict
    (fun i => hEs (f i)) (fun i => hEt (f i)) univ
    (by simp only [card_univ, Fintype.card_fin]; exact le_rfl)

end
end Erdos73.ColumnHandleFamily
