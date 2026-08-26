import ErdosProblems.Erdos73.StripSelectionNext
import ErdosProblems.Erdos73.StripSelectionExtension
import ErdosProblems.Erdos73.UnflaggedBlock

/-! Complete finite strip selection with a free consecutive block and congestion five. -/

namespace Erdos73
noncomputable section
open scoped Classical

open SimpleGraph Finset Erdos73Infrastructure.SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {c r m h : ℕ}

theorem exists_brickStripSelectionState
    (S : GraphSubdivisionModel (elementaryWall c r) G) (color : V → Bool)
    (P : Fin m → GraphPath G) (N : Finset V) (b : Bool)
    (hc : 2 ≤ c) (hr : 2 ≤ r)
    (hN : ∀ x ∈ N, ∃ w : ElementaryWallVertex c r,
      x = S.branchVertex w ∧ 0 < w.val.2.val ∧ w.val.2.val + 1 < 2 * c)
    (hcolor : ∀ x ∈ N, color x = b)
    (hP : ∀ j, IsOddTerminalPath N (P j))
    (hdis : Pairwise (fun j k => Disjoint (P j).vertexSet (P k).vertexSet))
    (hrows : 2 * h < r - 1) (hcols : 6 * h < c - 1) (hsize : 72 * h * h + h < m) :
    Nonempty (BrickStripSelectionState S color P h) := by
  have hex : ∀ i ≤ h, Nonempty (BrickStripSelectionState S color P i) := by
    intro i
    induction i with
    | zero => exact fun _ => ⟨BrickStripSelectionState.empty S color P⟩
    | succ i ih =>
      intro hih
      have hi : i ≤ h := by omega
      obtain ⟨st⟩ := ih hi
      have hisize : 72 * i * i + i < m :=
        (Nat.add_le_add (Nat.mul_le_mul (Nat.mul_le_mul_left 72 hi) hi) hi).trans_lt hsize
      obtain ⟨t, ht, hrow, hcol, havoid⟩ :=
        st.exists_next_segment S color P N b hc hr hN hcolor hP hdis
          ((Nat.mul_le_mul_left 2 hi).trans_lt hrows)
          ((Nat.mul_le_mul_left 6 hi).trans_lt hcols) hisize
      exact ⟨st.extend hdis t ht hrow hcol havoid⟩
  exact hex h le_rfl

theorem BrickStripSelectionState.exists_free_block
    {S : GraphSubdivisionModel (elementaryWall c r) G} {color : V → Bool}
    {P : Fin m → GraphPath G} (st : BrickStripSelectionState S color P h)
    (d : ℕ) (hwidth : (6 * h + 1) * d ≤ c - 1) :
    ∃ a : ℕ, a + d ≤ c - 1 ∧
      ∀ j : Fin h, ∀ b : Fin (c - 1), a ≤ b.val → b.val < a + d →
        Disjoint (st.segment j).path.vertexSet (brickFaceColumnStrip S b) := by
  obtain ⟨a, ha, hfree⟩ := exists_unflagged_block st.forbiddenColumns st.columns_card hwidth
  exact ⟨a, ha, fun j b hlo hhi => st.avoids_available_columns j b (hfree b hlo hhi)⟩

theorem BrickStripSelectionState.support_congestion_le_five
    {S : GraphSubdivisionModel (elementaryWall c r) G} {color : V → Bool}
    {P : Fin m → GraphPath G} (st : BrickStripSelectionState S color P h) (x : V) :
    (Finset.univ.filter (fun j => x ∈
      brickStripNetwork S (st.segment j).rows (st.segment j).columns ∪
        (st.segment j).path.vertexSet)).card ≤ 5 := by
  exact union_disjoint_supports_membership_card_le_add_one
    (fun j => brickStripNetwork S (st.segment j).rows (st.segment j).columns)
    (fun j => (st.segment j).path.vertexSet) st.paths_disjoint 4
    (brickStripNetwork_membership_card_le_four S (fun j => (st.segment j).rows)
      (fun j => (st.segment j).columns) st.rows_disjoint st.columns_disjoint) x

end
end Erdos73
