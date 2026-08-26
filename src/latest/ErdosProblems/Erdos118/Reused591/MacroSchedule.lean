import ErdosProblems.Erdos118.Reused591.MacroForest

namespace Erdos118.Reused591

/-!
# The serial countable macro construction

Every unfinished node receives children with parameters `1, 2, ...`.
All nodes remain available forever, and the global log grows only by
the freshly chosen block. The pairing schedule never refers forward.
-/

namespace Erdos591.Positive.Game.Macro.Forest

variable {N H : Set ℕ} (hH : H.Infinite) (b : Concrete.Hist N → ℕ)

noncomputable def stages : ℕ → Stage
  | 0 => Stage.initial
  | r + 1 => Stage.next hH b (stages r)

noncomputable def chunkAt (r : ℕ) :
    Chunk H b (stages hH b r).support (stages hH b r).parameter
      (stages hH b r).scheduledParent.cursor :=
  chooseChunk hH b (stages hH b r).support (stages hH b r).parameter
    (stages hH b r).scheduledParent.cursor

theorem stages_succ (r : ℕ) : stages hH b (r + 1) =
    (stages hH b r).append (stages hH b r).scheduledParent
      (chunkAt hH b r).block (chunkAt hH b r).cursor (chunkAt hH b r).expansion.legal := rfl

theorem stages_valid (r : ℕ) : Stage.Valid H b (stages hH b r) := by
  induction r with
  | zero => exact Stage.valid_initial H b
  | succ r ih => exact ih.next hH

@[simp] theorem stages_log_length (r : ℕ) : (stages hH b r).log.length = r := by
  induction r with
  | zero => rfl
  | succ r ih => simp [stages_succ, Stage.append, ih]

@[simp] theorem stages_nodes_length (r : ℕ) : (stages hH b r).nodes.length = r + 1 := by
  simpa using (stages_valid hH b r).shape

noncomputable def node (n : ℕ) : Node := (stages hH b n).nodes.getD n Node.initial

@[simp] theorem node_zero : node hH b 0 = Node.initial := rfl

theorem node_mem (n : ℕ) : node hH b n ∈ (stages hH b n).nodes := by
  have hn : n < (stages hH b n).nodes.length := by simp
  rw [node, List.getD_eq_getElem _ _ hn]
  exact List.getElem_mem hn

theorem stage_get_next (r n : ℕ) (hn : n ≤ r) :
    (stages hH b (r + 1)).nodes.getD n Node.initial =
      (stages hH b r).nodes.getD n Node.initial := by
  rw [stages_succ]
  apply List.getD_append
  simpa using Nat.lt_succ_of_le hn

/-- A node's stored data never changes at later construction times. -/
theorem node_stable (n r : ℕ) (hn : n ≤ r) :
    (stages hH b r).nodes.getD n Node.initial = node hH b n := by
  induction r, hn using Nat.le_induction with
  | base => rfl
  | succ r hr ih => exact (stage_get_next hH b r n hr).trans ih

theorem stage_parent (r : ℕ) :
    (stages hH b r).scheduledParent = node hH b (Nat.unpair r).1 := by
  rw [Stage.scheduledParent, stages_log_length]
  exact node_stable hH b _ _ (Nat.unpair_left_le r)

theorem stage_parameter (r : ℕ) : (stages hH b r).parameter = (Nat.unpair r).2 + 1 := by
  simp [Stage.parameter]

theorem node_succ (r : ℕ) : node hH b (r + 1) =
    (stages hH b r).scheduledParent.append r (chunkAt hH b r).block
      (chunkAt hH b r).cursor (chunkAt hH b r).expansion.legal := by
  rw [node, stages_succ]
  change ((stages hH b r).nodes ++ [_]).getD (r + 1) Node.initial = _
  rw [List.getD_append_right _ _ _ _ (by simp)]
  simp [Node.append]

theorem node_succ_cursor (r : ℕ) :
    (node hH b (r + 1)).cursor = (chunkAt hH b r).cursor := by
  rw [node_succ]
  rfl

theorem node_succ_segments (r : ℕ) : (node hH b (r + 1)).segments =
    (node hH b (Nat.unpair r).1).segments ++ [(r, (chunkAt hH b r).block)] := by
  rw [node_succ]
  simp [Node.append, stage_parent]

theorem node_expansion (r : ℕ) :
    Expansion ((Nat.unpair r).2 + 1) (node hH b (Nat.unpair r).1).cursor
      (chunkAt hH b r).block (node hH b (r + 1)).cursor := by
  rw [node_succ_cursor]
  simpa only [stage_parameter, stage_parent] using (chunkAt hH b r).expansion

theorem node_end (r : ℕ) :
    (node hH b (r + 1)).cursor.terminal = true ∨
      (node hH b (r + 1)).cursor.relaxed = true :=
  (node_expansion hH b r).end

def child (p j : ℕ) : ℕ := Nat.pair p j + 1

theorem parent_lt_child (p j : ℕ) : p < child p j :=
  Nat.lt_succ_of_le (Nat.left_le_pair p j)

theorem child_strictMono (p : ℕ) : StrictMono (child p) := by
  intro i j hij
  exact Nat.add_lt_add_right (Nat.pair_lt_pair_right p hij) 1

theorem child_expansion (p j : ℕ) :
    Expansion (j + 1) (node hH b p).cursor (chunkAt hH b (Nat.pair p j)).block
      (node hH b (child p j)).cursor := by
  simpa [child] using node_expansion hH b (Nat.pair p j)

/-- Each unfinished parent gets a genuine macro for every parameter,
not a terminal dummy copy. -/
theorem child_extension (p j : ℕ) (hp : (node hH b p).cursor.terminal = false) :
    Extension (j + 1) (node hH b p).cursor (chunkAt hH b (Nat.pair p j)).block
      (node hH b (child p j)).cursor :=
  (child_expansion hH b p j).extension hp

theorem root_ranks (j : ℕ) :
    (node hH b (child 0 j)).cursor.relaxed = true ∧
      bodyRank (node hH b (child 0 j)).cursor = j ∧
      leafRank (node hH b (child 0 j)).cursor = j := by
  have hext := child_extension hH b 0 j rfl
  have hr := hext.initial_ranks (Nat.succ_pos j)
  exact ⟨hr.1, by omega, by omega⟩

theorem root_label_card (j : ℕ) : (node hH b (child 0 j)).cursor.rootLabel.card = j + 1 :=
  (child_extension hH b 0 j rfl).initial_root_card

#print axioms stages_valid
#print axioms node_stable
#print axioms child_extension
#print axioms root_ranks

end Erdos591.Positive.Game.Macro.Forest

end Erdos118.Reused591
