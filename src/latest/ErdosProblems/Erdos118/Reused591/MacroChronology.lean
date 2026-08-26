import ErdosProblems.Erdos118.Reused591.MacroSchedule

namespace Erdos118.Reused591

/-!
# Chronological separation in the macro forest

Inputs of earlier construction blocks are strictly below every input
of a later nonempty block. Each branch inherits a genuinely increasing
input list from the one global log, and completed cursors decode to the
literal carrier used in the partition relation.
-/

namespace Erdos591.Positive.Game.Macro.Forest

variable {N H : Set ℕ} (hH : H.Infinite) (b : Concrete.Hist N → ℕ)

theorem stages_inputs_succ (r : ℕ) :
    (stages hH b (r + 1)).inputs = (stages hH b r).inputs ++ raw (chunkAt hH b r).block := by
  rw [stages_succ, Stage.inputs_append]

theorem stages_inputs_mono (r s : ℕ) (hrs : r ≤ s) :
    List.Sublist (stages hH b r).inputs (stages hH b s).inputs := by
  induction s, hrs using Nat.le_induction with
  | base => exact List.Sublist.refl _
  | succ s _ ih =>
      rw [stages_inputs_succ]
      exact ih.trans (List.sublist_append_left _ _)

theorem chunk_inputs_stage (r s : ℕ) (hrs : r < s) :
    List.Sublist (raw (chunkAt hH b r).block) (stages hH b s).inputs := by
  apply List.Sublist.trans _ (stages_inputs_mono hH b (r + 1) s hrs)
  rw [stages_inputs_succ]
  exact List.sublist_append_right _ _

theorem chunks_separated (r s : ℕ) (hrs : r < s) :
    ∀ x ∈ raw (chunkAt hH b r).block, ∀ y ∈ raw (chunkAt hH b s).block, x < y := by
  intro x hx y hy
  have hx' := (chunk_inputs_stage hH b r s hrs).subset hx
  exact (Finset.le_sup (f := id) (List.mem_toFinset.mpr hx')).trans_lt
    ((chunkAt hH b s).fresh y hy)

theorem node_mem_at (n r : ℕ) (hn : n ≤ r) : node hH b n ∈ (stages hH b r).nodes := by
  rw [← node_stable hH b n r hn]
  have hi : n < (stages hH b r).nodes.length := by simpa using Nat.lt_succ_of_le hn
  rw [List.getD_eq_getElem _ _ hi]
  exact List.getElem_mem hi

theorem node_segments_sublist (n r : ℕ) (hn : n ≤ r) :
    List.Sublist (node hH b n).segments (stages hH b r).log :=
  (stages_valid hH b r).branches _ (node_mem_at hH b n r hn)

theorem node_raw_sublist (n r : ℕ) (hn : n ≤ r) :
    List.Sublist (raw (node hH b n).atoms) (stages hH b r).inputs :=
  raw_sublist ((node_segments_sublist hH b n r hn).flatMap Prod.snd)

theorem node_inputs_increasing (n : ℕ) : (raw (node hH b n).atoms).Pairwise (· < ·) :=
  (stages_valid hH b n).increasing.sublist (node_raw_sublist hH b n n le_rfl)

theorem node_inputs_pool (n : ℕ) : ∀ x ∈ raw (node hH b n).atoms, x ∈ H := by
  intro x hx
  exact (stages_valid hH b n).pool x ((node_raw_sublist hH b n n le_rfl).subset hx)

theorem node_support_stage (n r : ℕ) (hn : n ≤ r) :
    (node hH b n).cursor.support ⊆ (stages hH b r).support := by
  apply (node hH b n).support.trans
  intro x hx
  exact List.mem_toFinset.mpr
    ((node_raw_sublist hH b n r hn).subset (List.mem_toFinset.mp hx))

theorem node_coordinates_sublist (n : ℕ) :
    List.Sublist (node hH b n).cursor.coordinates (raw (node hH b n).atoms) := by
  rw [(node hH b n).coordinates]
  simpa [raw, Atomic.tag, List.map_map, Function.comp_def] using
    Atomic.values_sublist_inputs (Atomic.tag false (node hH b n).atoms)

theorem node_coordinates_increasing (n : ℕ) :
    (node hH b n).cursor.coordinates.Pairwise (· < ·) :=
  (node_inputs_increasing hH b n).sublist (node_coordinates_sublist hH b n)

theorem terminal_node_vertex (n : ℕ) (hn : (node hH b n).cursor.terminal = true) :
    ∃ s : Erdos591.Negative.Exact.G,
      Erdos591.Negative.Exact.word s.val = (node hH b n).cursor.coordinates :=
  LabeledWord.terminal_good (node hH b n).invariant.1
    (node_coordinates_increasing hH b n) hn

noncomputable def firstAt (r : ℕ) : ℕ := ((chunkAt hH b r).block.headD (∅, 0)).2

theorem firstAt_mem (r : ℕ) (hr : (chunkAt hH b r).block ≠ []) :
    firstAt hH b r ∈ raw (chunkAt hH b r).block := by
  cases heq : (chunkAt hH b r).block with
  | nil => exact (hr heq).elim
  | cons a xs =>
      rw [firstAt, heq]
      exact List.mem_append_left _ (Atomic.Atom.value_mem ⟨false, a.1, a.2⟩)

/-- Different children are ordered by their first new *coordinate*,
not by a possibly discarded label value. -/
theorem child_first_strictMono (p : ℕ) (hp : (node hH b p).cursor.terminal = false) :
    StrictMono (fun j => firstAt hH b (Nat.pair p j)) := by
  intro i j hij
  exact chunks_separated hH b _ _ (Nat.pair_lt_pair_right p hij) _
    (firstAt_mem hH b _ (child_extension hH b p i hp).nonempty) _
    (firstAt_mem hH b _ (child_extension hH b p j hp).nonempty)

#print axioms chunks_separated
#print axioms terminal_node_vertex
#print axioms child_first_strictMono

end Erdos591.Positive.Game.Macro.Forest

end Erdos118.Reused591
