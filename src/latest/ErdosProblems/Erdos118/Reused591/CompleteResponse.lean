import ErdosProblems.Erdos118.Reused591.ZeroResponse

namespace Erdos118.Reused591

/-!
# Complete-word responses and their exact vertices

A complete response stores its actual finite input and accepted parser
run. Such responses exist on every infinite numerical tail. The same
response can be used at any initial cursor with a zero-size command.
-/

namespace Erdos591.Positive.Game

structure CompleteResponse where
  input : Finset ℕ
  cursor : LabeledWord
  run : LabeledWord.finishParser.run LabeledWord.initial (input.sort (· ≤ ·)) = some cursor

namespace CompleteResponse

theorem coordinates (s : CompleteResponse) : s.cursor.coordinates = s.input.sort (· ≤ ·) := by
  simpa [LabeledWord.initial] using
    (LabeledWord.finish_spec LabeledWord.cursorInvariant_initial.1 s.run).2.1

theorem terminal (s : CompleteResponse) : s.cursor.terminal = true :=
  LabeledWord.finishParser.run_stopped s.run

theorem vertex_exists (s : CompleteResponse) :
    ∃ v : Erdos591.Negative.Exact.G, Erdos591.Negative.Exact.word v.val = s.cursor.coordinates :=
  LabeledWord.finish_good LabeledWord.cursorInvariant_initial.1
    (by simp [LabeledWord.initial]) (Finset.sortedLT_sort s.input).pairwise
    (by simp [LabeledWord.initial]) s.run

noncomputable def vertex (s : CompleteResponse) : Erdos591.Negative.Exact.G :=
  s.vertex_exists.choose

theorem vertex_word (s : CompleteResponse) :
    Erdos591.Negative.Exact.word s.vertex.val = s.cursor.coordinates :=
  s.vertex_exists.choose_spec

theorem exists_above {H : Set ℕ} (hH : H.Infinite) (B : ℕ) :
    ∃ s : CompleteResponse, (↑s.input : Set ℕ) ⊆ H ∧ ∀ x ∈ s.input, B < x := by
  let M := H \ Set.Iic B
  have hM : M.Infinite := hH.sdiff (Set.finite_Iic B)
  obtain ⟨u, ⟨w, hw⟩, hu⟩ := LabeledWord.finish_exists LabeledWord.initial hM
  exact ⟨⟨u, w, hw⟩, fun x hx => (hu hx).1, fun x hx => lt_of_not_ge (hu hx).2⟩

theorem reply (s : CompleteResponse) (board : Board) (r : Request)
    (hinit : board.get r.side = LabeledWord.initial) (hsize : r.size = 0) :
    Reply board r s.input (board.update r.side s.cursor) := by
  apply (Reply.size_zero_iff_finish board r s.input _ (by simp [hinit, LabeledWord.initial])
    hsize).mpr
  apply Reply.finish r.side s.input s.cursor
  · simp [hinit, LabeledWord.terminal, LabeledWord.initial]
  · simpa [hinit] using s.run

#print axioms exists_above
#print axioms reply

end CompleteResponse

end Erdos591.Positive.Game

end Erdos118.Reused591
