import ErdosProblems.Erdos591.GamePosition
import ErdosProblems.Erdos591.GameSupport
import ErdosProblems.Erdos591.GamePayoff

/-!
# Global invariants of legal histories

All stored numerical data stay in the input set and below the current
freshness bound. Each cursor remains a parsed increasing literal prefix,
and the two numerical supports remain disjoint.
-/

namespace Erdos591.Positive.Game

namespace Board

def Correct (b : Board) : Prop :=
  ∀ side, (b.get side).CursorInvariant ∧ (b.get side).coordinates.Pairwise (· < ·)

def DisjointWords (b : Board) : Prop := Disjoint b.left.support b.right.support

@[simp] theorem correct_initial : initial.Correct := by
  intro side
  cases side <;>
    exact ⟨LabeledWord.cursorInvariant_initial, by simp [initial, get, LabeledWord.initial]⟩

@[simp] theorem disjointWords_initial : initial.DisjointWords := by
  simp [DisjointWords, initial]

theorem update_correct {b : Board} (hb : b.Correct) (side : Bool) (w : LabeledWord)
    (hw : w.CursorInvariant ∧ w.coordinates.Pairwise (· < ·)) : (b.update side w).Correct := by
  intro s
  cases side <;> cases s
  · exact hw
  · exact hb true
  · exact hb false
  · exact hw

theorem update_disjointWords {b : Board} (hb : b.DisjointWords)
    (side : Bool) (w : LabeledWord) {u : Finset ℕ}
    (hw : w.support ⊆ (b.get side).support ∪ u) (hu : Disjoint u b.support) :
    (b.update side w).DisjointWords := by
  cases side with
  | false =>
      apply Finset.disjoint_left.mpr
      intro x hx hxright
      rcases Finset.mem_union.mp (hw hx) with hxleft | hxu
      · exact Finset.disjoint_left.mp hb hxleft hxright
      · exact Finset.disjoint_left.mp hu hxu (Finset.mem_union_right _ hxright)
  | true =>
      apply Finset.disjoint_left.mpr
      intro x hxleft hx
      rcases Finset.mem_union.mp (hw hx) with hxright | hxu
      · exact Finset.disjoint_left.mp hb hxleft hxright
      · exact Finset.disjoint_left.mp hu hxu (Finset.mem_union_left _ hxleft)

end Board

theorem Reply.correct {b b' : Board} {r : Request} {u : Finset ℕ}
    (h : Reply b r u b') (hb : b.Correct) (hpos : ∀ x ∈ u, 0 < x)
    (hsep : ∀ side, ∀ x ∈ (b.get side).coordinates, ∀ y ∈ u, x < y) : b'.Correct := by
  cases h with
  | finish side u w _ hrun =>
      apply Board.update_correct hb side w
      refine ⟨LabeledWord.finish_invariant (hb side).1 hrun, ?_⟩
      obtain ⟨_, hcoords, _⟩ := LabeledWord.finish_spec (hb side).1.1 hrun
      rw [hcoords]
      refine List.pairwise_append.mpr ⟨(hb side).2, (Finset.sortedLT_sort u).pairwise, ?_⟩
      intro x hx y hy
      exact hsep side x hx y (by simpa using hy)
  | advance side d u w hlegal hrun =>
      obtain ⟨w₁, hw₁, hcorrect⟩ := Advance.run_invariant ⟨b.get side, hlegal.1⟩ d
        (u.sort (· ≤ ·)) (.remainder w) (hb side).1 hlegal
        (Finset.sortedLT_sort u).pairwise (fun x hx => hpos x (by simpa using hx)) hrun
      have heq₁ : w = w₁ := Advance.State.remainder.inj hw₁
      subst w₁
      obtain ⟨w₂, hw₂, hinc⟩ := Advance.run_increasing ⟨b.get side, hlegal.1⟩ d
        (u.sort (· ≤ ·)) (.remainder w) (hb side).2 (Finset.sortedLT_sort u).pairwise
        (fun x hx y hy => hsep side x hx y (by simpa using hy)) hrun
      have heq₂ : w = w₂ := Advance.State.remainder.inj hw₂
      subst w₂
      exact Board.update_correct hb side w ⟨hcorrect, hinc⟩

namespace Position

/-- Every numerical value in either word or any of its labels is an
input-set member, positive, and at most the current freshness bound. -/
def StoredWithin (N : Set ℕ) (p : Position) : Prop :=
  ∀ x ∈ p.board.support, x ∈ N ∧ 0 < x ∧ x ≤ p.bound

@[simp] theorem storedWithin_initial (N : Set ℕ) : StoredWithin N initial := by
  simp [StoredWithin, initial, Board.support, Board.initial]

theorem Next.storedWithin {N : Set ℕ} {p q : Position} (h : Next N q p)
    (hp : StoredWithin N p) : StoredWithin N q := by
  have hbound := h.bound_le
  cases h with
  | request p mode r _ _ _ _ => exact hp
  | reply p r u b _ hr huN hfresh =>
      intro x hx
      rcases Finset.mem_union.mp (hr.support_subset hx) with hxold | hxu
      · exact ⟨(hp x hxold).1, (hp x hxold).2.1, (hp x hxold).2.2.trans hbound⟩
      · exact ⟨huN hxu, (Nat.zero_le p.bound).trans_lt (hfresh x hxu), Finset.le_sup (f := id) hxu⟩

theorem Next.correct {N : Set ℕ} {p q : Position} (h : Next N q p)
    (hstore : StoredWithin N p) (hp : p.board.Correct) : q.board.Correct := by
  cases h with
  | request _ _ _ _ _ _ _ => exact hp
  | reply p r u b _ hr _ hfresh =>
      apply hr.correct hp (fun x hx => (Nat.zero_le p.bound).trans_lt (hfresh x hx))
      intro side x hx y hy
      have hxs : x ∈ p.board.support := p.board.get_support_subset side
        (LabeledWord.coordinate_mem_support hx)
      exact (hstore x hxs).2.2.trans_lt (hfresh y hy)

theorem Next.disjointWords {N : Set ℕ} {p q : Position} (h : Next N q p)
    (hstore : StoredWithin N p) (hp : p.board.DisjointWords) : q.board.DisjointWords := by
  cases h with
  | request _ _ _ _ _ _ _ => exact hp
  | reply p r u b _ hr _ hfresh =>
      obtain ⟨w, rfl, hw⟩ := hr.word_support
      apply Board.update_disjointWords hp r.side w hw
      apply Finset.disjoint_left.mpr
      intro x hxu hxold
      exact (not_lt_of_ge (hstore x hxold).2.2) (hfresh x hxu)

def DataInvariant (N : Set ℕ) (p : Position) : Prop :=
  StoredWithin N p ∧ p.board.Correct ∧ p.board.DisjointWords

@[simp] theorem dataInvariant_initial (N : Set ℕ) : DataInvariant N initial :=
  ⟨storedWithin_initial N, Board.correct_initial, Board.disjointWords_initial⟩

theorem Next.dataInvariant {N : Set ℕ} {p q : Position} (h : Next N q p)
    (hp : DataInvariant N p) : DataInvariant N q :=
  ⟨h.storedWithin hp.1, h.correct hp.1 hp.2.1, h.disjointWords hp.1 hp.2.2⟩

theorem history_dataInvariant {N : Set ℕ} (h : LegalHistory N) : DataInvariant N h.position :=
  h.invariant (DataInvariant N) (dataInvariant_initial N) fun _ _ hn hp => hn.dataInvariant hp

/-- Whenever both words are complete, they decode to actual vertices
of the exact carrier and have disjoint coordinate supports. -/
theorem history_terminal_vertices {N : Set ℕ} (h : LegalHistory N)
    (hdone : Concrete.done h.position.board = true) :
    ∃ s t : Erdos591.Negative.Exact.G,
      Erdos591.Negative.Exact.word s.val = h.position.board.left.coordinates ∧
      Erdos591.Negative.Exact.word t.val = h.position.board.right.coordinates ∧
      Disjoint (Erdos591.Negative.Exact.word s.val).toFinset
        (Erdos591.Negative.Exact.word t.val).toFinset := by
  have hdata := history_dataInvariant h
  have hleft := hdata.2.1 false
  have hright := hdata.2.1 true
  have hterms : h.position.board.left.terminal = true ∧
      h.position.board.right.terminal = true := by simpa [Concrete.done] using hdone
  obtain ⟨s, hs⟩ := LabeledWord.terminal_good hleft.1.1 hleft.2 hterms.1
  obtain ⟨t, ht⟩ := LabeledWord.terminal_good hright.1.1 hright.2 hterms.2
  refine ⟨s, t, hs, ht, ?_⟩
  rw [hs, ht]
  apply Finset.disjoint_left.mpr
  intro x hx hy
  exact Finset.disjoint_left.mp hdata.2.2
    (LabeledWord.coordinate_mem_support (List.mem_toFinset.mp hx))
    (LabeledWord.coordinate_mem_support (List.mem_toFinset.mp hy))

#print axioms history_dataInvariant
#print axioms history_terminal_vertices

end Position

end Erdos591.Positive.Game
