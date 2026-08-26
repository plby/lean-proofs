import ErdosProblems.Erdos591.ReplyRuns

/-!
# Numerical separation immediately after an actual response

Every response reads a new coordinate above all old stored values.
The untouched word is therefore below the selected word's new last
coordinate. This is the precise handoff inequality, independent of
whether the reply stops at a marker, a selected leaf, or completion.
-/

namespace Erdos591.Positive.Game

theorem Reply.other_le_last {board last : Board} {r : Request} {u : Finset ℕ}
    (hr : Reply board r u last) (hpos : ∀ x ∈ u, 0 < x)
    (hinc : (last.get r.side).coordinates.Pairwise (· < ·))
    (hsep : ∀ y ∈ (board.get (!r.side)).coordinates, ∀ x ∈ u, y < x) :
    ∀ y ∈ (last.get (!r.side)).coordinates, y ≤ (last.get r.side).coordinates.getLastD 0 := by
  obtain ⟨n, hnu, xs, hc⟩ := hr.coordinates_extend_input hpos
  have hn : n ∈ (last.get r.side).coordinates := by rw [hc]; simp
  have hlast : n ≤ (last.get r.side).coordinates.getLastD 0 := by
    simpa only [List.getLastD_eq_getLast?,
      List.getLast?_eq_some_getLast (List.ne_nil_of_mem hn), Option.getD_some] using
      (hinc.imp Nat.le_of_lt).rel_getLast hn
  intro y hy
  rw [hr.other_eq] at hy
  exact (hsep y hy n hnu).le.trans hlast

theorem Position.Next.reply_separation {N : Set ℕ} {p q : Position}
    (h : Position.Next N q p) (hstore : Position.StoredWithin N p)
    (hcorrect : q.board.Correct) {r : Request} (hp : p.pending = some r) :
    ∀ y ∈ (q.board.get (!r.side)).coordinates,
      y ≤ (q.board.get r.side).coordinates.getLastD 0 := by
  cases h with
  | request p mode s ht _ _ _ => simp [hp] at ht
  | reply p s u board hs hr _ hf =>
      have heq : s = r := Option.some.inj (hs.symm.trans hp)
      subst r
      apply hr.other_le_last (fun x hx => (Nat.zero_le p.bound).trans_lt (hf x hx))
        (hcorrect s.side).2
      intro y hy x hx
      have hyb := (hstore y (p.board.get_support_subset (!s.side)
        (LabeledWord.coordinate_mem_support hy))).2.2
      exact hyb.trans_lt (hf x hx)

theorem History.Next.reply_separation {N : Set ℕ} {p q : Concrete.Hist N}
    (h : History.Next q p) {r : Request} (hp : p.position.pending = some r) :
    ∀ y ∈ (q.position.board.get (!r.side)).coordinates,
      y ≤ (q.position.board.get r.side).coordinates.getLastD 0 :=
  (History.Next.position_next h).reply_separation (Position.history_dataInvariant p).1
    (Position.history_dataInvariant q).2.1 hp

#print axioms History.Next.reply_separation

end Erdos591.Positive.Game
