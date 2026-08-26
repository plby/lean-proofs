import ErdosProblems.Erdos591.NextMarkerReplay
import ErdosProblems.Erdos591.ReachBodyMarker
import ErdosProblems.Erdos591.FollowInputs
import ErdosProblems.Erdos591.FinishRestriction

/-!
# Reach a fine body marker and submit the older next-marker response

The extra numerical threshold is imposed before continuing the fine
history. Both words' new coordinate runs retain that bound, allowing
the other word's eventual complete response to be replayed later.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact

theorem winning_pending_root_advance_zero {N H : Set ℕ} (hHN : H ⊆ N) (hH : H.Infinite)
    (blue : SimpleGraph G) {b : Concrete.Hist N → ℕ}
    {σ : (exactGame N blue).ArchitectStrategy} {p : Concrete.Hist N}
    (hwin : (exactGame N blue).ArchitectWins H b σ p) {r : Request}
    (hp : p.position.pending = some r) (side : Bool) (hside : r.side = side)
    (hrel : (p.position.board.get side).relaxed = true) {i : ℕ}
    (hi : LabeledWord.BeforeBody i (p.position.board.get side)) : r = ⟨side, .advance 0⟩ := by
  cases r with
  | mk s command =>
      have hse : s = side := hside
      subst s
      cases command with
      | finish =>
          exact ((winning_pending_finish_not_pending hHN hH blue hwin hp rfl)
            (Or.inl ⟨i, hi⟩)).elim
      | advance d =>
          have hlegal : (p.position.board.get side).AllowedSize d :=
            (Position.history_controlInvariant p).2 _ hp
          have hdata := of_decide_eq_true hrel
          have hleaf : LabeledWord.UpToLeaf (p.position.board.get side).leafIndex
              (p.position.board.get side) := ⟨hdata.2.1, hdata.2.2, le_rfl⟩
          obtain ⟨a, k, hparse⟩ := hleaf.parser_leaves ((Position.history_dataInvariant p).2.1 side).1
          have hd : d = 0 := by
            rcases hlegal.2 with hd | hstart | hmarker
            · exact hd
            · simp [hparse] at hstart
            · simp [LabeledWord.markerEvent, hparse] at hmarker
          simp [hd]

theorem winning_next_marker_replay {N H : Set ℕ} (hHN : H ⊆ N) (hH : H.Infinite)
    (blue : SimpleGraph G) {b : Concrete.Hist N → ℕ}
    {σ : (exactGame N blue).ArchitectStrategy} (fine old : Concrete.Hist N)
    (hwin : (exactGame N blue).ArchitectWins H b σ fine) (s t : Bool) {i : ℕ}
    (hp : old.position.pending = some ⟨t, .advance 0⟩)
    (hsame : LabeledWord.SameStructure (old.position.board.get t) (fine.position.board.get s))
    (hrel : (old.position.board.get t).relaxed = true)
    (hn : (old.position.board.get t).NoLeafPending)
    (hcoarse : LabeledWord.BeforeBody i (old.position.board.get t))
    (hnext : ∀ k ∈ (old.position.board.get t).rootLabel,
      (old.position.board.get t).bodyLabels.length < k → i ≤ k)
    (hfine : LabeledWord.BeforeBody i (fine.position.board.get s))
    (B : ℕ) (hB : max old.position.bound (b old) ≤ B) :
    ∃ q v d, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) fine q ∧
      (exactGame N blue).FollowStep σ H b old v ∧
      q.position.pending = some ⟨s, .advance d⟩ ∧ 0 < d ∧ v.position.pending = none ∧
      LabeledWord.SameStructure (v.position.board.get t) (q.position.board.get s) ∧
      (q.position.board.get s).markerEvent = true ∧ (v.position.board.get t).markerEvent = true ∧
      (q.position.board.get s).bodyLabels.length + 1 = i ∧
      v.position.board.get (!t) = old.position.board.get (!t) ∧
      ∀ side, ∃ as, LabeledWord.LegalRun (fine.position.board.get side) as
        (q.position.board.get side) ∧ ∀ a ∈ as, a.2 ∈ H ∧ B < a.2 := by
  let b' : Concrete.Hist N → ℕ := fun p => max (b p) B
  have hwin' := hwin.mono (exactGame N blue) (Set.Subset.refl H)
    (fun p => le_max_left (b p) B)
  have hstart := LabeledWord.relaxed_ne_start ((Position.history_dataInvariant old).2.1 t).1 hrel
  have hstartFine : (fine.position.board.get s).parser ≠ .start :=
    fun he => hstart (hsame.parser_eq.trans he)
  obtain ⟨q, d, hpath, hpend, hd, hm, hidx⟩ := winning_reach_body_marker hHN hH blue
    (b := b') hwin' s i hstartFine hfine
  have hinputs := follow_word_inputs hpath B (fun p => le_max_right (b p) B)
  obtain ⟨as, has, hpool⟩ := hinputs s
  have hinc : (as.map Prod.snd).Pairwise (· < ·) := by
    have hqinc := ((Position.history_dataInvariant q).2.1 s).2
    rw [LabeledWord.runAtoms_coordinates has.run] at hqinc
    exact (List.pairwise_append.mp hqinc).2.1
  obtain ⟨v, hs, hvn, hshape, hvm, _hvidx, hother⟩ := Concrete.follow_next_marker hHN (payoff blue)
    σ old t hp hsame hrel hn hcoarse hnext has.run hm hidx hinc
    (fun a ha => ⟨(hpool a ha).1, ((le_max_left _ _).trans hB).trans_lt (hpool a ha).2,
      ((le_max_right _ _).trans hB).trans_lt (hpool a ha).2⟩)
  have horiginal : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) fine q :=
    Relation.ReflTransGen.mono (fun _ _ hs =>
      FiniteResponseGame.FollowStep.mono (exactGame N blue) (Set.Subset.refl H)
        (fun p => le_max_left (b p) B) hs) _ _ hpath
  exact ⟨q, v, d, horiginal, hs, hpend, hd, hvn, hshape, hm, hvm, hidx, hother, hinputs⟩

#print axioms winning_pending_root_advance_zero
#print axioms winning_next_marker_replay

end Erdos591.Positive.Game.Payoff
