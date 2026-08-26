import ErdosProblems.Erdos591.NextLeafReplay
import ErdosProblems.Erdos591.ReachSelectedLeaf

/-!
# Reaching a fine selected leaf and submitting its delayed coarse reply

Impose one extra finite numerical bound before continuing the fine play.
Stop exactly at its prescribed selected leaf, retaining all new inputs
of both words above that bound. The selected coordinate continuation is
then submitted as the older next-selected-leaf advance response.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact

theorem winning_pending_leaf_advance_zero {N H : Set ℕ} (hHN : H ⊆ N) (hH : H.Infinite)
    (blue : SimpleGraph G) {b : Concrete.Hist N → ℕ}
    {σ : (exactGame N blue).ArchitectStrategy} {p : Concrete.Hist N}
    (hwin : (exactGame N blue).ArchitectWins H b σ p) {r : Request}
    (hp : p.position.pending = some r) (side : Bool) (hside : r.side = side) {j : ℕ}
    (hs : LabeledWord.UpToLeaf j (p.position.board.get side))
    (hlt : (p.position.board.get side).leafIndex < j) : r = ⟨side, .advance 0⟩ := by
  cases r with
  | mk s command =>
      have hse : s = side := hside
      subst s
      cases command with
      | finish =>
          exact ((winning_pending_finish_not_pending hHN hH blue hwin hp rfl)
            (Or.inr ⟨hs.selected, j, hs.mem, hlt⟩)).elim
      | advance d =>
          have hlegal : (p.position.board.get side).AllowedSize d :=
            (Position.history_controlInvariant p).2 _ hp
          obtain ⟨a, k, hparse⟩ := hs.parser_leaves ((Position.history_dataInvariant p).2.1 side).1
          have hd : d = 0 := by
            rcases hlegal.2 with hd | hstart | hmarker
            · exact hd
            · simp [hparse] at hstart
            · simp [LabeledWord.markerEvent, hparse] at hmarker
          simp [hd]

theorem winning_next_leaf_replay_fresh {N H : Set ℕ} (hHN : H ⊆ N) (hH : H.Infinite)
    (blue : SimpleGraph G) {b : Concrete.Hist N → ℕ}
    {σ : (exactGame N blue).ArchitectStrategy} (fine old : Concrete.Hist N)
    (hwin : (exactGame N blue).ArchitectWins H b σ fine) (s t : Bool) {j : ℕ}
    (hp : old.position.pending = some ⟨t, .advance 0⟩)
    (hsame : LabeledWord.SameStructure (old.position.board.get t) (fine.position.board.get s))
    (hcoarse : LabeledWord.UpToLeaf j (old.position.board.get t))
    (hstrict : (old.position.board.get t).leafIndex < j)
    (hnext : ∀ k ∈ (old.position.board.get t).currentLabel,
      (old.position.board.get t).leafIndex < k → j ≤ k)
    (hfine : LabeledWord.UpToLeaf j (fine.position.board.get s))
    (B : ℕ) (hB : max old.position.bound (b old) ≤ B) :
    ∃ q v, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) fine q ∧
      (exactGame N blue).FollowStep σ H b old v ∧
      q.position.pending = none ∧ v.position.pending = none ∧
      LabeledWord.SameStructure (v.position.board.get t) (q.position.board.get s) ∧
      (q.position.board.get s).relaxed = true ∧ (v.position.board.get t).relaxed = true ∧
      (q.position.board.get s).leafIndex = j ∧
      v.position.board.get (!t) = old.position.board.get (!t) ∧
      (∀ side, ∃ as, LabeledWord.LegalRun (fine.position.board.get side) as
        (q.position.board.get side) ∧ ∀ a ∈ as, a.2 ∈ H ∧ B < a.2) ∧
      (q.position.board.get s).bodyLabels = (fine.position.board.get s).bodyLabels ∧
      (q.position.board.get s).bodyMarker = (fine.position.board.get s).bodyMarker ∧
      ∀ y ∈ (q.position.board.get (!s)).coordinates,
        y ≤ (q.position.board.get s).coordinates.getLastD 0 := by
  let b' : Concrete.Hist N → ℕ := fun p => max (b p) B
  have hwin' := hwin.mono (exactGame N blue) (Set.Subset.refl H)
    (fun p => le_max_left (b p) B)
  have hfineStrict : (fine.position.board.get s).leafIndex < j := hsame.leaf_eq ▸ hstrict
  obtain ⟨q, hpath, hn, hr, hi, hlabels, hmarker, hsep⟩ :=
    winning_reach_selected_leaf_fresh hHN hH blue (b := b') hwin' s j hfine hfineStrict
  have hinputs := follow_word_inputs hpath B (fun p => le_max_right (b p) B)
  obtain ⟨as, has, hpool⟩ := hinputs s
  have hinc : (as.map Prod.snd).Pairwise (· < ·) := by
    have hqinc := ((Position.history_dataInvariant q).2.1 s).2
    rw [LabeledWord.runAtoms_coordinates has.run] at hqinc
    exact (List.pairwise_append.mp hqinc).2.1
  obtain ⟨v, hs, hvn, hshape, hvr, _hbody, hother⟩ := Concrete.follow_next_leaf hHN (payoff blue)
    σ old t hp hsame hcoarse hstrict hnext has.run hi (congrArg List.length hlabels) hmarker hinc
    (fun a ha => ⟨(hpool a ha).1, ((le_max_left _ _).trans hB).trans_lt (hpool a ha).2,
      ((le_max_right _ _).trans hB).trans_lt (hpool a ha).2⟩)
  have horiginal : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) fine q :=
    Relation.ReflTransGen.mono (fun _ _ hs =>
      FiniteResponseGame.FollowStep.mono (exactGame N blue) (Set.Subset.refl H)
        (fun p => le_max_left (b p) B) hs) _ _ hpath
  exact ⟨q, v, horiginal, hs, hn, hvn, hshape, hr, hvr, hi, hother, hinputs,
    hlabels, hmarker, hsep⟩

theorem winning_next_leaf_replay {N H : Set ℕ} (hHN : H ⊆ N) (hH : H.Infinite)
    (blue : SimpleGraph G) {b : Concrete.Hist N → ℕ}
    {σ : (exactGame N blue).ArchitectStrategy} (fine old : Concrete.Hist N)
    (hwin : (exactGame N blue).ArchitectWins H b σ fine) (s t : Bool) {j : ℕ}
    (hp : old.position.pending = some ⟨t, .advance 0⟩)
    (hsame : LabeledWord.SameStructure (old.position.board.get t) (fine.position.board.get s))
    (hcoarse : LabeledWord.UpToLeaf j (old.position.board.get t))
    (hstrict : (old.position.board.get t).leafIndex < j)
    (hnext : ∀ k ∈ (old.position.board.get t).currentLabel,
      (old.position.board.get t).leafIndex < k → j ≤ k)
    (hfine : LabeledWord.UpToLeaf j (fine.position.board.get s))
    (B : ℕ) (hB : max old.position.bound (b old) ≤ B) :
    ∃ q v, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) fine q ∧
      (exactGame N blue).FollowStep σ H b old v ∧
      q.position.pending = none ∧ v.position.pending = none ∧
      LabeledWord.SameStructure (v.position.board.get t) (q.position.board.get s) ∧
      (q.position.board.get s).relaxed = true ∧ (v.position.board.get t).relaxed = true ∧
      (q.position.board.get s).leafIndex = j ∧
      v.position.board.get (!t) = old.position.board.get (!t) ∧
      ∀ side, ∃ as, LabeledWord.LegalRun (fine.position.board.get side) as
        (q.position.board.get side) ∧ ∀ a ∈ as, a.2 ∈ H ∧ B < a.2 := by
  obtain ⟨q, v, hq, hv, hqn, hvn, he, hqr, hvr, hi, ho, hruns, _⟩ :=
    winning_next_leaf_replay_fresh hHN hH blue fine old hwin s t hp hsame hcoarse
      hstrict hnext hfine B hB
  exact ⟨q, v, hq, hv, hqn, hvn, he, hqr, hvr, hi, ho, hruns⟩

#print axioms winning_pending_leaf_advance_zero
#print axioms winning_next_leaf_replay
#print axioms winning_next_leaf_replay_fresh

end Erdos591.Positive.Game.Payoff
