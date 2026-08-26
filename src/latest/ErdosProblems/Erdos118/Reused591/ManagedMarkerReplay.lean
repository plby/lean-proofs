import ErdosProblems.Erdos118.Reused591.ManagedReach
import ErdosProblems.Erdos118.Reused591.NextMarkerReplay
import ErdosProblems.Erdos118.Reused591.FollowInputs

namespace Erdos118.Reused591

/-!
# Submit an old next-marker response after a managed fine continuation

A previously constructed fresh prefix is retained from a virtual fine
cursor. Continue the actual fine history on a fresh subpool until the
shared body marker, preserving its managed opposite word. Concatenating
the prefix with this run is exactly the older pending response.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact
open Relay

theorem winning_managed_marker_replay_from_prefix {N H J : Set ℕ}
    (hHN : H ⊆ N) (hJH : J ⊆ H) (hJ : J.Infinite) (blue : SimpleGraph G)
    {b : Concrete.Hist N → ℕ} {σ : (exactGame N blue).ArchitectStrategy}
    (fine old : Concrete.Hist N) (hwin : (exactGame N blue).ArchitectWins J b σ fine)
    (s t : Bool) {i : ℕ} (hp : old.position.pending = some ⟨t, .advance 0⟩)
    {anchor : LabeledWord} {frontAtoms : List (Finset ℕ × ℕ)}
    (hsame : LabeledWord.SameStructure (old.position.board.get t) anchor)
    (hprefix : LabeledWord.LegalRun anchor frontAtoms (fine.position.board.get s))
    (hprefixPool : ∀ a ∈ frontAtoms, a.2 ∈ H ∧ max old.position.bound (b old) < a.2)
    (hJfresh : ∀ x ∈ J, max old.position.bound (b old) < x)
    (hrel : (old.position.board.get t).relaxed = true)
    (hn : (old.position.board.get t).NoLeafPending)
    (hcoarse : LabeledWord.BeforeBody i (old.position.board.get t))
    (hnext : ∀ k ∈ (old.position.board.get t).rootLabel,
      (old.position.board.get t).bodyLabels.length < k → i ≤ k)
    (hfine : LabeledWord.BeforeBody i (fine.position.board.get s))
    {targetSide mode : Bool} {other : LabeledWord} (origin : Concrete.Hist N)
    (hmanaged : ∃ M : Managed N J blue b σ targetSide mode other (fine.position.board.get (!s)),
      Relation.ReflTransGen ((exactGame N blue).FollowStep σ J b) origin M.target) :
    ∃ q v d, Relation.ReflTransGen ((exactGame N blue).FollowStep σ J b) fine q ∧
      (exactGame N blue).FollowStep σ H b old v ∧
      q.position.pending = some ⟨s, .advance d⟩ ∧ 0 < d ∧ v.position.pending = none ∧
      LabeledWord.SameStructure (v.position.board.get t) (q.position.board.get s) ∧
      (q.position.board.get s).markerEvent = true ∧ (v.position.board.get t).markerEvent = true ∧
      (q.position.board.get s).bodyLabels.length + 1 = i ∧
      v.position.board.get (!t) = old.position.board.get (!t) ∧
      ∃ M : Managed N J blue b σ targetSide mode other (q.position.board.get (!s)),
        Relation.ReflTransGen ((exactGame N blue).FollowStep σ J b) origin M.target := by
  have hstartOld := LabeledWord.relaxed_ne_start
    ((Position.history_dataInvariant old).2.1 t).1 hrel
  have hstartAnchor : anchor.parser ≠ .start :=
    fun he => hstartOld (hsame.parser_eq.trans he)
  obtain ⟨q, d, hpath, hqpend, hd, hm, hiq, hMq⟩ :=
    managed_reach_body_marker_from (hJH.trans hHN) hJ blue hwin s i
      (hprefix.parser_ne_start hstartAnchor) hfine origin hmanaged
  obtain ⟨as, has, hpool⟩ := follow_word_inputs hpath 0 (fun _ => Nat.zero_le _) s
  have hwhole := hprefix.append has
  have hinc : ((frontAtoms ++ as).map Prod.snd).Pairwise (· < ·) := by
    have hqinc := ((Position.history_dataInvariant q).2.1 s).2
    rw [LabeledWord.runAtoms_coordinates hwhole.run] at hqinc
    exact (List.pairwise_append.mp hqinc).2.1
  have hwholePool : ∀ a ∈ frontAtoms ++ as,
      a.2 ∈ H ∧ old.position.bound < a.2 ∧ b old < a.2 := by
    intro a ha
    have hf : a.2 ∈ H ∧ max old.position.bound (b old) < a.2 := by
      rcases List.mem_append.mp ha with ha | ha
      · exact hprefixPool a ha
      · exact ⟨hJH (hpool a ha).1, hJfresh a.2 (hpool a ha).1⟩
    exact ⟨hf.1, (le_max_left _ _).trans_lt hf.2, (le_max_right _ _).trans_lt hf.2⟩
  obtain ⟨v, hs, hvn, hshape, hvm, _hvi, hother⟩ :=
    Concrete.follow_next_marker hHN (payoff blue) σ old t hp hsame hrel hn hcoarse hnext
      hwhole.run hm hiq hinc hwholePool
  exact ⟨q, v, d, hpath, hs, hqpend, hd, hvn, hshape, hm, hvm, hiq, hother, hMq⟩

#print axioms winning_managed_marker_replay_from_prefix

end Erdos591.Positive.Game.Payoff

end Erdos118.Reused591
