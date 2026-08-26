import ErdosProblems.Erdos118.Reused591.NextMarkerEndpoint
import ErdosProblems.Erdos118.Reused591.NextMarkerReplay
import ErdosProblems.Erdos118.Reused591.RootGluingHistory

namespace Erdos118.Reused591

/-!
# Paired next-marker requests with stationary opposite words

One actual fine response extends the retained virtual prefix. Its
coordinate run is replayed as the older pending response. Both
histories then request positive body labels at the common marker.
Neither response nor either architect request moves the opposite word.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact

theorem paired_next_marker_requests {N H J : Set ℕ}
    (hHN : H ⊆ N) (hH : H.Infinite) (hJH : J ⊆ H) (hJ : J.Infinite)
    (blue : SimpleGraph G) {b : Concrete.Hist N → ℕ}
    {σ : (exactGame N blue).ArchitectStrategy} (old fine : Concrete.Hist N)
    (hwinOld : (exactGame N blue).ArchitectWins H b σ old)
    (hwinFine : (exactGame N blue).ArchitectWins J b σ fine) (s t : Bool) {i : ℕ}
    (hpOld : old.position.pending = some ⟨s, .advance 0⟩)
    (hpFine : fine.position.pending = some ⟨t, .advance 0⟩)
    {anchor : LabeledWord} {frontAtoms : List (Finset ℕ × ℕ)}
    (hsame : LabeledWord.SameStructure (old.position.board.get s) anchor)
    (hfront : LabeledWord.LegalRun anchor frontAtoms (fine.position.board.get t))
    (hfrontPool : ∀ a ∈ frontAtoms, a.2 ∈ H ∧ max old.position.bound (b old) < a.2)
    (hJfresh : ∀ x ∈ J, max old.position.bound (b old) < x)
    (hrelOld : (old.position.board.get s).relaxed = true)
    (hnoOld : (old.position.board.get s).NoLeafPending)
    (hbeforeOld : LabeledWord.BeforeBody i (old.position.board.get s))
    (hnextOld : ∀ k ∈ (old.position.board.get s).rootLabel,
      (old.position.board.get s).bodyLabels.length < k → i ≤ k)
    (hrelFine : (fine.position.board.get t).relaxed = true)
    (hnoFine : (fine.position.board.get t).NoLeafPending)
    (hbeforeFine : LabeledWord.BeforeBody i (fine.position.board.get t))
    (hnextFine : ∀ k ∈ (fine.position.board.get t).rootLabel,
      (fine.position.board.get t).bodyLabels.length < k → i ≤ k) :
    ∃ q v a c, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) old q ∧
      Relation.ReflTransGen ((exactGame N blue).FollowStep σ J b) fine v ∧
      q.position.pending = some ⟨s, .advance a⟩ ∧
      v.position.pending = some ⟨t, .advance c⟩ ∧ 0 < a ∧ 0 < c ∧
      LabeledWord.SameStructure (q.position.board.get s) (v.position.board.get t) ∧
      (q.position.board.get s).markerEvent = true ∧
      (v.position.board.get t).markerEvent = true ∧
      (q.position.board.get s).bodyLabels.length + 1 = i ∧
      (v.position.board.get t).bodyLabels.length + 1 = i ∧
      (q.position.board.get s).rootLabel = (old.position.board.get s).rootLabel ∧
      (v.position.board.get t).rootLabel = (fine.position.board.get t).rootLabel ∧
      q.position.board.get (!s) = old.position.board.get (!s) ∧
      v.position.board.get (!t) = fine.position.board.get (!t) := by
  have hk : (exactGame N blue).kind fine = .builder :=
    (Concrete.kind_builder_iff (payoff blue) fine).mpr ⟨_, hpFine⟩
  obtain ⟨u, hu, huJ, hub⟩ :=
    (exactGame N blue).response_exists_above (hJH.trans hHN) hJ fine hk (b fine)
  let v₀ := Concrete.response fine u
  have hstepFine : (exactGame N blue).FollowStep σ J b fine v₀ :=
    FiniteResponseGame.FollowStep.builder (exactGame N blue) σ fine u hk hu huJ hub
  have hr := (Concrete.response_spec hu).reply_spec hpFine
  obtain ⟨hmarkerFine, hindexFine⟩ := hr.next_marker_endpoint
    ((Position.history_dataInvariant fine).2.1 t).1 hrelFine hnoFine hbeforeFine hnextFine
  obtain ⟨newAtoms, hnew, hnewMem⟩ := hr.legal_run
    (fun x hx => (Nat.zero_le _).trans_lt (hub x hx)) t
  have hwhole := hfront.append hnew
  have hinc : ((frontAtoms ++ newAtoms).map Prod.snd).Pairwise (· < ·) := by
    have hi := ((Position.history_dataInvariant v₀).2.1 t).2
    rw [LabeledWord.runAtoms_coordinates hwhole.run] at hi
    exact (List.pairwise_append.mp hi).2.1
  have hpool : ∀ a ∈ frontAtoms ++ newAtoms,
      a.2 ∈ H ∧ old.position.bound < a.2 ∧ b old < a.2 := by
    intro a ha
    have hf : a.2 ∈ H ∧ max old.position.bound (b old) < a.2 := by
      rcases List.mem_append.mp ha with ha | ha
      · exact hfrontPool a ha
      · exact ⟨hJH (huJ (hnewMem a ha)), hJfresh a.2 (huJ (hnewMem a ha))⟩
    exact ⟨hf.1, (le_max_left _ _).trans_lt hf.2, (le_max_right _ _).trans_lt hf.2⟩
  obtain ⟨q₀, hstepOld, hnOld, hshape, hmOld, hiOld, hotherOld⟩ :=
    Concrete.follow_next_marker hHN (payoff blue) σ old s hpOld hsame hrelOld hnoOld
      hbeforeOld hnextOld hwhole.run hmarkerFine hindexFine hinc hpool
  have hnFine := (History.Next.position_next
    (FiniteResponseGame.FollowStep.next (exactGame N blue) hstepFine)).no_pending_after_reply hpFine
  obtain ⟨q, a, hrequestOld, hboardOld, hpq, ha⟩ := winning_request_at_marker hHN hH blue
    (hwinOld.of_reachable (exactGame N blue) (.single hstepOld)) s hnOld hmOld
  obtain ⟨v, c, hrequestFine, hboardFine, hpv, hc⟩ :=
    winning_request_at_marker (hJH.trans hHN) hJ blue
      (hwinFine.of_reachable (exactGame N blue) (.single hstepFine)) t hnFine hmarkerFine
  have hpathOld := (Relation.ReflTransGen.single hstepOld).tail hrequestOld
  have hpathFine := (Relation.ReflTransGen.single hstepFine).tail hrequestFine
  obtain ⟨oldAtoms, hOldRun, _⟩ :=
    (History.reachable_word_extension (follow_history_path hpathOld)).2 s
  obtain ⟨fineAtoms, hFineRun, _⟩ :=
    (History.reachable_word_extension (follow_history_path hpathFine)).2 t
  have hrootOld := hOldRun.rootLabel_eq
    (LabeledWord.relaxed_ne_start ((Position.history_dataInvariant old).2.1 s).1 hrelOld)
  have hrootFine := hFineRun.rootLabel_eq
    (LabeledWord.relaxed_ne_start ((Position.history_dataInvariant fine).2.1 t).1 hrelFine)
  exact ⟨q, v, a, c, hpathOld, hpathFine, hpq, hpv, ha, hc,
    by simpa [hboardOld, hboardFine] using hshape,
    by simpa [hboardOld] using hmOld, by simpa [hboardFine] using hmarkerFine,
    by simpa [hboardOld] using hiOld, by simpa [hboardFine] using hindexFine,
    hrootOld, hrootFine, by simpa [hboardOld] using hotherOld,
    by simpa [hboardFine] using hr.other_eq⟩

#print axioms paired_next_marker_requests

end Erdos591.Positive.Game.Payoff

end Erdos118.Reused591
