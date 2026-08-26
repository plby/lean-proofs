import ErdosProblems.Erdos591.InsideSingletonBoundary
import ErdosProblems.Erdos591.NextMarkerEndpoint
import ErdosProblems.Erdos591.LastBodyUniformization

/-!
# Detect the critical opposite leaf before choosing the last body marker

A test size-zero response reaches the next selected marker, which is
last. Terminal uniformity forces its body request to have size one.
The singleton boundary then proves that the unchanged opposite word
was already exhausted before this test response was chosen.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact

theorem winning_before_singleton_last_other_exhausted {N H : Set ℕ}
    (hHN : H ⊆ N) (hH : H.Infinite) (blue : SimpleGraph G)
    {b : Concrete.Hist N → ℕ} {σ : (exactGame N blue).ArchitectStrategy}
    (origin : Concrete.Hist N) {p : Concrete.Hist N}
    (hwin : (exactGame N blue).ArchitectWins H b σ p)
    (hfrom : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin p)
    (hall : ∀ z w, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin z →
      (exactGame N blue).kind z = .terminal w → lastBodySingletonColor false z = true)
    (hmode : p.position.mode = some true)
    (hp : p.position.pending = some ⟨false, .advance 0⟩)
    (hrel : p.position.board.left.relaxed = true)
    (hn : p.position.board.left.NoLeafPending) {i : ℕ}
    (hi : LabeledWord.BeforeBody i p.position.board.left)
    (hnext : ∀ k ∈ p.position.board.left.rootLabel,
      p.position.board.left.bodyLabels.length < k → i ≤ k)
    (hrootLast : ∀ k ∈ p.position.board.left.rootLabel, k ≤ i)
    (hstartT : p.position.board.right.parser ≠ .start) :
    ¬ Macro.Pending p.position.board.right := by
  have hk : (exactGame N blue).kind p = .builder :=
    (Concrete.kind_builder_iff (payoff blue) p).mpr ⟨_, hp⟩
  obtain ⟨u, hu, huH, hub⟩ := (exactGame N blue).response_exists_above hHN hH p hk (b p)
  let q := Concrete.response p u
  have hs : (exactGame N blue).FollowStep σ H b p q :=
    FiniteResponseGame.FollowStep.builder (exactGame N blue) σ p u hk hu huH hub
  have hr := (Concrete.response_spec hu).reply_spec hp
  have hnextq := History.Next.position_next
    (FiniteResponseGame.FollowStep.next (exactGame N blue) hs)
  have hqnone : q.position.pending = none := hnextq.no_pending_after_reply hp
  have hw := ((Position.history_dataInvariant p).2.1 false).1
  have hend := hr.next_marker_endpoint hw hrel hn hi hnext
  have hqwin := hwin.of_reachable (exactGame N blue) (Relation.ReflTransGen.single hs)
  obtain ⟨v, d, hrequest, hboard, hpend, _hd⟩ :=
    winning_request_at_marker hHN hH blue hqwin false hqnone hend.1
  have hpv := (Relation.ReflTransGen.single hs).tail hrequest
  have hrootq : ∀ k ∈ q.position.board.left.rootLabel,
      k ≤ q.position.board.left.bodyLabels.length + 1 := by
    obtain ⟨as, has, _⟩ := hnextq.word_extension false
    have hstart : p.position.board.left.parser ≠ .start := LabeledWord.relaxed_ne_start hw hrel
    have hroot := has.rootLabel_eq hstart
    intro k hk
    have hk' := hrootLast k (hroot ▸ hk)
    rw [show q.position.board.left.bodyLabels.length + 1 = i from hend.2]
    exact hk'
  have hvm : v.position.board.left.markerEvent = true := by
    simpa only [hboard, Board.get] using hend.1
  have hrootv : ∀ k ∈ v.position.board.left.rootLabel,
      k ≤ v.position.board.left.bodyLabels.length + 1 := by simpa only [hboard] using hrootq
  have hsize := pending_last_body_observable hHN hH blue origin v false true
    (hfrom.trans hpv) hall hpend rfl hvm hrootv
  have hd : d = 1 := of_decide_eq_true hsize
  have hother : q.position.board.right = p.position.board.right := hr.other_eq
  have hlast := winning_singleton_last_other_exhausted hHN hH blue
    (hwin.of_reachable (exactGame N blue) hpv) (follow_mode_some hpv hmode)
    (by simpa only [hd] using hpend) hvm hrootv
    (by simpa only [hboard, hother] using hstartT)
  simpa only [hboard, hother] using hlast

#print axioms winning_before_singleton_last_other_exhausted

end Erdos591.Positive.Game.Payoff
