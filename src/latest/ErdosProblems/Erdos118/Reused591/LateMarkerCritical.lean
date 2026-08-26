import ErdosProblems.Erdos118.Reused591.MarkerOrder
import ErdosProblems.Erdos118.Reused591.PendingOpposite
import ErdosProblems.Erdos118.Reused591.NextMarkerEndpoint
import ErdosProblems.Erdos118.Reused591.RootGluingHistory

namespace Erdos118.Reused591

/-!
# The nonlast critical opposite leaf in the late-marker case

Test continuations identify the unchanged second word before the first
word's last-body marker is chosen. Its current body is the last selected
one, but its current selected leaf is not last. These are observations
about the original history, not commitments of the test coordinates.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact

theorem winning_late_last_marker_other_nonlast {N H : Set ℕ}
    (hHN : H ⊆ N) (hH : H.Infinite) (blue : SimpleGraph G)
    {b : Concrete.Hist N → ℕ} {σ : (exactGame N blue).ArchitectStrategy}
    (origin : Concrete.Hist N) {p : Concrete.Hist N}
    (hwin : (exactGame N blue).ArchitectWins H b σ p)
    (hfrom : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin p)
    (hall : ∀ z w, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin z →
      (exactGame N blue).kind z = .terminal w → lateFirstMarkerColor z = true)
    {d : ℕ} (hd : 2 ≤ d) (hp : p.position.pending = some ⟨false, .advance d⟩)
    (hm : p.position.board.left.markerEvent = true)
    (hroot : ∀ k ∈ p.position.board.left.rootLabel,
      k ≤ p.position.board.left.bodyLabels.length + 1)
    (hrelT : p.position.board.right.relaxed = true) :
    p.position.board.right.lastSelectedBody = p.position.board.right.bodyLabels.length ∧
      (∃ j ∈ p.position.board.right.currentLabel, p.position.board.right.leafIndex < j) ∧
      2 ≤ p.position.board.right.currentLabel.card := by
  have hstartT := LabeledWord.relaxed_ne_start
    ((Position.history_dataInvariant p).2.1 true).1 hrelT
  have hremain := winning_large_body_other_pending hHN hH blue hwin false hd hp hm hstartT
  have hk : (exactGame N blue).kind p = .builder :=
    (Concrete.kind_builder_iff (payoff blue) p).mpr ⟨_, hp⟩
  obtain ⟨u, hu, huH, hub⟩ := (exactGame N blue).response_exists_above hHN hH p hk (b p)
  let q := Concrete.response p u
  have hs : (exactGame N blue).FollowStep σ H b p q :=
    FiniteResponseGame.FollowStep.builder (exactGame N blue) σ p u hk hu huH hub
  have hr := (Concrete.response_spec hu).reply_spec hp
  obtain ⟨hrel, hcount, _hmarker⟩ := hr.selected_marker_metadata
    ((Position.history_dataInvariant p).2.1 false).1 hm (by omega)
    (fun x hx => (Nat.zero_le _).trans_lt (hub x hx))
  change q.position.board.left.bodyLabels.length = p.position.board.left.bodyLabels.length + 1
    at hcount
  have hpath := Relation.ReflTransGen.single hs
  obtain ⟨as, has, _⟩ := follow_word_inputs hpath 0 (fun _ => Nat.zero_le _) false
  obtain ⟨r, hparse⟩ := LabeledWord.marker_blocks hm
  have hrootEq : q.position.board.left.rootLabel = p.position.board.left.rootLabel :=
    has.rootLabel_eq (by simp [Board.get, hparse])
  have hlast : q.position.board.left.lastSelectedBody =
      q.position.board.left.bodyLabels.length := by
    rw [LabeledWord.lastSelectedBody, hrootEq, hcount]
    exact LabeledWord.lastSelectedBody_of_marker hm hroot
  have hother : q.position.board.right = p.position.board.right := hr.other_eq
  have hnFuture : ∀ i ∈ p.position.board.right.rootLabel,
      i ≤ p.position.board.right.bodyLabels.length := by
    have hh := winning_late_marker_no_future_right hHN hH blue origin q
      (hwin.of_reachable (exactGame N blue) hpath) (hfrom.trans hpath) hall hrel hlast
      (by rw [hother]; exact hstartT)
    simpa only [hother] using hh
  have hsel := (of_decide_eq_true hrelT).2.1
  have hlastT : p.position.board.right.lastSelectedBody =
      p.position.board.right.bodyLabels.length :=
    le_antisymm (Finset.sup_le hnFuture) (Finset.le_sup (f := id) hsel)
  have hlater : ∃ j ∈ p.position.board.right.currentLabel,
      p.position.board.right.leafIndex < j := by
    rcases hremain with ⟨i, hi, hlt⟩ | ⟨_hsel, j, hj, hlt⟩
    · exact (not_lt_of_ge (hnFuture i hi) hlt).elim
    · exact ⟨j, hj, hlt⟩
  refine ⟨hlastT, hlater, ?_⟩
  obtain ⟨j, hj, hlt⟩ := hlater
  have hcur := (of_decide_eq_true hrelT).2.2
  by_contra hncard
  have heq := Finset.card_le_one.mp (show p.position.board.right.currentLabel.card ≤ 1 by omega)
    _ hcur j hj
  omega

theorem winning_before_late_last_other_nonlast {N H : Set ℕ}
    (hHN : H ⊆ N) (hH : H.Infinite) (blue : SimpleGraph G)
    {b : Concrete.Hist N → ℕ} {σ : (exactGame N blue).ArchitectStrategy}
    (origin : Concrete.Hist N) {p : Concrete.Hist N}
    (hwin : (exactGame N blue).ArchitectWins H b σ p)
    (hfrom : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin p)
    (hall : ∀ z w, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin z →
      (exactGame N blue).kind z = .terminal w → lateFirstMarkerColor z = true)
    (hlarge : ∀ q d, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin q →
      q.position.pending = some ⟨false, .advance d⟩ → q.position.board.left.markerEvent = true →
      (∀ k ∈ q.position.board.left.rootLabel,
        k ≤ q.position.board.left.bodyLabels.length + 1) → 2 ≤ d)
    (hp : p.position.pending = some ⟨false, .advance 0⟩)
    (hrel : p.position.board.left.relaxed = true)
    (hn : p.position.board.left.NoLeafPending) {i : ℕ}
    (hi : LabeledWord.BeforeBody i p.position.board.left)
    (hnext : ∀ k ∈ p.position.board.left.rootLabel,
      p.position.board.left.bodyLabels.length < k → i ≤ k)
    (hrootLast : ∀ k ∈ p.position.board.left.rootLabel, k ≤ i)
    (hrelT : p.position.board.right.relaxed = true) :
    p.position.board.right.lastSelectedBody = p.position.board.right.bodyLabels.length ∧
      (∃ j ∈ p.position.board.right.currentLabel, p.position.board.right.leafIndex < j) ∧
      2 ≤ p.position.board.right.currentLabel.card := by
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
    have hstart := LabeledWord.relaxed_ne_start hw hrel
    have hroots := has.rootLabel_eq hstart
    intro k hk
    have hk' := hrootLast k (hroots ▸ hk)
    rw [show q.position.board.left.bodyLabels.length + 1 = i from hend.2]
    exact hk'
  have hvm : v.position.board.left.markerEvent = true := by
    simpa only [hboard, Board.get] using hend.1
  have hrootv : ∀ k ∈ v.position.board.left.rootLabel,
      k ≤ v.position.board.left.bodyLabels.length + 1 := by simpa only [hboard] using hrootq
  have hd := hlarge v d (hfrom.trans hpv) hpend hvm hrootv
  have hother : q.position.board.right = p.position.board.right := hr.other_eq
  have hcritical := winning_late_last_marker_other_nonlast hHN hH blue origin
    (hwin.of_reachable (exactGame N blue) hpv) (hfrom.trans hpv) hall hd hpend hvm hrootv
    (by simpa only [hboard, hother] using hrelT)
  simpa only [hboard, hother] using hcritical

#print axioms winning_late_last_marker_other_nonlast
#print axioms winning_before_late_last_other_nonlast

end Erdos591.Positive.Game.Payoff

end Erdos118.Reused591
