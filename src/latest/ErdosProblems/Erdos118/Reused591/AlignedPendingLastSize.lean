import ErdosProblems.Erdos118.Reused591.LastBodyPersistence
import ErdosProblems.Erdos118.Reused591.TerminalMarkerCounts

namespace Erdos118.Reused591

/-!
# The actual opposite last-body request has one fewer selection

At an aligned reachable right last-body request, the already read left
last-body label has cardinality one more than the requested size. A test
response and terminal extension recover the right slot exactly; no size
is assumed for a request that has not yet been issued.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact

theorem aligned_pending_right_last_size {N H : Set ℕ} (hHN : H ⊆ N) (hH : H.Infinite)
    (blue : SimpleGraph G) {b : Concrete.Hist N → ℕ}
    {σ : (exactGame N blue).ArchitectStrategy} (origin p : Concrete.Hist N)
    {a d : ℕ} (ha : 2 ≤ a)
    (hop : origin.position.pending = some ⟨false, .advance a⟩)
    (hboard : origin.position.board = Board.initial) (hmode : origin.position.mode = some true)
    (hwin : (exactGame N blue).ArchitectWins H b σ origin)
    (hfrom : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin p)
    (hall : ∀ z w, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin z →
      (exactGame N blue).kind z = .terminal w → alignedBodyCountColor z = true)
    (hp : p.position.pending = some ⟨true, .advance d⟩)
    (hm : p.position.board.right.markerEvent = true)
    (hrootR : ∀ i ∈ p.position.board.right.rootLabel,
      i ≤ p.position.board.right.bodyLabels.length + 1)
    (hrelL : p.position.board.left.relaxed = true)
    (hrootL : ∀ i ∈ p.position.board.left.rootLabel,
      i ≤ p.position.board.left.bodyLabels.length) :
    p.position.board.left.currentLabel.card = d + 1 := by
  have hk : (exactGame N blue).kind p = .builder :=
    (Concrete.kind_builder_iff (payoff blue) p).mpr ⟨_, hp⟩
  obtain ⟨u, hu, huH, hub⟩ := (exactGame N blue).response_exists_above hHN hH p hk (b p)
  have hs : (exactGame N blue).FollowStep σ H b p (Concrete.response p u) :=
    FiniteResponseGame.FollowStep.builder (exactGame N blue) σ p u hk hu huH hub
  obtain ⟨z, hzpath, hz⟩ :=
    (hwin.of_reachable (exactGame N blue) (hfrom.tail hs)).exists_terminal
      (exactGame N blue) hHN hH
  have hpz := (Relation.ReflTransGen.single hs).trans hzpath
  have horigin := hfrom.trans hpz
  obtain ⟨s, t, hc, hmax, hhead, hcard⟩ :=
    terminal_inside_clear_data blue origin z (by omega) hop hboard hmode hwin horigin hz
  obtain ⟨hl, hr, _hpos⟩ := hc.inside_roots_nonempty hhead hmax (by simpa only [hcard] using ha)
  have hcount := hc.aligned_last_body_count hhead hmax hl hr
    (of_decide_eq_true (hall z true horigin hz))
  obtain ⟨as, has, _⟩ := follow_word_inputs hpz 0 (fun _ => Nat.zero_le _) false
  have hleft : z.position.board.left.lastSelectedLabel = p.position.board.left.currentLabel :=
    has.lastSelectedLabel_eq_current ((Position.history_dataInvariant p).2.1 false).1 hrelL hrootL
  obtain ⟨bs, hbs, _⟩ := follow_word_inputs hzpath 0 (fun _ => Nat.zero_le _) true
  have hreply := (Concrete.response_spec hu).reply_spec hp
  have hright : z.position.board.right.lastSelectedLabel.card = d :=
    hreply.lastSelectedLabel_card_after hm hrootR hbs
  simpa only [hleft, hright] using hcount

#print axioms aligned_pending_right_last_size

end Erdos591.Positive.Game.Payoff

end Erdos118.Reused591
