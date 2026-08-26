import ErdosProblems.Erdos118.Reused591.MarkerRecovery
import ErdosProblems.Erdos118.Reused591.SelectedMarkerResponse
import ErdosProblems.Erdos118.Reused591.TerminalUniformization
import ErdosProblems.Erdos118.Reused591.FollowInputs

namespace Erdos118.Reused591

/-!
# Terminal marker order and the absence of a later opposite body

The marker comparison is a total Boolean observable. Its uniform value
is obtained from the fixed-strategy terminal-color theorem. A future
opposite selected body would allow its marker to be chosen above an
already recorded last first-word marker, contradicting the late order.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact

noncomputable def lateFirstMarkerColor {N : Set ℕ} (p : Concrete.Hist N) : Bool :=
  decide (p.position.board.right.lastSelectedMarker < p.position.board.left.lastSelectedMarker)

theorem last_marker_order_uniformization {N H : Set ℕ} (hHN : H ⊆ N) (hH : H.Infinite)
    (blue : SimpleGraph G) (b : Concrete.Hist N → ℕ)
    (σ : (exactGame N blue).ArchitectStrategy) :
    ∃ L, L ⊆ H ∧ L.Infinite ∧ ∃ c : Concrete.Hist N → ℕ, (∀ p, b p ≤ c p) ∧
      ∃ value : Concrete.Hist N → Bool, ∀ p z w,
        Relation.ReflTransGen ((exactGame N blue).FollowStep σ L c) p z →
        (exactGame N blue).kind z = .terminal w → lateFirstMarkerColor z = value p :=
  (exactGame N blue).terminal_bool_uniformization hHN hH b σ lateFirstMarkerColor

theorem winning_late_marker_no_future_right {N H : Set ℕ}
    (hHN : H ⊆ N) (hH : H.Infinite) (blue : SimpleGraph G)
    {b : Concrete.Hist N → ℕ} {σ : (exactGame N blue).ArchitectStrategy}
    (origin p : Concrete.Hist N)
    (hwin : (exactGame N blue).ArchitectWins H b σ p)
    (hfrom : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin p)
    (hall : ∀ z w, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin z →
      (exactGame N blue).kind z = .terminal w → lateFirstMarkerColor z = true)
    (hrel : p.position.board.left.relaxed = true)
    (hlast : p.position.board.left.lastSelectedBody = p.position.board.left.bodyLabels.length)
    (hstart : p.position.board.right.parser ≠ .start) :
    ∀ i ∈ p.position.board.right.rootLabel, i ≤ p.position.board.right.bodyLabels.length := by
  by_contra hnot
  simp only [not_forall, not_le] at hnot
  obtain ⟨j, hj, hjlt⟩ := hnot
  let i := p.position.board.right.lastSelectedBody
  have himem : i ∈ p.position.board.right.rootLabel := by
    simpa [i, LabeledWord.lastSelectedBody] using
      Finset.sup_mem_of_nonempty (f := id) (show p.position.board.right.rootLabel.Nonempty
        from ⟨j, hj⟩)
  have hibefore : LabeledWord.BeforeBody i p.position.board.right :=
    ⟨himem, hjlt.trans_le (Finset.le_sup (f := id) hj)⟩
  obtain ⟨q, d, hpq, hpend, hd, hm, hcount⟩ :=
    winning_reach_body_marker hHN hH blue hwin true i hstart hibefore
  have hkind : (exactGame N blue).kind q = .builder :=
    (Concrete.kind_builder_iff (payoff blue) q).mpr ⟨_, hpend⟩
  obtain ⟨u, hu, huH, hub⟩ := (exactGame N blue).response_exists_above hHN hH q hkind
    (max (b q) p.position.board.left.bodyMarker)
  let r := Concrete.response q u
  have hqr : (exactGame N blue).FollowStep σ H b q r :=
    FiniteResponseGame.FollowStep.builder (exactGame N blue) σ q u hkind hu huH
      (fun x hx => (le_max_left _ _).trans_lt (hub x hx))
  have hpr := hpq.tail hqr
  have hr := (Concrete.response_spec hu).reply_spec hpend
  obtain ⟨hrrel, hrcount, hrmarker⟩ := hr.selected_marker_metadata
    ((Position.history_dataInvariant q).2.1 true).1 hm hd
    (fun x hx => (Nat.zero_le _).trans_lt (hub x hx))
  have hfresh : p.position.board.left.bodyMarker < r.position.board.right.bodyMarker :=
    (le_max_right _ _).trans_lt (hub _ hrmarker)
  obtain ⟨as, has, _⟩ := follow_word_inputs hpr 0 (fun _ => Nat.zero_le _) true
  have hroot : r.position.board.right.rootLabel = p.position.board.right.rootLabel :=
    has.rootLabel_eq hstart
  have hrlast : r.position.board.right.lastSelectedBody =
      r.position.board.right.bodyLabels.length := by
    have hc : r.position.board.right.bodyLabels.length = i := hrcount.trans hcount
    rw [LabeledWord.lastSelectedBody, hroot, hc]
    rfl
  obtain ⟨z, hrz, hz⟩ := (hwin.of_reachable (exactGame N blue) hpr).exists_terminal
    (exactGame N blue) hHN hH
  have hdone := ((Concrete.kind_terminal_iff (payoff blue) z true).mp hz).2.1
  have hleft := History.lastSelectedMarker_eq_of_relaxed_prefix
    (follow_history_path (hpr.trans hrz)) hdone false hrel hlast
  have hright := History.lastSelectedMarker_eq_of_relaxed_prefix
    (follow_history_path hrz) hdone true hrrel hrlast
  have hcolor := hall z true (hfrom.trans (hpr.trans hrz)) hz
  have hlt : z.position.board.right.lastSelectedMarker <
      z.position.board.left.lastSelectedMarker := of_decide_eq_true hcolor
  change z.position.board.left.lastSelectedMarker = _ at hleft
  change z.position.board.right.lastSelectedMarker = _ at hright
  rw [hleft, hright] at hlt
  exact (not_lt_of_ge hfresh.le) hlt

#print axioms last_marker_order_uniformization
#print axioms winning_late_marker_no_future_right

end Erdos591.Positive.Game.Payoff

end Erdos118.Reused591
