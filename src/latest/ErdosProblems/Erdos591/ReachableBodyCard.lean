import ErdosProblems.Erdos591.ReachableRootCard
import ErdosProblems.Erdos591.SelectedBodyCard

/-! # An actual pending selected-body request fixes its terminal label cardinality -/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact

theorem reachable_body_label_card {N H : Set ℕ} (blue : SimpleGraph G)
    {b : Concrete.Hist N → ℕ} {σ : (exactGame N blue).ArchitectStrategy}
    (p q : Concrete.Hist N) (side : Bool) {d : ℕ}
    (hp : p.position.pending = some ⟨side, .advance d⟩)
    (hm : (p.position.board.get side).markerEvent = true)
    (hpath : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) p q)
    {value : Bool} (hq : (exactGame N blue).kind q = .terminal value) :
    ((q.position.board.get side).bodyLabels.getD
      (p.position.board.get side).bodyLabels.length ∅).card = d := by
  have hk : (exactGame N blue).kind p = .builder :=
    (Concrete.kind_builder_iff (payoff blue) p).mpr ⟨_, hp⟩
  rcases hpath.cases_head with heq | ⟨v, hpv, hvq⟩
  · rw [← heq, hk] at hq
    cases hq
  obtain ⟨u, hu, hv⟩ : ∃ u, u ∈ (exactGame N blue).family p ∧ v = Concrete.response p u := by
    cases hpv.1 with
    | architect _ hh _ => simp [hk] at hh
    | builder u _ hu _ _ => exact ⟨u, hu, rfl⟩
  obtain ⟨as, has, _⟩ := follow_word_inputs hvq 0 (fun _ => Nat.zero_le _) side
  rw [hv] at has
  exact ((Concrete.response_spec hu).reply_spec hp).body_label_card_after hm has

#print axioms reachable_body_label_card

theorem reachable_last_body_label_card {N H : Set ℕ} (blue : SimpleGraph G)
    {b : Concrete.Hist N → ℕ} {σ : (exactGame N blue).ArchitectStrategy}
    (p q : Concrete.Hist N) (side : Bool) {d : ℕ}
    (hp : p.position.pending = some ⟨side, .advance d⟩)
    (hm : (p.position.board.get side).markerEvent = true)
    (hrootLast : ∀ i ∈ (p.position.board.get side).rootLabel,
      i ≤ (p.position.board.get side).bodyLabels.length + 1)
    (hpath : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) p q)
    {value : Bool} (hq : (exactGame N blue).kind q = .terminal value) :
    (q.position.board.get side).lastSelectedLabel.card = d := by
  have hcard := reachable_body_label_card blue p q side hp hm hpath hq
  obtain ⟨r, hparse⟩ := LabeledWord.marker_blocks hm
  obtain ⟨as, has, _⟩ := follow_word_inputs hpath 0 (fun _ => Nat.zero_le _) side
  have hroot := has.rootLabel_eq (by simp [hparse])
  have hlast : (q.position.board.get side).lastSelectedBody =
      (p.position.board.get side).bodyLabels.length + 1 := by
    rw [LabeledWord.lastSelectedBody, hroot]
    exact LabeledWord.lastSelectedBody_of_marker hm hrootLast
  simpa only [LabeledWord.lastSelectedLabel, hlast, Nat.add_sub_cancel] using hcard

#print axioms reachable_last_body_label_card

end Erdos591.Positive.Game.Payoff
