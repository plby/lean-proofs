import ErdosProblems.Erdos118.Reused591.InitialRootCard
import ErdosProblems.Erdos118.Reused591.FollowInputs

namespace Erdos118.Reused591

/-! # Root cardinality retained from an actual positive opening request -/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact

theorem reachable_opening_root_card {N H : Set ℕ} (blue : SimpleGraph G)
    {b : Concrete.Hist N → ℕ} {σ : (exactGame N blue).ArchitectStrategy}
    (origin p : Concrete.Hist N) (side : Bool) {a : ℕ} (ha : 0 < a)
    (hop : origin.position.pending = some ⟨side, .advance a⟩)
    (hinit : origin.position.board.get side = LabeledWord.initial)
    (hpath : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin p)
    (hstart : (p.position.board.get side).parser ≠ .start) :
    (p.position.board.get side).rootLabel.card = a := by
  rcases hpath.cases_head with heq | ⟨q, hoq, hqp⟩
  · exact (hstart (by simp [← heq, hinit, LabeledWord.initial])).elim
  have hk : (exactGame N blue).kind origin = .builder :=
    (Concrete.kind_builder_iff (payoff blue) origin).mpr ⟨_, hop⟩
  obtain ⟨u, hu, _huH, hub, hq⟩ : ∃ u, u ∈ (exactGame N blue).family origin ∧
      (↑u : Set ℕ) ⊆ H ∧ (∀ x ∈ u, b origin < x) ∧ q = Concrete.response origin u := by
    cases hoq.1 with
    | architect _ hh _ => simp [hk] at hh
    | builder u _ hu huH hub => exact ⟨u, hu, huH, hub, rfl⟩
  have hr := (Concrete.response_spec hu).reply_spec hop
  have hmarker : (q.position.board.get side).markerEvent = true := by
    rw [hq]
    exact hr.initial_positive_marker hinit ha
      (fun x hx => (Nat.zero_le _).trans_lt (hub x hx))
  obtain ⟨r, hparse⟩ := LabeledWord.marker_blocks hmarker
  obtain ⟨as, has, _⟩ := follow_word_inputs hqp 0 (fun _ => Nat.zero_le _) side
  rw [has.rootLabel_eq (by simp [hparse]), hq]
  exact hr.initial_root_card hinit

#print axioms reachable_opening_root_card

end Erdos591.Positive.Game.Payoff

end Erdos118.Reused591
