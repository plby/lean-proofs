import ErdosProblems.Erdos591.FollowFreshInputs
import ErdosProblems.Erdos591.FirstRequestRecovery

/-!
# The first root coordinate is smaller in an actual positive opening

After the first left response, every future right coordinate exceeds
that history's bound. The existing left head is below the bound and
persists literally through subsequent coordinate extensions.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact

theorem follow_head_order_of_right_empty {N H : Set ℕ} {blue : SimpleGraph G}
    {b : Concrete.Hist N → ℕ} {σ : (exactGame N blue).ArchitectStrategy}
    {p q : Concrete.Hist N}
    (hpath : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) p q)
    (hl : p.position.board.left.coordinates ≠ [])
    (hr : p.position.board.right.coordinates = [])
    (hqr : q.position.board.right.coordinates ≠ []) :
    q.position.board.left.coordinates.headD 0 < q.position.board.right.coordinates.headD 0 := by
  obtain ⟨leftAtoms, hleft, _⟩ := follow_word_inputs_above_bound hpath false
  obtain ⟨rightAtoms, hright, hfresh⟩ := follow_word_inputs_above_bound hpath true
  have hleftCoords := LabeledWord.runAtoms_coordinates hleft.run
  have hrightCoords : q.position.board.right.coordinates = rightAtoms.map Prod.snd := by
    simpa only [Board.get, hr, List.nil_append] using
      LabeledWord.runAtoms_coordinates hright.run
  cases hp : p.position.board.left.coordinates with
  | nil => exact (hl hp).elim
  | cons x xs =>
      have hx : x ∈ p.position.board.left.coordinates := by simp [hp]
      have hxBound := (Position.history_dataInvariant p).1 x
        (p.position.board.get_support_subset false (LabeledWord.coordinate_mem_support hx))
      have hhead : q.position.board.left.coordinates.headD 0 = x := by
        simpa only [Board.get, hp, List.cons_append, List.headD_cons] using
          congrArg (fun l : List ℕ => l.headD 0) hleftCoords
      cases hq : q.position.board.right.coordinates with
      | nil => exact (hqr hq).elim
      | cons y ys =>
          have hy : y ∈ rightAtoms.map Prod.snd := by
            rw [← hrightCoords, hq]
            simp
          obtain ⟨atom, hatom, hay⟩ := List.mem_map.mp hy
          have hxy : x < y := hay ▸ hxBound.2.2.trans_lt (hfresh atom hatom).2
          simpa only [hhead, hq, List.headD_cons] using hxy

theorem positive_opening_head_order {N H : Set ℕ} (blue : SimpleGraph G)
    {b : Concrete.Hist N → ℕ} {σ : (exactGame N blue).ArchitectStrategy}
    (origin q : Concrete.Hist N) {a : ℕ} (ha : 0 < a)
    (hop : origin.position.pending = some ⟨false, .advance a⟩)
    (hboard : origin.position.board = Board.initial)
    (hpath : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin q)
    (hqr : q.position.board.right.coordinates ≠ []) :
    q.position.board.left.coordinates.headD 0 < q.position.board.right.coordinates.headD 0 := by
  rcases hpath.cases_head with heq | ⟨p, hopStep, hpq⟩
  · exact (hqr (by simp [← heq, hboard, Board.initial, LabeledWord.initial])).elim
  have hk : (exactGame N blue).kind origin = .builder :=
    (Concrete.kind_builder_iff (payoff blue) origin).mpr ⟨_, hop⟩
  obtain ⟨u, hu, hub, hp⟩ : ∃ u, u ∈ (exactGame N blue).family origin ∧
      (∀ x ∈ u, b origin < x) ∧ p = Concrete.response origin u := by
    cases hopStep.1 with
    | architect _ hh _ => simp [hk] at hh
    | builder u _ hu _ hub => exact ⟨u, hu, hub, rfl⟩
  have hreply := (Concrete.response_spec hu).reply_spec hop
  have hmarker : p.position.board.left.markerEvent = true := by
    rw [hp]
    exact hreply.initial_positive_marker (by simp [hboard, Board.initial, Board.get]) ha
      (fun x hx => (Nat.zero_le _).trans_lt (hub x hx))
  have hleft : p.position.board.left.coordinates ≠ [] := by
    intro hnil
    obtain ⟨r, hparse⟩ := LabeledWord.marker_blocks hmarker
    have hparsed := ((Position.history_dataInvariant p).2.1 false).1.1
    simp [LabeledWord.Parsed, Board.get, hnil, hparse] at hparsed
  have hright : p.position.board.right.coordinates = [] := by
    have ho := hreply.other_eq
    change (Concrete.response origin u).position.board.right = origin.position.board.right at ho
    simp only [hp, ho, hboard, Board.initial, LabeledWord.initial]
  exact follow_head_order_of_right_empty hpq hleft hright hqr

#print axioms follow_head_order_of_right_empty
#print axioms positive_opening_head_order

end Erdos591.Positive.Game.Payoff
