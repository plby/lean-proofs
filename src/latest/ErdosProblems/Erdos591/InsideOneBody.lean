import ErdosProblems.Erdos591.InsideLastBodyTriangle
import ErdosProblems.Erdos591.InitialRootCard

/-! # Every winning inside opening of root-label size one gives a blue triangle -/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact

theorem inside_one_body_triangle {N H : Set ℕ} (hHN : H ⊆ N) (hH : H.Infinite)
    (blue : SimpleGraph G) {b : Concrete.Hist N → ℕ}
    {σ : (exactGame N blue).ArchitectStrategy}
    (hroot : (exactGame N blue).ArchitectWins H b σ
      (History.initial (Position.Next N) Position.initial))
    {p : Concrete.Hist N} (hwin : (exactGame N blue).ArchitectWins H b σ p)
    (hp : p.position.pending = some ⟨false, .advance 1⟩)
    (hboard : p.position.board = Board.initial) (hmode : p.position.mode = some true) :
    ¬ blue.CliqueFree 3 := by
  have hk : (exactGame N blue).kind p = .builder :=
    (Concrete.kind_builder_iff (payoff blue) p).mpr ⟨_, hp⟩
  obtain ⟨u, hu, huH, hub⟩ := (exactGame N blue).response_exists_above hHN hH p hk (b p)
  let q := Concrete.response p u
  have hs : (exactGame N blue).FollowStep σ H b p q :=
    FiniteResponseGame.FollowStep.builder (exactGame N blue) σ p u hk hu huH hub
  have hr := (Concrete.response_spec hu).reply_spec hp
  have hi : p.position.board.get false = LabeledWord.initial := by
    simp [hboard, Board.initial, Board.get]
  have hm := hr.initial_positive_marker hi (by decide : 0 < 1)
    (fun x hx => (Nat.zero_le (b p)).trans_lt (hub x hx))
  have hc := hr.initial_root_card hi
  have hn := (History.Next.position_next (FiniteResponseGame.FollowStep.next
    (exactGame N blue) hs)).no_pending_after_reply hp
  have hwinq := hwin.of_reachable (exactGame N blue) (Relation.ReflTransGen.single hs)
  obtain ⟨v, d, hrequest, hb, hpend, hd⟩ := winning_request_at_marker hHN hH blue hwinq false hn hm
  have hpath := (Relation.ReflTransGen.single hs).tail hrequest
  have hmarker : v.position.board.left.markerEvent = true := by
    simpa [hb, Board.get] using hm
  have hcard : v.position.board.left.rootLabel.card = 1 := by
    simpa [hb, Board.get] using hc
  have hrootLast : ∀ i ∈ v.position.board.left.rootLabel,
      i ≤ v.position.board.left.bodyLabels.length + 1 := by
    intro i hi
    exact (Finset.card_le_one.mp hcard.le i hi _ (LabeledWord.marker_body_mem hmarker)).le
  exact inside_last_body_triangle hHN hH blue hroot hwin (by decide : 0 < 1) hp hboard hmode
    (hwin.of_reachable (exactGame N blue) hpath) (follow_mode_some hpath hmode)
    (by simpa [hb, q, hboard, Board.initial, Board.get] using hr.other_eq)
    hd hpend hmarker hrootLast

#print axioms inside_one_body_triangle

end Erdos591.Positive.Game.Payoff
