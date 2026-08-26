import ErdosProblems.Erdos591.SelectedBodyCard
import ErdosProblems.Erdos591.TerminalUniformization
import ErdosProblems.Erdos591.FollowInputs

/-!
# Uniform last-body request sizes from terminal label data

The size of a pending last-selected-body request is recovered from
the fixed label slot in any terminal continuation. Uniformizing its
Boolean singleton test therefore gives a statement about every actual
reachable pending last-body request, without inspecting an unissued label.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact

def lastBodySingletonColor {N : Set ℕ} (side : Bool) (p : Concrete.Hist N) : Bool :=
  decide ((p.position.board.get side).lastSelectedLabel.card = 1)

theorem pending_last_body_observable {N H : Set ℕ} (hHN : H ⊆ N) (hH : H.Infinite)
    (blue : SimpleGraph G) {b : Concrete.Hist N → ℕ}
    {σ : (exactGame N blue).ArchitectStrategy} (origin p : Concrete.Hist N) (side value : Bool)
    (hfrom : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin p)
    (hall : ∀ z w, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin z →
      (exactGame N blue).kind z = .terminal w → lastBodySingletonColor side z = value)
    {r : Request} (hp : p.position.pending = some r) (hside : r.side = side)
    (hm : (p.position.board.get side).markerEvent = true)
    (hroot : ∀ i ∈ (p.position.board.get side).rootLabel,
      i ≤ (p.position.board.get side).bodyLabels.length + 1) : decide (r.size = 1) = value := by
  have hk : (exactGame N blue).kind p = .builder :=
    (Concrete.kind_builder_iff (payoff blue) p).mpr ⟨_, hp⟩
  obtain ⟨u, hu, huH, hub⟩ := (exactGame N blue).response_exists_above hHN hH p hk (b p)
  have hs : (exactGame N blue).FollowStep σ H b p (Concrete.response p u) :=
    FiniteResponseGame.FollowStep.builder (exactGame N blue) σ p u hk hu huH hub
  obtain ⟨z, w, hpath, hterminal⟩ := (exactGame N blue).terminal_reachable_of_infinite
    hHN hH b σ (Concrete.response p u)
  obtain ⟨as, has, _hpool⟩ := follow_word_inputs hpath 0 (fun _ => Nat.zero_le _) side
  have hr := (Concrete.response_spec hu).reply_spec hp
  have hcard : (z.position.board.get side).lastSelectedLabel.card = r.size := by
    apply hr.lastSelectedLabel_card_after
    · simpa [hside] using hm
    · simpa [hside] using hroot
    · simpa [hside] using has
  have he := hall z w ((hfrom.tail hs).trans hpath) hterminal
  simpa [lastBodySingletonColor, hcard] using he

theorem last_body_request_uniformization {N H : Set ℕ} (hHN : H ⊆ N) (hH : H.Infinite)
    (blue : SimpleGraph G) (b : Concrete.Hist N → ℕ)
    (σ : (exactGame N blue).ArchitectStrategy) (origin : Concrete.Hist N) (side : Bool) :
    ∃ L, L ⊆ H ∧ L.Infinite ∧ ∃ c : Concrete.Hist N → ℕ, (∀ p, b p ≤ c p) ∧ ∃ value : Bool,
      ∀ p r, Relation.ReflTransGen ((exactGame N blue).FollowStep σ L c) origin p →
        p.position.pending = some r → r.side = side →
        (p.position.board.get side).markerEvent = true →
        (∀ i ∈ (p.position.board.get side).rootLabel,
          i ≤ (p.position.board.get side).bodyLabels.length + 1) → decide (r.size = 1) = value := by
  obtain ⟨L, hLH, hL, c, hbc, v, hv⟩ := (exactGame N blue).terminal_bool_uniformization
    hHN hH b σ (lastBodySingletonColor side)
  refine ⟨L, hLH, hL, c, hbc, v origin, ?_⟩
  intro p r hfrom hp hside hm hroot
  exact pending_last_body_observable (hLH.trans hHN) hL blue origin p side (v origin) hfrom
    (hv origin) hp hside hm hroot

#print axioms pending_last_body_observable
#print axioms last_body_request_uniformization

end Erdos591.Positive.Game.Payoff
