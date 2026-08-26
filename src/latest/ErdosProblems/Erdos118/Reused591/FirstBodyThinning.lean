import ErdosProblems.Erdos118.Reused591.PositiveSecondRequest

namespace Erdos118.Reused591

/-!
# Uniformity of the first selected-body request

Color each opening response by whether its following deterministic
strategy request has size one. Nash--Williams applies to the already
proved thin response family. Every conservative response on the new
pool reaches a selected-body marker, and its next request has positive
size, so the two colors give singleton versus at-least-two requests.
-/

namespace Erdos591.Positive.Game

open Erdos591.Negative.Exact
open Payoff
open Erdos590.Larson.NashWilliams

noncomputable def nextRequestSize {N : Set ℕ} (blue : SimpleGraph G)
    (σ : (exactGame N blue).ArchitectStrategy) (p : Concrete.Hist N) : ℕ := by
  classical
  exact if h : (exactGame N blue).kind p = .architect then
    ((σ.move p h).position.pending.map Request.size).getD 0 else 0

theorem nextRequestSize_eq {N H : Set ℕ} {blue : SimpleGraph G} {b : Concrete.Hist N → ℕ}
    {σ : (exactGame N blue).ArchitectStrategy} {p q : Concrete.Hist N} {r : Request}
    (hk : (exactGame N blue).kind p = .architect)
    (hs : (exactGame N blue).FollowStep σ H b p q) (hp : q.position.pending = some r) :
    nextRequestSize blue σ p = r.size := by
  simp only [nextRequestSize, dif_pos hk, ← hs.2 hk, hp, Option.map_some, Option.getD_some]

namespace Payoff

theorem first_body_request_dichotomy {N H : Set ℕ} (hHN : H ⊆ N) (hH : H.Infinite)
    (blue : SimpleGraph G) {b : Concrete.Hist N → ℕ}
    {σ : (exactGame N blue).ArchitectStrategy} {p : Concrete.Hist N}
    (hwin : (exactGame N blue).ArchitectWins H b σ p) {a : ℕ} (ha : 0 < a)
    (hp : p.position.pending = some ⟨false, .advance a⟩)
    (hi : p.position.board.left = LabeledWord.initial) :
    ∃ L, L ⊆ H ∧ L.Infinite ∧ ∃ single : Bool,
      ∀ u, u ∈ (exactGame N blue).family p → (↑u : Set ℕ) ⊆ L → (∀ x ∈ u, b p < x) →
        ∃ q d, (exactGame N blue).FollowStep σ L b (Concrete.response p u) q ∧
          q.position.board = (Concrete.response p u).position.board ∧
          q.position.pending = some ⟨false, .advance d⟩ ∧ 0 < d ∧
          (d = 1 ↔ single = true) := by
  classical
  have hk : (exactGame N blue).kind p = .builder :=
    (Concrete.kind_builder_iff (payoff blue) p).mpr ⟨_, hp⟩
  let color : Finset ℕ → Bool :=
    fun u => decide (nextRequestSize blue σ (Concrete.response p u) = 1)
  obtain ⟨L, hLH, hL, single, hcolor⟩ :=
    nashWilliams_two ((exactGame N blue).family p) ((exactGame N blue).thin p hk) color hH
  refine ⟨L, hLH, hL, single, ?_⟩
  intro u hu huL hub
  have hLN := hLH.trans hHN
  have hwinL := hwin.mono (exactGame N blue) hLH (fun _ => le_rfl)
  have hs : (exactGame N blue).FollowStep σ L b p (Concrete.response p u) :=
    FiniteResponseGame.FollowStep.builder (exactGame N blue) σ p u hk hu huL hub
  have hreply := (Concrete.response_spec hu).reply_spec hp
  have hm := hreply.initial_positive_marker hi ha
    (fun x hx => (Nat.zero_le (b p)).trans_lt (hub x hx))
  have hn := (History.Next.position_next (FiniteResponseGame.FollowStep.next
    (exactGame N blue) hs)).no_pending_after_reply hp
  have hwinResponse := hwinL.of_reachable (exactGame N blue) (Relation.ReflTransGen.single hs)
  obtain ⟨q, d, hrequest, hb, hpend, hd⟩ :=
    winning_request_at_marker hLN hL blue hwinResponse false hn hm
  have hkResponse : (exactGame N blue).kind (Concrete.response p u) = .architect :=
    (Concrete.kind_architect_iff (payoff blue) _).mpr
      ⟨hn, Board.not_done_of_live (LabeledWord.marker_not_terminal hm)⟩
  have hsize : nextRequestSize blue σ (Concrete.response p u) = d :=
    nextRequestSize_eq hkResponse hrequest hpend
  have hvalue : decide (d = 1) = single := by simpa [color, hsize] using hcolor u hu huL
  exact ⟨q, d, hrequest, hb, hpend, hd, by rw [← hvalue]; simp⟩

#print axioms first_body_request_dichotomy

/-- The same dichotomy for actual first-response and first-body-request
history steps, independently of which response constructor produced them. -/
theorem first_body_history_dichotomy {N H : Set ℕ} (hHN : H ⊆ N) (hH : H.Infinite)
    (blue : SimpleGraph G) {b : Concrete.Hist N → ℕ}
    {σ : (exactGame N blue).ArchitectStrategy} {p : Concrete.Hist N}
    (hwin : (exactGame N blue).ArchitectWins H b σ p) {a : ℕ} (ha : 0 < a)
    (hp : p.position.pending = some ⟨false, .advance a⟩)
    (hi : p.position.board.left = LabeledWord.initial) :
    ∃ L, L ⊆ H ∧ L.Infinite ∧ ∃ single : Bool,
      ∀ q v d, (exactGame N blue).FollowStep σ L b p q →
        (exactGame N blue).FollowStep σ L b q v →
        v.position.pending = some ⟨false, .advance d⟩ →
        0 < d ∧ (d = 1 ↔ single = true) := by
  obtain ⟨L, hLH, hL, single, hthin⟩ := first_body_request_dichotomy hHN hH blue hwin ha hp hi
  refine ⟨L, hLH, hL, single, ?_⟩
  intro q v d hs₀ hs₁ hv
  have hk : (exactGame N blue).kind p = .builder :=
    (Concrete.kind_builder_iff (payoff blue) p).mpr ⟨_, hp⟩
  obtain ⟨u, hu, huL, hub, hq⟩ : ∃ u, u ∈ (exactGame N blue).family p ∧
      (↑u : Set ℕ) ⊆ L ∧ (∀ x ∈ u, b p < x) ∧ q = Concrete.response p u := by
    cases hs₀.1 with
    | architect _ ha _ => simp [hk] at ha
    | builder u _ hu huL hub => exact ⟨u, hu, huL, hub, rfl⟩
  subst q
  obtain ⟨q', d', hs', _hb', hp', hd', he'⟩ := hthin u hu huL hub
  have hreply := (Concrete.response_spec hu).reply_spec hp
  have hm := hreply.initial_positive_marker hi ha
    (fun x hx => (Nat.zero_le (b p)).trans_lt (hub x hx))
  have hn := (History.Next.position_next (FiniteResponseGame.FollowStep.next
    (exactGame N blue) hs₀)).no_pending_after_reply hp
  have hkResponse : (exactGame N blue).kind (Concrete.response p u) = .architect :=
    (Concrete.kind_architect_iff (payoff blue) _).mpr
      ⟨hn, Board.not_done_of_live (LabeledWord.marker_not_terminal hm)⟩
  have hvq : v = q' := (hs₁.2 hkResponse).trans (hs'.2 hkResponse).symm
  have heq : d = d' := by
    have hreq : (⟨false, .advance d⟩ : Request) = ⟨false, .advance d'⟩ :=
      Option.some.inj (hv.symm.trans (hvq ▸ hp'))
    simpa using hreq
  exact heq ▸ ⟨hd', he'⟩

#print axioms first_body_history_dichotomy

end Payoff

end Erdos591.Positive.Game

end Erdos118.Reused591
