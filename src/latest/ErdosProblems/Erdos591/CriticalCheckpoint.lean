import ErdosProblems.Erdos591.CriticalObservables

/-! # Exact partial-history interface for the critical opposite leaf -/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact

structure CriticalCheckpoint {N : Set ℕ} (p : Concrete.Hist N) : Prop where
  left_relaxed : p.position.board.left.relaxed = true
  right_relaxed : p.position.board.right.relaxed = true
  coordinate_order : p.position.board.left.coordinates.getLastD 0 <
    p.position.board.right.coordinates.getLastD 0
  left_before : p.position.board.left.bodyLabels.length < p.position.board.left.lastSelectedBody
  left_penultimate : ∀ k ∈ p.position.board.left.rootLabel,
    k < p.position.board.left.lastSelectedBody → k ≤ p.position.board.left.bodyLabels.length
  left_exhausted : p.position.board.left.NoLeafPending

theorem CriticalCheckpoint.terminal_observables {N : Set ℕ} {p q : Concrete.Hist N}
    (h : CriticalCheckpoint p)
    (hpath : Relation.ReflTransGen (fun p q => History.Next q p) p q)
    {s t : G} (hc : Clear q.position.board s t) (hmax : MaxOrder true q.position.board) :
    q.position.board.right.criticalBodyRank q.position.board.left.lastSelectedLabel.card =
        (p.position.board.right.rootLabel.filter
          (fun i => i ≤ p.position.board.right.bodyLabels.length)).card ∧
      q.position.board.right.criticalLeafRank q.position.board.left.lastSelectedLabel.card =
        (p.position.board.right.currentLabel.filter
          (fun j => j ≤ p.position.board.right.leafIndex)).card ∧
      (criticalLastColor q = true ↔ p.position.board.right.NoLeafPending) :=
  (history_critical_observables hpath hc hmax h.left_relaxed h.right_relaxed
    h.coordinate_order h.left_before h.left_penultimate h.left_exhausted).2

theorem critical_last_uniformization {N H : Set ℕ}
    (hHN : H ⊆ N) (hH : H.Infinite) (blue : SimpleGraph G)
    {b : Concrete.Hist N → ℕ} {σ : (exactGame N blue).ArchitectStrategy}
    (origin : Concrete.Hist N) {a : ℕ} (ha : 0 < a)
    (hop : origin.position.pending = some ⟨false, .advance a⟩)
    (hboard : origin.position.board = Board.initial) (hmode : origin.position.mode = some true)
    (hwin : (exactGame N blue).ArchitectWins H b σ origin) :
    ∃ L, L ⊆ H ∧ L.Infinite ∧ ∃ c : Concrete.Hist N → ℕ, (∀ q, b q ≤ c q) ∧
      ∃ value : Bool,
        (∀ q w, Relation.ReflTransGen ((exactGame N blue).FollowStep σ L c) origin q →
          (exactGame N blue).kind q = .terminal w → criticalLastColor q = value) ∧
        ∀ p, Relation.ReflTransGen ((exactGame N blue).FollowStep σ L c) origin p →
          CriticalCheckpoint p → (p.position.board.right.NoLeafPending ↔ value = true) := by
  obtain ⟨L, hLH, hL, c, hbc, v, hv⟩ :=
    (exactGame N blue).terminal_bool_uniformization hHN hH b σ criticalLastColor
  have hwinL := hwin.mono (exactGame N blue) hLH hbc
  refine ⟨L, hLH, hL, c, hbc, v origin, hv origin, ?_⟩
  intro p hfrom hcheckpoint
  obtain ⟨q, hpq, hq⟩ := (hwinL.of_reachable (exactGame N blue) hfrom).exists_terminal
    (exactGame N blue) (hLH.trans hHN) hL
  have hfull := hfrom.trans hpq
  obtain ⟨s, t, hc, hmax, _hfirst, _hcard⟩ :=
    terminal_inside_clear_data blue origin q ha hop hboard hmode hwinL hfull hq
  have hlast := (hcheckpoint.terminal_observables (follow_history_path hpq) hc hmax).2.2
  rw [hv origin q true hfull hq] at hlast
  exact hlast.symm

#print axioms CriticalCheckpoint.terminal_observables
#print axioms critical_last_uniformization

end Erdos591.Positive.Game.Payoff
