import ErdosProblems.Erdos591.InsideEarlyMarkerReduction
import ErdosProblems.Erdos591.TerminalMarkerCounts

/-!
# Reduction to uniformly aligned or uniformly strict pre-last counts

The proved late-marker exclusion supplies A ≤ B. One further terminal
Boolean uniformization makes equality constant. The new pool and bound
retain the existing first and last body-request size restrictions.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact

theorem inside_count_alternative {N H : Set ℕ}
    (hHN : H ⊆ N) (hH : H.Infinite) (blue : SimpleGraph G) (htri : blue.CliqueFree 3)
    {b : Concrete.Hist N → ℕ} {σ : (exactGame N blue).ArchitectStrategy}
    (hroot : (exactGame N blue).ArchitectWins H b σ
      (History.initial (Position.Next N) Position.initial))
    {p : Concrete.Hist N} (hwin : (exactGame N blue).ArchitectWins H b σ p)
    {a : ℕ} (ha : 0 < a) (hp : p.position.pending = some ⟨false, .advance a⟩)
    (hboard : p.position.board = Board.initial) (hmode : p.position.mode = some true) :
    2 ≤ a ∧ ∃ L, L ⊆ H ∧ L.Infinite ∧ ∃ c : Concrete.Hist N → ℕ, (∀ q, b q ≤ c q) ∧
      (∀ q v d, (exactGame N blue).FollowStep σ L c p q →
        (exactGame N blue).FollowStep σ L c q v →
        v.position.pending = some ⟨false, .advance d⟩ → 2 ≤ d) ∧
      (∀ q d, Relation.ReflTransGen ((exactGame N blue).FollowStep σ L c) p q →
        q.position.pending = some ⟨false, .advance d⟩ →
        q.position.board.left.markerEvent = true →
        (∀ k ∈ q.position.board.left.rootLabel,
          k ≤ q.position.board.left.bodyLabels.length + 1) → 2 ≤ d) ∧
      ∃ aligned : Bool, ∀ z w,
        Relation.ReflTransGen ((exactGame N blue).FollowStep σ L c) p z →
        (exactGame N blue).kind z = .terminal w →
          lastBodySingletonColor false z = false ∧ lateFirstMarkerColor z = false ∧
          alignedBodyCountColor z = aligned ∧
          if aligned then z.position.board.left.beforeLastLeafCount =
              z.position.board.right.beforeLastLeafCount
          else z.position.board.left.beforeLastLeafCount <
              z.position.board.right.beforeLastLeafCount := by
  obtain ⟨haLarge, I, hIH, hI, c₀, hbc₀, hfirst, hlarge, hcolors⟩ :=
    inside_early_marker_reduction hHN hH blue htri hroot hwin ha hp hboard hmode
  obtain ⟨L, hLI, hL, c, hc₀c, value, hvalue⟩ :=
    (exactGame N blue).terminal_bool_uniformization (hIH.trans hHN) hI c₀ σ alignedBodyCountColor
  have hLH := hLI.trans hIH
  have hbc : ∀ q, b q ≤ c q := fun q => (hbc₀ q).trans (hc₀c q)
  have hpaths {u v : Concrete.Hist N}
      (hpath : Relation.ReflTransGen ((exactGame N blue).FollowStep σ L c) u v) :
      Relation.ReflTransGen ((exactGame N blue).FollowStep σ I c₀) u v :=
    Relation.ReflTransGen.mono (fun _ _ hs =>
      FiniteResponseGame.FollowStep.mono (exactGame N blue) hLI hc₀c hs) _ _ hpath
  refine ⟨haLarge, L, hLH, hL, c, hbc, ?_, ?_, value p, ?_⟩
  · intro q v d hpq hqv hpv
    exact hfirst q v d
      (FiniteResponseGame.FollowStep.mono (exactGame N blue) hLI hc₀c hpq)
      (FiniteResponseGame.FollowStep.mono (exactGame N blue) hLI hc₀c hqv) hpv
  · intro q d hpath hpq hm hr
    exact hlarge q d (hpaths hpath) hpq hm hr
  · intro z w hpath hz
    have hold := hcolors z w (hpaths hpath) hz
    have haligned := hvalue p z w hpath hz
    have hle := terminal_not_late_before_count_le blue p z haLarge hp hboard hmode
      (hwin.mono (exactGame N blue) hLH hbc) hpath hz hold.2
    refine ⟨hold.1, hold.2, haligned, ?_⟩
    cases hv : value p with
    | true =>
        have heq := of_decide_eq_true (haligned.trans hv)
        simpa only [hv, ↓reduceIte] using heq
    | false =>
        have hne := of_decide_eq_false (haligned.trans hv)
        have hlt : z.position.board.left.beforeLastLeafCount <
            z.position.board.right.beforeLastLeafCount := by omega
        simpa only [hv, Bool.false_eq_true, ↓reduceIte] using hlt

#print axioms inside_count_alternative

end Erdos591.Positive.Game.Payoff
