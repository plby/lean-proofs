import ErdosProblems.Erdos591.InsideLateMarker

/-! # Excluding the late-marker value after terminal uniformization -/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact

theorem inside_early_marker_reduction {N H : Set ℕ}
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
      ∀ z w, Relation.ReflTransGen ((exactGame N blue).FollowStep σ L c) p z →
        (exactGame N blue).kind z = .terminal w →
          lastBodySingletonColor false z = false ∧ lateFirstMarkerColor z = false := by
  obtain ⟨haLarge, I, hIH, hI, c₀, hbc₀, hfirst, hlarge, hlast⟩ :=
    inside_large_endpoint_reduction hHN hH blue htri hroot hwin ha hp hboard hmode
  obtain ⟨L, hLI, hL, c, hc₀c, value, hvalue⟩ :=
    last_marker_order_uniformization (hIH.trans hHN) hI blue c₀ σ
  have hLH := hLI.trans hIH
  have hbc : ∀ q, b q ≤ c q := fun q => (hbc₀ q).trans (hc₀c q)
  have hpaths {u v : Concrete.Hist N}
      (hpath : Relation.ReflTransGen ((exactGame N blue).FollowStep σ L c) u v) :
      Relation.ReflTransGen ((exactGame N blue).FollowStep σ I c₀) u v :=
    Relation.ReflTransGen.mono (fun _ _ hs =>
      FiniteResponseGame.FollowStep.mono (exactGame N blue) hLI hc₀c hs) _ _ hpath
  have hfirst' : ∀ q v d, (exactGame N blue).FollowStep σ L c p q →
      (exactGame N blue).FollowStep σ L c q v →
      v.position.pending = some ⟨false, .advance d⟩ → 2 ≤ d := by
    intro q v d hpq hqv hpv
    exact hfirst q v d
      (FiniteResponseGame.FollowStep.mono (exactGame N blue) hLI hc₀c hpq)
      (FiniteResponseGame.FollowStep.mono (exactGame N blue) hLI hc₀c hqv) hpv
  have hlarge' : ∀ q d, Relation.ReflTransGen ((exactGame N blue).FollowStep σ L c) p q →
      q.position.pending = some ⟨false, .advance d⟩ → q.position.board.left.markerEvent = true →
      (∀ k ∈ q.position.board.left.rootLabel,
        k ≤ q.position.board.left.bodyLabels.length + 1) → 2 ≤ d :=
    fun q d hpath hpq hm hr => hlarge q d (hpaths hpath) hpq hm hr
  cases hv : value p with
  | true =>
      exact (inside_late_marker_of_endpoints (hLH.trans hHN) hL blue
        (hroot.mono (exactGame N blue) hLH hbc) (hwin.mono (exactGame N blue) hLH hbc)
        haLarge hp hboard hmode hfirst' hlarge'
        (fun z w hpath hz => by simpa only [hv] using hvalue p z w hpath hz) htri).elim
  | false =>
      refine ⟨haLarge, L, hLH, hL, c, hbc, hfirst', hlarge', ?_⟩
      intro z w hpath hz
      exact ⟨hlast z w (hpaths hpath) hz,
        by simpa only [hv] using hvalue p z w hpath hz⟩

#print axioms inside_early_marker_reduction

end Erdos591.Positive.Game.Payoff
