import ErdosProblems.Erdos118.Reused591.StrictCriticalData

namespace Erdos118.Reused591

/-!
# Fix the strict critical body's position before the second root is read

The finite color uses the already issued second-root request size.
Terminal bounds show that its truncation is inactive on every winning
continuation. Nonvacuity supplies a value strictly between zero and the
requested root cardinality; no coordinate in the fixed past is changed.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact

theorem strict_critical_body_uniformization {N H : Set ℕ}
    (hHN : H ⊆ N) (hH : H.Infinite) (blue : SimpleGraph G)
    {b : Concrete.Hist N → ℕ} {σ : (exactGame N blue).ArchitectStrategy}
    (origin p : Concrete.Hist N) {a e : ℕ} (ha : 2 ≤ a) (he : 0 < e)
    (hop : origin.position.pending = some ⟨false, .advance a⟩)
    (hboard : origin.position.board = Board.initial) (hmode : origin.position.mode = some true)
    (hwin : (exactGame N blue).ArchitectWins H b σ origin)
    (hfrom : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin p)
    (hp : p.position.pending = some ⟨true, .advance e⟩)
    (hinit : p.position.board.right = LabeledWord.initial)
    (hall : ∀ z w, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin z →
      (exactGame N blue).kind z = .terminal w →
        z.position.board.left.beforeLastLeafCount < z.position.board.right.beforeLastLeafCount) :
    ∃ L, L ⊆ H ∧ L.Infinite ∧ ∃ c : Concrete.Hist N → ℕ, (∀ q, b q ≤ c q) ∧
      ∃ j : ℕ, 0 < j ∧ j < e ∧ ∀ q w,
        Relation.ReflTransGen ((exactGame N blue).FollowStep σ L c) p q →
        (exactGame N blue).kind q = .terminal w →
          q.position.board.right.criticalBodyRank q.position.board.left.lastSelectedLabel.card = j ∧
            (criticalLastColor q = true → j + 1 < e) := by
  obtain ⟨L, hLH, hL, c, hbc, value, hvalue⟩ :=
    (exactGame N blue).terminal_finite_uniformization hHN hH b σ (criticalBodyColor e) p
  have paths {u v : Concrete.Hist N}
      (hpath : Relation.ReflTransGen ((exactGame N blue).FollowStep σ L c) u v) :
      Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) u v :=
    Relation.ReflTransGen.mono (fun _ _ hs =>
      FiniteResponseGame.FollowStep.mono (exactGame N blue) hLH hbc hs) _ _ hpath
  have data (q : Concrete.Hist N) (w : Bool)
      (hpath : Relation.ReflTransGen ((exactGame N blue).FollowStep σ L c) p q)
      (hq : (exactGame N blue).kind q = .terminal w) :
      0 < q.position.board.right.criticalBodyRank q.position.board.left.lastSelectedLabel.card ∧
        q.position.board.right.criticalBodyRank q.position.board.left.lastSelectedLabel.card < e ∧
        (criticalLastColor q = true →
          q.position.board.right.criticalBodyRank q.position.board.left.lastSelectedLabel.card + 1 <
            e) := by
    have hfull := hfrom.trans (paths hpath)
    obtain ⟨_hsize, hpos, hlt, hlast⟩ := terminal_strict_critical_data blue origin q ha hop
      hboard hmode hwin hfull hq (hall q w hfull hq)
    have hdone := ((Concrete.kind_terminal_iff (payoff blue) q w).mp hq).2.1
    have hterm := Board.terminal_of_done hdone true
    have hcard := reachable_opening_root_card blue p q true he hp hinit hpath
      (by intro hs; simp [LabeledWord.terminal, hs] at hterm)
    change q.position.board.right.rootLabel.card = e at hcard
    exact ⟨hpos, by simpa only [hcard] using hlt, by simpa only [hcard] using hlast⟩
  have fixed (q : Concrete.Hist N) (w : Bool)
      (hpath : Relation.ReflTransGen ((exactGame N blue).FollowStep σ L c) p q)
      (hq : (exactGame N blue).kind q = .terminal w) :
      q.position.board.right.criticalBodyRank q.position.board.left.lastSelectedLabel.card =
        value.val := by
    have hc := congrArg Fin.val (hvalue q w hpath hq)
    simpa only [criticalBodyColor, min_eq_left (data q w hpath hq).2.1.le] using hc
  obtain ⟨q₀, hpq₀, hq₀⟩ :=
    ((hwin.of_reachable (exactGame N blue) hfrom).mono (exactGame N blue) hLH hbc).exists_terminal
      (exactGame N blue) (hLH.trans hHN) hL
  have hdata := data q₀ true hpq₀ hq₀
  rw [fixed q₀ true hpq₀ hq₀] at hdata
  refine ⟨L, hLH, hL, c, hbc, value.val, hdata.1, hdata.2.1, ?_⟩
  intro q w hpath hq
  have heq := fixed q w hpath hq
  exact ⟨heq, by simpa only [heq] using (data q w hpath hq).2.2⟩

#print axioms strict_critical_body_uniformization

end Erdos591.Positive.Game.Payoff

end Erdos118.Reused591
