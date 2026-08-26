import ErdosProblems.Erdos591.StrictCriticalData
import ErdosProblems.Erdos591.ReachableBodyCard

/-!
# Fix the critical leaf position before its body label is read

The critical body has already been localized to the current actual
marker. The issued request fixes the full label size in every terminal
extension. A finite color then fixes the critical rank, and the exact
filter cardinality distinguishes last from nonlast without changing any
past input, label, or response.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact

theorem strict_critical_leaf_uniformization {N H : Set ℕ}
    (hHN : H ⊆ N) (hH : H.Infinite) (blue : SimpleGraph G)
    {b : Concrete.Hist N → ℕ} {σ : (exactGame N blue).ArchitectStrategy}
    (origin p : Concrete.Hist N) {a d : ℕ} (ha : 2 ≤ a)
    (hop : origin.position.pending = some ⟨false, .advance a⟩)
    (hboard : origin.position.board = Board.initial) (hmode : origin.position.mode = some true)
    (hwin : (exactGame N blue).ArchitectWins H b σ origin)
    (hfrom : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin p)
    (hp : p.position.pending = some ⟨true, .advance d⟩)
    (hm : p.position.board.right.markerEvent = true)
    (hall : ∀ z w, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin z →
      (exactGame N blue).kind z = .terminal w →
        z.position.board.left.beforeLastLeafCount < z.position.board.right.beforeLastLeafCount)
    (hbody : ∀ q w, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) p q →
      (exactGame N blue).kind q = .terminal w →
        (q.position.board.right.criticalPair q.position.board.left.lastSelectedLabel.card).1 =
          p.position.board.right.bodyLabels.length + 1) :
    ∃ L, L ⊆ H ∧ L.Infinite ∧ ∃ c : Concrete.Hist N → ℕ, (∀ q, b q ≤ c q) ∧
      ∃ s : ℕ, 0 < s ∧ s ≤ d ∧ ∀ q w,
        Relation.ReflTransGen ((exactGame N blue).FollowStep σ L c) p q →
        (exactGame N blue).kind q = .terminal w →
          q.position.board.right.criticalLeafRank q.position.board.left.lastSelectedLabel.card = s ∧
            (criticalLastColor q = true ↔ s = d) := by
  obtain ⟨L, hLH, hL, c, hbc, value, hvalue⟩ :=
    (exactGame N blue).terminal_finite_uniformization hHN hH b σ (criticalLeafColor d) p
  have paths {u v : Concrete.Hist N}
      (hpath : Relation.ReflTransGen ((exactGame N blue).FollowStep σ L c) u v) :
      Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) u v :=
    Relation.ReflTransGen.mono (fun _ _ hs =>
      FiniteResponseGame.FollowStep.mono (exactGame N blue) hLH hbc hs) _ _ hpath
  have data (q : Concrete.Hist N) (w : Bool)
      (hpath : Relation.ReflTransGen ((exactGame N blue).FollowStep σ L c) p q)
      (hq : (exactGame N blue).kind q = .terminal w) :
      0 < q.position.board.right.criticalLeafRank q.position.board.left.lastSelectedLabel.card ∧
        q.position.board.right.criticalLeafRank q.position.board.left.lastSelectedLabel.card ≤ d ∧
        (criticalLastColor q = true ↔
          q.position.board.right.criticalLeafRank
            q.position.board.left.lastSelectedLabel.card = d) := by
    have hfull := hfrom.trans (paths hpath)
    obtain ⟨s, t, hc, hmax, hfirst, hrootCard⟩ :=
      terminal_inside_clear_data blue origin q (by omega) hop hboard hmode hwin hfull hq
    have hspec := (hc.strict_critical_data hfirst hmax (by simpa only [hrootCard] using ha)
      (hall q w hfull hq)).2.1
    have hcard := reachable_body_label_card blue p q true hp hm hpath hq
    change (q.position.board.right.bodyLabels.getD p.position.board.right.bodyLabels.length ∅).card
      = d at hcard
    have hcriticalCard : (q.position.board.right.bodyLabels.getD
        ((q.position.board.right.criticalPair q.position.board.left.lastSelectedLabel.card).1 - 1)
        ∅).card = d := by
      rw [hbody q w (paths hpath) hq, Nat.add_sub_cancel]
      exact hcard
    exact ⟨LabeledWord.criticalLeafRank_pos hspec,
      by simpa only [hcriticalCard] using (q.position.board.right.criticalLeafRank_le
        q.position.board.left.lastSelectedLabel.card),
      by simpa only [criticalLastColor, hcriticalCard] using
        (q.position.board.right.criticalLast_iff_leafRank_eq
        q.position.board.left.lastSelectedLabel.card)⟩
  have fixed (q : Concrete.Hist N) (w : Bool)
      (hpath : Relation.ReflTransGen ((exactGame N blue).FollowStep σ L c) p q)
      (hq : (exactGame N blue).kind q = .terminal w) :
      q.position.board.right.criticalLeafRank q.position.board.left.lastSelectedLabel.card =
        value.val := by
    have hc := congrArg Fin.val (hvalue q w hpath hq)
    simpa only [criticalLeafColor, min_eq_left (data q w hpath hq).2.1] using hc
  obtain ⟨q₀, hpq₀, hq₀⟩ :=
    ((hwin.of_reachable (exactGame N blue) hfrom).mono (exactGame N blue) hLH hbc).exists_terminal
      (exactGame N blue) (hLH.trans hHN) hL
  have hdata := data q₀ true hpq₀ hq₀
  rw [fixed q₀ true hpq₀ hq₀] at hdata
  refine ⟨L, hLH, hL, c, hbc, value.val, hdata.1, hdata.2.1, ?_⟩
  intro q w hpath hq
  have heq := fixed q w hpath hq
  exact ⟨heq, by simpa only [heq] using (data q w hpath hq).2.2⟩

#print axioms strict_critical_leaf_uniformization

end Erdos591.Positive.Game.Payoff
