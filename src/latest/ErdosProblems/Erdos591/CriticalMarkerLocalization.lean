import ErdosProblems.Erdos591.FiniteRank
import ErdosProblems.Erdos591.StrictLeafLocalization

/-!
# The fixed body rank identifies an actual pending marker

Root labels do not change after they are read. A terminal critical
body and a pending selected marker having the same finite root rank
are therefore the same numerical index. This discharges the exact
body-localization premise needed before localizing its leaf rank.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact

theorem terminal_critical_body_eq_of_marker_rank {N H : Set ℕ}
    (blue : SimpleGraph G) {b : Concrete.Hist N → ℕ}
    {σ : (exactGame N blue).ArchitectStrategy}
    (origin p q : Concrete.Hist N) {a j : ℕ} (ha : 2 ≤ a)
    (hop : origin.position.pending = some ⟨false, .advance a⟩)
    (hboard : origin.position.board = Board.initial) (hmode : origin.position.mode = some true)
    (hwin : (exactGame N blue).ArchitectWins H b σ origin)
    (hfrom : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin p)
    (hpath : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) p q)
    {value : Bool} (hq : (exactGame N blue).kind q = .terminal value)
    (hstrict : q.position.board.left.beforeLastLeafCount <
      q.position.board.right.beforeLastLeafCount)
    (hm : p.position.board.right.markerEvent = true)
    (hpRank : (p.position.board.right.rootLabel.filter
      (fun i => i ≤ p.position.board.right.bodyLabels.length + 1)).card = j)
    (hqRank : q.position.board.right.criticalBodyRank q.position.board.left.lastSelectedLabel.card =
      j) :
    (q.position.board.right.criticalPair q.position.board.left.lastSelectedLabel.card).1 =
      p.position.board.right.bodyLabels.length + 1 := by
  obtain ⟨s, t, hc, hmax, hfirst, hcard⟩ :=
    terminal_inside_clear_data blue origin q (by omega) hop hboard hmode hwin (hfrom.trans hpath) hq
  have hspec := (hc.strict_critical_data hfirst hmax (by simpa only [hcard] using ha) hstrict).2.1
  obtain ⟨r, hparse⟩ := LabeledWord.marker_blocks hm
  obtain ⟨as, has, _⟩ := follow_word_inputs hpath 0 (fun _ => Nat.zero_le _) true
  have hroot : q.position.board.right.rootLabel = p.position.board.right.rootLabel :=
    has.rootLabel_eq (by simp [Board.get, hparse])
  apply finite_rank_injective q.position.board.right.rootLabel (Finset.mem_sigma.mp hspec.1).1
    (hroot ▸ LabeledWord.marker_body_mem hm)
  exact hqRank.trans (by simpa only [hroot] using hpRank.symm)

theorem strict_critical_leaf_uniformization_of_rank {N H : Set ℕ}
    (hHN : H ⊆ N) (hH : H.Infinite) (blue : SimpleGraph G)
    {b : Concrete.Hist N → ℕ} {σ : (exactGame N blue).ArchitectStrategy}
    (origin p : Concrete.Hist N) {a d j : ℕ} (ha : 2 ≤ a)
    (hop : origin.position.pending = some ⟨false, .advance a⟩)
    (hboard : origin.position.board = Board.initial) (hmode : origin.position.mode = some true)
    (hwin : (exactGame N blue).ArchitectWins H b σ origin)
    (hfrom : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin p)
    (hp : p.position.pending = some ⟨true, .advance d⟩)
    (hm : p.position.board.right.markerEvent = true)
    (hall : ∀ z w, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin z →
      (exactGame N blue).kind z = .terminal w →
        z.position.board.left.beforeLastLeafCount < z.position.board.right.beforeLastLeafCount)
    (hpRank : (p.position.board.right.rootLabel.filter
      (fun i => i ≤ p.position.board.right.bodyLabels.length + 1)).card = j)
    (hfixed : ∀ q w, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) p q →
      (exactGame N blue).kind q = .terminal w →
        q.position.board.right.criticalBodyRank q.position.board.left.lastSelectedLabel.card = j) :
    ∃ L, L ⊆ H ∧ L.Infinite ∧ ∃ c : Concrete.Hist N → ℕ, (∀ q, b q ≤ c q) ∧
      ∃ s : ℕ, 0 < s ∧ s ≤ d ∧ ∀ q w,
        Relation.ReflTransGen ((exactGame N blue).FollowStep σ L c) p q →
        (exactGame N blue).kind q = .terminal w →
          q.position.board.right.criticalLeafRank q.position.board.left.lastSelectedLabel.card = s ∧
            (criticalLastColor q = true ↔ s = d) := by
  apply strict_critical_leaf_uniformization hHN hH blue origin p ha hop hboard hmode hwin
    hfrom hp hm hall
  intro q w hpath hq
  exact terminal_critical_body_eq_of_marker_rank blue origin p q ha hop hboard hmode hwin
    hfrom hpath hq (hall q w (hfrom.trans hpath) hq) hm hpRank (hfixed q w hpath hq)

#print axioms terminal_critical_body_eq_of_marker_rank
#print axioms strict_critical_leaf_uniformization_of_rank

end Erdos591.Positive.Game.Payoff
