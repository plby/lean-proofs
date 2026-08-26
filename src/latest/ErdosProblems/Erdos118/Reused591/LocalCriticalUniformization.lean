import ErdosProblems.Erdos118.Reused591.FixedBoundThinning
import ErdosProblems.Erdos118.Reused591.StrictBodyLocalization
import ErdosProblems.Erdos118.Reused591.CriticalMarkerLocalization

namespace Erdos118.Reused591

/-!
# Critical localization below a fixed prefix on a separate future pool

`H` contains the already played history. Only future inputs are thinned
inside `K ⊆ H`. The bound stays `b`; neither the origin-to-prefix path nor
the strategy is changed. This interface permits successive localizations
at different pending requests without reassigning old inputs to a new pool.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact

theorem strict_critical_body_local {N H K : Set ℕ}
    (hHN : H ⊆ N) (hKH : K ⊆ H) (hK : K.Infinite) (blue : SimpleGraph G)
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
    ∃ L, L ⊆ K ∧ L.Infinite ∧ ∃ j : ℕ, 0 < j ∧ j < e ∧ ∀ q w,
      Relation.ReflTransGen ((exactGame N blue).FollowStep σ L b) p q →
      (exactGame N blue).kind q = .terminal w →
        q.position.board.right.criticalBodyRank q.position.board.left.lastSelectedLabel.card = j ∧
          (criticalLastColor q = true → j + 1 < e) := by
  obtain ⟨L, hLK, hL, value, hvalue⟩ :=
    Concrete.terminal_finite_uniformization_fixed_bound (hKH.trans hHN) hK b σ
      (criticalBodyColor e) p
  have paths {u v : Concrete.Hist N}
      (hpath : Relation.ReflTransGen ((exactGame N blue).FollowStep σ L b) u v) :
      Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) u v :=
    Relation.ReflTransGen.mono (fun _ _ hs =>
      FiniteResponseGame.FollowStep.mono (exactGame N blue) (hLK.trans hKH)
        (fun _ => le_rfl) hs) _ _ hpath
  have data (q : Concrete.Hist N) (w : Bool)
      (hpath : Relation.ReflTransGen ((exactGame N blue).FollowStep σ L b) p q)
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
      (hpath : Relation.ReflTransGen ((exactGame N blue).FollowStep σ L b) p q)
      (hq : (exactGame N blue).kind q = .terminal w) :
      q.position.board.right.criticalBodyRank q.position.board.left.lastSelectedLabel.card =
        value.val := by
    have hc := congrArg Fin.val (hvalue q w hpath hq)
    simpa only [criticalBodyColor, min_eq_left (data q w hpath hq).2.1.le] using hc
  obtain ⟨q₀, w₀, hpq₀, hq₀⟩ := (exactGame N blue).terminal_reachable_of_infinite
    ((hLK.trans hKH).trans hHN) hL b σ p
  have hdata := data q₀ w₀ hpq₀ hq₀
  rw [fixed q₀ w₀ hpq₀ hq₀] at hdata
  refine ⟨L, hLK, hL, value.val, hdata.1, hdata.2.1, ?_⟩
  intro q w hpath hq
  have heq := fixed q w hpath hq
  exact ⟨heq, by simpa only [heq] using (data q w hpath hq).2.2⟩

theorem strict_critical_leaf_local {N H K : Set ℕ}
    (hHN : H ⊆ N) (hKH : K ⊆ H) (hK : K.Infinite) (blue : SimpleGraph G)
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
    (hbody : ∀ q w, Relation.ReflTransGen ((exactGame N blue).FollowStep σ K b) p q →
      (exactGame N blue).kind q = .terminal w →
        (q.position.board.right.criticalPair q.position.board.left.lastSelectedLabel.card).1 =
          p.position.board.right.bodyLabels.length + 1) :
    ∃ L, L ⊆ K ∧ L.Infinite ∧ ∃ s : ℕ, 0 < s ∧ s ≤ d ∧ ∀ q w,
      Relation.ReflTransGen ((exactGame N blue).FollowStep σ L b) p q →
      (exactGame N blue).kind q = .terminal w →
        q.position.board.right.criticalLeafRank q.position.board.left.lastSelectedLabel.card = s ∧
          (criticalLastColor q = true ↔ s = d) := by
  obtain ⟨L, hLK, hL, value, hvalue⟩ :=
    Concrete.terminal_finite_uniformization_fixed_bound (hKH.trans hHN) hK b σ
      (criticalLeafColor d) p
  have paths {u v : Concrete.Hist N}
      (hpath : Relation.ReflTransGen ((exactGame N blue).FollowStep σ L b) u v) :
      Relation.ReflTransGen ((exactGame N blue).FollowStep σ K b) u v :=
    Relation.ReflTransGen.mono (fun _ _ hs =>
      FiniteResponseGame.FollowStep.mono (exactGame N blue) hLK (fun _ => le_rfl) hs) _ _ hpath
  have pathsH {u v : Concrete.Hist N}
      (hpath : Relation.ReflTransGen ((exactGame N blue).FollowStep σ K b) u v) :
      Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) u v :=
    Relation.ReflTransGen.mono (fun _ _ hs =>
      FiniteResponseGame.FollowStep.mono (exactGame N blue) hKH (fun _ => le_rfl) hs) _ _ hpath
  have data (q : Concrete.Hist N) (w : Bool)
      (hpath : Relation.ReflTransGen ((exactGame N blue).FollowStep σ L b) p q)
      (hq : (exactGame N blue).kind q = .terminal w) :
      0 < q.position.board.right.criticalLeafRank q.position.board.left.lastSelectedLabel.card ∧
        q.position.board.right.criticalLeafRank q.position.board.left.lastSelectedLabel.card ≤ d ∧
        (criticalLastColor q = true ↔
          q.position.board.right.criticalLeafRank
            q.position.board.left.lastSelectedLabel.card = d) := by
    have hfull := hfrom.trans (pathsH (paths hpath))
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
      (hpath : Relation.ReflTransGen ((exactGame N blue).FollowStep σ L b) p q)
      (hq : (exactGame N blue).kind q = .terminal w) :
      q.position.board.right.criticalLeafRank q.position.board.left.lastSelectedLabel.card =
        value.val := by
    have hc := congrArg Fin.val (hvalue q w hpath hq)
    simpa only [criticalLeafColor, min_eq_left (data q w hpath hq).2.1] using hc
  obtain ⟨q₀, w₀, hpq₀, hq₀⟩ := (exactGame N blue).terminal_reachable_of_infinite
    ((hLK.trans hKH).trans hHN) hL b σ p
  have hdata := data q₀ w₀ hpq₀ hq₀
  rw [fixed q₀ w₀ hpq₀ hq₀] at hdata
  refine ⟨L, hLK, hL, value.val, hdata.1, hdata.2.1, ?_⟩
  intro q w hpath hq
  have heq := fixed q w hpath hq
  exact ⟨heq, by simpa only [heq] using (data q w hpath hq).2.2⟩

theorem strict_critical_leaf_local_of_rank {N H K : Set ℕ}
    (hHN : H ⊆ N) (hKH : K ⊆ H) (hK : K.Infinite) (blue : SimpleGraph G)
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
    (hfixed : ∀ q w, Relation.ReflTransGen ((exactGame N blue).FollowStep σ K b) p q →
      (exactGame N blue).kind q = .terminal w →
        q.position.board.right.criticalBodyRank q.position.board.left.lastSelectedLabel.card = j) :
    ∃ L, L ⊆ K ∧ L.Infinite ∧ ∃ s : ℕ, 0 < s ∧ s ≤ d ∧ ∀ q w,
      Relation.ReflTransGen ((exactGame N blue).FollowStep σ L b) p q →
      (exactGame N blue).kind q = .terminal w →
        q.position.board.right.criticalLeafRank q.position.board.left.lastSelectedLabel.card = s ∧
          (criticalLastColor q = true ↔ s = d) := by
  apply strict_critical_leaf_local hHN hKH hK blue origin p ha hop hboard hmode hwin
    hfrom hp hm hall
  intro q w hpath hq
  have hpathH : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) p q :=
    Relation.ReflTransGen.mono (fun _ _ hs =>
      FiniteResponseGame.FollowStep.mono (exactGame N blue) hKH (fun _ => le_rfl) hs) _ _ hpath
  exact terminal_critical_body_eq_of_marker_rank blue origin p q ha hop hboard hmode hwin
    hfrom hpathH hq (hall q w (hfrom.trans hpathH) hq) hm hpRank (hfixed q w hpath hq)

#print axioms strict_critical_body_local
#print axioms strict_critical_leaf_local
#print axioms strict_critical_leaf_local_of_rank

end Erdos591.Positive.Game.Payoff

end Erdos118.Reused591
