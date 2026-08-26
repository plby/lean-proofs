import ErdosProblems.Erdos118.Reused591.CriticalFutureBodyBound
import ErdosProblems.Erdos118.Reused591.FutureBodyLocalization

namespace Erdos118.Reused591

/-!
# The strict spliced anchor has a fixed positive size below the issued last-body size

All terminal estimates are recovered from the original actual inside
opening. The old prefix uses its ambient pool; only future inputs use
the supplied smaller pool. Neither pending body label is read here.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact

theorem strict_spliced_anchor_localization {N H J HU : Set ℕ}
    (hHN : H ⊆ N) (hJH : J ⊆ H) (hJ : J.Infinite) (blue : SimpleGraph G)
    {b : Concrete.Hist N → ℕ} {σ : (exactGame N blue).ArchitectStrategy}
    (origin p : Concrete.Hist N) {a BU e g j k R : ℕ}
    (U : SplicedRootLabels HU BU e g j (k + 1)) (ha : 2 ≤ a) (hkg : k + 1 < g)
    (hop : origin.position.pending = some ⟨false, .advance a⟩)
    (hboard : origin.position.board = Board.initial) (hmode : origin.position.mode = some true)
    (hwin : (exactGame N blue).ArchitectWins H b σ origin)
    (hfrom : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin p)
    (hp : p.position.pending = some ⟨false, .advance R⟩)
    (hm : p.position.board.left.markerEvent = true)
    (hrootLast : ∀ i ∈ p.position.board.left.rootLabel,
      i ≤ p.position.board.left.bodyLabels.length + 1)
    (hUrel : p.position.board.right.relaxed = true)
    (hUroot : p.position.board.right.rootLabel = U.upper)
    (hall : ∀ z w, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin z →
      (exactGame N blue).kind z = .terminal w →
        z.position.board.left.beforeLastLeafCount < z.position.board.right.beforeLastLeafCount)
    (hfixed : ∀ z w, Relation.ReflTransGen ((exactGame N blue).FollowStep σ J b) p z →
      (exactGame N blue).kind z = .terminal w →
        z.position.board.right.criticalBodyRank z.position.board.left.lastSelectedLabel.card = k) :
    ∃ L, L ⊆ J ∧ L.Infinite ∧ ∃ K, 0 < K ∧ K + 2 ≤ R ∧ ∀ z w,
      Relation.ReflTransGen ((exactGame N blue).FollowStep σ L b) p z →
      (exactGame N blue).kind z = .terminal w →
        (z.position.board.right.bodyLabels.getD (U.anchor - 1) ∅).card = K := by
  apply bounded_future_body_localization (hJH.trans hHN) hJ blue p true U.anchor R
  intro z w hpz hz
  have hpzH : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) p z :=
    Relation.ReflTransGen.mono (fun _ _ hs =>
      FiniteResponseGame.FollowStep.mono (exactGame N blue) hJH (fun _ => le_rfl) hs) _ _ hpz
  have hfull := hfrom.trans hpzH
  obtain ⟨s, t, hc, hmax, hfirst, hcardRoot⟩ :=
    terminal_inside_clear_data blue origin z (by omega) hop hboard hmode hwin hfull hz
  have hspec := (hc.strict_critical_data hfirst hmax (by simpa only [hcardRoot] using ha)
    (hall z w hfull hz)).2.1
  obtain ⟨as, has, _⟩ := follow_word_inputs hpz 0 (fun _ => Nat.zero_le _) true
  have hrootZ : z.position.board.right.rootLabel = U.upper :=
    (has.rootLabel_eq (LabeledWord.relaxed_ne_start
      ((Position.history_dataInvariant p).2.1 true).1 hUrel)).trans hUroot
  have hbound := hc.2.1.spliced_anchor_card_bound U hkg hrootZ hspec (hfixed z w hpz hz)
  have hcard := reachable_last_body_label_card blue p z false hp hm hrootLast hpz hz
  change z.position.board.left.lastSelectedLabel.card = R at hcard
  simpa only [Board.get, hcard] using hbound

#print axioms strict_spliced_anchor_localization

theorem terminal_strict_profile_on_subset {N H J : Set ℕ} (hJH : J ⊆ H)
    (blue : SimpleGraph G) {b : Concrete.Hist N → ℕ}
    {σ : (exactGame N blue).ArchitectStrategy} (origin p : Concrete.Hist N) {a k : ℕ}
    (ha : 2 ≤ a) (hop : origin.position.pending = some ⟨false, .advance a⟩)
    (hboard : origin.position.board = Board.initial) (hmode : origin.position.mode = some true)
    (hwin : (exactGame N blue).ArchitectWins H b σ origin)
    (hfrom : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin p)
    (hall : ∀ z w, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin z →
      (exactGame N blue).kind z = .terminal w →
        z.position.board.left.beforeLastLeafCount < z.position.board.right.beforeLastLeafCount)
    (hfixed : ∀ z w, Relation.ReflTransGen ((exactGame N blue).FollowStep σ J b) p z →
      (exactGame N blue).kind z = .terminal w →
        z.position.board.right.criticalBodyRank z.position.board.left.lastSelectedLabel.card = k)
    (hlast : ∀ z w, Relation.ReflTransGen ((exactGame N blue).FollowStep σ J b) p z →
      (exactGame N blue).kind z = .terminal w → criticalLastColor z = true) :
    ∀ z w, Relation.ReflTransGen ((exactGame N blue).FollowStep σ J b) p z →
      (exactGame N blue).kind z = .terminal w →
        z.position.board.right.CriticalPairSpec z.position.board.left.lastSelectedLabel.card
          (z.position.board.right.criticalPair z.position.board.left.lastSelectedLabel.card) ∧
        z.position.board.right.criticalBodyRank z.position.board.left.lastSelectedLabel.card = k ∧
        criticalLastColor z = true := by
  intro z w hpz hz
  have hpzH : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) p z :=
    Relation.ReflTransGen.mono (fun _ _ hs =>
      FiniteResponseGame.FollowStep.mono (exactGame N blue) hJH (fun _ => le_rfl) hs) _ _ hpz
  have hfull := hfrom.trans hpzH
  obtain ⟨s, t, hc, hmax, hfirst, hcard⟩ :=
    terminal_inside_clear_data blue origin z (by omega) hop hboard hmode hwin hfull hz
  exact ⟨(hc.strict_critical_data hfirst hmax (by simpa only [hcard] using ha)
    (hall z w hfull hz)).2.1, hfixed z w hpz hz, hlast z w hpz hz⟩

#print axioms terminal_strict_profile_on_subset

end Erdos591.Positive.Game.Payoff

end Erdos118.Reused591
