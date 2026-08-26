import ErdosProblems.Erdos591.RootGluingHistory

/-!
# Two-level last--first gluing of actual winning strategy histories

Choose overlapping root labels, obtain both body requests, and only then
choose overlapping body labels. The resulting shared word is at its last
selected leaf in the lower play and its first selected leaf in the upper
play. In particular the lower labeling has no pending selected index.
This is the two-history gluing lemma, not the three-history triangle proof.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact

theorem winning_last_first_gluing_fresh {N H : Set ℕ} (hHN : H ⊆ N) (hH : H.Infinite)
    (blue : SimpleGraph G) {b : Concrete.Hist N → ℕ}
    {σ : (exactGame N blue).ArchitectStrategy} {lower upper : Concrete.Hist N}
    (hwinl : (exactGame N blue).ArchitectWins H b σ lower)
    (hwinu : (exactGame N blue).ArchitectWins H b σ upper) (s t : Bool)
    {a c : ℕ} (ha : 0 < a) (hc : 0 < c)
    (hlower : lower.position.pending = some ⟨s, .advance a⟩)
    (hupper : upper.position.pending = some ⟨t, .advance c⟩)
    (hil : lower.position.board.get s = LabeledWord.initial)
    (hiu : upper.position.board.get t = LabeledWord.initial) :
    ∃ q v, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) lower q ∧
      Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) upper v ∧
      q.position.pending = none ∧ v.position.pending = none ∧
      LabeledWord.SameStructure (q.position.board.get s) (v.position.board.get t) ∧
      (q.position.board.get s).relaxed = true ∧ (v.position.board.get t).relaxed = true ∧
      ¬ Macro.Pending (q.position.board.get s) ∧
      v.position.board.get (!t) = upper.position.board.get (!t) ∧
      ∀ y ∈ (q.position.board.get (!s)).coordinates,
        y ≤ (q.position.board.get s).coordinates.getLastD 0 := by
  let B := max (max lower.position.bound (b lower)) (max upper.position.bound (b upper))
  obtain ⟨L⟩ := LastFirstLabels.exists_of_infinite hH B a c ha hc
  obtain ⟨p, u, d, e, hlp, huu, hp, hu, hd, he, hsame, hmp, hmu, hindex,
      hrootp, _hrootu, hotheru⟩ :=
    winning_root_gluing hHN hH blue hwinl hwinu s t L hlower hupper hil hiu
      (le_max_left _ _) (le_max_right _ _)
  have hwinp := hwinl.of_reachable (exactGame N blue) hlp
  let C := max (max p.position.bound (b p)) (max u.position.bound (b u))
  obtain ⟨D⟩ := LastFirstLabels.exists_of_infinite hH C d e hd he
  obtain ⟨q, v, hpq, huv, hqnone, hvnone, hshape, hqr, hvr, hleaf, hlabels, _hlabelv,
      hotherv, hsep⟩ :=
    winning_body_gluing_fresh hHN hH blue hwinp s t D hp hu hmp hmu hsame
      (le_max_left _ _) (le_max_right _ _)
  have hstart : (p.position.board.get s).parser ≠ .start := by
    obtain ⟨r, hr⟩ := LabeledWord.marker_blocks hmp
    simp [hr]
  obtain ⟨as, has, _⟩ := (History.reachable_word_extension (follow_history_path hpq)).2 s
  have hrootq : (q.position.board.get s).rootLabel = L.lower :=
    (has.rootLabel_eq hstart).trans hrootp
  have hcount : (q.position.board.get s).bodyLabels.length = L.pivot := by
    rw [hlabels, List.length_append, List.length_singleton]
    exact hindex
  have hbound : ∀ i ∈ (q.position.board.get s).rootLabel,
      i ≤ (q.position.board.get s).bodyLabels.length := by
    intro i hi
    rw [hcount]
    exact L.lower_le i (hrootq ▸ hi)
  have hcurrent : (q.position.board.get s).currentLabel = D.lower := by
    simp [LabeledWord.currentLabel, hlabels]
  have hnot := last_selected_leaf_not_pending D hbound hcurrent hleaf
  exact ⟨q, v, hlp.trans hpq, huu.tail huv, hqnone, hvnone, hshape, hqr, hvr,
    hnot, hotherv.trans hotheru, hsep⟩

theorem winning_last_first_gluing {N H : Set ℕ} (hHN : H ⊆ N) (hH : H.Infinite)
    (blue : SimpleGraph G) {b : Concrete.Hist N → ℕ}
    {σ : (exactGame N blue).ArchitectStrategy} {lower upper : Concrete.Hist N}
    (hwinl : (exactGame N blue).ArchitectWins H b σ lower)
    (hwinu : (exactGame N blue).ArchitectWins H b σ upper) (s t : Bool)
    {a c : ℕ} (ha : 0 < a) (hc : 0 < c)
    (hlower : lower.position.pending = some ⟨s, .advance a⟩)
    (hupper : upper.position.pending = some ⟨t, .advance c⟩)
    (hil : lower.position.board.get s = LabeledWord.initial)
    (hiu : upper.position.board.get t = LabeledWord.initial) :
    ∃ q v, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) lower q ∧
      Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) upper v ∧
      q.position.pending = none ∧ v.position.pending = none ∧
      LabeledWord.SameStructure (q.position.board.get s) (v.position.board.get t) ∧
      (q.position.board.get s).relaxed = true ∧ (v.position.board.get t).relaxed = true ∧
      ¬ Macro.Pending (q.position.board.get s) ∧
      v.position.board.get (!t) = upper.position.board.get (!t) := by
  obtain ⟨q, v, hq, hv, hnq, hnv, he, hrq, hrv, hp, ho, _⟩ :=
    winning_last_first_gluing_fresh hHN hH blue hwinl hwinu s t ha hc hlower hupper hil hiu
  exact ⟨q, v, hq, hv, hnq, hnv, he, hrq, hrv, hp, ho⟩

#print axioms winning_last_first_gluing
#print axioms winning_last_first_gluing_fresh

end Erdos591.Positive.Game.Payoff
