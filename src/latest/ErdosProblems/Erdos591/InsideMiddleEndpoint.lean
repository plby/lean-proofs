import ErdosProblems.Erdos591.InsideLastLeafCheckpoint
import ErdosProblems.Erdos591.ManagedReach

/-!
# Reach a middle-phase endpoint while retaining the final common leaf

Exhaust the nonlast selected first-word leaves through their greatest
index, keeping the opposite delayed play managed. Its next selected
leaf is its last, by the final-leaf test. The common final first-word
coordinate has not yet been submitted.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact
open Relay

theorem inside_middle_endpoint {N H : Set ℕ}
    (hHN : H ⊆ N) (hH : H.Infinite) (blue : SimpleGraph G)
    {b : Concrete.Hist N → ℕ} {σ : (exactGame N blue).ArchitectStrategy}
    {p : Concrete.Hist N} (hwin : (exactGame N blue).ArchitectWins H b σ p)
    (hmode : p.position.mode = some true) (hnone : p.position.pending = none)
    (hsep : ∀ y ∈ p.position.board.right.coordinates,
      y ≤ p.position.board.left.coordinates.getLastD 0)
    {k j : ℕ} (hk : LabeledWord.UpToLeaf k p.position.board.left) (hkj : k < j)
    (hj : j ∈ p.position.board.left.currentLabel)
    (hleaves : ∀ i ∈ p.position.board.left.currentLabel, i = j ∨ i ≤ k)
    (hrootLast : ∀ i ∈ p.position.board.left.rootLabel,
      i ≤ p.position.board.left.bodyLabels.length)
    {t mode : Bool} {other : LabeledWord} (upperOrigin : Concrete.Hist N)
    (hmanaged : ∃ M : Managed N H blue b σ t mode other p.position.board.right,
      Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) upperOrigin M.target) :
    ∃ q, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) p q ∧
      q.position.pending = some ⟨false, .advance 0⟩ ∧
      q.position.board.left.relaxed = true ∧ q.position.board.left.leafIndex = k ∧
      q.position.board.left.bodyLabels = p.position.board.left.bodyLabels ∧
      q.position.board.left.bodyMarker = p.position.board.left.bodyMarker ∧
      q.position.board.right.relaxed = true ∧ ¬ Macro.Pending q.position.board.right ∧
      ∃ M : Managed N H blue b σ t mode other q.position.board.right,
        Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) upperOrigin M.target := by
  obtain ⟨v, hpv, hvn, hvr, hvi, hlabels, hmarker, hvsep, hMv⟩ :=
    managed_reach_selected_leaf_le_from hHN hH blue hwin false k hnone hk hsep
      upperOrigin hmanaged
  change v.position.board.left.relaxed = true at hvr
  change v.position.board.left.leafIndex = k at hvi
  change v.position.board.left.bodyLabels = p.position.board.left.bodyLabels at hlabels
  change v.position.board.left.bodyMarker = p.position.board.left.bodyMarker at hmarker
  have hcurrent : v.position.board.left.currentLabel = p.position.board.left.currentLabel := by
    simp [LabeledWord.currentLabel, hlabels]
  obtain ⟨r, l, hparse⟩ := hk.parser_leaves ((Position.history_dataInvariant p).2.1 false).1
  obtain ⟨as, has, _⟩ := follow_word_inputs hpv 0 (fun _ => Nat.zero_le _) false
  have hroot : v.position.board.left.rootLabel = p.position.board.left.rootLabel :=
    has.rootLabel_eq (by simp [Board.get, hparse])
  have hrootV : ∀ i ∈ v.position.board.left.rootLabel,
      i ≤ v.position.board.left.bodyLabels.length := by
    simpa only [hroot, hlabels] using hrootLast
  have htarget : LabeledWord.UpToLeaf j v.position.board.left :=
    ⟨(of_decide_eq_true hvr).2.1, hcurrent ▸ hj, by rw [hvi]; exact hkj.le⟩
  have hnext : ∀ i ∈ v.position.board.left.currentLabel,
      v.position.board.left.leafIndex < i → j ≤ i := by
    intro i hi hlt
    rcases hleaves i (hcurrent ▸ hi) with heq | hle
    · exact heq.ge
    · rw [hvi] at hlt
      exact (not_lt_of_ge hle hlt).elim
  have hlast : ∀ i ∈ v.position.board.left.currentLabel, i ≤ j := by
    intro i hi
    exact (hleaves i (hcurrent ▸ hi)).elim (fun he => he.le) (fun he => he.trans hkj.le)
  obtain ⟨q, hvq, hp, hleft, hright, _hqsep, hdone, Mq, hMq⟩ :=
    inside_last_leaf_checkpoint hHN hH blue (hwin.of_reachable (exactGame N blue) hpv)
      (follow_mode_some hpv hmode) hvr hvsep htarget (by rw [hvi]; exact hkj)
      hnext hrootV hlast upperOrigin hMv
  exact ⟨q, hpv.trans hvq, hp, by simpa only [hleft] using hvr,
    by simpa only [hleft] using hvi, by simpa only [hleft] using hlabels,
    by simpa only [hleft] using hmarker, hright, hdone, Mq, hMq⟩

#print axioms inside_middle_endpoint

end Erdos591.Positive.Game.Payoff
