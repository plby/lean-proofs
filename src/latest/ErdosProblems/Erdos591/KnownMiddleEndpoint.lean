import ErdosProblems.Erdos591.KnownLastLeafCheckpoint
import ErdosProblems.Erdos591.ReachSelectedLeaf
import ErdosProblems.Erdos591.LastBodyEndpoint

/-!
# Exhaust the middle selections after both last-body labels have been read

Reach the penultimate first-word selection, take exactly the next
opposite leaf, and leave the common final leaf pending. The opposite
last-body label and marker remain the originally stored ones.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact

theorem known_middle_endpoint {N H : Set ℕ}
    (hHN : H ⊆ N) (hH : H.Infinite) (blue : SimpleGraph G)
    {b : Concrete.Hist N → ℕ} {σ : (exactGame N blue).ArchitectStrategy}
    {p : Concrete.Hist N} (hwin : (exactGame N blue).ArchitectWins H b σ p)
    (hmode : p.position.mode = some true) {k j : ℕ}
    (hk : LabeledWord.UpToLeaf k p.position.board.left) (hkj : k < j)
    (hj : j ∈ p.position.board.left.currentLabel)
    (hleaves : ∀ i ∈ p.position.board.left.currentLabel, i = j ∨ i ≤ k)
    (hrootS : ∀ i ∈ p.position.board.left.rootLabel, i ≤ p.position.board.left.bodyLabels.length)
    (hrelT : p.position.board.right.relaxed = true)
    (hrootT : ∀ i ∈ p.position.board.right.rootLabel, i ≤ p.position.board.right.bodyLabels.length)
    (hentry : p.position.board.left.leafIndex < k ∨ (p.position.pending = none ∧
      ∀ y ∈ p.position.board.right.coordinates, y ≤ p.position.board.left.coordinates.getLastD 0)) :
    ∃ q, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) p q ∧
      q.position.pending = some ⟨false, .advance 0⟩ ∧
      q.position.board.left.relaxed = true ∧ q.position.board.left.leafIndex = k ∧
      q.position.board.left.bodyLabels = p.position.board.left.bodyLabels ∧
      q.position.board.left.bodyMarker = p.position.board.left.bodyMarker ∧
      q.position.board.right.relaxed = true ∧ ¬ Macro.Pending q.position.board.right ∧
      q.position.board.right.bodyLabels = p.position.board.right.bodyLabels ∧
      q.position.board.right.bodyMarker = p.position.board.right.bodyMarker ∧
      q.position.board.right.leafIndex = p.position.board.right.currentLabel.sup id := by
  obtain ⟨v, hpv, hvn, hvr, hvi, hvb, hvm, hvsep⟩ :
      ∃ v, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) p v ∧
        v.position.pending = none ∧ v.position.board.left.relaxed = true ∧
        v.position.board.left.leafIndex = k ∧
        v.position.board.left.bodyLabels = p.position.board.left.bodyLabels ∧
        v.position.board.left.bodyMarker = p.position.board.left.bodyMarker ∧
        ∀ y ∈ v.position.board.right.coordinates,
          y ≤ v.position.board.left.coordinates.getLastD 0 := by
    rcases hentry with hlt | ⟨hn, hsep⟩
    · simpa only [Board.get, Bool.not_false] using
        winning_reach_selected_leaf_fresh hHN hH blue hwin false k hk hlt
    · simpa only [Board.get, Bool.not_false] using
        winning_reach_selected_leaf_le_fresh hHN hH blue hwin false k hn hk hsep
  obtain ⟨r, l, hparse⟩ := hk.parser_leaves ((Position.history_dataInvariant p).2.1 false).1
  have hstartS : p.position.board.left.parser ≠ .start := by simp [hparse]
  have hstartT := LabeledWord.relaxed_ne_start
    ((Position.history_dataInvariant p).2.1 true).1 hrelT
  obtain ⟨as, has, _⟩ := follow_word_inputs hpv 0 (fun _ => Nat.zero_le _) false
  obtain ⟨bs, hbs, _⟩ := follow_word_inputs hpv 0 (fun _ => Nat.zero_le _) true
  have hvrootS : v.position.board.left.rootLabel = p.position.board.left.rootLabel :=
    has.rootLabel_eq hstartS
  have hvrootT : v.position.board.right.rootLabel = p.position.board.right.rootLabel :=
    hbs.rootLabel_eq hstartT
  have hvcurrent : v.position.board.left.currentLabel = p.position.board.left.currentLabel := by
    simp only [LabeledWord.currentLabel, hvb]
  have hvtarget : LabeledWord.UpToLeaf j v.position.board.left :=
    ⟨(of_decide_eq_true hvr).2.1, hvcurrent ▸ hj, by rw [hvi]; exact hkj.le⟩
  have hvnext : ∀ i ∈ v.position.board.left.currentLabel,
      v.position.board.left.leafIndex < i → j ≤ i := by
    intro i hi hlt
    rcases hleaves i (hvcurrent ▸ hi) with heq | hle
    · exact heq.ge
    · rw [hvi] at hlt
      exact (not_lt_of_ge hle hlt).elim
  have hvlast : ∀ i ∈ v.position.board.left.currentLabel, i ≤ j := by
    intro i hi
    exact (hleaves i (hvcurrent ▸ hi)).elim Eq.le (fun hle => hle.trans hkj.le)
  have hvTroot : ∀ i ∈ v.position.board.right.rootLabel,
      i ≤ v.position.board.right.bodyLabels.length := by
    intro i hi
    exact (hrootT i (hvrootT ▸ hi)).trans (hbs.bodyLabels_prefix hstartT).length_le
  have hvposT : 0 < v.position.board.right.coordinates.length := by
    obtain ⟨cs, hcs⟩ := History.word_run p true
    exact (hcs.relaxed_coordinates_pos hrelT).trans_le hbs.coordinates_prefix.length_le
  obtain ⟨q, hvq, hpq, hql, hqr, hqLast⟩ := known_last_leaf_checkpoint hHN hH blue
    (hwin.of_reachable (exactGame N blue) hpv) (follow_mode_some hpv hmode) hvn hvr hvsep
    hvtarget (by rw [hvi]; exact hkj) hvnext
    (by simpa only [hvrootS, hvb] using hrootS) hvlast hvTroot hvposT
  have hpath := hpv.trans hvq
  obtain ⟨ds, hds, _⟩ := follow_word_inputs hpath 0 (fun _ => Nat.zero_le _) true
  obtain ⟨hlabels, hmarker, hidx⟩ :=
    hds.last_body_relaxed_endpoint hstartT hrootT hqr hqLast
  exact ⟨q, hpath, hpq, by simpa only [hql] using hvr, by simpa only [hql] using hvi,
    by simpa only [hql] using hvb, by simpa only [hql] using hvm, hqr, hqLast,
    hlabels, hmarker, hidx⟩

#print axioms known_middle_endpoint

end Erdos591.Positive.Game.Payoff
