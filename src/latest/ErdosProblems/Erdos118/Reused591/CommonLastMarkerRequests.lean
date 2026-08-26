import ErdosProblems.Erdos118.Reused591.PairedMarkerRequests
import ErdosProblems.Erdos118.Reused591.LastLastUpper

namespace Erdos118.Reused591

/-!
# Synchronizing the common last-body marker

The two root labels have a common last selected body. Their current
words are at their respective penultimate endpoints. The retained
fresh prefix permits replay of the older response without changing
either opposite word. Both last-body requests are actual requests.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact

theorem common_last_marker_requests {N H J : Set ℕ}
    (hHN : H ⊆ N) (hH : H.Infinite) (hJH : J ⊆ H) (hJ : J.Infinite)
    (blue : SimpleGraph G) {b : Concrete.Hist N → ℕ}
    {σ : (exactGame N blue).ArchitectStrategy} (old fine : Concrete.Hist N)
    {B a c : ℕ} (L : LastLastLabels H B a c)
    (hwinOld : (exactGame N blue).ArchitectWins H b σ old)
    (hwinFine : (exactGame N blue).ArchitectWins J b σ fine)
    (hpOld : old.position.pending = some ⟨false, .advance 0⟩)
    (hpFine : fine.position.pending = some ⟨false, .advance 0⟩)
    (hrOld : old.position.board.left.rootLabel = L.lower)
    (hbOld : old.position.board.left.bodyLabels.length = L.penultimate)
    (hrelOld : old.position.board.left.relaxed = true)
    (hnoOld : old.position.board.left.NoLeafPending)
    (hrFine : fine.position.board.left.rootLabel = L.upper)
    (hbFine : fine.position.board.left.bodyLabels.length = L.upperPenultimate)
    (hrelFine : fine.position.board.left.relaxed = true)
    (hnoFine : fine.position.board.left.NoLeafPending)
    {frontAtoms : List (Finset ℕ × ℕ)}
    (hfront : LabeledWord.LegalRun (LabeledWord.rootRelabel L.upper old.position.board.left)
      frontAtoms fine.position.board.left)
    (hfrontPool : ∀ atom ∈ frontAtoms,
      atom.2 ∈ H ∧ max old.position.bound (b old) < atom.2)
    (hJfresh : ∀ x ∈ J, max old.position.bound (b old) < x) :
    ∃ st su p q,
      Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) old st ∧
      Relation.ReflTransGen ((exactGame N blue).FollowStep σ J b) fine su ∧
      st.position.pending = some ⟨false, .advance p⟩ ∧
      su.position.pending = some ⟨false, .advance q⟩ ∧ 0 < p ∧ 0 < q ∧
      LabeledWord.SameStructure st.position.board.left su.position.board.left ∧
      st.position.board.left.markerEvent = true ∧ su.position.board.left.markerEvent = true ∧
      st.position.board.left.bodyLabels.length + 1 = L.pivot ∧
      su.position.board.left.bodyLabels.length + 1 = L.pivot ∧
      st.position.board.left.rootLabel = L.lower ∧ su.position.board.left.rootLabel = L.upper ∧
      (∀ k ∈ st.position.board.left.rootLabel,
        k ≤ st.position.board.left.bodyLabels.length + 1) ∧
      (∀ k ∈ su.position.board.left.rootLabel,
        k ≤ su.position.board.left.bodyLabels.length + 1) ∧
      st.position.board.right = old.position.board.right ∧
      su.position.board.right = fine.position.board.right := by
  have hbeforeOld : LabeledWord.BeforeBody L.pivot old.position.board.left :=
    ⟨hrOld ▸ L.pivot_lower, by simpa only [hbOld] using L.penultimate_lt_pivot⟩
  have hnextOld : ∀ k ∈ old.position.board.left.rootLabel,
      old.position.board.left.bodyLabels.length < k → L.pivot ≤ k := by
    intro k hk hlt
    rcases L.lower_bounds k (hrOld ▸ hk) with heq | hle
    · exact heq.ge
    · rw [hbOld] at hlt
      exact (not_lt_of_ge hle hlt).elim
  have hbeforeFine : LabeledWord.BeforeBody L.pivot fine.position.board.left :=
    ⟨hrFine ▸ L.pivot_upper, by simpa only [hbFine] using L.upperPenultimate_lt_pivot⟩
  have hnextFine : ∀ k ∈ fine.position.board.left.rootLabel,
      fine.position.board.left.bodyLabels.length < k → L.pivot ≤ k := by
    intro k hk hlt
    rcases L.upper_bounds_penultimate k (hrFine ▸ hk) with heq | hle
    · exact heq.ge
    · rw [hbFine] at hlt
      exact (not_lt_of_ge hle hlt).elim
  obtain ⟨st, su, p, q, hst, hsu, hp, hq, hposp, hposq, hsame, hmst, hmsu,
      hist, hisu, hrst, hrsu, host, hosu⟩ :=
    paired_next_marker_requests hHN hH hJH hJ blue old fine hwinOld hwinFine false false
      hpOld hpFine (LabeledWord.rootRelabel_sameStructure L.upper old.position.board.left).symm
      hfront hfrontPool hJfresh hrelOld hnoOld hbeforeOld hnextOld
      hrelFine hnoFine hbeforeFine hnextFine
  change st.position.board.left.rootLabel = old.position.board.left.rootLabel at hrst
  change su.position.board.left.rootLabel = fine.position.board.left.rootLabel at hrsu
  change st.position.board.left.bodyLabels.length + 1 = L.pivot at hist
  change su.position.board.left.bodyLabels.length + 1 = L.pivot at hisu
  refine ⟨st, su, p, q, hst, hsu, hp, hq, hposp, hposq, hsame, hmst, hmsu, hist,
    hisu, hrst.trans hrOld, hrsu.trans hrFine, ?_, ?_, host, hosu⟩
  · intro k hk
    rw [hist]
    exact L.lower_le_pivot k (by simpa only [hrst, hrOld] using hk)
  · intro k hk
    rw [hisu]
    exact (L.upper_bounds k (by simpa only [hrsu, hrFine] using hk)).2

#print axioms common_last_marker_requests

end Erdos591.Positive.Game.Payoff

end Erdos118.Reused591
