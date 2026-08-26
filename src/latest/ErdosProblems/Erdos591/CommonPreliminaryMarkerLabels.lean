import ErdosProblems.Erdos591.CommonLastMarkerRequests
import ErdosProblems.Erdos591.CriticalPreliminaryRequestBound
import ErdosProblems.Erdos591.PreliminaryPivotLabels

/-!
# Actual common last-body requests and full labels for the preliminary phases

The two old critical checkpoints precede their actual last-S-body
requests. Their remaining critical-body leaf counts bound any requested
preliminary group sizes. Only after both response bounds and sizes are
known are the two full S labels chosen from the current future pool.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact

theorem common_preliminary_marker_labels {N H J : Set ℕ}
    (hHN : H ⊆ N) (hJH : J ⊆ H) (hJ : J.Infinite) (blue : SimpleGraph G)
    {b : Concrete.Hist N → ℕ} {σ : (exactGame N blue).ArchitectStrategy}
    (origin old fine : Concrete.Hist N) {B a r t : ℕ}
    (S : LastLastLabels H B a) (ha : 2 ≤ a)
    (hop : origin.position.pending = some ⟨false, .advance a⟩)
    (hboard : origin.position.board = Board.initial) (hmode : origin.position.mode = some true)
    (hwin : (exactGame N blue).ArchitectWins H b σ origin)
    (hfromOld : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin old)
    (hfromFine : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin fine)
    (hOld : CriticalCheckpoint old) (hFine : CriticalCheckpoint fine)
    (hpOld : old.position.pending = some ⟨false, .advance 0⟩)
    (hpFine : fine.position.pending = some ⟨false, .advance 0⟩)
    (hrOld : old.position.board.left.rootLabel = S.lower)
    (hbOld : old.position.board.left.bodyLabels.length = S.penultimate)
    (hrFine : fine.position.board.left.rootLabel = S.upper)
    (hbFine : fine.position.board.left.bodyLabels.length = S.upperPenultimate)
    (hr : r ≤ old.position.board.right.currentLabel.card -
      (old.position.board.right.currentLabel.filter
        (fun x => x ≤ old.position.board.right.leafIndex)).card)
    (ht : t ≤ fine.position.board.right.currentLabel.card -
      (fine.position.board.right.currentLabel.filter
        (fun x => x ≤ fine.position.board.right.leafIndex)).card)
    (hall : ∀ z w, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin z →
      (exactGame N blue).kind z = .terminal w →
        z.position.board.left.beforeLastLeafCount < z.position.board.right.beforeLastLeafCount)
    {frontAtoms : List (Finset ℕ × ℕ)}
    (hfront : LabeledWord.LegalRun (LabeledWord.rootRelabel S.upper old.position.board.left)
      frontAtoms fine.position.board.left)
    (hfrontPool : ∀ atom ∈ frontAtoms,
      atom.2 ∈ H ∧ max old.position.bound (b old) < atom.2)
    (hJfresh : ∀ x ∈ J, max old.position.bound (b old) < x) :
    ∃ st su p q D, ∃ _L : PreliminaryPivotLabels J D p q r t,
      r + 2 ≤ p ∧ t + 2 ≤ q ∧
      Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) old st ∧
      Relation.ReflTransGen ((exactGame N blue).FollowStep σ J b) fine su ∧
      Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin st ∧
      Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin su ∧
      (exactGame N blue).ArchitectWins J b σ st ∧
      (exactGame N blue).ArchitectWins J b σ su ∧
      st.position.pending = some ⟨false, .advance p⟩ ∧
      su.position.pending = some ⟨false, .advance q⟩ ∧
      LabeledWord.SameStructure st.position.board.left su.position.board.left ∧
      st.position.board.left.markerEvent = true ∧ su.position.board.left.markerEvent = true ∧
      st.position.board.left.bodyLabels.length + 1 = S.pivot ∧
      su.position.board.left.bodyLabels.length + 1 = S.pivot ∧
      st.position.board.left.rootLabel = S.lower ∧ su.position.board.left.rootLabel = S.upper ∧
      (∀ k ∈ st.position.board.left.rootLabel,
        k ≤ st.position.board.left.bodyLabels.length + 1) ∧
      (∀ k ∈ su.position.board.left.rootLabel,
        k ≤ su.position.board.left.bodyLabels.length + 1) ∧
      st.position.board.right = old.position.board.right ∧
      su.position.board.right = fine.position.board.right ∧
      max st.position.bound (b st) ≤ D ∧ max su.position.bound (b su) ≤ D := by
  have hwinFine := (hwin.of_reachable (exactGame N blue) hfromFine).mono
    (exactGame N blue) hJH (fun _ => le_rfl)
  obtain ⟨st, su, p, q, hOldST, hFineSU, hpST, hpSU, _hp, _hq, hshape, hmST, hmSU,
      hiST, hiSU, hrST, hrSU, hrootST, hrootSU, hoST, hoSU⟩ :=
    common_last_marker_requests hHN (hJ.mono hJH) hJH hJ blue old fine S
      (hwin.of_reachable (exactGame N blue) hfromOld) hwinFine hpOld hpFine
      hrOld hbOld hOld.left_relaxed hOld.left_exhausted hrFine hbFine
      hFine.left_relaxed hFine.left_exhausted hfront hfrontPool hJfresh
  have hFineSUH : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) fine su :=
    Relation.ReflTransGen.mono (fun _ _ hs => FiniteResponseGame.FollowStep.mono
      (exactGame N blue) hJH (fun _ => le_rfl) hs) _ _ hFineSU
  have hfromST := hfromOld.trans hOldST
  have hfromSU := hfromFine.trans hFineSUH
  have hboundST := critical_preliminary_request_bound hHN hJH hJ blue origin old st ha
    hop hboard hmode hwin hfromOld hOldST hOld hpST hmST hrootST hall
  have hboundSU := critical_preliminary_request_bound hHN hJH hJ blue origin fine su ha
    hop hboard hmode hwin hfromFine hFineSUH hFine hpSU hmSU hrootSU hall
  have hpLarge : r + 2 ≤ p := by omega
  have hqLarge : t + 2 ≤ q := by omega
  let D := max (max st.position.bound (b st)) (max su.position.bound (b su))
  obtain ⟨L⟩ := PreliminaryPivotLabels.exists_of_infinite hJ D p q r t hpLarge hqLarge
  exact ⟨st, su, p, q, D, L, hpLarge, hqLarge, hOldST, hFineSU, hfromST, hfromSU,
    (hwin.of_reachable (exactGame N blue) hfromST).mono
      (exactGame N blue) hJH (fun _ => le_rfl), hwinFine.of_reachable (exactGame N blue) hFineSU,
    hpST, hpSU, hshape, hmST, hmSU, hiST, hiSU, hrST, hrSU, hrootST, hrootSU,
    hoST, hoSU, le_max_left _ _, le_max_right _ _⟩

#print axioms common_preliminary_marker_labels

end Erdos591.Positive.Game.Payoff
