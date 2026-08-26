import ErdosProblems.Erdos118.Reused591.NonlastPreparedAnchorTriangle
import ErdosProblems.Erdos118.Reused591.PairedMarkerRequests
import ErdosProblems.Erdos118.Reused591.CriticalPreliminaryRequestBound
import ErdosProblems.Erdos118.Reused591.CriticalOpeningHandoff

namespace Erdos118.Reused591

/-! # The saved U checkpoint through both actual T marker requests and the triangle -/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact
open Relay

theorem nonlast_prepared_checkpoint_triangle {N H0 H HU : Set ℕ}
    (hH0N : H0 ⊆ N) (hHH0 : H ⊆ H0) (hH : H.Infinite) (blue : SimpleGraph G)
    {b : Concrete.Hist N → ℕ} {σ : (exactGame N blue).ArchitectStrategy}
    (origin checkpoint oldT : Concrete.Hist N) {a BU e g j k i : ℕ}
    (U : SplicedRootLabels HU BU e g j k)
    (PU : PreparedSelection N H blue b σ checkpoint.position.board.right)
    (ha : 2 ≤ a) (hAfterU : k < g)
    (hop : origin.position.pending = some ⟨false, .advance a⟩)
    (hboard : origin.position.board = Board.initial) (hmode : origin.position.mode = some true)
    (hwin : (exactGame N blue).ArchitectWins H0 b σ origin)
    (hfrom : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H0 b) origin checkpoint)
    (hCheckpoint : CriticalCheckpoint checkpoint)
    (hwinOldT : (exactGame N blue).ArchitectWins H b σ oldT)
    (hModeSU : PU.target.position.mode = some true) (hPUside : PU.side = true)
    (hpOld : oldT.position.pending = some ⟨true, .advance 0⟩)
    (hrelOld : oldT.position.board.right.relaxed = true)
    (hnoOld : oldT.position.board.right.NoLeafPending)
    (hbeforeOld : LabeledWord.BeforeBody i oldT.position.board.right)
    (hnextOld : ∀ m ∈ oldT.position.board.right.rootLabel,
      oldT.position.board.right.bodyLabels.length < m → i ≤ m)
    {anchor : LabeledWord} {front : List (Finset ℕ × ℕ)}
    (hshape : LabeledWord.SameStructure oldT.position.board.right anchor)
    (hfront : LabeledWord.LegalRun anchor front checkpoint.position.board.left)
    (hpool : ∀ atom ∈ front, atom.2 ∈ H ∧ max oldT.position.bound (b oldT) < atom.2)
    (hFresh : ∀ x ∈ H, max oldT.position.bound (b oldT) < x)
    (hlastT : checkpoint.position.board.left.lastSelectedBody = i)
    (hUlt : checkpoint.position.board.right.leafIndex <
      checkpoint.position.board.right.currentLabel.sup id)
    (hPUpivot : PU.labels.pivot = checkpoint.position.board.right.currentLabel.sup id)
    (hUroot : checkpoint.position.board.right.rootLabel = U.upper)
    (hUbody : checkpoint.position.board.right.bodyLabels.length = U.anchor)
    (hLowerRoot : PU.target.position.board.right.rootLabel = U.lower)
    (hall : ∀ z w, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H0 b) origin z →
      (exactGame N blue).kind z = .terminal w →
        z.position.board.left.beforeLastLeafCount < z.position.board.right.beforeLastLeafCount)
    (hSrel : PU.target.position.board.left.relaxed = true)
    (hS : LabeledWord.SameStructure oldT.position.board.left PU.target.position.board.left)
    {gamma : ℕ} (hSUp : LabeledWord.UpToLeaf gamma oldT.position.board.left)
    (hSstrict : oldT.position.board.left.leafIndex < gamma)
    (hSnext : ∀ m ∈ oldT.position.board.left.currentLabel,
      oldT.position.board.left.leafIndex < m → gamma ≤ m)
    (hSroot : ∀ m ∈ PU.target.position.board.left.rootLabel,
      m ≤ PU.target.position.board.left.bodyLabels.length)
    (hgamma : gamma ∈ PU.target.position.board.left.currentLabel)
    (hSlast : ∀ m ∈ PU.target.position.board.left.currentLabel, m ≤ gamma) :
    ¬ blue.CliqueFree 3 := by
  have hHN := hHH0.trans hH0N
  have pathH0 {v w : Concrete.Hist N}
      (hp : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) v w) :
      Relation.ReflTransGen ((exactGame N blue).FollowStep σ H0 b) v w :=
    Relation.ReflTransGen.mono (fun _ _ hs =>
      FiniteResponseGame.FollowStep.mono (exactGame N blue) hHH0 (fun _ => le_rfl) hs) _ _ hp
  have hwinC := (hwin.of_reachable (exactGame N blue) hfrom).mono
    (exactGame N blue) hHH0 (fun _ => le_rfl)
  have hmem : i ∈ checkpoint.position.board.left.rootLabel := by
    rw [← hlastT]
    simpa [LabeledWord.lastSelectedBody] using Finset.sup_mem_of_nonempty (f := id)
      ⟨_, (of_decide_eq_true hCheckpoint.left_relaxed).2.1⟩
  have hbefore : LabeledWord.BeforeBody i checkpoint.position.board.left :=
    ⟨hmem, by simpa only [hlastT] using hCheckpoint.left_before⟩
  have hnext : ∀ m ∈ checkpoint.position.board.left.rootLabel,
      checkpoint.position.board.left.bodyLabels.length < m → i ≤ m := by
    intro m hm hlt
    by_contra hn
    have hle := hCheckpoint.left_penultimate m hm
      (by simpa only [hlastT] using lt_of_not_ge hn)
    omega
  obtain ⟨v, hcv, hVboard, hpV⟩ := winning_next_body_after_fresh_leaf hHN hH blue hwinC true
    hCheckpoint.right_relaxed hCheckpoint.separation hCheckpoint.left_relaxed hbefore
  obtain ⟨st, upper, D, R, hOldST, hVupper, hpST, hpUpper, hD, _hR, hTshape,
      hmST, hmUpper, _hiST, hiUpper, _hrootST, hrootUpper, hSTother, hUpperOther⟩ :=
    paired_next_marker_requests hHN hH (Set.Subset.refl H) hH blue oldT v hwinOldT
      (hwinC.of_reachable (exactGame N blue) hcv) true false hpOld hpV hshape
      (by simpa only [Board.get, hVboard] using hfront) hpool hFresh hrelOld hnoOld
      hbeforeOld hnextOld (by simpa only [Board.get, hVboard] using hCheckpoint.left_relaxed)
      (by simpa only [Board.get, hVboard] using hCheckpoint.left_exhausted)
      (by simpa only [Board.get, hVboard] using hbefore)
      (by simpa only [Board.get, hVboard] using hnext)
  simp only [Board.get, Bool.not_true, Bool.not_false] at hSTother hUpperOther hrootUpper hiUpper
  have hcUpper := hcv.trans hVupper
  have hother : upper.position.board.right = checkpoint.position.board.right := by
    simpa only [hVboard] using hUpperOther
  have hrootEq : upper.position.board.left.rootLabel =
      checkpoint.position.board.left.rootLabel := by
    simpa only [hVboard] using hrootUpper
  have hroot : ∀ m ∈ upper.position.board.left.rootLabel,
      m ≤ upper.position.board.left.bodyLabels.length + 1 := by
    intro m hm
    rw [hiUpper, ← hlastT]
    exact Finset.le_sup (f := id) (hrootEq ▸ hm)
  have hbound := critical_preliminary_request_bound hH0N hHH0 hH blue origin checkpoint upper ha
    hop hboard hmode hwin hfrom (pathH0 hcUpper) hCheckpoint hpUpper hmUpper hroot hall
  obtain ⟨Q, hQt, hQs, hQpivot⟩ :
      ∃ Q : PreparedSelection N H blue b σ upper.position.board.right,
        Q.target = PU.target ∧ Q.side = PU.side ∧ Q.labels.pivot = PU.labels.pivot := by
    rw [hother]
    exact ⟨PU, rfl, rfl, rfl⟩
  exact nonlast_prepared_anchor_triangle hH0N hHH0 hH
    (fun x hx => (Nat.zero_le _).trans_lt (hFresh x hx)) blue origin checkpoint upper st U Q
    ha hD hAfterU hop hboard hmode hwin hfrom (pathH0 hcUpper) hCheckpoint
    (hwinOldT.of_reachable (exactGame N blue) hOldST)
    (by simpa only [hQt] using hModeSU) (hQs.trans hPUside)
    hpUpper hpST hmUpper hmST hTshape.symm hroot hother hUlt hbound
    (by simpa only [hother] using hQpivot.trans hPUpivot)
    (by simpa only [hother] using hUroot) (by simpa only [hother] using hUbody)
    (by simpa only [hQt] using hLowerRoot) hall
    (by simpa only [hQt] using hSrel) (by simpa only [hSTother, hQt] using hS)
    (by simpa only [hSTother] using hSUp) (by simpa only [hSTother] using hSstrict)
    (by simpa only [hSTother] using hSnext) (by simpa only [hQt] using hSroot)
    (by simpa only [hQt] using hgamma) (by simpa only [hQt] using hSlast)

#print axioms nonlast_prepared_checkpoint_triangle

end Erdos591.Positive.Game.Payoff

end Erdos118.Reused591
