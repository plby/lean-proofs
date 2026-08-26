import ErdosProblems.Erdos118.Reused591.SharedFirstLeafHandoff
import ErdosProblems.Erdos118.Reused591.PairedMarkerRequests

namespace Erdos118.Reused591

/-!
# Submit the shared first leaf, then synchronize the other last-body marker

The waiting third play's recorded bound applies to the whole retained
other-word prefix. The newly submitted first-word response changes none
of that prefix. One fresh other-word response can therefore be replayed
in the waiting play, leaving both first words stationary.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact

theorem shared_first_then_marker {N H J : Set ℕ}
    (hHN : H ⊆ N) (hH : H.Infinite) (hJH : J ⊆ H) (hJ : J.Infinite)
    (blue : SimpleGraph G) {b : Concrete.Hist N → ℕ}
    {σ : (exactGame N blue).ArchitectStrategy} (lower upper old : Concrete.Hist N)
    {B p q i j : ℕ} (L : LastFirstLabels H B 1 p) (U : LastFirstLabels H B 1 q)
    (hfirst : U.pivot = L.pivot) (hmarker : U.marker = L.marker)
    (hwinL : (exactGame N blue).ArchitectWins H b σ lower)
    (hwinU : (exactGame N blue).ArchitectWins H b σ upper)
    (hwinOld : (exactGame N blue).ArchitectWins H b σ old)
    (hpL : lower.position.pending = some ⟨true, .advance p⟩)
    (hpU : upper.position.pending = some ⟨false, .advance q⟩)
    (hmL : lower.position.board.right.markerEvent = true)
    (hmU : upper.position.board.left.markerEvent = true)
    (hT : LabeledWord.SameStructure lower.position.board.right upper.position.board.left)
    (hrootL : ∀ k ∈ lower.position.board.right.rootLabel,
      k ≤ lower.position.board.right.bodyLabels.length + 1)
    (hrootU : ∀ k ∈ upper.position.board.left.rootLabel,
      k ≤ upper.position.board.left.bodyLabels.length + 1)
    (hS : LabeledWord.UpToLeaf j lower.position.board.left)
    (hSstrict : lower.position.board.left.leafIndex < j)
    (hUrel : upper.position.board.right.relaxed = true)
    (hUno : upper.position.board.right.NoLeafPending)
    (hUbefore : LabeledWord.BeforeBody i upper.position.board.right)
    (hUnext : ∀ k ∈ upper.position.board.right.rootLabel,
      upper.position.board.right.bodyLabels.length < k → i ≤ k)
    (hBL : max lower.position.bound (b lower) ≤ B)
    (hBU : max upper.position.bound (b upper) ≤ B)
    (hpOld : old.position.pending = some ⟨true, .advance 0⟩)
    (hOldRel : old.position.board.right.relaxed = true)
    (hOldNo : old.position.board.right.NoLeafPending)
    (hOldBefore : LabeledWord.BeforeBody i old.position.board.right)
    (hOldNext : ∀ k ∈ old.position.board.right.rootLabel,
      old.position.board.right.bodyLabels.length < k → i ≤ k)
    {anchor : LabeledWord} {front : List (Finset ℕ × ℕ)}
    (hOldShape : LabeledWord.SameStructure old.position.board.right anchor)
    (hfront : LabeledWord.LegalRun anchor front upper.position.board.right)
    (hfrontPool : ∀ atom ∈ front, atom.2 ∈ H ∧ max old.position.bound (b old) < atom.2)
    (hJfresh : ∀ x ∈ J, max old.position.bound (b old) < x) :
    ∃ st su tu d e,
      Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) lower st ∧
      Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) old su ∧
      Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) upper tu ∧
      st.position.pending = some ⟨false, .advance 0⟩ ∧
      su.position.pending = some ⟨true, .advance d⟩ ∧
      tu.position.pending = some ⟨true, .advance e⟩ ∧ 0 < d ∧ 0 < e ∧
      LabeledWord.SameStructure st.position.board.right tu.position.board.left ∧
      st.position.board.right.relaxed = true ∧ tu.position.board.left.relaxed = true ∧
      st.position.board.right.currentLabel = L.upper ∧
      tu.position.board.left.currentLabel = U.upper ∧
      st.position.board.right.leafIndex = L.pivot ∧ tu.position.board.left.leafIndex = L.pivot ∧
      (∀ k ∈ st.position.board.right.rootLabel, k ≤ st.position.board.right.bodyLabels.length) ∧
      (∀ k ∈ tu.position.board.left.rootLabel, k ≤ tu.position.board.left.bodyLabels.length) ∧
      st.position.board.left = lower.position.board.left ∧
      su.position.board.left = old.position.board.left ∧
      LabeledWord.SameStructure su.position.board.right tu.position.board.right ∧
      su.position.board.right.markerEvent = true ∧ tu.position.board.right.markerEvent = true ∧
      su.position.board.right.bodyLabels.length + 1 = i ∧
      tu.position.board.right.bodyLabels.length + 1 = i ∧
      su.position.board.right.rootLabel = old.position.board.right.rootLabel ∧
      tu.position.board.right.rootLabel = upper.position.board.right.rootLabel := by
  obtain ⟨st, v, hLST, hUv, hpST, hpV, hTshape, hSTrel, hVrel, hSTlabel, hVlabel,
      hSTindex, hVindex, hSTbody, hVbody, hSTroot, hVroot, hSTother, hVother⟩ :=
    shared_first_leaf_handoff hHN hH blue lower upper false L U hfirst hmarker hwinL hwinU
      hpL hpU hmL hmU hT hS hSstrict hUrel (Or.inl ⟨i, hUbefore⟩) hBL hBU
  change v.position.board.right = upper.position.board.right at hVother
  change v.position.board.left.bodyLabels = upper.position.board.left.bodyLabels ++ [U.upper]
    at hVbody
  change v.position.board.left.rootLabel = upper.position.board.left.rootLabel at hVroot
  have hwinV := (hwinU.of_reachable (exactGame N blue) hUv).mono
    (exactGame N blue) hJH (fun _ => le_rfl)
  obtain ⟨su, tu, d, e, hOldSU, hVtu, hpSU, hpTU, hd, he, hUshape, hmSU, hmTU,
      hiSU, hiTU, hSUroot, hTUroot, hSUother, hTUother⟩ :=
    paired_next_marker_requests hHN hH hJH hJ blue old v hwinOld hwinV true true hpOld hpV
      hOldShape (by simpa only [Board.get, hVother] using hfront) hfrontPool hJfresh
      hOldRel hOldNo hOldBefore hOldNext
      (by simpa only [Board.get, hVother] using hUrel)
      (by simpa only [Board.get, hVother] using hUno)
      (by simpa only [Board.get, hVother] using hUbefore)
      (by simpa only [Board.get, hVother] using hUnext)
  have hVtuH : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) v tu :=
    Relation.ReflTransGen.mono (fun _ _ hs =>
      FiniteResponseGame.FollowStep.mono (exactGame N blue) hJH (fun _ => le_rfl) hs) _ _ hVtu
  change tu.position.board.left = v.position.board.left at hTUother
  change tu.position.board.right.rootLabel = v.position.board.right.rootLabel at hTUroot
  refine ⟨st, su, tu, d, e, hLST, hOldSU, hUv.trans hVtuH, hpST, hpSU, hpTU, hd, he,
    ?_, hSTrel, ?_, hSTlabel, ?_, hSTindex, ?_, ?_, ?_, hSTother, hSUother,
    hUshape, hmSU, hmTU, hiSU, hiTU, hSUroot, ?_⟩
  · simpa only [hTUother, Board.get] using hTshape
  · simpa only [hTUother, Board.get] using hVrel
  · simpa only [hTUother, Board.get] using hVlabel
  · simpa only [hTUother, Board.get] using hVindex
  · simpa only [hSTroot, hSTbody, List.length_append, List.length_singleton] using hrootL
  · simpa only [hTUother, hVroot, hVbody, List.length_append, List.length_singleton] using hrootU
  · simpa only [hVother] using hTUroot

#print axioms shared_first_then_marker

end Erdos591.Positive.Game.Payoff

end Erdos118.Reused591
