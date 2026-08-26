import ErdosProblems.Erdos118.Reused591.FirstLastLabels
import ErdosProblems.Erdos118.Reused591.FirstLeafGluingHistory
import ErdosProblems.Erdos118.Reused591.FreshLeafNextMarker

namespace Erdos118.Reused591

/-!
# The shared first leaf of the two common-last first-word bodies

Both full labels are chosen after the two actual requests. The common
first response leaves each opposite word unchanged and requests its
next selected body. Literal body cursors retain the common prefix for
the later two-stage interior replay and shared last leaf.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact

theorem first_last_body_opening {N H : Set ℕ} (hHN : H ⊆ N) (hH : H.Infinite)
    (blue : SimpleGraph G) {b : Concrete.Hist N → ℕ}
    {σ : (exactGame N blue).ArchitectStrategy} (st su : Concrete.Hist N)
    {B p q i j : ℕ} (L : FirstLastLabels H B p q)
    (hwinST : (exactGame N blue).ArchitectWins H b σ st)
    (hwinSU : (exactGame N blue).ArchitectWins H b σ su)
    (hpST : st.position.pending = some ⟨false, .advance p⟩)
    (hpSU : su.position.pending = some ⟨false, .advance q⟩)
    (hmST : st.position.board.left.markerEvent = true)
    (hmSU : su.position.board.left.markerEvent = true)
    (hS : LabeledWord.SameStructure st.position.board.left su.position.board.left)
    (hrootST : ∀ k ∈ st.position.board.left.rootLabel,
      k ≤ st.position.board.left.bodyLabels.length + 1)
    (hrootSU : ∀ k ∈ su.position.board.left.rootLabel,
      k ≤ su.position.board.left.bodyLabels.length + 1)
    (hrelT : st.position.board.right.relaxed = true)
    (hrelU : su.position.board.right.relaxed = true)
    (hbeforeT : LabeledWord.BeforeBody i st.position.board.right)
    (hbeforeU : LabeledWord.BeforeBody j su.position.board.right)
    (hBST : max st.position.bound (b st) ≤ B)
    (hBSU : max su.position.bound (b su) ≤ B) :
    ∃ st' su', Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) st st' ∧
      Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) su su' ∧
      st'.position.pending = some ⟨true, .advance 0⟩ ∧
      su'.position.pending = some ⟨true, .advance 0⟩ ∧
      LabeledWord.SameStructure st'.position.board.left su'.position.board.left ∧
      st'.position.board.left.relaxed = true ∧ su'.position.board.left.relaxed = true ∧
      st'.position.board.left.currentLabel = L.lower ∧
      su'.position.board.left.currentLabel = L.upper ∧
      st'.position.board.left.leafIndex = L.first ∧ su'.position.board.left.leafIndex = L.first ∧
      (∀ k ∈ st'.position.board.left.rootLabel, k ≤ st'.position.board.left.bodyLabels.length) ∧
      (∀ k ∈ su'.position.board.left.rootLabel, k ≤ su'.position.board.left.bodyLabels.length) ∧
      st'.position.board.right = st.position.board.right ∧
      su'.position.board.right = su.position.board.right ∧
      ∃ r xs, st.position.board.left.parser = .blocks (r + 1) ∧
        st'.position.board.left =
          LabeledWord.bodyLeafCursor st.position.board.left L.lower L.marker r xs ∧
        su'.position.board.left =
          LabeledWord.bodyLeafCursor su.position.board.left L.upper L.marker r xs ∧
        xs.length = L.first ∧ (L.marker :: xs).Pairwise (· < ·) ∧
        (∀ x ∈ xs, x ∈ H ∧ L.marker < x) := by
  obtain ⟨v, w, hSTv, hSUw, _hnv, _hnw, hshape, hrelV, hrelW, hiV, hiW,
      hbodyV, hbodyW, hotherV, hotherW, r, xs, hparse, hwordV, hwordW, hlen, hinc, hpool⟩ :=
    first_leaf_gluing_prefix hHN hH blue σ st su false false L.first_to_lower
      L.first_to_upper rfl rfl hpST hpSU hmST hmSU hS hBST hBSU
  have hsepV := (FiniteResponseGame.FollowStep.next (exactGame N blue) hSTv).reply_separation hpST
  have hsepW := (FiniteResponseGame.FollowStep.next (exactGame N blue) hSUw).reply_separation hpSU
  obtain ⟨st', hvst, hstBoard, hstPending⟩ := winning_next_body_after_fresh_leaf hHN hH blue
    (hwinST.of_reachable (exactGame N blue) (.single hSTv)) false hrelV hsepV
    (by rw [hotherV]; exact hrelT) (by rw [hotherV]; exact hbeforeT)
  obtain ⟨su', hwsu, hsuBoard, hsuPending⟩ := winning_next_body_after_fresh_leaf hHN hH blue
    (hwinSU.of_reachable (exactGame N blue) (.single hSUw)) false hrelW hsepW
    (by rw [hotherW]; exact hrelU) (by rw [hotherW]; exact hbeforeU)
  change LabeledWord.SameStructure v.position.board.left w.position.board.left at hshape
  change v.position.board.left.relaxed = true at hrelV
  change w.position.board.left.relaxed = true at hrelW
  change v.position.board.left.leafIndex = L.first at hiV
  change w.position.board.left.leafIndex = L.first at hiW
  change v.position.board.right = st.position.board.right at hotherV
  change w.position.board.right = su.position.board.right at hotherW
  change v.position.board.left =
    LabeledWord.bodyLeafCursor st.position.board.left L.lower L.marker r xs at hwordV
  change w.position.board.left =
    LabeledWord.bodyLeafCursor su.position.board.left L.upper L.marker r xs at hwordW
  change v.position.board.left.bodyLabels = st.position.board.left.bodyLabels ++ [L.lower]
    at hbodyV
  change w.position.board.left.bodyLabels = su.position.board.left.bodyLabels ++ [L.upper]
    at hbodyW
  refine ⟨st', su', (Relation.ReflTransGen.single hSTv).trans hvst,
    (Relation.ReflTransGen.single hSUw).trans hwsu, hstPending, hsuPending, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, r, xs, hparse, ?_, ?_, hlen, hinc, hpool⟩
  · simpa only [hstBoard, hsuBoard] using hshape
  · simpa only [hstBoard] using hrelV
  · simpa only [hsuBoard] using hrelW
  · simp [hstBoard, LabeledWord.currentLabel, hbodyV]
  · simp [hsuBoard, LabeledWord.currentLabel, hbodyW]
  · simpa only [hstBoard] using hiV
  · simpa only [hsuBoard] using hiW
  · simpa [hstBoard, hwordV, LabeledWord.bodyLeafCursor] using hrootST
  · simpa [hsuBoard, hwordW, LabeledWord.bodyLeafCursor] using hrootSU
  · simpa only [hstBoard] using hotherV
  · simpa only [hsuBoard] using hotherW
  · simpa only [hstBoard] using hwordV
  · simpa only [hsuBoard] using hwordW

#print axioms first_last_body_opening

end Erdos591.Positive.Game.Payoff

end Erdos118.Reused591
