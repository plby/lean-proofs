import ErdosProblems.Erdos118.Reused591.PreparedSelection

namespace Erdos118.Reused591

/-! # Install a delayed upper first-leaf response at a prescribed lower selection -/

namespace Erdos591.Positive.Game.Relay

open Erdos591.Negative.Exact
open Payoff

theorem prepare_selection {N H : Set ℕ} (hHN : H ⊆ N) (hH : H.Infinite)
    (blue : SimpleGraph G) {b : Concrete.Hist N → ℕ}
    {σ : (exactGame N blue).ArchitectStrategy} {lower upper : Concrete.Hist N}
    (hwin : (exactGame N blue).ArchitectWins H b σ upper) (s t : Bool)
    {B a c : ℕ} (D : Finset ℕ) (hD : D.card = a) (L : LastFirstLabels H B 1 c)
    (hPivot : L.pivot ∈ D)
    (hFresh : ∀ x ∈ D, x ∈ H ∧ B < x ∧ x < L.marker)
    (hlower : lower.position.pending = some ⟨s, .advance a⟩)
    (hupper : upper.position.pending = some ⟨t, .advance c⟩)
    (hml : (lower.position.board.get s).markerEvent = true)
    (hmu : (upper.position.board.get t).markerEvent = true)
    (hsame : LabeledWord.SameStructure (lower.position.board.get s)
      (upper.position.board.get t))
    (hBl : max lower.position.bound (b lower) ≤ B)
    (hBu : max upper.position.bound (b upper) ≤ B) :
    ∃ q, (exactGame N blue).FollowStep σ H b lower q ∧ q.position.pending = none ∧
      (q.position.board.get s).relaxed = true ∧
      q.position.board.get (!s) = lower.position.board.get (!s) ∧
      ∃ P : PreparedSelection N H blue b σ (q.position.board.get s),
        P.target = upper ∧ P.side = t ∧ HEq P.labels L ∧ P.stem = lower.position.board.get s ∧
          P.lowerLabel = D ∧ P.labels.pivot = L.pivot ∧ P.labels.upper = L.upper := by
  have hlegal : (lower.position.board.get s).AllowedSize D.card :=
    ⟨LabeledWord.marker_not_terminal hml, Or.inr (Or.inr hml)⟩
  obtain ⟨u, last, tail, hr, hsort, hpool, hfresh, first, hread, hrest⟩ :=
    Reply.prescribed_advance_exists_run hH lower.position.board s D L.marker B
      hlegal hFresh L.marker_fresh
  rw [hD] at hr
  obtain ⟨q, hstep, hboard, hnone⟩ := Concrete.follow_reply hHN (payoff blue) σ lower
    hlower hr hpool (fun x hx =>
      ⟨((le_max_left _ _).trans hBl).trans_lt (hfresh x hx),
        ((le_max_right _ _).trans hBl).trans_lt (hfresh x hx)⟩)
  have hword : q.position.board.get s = last := by simp [hboard]
  have hw := ((Position.history_dataInvariant lower).2.1 s).1
  have hfirstCorrect := hw.read
    (LabeledWord.allowedLabel_of_size hlegal rfl (fun x hx =>
      ⟨(Nat.zero_le B).trans_lt (hFresh x hx).2.1, (hFresh x hx).2.2⟩)) hread
  have hstate := LabeledWord.FirstLeafState.of_marker_read hml ⟨L.pivot, hPivot⟩ hread
  have hlastState := hstate.remainder hfirstCorrect hrest
  have hminimum := hstate.remainder_minimum hfirstCorrect hrest
  have hlabels := hstate.remainder_bodyLabels hfirstCorrect hrest
  obtain ⟨r, hparse⟩ := LabeledWord.marker_blocks hml
  have hfirst : first = (lower.position.board.get s).record D L.marker
      (Parser.normalize r L.marker) := by
    exact Option.some.inj (hread.symm.trans (by
      simp [LabeledWord.read, hparse, Parser.step]))
  have hfirstLabels : first.bodyLabels =
      (lower.position.board.get s).bodyLabels ++ [D] := by
    simp [hfirst, LabeledWord.record, hparse]
  have hcurrent : last.currentLabel = D := by
    simp [LabeledWord.currentLabel, hlabels, hfirstLabels]
  have hrun := LabeledWord.zero_run_legal _ (fun _ _ => rfl) hrest
  let P : PreparedSelection N H blue b σ last := {
    target := upper
    side := t
    stem := lower.position.board.get s
    remainingBodies := r
    budget := B
    lowerSize := a
    upperSize := c
    lowerLabel := D
    lowerCard := hD
    labels := L
    targetPending := hupper
    targetMarker := hmu
    targetBound := hBu
    targetWinning := hwin
    stemSame := hsame
    stemParser := hparse
    first := first
    firstRead := hread
    atoms := tail.map fun n => (∅, n)
    run := hrun
    bodyLabels_eq := hlabels
    pool := by
      intro atom ha
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
      have hu : x ∈ u := (Finset.mem_sort (· ≤ ·)).mp (by
        rw [hsort]
        exact List.mem_append_right _ (List.mem_cons_of_mem L.marker hx))
      exact ⟨hpool hu, hfresh x hu⟩
    upto := ⟨hlastState.selected, hcurrent ▸ hPivot,
      hminimum.2.2 L.pivot (hcurrent ▸ hPivot)⟩ }
  refine ⟨q, hstep, hnone, ?_, ?_, ?_⟩
  · rw [hword]
    exact hminimum.1
  · simpa [hboard] using hr.other_eq
  · rw [hword]
    exact ⟨P, rfl, rfl, HEq.rfl, rfl, rfl, rfl, rfl⟩

#print axioms prepare_selection

end Erdos591.Positive.Game.Relay

end Erdos118.Reused591
