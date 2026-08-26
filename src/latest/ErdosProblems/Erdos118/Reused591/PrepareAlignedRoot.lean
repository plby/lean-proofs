import ErdosProblems.Erdos118.Reused591.AlignedRootPlan

namespace Erdos118.Reused591

/-!
# Installing an aligned reservation with an actual lower root response

The two root requests are already known. Their common input root and
labels exceed both bounds, and the exact lower prefix up to its first
selected marker is retained for the delayed upper replay.
-/

namespace Erdos591.Positive.Game.Relay

open Erdos591.Negative.Exact
open Payoff

theorem prepare_aligned_root {N H : Set ℕ} (hHN : H ⊆ N) (hH : H.Infinite)
    (blue : SimpleGraph G) {b : Concrete.Hist N → ℕ}
    {σ : (exactGame N blue).ArchitectStrategy} {lower upper : Concrete.Hist N}
    (hwin : (exactGame N blue).ArchitectWins H b σ upper) (s t : Bool)
    {B a c : ℕ} (L : AlignedRootLabels H B a c)
    (hlower : lower.position.pending = some ⟨s, .advance a⟩)
    (hupper : upper.position.pending = some ⟨t, .advance c⟩)
    (hil : lower.position.board.get s = LabeledWord.initial)
    (hiu : upper.position.board.get t = LabeledWord.initial)
    (hBl : max lower.position.bound (b lower) ≤ B)
    (hBu : max upper.position.bound (b upper) ≤ B) :
    ∃ q, (exactGame N blue).FollowStep σ H b lower q ∧ q.position.pending = none ∧
      (q.position.board.get s).markerEvent = true ∧
      q.position.board.get (!s) = lower.position.board.get (!s) ∧
      ∃ R : AlignedRootPlan N H blue b σ (q.position.board.get s),
        R.target = upper ∧ R.side = t ∧ HEq R.labels L ∧
          R.labels.lower = L.lower ∧ R.labels.upper = L.upper ∧ R.labels.shared = L.shared := by
  have hlegal : (lower.position.board.get s).AllowedSize L.lower.card := by
    simp [hil, LabeledWord.AllowedSize, LabeledWord.terminal, LabeledWord.initial]
  obtain ⟨u, last, tail, hr, hsort, hpool, hfresh, first, hread, hrest⟩ :=
    Reply.prescribed_advance_exists_run hH lower.position.board s L.lower L.marker B
      hlegal L.lower_fresh L.marker_fresh
  rw [L.lower_card] at hr
  obtain ⟨q, hstep, hboard, hnone⟩ := Concrete.follow_reply hHN (payoff blue) σ lower
    hlower hr hpool (fun x hx =>
      ⟨((le_max_left _ _).trans hBl).trans_lt (hfresh x hx),
        ((le_max_right _ _).trans hBl).trans_lt (hfresh x hx)⟩)
  have hword : q.position.board.get s = last := by simp [hboard]
  have hread' : LabeledWord.initial.read L.lower L.marker = some first := by
    simpa [hil] using hread
  have hfirst : first = LabeledCode.rootCursor L.lower L.marker :=
    Option.some.inj (hread'.symm.trans (LabeledCode.read_root _ _))
  have hrun := LabeledWord.zero_run_legal _ (fun _ _ => rfl) hrest
  have hstart := LabeledWord.read_parser_ne_start hread
  have hroot : last.rootLabel = L.lower := by
    simpa [hfirst, LabeledCode.rootCursor] using hrun.rootLabel_eq hstart
  have hlabels : ∀ i ∈ L.lower, 0 < i ∧ i < L.marker := by
    intro i hi
    exact ⟨(Nat.zero_le B).trans_lt (L.lower_fresh i hi).2.1, (L.lower_fresh i hi).2.2⟩
  have hno : first.NoRootPassed := by
    intro i hi
    have hi' : i ∈ L.lower := by simpa [hfirst, LabeledCode.rootCursor] using hi
    simpa [hfirst, LabeledCode.rootCursor] using (hlabels i hi').1
  have hlastNo := hno.remainder hstart hrest
  have hcorrect := LabeledWord.cursorInvariant_initial.read
    (show LabeledWord.initial.AllowedLabel L.lower L.marker from ⟨hlabels, trivial⟩) hread'
  have hmarker : last.markerEvent = true := by
    apply Macro.first_marker_of_pending hcorrect hstart
      (by simp [hfirst, LabeledWord.EmptyBodies, LabeledCode.rootCursor]) _ hrest
    exact Or.inl ⟨L.shared, by simpa [hfirst, LabeledCode.rootCursor] using L.shared_lower,
      by simpa [hfirst, LabeledCode.rootCursor] using (hlabels L.shared L.shared_lower).1⟩
  let R : AlignedRootPlan N H blue b σ last := {
    target := upper
    side := t
    budget := B
    lowerSize := a
    upperSize := c
    labels := L
    targetPending := hupper
    targetInitial := hiu
    targetBound := hBu
    targetWinning := hwin
    atoms := tail.map fun n => (∅, n)
    run := by simpa only [hfirst] using hrun
    pool := by
      intro atom ha
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
      have hu : x ∈ u := (Finset.mem_sort (· ≤ ·)).mp (by
        rw [hsort]
        exact List.mem_append_right _ (List.mem_cons_of_mem L.marker hx))
      exact ⟨hpool hu, hfresh x hu⟩
    before := hlastNo L.shared (hroot ▸ L.shared_lower) }
  refine ⟨q, hstep, hnone, by simpa only [hword] using hmarker,
    by simpa [hboard] using hr.other_eq, ?_⟩
  rw [hword]
  exact ⟨R, rfl, rfl, HEq.rfl, rfl, rfl, rfl⟩

#print axioms prepare_aligned_root

end Erdos591.Positive.Game.Relay

end Erdos118.Reused591
