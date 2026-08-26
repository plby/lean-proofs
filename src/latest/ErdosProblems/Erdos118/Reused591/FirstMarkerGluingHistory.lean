import ErdosProblems.Erdos118.Reused591.FirstLeafGluingHistory
import ErdosProblems.Erdos118.Reused591.InitialRequestSelection

namespace Erdos118.Reused591

/-!
# Two actual root responses with the same first selected body marker

The two root labels have a common least entry and marker. Choose one
opening remainder, then replay its coordinates with the other root label.
Both initial responses stop at the same first body decision; no body
request or later label is chosen by this construction.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact

theorem first_marker_gluing {N H : Set ℕ} (hHN : H ⊆ N) (hH : H.Infinite)
    (blue : SimpleGraph G) {b : Concrete.Hist N → ℕ}
    (σ : (exactGame N blue).ArchitectStrategy) (lower upper : Concrete.Hist N) (s t : Bool)
    {B a c : ℕ} (L : LastFirstLabels H B 1 a) (U : LastFirstLabels H B 1 c)
    (hpivot : U.pivot = L.pivot) (hmarker : U.marker = L.marker)
    (hpL : lower.position.pending = some ⟨s, .advance a⟩)
    (hpU : upper.position.pending = some ⟨t, .advance c⟩)
    (hiL : lower.position.board.get s = LabeledWord.initial)
    (hiU : upper.position.board.get t = LabeledWord.initial)
    (hbL : max lower.position.bound (b lower) ≤ B)
    (hbU : max upper.position.bound (b upper) ≤ B) :
    ∃ q v, (exactGame N blue).FollowStep σ H b lower q ∧
      (exactGame N blue).FollowStep σ H b upper v ∧
      q.position.pending = none ∧ v.position.pending = none ∧
      LabeledWord.SameStructure (q.position.board.get s) (v.position.board.get t) ∧
      (q.position.board.get s).markerEvent = true ∧ (v.position.board.get t).markerEvent = true ∧
      (q.position.board.get s).bodyLabels.length + 1 = L.pivot ∧
      (v.position.board.get t).bodyLabels.length + 1 = L.pivot ∧
      (q.position.board.get s).rootLabel = L.upper ∧
      (v.position.board.get t).rootLabel = U.upper ∧
      q.position.board.get (!s) = lower.position.board.get (!s) ∧
      v.position.board.get (!t) = upper.position.board.get (!t) := by
  have hlegal : (lower.position.board.get s).AllowedSize L.upper.card := by
    simp [hiL, LabeledWord.AllowedSize, LabeledWord.initial, LabeledWord.terminal]
  obtain ⟨uL, last, tail, hrL, hsortL, huLH, huLB, first, hread, hrest⟩ :=
    Reply.prescribed_advance_exists_run hH lower.position.board s L.upper L.marker B
      hlegal L.upper_fresh L.marker_fresh
  rw [L.upper_card] at hrL
  have hread' : LabeledWord.initial.read L.upper L.marker = some first := by
    simpa [hiL] using hread
  have hfirst : first = LabeledCode.rootCursor L.upper L.marker :=
    Option.some.inj (hread'.symm.trans (LabeledCode.read_root _ _))
  have hrun := LabeledWord.zero_run_legal _ (fun _ _ => rfl) hrest
  have hstart := LabeledWord.read_parser_ne_start hread
  have hroot : last.rootLabel = L.upper := by
    simpa [hfirst, LabeledCode.rootCursor] using hrun.rootLabel_eq hstart
  have hno : first.NoRootPassed := by
    intro i hi
    have hi' : i ∈ L.upper := by simpa [hfirst, LabeledCode.rootCursor] using hi
    simpa [hfirst, LabeledCode.rootCursor] using (L.label_bounds.2 i hi').1
  have hlastNo := hno.remainder hstart hrest
  have ha : 0 < a := L.upper_card ▸ Finset.card_pos.mpr ⟨L.pivot, L.pivot_upper⟩
  have hmL : last.markerEvent = true := by
    simpa using hrL.initial_positive_marker hiL ha
      (fun x hx => (Nat.zero_le B).trans_lt (huLB x hx))
  have hindex : last.bodyLabels.length + 1 = L.pivot := by
    apply le_antisymm (hlastNo L.pivot (hroot ▸ L.pivot_upper))
    exact L.upper_ge _ (hroot ▸ LabeledWord.marker_body_mem hmL)
  have htailInc : (L.marker :: tail).Pairwise (· < ·) := by
    have huInc := (Finset.sortedLT_sort uL).pairwise
    rw [hsortL] at huInc
    exact (List.pairwise_append.mp huInc).2.1
  have htailH : ∀ x ∈ tail, x ∈ H := by
    intro x hx
    apply huLH
    apply (Finset.mem_sort (· ≤ ·)).mp
    rw [hsortL]
    exact List.mem_append_right _ (List.mem_cons_of_mem _ hx)
  have hraw : (LabeledCode.rootCursor L.upper L.marker).runAtoms
      (tail.map fun n => (∅, n)) = some last := by simpa [hfirst] using hrun.run
  have hrestU := LabeledWord.rootRelabel_first_marker hraw
    (by simpa [hmarker] using U.label_bounds.2) hmL
    (by simpa [hindex, ← hpivot] using U.pivot_upper)
    (fun i hi => by simpa [hindex, ← hpivot] using U.upper_ge i hi)
  have hlegalU : (upper.position.board.get t).AllowedSize U.upper.card := by
    simp [hiU, LabeledWord.AllowedSize, LabeledWord.initial, LabeledWord.terminal]
  let input := U.upper.sort (· ≤ ·) ++ L.marker :: tail
  have hinput : input.Pairwise (· < ·) := by
    apply List.pairwise_append.mpr
    refine ⟨(Finset.sortedLT_sort U.upper).pairwise, htailInc, ?_⟩
    intro x hx y hy
    have hxM : x < L.marker := by
      simpa [hmarker] using (U.upper_fresh x ((Finset.mem_sort (· ≤ ·)).mp hx)).2.2
    rcases List.mem_cons.mp hy with rfl | hy
    · exact hxM
    · exact hxM.trans ((List.pairwise_cons.mp htailInc).1 y hy)
  have hrU := Reply.advance_of_list upper.position.board t U.upper L.marker tail
    (LabeledCode.rootCursor U.upper L.marker) (LabeledWord.rootRelabel U.upper last)
    hlegalU (by rw [hiU]; exact LabeledCode.read_root _ _) (by simpa using hrestU) hinput
  rw [U.upper_card] at hrU
  have hvalues : ∀ x ∈ input, x ∈ H ∧ B < x := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · have hh := U.upper_fresh x ((Finset.mem_sort (· ≤ ·)).mp hx)
      exact ⟨hh.1, hh.2.1⟩
    · rcases List.mem_cons.mp hx with rfl | hx
      · exact L.marker_fresh
      · exact ⟨htailH x hx, L.marker_fresh.2.trans ((List.pairwise_cons.mp htailInc).1 x hx)⟩
  obtain ⟨q, hsL, hbq, hnL⟩ := Concrete.follow_reply hHN (payoff blue) σ lower hpL hrL huLH
    (fun x hx => ⟨((le_max_left _ _).trans hbL).trans_lt (huLB x hx),
      ((le_max_right _ _).trans hbL).trans_lt (huLB x hx)⟩)
  obtain ⟨v, hsU, hbv, hnU⟩ := Concrete.follow_reply hHN (payoff blue) σ upper hpU hrU
    (fun x hx => (hvalues x (List.mem_toFinset.mp hx)).1)
    (fun x hx => ⟨((le_max_left _ _).trans hbU).trans_lt (hvalues x (List.mem_toFinset.mp hx)).2,
      ((le_max_right _ _).trans hbU).trans_lt (hvalues x (List.mem_toFinset.mp hx)).2⟩)
  have hshape := (LabeledWord.rootRelabel_sameStructure U.upper last).symm
  have hmU : (LabeledWord.rootRelabel U.upper last).markerEvent = true := by
    obtain ⟨r, hparse⟩ := LabeledWord.marker_blocks hmL
    simp [LabeledWord.markerEvent, LabeledWord.rootRelabel, hparse, hindex, ← hpivot, U.pivot_upper]
  exact ⟨q, v, hsL, hsU, hnL, hnU, by simpa [hbq, hbv] using hshape,
    by simpa [hbq] using hmL, by simpa [hbv] using hmU,
    by simpa [hbq] using hindex, by simpa [hbv, LabeledWord.rootRelabel] using hindex,
    by simpa [hbq] using hroot, by simp [hbv, LabeledWord.rootRelabel],
    by simpa [hbq] using hrL.other_eq, by simpa [hbv] using hrU.other_eq⟩

#print axioms first_marker_gluing

end Erdos591.Positive.Game.Payoff

end Erdos118.Reused591
