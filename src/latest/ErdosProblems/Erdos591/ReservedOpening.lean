import ErdosProblems.Erdos591.RootGluing
import ErdosProblems.Erdos591.SharedTail
import ErdosProblems.Erdos591.CutPersistence

/-!
# Finish an unsubmitted root response from an existing coordinate prefix

The reserved root label need not overlap the old label at its first
selected body. Erase the old body labels, continue to the reserved
first marker on a fresh tail, and prove that the whole concatenation
is the actual initial response. New coordinates retain a separate bound.
-/

namespace Erdos591.Positive.Game

theorem Reply.reserved_root_exists_run {H : Set ℕ} (hH : H.Infinite)
    (board : Board) (side : Bool) (hinit : board.get side = LabeledWord.initial)
    {D C : Finset ℕ} {n B : ℕ} {as : List (Finset ℕ × ℕ)} {w : LabeledWord}
    (hraw : (LabeledCode.rootCursor D n).runAtoms as = some w)
    (hC : ∀ x ∈ C, x ∈ H ∧ B < x ∧ x < n) (hn : n ∈ H ∧ B < n)
    (hCne : C.Nonempty) (hbefore : ∀ i ∈ C, w.bodyLabels.length < i)
    (hinc : (n :: as.map Prod.snd).Pairwise (· < ·))
    (hpool : ∀ x ∈ as.map Prod.snd, x ∈ H) (K : ℕ) :
    ∃ u last tail, Reply board ⟨side, .advance C.card⟩ u (board.update side last) ∧
      (↑u : Set ℕ) ⊆ H ∧ (∀ x ∈ u, B < x) ∧
      LabeledWord.LegalRun (LabeledWord.rootRelabel C w) (tail.map fun n => (∅, n)) last ∧
      (∀ x ∈ tail, x ∈ H ∧ K < x) ∧ last.markerEvent = true ∧
      last.NoRootPassed ∧ last.rootLabel = C ∧ last.coordinates = w.coordinates ++ tail := by
  have hCbounds : ∀ x ∈ C, 0 < x ∧ x < n :=
    fun x hx => ⟨(Nat.zero_le B).trans_lt (hC x hx).2.1, (hC x hx).2.2⟩
  have hrootCorrect := LabeledWord.cursorInvariant_initial.read
    (show LabeledWord.initial.AllowedLabel C n from ⟨hCbounds, trivial⟩)
    (LabeledCode.read_root C n)
  have hrootStart : (LabeledCode.rootCursor C n).parser ≠ .start := by
    simp [LabeledCode.rootCursor]
  have hrawRel := LabeledWord.runAtoms_rootRelabel C
    (show (LabeledCode.rootCursor D n).parser ≠ .start by simp [LabeledCode.rootCursor]) hraw
  rw [LabeledWord.rootRelabel_rootCursor] at hrawRel
  have hold := LabeledWord.legal_of_zero_atoms hrawRel
  have hw := hold.cursorInvariant hrootCorrect
  have hstart := hold.parser_ne_start hrootStart
  have hno : (LabeledWord.rootRelabel C w).NoRootPassed := by
    simpa only [LabeledWord.NoRootPassed, LabeledWord.rootRelabel, List.length_replicate]
      using hbefore
  have hpending : Macro.Pending (LabeledWord.rootRelabel C w) := by
    obtain ⟨i, hi⟩ := hCne
    exact Or.inl ⟨i, hi, hno i hi⟩
  let M := max K ((n :: as.map Prod.snd).toFinset.sup id)
  have hM : ∀ x ∈ n :: as.map Prod.snd, x ≤ M := by
    intro x hx
    exact (Finset.le_sup (f := id) (List.mem_toFinset.mpr hx)).trans (le_max_right _ _)
  let J := H \ Set.Iic M
  have hJ : J.Infinite := hH.sdiff (Set.finite_Iic M)
  obtain ⟨v, ⟨last, hrest⟩, hvJ⟩ :=
    LabeledWord.advanceRemainder_exists (LabeledWord.rootRelabel C w) hJ
  let tail := v.sort (· ≤ ·)
  have htail : ∀ x ∈ tail, x ∈ H ∧ M < x := by
    intro x hx
    have hmem := hvJ ((Finset.mem_sort (· ≤ ·)).mp hx)
    exact ⟨hmem.1, lt_of_not_ge hmem.2⟩
  have hlastRun := LabeledWord.zero_run_legal _ (fun _ _ => rfl) hrest
  have hm := Macro.first_marker_of_pending hw hstart
    (LabeledWord.rootRelabel_emptyBodies C w) hpending hrest
  have hlastNo := hno.remainder hstart hrest
  have hrootNo : (LabeledCode.rootCursor C n).NoRootPassed := by
    intro i hi
    exact (hCbounds i hi).1
  have hrootPending : Macro.Pending (LabeledCode.rootCursor C n) := by
    obtain ⟨i, hi⟩ := hCne
    exact Or.inl ⟨i, hi, (hCbounds i hi).1⟩
  have hwhole : LabeledWord.advanceRemainder.run (LabeledCode.rootCursor C n)
      (as.map Prod.snd ++ tail) = some last := by
    apply LabeledWord.advanceRemainder_to_first_marker hrootCorrect hrootStart
      (by simp [LabeledWord.EmptyBodies, LabeledCode.rootCursor]) hrootPending hrootNo
      _ hm hlastNo
    simpa only [List.map_append] using (hold.append hlastRun).run
  have hcoordsInc : (n :: (as.map Prod.snd ++ tail)).Pairwise (· < ·) := by
    have hfull : ((n :: as.map Prod.snd) ++ tail).Pairwise (· < ·) :=
      List.pairwise_append.mpr ⟨hinc, (Finset.sortedLT_sort v).pairwise,
        fun x hx y hy => (hM x hx).trans_lt (htail y hy).2⟩
    simpa only [List.cons_append] using hfull
  let input := C.sort (· ≤ ·) ++ n :: (as.map Prod.snd ++ tail)
  have hinputInc : input.Pairwise (· < ·) := by
    refine List.pairwise_append.mpr ⟨(Finset.sortedLT_sort C).pairwise, hcoordsInc, ?_⟩
    intro x hx y hy
    have hxn := (hC x ((Finset.mem_sort (· ≤ ·)).mp hx)).2.2
    rcases List.mem_cons.mp hy with rfl | hy
    · exact hxn
    · exact hxn.trans ((List.pairwise_cons.mp hcoordsInc).1 y hy)
  have hlegal : (board.get side).AllowedSize C.card := by
    simp [hinit, LabeledWord.AllowedSize, LabeledWord.terminal, LabeledWord.initial]
  have hreply := Reply.advance_of_list board side C n (as.map Prod.snd ++ tail)
    (LabeledCode.rootCursor C n) last hlegal
    (by rw [hinit]; exact LabeledCode.read_root C n) hwhole hinputInc
  have hvalues : ∀ x ∈ input, x ∈ H ∧ B < x := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · have h := hC x ((Finset.mem_sort (· ≤ ·)).mp hx)
      exact ⟨h.1, h.2.1⟩
    · rcases List.mem_cons.mp hx with rfl | hx
      · exact hn
      · rcases List.mem_append.mp hx with hx | hx
        · exact ⟨hpool x hx, hn.2.trans ((List.pairwise_cons.mp hinc).1 x hx)⟩
        · exact ⟨(htail x hx).1, (hn.2.trans_le (hM n (by simp))).trans (htail x hx).2⟩
  refine ⟨input.toFinset, last, tail, hreply,
    (fun x hx => (hvalues x (List.mem_toFinset.mp hx)).1),
    (fun x hx => (hvalues x (List.mem_toFinset.mp hx)).2), hlastRun,
    (fun x hx => ⟨(htail x hx).1, (le_max_left _ _).trans_lt (htail x hx).2⟩),
    hm, hlastNo, ?_, ?_⟩
  · simpa only [LabeledCode.rootCursor] using (hold.append hlastRun).rootLabel_eq hrootStart
  · simpa [LabeledWord.rootRelabel, tail] using LabeledWord.runAtoms_coordinates hlastRun.run

#print axioms Reply.reserved_root_exists_run

end Erdos591.Positive.Game
