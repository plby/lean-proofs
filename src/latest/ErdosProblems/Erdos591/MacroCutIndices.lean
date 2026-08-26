import ErdosProblems.Erdos591.MacroCuts
import ErdosProblems.Erdos591.WordPositions

/-!
# Exact cut-label indices for completed macro branches

The geometric macro boundary has the same body and leaf indices as its
literal completed word. Those selected indices persist into the final
cursor, giving strict cut bounds and genuine subsets of its fine labels.
-/

namespace Erdos591.Positive.Game.Macro.Forest

open Erdos591.Negative.Exact

variable {N H : Set ℕ} (hH : H.Infinite) (b : Concrete.Hist N → ℕ)

theorem Descendant.legal_tail {p n : ℕ} (h : Descendant p n) :
    ∃ xs, LabeledWord.LegalRun (node hH b p).cursor xs (node hH b n).cursor := by
  have hp : List.IsPrefix (node hH b p).atoms (node hH b n).atoms :=
    (h.segments_prefix hH b).flatMap Prod.snd
  obtain ⟨xs, heq⟩ := hp
  have hn : LabeledWord.LegalRun LabeledWord.initial (node hH b n).atoms
      (node hH b n).cursor := (node hH b n).legal
  rw [← heq] at hn
  obtain ⟨u, hu, ht⟩ := hn.split
  have heq' : u = (node hH b p).cursor :=
    Option.some.inj (hu.run.symm.trans (node hH b p).legal.run)
  exact ⟨xs, heq' ▸ ht⟩

theorem cut_selected_leaf (n m : ℕ) (hnm : root n ≠ root m) (s t : G)
    (hs : Erdos591.Negative.Exact.word s.val = (node hH b n).cursor.coordinates)
    (ht : Erdos591.Negative.Exact.word t.val = (node hH b m).cursor.coordinates)
    (k : ℕ) (hcut : Payoff.Cut (Erdos591.Negative.Exact.word s.val)
      (Erdos591.Negative.Exact.word t.val) k) :
    ∃ i j, Payoff.LeafCut s.val t.val i j ∧ k = Payoff.leafPosition s.val i j ∧
      (i + 1 < s.val.length ∧ j + 1 < (s.val.getD i []).length) ∧
      i + 1 ∈ (node hH b n).cursor.rootLabel ∧
      j + 1 ∈ (node hH b n).cursor.bodyLabels.getD i ∅ := by
  have hcut' : Payoff.Cut (node hH b n).cursor.coordinates
      (node hH b m).cursor.coordinates k := by simpa only [hs, ht] using hcut
  obtain ⟨p, hp, hr, hlen⟩ := cut_relaxed_prefix hH b n m hnm k hcut'
  have hcoords : (node hH b p).cursor.coordinates =
      (Erdos591.Negative.Exact.word s.val).take (k + 1) := by
    rw [hs]
    simpa [hlen] using List.prefix_iff_eq_take.mp (hp.coordinates_prefix hH b)
  have hk : k < (Erdos591.Negative.Exact.word s.val).length := by
    have hh := hcut.1
    omega
  obtain ⟨i, j, hi, hj, hI, hJ, hR, hB, hpos⟩ :=
    LabeledCode.relaxed_prefix_indices (node hH b p).legal s.val k hcoords hk hr
  have hselected : 0 < (node hH b p).cursor.leafIndex ∧
      (node hH b p).cursor.bodyLabels.length ∈ (node hH b p).cursor.rootLabel ∧
      (node hH b p).cursor.leafIndex ∈ (node hH b p).cursor.currentLabel := by
    simpa [LabeledWord.relaxed] using hr
  have hbounds := (node hH b p).invariant.2.2
  have hstrict : i + 1 < s.val.length ∧ j + 1 < (s.val.getD i []).length := by
    have hroot := (hbounds.1 _ hselected.2.1).2
    have hleaf := (hbounds.2 _ hselected.2.2).2
    simpa only [hI, hJ, hR, hB] using And.intro hroot hleaf
  obtain ⟨xs, htail⟩ := hp.legal_tail hH b
  have hstart : (node hH b p).cursor.parser ≠ .start := by
    have hout := LabeledWord.relaxed_outstanding (node hH b p).invariant.2.1 hbounds hr
    intro heq
    simp [heq, LabeledWord.outstandingBodies, LabeledWord.outstandingLeaves] at hout
  have hroot := htail.rootLabel_eq hstart
  have hC : i + 1 ∈ (node hH b n).cursor.rootLabel := by
    rw [hroot, ← hI]
    exact hselected.2.1
  have hcurrent : (node hH b p).cursor.currentLabel =
      (node hH b p).cursor.bodyLabels.getD i ∅ := by
    simp only [LabeledWord.currentLabel, List.getLastD_eq_getLast?, List.getLast?_eq_getElem?,
      List.getD_eq_getElem?_getD, hI, Nat.add_sub_cancel]
  obtain ⟨rest, heq⟩ := htail.bodyLabels_prefix hstart
  have hget : (node hH b n).cursor.bodyLabels.getD i ∅ =
      (node hH b p).cursor.bodyLabels.getD i ∅ := by
    rw [← heq]
    apply List.getD_append
    omega
  have hD : j + 1 ∈ (node hH b n).cursor.bodyLabels.getD i ∅ := by
    rw [hget, ← hcurrent, ← hJ]
    exact hselected.2.2
  exact ⟨i, j, ⟨hi, hj, hpos ▸ hcut⟩, hpos, hstrict, hC, hD⟩

theorem leafCut_selected (n m : ℕ) (hnm : root n ≠ root m) (s t : G)
    (hs : Erdos591.Negative.Exact.word s.val = (node hH b n).cursor.coordinates)
    (ht : Erdos591.Negative.Exact.word t.val = (node hH b m).cursor.coordinates)
    (i j : ℕ) (hcut : Payoff.LeafCut s.val t.val i j) :
    (i + 1 < s.val.length ∧ j + 1 < (s.val.getD i []).length) ∧
      i + 1 ∈ (node hH b n).cursor.rootLabel ∧
      j + 1 ∈ (node hH b n).cursor.bodyLabels.getD i ∅ := by
  obtain ⟨p, q, hpq, hpos, hstrict, hC, hD⟩ :=
    cut_selected_leaf hH b n m hnm s t hs ht _ hcut.2.2
  obtain ⟨rfl, rfl⟩ := LabeledCode.leafPosition_injective s.val
    hcut.1 hcut.2.1 hpq.1 hpq.2.1 hpos
  exact ⟨hstrict, hC, hD⟩

theorem cuts_admissible (n m : ℕ) (hnm : root n ≠ root m) (s t : G)
    (hs : Erdos591.Negative.Exact.word s.val = (node hH b n).cursor.coordinates)
    (ht : Erdos591.Negative.Exact.word t.val = (node hH b m).cursor.coordinates) :
    CutLabels.Admissible s.val t.val := by
  constructor
  · exact fun i j hcut => (leafCut_selected hH b n m hnm s t hs ht i j hcut).1
  · intro k hcut
    obtain ⟨i, j, hij, hpos, _⟩ := cut_selected_leaf hH b n m hnm s t hs ht k hcut
    exact ⟨i, j, hij, hpos⟩

theorem cut_root_subset (n m : ℕ) (hnm : root n ≠ root m) (s t : G)
    (hs : Erdos591.Negative.Exact.word s.val = (node hH b n).cursor.coordinates)
    (ht : Erdos591.Negative.Exact.word t.val = (node hH b m).cursor.coordinates) :
    CutLabels.root s.val t.val ⊆ (node hH b n).cursor.rootLabel := by
  apply CutLabels.root_subset
  exact fun i j hcut => (leafCut_selected hH b n m hnm s t hs ht i j hcut).2.1

theorem cut_body_subset (n m : ℕ) (hnm : root n ≠ root m) (s t : G)
    (hs : Erdos591.Negative.Exact.word s.val = (node hH b n).cursor.coordinates)
    (ht : Erdos591.Negative.Exact.word t.val = (node hH b m).cursor.coordinates) (i : ℕ) :
    CutLabels.body s.val t.val i ⊆ (node hH b n).cursor.bodyLabels.getD i ∅ := by
  apply CutLabels.body_subset
  exact fun j hcut => (leafCut_selected hH b n m hnm s t hs ht i j hcut).2.2

#print axioms cuts_admissible
#print axioms cut_root_subset
#print axioms cut_body_subset

end Erdos591.Positive.Game.Macro.Forest
