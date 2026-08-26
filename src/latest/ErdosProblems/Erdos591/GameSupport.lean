import ErdosProblems.Erdos591.GameBoard
import ErdosProblems.Erdos591.ResponseParser
import Mathlib.Data.Finset.Union

/-!
# Numerical support of labeled words and replies

The support includes label values, not only word coordinates. These
lemmas ensure that the positional freshness bound covers every number
stored in either cursor.
-/

namespace Erdos591.Positive.Game

namespace LabeledWord

def support (w : LabeledWord) : Finset ℕ :=
  w.coordinates.toFinset ∪ w.rootLabel ∪ w.bodyLabels.toFinset.biUnion id

theorem mem_support {w : LabeledWord} {x : ℕ} :
    x ∈ w.support ↔ x ∈ w.coordinates ∨ x ∈ w.rootLabel ∨ ∃ L ∈ w.bodyLabels, x ∈ L := by
  simp [support]

theorem coordinate_mem_support {w : LabeledWord} {x : ℕ} (hx : x ∈ w.coordinates) :
    x ∈ w.support := mem_support.mpr (Or.inl hx)

@[simp] theorem support_initial : initial.support = ∅ := by
  simp [support, initial]

theorem read_support {w w' : LabeledWord} {L : Finset ℕ} {n : ℕ}
    (h : w.read L n = some w') : w'.support ⊆ insert n (w.support ∪ L) := by
  cases hs : w.parser with
  | start =>
      have heq : w.record L n (.blocks n) = w' := by
        simpa [LabeledWord.read, hs, Parser.step] using h
      subst w'
      intro x hx
      simp only [mem_support, record, hs, List.mem_append, List.mem_singleton,
        List.not_mem_nil, false_and, exists_false, or_false] at hx
      simp only [Finset.mem_insert, Finset.mem_union, mem_support]
      aesop
  | blocks r =>
      cases r with
      | zero => simp [LabeledWord.read, hs, Parser.step] at h
      | succ r =>
          have heq : w.record L n (Parser.normalize r n) = w' := by
            simpa [LabeledWord.read, hs, Parser.step] using h
          subst w'
          intro x hx
          simp only [mem_support, record, hs, List.mem_append, List.mem_singleton] at hx
          simp only [Finset.mem_insert, Finset.mem_union, mem_support]
          aesop
  | leaves r b =>
      have heq : w.record L n (Parser.normalize r b) = w' := by
        simpa [LabeledWord.read, hs, Parser.step] using h
      subst w'
      intro x hx
      simp only [mem_support, record, hs, List.mem_append, List.mem_singleton] at hx
      simp only [Finset.mem_insert, Finset.mem_union, mem_support]
      aesop

theorem read_support_within {w w' : LabeledWord} {L F : Finset ℕ} {n : ℕ}
    (hw : w.support ⊆ F) (hL : L ⊆ F) (hn : n ∈ F)
    (h : w.read L n = some w') : w'.support ⊆ F :=
  (read_support h).trans (Finset.insert_subset hn (Finset.union_subset hw hL))

theorem run_support_within (D : ResponseParser LabeledWord)
    (hstep : ∀ w n, D.step w n = w.read ∅ n)
    {w w' : LabeledWord} {xs : List ℕ} {F : Finset ℕ}
    (hw : w.support ⊆ F) (hxs : ∀ n ∈ xs, n ∈ F)
    (h : D.run w xs = some w') : w'.support ⊆ F := by
  apply D.run_invariant_on (fun u => u.support ⊆ F) (fun n => n ∈ F) ?_ hw hxs h
  intro u n v hu hn huv
  rw [hstep] at huv
  exact read_support_within hu (Finset.empty_subset F) hn huv

theorem finish_support {w w' : LabeledWord} {xs : List ℕ}
    (h : finishParser.run w xs = some w') : w'.support ⊆ w.support ∪ xs.toFinset := by
  apply run_support_within finishParser (fun _ _ => rfl)
    Finset.subset_union_left ?_ h
  intro n hn
  exact Finset.mem_union_right _ (List.mem_toFinset.mpr hn)

theorem advanceRemainder_support {w w' : LabeledWord} {xs : List ℕ}
    (h : advanceRemainder.run w xs = some w') : w'.support ⊆ w.support ∪ xs.toFinset := by
  apply run_support_within advanceRemainder (fun _ _ => rfl)
    Finset.subset_union_left ?_ h
  intro n hn
  exact Finset.mem_union_right _ (List.mem_toFinset.mpr hn)

end LabeledWord

namespace Advance

theorem run_support (w : Unfinished) (d : ℕ) (xs : List ℕ) (q : State)
    (h : parser.run (.prelude w d []) xs = some q) :
    ∃ last, q = .remainder last ∧ last.support ⊆ w.val.support ∪ xs.toFinset := by
  obtain ⟨labels, n, rest, first, last, hxs, _, hf, hl, hq⟩ :=
    run_prelude w d [] xs q h
  have hf' : w.val.read labels.toFinset n = some first := by simpa using hf
  have hlabels : labels.toFinset ⊆ w.val.support ∪ xs.toFinset := by
    intro x hx
    apply Finset.mem_union_right
    apply List.mem_toFinset.mpr
    rw [hxs]
    exact List.mem_append_left _ (List.mem_toFinset.mp hx)
  have hn : n ∈ w.val.support ∪ xs.toFinset := by
    apply Finset.mem_union_right
    simp [hxs]
  have hfirst := LabeledWord.read_support_within Finset.subset_union_left hlabels hn hf'
  refine ⟨last, hq, ?_⟩
  apply LabeledWord.run_support_within LabeledWord.advanceRemainder (fun _ _ => rfl)
    hfirst ?_ hl
  intro x hx
  apply Finset.mem_union_right
  apply List.mem_toFinset.mpr
  rw [hxs]
  exact List.mem_append_right _ (List.mem_cons_of_mem n hx)

end Advance

namespace Board

def support (b : Board) : Finset ℕ := b.left.support ∪ b.right.support

theorem get_support_subset (b : Board) (side : Bool) : (b.get side).support ⊆ b.support := by
  cases side with
  | false => exact Finset.subset_union_left
  | true => exact Finset.subset_union_right

theorem update_support_subset (b : Board) (side : Bool) (w : LabeledWord) {F : Finset ℕ}
    (hb : b.support ⊆ F) (hw : w.support ⊆ F) : (b.update side w).support ⊆ F := by
  cases side with
  | false => exact Finset.union_subset hw (Finset.subset_union_right.trans hb)
  | true => exact Finset.union_subset (Finset.subset_union_left.trans hb) hw

end Board

theorem Reply.support_subset {b b' : Board} {r : Request} {u : Finset ℕ}
    (h : Reply b r u b') : b'.support ⊆ b.support ∪ u := by
  cases h with
  | finish side u w _ hrun =>
      apply b.update_support_subset side w Finset.subset_union_left
      have hw := LabeledWord.finish_support hrun
      simpa using hw.trans
        (Finset.union_subset_union (b.get_support_subset side) (Finset.Subset.refl _))
  | advance side d u w hlegal hrun =>
      obtain ⟨last, hq, hs⟩ := Advance.run_support ⟨b.get side, hlegal.1⟩ d
        (u.sort (· ≤ ·)) (.remainder w) hrun
      have heq : w = last := Advance.State.remainder.inj hq
      subst last
      apply b.update_support_subset side w Finset.subset_union_left
      simpa using hs.trans
        (Finset.union_subset_union (b.get_support_subset side) (Finset.Subset.refl _))

theorem Reply.word_support {b b' : Board} {r : Request} {u : Finset ℕ}
    (h : Reply b r u b') :
    ∃ w, b' = b.update r.side w ∧ w.support ⊆ (b.get r.side).support ∪ u := by
  cases h with
  | finish side u w _ hrun =>
      exact ⟨w, rfl, by simpa using LabeledWord.finish_support hrun⟩
  | advance side d u w hlegal hrun =>
      obtain ⟨last, hq, hs⟩ := Advance.run_support ⟨b.get side, hlegal.1⟩ d
        (u.sort (· ≤ ·)) (.remainder w) hrun
      have heq : w = last := Advance.State.remainder.inj hq
      subst last
      exact ⟨w, rfl, by simpa using hs⟩

#print axioms Reply.support_subset

end Erdos591.Positive.Game
