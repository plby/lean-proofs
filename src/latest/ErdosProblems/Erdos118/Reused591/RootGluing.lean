import ErdosProblems.Erdos118.Reused591.RootRelabel
import ErdosProblems.Erdos118.Reused591.OverlapLabels

namespace Erdos118.Reused591

/-!
# The actual upper response in last--first root gluing

When the lower coordinate word reaches the last body selected by its
root label, the upper root label selects that body first. The upper
opening response is reconstructed with its own fixed label and the same
word coordinates. All its inputs stay in the given pool and above the
bound fixed before the common root was chosen.
-/

namespace Erdos591.Positive.Game

theorem Reply.advance_of_list (board : Board) (side : Bool) (D : Finset ℕ)
    (n : ℕ) (xs : List ℕ) (first last : LabeledWord)
    (hlegal : (board.get side).AllowedSize D.card)
    (hread : (board.get side).read D n = some first)
    (hrest : LabeledWord.advanceRemainder.run first xs = some last)
    (hinc : (D.sort (· ≤ ·) ++ n :: xs).Pairwise (· < ·)) :
    Reply board ⟨side, .advance D.card⟩ (D.sort (· ≤ ·) ++ n :: xs).toFinset
      (board.update side last) := by
  apply Reply.advance side D.card _ last hlegal
  rw [Erdos590.Larson.sort_toFinset_eq_self_of_pairwise hinc]
  have hr := Advance.run_prelude_build ⟨board.get side, hlegal.1⟩ []
    (D.sort (· ≤ ·)) n xs first last (by simpa using hread) hrest
  simpa using hr

namespace LastFirstLabels

theorem root_reply {H : Set ℕ} {B a c : ℕ} (L : LastFirstLabels H B a c)
    (board : Board) (side : Bool) (hinit : board.get side = LabeledWord.initial)
    {v : LabeledWord} {xs : List (Finset ℕ × ℕ)}
    (hr : (LabeledCode.rootCursor L.lower L.marker).runAtoms xs = some v)
    (hm : v.markerEvent = true) (hindex : v.bodyLabels.length + 1 = L.pivot)
    (hinc : (L.marker :: xs.map Prod.snd).Pairwise (· < ·))
    (hpool : ∀ x ∈ xs.map Prod.snd, x ∈ H) :
    ∃ u, Reply board ⟨side, .advance c⟩ u (board.update side (LabeledWord.rootRelabel L.upper v)) ∧
      u.sort (· ≤ ·) = L.upper.sort (· ≤ ·) ++ L.marker :: xs.map Prod.snd ∧
      (↑u : Set ℕ) ⊆ H ∧ ∀ x ∈ u, B < x := by
  have hrest := LabeledWord.rootRelabel_first_marker hr L.label_bounds.2 hm
    (hindex ▸ L.pivot_upper) (fun i hi => hindex ▸ L.upper_ge i hi)
  let input := L.upper.sort (· ≤ ·) ++ L.marker :: xs.map Prod.snd
  have hinput : input.Pairwise (· < ·) := by
    refine List.pairwise_append.mpr ⟨(Finset.sortedLT_sort L.upper).pairwise, hinc, ?_⟩
    intro x hx y hy
    have hxm := (L.upper_fresh x ((Finset.mem_sort (· ≤ ·)).mp hx)).2.2
    rcases List.mem_cons.mp hy with rfl | hy
    · exact hxm
    · exact hxm.trans ((List.pairwise_cons.mp hinc).1 y hy)
  have hlegal : (board.get side).AllowedSize L.upper.card := by
    simp [hinit, LabeledWord.AllowedSize, LabeledWord.terminal, LabeledWord.initial]
  have hreply := Reply.advance_of_list board side L.upper L.marker (xs.map Prod.snd)
    (LabeledCode.rootCursor L.upper L.marker) (LabeledWord.rootRelabel L.upper v)
    hlegal (by rw [hinit]; exact LabeledCode.read_root _ _) hrest hinput
  rw [L.upper_card] at hreply
  have hvalues : ∀ x ∈ input, x ∈ H ∧ B < x := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · have hf := L.upper_fresh x ((Finset.mem_sort (· ≤ ·)).mp hx)
      exact ⟨hf.1, hf.2.1⟩
    · rcases List.mem_cons.mp hx with rfl | hx
      · exact L.marker_fresh
      · exact ⟨hpool x hx, L.marker_fresh.2.trans ((List.pairwise_cons.mp hinc).1 x hx)⟩
  exact ⟨input.toFinset, hreply, Erdos590.Larson.sort_toFinset_eq_self_of_pairwise hinput,
    fun x hx => (hvalues x (List.mem_toFinset.mp hx)).1,
    fun x hx => (hvalues x (List.mem_toFinset.mp hx)).2⟩

#print axioms root_reply

end LastFirstLabels

end Erdos591.Positive.Game

end Erdos118.Reused591
