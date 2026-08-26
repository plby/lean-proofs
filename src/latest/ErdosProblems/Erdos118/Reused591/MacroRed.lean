import ErdosProblems.Erdos118.Reused591.MacroInterleaving
import ErdosProblems.Erdos118.Reused591.ReplayRed

namespace Erdos118.Reused591

/-!
# Cross-root non-blue pairs in the all-builder-wins branch

The play, cut geometry, label coarsening, chronological input bounds,
opening side, and maximum-order flag are all constructed here from the
actual forest records. No replay certificate is assumed of the pair.
-/

namespace Erdos591.Positive.Game.Atomic

open Erdos591.Negative.Exact

theorem first_false_of_root_lt (s t : G) (xs : List Atom)
    (hproj : ∀ side, project xs side = cutProgram s.val t.val side)
    (hinc : (inputs xs).Pairwise (· < ·)) (hlt : s.val.length < t.val.length) :
    ∀ a ∈ xs.head?, a.side = false := by
  intro a ha
  cases hxs : xs with
  | nil => simp [hxs] at ha
  | cons A tail =>
      have heq : a = A := by simpa [hxs, eq_comm] using ha
      subst a
      cases hA : A.side with
      | false => rfl
      | true =>
          have hvalue : A.value = t.val.length := by
            have hh := congrArg (fun ps => (ps.map Prod.snd).headD 0) (hproj true)
            simpa [hxs, project, hA, cutProgram, LabeledCode.atoms] using hh
          have hmem : (CutLabels.root s.val t.val, s.val.length) ∈ project tail false := by
            have hh := hproj false
            simp only [hxs, project, hA, Bool.true_eq_false, ↓reduceIte] at hh
            rw [hh]
            simp [cutProgram, LabeledCode.atoms]
          obtain ⟨B, hB, _, hpair⟩ := mem_project hmem
          have hBvalue : B.value = s.val.length := congrArg Prod.snd hpair
          have hvalues := hinc.sublist (values_sublist_inputs xs)
          rw [hxs, List.map_cons, List.pairwise_cons] at hvalues
          have hh := hvalues.1 B.value (List.mem_map.mpr ⟨B, hB, rfl⟩)
          rw [hvalue, hBvalue] at hh
          exact (lt_asymm hlt hh).elim

theorem last_mem_of_nonempty (xs : List ℕ) (hx : xs ≠ []) : xs.getLastD 0 ∈ xs := by
  cases xs with
  | nil => exact (hx rfl).elim
  | cons x xs =>
      rw [List.getLastD_cons]
      exact List.getLastD_mem_cons

theorem max_order_exists (s t : G)
    (hd : Disjoint (word s.val).toFinset (word t.val).toFinset) :
    ∃ mode, Payoff.MaxOrder mode (cutBoard s.val t.val) := by
  have hs := last_mem_of_nonempty (word s.val) (word_ne_nil s.val)
  have ht := last_mem_of_nonempty (word t.val) (word_ne_nil t.val)
  have hne : (word s.val).getLastD 0 ≠ (word t.val).getLastD 0 := by
    intro heq
    exact Finset.disjoint_left.mp hd (List.mem_toFinset.mpr hs)
      (heq ▸ List.mem_toFinset.mpr ht)
  rcases lt_or_gt_of_ne hne with hst | hts
  · exact ⟨false, by simpa [Payoff.MaxOrder, cutBoard] using hst⟩
  · exact ⟨true, by simpa [Payoff.MaxOrder, cutBoard] using hts⟩

end Erdos591.Positive.Game.Atomic

namespace Erdos591.Positive.Game.Macro.Forest

open Erdos591.Negative.Exact

variable {N H : Set ℕ} (hH : H.Infinite) (b : Concrete.Hist N → ℕ)

theorem decoded_words_disjoint (n m : ℕ) (hnm : root n ≠ root m) (s t : G)
    (hs : Erdos591.Negative.Exact.word s.val = (node hH b n).cursor.coordinates)
    (ht : Erdos591.Negative.Exact.word t.val = (node hH b m).cursor.coordinates) :
    Disjoint (Erdos591.Negative.Exact.word s.val).toFinset
      (Erdos591.Negative.Exact.word t.val).toFinset := by
  rw [hs, ht]
  apply (node_support_disjoint hH b n m hnm).mono
  · exact fun _ hx => LabeledWord.coordinate_mem_support (List.mem_toFinset.mp hx)
  · exact fun _ hx => LabeledWord.coordinate_mem_support (List.mem_toFinset.mp hx)

theorem not_blue_of_ordered_roots (hHN : H ⊆ N) (blue : SimpleGraph G)
    (hbuilder : (Payoff.exactGame N blue).AllBuilderWins H b
      (History.initial (Position.Next N) Position.initial))
    (n m : ℕ) (hnm : root n ≠ root m) (s t : G)
    (hs : Erdos591.Negative.Exact.word s.val = (node hH b n).cursor.coordinates)
    (ht : Erdos591.Negative.Exact.word t.val = (node hH b m).cursor.coordinates)
    (hlt : s.val.length < t.val.length) : ¬ blue.Adj s t := by
  obtain ⟨xs, hselect, hproj⟩ := cut_interleaving hH b n m hnm s t hs ht
  have hinc := taggedLog_increasing hH b (root n) (max n m)
  have hfirst := Atomic.first_false_of_root_lt s t xs hproj
    (hinc.sublist hselect.inputs_sublist) hlt
  obtain ⟨mode, hmax⟩ := Atomic.max_order_exists s t
    (decoded_words_disjoint hH b n m hnm s t hs ht)
  exact Atomic.not_blue_of_canonical_interleaving hHN blue b mode hbuilder s t
    (cuts_admissible hH b n m hnm s t hs ht)
    (cuts_admissible hH b m n hnm.symm t s ht hs)
    xs (taggedLog hH b (root n) (max n m)) hselect hproj hinc
    (taggedLog_spaced hH b (root n) (max n m))
    (taggedLog_pool hH b (root n) (max n m))
    (taggedLog_positive hH b (root n) (max n m)) hfirst hmax

/-- Every pair of completed constructed words with different root
owners is non-blue in the all-builder alternative. -/
theorem not_blue_of_different_roots (hHN : H ⊆ N) (blue : SimpleGraph G)
    (hbuilder : (Payoff.exactGame N blue).AllBuilderWins H b
      (History.initial (Position.Next N) Position.initial))
    (n m : ℕ) (hnm : root n ≠ root m) (s t : G)
    (hs : Erdos591.Negative.Exact.word s.val = (node hH b n).cursor.coordinates)
    (ht : Erdos591.Negative.Exact.word t.val = (node hH b m).cursor.coordinates) :
    ¬ blue.Adj s t := by
  have hd := decoded_words_disjoint hH b n m hnm s t hs ht
  have hne : s.val.length ≠ t.val.length := by
    intro heq
    have hsMem : s.val.length ∈ (Erdos591.Negative.Exact.word s.val).toFinset := by
      simp [Erdos591.Negative.Exact.word]
    have htMem : s.val.length ∈ (Erdos591.Negative.Exact.word t.val).toFinset := by
      rw [heq]
      simp [Erdos591.Negative.Exact.word]
    exact Finset.disjoint_left.mp hd hsMem htMem
  rcases lt_or_gt_of_ne hne with hst | hts
  · exact not_blue_of_ordered_roots hH b hHN blue hbuilder n m hnm s t hs ht hst
  · intro hblue
    exact not_blue_of_ordered_roots hH b hHN blue hbuilder m n hnm.symm t s ht hs hts hblue.symm

theorem different_root_fibers_nonadjacent (hHN : H ⊆ N) (blue : SimpleGraph G)
    (hbuilder : (Payoff.exactGame N blue).AllBuilderWins H b
      (History.initial (Position.Next N) Position.initial))
    {i j : ℕ} (hij : i ≠ j) {s t : G}
    (hs : s ∈ vertices hH b (child 0 i)) (ht : t ∈ vertices hH b (child 0 j)) :
    ¬ blue.Adj s t := by
  obtain ⟨n, hn, _, hs⟩ := hs
  obtain ⟨m, hm, _, ht⟩ := ht
  have hnm : root n ≠ root m := by
    rw [hn.root_eq (parent_lt_child 0 i), hm.root_eq (parent_lt_child 0 j)]
    simp only [root_child]
    exact (child_strictMono 0).injective.ne hij
  exact not_blue_of_different_roots hH b hHN blue hbuilder n m hnm s t hs ht

#print axioms not_blue_of_different_roots
#print axioms different_root_fibers_nonadjacent

end Erdos591.Positive.Game.Macro.Forest

end Erdos118.Reused591
