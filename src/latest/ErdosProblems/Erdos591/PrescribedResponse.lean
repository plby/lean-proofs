import ErdosProblems.Erdos591.AtomicTrace

/-!
# Advance responses with a prescribed label and marker

After a legal label and its later marker have been fixed, the genuine
first-event remainder exists on every infinite tail. Concatenating the
label, marker and remainder gives an increasing response with exactly
the prescribed prelude, all above the original conservative bound.
-/

namespace Erdos591.Positive.Game

theorem Reply.prescribed_advance_exists_run {H : Set ℕ} (hH : H.Infinite)
    (board : Board) (side : Bool) (D : Finset ℕ) (n B : ℕ)
    (hlegal : (board.get side).AllowedSize D.card)
    (hD : ∀ x ∈ D, x ∈ H ∧ B < x ∧ x < n) (hn : n ∈ H ∧ B < n) :
    ∃ u last tail, Reply board ⟨side, .advance D.card⟩ u (board.update side last) ∧
      u.sort (· ≤ ·) = D.sort (· ≤ ·) ++ n :: tail ∧
      (↑u : Set ℕ) ⊆ H ∧ (∀ x ∈ u, B < x) ∧
      ∃ first, (board.get side).read D n = some first ∧
        LabeledWord.advanceRemainder.run first tail = some last := by
  obtain ⟨first, hfirst⟩ := LabeledWord.read_exists hlegal.1 D n
  let M := H \ Set.Iic n
  have hM : M.Infinite := hH.sdiff (Set.finite_Iic n)
  obtain ⟨R, ⟨last, hlast⟩, hR⟩ := LabeledWord.advanceRemainder_exists first hM
  have hRmem (x : ℕ) (hx : x ∈ R.sort (· ≤ ·)) : x ∈ H ∧ n < x :=
    ⟨(hR ((Finset.mem_sort (· ≤ ·)).mp hx)).1,
      lt_of_not_ge (hR ((Finset.mem_sort (· ≤ ·)).mp hx)).2⟩
  let xs := D.sort (· ≤ ·) ++ n :: R.sort (· ≤ ·)
  have hinc : xs.Pairwise (· < ·) := by
    refine List.pairwise_append.mpr ⟨(Finset.sortedLT_sort D).pairwise, ?_, ?_⟩
    · exact List.pairwise_cons.mpr
        ⟨fun x hx => (hRmem x hx).2, (Finset.sortedLT_sort R).pairwise⟩
    · intro x hx y hy
      have hxn := (hD x ((Finset.mem_sort (· ≤ ·)).mp hx)).2.2
      rcases List.mem_cons.mp hy with rfl | hy
      · exact hxn
      · exact hxn.trans (hRmem y hy).2
  have hsort : xs.toFinset.sort (· ≤ ·) = xs :=
    Erdos590.Larson.sort_toFinset_eq_self_of_pairwise hinc
  have hrun := Advance.run_prelude_build ⟨board.get side, hlegal.1⟩ [] (D.sort (· ≤ ·)) n
    (R.sort (· ≤ ·)) first last (by simpa using hfirst) hlast
  have hreply : Reply board ⟨side, .advance D.card⟩ xs.toFinset (board.update side last) := by
    apply Reply.advance side D.card xs.toFinset last hlegal
    rw [hsort]
    simpa [xs] using hrun
  have hvalues : ∀ x ∈ xs, x ∈ H ∧ B < x := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · have hh := hD x ((Finset.mem_sort (· ≤ ·)).mp hx)
      exact ⟨hh.1, hh.2.1⟩
    · rcases List.mem_cons.mp hx with rfl | hx
      · exact hn
      · exact ⟨(hRmem x hx).1, hn.2.trans (hRmem x hx).2⟩
  exact ⟨xs.toFinset, last, R.sort (· ≤ ·), hreply, hsort,
    fun x hx => (hvalues x (List.mem_toFinset.mp hx)).1,
    (fun x hx => (hvalues x (List.mem_toFinset.mp hx)).2), first, hfirst, hlast⟩

theorem Reply.prescribed_advance_exists {H : Set ℕ} (hH : H.Infinite)
    (board : Board) (side : Bool) (D : Finset ℕ) (n B : ℕ)
    (hlegal : (board.get side).AllowedSize D.card)
    (hD : ∀ x ∈ D, x ∈ H ∧ B < x ∧ x < n) (hn : n ∈ H ∧ B < n) :
    ∃ u last tail, Reply board ⟨side, .advance D.card⟩ u (board.update side last) ∧
      u.sort (· ≤ ·) = D.sort (· ≤ ·) ++ n :: tail ∧
      (↑u : Set ℕ) ⊆ H ∧ ∀ x ∈ u, B < x := by
  obtain ⟨u, last, tail, hr, hsort, hpool, hfresh, _⟩ :=
    prescribed_advance_exists_run hH board side D n B hlegal hD hn
  exact ⟨u, last, tail, hr, hsort, hpool, hfresh⟩

#print axioms Reply.prescribed_advance_exists
#print axioms Reply.prescribed_advance_exists_run

end Erdos591.Positive.Game
