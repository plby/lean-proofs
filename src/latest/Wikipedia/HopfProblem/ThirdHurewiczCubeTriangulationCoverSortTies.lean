import Wikipedia.HopfProblem.ThirdHurewiczCubeTriangulationCoverSort
import Mathlib.Tactic.FinCases

/-!
# Agreement on overlaps of sorting cells

Two sorting permutations differ only by adjacent swaps at equal coordinate
values. A function invariant under these two elementary tie swaps therefore
has the same value on every permutation cell containing the point.
-/

noncomputable section

namespace Wikipedia.HopfProblem.ThirdHurewicz.CubeTriangulation

variable {α : Type*} [LinearOrder α]

theorem SortedCoordinates.le_first {u : Fin 3 → α} {e : Equiv.Perm (Fin 3)}
    (he : SortedCoordinates u e) (i : Fin 3) : u i ≤ u (e 0) := by
  obtain ⟨j, rfl⟩ := e.surjective i
  fin_cases j
  · exact le_rfl
  · exact he.2
  · exact he.1.trans he.2

theorem sorted_first_value_eq (u : Fin 3 → α) {e f : Equiv.Perm (Fin 3)}
    (he : SortedCoordinates u e) (hf : SortedCoordinates u f) :
    u (e 0) = u (f 0) :=
  le_antisymm (hf.le_first (e 0)) (he.le_first (f 0))

theorem SortedCoordinates.swap01 {u : Fin 3 → α} {e : Equiv.Perm (Fin 3)}
    (he : SortedCoordinates u e) (ht : u (e 0) = u (e 1)) :
    SortedCoordinates u ((Equiv.swap 0 1).trans e) := by
  simpa [SortedCoordinates, Equiv.swap_apply_def] using
    And.intro (he.1.trans he.2) ht.le

theorem SortedCoordinates.swap12 {u : Fin 3 → α} {e : Equiv.Perm (Fin 3)}
    (he : SortedCoordinates u e) (ht : u (e 1) = u (e 2)) :
    SortedCoordinates u ((Equiv.swap 1 2).trans e) := by
  simpa [SortedCoordinates, Equiv.swap_apply_def] using
    And.intro ht.le (he.1.trans he.2)

private theorem permutation_ext_zero_one {e f : Equiv.Perm (Fin 3)}
    (h0 : e 0 = f 0) (h1 : e 1 = f 1) : e = f := by
  apply Equiv.ext
  intro i
  fin_cases i
  · exact h0
  · exact h1
  · obtain ⟨j, hj⟩ := f.surjective (e 2)
    fin_cases j
    · exact ((by decide : (0 : Fin 3) ≠ 2) (e.injective (h0.trans hj))).elim
    · exact ((by decide : (1 : Fin 3) ≠ 2) (e.injective (h1.trans hj))).elim
    · exact hj.symm

private theorem eq_of_sorted_same_first (u : Fin 3 → α) {A : Type*}
    (F : Equiv.Perm (Fin 3) → A)
    (h12 : ∀ e, SortedCoordinates u e → u (e 1) = u (e 2) →
      F e = F ((Equiv.swap 1 2).trans e))
    {e f : Equiv.Perm (Fin 3)} (he : SortedCoordinates u e)
    (hf : SortedCoordinates u f) (h0 : e 0 = f 0) : F e = F f := by
  obtain ⟨i, hi⟩ := e.surjective (f 1)
  fin_cases i
  · exact ((by decide : (0 : Fin 3) ≠ 1)
      (f.injective (h0.symm.trans hi))).elim
  · exact congrArg F (permutation_ext_zero_one h0 hi)
  · have hp : (Equiv.swap 1 2).trans e = f :=
      permutation_ext_zero_one
        (by simpa [Equiv.swap_apply_def] using h0)
        (by simpa [Equiv.swap_apply_def] using hi)
    have hrev : u (e 1) ≤ u (e 2) := by
      have hh := hf.1
      rw [← hp] at hh
      simpa [Equiv.swap_apply_def] using hh
    exact (h12 e he (le_antisymm hrev he.1)).trans (congrArg F hp)

/-- Invariance under sorted adjacent tie swaps implies agreement on every
sorting-cell overlap. The maps are actual permutations of the three positions. -/
theorem eq_of_sorted_adjacent (u : Fin 3 → α) {A : Type*}
    (F : Equiv.Perm (Fin 3) → A)
    (h01 : ∀ e, SortedCoordinates u e → u (e 0) = u (e 1) →
      F e = F ((Equiv.swap 0 1).trans e))
    (h12 : ∀ e, SortedCoordinates u e → u (e 1) = u (e 2) →
      F e = F ((Equiv.swap 1 2).trans e))
    {e f : Equiv.Perm (Fin 3)} (he : SortedCoordinates u e)
    (hf : SortedCoordinates u f) : F e = F f := by
  obtain ⟨i, hi⟩ := e.surjective (f 0)
  fin_cases i
  · exact eq_of_sorted_same_first u F h12 he hf hi
  · change e 1 = f 0 at hi
    have ht : u (e 0) = u (e 1) := by
      rw [hi]
      exact sorted_first_value_eq u he hf
    have hg := he.swap01 ht
    have hg0 : ((Equiv.swap 0 1).trans e) 0 = f 0 := by
      simpa [Equiv.swap_apply_def] using hi
    exact (h01 e he ht).trans (eq_of_sorted_same_first u F h12 hg hf hg0)
  · change e 2 = f 0 at hi
    have ht : u (e 0) = u (e 2) := by
      rw [hi]
      exact sorted_first_value_eq u he hf
    have ht12 : u (e 1) = u (e 2) :=
      le_antisymm (he.2.trans ht.le) he.1
    have hg := he.swap12 ht12
    have ht01 : u (((Equiv.swap 1 2).trans e) 0) =
        u (((Equiv.swap 1 2).trans e) 1) := by
      simpa [Equiv.swap_apply_def] using ht
    have hh := hg.swap01 ht01
    have hh0 : ((Equiv.swap 0 1).trans ((Equiv.swap 1 2).trans e)) 0 = f 0 := by
      simpa [Equiv.swap_apply_def] using hi
    exact (h12 e he ht12).trans ((h01 _ hg ht01).trans
      (eq_of_sorted_same_first u F h12 hh hf hh0))

/-- All sorting permutations give exactly the same ordered coordinate values. -/
theorem sorted_values_eq (u : Fin 3 → α) {e f : Equiv.Perm (Fin 3)}
    (he : SortedCoordinates u e) (hf : SortedCoordinates u f) :
    ∀ i : Fin 3, u (e i) = u (f i) := by
  have hfun : (fun i => u (e i)) = (fun i => u (f i)) :=
    eq_of_sorted_adjacent u (fun g i => u (g i))
      (fun g _ ht => by
        funext i
        fin_cases i <;> simp [Equiv.swap_apply_def, ht])
      (fun g _ ht => by
        funext i
        fin_cases i <;> simp [Equiv.swap_apply_def, ht]) he hf
  exact congrFun hfun

end Wikipedia.HopfProblem.ThirdHurewicz.CubeTriangulation
