import Wikipedia.HopfProblem.HigherHurewiczCubeTriangulationSortSwap
import Wikipedia.HopfProblem.HigherHurewiczCubeTriangulationSortStabilizer

/-!
# Adjacent-tie agreement on all finite-dimensional sorting overlaps

Sorted permutations have the same coordinate tuple. Their relative
permutation therefore preserves that tuple, and support induction reduces
it to equal-value transpositions. Each such transposition is a product of
the actual adjacent tie swaps along its interval.
-/

noncomputable section

namespace Wikipedia.HopfProblem.HigherHurewicz.CubeTriangulation

variable {n : ℕ} {α : Type*} [LinearOrder α]

/-- Adjacent equal-coordinate compatibility suffices on every sorting overlap,
in every positive cube dimension. -/
theorem eq_of_sorted_adjacent (u : Fin (n + 1) → α) {A : Type*}
    (F : Equiv.Perm (Fin (n + 1)) → A)
    (hswap : ∀ e, SortedCoordinates u e → ∀ i : Fin n,
      u (e i.castSucc) = u (e i.succ) →
        F e = F ((Equiv.swap i.castSucc i.succ).trans e))
    {e f : Equiv.Perm (Fin (n + 1))} (he : SortedCoordinates u e)
    (hf : SortedCoordinates u f) : F e = F f := by
  have hr : ∀ i, u (e ((f.trans e.symm) i)) = u (e i) := by
    intro i
    simpa only [Equiv.trans_apply, Equiv.apply_symm_apply] using
      (sorted_values_eq u he hf i).symm
  have hG : F ((1 : Equiv.Perm (Fin (n + 1))).trans e) =
      F ((f.trans e.symm).trans e) :=
    eq_of_value_preserving_swaps (fun i => u (e i)) (fun r => F (r.trans e))
      (by
        intro r hvalues a b hab
        have hsorted : SortedCoordinates u (r.trans e) := by
          intro i j hij
          change u (e (r j)) ≤ u (e (r i))
          rw [hvalues, hvalues]
          exact he hij
        have ht : u ((r.trans e) (r.symm a)) = u ((r.trans e) (r.symm b)) := by
          simpa only [Equiv.trans_apply, Equiv.apply_symm_apply] using hab
        have hh := eq_swap_of_sorted_tie u F hswap hsorted (r.symm a) (r.symm b) ht
        refine hh.trans (congrArg F ?_)
        apply Equiv.ext
        intro i
        change e ((r * Equiv.swap (r.symm a) (r.symm b)) i) =
          e ((Equiv.swap a b * r) i)
        exact congrArg (fun q : Equiv.Perm (Fin (n + 1)) => e (q i))
          (Equiv.swap_mul_eq_mul_swap r a b).symm)
      (f.trans e.symm) hr
  simpa only [Equiv.Perm.one_def, Equiv.refl_trans, Equiv.trans_assoc,
    Equiv.symm_trans_self, Equiv.trans_refl] using hG

/-- In dimension zero there is only one permutation, so no compatibility
condition is required. -/
theorem eq_of_permutations_fin_zero {A : Type*} (F : Equiv.Perm (Fin 0) → A)
    (e f : Equiv.Perm (Fin 0)) : F e = F f :=
  congrArg F (Subsingleton.elim e f)

end Wikipedia.HopfProblem.HigherHurewicz.CubeTriangulation
