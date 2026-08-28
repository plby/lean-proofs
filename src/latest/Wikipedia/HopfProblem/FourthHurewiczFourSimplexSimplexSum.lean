import Wikipedia.HopfProblem.FourthHurewiczFourSimplexQuotientCells
import Wikipedia.HopfProblem.FourthHurewiczFourSimplexOrientationSum
import Wikipedia.HopfProblem.FourthHurewiczFourSimplexCycles

/-!
# The signed permutation-simplex chain of a based simplex

The identity cell recovers the original simplex; all other cells are
constant.  Cancellation of the permutation signs therefore gives the
original simplex minus the constant simplex, in every dimension at least two.
-/

noncomputable section

namespace Wikipedia.HopfProblem.HigherHurewicz.SimplexGeometry

open FirstHurewicz CubeTriangulation

variable {X : Type} [TopologicalSpace X] {x : X}

/-- Literal equality in the original singular chain group, without enumerating cells. -/
theorem basedSimplex_simplexChain_sum {n : ℕ} (τ : BasedSimplex (n + 2) x) :
    (∑ e : Equiv.Perm (Fin (n + 2)), cubeOrientation e •
      simplexChain X (n + 2) ((basedSimplexLoop τ).val.comp (cubeSimplex e))) =
        correctedSimplexChain (n + 2) x τ.val := by
  classical
  let c := constantSimplexChain (n + 2) x
  have heq (e : Equiv.Perm (Fin (n + 2))) :
      cubeOrientation e •
        simplexChain X (n + 2) ((basedSimplexLoop τ).val.comp (cubeSimplex e)) =
      (if e = Equiv.refl (Fin (n + 2)) then correctedSimplexChain (n + 2) x τ.val else 0) +
        cubeOrientation e • c := by
    by_cases he : e = Equiv.refl (Fin (n + 2))
    · subst e
      rw [basedSimplexLoop_cubeSimplex_refl, cubeOrientation_refl,
        one_smul, if_pos rfl, one_smul]
      change simplexChain X (n + 2) τ.val = (simplexChain X (n + 2) τ.val - c) + c
      exact (sub_add_cancel _ _).symm
    · rw [basedSimplexLoop_cubeSimplex_other τ e he, if_neg he, zero_add]
      rfl
  calc
    _ = ∑ e : Equiv.Perm (Fin (n + 2)),
        ((if e = Equiv.refl (Fin (n + 2)) then correctedSimplexChain (n + 2) x τ.val else 0) +
          cubeOrientation e • c) := Finset.sum_congr rfl (fun e _ => heq e)
    _ = correctedSimplexChain (n + 2) x τ.val +
        (∑ e : Equiv.Perm (Fin (n + 2)), cubeOrientation e) • c := by
      rw [Finset.sum_add_distrib]
      have hc : (∑ e : Equiv.Perm (Fin (n + 2)), cubeOrientation e) • c =
          ∑ e : Equiv.Perm (Fin (n + 2)), cubeOrientation e • c := by
        let f : ℤ →+ Chains X (n + 2) :=
          { toFun := fun k => k • c
            map_zero' := zero_zsmul c
            map_add' := fun a b => add_zsmul c a b }
        exact map_sum f cubeOrientation Finset.univ
      rw [← hc]
      simp
    _ = correctedSimplexChain (n + 2) x τ.val := by
      rw [cubeOrientation_sum n, zero_smul, add_zero]

end Wikipedia.HopfProblem.HigherHurewicz.SimplexGeometry

namespace Wikipedia.HopfProblem.FourthHurewicz

open FirstHurewicz HigherHurewicz.CubeTriangulation

variable {X : Type} [TopologicalSpace X] {x : X}

/-- The original signed twenty-four-cell chain is exactly the corrected four-simplex. -/
theorem basedFourSimplex_simplexChain_sum (τ : BasedFourSimplex x) :
    (∑ e : Equiv.Perm (Fin 4), cubeOrientation e •
      simplexChain X 4 ((basedFourSimplexLoop τ).val.comp (cubeSimplex e))) =
        basedFourSimplexChain τ :=
  HigherHurewicz.SimplexGeometry.basedSimplex_simplexChain_sum τ

end Wikipedia.HopfProblem.FourthHurewicz
