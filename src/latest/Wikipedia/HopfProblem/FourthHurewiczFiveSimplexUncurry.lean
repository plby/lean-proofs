import Wikipedia.HopfProblem.FourthHurewiczFiveSimplexUncurryOperations
import Wikipedia.HopfProblem.FourthHurewiczCubeSubdivisionNativeSymmetries

/-!
# Uncurrying and permutations of the outer cube coordinates

The inner one-loop coordinate is prepended. A swap of two outer
coordinates therefore becomes the swap of their successor coordinates
in the uncurried cube, with coordinate zero unchanged. This is an
equality of the original generalized loops, not only of homotopy classes.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.HigherHurewicz.CubicalBoundary

open NativeSubdivision

variable {X : Type*} [TopologicalSpace X] {x : X} {n : ℕ}

/-- Prepending the inner coordinate shifts both swapped outer coordinates by one. -/
theorem uncurryLoop_swap
    (p : GenLoop (Fin n) (GenLoop (Fin 1) X x) GenLoop.const) (i j : Fin n) :
    uncurryLoop (permuteCubeLoop p (Equiv.swap i j)) =
      permuteCubeLoop (uncurryLoop p) (Equiv.swap i.succ j.succ) := by
  have hzero : Equiv.swap i.succ j.succ (0 : Fin (n + 1)) = 0 :=
    Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero i).symm (Fin.succ_ne_zero j).symm
  have hsucc (k : Fin n) :
      Equiv.swap i.succ j.succ k.succ = (Equiv.swap i j k).succ := by
    by_cases hki : k = i
    · subst k
      simp
    by_cases hkj : k = j
    · subst k
      simp
    have hki' : k.succ ≠ i.succ := fun h => hki (Fin.succ_inj.mp h)
    have hkj' : k.succ ≠ j.succ := fun h => hkj (Fin.succ_inj.mp h)
    rw [Equiv.swap_apply_of_ne_of_ne hki' hkj',
      Equiv.swap_apply_of_ne_of_ne hki hkj]
  apply GenLoop.ext
  intro u
  change p (fun k => u (Equiv.swap i j k).succ) (fun _ => u 0) =
    p (fun k => u (Equiv.swap i.succ j.succ k.succ))
      (fun _ => u (Equiv.swap i.succ j.succ 0))
  simp only [hsucc, hzero]

end Wikipedia.HopfProblem.HigherHurewicz.CubicalBoundary
