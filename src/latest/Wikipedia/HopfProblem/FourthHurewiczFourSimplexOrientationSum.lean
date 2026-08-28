import Wikipedia.HopfProblem.HigherHurewiczCubeTriangulationGeometry

/-!
# Cancellation of the coordinate-permutation orientations

Pairing each coordinate order with a fixed transposition cancels its sign.
This works in every dimension at least two, without enumerating permutations.
-/

noncomputable section

namespace Wikipedia.HopfProblem.HigherHurewicz.SimplexGeometry

open CubeTriangulation

/-- Even and odd coordinate orders have zero total orientation. -/
theorem cubeOrientation_sum (n : ℕ) :
    ∑ e : Equiv.Perm (Fin (n + 2)), cubeOrientation e = 0 := by
  have hij : (0 : Fin (n + 2)) ≠ 1 := Fin.zero_ne_one
  have h := Equiv.sum_comp (Equiv.mulRight (Equiv.swap (0 : Fin (n + 2)) 1))
    (cubeOrientation (n := n + 2))
  change (∑ e : Equiv.Perm (Fin (n + 2)),
      cubeOrientation ((Equiv.swap 0 1).trans e)) =
      ∑ e : Equiv.Perm (Fin (n + 2)), cubeOrientation e at h
  simp_rw [cubeOrientation_swap _ hij] at h
  rw [Finset.sum_neg_distrib] at h
  omega

/-- The same cancellation with coefficients in any additive commutative group. -/
theorem cubeOrientation_constant_sum {A : Type*} [AddCommGroup A] (n : ℕ) (a : A) :
    (∑ e : Equiv.Perm (Fin (n + 2)), cubeOrientation e • a) = 0 := by
  have h := map_sum (zmultiplesHom A a) (cubeOrientation (n := n + 2)) Finset.univ
  rw [cubeOrientation_sum] at h
  exact h.symm.trans (zero_zsmul a)

end Wikipedia.HopfProblem.HigherHurewicz.SimplexGeometry
