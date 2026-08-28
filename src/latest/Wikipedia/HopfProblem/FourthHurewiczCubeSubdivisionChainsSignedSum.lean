import Wikipedia.HopfProblem.HigherHurewiczCubeTriangulationGeometry
import Mathlib.Data.Fintype.Perm

/-!
# Cancellation of signed coordinate permutations

A family unchanged by one coordinate transposition has zero alternating
sum. This is a genuine finite pairing argument and requires no absence
of two-torsion in the target group.
-/

noncomputable section

namespace Wikipedia.HopfProblem.FourthHurewicz.CubeSubdivision

open HigherHurewicz.CubeTriangulation

theorem signed_sum_eq_zero_of_swap_invariant {n : ℕ} {A : Type*} [AddCommGroup A]
    (i j : Fin n) (hij : i ≠ j) (f : Equiv.Perm (Fin n) → A)
    (hf : ∀ e, f ((Equiv.swap i j).trans e) = f e) :
    ∑ e, cubeOrientation e • f e = 0 := by
  classical
  apply Finset.sum_ninvolution (fun e => (Equiv.swap i j).trans e)
  · intro e
    rw [cubeOrientation_swap e hij, hf, neg_smul, add_neg_cancel]
  · intro e _ he
    have h := congrArg (fun k : Equiv.Perm (Fin n) => k i) he
    have h' : e j = e i := by simpa using h
    exact hij (e.injective h').symm
  · intro e
    exact Finset.mem_univ _
  · intro e
    ext k
    simp

theorem signed_sum_constant_eq_zero {n : ℕ} [Nontrivial (Fin n)]
    {A : Type*} [AddCommGroup A] (a : A) :
    ∑ e : Equiv.Perm (Fin n), cubeOrientation e • a = 0 := by
  obtain ⟨i, j, hij⟩ := exists_pair_ne (Fin n)
  exact signed_sum_eq_zero_of_swap_invariant i j hij (fun _ => a) (fun _ => rfl)

end Wikipedia.HopfProblem.FourthHurewicz.CubeSubdivision
