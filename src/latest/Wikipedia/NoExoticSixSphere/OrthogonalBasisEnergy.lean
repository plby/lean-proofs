import Wikipedia.NoExoticSixSphere.OrthogonalAntipodalEnergy

/-!
# Energy in an arbitrary orthonormal basis

The Hilbert--Schmidt form and its integrated path energy can be summed over
any actual orthonormal basis, including a generator's Gram eigenbasis.
-/

open scoped ContDiff

namespace NoExoticSixSphere

open GLOrthonormalization

variable {n : ℕ}

theorem HilbertSchmidt.squareNorm_eq_sum_basis
    (b : OrthonormalBasis (Fin n) ℝ (Vector n)) (A : Vector n →L[ℝ] Vector n) :
    HilbertSchmidt.squareNorm A = ∑ i : Fin n, ‖A (b i)‖ ^ 2 := by
  rw [HilbertSchmidt.squareNorm, HilbertSchmidt.innerForm_eq_trace,
    ← HilbertSchmidt.sum_inner_eq_trace b]
  simp only [real_inner_self_eq_norm_sq]

theorem OrthogonalPathEnergy.energy_eq_basis_sum {A : ℝ → Vector n →L[ℝ] Vector n}
    (hA : ContDiff ℝ ∞ A) (b : OrthonormalBasis (Fin n) ℝ (Vector n)) (l u : ℝ) :
    OrthogonalPathEnergy.energy A l u =
      ∑ i : Fin n, ∫ t : ℝ in l..u, ‖deriv A t (b i)‖ ^ 2 := by
  unfold OrthogonalPathEnergy.energy
  simp_rw [HilbertSchmidt.squareNorm_eq_sum_basis b]
  apply intervalIntegral.integral_finsetSum
  intro i _
  have hc : Continuous (fun t ↦ ‖deriv A t (b i)‖ ^ 2) :=
    ((ContDiff.deriv' (n := ∞) hA).continuous.clm_apply continuous_const).norm.pow 2
  exact hc.intervalIntegrable l u

end NoExoticSixSphere
