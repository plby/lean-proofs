import Wikipedia.HomotopyGroupsOfSpheres.SymmetricUnitaryNegativeVariation
import Wikipedia.HomotopyGroupsOfSpheres.SymmetricUnitaryAntipodalSpectrum
import Wikipedia.HomotopyGroupsOfSpheres.BalancedRotationPaths

/-!
# Negative constrained variations at every nonminimal balanced antipodal generator

The signed odd spectral block supplies an injective `n`-parameter real
family. Every nonzero coefficient vector has strictly negative actual
second energy derivative. The entire variation remains in the symmetric
determinant-one space and fixes the identity and the antipode.
-/

noncomputable section

namespace Wikipedia.HomotopyGroupsOfSpheres.BalancedRealInvolutions

open RealSymmetricMixing ImaginarySymmetricMatrices

theorem exists_antipodal_real_commutator_family (n : ℕ)
    (A : Matrix (Index n) (Index n) ℝ) (hsym : A.transpose = A) (htrace : A.trace = 0)
    (hexp : NormedSpace.exp (imaginary A) = -1)
    (hmin : A * A ≠ Real.pi ^ 2 • (1 : Matrix (Index n) (Index n) ℝ)) :
    ∃ L : (Fin n → ℝ) →ₗ[ℝ] DirectionSpace (Index n), Function.Injective L ∧
      ∀ c, c ≠ 0 → 4 * Real.pi ^ 2 * RealMatrixSquareNorm.squareNorm (L c).val <
        RealMatrixSquareNorm.squareNorm (RealMatrixSquareNorm.commutator A (L c).val) := by
  obtain ⟨U, m, hA, htr⟩ := antipodal_diagonalization A hsym hexp
  have hsum : ∑ a, (2 * (m a : ℝ) + 1) = 0 := by
    have he : Real.pi * (∑ a, (2 * (m a : ℝ) + 1)) = 0 := by
      rw [Finset.mul_sum]
      exact htr.symm.trans htrace
    exact (mul_eq_zero.mp he).resolve_left Real.pi_ne_zero
  have hfast : ∃ a, m a ≠ 0 ∧ m a ≠ -1 := by
    by_contra h
    push Not at h
    have hm (a : Index n) : m a = 0 ∨ m a = -1 := by
      by_cases ha : m a = 0
      · exact Or.inl ha
      · exact Or.inr (h a ha)
    apply hmin
    rw [hA]
    exact minimal_odd_conjugate_square U m hm
  obtain ⟨L, hL, _, hstrict⟩ := exists_balanced_commutator_family n m hsum hfast U
  refine ⟨L, hL, ?_⟩
  simpa only [← hA] using hstrict

theorem exponential_eq_antipode (n : ℕ) (A : DirectionSpace (Index n))
    (hexp : NormedSpace.exp (imaginary A.val) = -1) :
    QuaternionicSymmetricMatrices.exponential A = antipode n := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  exact hexp.trans (antipode_matrix n).symm

theorem exists_antipodal_negative_variation_family (n : ℕ) (A : DirectionSpace (Index n))
    (hexp : NormedSpace.exp (imaginary A.val) = -1)
    (hmin : A.val * A.val ≠ Real.pi ^ 2 • (1 : Matrix (Index n) (Index n) ℝ)) :
    ∃ L : (Fin n → ℝ) →ₗ[ℝ] DirectionSpace (Index n), Function.Injective L ∧
      (∀ c s, QuaternionicSymmetricMatrices.endpointVariation A (L c) s 0 =
          QuaternionicSymmetricMatrices.specialIdentity ∧
        QuaternionicSymmetricMatrices.endpointVariation A (L c) s 1 = antipode n) ∧
      ∀ c, c ≠ 0 → deriv (deriv (fun s ↦ QuaternionicSymmetricMatrices.energy
        (fun t ↦ QuaternionicSymmetricMatrices.endpointVariation A (L c) s t))) 0 < 0 := by
  obtain ⟨L, hL, hstrict⟩ := exists_antipodal_real_commutator_family n A.val
    A.property.1 A.property.2 hexp hmin
  refine ⟨L, hL, ?_, ?_⟩
  · intro c s
    exact ⟨QuaternionicSymmetricMatrices.endpointVariation_at_zero A (L c) s,
      (QuaternionicSymmetricMatrices.endpointVariation_at_one A (L c) s).trans
        (exponential_eq_antipode n A hexp)⟩
  · intro c hc
    exact QuaternionicSymmetricMatrices.negative_secondDerivative_of_real_commutator
      A (L c) (hstrict c hc)

end Wikipedia.HomotopyGroupsOfSpheres.BalancedRealInvolutions
