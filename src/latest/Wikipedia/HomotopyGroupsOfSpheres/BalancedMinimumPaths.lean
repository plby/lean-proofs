import Wikipedia.HomotopyGroupsOfSpheres.SymmetricUnitaryMinimumGenerator
import Wikipedia.HomotopyGroupsOfSpheres.BalancedMinimumExponential

/-!
# The balanced rotations are exactly the smooth minimum-energy paths

This is the equality case for arbitrary smooth paths from the identity
to the antipode in the actual symmetric determinant-one unitary space.
The recovered parameter is the previously constructed balanced real
involution, and the path formula is the original rotation map.
-/

noncomputable section

open scoped Matrix.Norms.Operator ContDiff

namespace Wikipedia.HomotopyGroupsOfSpheres.BalancedRealInvolutions

open ComplexMatrixRealRepresentation

theorem real_dimension_cast (n : ℕ) :
    ((2 * Fintype.card (Index n) : ℕ) : ℝ) = 4 * (n : ℝ) := by
  simp only [Index, Fintype.card_sum, Fintype.card_fin, Nat.cast_mul, Nat.cast_ofNat,
    Nat.cast_add]
  ring

theorem energy_rotation {n : ℕ} (J : Space n) :
    QuaternionicSymmetricMatrices.energy (fun t ↦ rotation J (t * Real.pi)) =
      (4 * n : ℝ) * Real.pi ^ 2 := by
  have hpath (t : ℝ) : action (rotation J (t * Real.pi)).val.val.val =
      ((1 : NoExoticSixSphere.GLOrthonormalization.OrthogonalOperators
          (2 * Fintype.card (Index n))) *
        NoExoticSixSphere.OrthogonalExponential.exp
          (t • skewMap (minimumGenerator J))).val.val := by
    have h := specialOrthogonal_curve (minimumGenerator J) t
    rw [exponentialCurve_minimumGenerator] at h
    simpa only [one_mul] using! congrArg
      (fun B : NoExoticSixSphere.GLOrthonormalization.OrthogonalOperators
        (2 * Fintype.card (Index n)) ↦ B.val.val) h
  unfold QuaternionicSymmetricMatrices.energy
  simp_rw [hpath]
  rw [NoExoticSixSphere.OrthogonalPathEnergy.energy_left_exp]
  change (1 - 0 : ℝ) * NoExoticSixSphere.HilbertSchmidt.squareNorm
    (action (ImaginarySymmetricMatrices.imaginary (minimumGenerator J).val)) = _
  rw [squareNorm_action_imaginary, minimumGenerator_squareNorm]
  ring

theorem eq_rotation_of_energy_eq_min {n : ℕ}
    {γ : ℝ → QuaternionicSymmetricMatrices.SpecialSpace (Index n)}
    (hγ : ContDiff ℝ ∞ (fun t ↦ (γ t).val.val.val))
    (hzero : γ 0 = QuaternionicSymmetricMatrices.specialIdentity)
    (hone : γ 1 = antipode n)
    (henergy : QuaternionicSymmetricMatrices.energy γ = (4 * n : ℝ) * Real.pi ^ 2) :
    ∃ J : Space n, ∀ t ∈ Set.Icc (0 : ℝ) 1, γ t = rotation J (t * Real.pi) := by
  have he : QuaternionicSymmetricMatrices.energy γ =
      (2 * Fintype.card (Index n) : ℕ) * Real.pi ^ 2 := by
    rw [real_dimension_cast]
    exact henergy
  have hend : (γ 1).val.val.val = -1 := by rw [hone, antipode_matrix]
  obtain ⟨A, hsym, hsq, htrace, hpath⟩ :=
    QuaternionicSymmetricMatrices.exists_minimum_generator hγ hzero hend he
  let J := ofRelations n A hsym hsq htrace
  refine ⟨J, ?_⟩
  intro t ht
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  exact (hpath t ht).trans (exp_imaginary_involution J (t * Real.pi))

theorem energy_eq_min_iff {n : ℕ}
    {γ : ℝ → QuaternionicSymmetricMatrices.SpecialSpace (Index n)}
    (hγ : ContDiff ℝ ∞ (fun t ↦ (γ t).val.val.val))
    (hzero : γ 0 = QuaternionicSymmetricMatrices.specialIdentity)
    (hone : γ 1 = antipode n) :
    QuaternionicSymmetricMatrices.energy γ = (4 * n : ℝ) * Real.pi ^ 2 ↔
      ∃ J : Space n, ∀ t ∈ Set.Icc (0 : ℝ) 1, γ t = rotation J (t * Real.pi) := by
  constructor
  · exact eq_rotation_of_energy_eq_min hγ hzero hone
  · rintro ⟨J, hJ⟩
    have he : QuaternionicSymmetricMatrices.energy γ =
        QuaternionicSymmetricMatrices.energy (fun t ↦ rotation J (t * Real.pi)) := by
      apply NoExoticSixSphere.OrthogonalPathEnergy.energy_congr_Icc zero_le_one
      intro t ht
      exact congrArg (fun B : QuaternionicSymmetricMatrices.SpecialSpace (Index n) ↦
        action B.val.val.val) (hJ t ht)
    exact he.trans (energy_rotation J)

end Wikipedia.HomotopyGroupsOfSpheres.BalancedRealInvolutions
