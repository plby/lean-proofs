/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos387.OffDiagonalMoment

/-!
# Reciprocal moments summed over a family of moduli

The high-moment argument sums one modular reciprocal energy over every
admissible modulus.  Its rational diagonal is independent of the modulus;
all modulus dependence is therefore confined to the off-diagonal family
already treated in `OffDiagonalMoment`.
-/

namespace Erdos387

open scoped BigOperators

namespace ReciprocalMoment

/-- Modular reciprocal-energy tuples tagged by the modulus parameter. -/
noncomputable def modularEnergyFamily
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Q : Finset ℕ) (modulus : ℕ → ℕ)
    (A : Finset ι) (U : Finset ℕ) :
    Finset (Σ _D : ℕ, ι → ℕ) := by
  classical
  exact Q.sigma fun D => modularReciprocalEnergyTuples (modulus D) A U

/-- Summing the diagonal/off-diagonal partition over a family of moduli
costs one copy of the rational diagonal for each modulus. -/
theorem modularEnergyFamily_card_le_diagonal_add_offDiagonal
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Q : Finset ℕ) (modulus : ℕ → ℕ)
    (A : Finset ι) (U : Finset ℕ)
    (hUpos : ∀ u ∈ U, 0 < u) :
    (modularEnergyFamily Q modulus A U).card ≤
      Q.card * (reciprocalEnergyTuples A U).card +
        (offDiagonalModulusTuples Q modulus A U).card := by
  classical
  rw [modularEnergyFamily, Finset.card_sigma]
  calc
    ∑ D ∈ Q, (modularReciprocalEnergyTuples (modulus D) A U).card ≤
        ∑ D ∈ Q, ((reciprocalEnergyTuples A U).card +
          (offDiagonalModularReciprocalTuples (modulus D) A U).card) := by
      apply Finset.sum_le_sum
      intro D hD
      exact modularReciprocalEnergyTuples_card_le_diagonal_add_offDiagonal
        (modulus D) A U hUpos
    _ = Q.card * (reciprocalEnergyTuples A U).card +
        ∑ D ∈ Q,
          (offDiagonalModularReciprocalTuples (modulus D) A U).card := by
      simp [Finset.sum_add_distrib]
    _ = Q.card * (reciprocalEnergyTuples A U).card +
        (offDiagonalModulusTuples Q modulus A U).card := by
      rw [offDiagonalModulusTuples, Finset.card_sigma]

/-- Weighted `T₁` moment over a complete family of moduli.  Opening each
fibre square injects into the corresponding modular reciprocal-energy set,
and the sigma cardinality then recombines the separate moduli. -/
theorem sum_halfPhase_fibre_secondMoment_le_modularEnergyFamily
    (ell : ℕ) (Q : Finset ℕ) (modulus : ℕ → ℕ)
    [∀ D, NeZero (modulus D)]
    (U : Finset ℕ) (weight : ℕ → (Fin ell → ℕ) → ℂ)
    (hweight : ∀ D ∈ Q, ∀ s ∈ halfTuples ell U, ‖weight D s‖ ≤ 1) :
    (∑ D ∈ Q, ∑ u : ZMod (modulus D),
        ‖AdditiveOrthogonality.residueFiberSum
          (halfTuples ell U) (halfPhase (modulus D)) (weight D) u‖ ^ 2) ≤
      ((modularEnergyFamily Q modulus (leftHalf ell) U).card : ℝ) := by
  calc
    (∑ D ∈ Q, ∑ u : ZMod (modulus D),
        ‖AdditiveOrthogonality.residueFiberSum
          (halfTuples ell U) (halfPhase (modulus D)) (weight D) u‖ ^ 2) ≤
        ∑ D ∈ Q,
          ((modularReciprocalEnergyTuples (modulus D)
            (leftHalf ell) U).card : ℝ) := by
      apply Finset.sum_le_sum
      intro D hD
      exact halfPhase_fibre_secondMoment_le_modularEnergy
        (modulus D) ell U (weight D) (hweight D hD)
    _ = ((∑ D ∈ Q,
          (modularReciprocalEnergyTuples (modulus D)
            (leftHalf ell) U).card : ℕ) : ℝ) := by
      push_cast
      rfl
    _ = ((modularEnergyFamily Q modulus (leftHalf ell) U).card : ℝ) := by
      rw [modularEnergyFamily, Finset.card_sigma]

end ReciprocalMoment

end Erdos387
