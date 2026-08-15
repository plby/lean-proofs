/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos387.ModularReciprocalEnergy
import ErdosProblems.Erdos387.RoughDivisorBound

/-!
# Finite reciprocal moments

This file packages the exact passage used in the high-moment argument of
BNPZ Lemma 9.2.  Two `ell`-tuples in the same modular reciprocal-sum fibre
are concatenated into one `2 * ell`-coordinate modular-energy tuple.  The
diagonal part is then controlled by the squarefull reciprocal-energy bound,
while the off-diagonal part carries a nonzero cleared numerator divisible by
the modulus.
-/

namespace Erdos387

open scoped BigOperators

namespace ReciprocalMoment

/-- All `ell`-tuples with coordinates in `U`. -/
noncomputable def halfTuples (ell : ℕ) (U : Finset ℕ) :
    Finset (Fin ell → ℕ) := by
  classical
  exact Fintype.piFinset fun _ : Fin ell => U

/-- The modular reciprocal-sum phase of one half tuple. -/
noncomputable def halfPhase (q : ℕ) {ell : ℕ}
    (s : Fin ell → ℕ) : ZMod q :=
  modularReciprocalSum q Finset.univ s

/-- Concatenate two half tuples, using the sum type as the `2 * ell`
coordinate index. -/
def combinePair {ell : ℕ}
    (ab : (Fin ell → ℕ) × (Fin ell → ℕ)) :
    (Fin ell ⊕ Fin ell) → ℕ :=
  Sum.elim ab.1 ab.2

/-- The left copy of `Fin ell` inside the sum index. -/
noncomputable def leftHalf (ell : ℕ) :
    Finset (Fin ell ⊕ Fin ell) := by
  classical
  exact Finset.univ.map
    ⟨Sum.inl, Sum.inl_injective⟩

/-- The right copy of `Fin ell` inside the sum index. -/
noncomputable def rightHalf (ell : ℕ) :
    Finset (Fin ell ⊕ Fin ell) := by
  classical
  exact Finset.univ.map
    ⟨Sum.inr, Sum.inr_injective⟩

theorem univ_sdiff_leftHalf (ell : ℕ) :
    (Finset.univ : Finset (Fin ell ⊕ Fin ell)) \ leftHalf ell =
      rightHalf ell := by
  classical
  ext i
  cases i <;> simp [leftHalf, rightHalf]

theorem combinePair_injective {ell : ℕ} :
    Function.Injective (combinePair (ell := ell)) := by
  intro ab cd h
  apply Prod.ext
  · funext i
    exact congrFun h (Sum.inl i)
  · funext i
    exact congrFun h (Sum.inr i)

theorem modularReciprocalSum_leftHalf_combinePair
    (q ell : ℕ)
    (ab : (Fin ell → ℕ) × (Fin ell → ℕ)) :
    modularReciprocalSum q (leftHalf ell) (combinePair ab) =
      halfPhase q ab.1 := by
  classical
  simp [modularReciprocalSum, leftHalf, combinePair, halfPhase]

theorem modularReciprocalSum_rightHalf_combinePair
    (q ell : ℕ)
    (ab : (Fin ell → ℕ) × (Fin ell → ℕ)) :
    modularReciprocalSum q
        ((Finset.univ : Finset (Fin ell ⊕ Fin ell)) \ leftHalf ell)
        (combinePair ab) =
      halfPhase q ab.2 := by
  classical
  rw [univ_sdiff_leftHalf]
  simp [modularReciprocalSum, rightHalf, combinePair, halfPhase]

theorem equalPhasePair_mapsTo_modularEnergy
    (q ell : ℕ) (U : Finset ℕ) :
    ((AdditiveOrthogonality.equalPhasePairs (halfTuples ell U)
        (halfPhase q) :
          Finset ((Fin ell → ℕ) × (Fin ell → ℕ))) :
        Set ((Fin ell → ℕ) × (Fin ell → ℕ))).MapsTo
      (combinePair (ell := ell))
      (modularReciprocalEnergyTuples q (leftHalf ell) U :
        Set ((Fin ell ⊕ Fin ell) → ℕ)) := by
  classical
  intro ab hab
  change ab ∈ AdditiveOrthogonality.equalPhasePairs
    (halfTuples ell U) (halfPhase q) at hab
  change combinePair ab ∈
    modularReciprocalEnergyTuples q (leftHalf ell) U
  rw [AdditiveOrthogonality.equalPhasePairs, Finset.mem_filter,
    Finset.mem_product] at hab
  rw [modularReciprocalEnergyTuples, Finset.mem_filter]
  constructor
  · rw [Fintype.mem_piFinset]
    intro i
    cases i with
    | inl i =>
        exact Fintype.mem_piFinset.mp hab.1.1 i
    | inr i =>
        exact Fintype.mem_piFinset.mp hab.1.2 i
  · rw [modularReciprocalSum_leftHalf_combinePair,
      modularReciprocalSum_rightHalf_combinePair]
    exact hab.2

/-- Equal modular-phase pairs inject into the corresponding modular
reciprocal-energy set. -/
theorem equalPhasePairs_card_le_modularEnergy
    (q ell : ℕ) (U : Finset ℕ) :
    (AdditiveOrthogonality.equalPhasePairs (halfTuples ell U)
      (halfPhase q)).card ≤
      (modularReciprocalEnergyTuples q (leftHalf ell) U).card := by
  classical
  apply Finset.card_le_card_of_injOn (combinePair (ell := ell))
    (equalPhasePair_mapsTo_modularEnergy q ell U)
  exact combinePair_injective.injOn

/-- Weighted second moments of the modular reciprocal phase are bounded by
the modular reciprocal-energy cardinality. -/
theorem halfPhase_fibre_secondMoment_le_modularEnergy
    (q ell : ℕ) [NeZero q] (U : Finset ℕ)
    (weight : (Fin ell → ℕ) → ℂ)
    (hweight : ∀ s ∈ halfTuples ell U, ‖weight s‖ ≤ 1) :
    (∑ u : ZMod q,
        ‖AdditiveOrthogonality.residueFiberSum
          (halfTuples ell U) (halfPhase q) weight u‖ ^ 2) ≤
      ((modularReciprocalEnergyTuples q (leftHalf ell) U).card : ℝ) := by
  exact (AdditiveOrthogonality.sum_norm_residueFiberSum_sq_le
    (halfTuples ell U) (halfPhase q) weight hweight).trans
      (by exact_mod_cast equalPhasePairs_card_le_modularEnergy q ell U)

/-- The diagonal energy on the sum index has the same elementary envelope
as the `Fin (2 * ell)` formulation. -/
theorem diagonalEnergy_card_le_envelope
    (ell : ℕ) (U : Finset ℕ) {z T L : ℕ}
    (hz : 1 < z) (hUpos : ∀ u ∈ U, 0 < u)
    (hUle : ∀ u ∈ U, u ≤ T)
    (hUrough : ∀ u ∈ U, IsZRough z u)
    (hTPow : T ^ (2 * ell) < z ^ (L + 1)) :
    (reciprocalEnergyTuples (leftHalf ell) U).card ≤
      T ^ ell * 2 ^ L * (2 ^ L) ^ (2 * ell) := by
  have hcard : Fintype.card (Fin ell ⊕ Fin ell) = 2 * ell := by
    simp [two_mul]
  have hTPow' : T ^ Fintype.card (Fin ell ⊕ Fin ell) < z ^ (L + 1) := by
    simpa [hcard] using hTPow
  simpa [hcard, sqrt_pow_two_mul] using
    (reciprocalEnergyTuples_card_le_roughSquarefull_envelope
      (leftHalf ell) U hz hUpos hUle hUrough hTPow')

/-- Complete diagonal/off-diagonal finite moment bound. -/
theorem modularEnergy_card_le_diagonalEnvelope_add_offDiagonal
    (q ell : ℕ) (U : Finset ℕ) {z T L : ℕ}
    (hz : 1 < z) (hUpos : ∀ u ∈ U, 0 < u)
    (hUle : ∀ u ∈ U, u ≤ T)
    (hUrough : ∀ u ∈ U, IsZRough z u)
    (hTPow : T ^ (2 * ell) < z ^ (L + 1)) :
    (modularReciprocalEnergyTuples q (leftHalf ell) U).card ≤
      T ^ ell * 2 ^ L * (2 ^ L) ^ (2 * ell) +
        (offDiagonalModularReciprocalTuples q (leftHalf ell) U).card := by
  exact (modularReciprocalEnergyTuples_card_le_diagonal_add_offDiagonal
    q (leftHalf ell) U hUpos).trans
      (Nat.add_le_add_right
        (diagonalEnergy_card_le_envelope ell U hz hUpos hUle hUrough hTPow) _)

end ReciprocalMoment

end Erdos387
