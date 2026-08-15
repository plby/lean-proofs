/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos387.ModularMomentFamily
import ErdosProblems.Erdos387.SubpowerOffDiagonalMoment

/-!
# Complete modular reciprocal moments on the subpower scale

This is the finite combinatorial core of the high-moment estimate: the
sum over all admissible moduli is bounded by a rational diagonal term and
an off-diagonal rough-divisor term, and each loss is absorbed into one copy
of the subpower base.
-/

namespace Erdos387

namespace SubpowerScale

/-- One explicit threshold sufficient for both the rational diagonal and
the modular off-diagonal reciprocal-energy estimates. -/
def reciprocalMomentThreshold (k ell : ℕ) : ℕ :=
  max (4 * ell)
    (max (max 1 (2 * ell * (2 * ell + 1)))
      (max 1 (4 * binaryMomentSlope k ell * (ell + 1))))

/-- Complete family moment bound.  The first summand is the rational
diagonal, repeated for every modulus; the second is the union of all
nonzero modular numerator collisions. -/
theorem modularEnergyFamily_card_le_medium_mul_base
    {ell N k : ℕ} (hk : 0 < k)
    (Q : Finset ℕ) (modulus : ℕ → ℕ) (U : Finset ℕ)
    (hN : reciprocalMomentThreshold k ell ≤ N)
    (hDmod : ∀ d ∈ Q, d ∣ modulus d)
    (hQrough : ∀ d ∈ Q, IsZRough (z N k) d)
    (hUpos : ∀ u ∈ U, 0 < u)
    (hUle : ∀ u ∈ U, u ≤ medium N k)
    (hUrough : ∀ u ∈ U, IsZRough (z N k) u)
    (hUcop : ∀ d ∈ Q, ∀ u ∈ U, u.Coprime (modulus d)) :
    (ReciprocalMoment.modularEnergyFamily Q modulus
        (ReciprocalMoment.leftHalf ell) U).card ≤
      (Q.card * medium N k ^ ell + U.card ^ (2 * ell)) * base N k := by
  have hfour : 4 * ell ≤ N := by
    exact (le_max_left _ _).trans hN
  have hrest :
      max (max 1 (2 * ell * (2 * ell + 1)))
          (max 1 (4 * binaryMomentSlope k ell * (ell + 1))) ≤ N := by
    exact (le_max_right _ _).trans hN
  have hdiagThreshold : max 1 (2 * ell * (2 * ell + 1)) ≤ N :=
    (le_max_left _ _).trans hrest
  have hoffThreshold :
      max 1 (4 * binaryMomentSlope k ell * (ell + 1)) ≤ N :=
    (le_max_right _ _).trans hrest
  have hdiagEnvelope :=
    ReciprocalMoment.diagonalEnergy_card_le_envelope ell U
      (two_le_z (by omega) hk) hUpos hUle hUrough
      (medium_pow_lt_z_pow_reciprocalEnergyDepth (by omega) hk)
  have hdiag :
      (reciprocalEnergyTuples (ReciprocalMoment.leftHalf ell) U).card ≤
        medium N k ^ ell * base N k := by
    exact hdiagEnvelope.trans (by
      have hmul := Nat.mul_le_mul_left (medium N k ^ ell)
        (reciprocalEnergyOverhead_le_base
          (N := N) (k := k) (ell := ell) hdiagThreshold)
      simpa [mul_assoc] using hmul)
  have hoff := offDiagonalModulusTuples_card_le_medium_mul_base hk
    Q modulus (ReciprocalMoment.leftHalf ell) U
      (max_le hfour hoffThreshold) hDmod hQrough hUcop hUle
  have hfamily :=
    ReciprocalMoment.modularEnergyFamily_card_le_diagonal_add_offDiagonal
      Q modulus (ReciprocalMoment.leftHalf ell) U hUpos
  calc
    (ReciprocalMoment.modularEnergyFamily Q modulus
        (ReciprocalMoment.leftHalf ell) U).card ≤
        Q.card *
            (reciprocalEnergyTuples (ReciprocalMoment.leftHalf ell) U).card +
          (ReciprocalMoment.offDiagonalModulusTuples Q modulus
            (ReciprocalMoment.leftHalf ell) U).card := hfamily
    _ ≤ Q.card * (medium N k ^ ell * base N k) +
          U.card ^ (2 * ell) * base N k := by
      exact Nat.add_le_add (Nat.mul_le_mul_left Q.card hdiag) hoff
    _ = (Q.card * medium N k ^ ell + U.card ^ (2 * ell)) *
          base N k := by ring

/-- Weighted `T₁` form of the complete subpower moment estimate. -/
theorem sum_halfPhase_fibre_secondMoment_le_medium_mul_base
    {ell N k : ℕ} (hk : 0 < k)
    (Q : Finset ℕ) (modulus : ℕ → ℕ) [∀ D, NeZero (modulus D)]
    (U : Finset ℕ) (weight : ℕ → (Fin ell → ℕ) → ℂ)
    (hN : reciprocalMomentThreshold k ell ≤ N)
    (hDmod : ∀ d ∈ Q, d ∣ modulus d)
    (hQrough : ∀ d ∈ Q, IsZRough (z N k) d)
    (hUpos : ∀ u ∈ U, 0 < u)
    (hUle : ∀ u ∈ U, u ≤ medium N k)
    (hUrough : ∀ u ∈ U, IsZRough (z N k) u)
    (hUcop : ∀ d ∈ Q, ∀ u ∈ U, u.Coprime (modulus d))
    (hweight : ∀ d ∈ Q, ∀ s ∈ ReciprocalMoment.halfTuples ell U,
      ‖weight d s‖ ≤ 1) :
    (∑ d ∈ Q, ∑ a : ZMod (modulus d),
        ‖AdditiveOrthogonality.residueFiberSum
          (ReciprocalMoment.halfTuples ell U)
          (ReciprocalMoment.halfPhase (modulus d)) (weight d) a‖ ^ 2) ≤
      ((Q.card * medium N k ^ ell + U.card ^ (2 * ell)) * base N k : ℕ) := by
  exact (ReciprocalMoment.sum_halfPhase_fibre_secondMoment_le_modularEnergyFamily
    ell Q modulus U weight hweight).trans (by
      exact_mod_cast modularEnergyFamily_card_le_medium_mul_base hk
        Q modulus U hN hDmod hQrough hUpos hUle hUrough hUcop)

end SubpowerScale

end Erdos387
