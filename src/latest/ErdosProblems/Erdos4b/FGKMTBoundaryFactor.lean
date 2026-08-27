/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTRoughWeights

/-!
# Separating the pre-sieve boundary from the harmonic correction

The correction to the ordinary harmonic sequence is the convolution of
the uniformly controlled rough correction and a squarefree factor
supported on primes dividing the pre-sieve modulus. This is an exact
identity, not an asymptotic replacement of either weight.
-/

namespace Erdos4b.FGKMT

noncomputable section

open ArithmeticFunction

theorem squarefreePrimeWeight_add_of_disjoint (a b : ℕ → ℝ)
    (hab : ∀ p : ℕ, p.Prime → a p * b p = 0) :
    squarefreePrimeWeight (fun p => a p + b p) =
      squarefreePrimeWeight a * squarefreePrimeWeight b := by
  apply (ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers _
    (squarefreePrimeWeight_isMultiplicative _) _
      ((squarefreePrimeWeight_isMultiplicative a).mul
        (squarefreePrimeWeight_isMultiplicative b))).2
  intro p j hp
  rcases j with _ | j
  · simp
  · rcases j with _ | j
    · simpa only [Nat.zero_add, pow_one] using
        (squarefreePrimeWeight_prime (fun p : ℕ => a p + b p) hp).trans
        (squarefreePrimeWeight_mul_prime a b hp).symm
    · rcases j with _ | j
      · change squarefreePrimeWeight _ (p ^ 2) =
          (squarefreePrimeWeight a * squarefreePrimeWeight b) (p ^ 2)
        rw [squarefreePrimeWeight_prime_pow_ge_two _ hp (le_refl 2),
          squarefreePrimeWeight_mul_prime_sq a b hp, hab p hp]
      · rw [squarefreePrimeWeight_prime_pow_ge_two _ hp (by omega),
          squarefreePrimeWeight_mul_prime_pow_ge_three a b hp (by omega)]

def preSieveBoundary (M : ℕ) : ArithmeticFunction ℝ :=
  squarefreePrimeWeight (fun p => if p ∣ M then -(1 / (p : ℝ)) else 0)

theorem mobiusHarmonicArithmetic_split (M : ℕ) :
    mobiusHarmonicArithmetic = preSieveBoundary M *
      squarefreePrimeWeight (fun p => if p ∣ M then 0 else -(1 / (p : ℝ))) := by
  have hsplit := squarefreePrimeWeight_add_of_disjoint
    (fun p => if p ∣ M then -(1 / (p : ℝ)) else 0)
    (fun p => if p ∣ M then 0 else -(1 / (p : ℝ)))
    (fun p _ => by by_cases hpM : p ∣ M <;> simp [hpM])
  have hsum :
      (fun p : ℕ => (if p ∣ M then -(1 / (p : ℝ)) else 0) +
        (if p ∣ M then 0 else -(1 / (p : ℝ)))) = (fun p : ℕ => -(1 / (p : ℝ))) := by
    funext p
    by_cases hpM : p ∣ M <;> simp [hpM]
  rw [hsum, squarefreePrimeWeight_neg_reciprocal] at hsplit
  exact hsplit

theorem harmonicCorrection_roughSieveWeight_eq (M : ℕ) (g : ℕ → ℝ) :
    harmonicCorrection (roughSieveWeight M g) =
      roughHarmonicCorrection M g * preSieveBoundary M := by
  rw [harmonicCorrection, mobiusHarmonicArithmetic_split M]
  unfold roughHarmonicCorrection
  ac_rfl

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.harmonicCorrection_roughSieveWeight_eq
