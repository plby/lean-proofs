import ErdosProblems.Erdos1141.ExceptionalPrimes
import ErdosProblems.Erdos1141.SparseAsymptotics

/-!
# The counting half of Pollack's residue-prime argument

Fewer than a prescribed power of `log m` residue primes forces a power
saving in the sum of the quadratic divisor coefficients through the exact
cutoff.  This theorem is uniform over all quadratic characters, including
imprimitive characters and the principal character.
-/

namespace Pollack17

open Filter
open scoped BigOperators

theorem eventually_few_residue_primes_divisor_sum
    (ε A : ℝ) (hε : 0 < ε) (hA : 0 < A) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ᶠ m : ℕ in atTop,
      ∀ χ : DirichletCharacter ℂ m, MulChar.IsQuadratic χ →
        ((residuePrimesUpTo m χ ε).card : ℝ) ≤ (Real.log (m : ℝ)) ^ A →
        ∀ X : ℕ, (X : ℝ) ≤ residuePrimeUpperBound m ε →
          (∑ n ∈ Finset.Icc 1 X, divisorCoefficient χ n) ≤
            (m : ℝ) ^ ((1 / 4 : ℝ) + ε - ρ) := by
  have hc : 0 < (1 / 4 : ℝ) + ε := by linarith
  have hB : 0 < A + 2 := by linarith
  obtain ⟨ρ, hρ, hsum⟩ := eventually_sparse_divisor_sum hc hB
  have hlogtop : Tendsto (fun m : ℕ => Real.log (m : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hram := hlogtop.eventually
    (eventually_const_mul_rpow_le (C := (Real.log 2)⁻¹) (d := 1 / 2)
      (a := 1) (b := A + 2) (by norm_num) (by linarith))
  have hres := hlogtop.eventually
    (eventually_const_mul_rpow_le (C := 1) (d := 1 / 2)
      (a := A) (b := A + 2) (by norm_num) (by linarith))
  refine ⟨ρ, hρ, ?_⟩
  filter_upwards [hsum, hram, hres, eventually_ge_atTop 1] with m hmSum hmRam hmRes hm1
  intro χ hχ hcount X hX
  apply hmSum χ hχ X hX
  have hmpos : 0 < m := hm1
  have hcard : ((exceptionalPrimes χ X).card : ℝ) ≤
      (m.primeFactors.card : ℝ) + ((residuePrimesUpTo m χ ε).card : ℝ) := by
    exact_mod_cast exceptionalPrimes_card_le hmpos.ne' χ hχ hX
  have hram' : Real.log (m : ℝ) / Real.log 2 ≤
      (1 / 2 : ℝ) * (Real.log (m : ℝ)) ^ (A + 2) := by
    simpa only [Real.rpow_one, div_eq_mul_inv, mul_comm] using hmRam
  have hres' : (Real.log (m : ℝ)) ^ A ≤
      (1 / 2 : ℝ) * (Real.log (m : ℝ)) ^ (A + 2) := by
    simpa only [one_mul] using hmRes
  linarith [primeFactors_card_le_log hmpos]

end Pollack17
