/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos822.MediumRangeInfrastructure
import ErdosProblems.Erdos822.AnchorCommonDivisorMass

/-! # Elementary power savings in medium rough-divisor fibers -/

namespace Erdos822

open scoped BigOperators Classical

theorem medium_progression_product_le {N d : ℕ}
    (hN : 2 ≤ N) (hdlo : N ^ 2 < d) (hdhi : d ≤ N ^ 20) :
    (d : ℝ) * ((1 : ℝ) / d + 1 / (N : ℝ) ^ 4) *
      ((1 : ℝ) / d + 1 / (N : ℝ) ^ 21) ≤ 4 / (N : ℝ) ^ 2 := by
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hpow4 : (N : ℝ) ^ 2 ≤ (N : ℝ) ^ 4 := pow_le_pow_right₀ hNR (by omega)
  have hpow21 : (N : ℝ) ^ 2 ≤ (N : ℝ) ^ 21 := pow_le_pow_right₀ hNR (by omega)
  have hd : (N : ℝ) ^ 2 ≤ d := by exact_mod_cast hdlo.le
  have hd23 : (d : ℝ) ≤ (N : ℝ) ^ 23 := by
    exact_mod_cast hdhi.trans (Nat.pow_le_pow_right (by omega : 1 ≤ N) (by omega : 20 ≤ 23))
  have h1 := one_div_le_one_div_of_le (by positivity : (0 : ℝ) < (N : ℝ) ^ 2) hd
  have h2 := one_div_le_one_div_of_le (by positivity : (0 : ℝ) < (N : ℝ) ^ 2) hpow4
  have h3 := one_div_le_one_div_of_le (by positivity : (0 : ℝ) < (N : ℝ) ^ 2) hpow21
  have h4 : (d : ℝ) / (N : ℝ) ^ 25 ≤ 1 / (N : ℝ) ^ 2 := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    calc
      _ ≤ (N : ℝ) ^ 23 * N ^ 2 := mul_le_mul_of_nonneg_right hd23 (by positivity)
      _ = _ := by ring
  calc
    _ = 1 / (d : ℝ) + 1 / (N : ℝ) ^ 4 + 1 / (N : ℝ) ^ 21 + (d : ℝ) / (N : ℝ) ^ 25 := by
      field_simp
      <;> ring
    _ ≤ 1 / (N : ℝ) ^ 2 + 1 / (N : ℝ) ^ 2 + 1 / (N : ℝ) ^ 2 + 1 / (N : ℝ) ^ 2 :=
      add_le_add (add_le_add (add_le_add h1 h2) h3) h4
    _ = _ := by ring

theorem medium_roughPairMass_mul_le {N y d : ℕ}
    (hN : 2 ≤ N) (hdlo : N ^ 2 < d) (hdhi : d ≤ N ^ 20)
    (hdrough : roughPart d y = d) :
    (N : ℝ) * d * roughQuadraticPairMassBound N y d ≤
      4 * (4 : ℝ) ^ d.primeFactors.card * (harmonic N : ℝ) ^ 2 / N := by
  have hcoef : (((2 ^ d.primeFactors.card : ℕ) : ℝ)) ^ 2 =
      (4 : ℝ) ^ d.primeFactors.card := by
    push_cast
    rw [← pow_mul, Nat.mul_comm, pow_mul]
    norm_num
  have hbase := medium_progression_product_le hN hdlo hdhi
  unfold roughQuadraticPairMassBound
  rw [hdrough, hcoef]
  push_cast
  calc
    _ = (N : ℝ) * (4 : ℝ) ^ d.primeFactors.card * (harmonic N : ℝ) ^ 2 *
        ((d : ℝ) * (1 / d + 1 / (N : ℝ) ^ 4) * (1 / d + 1 / (N : ℝ) ^ 21)) := by ring
    _ ≤ (N : ℝ) * (4 : ℝ) ^ d.primeFactors.card * (harmonic N : ℝ) ^ 2 *
        (4 / (N : ℝ) ^ 2) := mul_le_mul_of_nonneg_left hbase (by positivity)
    _ = _ := by
      have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
      field_simp

#print axioms medium_roughPairMass_mul_le

end Erdos822
