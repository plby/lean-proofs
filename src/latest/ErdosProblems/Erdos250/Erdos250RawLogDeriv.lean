import ErdosProblems.Erdos250.Erdos250RatFrac
import ErdosProblems.Erdos250.Erdos250Arithmetic

open scoped BigOperators

namespace DoublePartialFraction.OldRational

lemma oddFactorQ_eq_arithmetic_cast (d : ℕ) (hd : 1 ≤ d) :
    oddFactorQ d = (Erdos250Arithmetic.oddFactor d : ℕ) := by
  rw [oddFactorQ, Erdos250Arithmetic.oddFactor, Nat.cast_sub]
  · norm_num
  · exact one_le_pow₀ (by omega)

theorem rawLogDeriv_eq_arithmetic_logDerivCoeff
    (n k : ℕ) (hk : k ≤ n) :
    rawLogDeriv n k = Erdos250Arithmetic.logDerivCoeff n k := by
  rw [rawLogDeriv_eq_targetLogDeriv n k hk]
  have hhigh :
      (∑ d ∈ Finset.Icc (k + 1) (n + k),
          (2 : ℚ) ^ d / oddFactorQ d) =
        ∑ d ∈ Finset.Icc (k + 1) (n + k),
          ((2 ^ d : ℕ) : ℚ) / (Erdos250Arithmetic.oddFactor d : ℕ) := by
    apply Finset.sum_congr rfl
    intro d hd
    rw [oddFactorQ_eq_arithmetic_cast d (by
      have hd' := (Finset.mem_Icc.mp hd).1
      omega)]
    norm_num
  have hlowHigh :
      (∑ d ∈ Finset.Icc 1 k, (2 : ℚ) ^ d / oddFactorQ d) =
        ∑ d ∈ Finset.Icc 1 k,
          ((2 ^ d : ℕ) : ℚ) / (Erdos250Arithmetic.oddFactor d : ℕ) := by
    apply Finset.sum_congr rfl
    intro d hd
    rw [oddFactorQ_eq_arithmetic_cast d (Finset.mem_Icc.mp hd).1]
    norm_num
  have hlow :
      (∑ d ∈ Finset.Icc 1 (n - k), (1 : ℚ) / oddFactorQ d) =
        ∑ d ∈ Finset.Icc 1 (n - k),
          (1 : ℚ) / (Erdos250Arithmetic.oddFactor d : ℕ) := by
    apply Finset.sum_congr rfl
    intro d hd
    rw [oddFactorQ_eq_arithmetic_cast d (Finset.mem_Icc.mp hd).1]
  rw [targetLogDeriv, Erdos250Arithmetic.logDerivCoeff, hhigh, hlowHigh, hlow]

end DoublePartialFraction.OldRational
