import ErdosProblems.Erdos67b.MRPrimeSelbergWeights
import Mathlib.Analysis.Complex.Basic

/-!
# The positive Selberg square and its exact finite expansion

Primes above the coefficient cutoff have weight exactly one. Expansion
retains every least-common-multiple divisibility condition and bounds
the total absolute coefficient mass by `D^2`.
-/

open scoped BigOperators

namespace Erdos67b

noncomputable section

def mrPrimeSelbergLinear (D : ℕ) (hD : 1 ≤ D) (n : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 D, if d ∣ n then mrPrimeSelbergCoefficient D hD d else 0

def mrPrimeSelbergMajorant (D : ℕ) (hD : 1 ≤ D) (n : ℕ) : ℝ :=
  mrPrimeSelbergLinear D hD n ^ 2

theorem mrPrimeSelbergMajorant_nonneg (D : ℕ) (hD : 1 ≤ D) (n : ℕ) :
    0 ≤ mrPrimeSelbergMajorant D hD n := sq_nonneg _

theorem mrPrimeSelbergLinear_prime (D : ℕ) (hD : 1 ≤ D)
    {p : ℕ} (hp : p.Prime) (hDp : D < p) :
    mrPrimeSelbergLinear D hD p = 1 := by
  unfold mrPrimeSelbergLinear
  rw [Finset.sum_eq_single 1]
  · simp [mrPrimeSelbergCoefficient_one]
  · intro d hd hdne
    apply if_neg
    intro hdvd
    rcases (Nat.dvd_prime hp).mp hdvd with hdOne | hdP
    · exact hdne hdOne
    · have hdD := (Finset.mem_Icc.mp hd).2
      omega
  · intro hnot
    exact (hnot (Finset.mem_Icc.mpr ⟨le_rfl, hD⟩)).elim

theorem mrPrimeSelbergMajorant_prime (D : ℕ) (hD : 1 ≤ D)
    {p : ℕ} (hp : p.Prime) (hDp : D < p) :
    mrPrimeSelbergMajorant D hD p = 1 := by
  rw [mrPrimeSelbergMajorant, mrPrimeSelbergLinear_prime D hD hp hDp, one_pow]

theorem mrPrimeIndicator_le_selbergMajorant (D : ℕ) (hD : 1 ≤ D) (n : ℕ) :
    (if n.Prime ∧ D < n then (1 : ℝ) else 0) ≤ mrPrimeSelbergMajorant D hD n := by
  split_ifs with hn
  · exact (mrPrimeSelbergMajorant_prime D hD hn.1 hn.2).ge
  · exact mrPrimeSelbergMajorant_nonneg D hD n

theorem mrPrimeSelbergMajorant_eq_lcm_sum (D : ℕ) (hD : 1 ≤ D) (n : ℕ) :
    mrPrimeSelbergMajorant D hD n =
      ∑ d ∈ Finset.Icc 1 D, ∑ e ∈ Finset.Icc 1 D,
        if Nat.lcm d e ∣ n then
          mrPrimeSelbergCoefficient D hD d * mrPrimeSelbergCoefficient D hD e else 0 := by
  unfold mrPrimeSelbergMajorant mrPrimeSelbergLinear
  rw [pow_two, Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d _hd
  apply Finset.sum_congr rfl
  intro e _he
  by_cases hd : d ∣ n <;> by_cases he : e ∣ n <;> simp [Nat.lcm_dvd_iff, hd, he]

theorem mrPrimeSelberg_coefficient_abs_sum_le (D : ℕ) (hD : 1 ≤ D) :
    (∑ d ∈ Finset.Icc 1 D, ∑ e ∈ Finset.Icc 1 D,
      |mrPrimeSelbergCoefficient D hD d * mrPrimeSelbergCoefficient D hD e|) ≤ (D : ℝ) ^ 2 := by
  calc
    _ ≤ ∑ d ∈ Finset.Icc 1 D, ∑ e ∈ Finset.Icc 1 D, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro d _hd
      apply Finset.sum_le_sum
      intro e _he
      rw [abs_mul]
      exact mul_le_one₀ (mrAbs_primeSelbergCoefficient_le_one D hD d) (abs_nonneg _)
        (mrAbs_primeSelbergCoefficient_le_one D hD e)
    _ = _ := by simp [pow_two]

theorem mrPrimeSelberg_weighted_sum_eq (D : ℕ) (hD : 1 ≤ D)
    (S : Finset ℕ) (a : ℕ → ℂ) :
    (∑ n ∈ S, (mrPrimeSelbergMajorant D hD n : ℂ) * a n) =
      ∑ d ∈ Finset.Icc 1 D, ∑ e ∈ Finset.Icc 1 D,
        ((mrPrimeSelbergCoefficient D hD d * mrPrimeSelbergCoefficient D hD e : ℝ) : ℂ) *
          ∑ n ∈ S with Nat.lcm d e ∣ n, a n := by
  classical
  simp_rw [mrPrimeSelbergMajorant_eq_lcm_sum, Complex.ofReal_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _hd
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _he
  rw [Finset.sum_filter, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _hn
  by_cases hn : Nat.lcm d e ∣ n <;> simp [hn]

end

end Erdos67b
