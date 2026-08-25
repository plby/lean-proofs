import ErdosProblems.Erdos964.SemiprimeLargeSieve
import BoundedGaps.BombieriVinogradov.Analytic.Dyadic

/-!
# The large-conductor part of a semiprime block

Summing the bilinear large sieve over dyadic conductor intervals gives an
explicit bound retaining the reciprocal lower-conductor cutoff. Both prime
factors remain variables in this estimate.
-/

namespace Erdos964

open scoped BigOperators
open BoundedGaps.Maynard

private theorem sqrt_add_four_square_le (x r : ℝ) (hx : 0 ≤ x) (hr : 0 ≤ r) :
    Real.sqrt (x + (2 * r) ^ 2) ≤ Real.sqrt x + 2 * r := by
  apply Real.sqrt_le_iff.mpr
  constructor
  · positivity
  · have hcross : 0 ≤ Real.sqrt x * r := by positivity
    nlinarith [Real.sq_sqrt hx]

private theorem bilinearDyadic_bound_le_common (R D T m₀ M n₀ N : ℕ)
    (hR : 0 < R) (hD : 0 < D) (hDR : D ≤ 2 * R) (hRT : R ≤ T)
    (hM : 0 < M) (hN : 0 < N) (P Q : Finset ℕ) :
    (1 / (R : ℝ)) * (akbaryHambrookC3 * Real.sqrt ((M : ℝ) + (2 * (R : ℝ)) ^ 2) *
      Real.sqrt ((N : ℝ) + (2 * (R : ℝ)) ^ 2) * Real.sqrt P.card * Real.sqrt Q.card *
        Real.log (2 * (((m₀ + M) * (n₀ + N) : ℕ) : ℝ))) ≤
      akbaryHambrookC3 *
        ((2 / (D : ℝ)) * Real.sqrt (M : ℝ) * Real.sqrt (N : ℝ) +
          2 * Real.sqrt (M : ℝ) + 2 * Real.sqrt (N : ℝ) + 4 * T) *
        Real.sqrt P.card * Real.sqrt Q.card *
          Real.log (2 * (((m₀ + M) * (n₀ + N) : ℕ) : ℝ)) := by
  have hRpos : (0 : ℝ) < R := by exact_mod_cast hR
  have hDpos : (0 : ℝ) < D := by exact_mod_cast hD
  have hDRreal : (D : ℝ) ≤ 2 * R := by exact_mod_cast hDR
  have hRTreal : (R : ℝ) ≤ T := by exact_mod_cast hRT
  have hc3 := akbaryHambrookC3_pos.le
  have hlog : 0 ≤ Real.log (2 * (((m₀ + M) * (n₀ + N) : ℕ) : ℝ)) := by
    apply Real.log_nonneg
    have hK : (1 : ℝ) ≤ (((m₀ + M) * (n₀ + N) : ℕ) : ℝ) := by
      exact_mod_cast (Nat.mul_pos (by omega : 0 < m₀ + M) (by omega : 0 < n₀ + N))
    linarith
  have hinv : 1 / (R : ℝ) ≤ 2 / D := by
    apply (div_le_div_iff₀ hRpos hDpos).mpr
    simpa only [one_mul] using hDRreal
  have hcore : (1 / (R : ℝ)) *
      (Real.sqrt (M : ℝ) + 2 * R) * (Real.sqrt (N : ℝ) + 2 * R) ≤
      (2 / (D : ℝ)) * Real.sqrt (M : ℝ) * Real.sqrt (N : ℝ) +
        2 * Real.sqrt (M : ℝ) + 2 * Real.sqrt (N : ℝ) + 4 * T := by
    calc
      _ = (1 / (R : ℝ)) * Real.sqrt (M : ℝ) * Real.sqrt (N : ℝ) +
          2 * Real.sqrt (M : ℝ) + 2 * Real.sqrt (N : ℝ) + 4 * R := by
        field_simp
        ring
      _ ≤ _ := by gcongr
  calc
    _ ≤ (1 / (R : ℝ)) * (akbaryHambrookC3 * (Real.sqrt (M : ℝ) + 2 * R) *
        (Real.sqrt (N : ℝ) + 2 * R) * Real.sqrt P.card * Real.sqrt Q.card *
          Real.log (2 * (((m₀ + M) * (n₀ + N) : ℕ) : ℝ))) := by
      gcongr
      · exact sqrt_add_four_square_le (M : ℝ) R (Nat.cast_nonneg M) hRpos.le
      · exact sqrt_add_four_square_le (N : ℝ) R (Nat.cast_nonneg N) hRpos.le
    _ = akbaryHambrookC3 *
        ((1 / (R : ℝ)) * (Real.sqrt (M : ℝ) + 2 * R) * (Real.sqrt (N : ℝ) + 2 * R)) *
        Real.sqrt P.card * Real.sqrt Q.card *
          Real.log (2 * (((m₀ + M) * (n₀ + N) : ℕ) : ℝ)) := by ring
    _ ≤ _ := by gcongr

/-- Cumulative semiprime character mean above a positive conductor cutoff.
The logarithmic count of dyadic intervals is explicit. -/
theorem semiprimeBlock_largeConductor_mean_le
    (D T m₀ M n₀ N : ℕ) (hD : 0 < D) (hT : 0 < T) (hM : 0 < M) (hN : 0 < N)
    (P Q : Finset ℕ)
    (hPinterval : P ⊆ Finset.Ioc m₀ (m₀ + M))
    (hQinterval : Q ⊆ Finset.Ioc n₀ (n₀ + N))
    (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime)
    (hsep : ∀ p ∈ P, ∀ q ∈ Q, p < q) :
    (∑ d ∈ Finset.Ioc D T,
      (∑ ψ : primitiveCharacters d,
        primeProductBlockMaximum P Q ((m₀ + M) * (n₀ + N)) d ψ.1) / d.totient) ≤
      ((Nat.log 2 T + 1 : ℕ) : ℝ) * (akbaryHambrookC3 *
        ((2 / (D : ℝ)) * Real.sqrt (M : ℝ) * Real.sqrt (N : ℝ) +
          2 * Real.sqrt (M : ℝ) + 2 * Real.sqrt (N : ℝ) + 4 * T) *
        Real.sqrt P.card * Real.sqrt Q.card *
          Real.log (2 * (((m₀ + M) * (n₀ + N) : ℕ) : ℝ))) := by
  classical
  let U (d : ℕ) :=
    (∑ ψ : primitiveCharacters d,
      primeProductBlockMaximum P Q ((m₀ + M) * (n₀ + N)) d ψ.1) / d.totient
  let B := akbaryHambrookC3 *
    ((2 / (D : ℝ)) * Real.sqrt (M : ℝ) * Real.sqrt (N : ℝ) +
      2 * Real.sqrt (M : ℝ) + 2 * Real.sqrt (N : ℝ) + 4 * T) *
    Real.sqrt P.card * Real.sqrt Q.card *
      Real.log (2 * (((m₀ + M) * (n₀ + N) : ℕ) : ℝ))
  have hU (d : ℕ) : 0 ≤ U d := div_nonneg
    (Finset.sum_nonneg (fun ψ _ => primeProductBlockMaximum_nonneg _ _ _ _ ψ.1))
    (Nat.cast_nonneg _)
  have hlog : 0 ≤ Real.log (2 * (((m₀ + M) * (n₀ + N) : ℕ) : ℝ)) := by
    apply Real.log_nonneg
    have hK : (1 : ℝ) ≤ (((m₀ + M) * (n₀ + N) : ℕ) : ℝ) := by
      exact_mod_cast (Nat.mul_pos (by omega : 0 < m₀ + M) (by omega : 0 < n₀ + N))
    linarith
  have hB : 0 ≤ B := by
    dsimp only [B]
    have hc3 := akbaryHambrookC3_pos.le
    positivity
  change (∑ d ∈ Finset.Ioc D T, U d) ≤ ((Nat.log 2 T + 1 : ℕ) : ℝ) * B
  rw [sum_eq_sum_dyadicBlocks (X := T) (Finset.Ioc D T)
    (fun d hd => ⟨by have := (Finset.mem_Ioc.mp hd).1; omega, (Finset.mem_Ioc.mp hd).2⟩) U]
  calc
    _ ≤ ∑ α ∈ dyadicExponentRange T, B := by
      apply Finset.sum_le_sum
      intro α hα
      have hαbound : α ≤ Nat.log 2 T := by
        simpa only [dyadicExponentRange, Finset.mem_range, Nat.lt_succ_iff] using hα
      have hpow : 2 ^ α ≤ T :=
        (Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) hαbound).trans
          (Nat.pow_log_le_self 2 hT.ne')
      rcases ((Finset.Ioc D T).filter (fun d => d ∈ dyadicBlock α)).eq_empty_or_nonempty with
        hempty | ⟨d, hd⟩
      · rw [hempty, Finset.sum_empty]
        exact hB
      · have hdD := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hd).1).1
        have hdR := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hd).2).2
        have hDR : D ≤ 2 * 2 ^ α := by
          rw [pow_succ] at hdR
          omega
        calc
          _ ≤ ∑ d ∈ dyadicBlock α, U d := by
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · intro d hd
              exact (Finset.mem_filter.mp hd).2
            · intro d _ _
              exact hU d
          _ ≤ B := by
            change (∑ d ∈ Finset.Ioc (2 ^ α) (2 ^ (α + 1)), U d) ≤ B
            rw [pow_succ, Nat.mul_comm (2 ^ α) 2]
            exact (semiprimeBlock_dyadic_maximal_largeSieve (2 ^ α) m₀ M n₀ N
              (by positivity) hM hN P Q hPinterval hQinterval hP hQ hsep).trans
              (bilinearDyadic_bound_le_common (2 ^ α) D T m₀ M n₀ N
                (by positivity) hD hDR hpow hM hN P Q)
    _ = _ := by simp [dyadicExponentRange]

end Erdos964
