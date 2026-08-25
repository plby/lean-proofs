import ErdosProblems.Erdos964.LinearCharacterSieve
import BoundedGaps.BombieriVinogradov.Analytic.Dyadic

/-!
# Summing the linear large sieve over conductors

The maximal linear estimate on each dyadic conductor interval yields a
logarithmic number of copies of a bound of order `N + T * sqrt N` for
supports of size at most `N`. This is used for imprimitive corrections.
-/

namespace Erdos964

open scoped BigOperators
open BoundedGaps.Maynard

private theorem linearDyadic_bound_le_common (R T n₀ N : ℕ)
    (hR : 0 < R) (hRT : R ≤ T) (hN : 0 < N) (S : Finset ℕ) :
    (1 / (R : ℝ)) * (akbaryHambrookC3 * Real.sqrt (1 + (2 * (R : ℝ)) ^ 2) *
      Real.sqrt ((N : ℝ) + (2 * (R : ℝ)) ^ 2) * Real.sqrt S.card *
        Real.log (2 * ((n₀ + N : ℕ) : ℝ))) ≤
      3 * akbaryHambrookC3 * (Real.sqrt (N : ℝ) + 2 * T) * Real.sqrt S.card *
        Real.log (2 * ((n₀ + N : ℕ) : ℝ)) := by
  have hRreal : (1 : ℝ) ≤ R := by exact_mod_cast hR
  have hRpos : (0 : ℝ) < R := by exact_mod_cast hR
  have hRTreal : (R : ℝ) ≤ T := by exact_mod_cast hRT
  have hc3 := akbaryHambrookC3_pos.le
  have hlog : 0 ≤ Real.log (2 * ((n₀ + N : ℕ) : ℝ)) := by
    apply Real.log_nonneg
    have hK : (1 : ℝ) ≤ ((n₀ + N : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ n₀ + N by omega)
    linarith
  have hroot : Real.sqrt (1 + (2 * (R : ℝ)) ^ 2) ≤ 3 * R := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · nlinarith [sq_nonneg ((R : ℝ) - 1)]
  have hfirst : (1 / (R : ℝ)) * Real.sqrt (1 + (2 * (R : ℝ)) ^ 2) ≤ 3 := by
    calc
      _ ≤ (1 / (R : ℝ)) * (3 * R) := mul_le_mul_of_nonneg_left hroot (by positivity)
      _ = 3 := by field_simp
  have hsecond : Real.sqrt ((N : ℝ) + (2 * (R : ℝ)) ^ 2) ≤ Real.sqrt (N : ℝ) + 2 * T := by
    have hlocal : Real.sqrt ((N : ℝ) + (2 * (R : ℝ)) ^ 2) ≤ Real.sqrt (N : ℝ) + 2 * R := by
      apply Real.sqrt_le_iff.mpr
      constructor
      · positivity
      · have hcross : 0 ≤ Real.sqrt (N : ℝ) * R := by positivity
        nlinarith [Real.sq_sqrt (Nat.cast_nonneg N)]
    exact hlocal.trans (by linarith)
  calc
    _ = akbaryHambrookC3 * ((1 / (R : ℝ)) * Real.sqrt (1 + (2 * (R : ℝ)) ^ 2)) *
        Real.sqrt ((N : ℝ) + (2 * (R : ℝ)) ^ 2) * Real.sqrt S.card *
          Real.log (2 * ((n₀ + N : ℕ) : ℝ)) := by ring
    _ ≤ akbaryHambrookC3 * 3 * (Real.sqrt (N : ℝ) + 2 * T) * Real.sqrt S.card *
        Real.log (2 * ((n₀ + N : ℕ) : ℝ)) := by gcongr
    _ = _ := by ring

/-- Explicit cumulative reciprocal-totient mean of the linear endpoint
maxima. This estimate is unconditional and applies to any interval subset. -/
theorem finiteCharacterCutoffMaximum_mean_le (T n₀ N : ℕ) (hT : 0 < T) (hN : 0 < N)
    (S : Finset ℕ) (hS : S ⊆ Finset.Ioc n₀ (n₀ + N)) :
    (∑ d ∈ Finset.Ioc 0 T,
      (∑ ψ : primitiveCharacters d, finiteCharacterCutoffMaximum S (n₀ + N) d ψ.1) /
        d.totient) ≤
      (S.card : ℝ) + ((Nat.log 2 T + 1 : ℕ) : ℝ) *
        (3 * akbaryHambrookC3 * (Real.sqrt (N : ℝ) + 2 * T) * Real.sqrt S.card *
          Real.log (2 * ((n₀ + N : ℕ) : ℝ))) := by
  classical
  let U (d : ℕ) :=
    (∑ ψ : primitiveCharacters d, finiteCharacterCutoffMaximum S (n₀ + N) d ψ.1) / d.totient
  let B := 3 * akbaryHambrookC3 * (Real.sqrt (N : ℝ) + 2 * T) * Real.sqrt S.card *
    Real.log (2 * ((n₀ + N : ℕ) : ℝ))
  have hU (d : ℕ) : 0 ≤ U d := div_nonneg
    (Finset.sum_nonneg (fun ψ _ => finiteCharacterCutoffMaximum_nonneg _ _ _ ψ.1))
    (Nat.cast_nonneg _)
  have hone : U 1 ≤ S.card := by
    have hcard : Fintype.card (primitiveCharacters 1) ≤ 1 := by
      simpa using card_primitiveCharacters_le_totient (by norm_num : 0 < 1)
    calc
      U 1 ≤ (Fintype.card (primitiveCharacters 1) : ℝ) * S.card := by
        simp only [U, Nat.totient_one, Nat.cast_one, div_one]
        calc
          _ ≤ ∑ ψ : primitiveCharacters 1, (S.card : ℝ) :=
            Finset.sum_le_sum (fun ψ _ => finiteCharacterCutoffMaximum_le_card _ _ _ ψ.1)
          _ = _ := by simp
      _ ≤ 1 * (S.card : ℝ) := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by positivity)
      _ = _ := one_mul _
  have hdyadic : (∑ d ∈ Finset.Ioc 1 T, U d) ≤
      ((Nat.log 2 T + 1 : ℕ) : ℝ) * B := by
    rw [sum_eq_sum_dyadicBlocks (X := T) (Finset.Ioc 1 T)
      (fun d hd => ⟨(Finset.mem_Ioc.mp hd).1, (Finset.mem_Ioc.mp hd).2⟩) U]
    calc
      _ ≤ ∑ α ∈ dyadicExponentRange T, B := by
        apply Finset.sum_le_sum
        intro α hα
        have hαbound : α ≤ Nat.log 2 T := by
          simpa only [dyadicExponentRange, Finset.mem_range, Nat.lt_succ_iff] using hα
        have hpow : 2 ^ α ≤ T :=
          (Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) hαbound).trans
            (Nat.pow_log_le_self 2 hT.ne')
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
            exact (finiteCharacterCutoffMaximum_dyadic_largeSieve (2 ^ α) n₀ N
              (by positivity) hN S hS).trans
              (linearDyadic_bound_le_common (2 ^ α) T n₀ N (by positivity) hpow hN S)
      _ = _ := by simp [dyadicExponentRange]
  change (∑ d ∈ Finset.Ioc 0 T, U d) ≤ (S.card : ℝ) + _
  rw [← Finset.sum_Ioc_consecutive U (by norm_num : 0 ≤ 1) hT,
    show Finset.Ioc 0 1 = {1} by decide, Finset.sum_singleton]
  exact add_le_add hone hdyadic

end Erdos964
