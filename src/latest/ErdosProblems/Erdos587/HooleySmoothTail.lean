import ErdosProblems.Erdos587.HooleyRankinBound

/-!
# Exponential harmonic tails for smooth integers

Restricting the divisor twist to small-prime-supported divisors retains
the Rankin identity on smooth integers. This gives exponential decay
above a size threshold, with the already proved harmonic Delta mean as
the untwisted factor.
-/

open scoped BigOperators

namespace Erdos587

theorem delta_smooth_rankin_harmonic_bound (S : Finset ℕ) {N z : ℕ} (hz : 2 ≤ z)
    (hS : S ⊆ Finset.Icc 1 N) (hsmooth : ∀ n ∈ S, n.primeFactors ⊆ Nat.primesLE z)
    {β M : ℝ} (hβ0 : 0 ≤ β) (hβ : β ≤ 1 / 2)
    (hM : β * Real.log (z : ℝ) ≤ M) :
    (∑ n ∈ S, ((hooleyDelta n : ℝ) / n) * (n : ℝ) ^ β) ≤
      Real.exp (20 * deltaRankinMertensConstant * M * Real.exp M) *
        ∑ m ∈ Finset.Icc 1 N, (hooleyDelta m : ℝ) / m := by
  classical
  let g : ℕ → ℝ := fun d =>
    if d.primeFactors ⊆ Nat.primesLE z then deltaRankinWeight β d else 0
  let D : Finset ℕ := (Finset.Icc 1 N).filter (fun d => d.primeFactors ⊆ Nat.primesLE z)
  have hg (d : ℕ) : 0 ≤ g d := by
    dsimp only [g]
    split_ifs
    · exact deltaRankinWeight_nonneg hβ0 d
    · exact le_rfl
  have hid (n : ℕ) (hn : n ∈ S) : (∑ d ∈ n.divisors, g d) = (n : ℝ) ^ β := by
    have hn0 : n ≠ 0 := by have := (Finset.mem_Icc.mp (hS hn)).1; omega
    rw [← sum_divisors_deltaRankinWeight hn0 β]
    apply Finset.sum_congr rfl
    intro d hd
    have hdsub := (Nat.primeFactors_mono (Nat.mem_divisors.mp hd).1 hn0).trans (hsmooth n hn)
    exact if_pos hdsub
  have hweight : (∑ d ∈ Finset.Icc 1 N, (d.divisors.card : ℝ) * g d / d) =
      ∑ d ∈ D, (d.divisors.card : ℝ) * deltaRankinWeight β d / d := by
    simp only [D, g, Finset.sum_filter, mul_ite, mul_zero, ite_div, zero_div]
  have hmass : (∑ d ∈ D, (d.divisors.card : ℝ) * deltaRankinWeight β d / d) ≤
      Real.exp (20 * deltaRankinMertensConstant * M * Real.exp M) := by
    apply sum_smooth_deltaRankinWeight_bound D hz
    · intro d hd
      have := (Finset.mem_Icc.mp (Finset.mem_filter.mp hd).1).1
      omega
    · intro d hd
      exact (Finset.mem_filter.mp hd).2
    · exact hβ0
    · exact hβ
    · exact hM
  calc
    _ = ∑ n ∈ S, ((hooleyDelta n : ℝ) / n) * ∑ d ∈ n.divisors, g d := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [hid n hn]
    _ ≤ ∑ n ∈ Finset.Icc 1 N, ((hooleyDelta n : ℝ) / n) * ∑ d ∈ n.divisors, g d := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hS
      intro n hn hnot
      exact mul_nonneg (by positivity) (Finset.sum_nonneg (fun d _ => hg d))
    _ ≤ (∑ d ∈ Finset.Icc 1 N, (d.divisors.card : ℝ) * g d / d) *
        ∑ m ∈ Finset.Icc 1 N, (hooleyDelta m : ℝ) / m :=
      delta_harmonic_divisor_twist_le N g hg
    _ = (∑ d ∈ D, (d.divisors.card : ℝ) * deltaRankinWeight β d / d) *
        ∑ m ∈ Finset.Icc 1 N, (hooleyDelta m : ℝ) / m := by rw [hweight]
    _ ≤ _ := mul_le_mul_of_nonneg_right hmass (by positivity)

theorem delta_smooth_harmonic_tail_le (S : Finset ℕ) {N z : ℕ} (hz : 2 ≤ z)
    (hS : S ⊆ Finset.Icc 1 N) (hsmooth : ∀ n ∈ S, n.primeFactors ⊆ Nat.primesLE z)
    {T β M : ℝ} (hT : 0 < T) (hlarge : ∀ n ∈ S, T ≤ n)
    (hβ0 : 0 ≤ β) (hβ : β ≤ 1 / 2) (hM : β * Real.log (z : ℝ) ≤ M) :
    (∑ n ∈ S, (hooleyDelta n : ℝ) / n) ≤
      Real.exp (20 * deltaRankinMertensConstant * M * Real.exp M - β * Real.log T) *
        ∑ m ∈ Finset.Icc 1 N, (hooleyDelta m : ℝ) / m := by
  have htwist := delta_smooth_rankin_harmonic_bound S hz hS hsmooth hβ0 hβ hM
  have hlower : T ^ β * (∑ n ∈ S, (hooleyDelta n : ℝ) / n) ≤
      ∑ n ∈ S, ((hooleyDelta n : ℝ) / n) * (n : ℝ) ^ β := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro n hn
    simpa only [mul_comm] using
      mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hT.le (hlarge n hn) hβ0)
        (show (0 : ℝ) ≤ (hooleyDelta n : ℝ) / n by positivity)
  have hpow : 0 < T ^ β := Real.rpow_pos_of_pos hT β
  have hsmall : (∑ n ∈ S, (hooleyDelta n : ℝ) / n) ≤
      (∑ n ∈ S, ((hooleyDelta n : ℝ) / n) * (n : ℝ) ^ β) / T ^ β :=
    (le_div_iff₀ hpow).mpr (by simpa only [mul_comm] using hlower)
  have hbound := hsmall.trans (div_le_div_of_nonneg_right htwist hpow.le)
  calc
    _ ≤ (Real.exp (20 * deltaRankinMertensConstant * M * Real.exp M) *
        ∑ m ∈ Finset.Icc 1 N, (hooleyDelta m : ℝ) / m) / T ^ β := hbound
    _ = _ := by
      rw [Real.rpow_def_of_pos hT, Real.exp_sub]
      rw [mul_comm (Real.log T) β]
      ring

/-- A fixed Rankin parameter gives decay exponential in `log T / log z`.
The constant is uniform in both integer cutoffs and in the subset being
summed. No squarefree restriction is imposed. -/
theorem exists_delta_smooth_harmonic_tail_bound (M : ℝ) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ N z : ℕ, 2 ≤ N → 2 ≤ z → 2 * M ≤ Real.log (z : ℝ) →
      ∀ T : ℝ, 0 < T → ∀ S : Finset ℕ, S ⊆ Finset.Icc 1 N →
      (∀ n ∈ S, n.primeFactors ⊆ Nat.primesLE z) → (∀ n ∈ S, T ≤ n) →
      (∑ n ∈ S, (hooleyDelta n : ℝ) / n) ≤
        C * Real.log (N : ℝ) * (max 1 (Real.log (Real.log (N : ℝ)))) ^ 5 *
          Real.exp (-M * Real.log T / Real.log (z : ℝ)) := by
  obtain ⟨C₀, hC₀, hmean⟩ := exists_hooleyDelta_harmonic_loglog_bound
  refine ⟨Real.exp (20 * deltaRankinMertensConstant * M * Real.exp M) * C₀,
    mul_pos (Real.exp_pos _) hC₀, ?_⟩
  intro N z hN hz hzM T hT S hS hsmooth hlarge
  have hlogz : 0 < Real.log (z : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < z by omega))
  have hβ0 : 0 ≤ M / Real.log (z : ℝ) := div_nonneg hM hlogz.le
  have hβ : M / Real.log (z : ℝ) ≤ 1 / 2 := by
    apply (div_le_iff₀ hlogz).mpr
    linarith
  have hβM : M / Real.log (z : ℝ) * Real.log (z : ℝ) ≤ M := by
    rw [div_mul_cancel₀ _ hlogz.ne']
  have htail := delta_smooth_harmonic_tail_le S hz hS hsmooth hT hlarge hβ0 hβ hβM
  calc
    _ ≤ Real.exp (20 * deltaRankinMertensConstant * M * Real.exp M -
        M / Real.log (z : ℝ) * Real.log T) *
          ∑ m ∈ Finset.Icc 1 N, (hooleyDelta m : ℝ) / m := htail
    _ ≤ Real.exp (20 * deltaRankinMertensConstant * M * Real.exp M -
        M / Real.log (z : ℝ) * Real.log T) *
          (C₀ * Real.log (N : ℝ) * (max 1 (Real.log (Real.log (N : ℝ)))) ^ 5) :=
      mul_le_mul_of_nonneg_left (hmean N hN) (Real.exp_nonneg _)
    _ = _ := by
      rw [sub_eq_add_neg, Real.exp_add]
      have heq : -(M / Real.log (z : ℝ) * Real.log T) =
          -M * Real.log T / Real.log (z : ℝ) := by ring
      rw [heq]
      ring

end Erdos587
