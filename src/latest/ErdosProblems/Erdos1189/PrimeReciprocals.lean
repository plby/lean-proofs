/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
A logarithmic lower bound for the prime sum of log(p)/p.
Informal argument: the proved prime number theorem and finite Abel summation.
Formal author: OpenAI Codex.
-/

import ErdosProblems.Erdos1189.PrimeEstimates
import ErdosProblems.Erdos1189.ReciprocalAbel

namespace Erdos1189

open Finset Filter Asymptotics

lemma eventually_theta_lower :
    ∀ᶠ n : ℕ in atTop, (1 / 2 : ℝ) * n ≤ Chebyshev.theta n := by
  have ht : Tendsto (fun n : ℕ => Chebyshev.theta n / n) atTop (nhds 1) :=
    (isEquivalent_iff_tendsto_one (by
      filter_upwards [eventually_ge_atTop 1] with n hn
      exact_mod_cast (show n ≠ 0 by omega))).mp
        BoundedGaps.PrimeNumberTheorem.chebyshevTheta_natCast_isEquivalent
  filter_upwards [(tendsto_order.mp ht).1 (1 / 2) (by norm_num),
    eventually_ge_atTop 1] with n hn hn1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  exact ((lt_div_iff₀ hn0).mp hn).le

lemma exists_theta_linear_lower :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, (1 / 2 : ℝ) * n - C ≤ Chebyshev.theta n := by
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp eventually_theta_lower
  refine ⟨(n₀ : ℝ) / 2, by positivity, ?_⟩
  intro n
  by_cases hn : n₀ ≤ n
  · exact (sub_le_self _ (by positivity)).trans (hn₀ n hn)
  · have hnn₀ : (n : ℝ) ≤ n₀ := by exact_mod_cast (show n ≤ n₀ by omega)
    have := Chebyshev.theta_nonneg (n : ℝ)
    linarith

lemma initialSum_prime_log (N : ℕ) :
    initialSum (fun n => if n.Prime then Real.log n else 0) N =
      Chebyshev.theta N := by
  simp [initialSum_eq_sum_Ioc, Chebyshev.theta, sum_filter]

lemma primeLog_reciprocal_sum (N : ℕ) :
    (∑ i ∈ range N, (if (i + 1).Prime then Real.log ((i + 1 : ℕ) : ℝ) else 0) /
      (i + 1 : ℝ)) = ∑ p ∈ Nat.primesLE N, Real.log p / p := by
  rw [reciprocal_sum_eq_sum_Ioc (fun n => if n.Prime then Real.log n else 0)]
  have hset : (Ioc 0 N).filter Nat.Prime = Nat.primesLE N := by
    ext p
    simp only [mem_filter, mem_Ioc, Nat.mem_primesLE]
    exact ⟨fun h => ⟨h.1.2, h.2⟩, fun h => ⟨⟨h.2.pos, h.1⟩, h.2⟩⟩
  rw [← hset, sum_filter]
  simp only [ite_div, zero_div]

theorem eventually_primeLog_reciprocal_lower :
    ∀ᶠ P : ℕ in atTop,
      (1 / 4 : ℝ) * Real.log P ≤
        ∑ p ∈ Nat.primesLE (P - 1), Real.log p / p := by
  obtain ⟨C, _, htheta⟩ := exists_theta_linear_lower
  have htlog : Tendsto (fun P : ℕ => Real.log P) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [htlog.eventually (eventually_ge_atTop (4 * C)),
    eventually_ge_atTop 1] with P hlog hP
  have hbound := reciprocal_lower_of_prefix_deficit
    (f := fun n => if n.Prime then Real.log n else 0) (c := 1 / 2) (C := C)
    (N := P - 1) (fun n _ => by simpa only [initialSum_prime_log] using htheta n)
  rw [primeLog_reciprocal_sum] at hbound
  have hH := log_add_one_le_harmonic (P - 1)
  rw [Nat.sub_add_cancel hP] at hH
  linarith

end Erdos1189
