import ErdosProblems.Erdos587.HooleyDivisorSieve
import ErdosProblems.Erdos587.HooleyDelta

/-!
# Weighted finite covers by sifted divisor fibers

The divisor-fiber sieve can be summed against Delta weights. The covering
need not be disjoint, and its arithmetic majorant is kept explicit for
both the main smooth-part range and the Rankin-tail ranges.
-/

open scoped BigOperators

namespace Erdos587

lemma delta_natAbs_divisor_factor {v : ℤ} {d : ℕ} (hdiv : (d : ℤ) ∣ v) :
    v.natAbs = d * (v / d).natAbs := by
  have h := congrArg Int.natAbs (Int.mul_ediv_cancel_of_dvd hdiv)
  simpa only [Int.natAbs_mul, Int.natAbs_natCast] using h.symm

lemma delta_affine_cofactor_bound {v : ℤ} {d : ℕ} (hdiv : (d : ℤ) ∣ v)
    {K : ℝ} (hK : ((v / d).natAbs.divisors.card : ℝ) ≤ K) :
    (hooleyDelta v.natAbs : ℝ) ≤ K * hooleyDelta d := by
  calc
    _ = (hooleyDelta ((v / d).natAbs * d) : ℝ) := by
      rw [delta_natAbs_divisor_factor hdiv, mul_comm d]
    _ ≤ ((v / d).natAbs.divisors.card : ℝ) * hooleyDelta d := by
      exact_mod_cast hooleyDelta_mul_le (v / d).natAbs d
    _ ≤ _ := mul_le_mul_of_nonneg_right hK (by positivity)

theorem delta_weighted_divisor_sieve_le {A B : ℤ} (hB : B ≠ 0)
    (hAB : IsCoprime A B) {Q Y : ℕ} (hQ : 0 < Q) (S D : Finset ℕ)
    (hS : S ⊆ Finset.Icc 1 Y) (hD : ∀ d ∈ D, 0 < d)
    (hcut : ∀ d ∈ D, d * Q ^ 2 ≤ Y) {K : ℝ} (hK : 0 ≤ K)
    (hcover : ∀ n ∈ S, ∃ d ∈ D, (d : ℤ) ∣ A + B * n ∧
      (∀ p : ℕ, p.Prime → p ≤ Q → ¬ (p : ℤ) ∣ (A + B * n) / d) ∧
      (hooleyDelta (A + B * n).natAbs : ℝ) ≤ K * hooleyDelta d) :
    (∑ n ∈ S, (hooleyDelta (A + B * n).natAbs : ℝ)) ≤
      3 * ((B.natAbs : ℝ) / B.natAbs.totient) * Y / Real.log (Q + 1 : ℕ) *
        K * ∑ d ∈ D, (hooleyDelta d : ℝ) / d := by
  classical
  let F : ℕ → Finset ℕ := fun d => S.filter (fun n =>
    (d : ℤ) ∣ A + B * n ∧
      ∀ p : ℕ, p.Prime → p ≤ Q → ¬ (p : ℤ) ∣ (A + B * n) / d)
  have hpoint (n : ℕ) (hn : n ∈ S) :
      (hooleyDelta (A + B * n).natAbs : ℝ) ≤
        ∑ d ∈ D, if n ∈ F d then K * hooleyDelta d else 0 := by
    obtain ⟨d, hd, hdiv, hrough, hweight⟩ := hcover n hn
    have hnF : n ∈ F d := Finset.mem_filter.mpr ⟨hn, hdiv, hrough⟩
    calc
      _ ≤ K * hooleyDelta d := hweight
      _ = if n ∈ F d then K * hooleyDelta d else 0 := (if_pos hnF).symm
      _ ≤ _ := Finset.single_le_sum
        (s := D) (f := fun e => if n ∈ F e then K * hooleyDelta e else 0)
        (fun e he => by split_ifs <;> positivity) hd
  have hcard (d : ℕ) (hd : d ∈ D) : (F d).card ≤
      3 * ((B.natAbs : ℝ) / B.natAbs.totient) * (Y : ℝ) / d / Real.log (Q + 1 : ℕ) := by
    apply delta_affine_divisor_fiber_card_le_three hB hAB (hD d hd) hQ (hcut d hd) (F d)
    · exact (Finset.filter_subset _ _).trans hS
    · intro n hn
      exact (Finset.mem_filter.mp hn).2.1
    · intro n hn
      exact (Finset.mem_filter.mp hn).2.2
  calc
    _ ≤ ∑ n ∈ S, ∑ d ∈ D, if n ∈ F d then K * hooleyDelta d else 0 :=
      Finset.sum_le_sum hpoint
    _ = ∑ d ∈ D, (K * hooleyDelta d) * (F d).card := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro d hd
      rw [← Finset.sum_filter]
      have heq : S.filter (fun n => n ∈ F d) = F d := by
        ext n
        simp only [Finset.mem_filter, F, and_self_left]
      rw [heq]
      simp only [Finset.sum_const, nsmul_eq_mul, mul_comm]
    _ ≤ ∑ d ∈ D, (K * hooleyDelta d) *
        (3 * ((B.natAbs : ℝ) / B.natAbs.totient) * (Y : ℝ) / d / Real.log (Q + 1 : ℕ)) := by
      apply Finset.sum_le_sum
      intro d hd
      exact mul_le_mul_of_nonneg_left (hcard d hd) (by positivity)
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      ring

end Erdos587
