import ErdosProblems.Erdos587.HooleyApproximationCount
import ErdosProblems.Erdos587.HooleyLinearResidue
import ErdosProblems.Erdos587.HooleyGcdMean

/-!
# The large-progression rational-approximant count

The divisor encoding, uniform residue-progression mean, and exact
nonzero-error gcd sum give a seventh-log-log-power shell bound. No
additive error is introduced when the tolerance is less than one.
-/

open scoped BigOperators

namespace Erdos587

lemma delta_loglog_nat_mono {x y : ℕ} (hxy : x ≤ y) :
    max 1 (Real.log (Real.log (x : ℝ))) ≤ max 1 (Real.log (Real.log (y : ℝ))) := by
  by_cases hx : 2 ≤ x
  · apply max_le_max le_rfl
    apply Real.log_le_log (Real.log_pos (by exact_mod_cast (show 1 < x by omega)))
    exact Real.log_le_log (by exact_mod_cast (show 0 < x by omega)) (by exact_mod_cast hxy)
  · have hxsmall : x = 0 ∨ x = 1 := by omega
    rcases hxsmall with rfl | rfl <;>
      simpa only [Nat.cast_zero, Nat.cast_one, Real.log_zero, Real.log_one, max_eq_left zero_le_one]
        using (le_max_left (1 : ℝ) (Real.log (Real.log (y : ℝ))))

theorem exists_delta_approximant_shell_bound (r : ℕ) (hr : 0 < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ X q : ℕ, 0 < q → 16 ≤ X / q → X ≤ (X / q) ^ r →
      ∀ a : ℤ, IsCoprime a (q : ℤ) → ∀ B T : ℝ, 0 < B → 0 ≤ T →
      ∀ S : Finset DeltaApproximant,
      (∀ x ∈ S, 0 < x.index) → (∀ x ∈ S, B < x.denominator) →
      (∀ x ∈ S, (x.denominator : ℝ) ≤ 2 * B) →
      (∀ x ∈ S, x.index * x.denominator ≤ X) →
      (∀ x ∈ S, deltaApproximantError a q x ≠ 0) →
      (∀ x ∈ S, ((deltaApproximantError a q x).natAbs : ℝ) ≤ T) →
      (S.card : ℝ) ≤ C * ((X : ℝ) / q) * T *
        (max 1 (Real.log (Real.log (X : ℝ)))) ^ 7 := by
  classical
  obtain ⟨C₀, hC₀, hresidue⟩ := exists_delta_linear_residue_mean_bound r hr
  obtain ⟨C₁, hC₁, hgcd⟩ := exists_delta_signed_gcd_divisor_mean_bound
  refine ⟨C₀ * C₁, mul_pos hC₀ hC₁, ?_⟩
  intro X q hq hlength hsize a hcop B T hB hT S hindex hlow hupp hproduct hzero herror
  let E := S.image (deltaApproximantError a q)
  have hEzero : ∀ t ∈ E, t ≠ 0 := by
    intro t ht
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ht
    exact hzero x hx
  have hEbound : ∀ t ∈ E, (t.natAbs : ℝ) ≤ T := by
    intro t ht
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ht
    exact herror x hx
  have hcount := delta_approximant_card_le_residue_delta_sum hq hB S E hindex hlow hupp hproduct
    (fun x hx => Finset.mem_image.mpr ⟨x, hx, rfl⟩)
  have hcountR : (S.card : ℝ) ≤
      ∑ t ∈ E, ∑ n ∈ (Finset.Icc 1 X).filter (fun n : ℕ => (q : ℤ) ∣ a * n - t),
        (hooleyDelta n : ℝ) := by exact_mod_cast hcount
  have hqX : q ≤ X := by
    simpa only [one_mul] using (Nat.le_div_iff_mul_le hq).mp (by omega : 1 ≤ X / q)
  have hgcdBound : (∑ t ∈ E, ((q.gcd t.natAbs).divisors.card : ℝ)) ≤
      C₁ * T * max 1 (Real.log (Real.log (X : ℝ))) := by
    calc
      _ ≤ C₁ * T * max 1 (Real.log (Real.log (q : ℝ))) := hgcd q hq T hT E hEzero hEbound
      _ ≤ _ := mul_le_mul_of_nonneg_left (delta_loglog_nat_mono hqX) (by positivity)
  calc
    _ ≤ ∑ t ∈ E, ∑ n ∈ (Finset.Icc 1 X).filter (fun n : ℕ => (q : ℤ) ∣ a * n - t),
        (hooleyDelta n : ℝ) := hcountR
    _ ≤ ∑ t ∈ E, C₀ * (q.gcd t.natAbs).divisors.card * ((X : ℝ) / q) *
        (max 1 (Real.log (Real.log (X : ℝ)))) ^ 6 :=
      Finset.sum_le_sum (fun t _ => hresidue X q hq hlength hsize a t hcop)
    _ = (C₀ * ((X : ℝ) / q) * (max 1 (Real.log (Real.log (X : ℝ)))) ^ 6) *
        ∑ t ∈ E, ((q.gcd t.natAbs).divisors.card : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t ht
      ring
    _ ≤ (C₀ * ((X : ℝ) / q) * (max 1 (Real.log (Real.log (X : ℝ)))) ^ 6) *
        (C₁ * T * max 1 (Real.log (Real.log (X : ℝ)))) :=
      mul_le_mul_of_nonneg_left hgcdBound (by positivity)
    _ = _ := by ring

end Erdos587
