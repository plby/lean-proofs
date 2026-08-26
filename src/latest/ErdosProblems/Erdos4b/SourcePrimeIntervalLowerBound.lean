/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.SourcePrimeIntervalLogSaving

/-!
# Uniform prime counts in upper-half intervals of logarithmic relative length

Endpoint Chebyshev errors are compared at the common ambient logarithm.
The saving exponent is one larger than the prescribed interval-length
exponent, and its remaining constant is absorbed by a large logarithm.
-/

namespace Erdos4b

noncomputable section

open Filter
open scoped Topology

theorem logSaving_term_le_ambient (L : ℕ) {C x X t V : ℝ}
    (hC : 0 ≤ C) (hx : 0 ≤ x) (hxX : x ≤ X) (hV : 0 < V) (ht : V / 2 ≤ t) :
    C * x / t ^ L ≤ C * 2 ^ L * X / V ^ L := by
  calc
    _ ≤ C * X / (V / 2) ^ L := div_le_div₀ (mul_nonneg hC (hx.trans hxX))
      (mul_le_mul_of_nonneg_left hxX hC) (pow_pos (by positivity) L)
      (pow_le_pow_left₀ (by positivity) ht L)
    _ = _ := by rw [div_pow]; field_simp

theorem primeInterval_card_lower_of_logSaving
    (J : ℕ) {C δ : ℝ} {A B X X₀ : ℕ}
    (hC : 0 ≤ C) (hA : 0 < A) (hAB : A ≤ B) (hBX : B ≤ X)
    (hlogX : 0 < Real.log X)
    (htheta : ∀ x : ℕ, X₀ ≤ x →
      |Chebyshev.theta (x : ℝ) - (x : ℝ)| ≤ C * (x : ℝ) / Real.log x ^ (J + 1))
    (hXA : X₀ ≤ A - 1) (hXB : X₀ ≤ B - 1)
    (hlogA : Real.log X / 2 ≤ Real.log (A - 1 : ℕ))
    (hlogB : Real.log X / 2 ≤ Real.log (B - 1 : ℕ))
    (hsmall : 4 * C * 2 ^ (J + 1) ≤ δ * Real.log X)
    (hlength : δ * (X : ℝ) / Real.log X ^ J ≤ (B : ℝ) - A) :
    δ * (X : ℝ) / (2 * Real.log X ^ (J + 1)) ≤ (auxiliaryPrimeInterval A B).card := by
  let E : ℝ := C * 2 ^ (J + 1) * (X : ℝ) / Real.log X ^ (J + 1)
  have hEA : |Chebyshev.theta (A - 1 : ℕ) - (A - 1 : ℕ)| ≤ E := by
    apply (htheta _ hXA).trans
    exact logSaving_term_le_ambient (J + 1) hC (Nat.cast_nonneg _)
      (by exact_mod_cast (Nat.sub_le A 1).trans (hAB.trans hBX)) hlogX hlogA
  have hEB : |Chebyshev.theta (B - 1 : ℕ) - (B - 1 : ℕ)| ≤ E := by
    apply (htheta _ hXB).trans
    exact logSaving_term_le_ambient (J + 1) hC (Nat.cast_nonneg _)
      (by exact_mod_cast (Nat.sub_le B 1).trans hBX) hlogX hlogB
  have hE : 2 * E ≤ δ * (X : ℝ) / (2 * Real.log X ^ J) := by
    calc
      _ = (4 * C * 2 ^ (J + 1)) * (X : ℝ) / (2 * Real.log X ^ (J + 1)) := by dsimp [E]; ring
      _ ≤ (δ * Real.log X) * (X : ℝ) / (2 * Real.log X ^ (J + 1)) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hsmall (Nat.cast_nonneg _))
          (by positivity)
      _ = _ := by rw [pow_succ]; field_simp
  have hcount := interval_length_sub_theta_errors_le_log_mul_primeCount hA hAB
  have hlogBX : Real.log B ≤ Real.log X :=
    Real.log_le_log (by exact_mod_cast hA.trans_le hAB) (by exact_mod_cast hBX)
  have hcountX := hcount.trans
    (mul_le_mul_of_nonneg_right hlogBX (Nat.cast_nonneg _))
  have hhalf : δ * (X : ℝ) / Real.log X ^ J = 2 * (δ * (X : ℝ) / (2 * Real.log X ^ J)) := by
    ring
  have hmass : δ * (X : ℝ) / (2 * Real.log X ^ J) ≤
      Real.log X * (auxiliaryPrimeInterval A B).card := by linarith
  calc
    _ = (δ * (X : ℝ) / (2 * Real.log X ^ J)) / Real.log X := by
      rw [pow_succ]
      ring
    _ ≤ (Real.log X * (auxiliaryPrimeInterval A B).card) / Real.log X :=
      div_le_div_of_nonneg_right hmass hlogX.le
    _ = _ := mul_div_cancel_left₀ _ hlogX.ne'

theorem half_log_le_log_of_four_mul_ge {X x : ℕ} (hX : 0 < X)
    (hfour : X ≤ 4 * x) (hlog : 2 * Real.log 4 ≤ Real.log X) :
    Real.log X / 2 ≤ Real.log x := by
  have hx : 0 < x := by omega
  have hxR : (0 : ℝ) < x := by exact_mod_cast hx
  have hXlog : Real.log X ≤ Real.log (4 * (x : ℝ)) :=
    Real.log_le_log (by exact_mod_cast hX) (by exact_mod_cast hfour)
  rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) hxR.ne'] at hXlog
  linarith

theorem eventually_primeInterval_card_lower (J : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ X : ℕ in atTop, ∀ A B : ℕ, X ≤ 2 * A → A ≤ B → B ≤ X →
      δ * (X : ℝ) / Real.log X ^ J ≤ (B : ℝ) - A →
      δ * (X : ℝ) / (2 * Real.log X ^ (J + 1)) ≤ (auxiliaryPrimeInterval A B).card := by
  obtain ⟨C, hC, X₀, hX₀, htheta⟩ := exists_chebyshevTheta_nat_logSaving (J + 1)
  have hlogTop : Tendsto (fun X : ℕ ↦ Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop (max 8 (4 * X₀)), hlogTop.eventually_ge_atTop 1,
    hlogTop.eventually_ge_atTop (2 * Real.log 4),
    hlogTop.eventually_ge_atTop (4 * C * 2 ^ (J + 1) / δ)] with X hX hlog hlog4 hsave
  intro A B hhalf hAB hBX hlength
  have hA : 0 < A := by omega
  have hXA : X₀ ≤ A - 1 := by omega
  have hXB : X₀ ≤ B - 1 := by omega
  have hfourA : X ≤ 4 * (A - 1) := by omega
  have hfourB : X ≤ 4 * (B - 1) := by omega
  apply primeInterval_card_lower_of_logSaving J hC hA hAB hBX (by linarith) htheta hXA hXB
    (half_log_le_log_of_four_mul_ge (by omega) hfourA hlog4)
    (half_log_le_log_of_four_mul_ge (by omega) hfourB hlog4) _ hlength
  simpa only [mul_comm] using (div_le_iff₀ hδ).mp hsave

end

end Erdos4b
