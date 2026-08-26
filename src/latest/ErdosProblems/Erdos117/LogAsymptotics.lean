import ErdosProblems.Erdos117.LogScale

/-!
# The analytic passage to the exponential growth rate

These are generic statements about positive real sequences. The entry point
applies them to the proved upper and lower bounds for the extremal function.
-/

namespace Erdos117

open Filter Asymptotics
open scoped Topology

theorem sqrt_log_cube_isLittleO_id :
    (fun n : ℕ => Real.sqrt n * (Real.log ((n : ℝ) + 2)) ^ 3) =o[atTop]
      (fun n : ℕ => (n : ℝ)) := by
  have h := log_cube_isLittleO_sqrt.mul_isBigO
    (Asymptotics.isBigO_refl (fun n : ℕ => Real.sqrt n) atTop)
  simpa only [mul_comm, Real.mul_self_sqrt (Nat.cast_nonneg _)] using h

/-- The explicit error term is sublinear. -/
theorem tendsto_sqrt_log_cube_div :
    Tendsto (fun n : ℕ =>
      (Real.sqrt n * (Real.log ((n : ℝ) + 2)) ^ 3) / n) atTop (𝓝 0) :=
  sqrt_log_cube_isLittleO_id.tendsto_div_nhds_zero

theorem eventually_one_le_sqrt_log_cube :
    ∀ᶠ n : ℕ in atTop, 1 ≤ Real.sqrt n * (Real.log ((n : ℝ) + 2)) ^ 3 := by
  have hshift : Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop :=
    tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
  have hlog : Tendsto (fun n : ℕ => Real.log ((n : ℝ) + 2)) atTop atTop :=
    Real.tendsto_log_atTop.comp hshift
  filter_upwards [hlog.eventually (eventually_ge_atTop 1), eventually_ge_atTop 1] with n hn hn1
  have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hsqrt : (1 : ℝ) ≤ Real.sqrt n := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hn1'
  exact one_le_mul_of_one_le_of_one_le hsqrt (one_le_pow₀ hn)

/-- The two logarithmic estimates force normalized logarithms to converge
to `log(2)/2`. -/
theorem tendsto_log_div_of_sandwich {a : ℕ → ℝ} {C : ℝ}
    (hlower : ∀ᶠ n : ℕ in atTop,
      (n : ℝ) * (Real.log 2 / 2) - Real.log 2 ≤ Real.log (a n))
    (hupper : ∀ᶠ n : ℕ in atTop,
      Real.log (a n) ≤ (n : ℝ) * (Real.log 2 / 2) +
        C * (Real.sqrt n * (Real.log ((n : ℝ) + 2)) ^ 3)) :
    Tendsto (fun n : ℕ => Real.log (a n) / n) atTop (𝓝 (Real.log 2 / 2)) := by
  have hlowlim : Tendsto (fun n : ℕ => Real.log 2 / 2 - Real.log 2 / n)
      atTop (𝓝 (Real.log 2 / 2)) := by
    have h := (tendsto_const_nhds (x := Real.log 2 / 2)).sub
      (tendsto_natCast_atTop_atTop.const_div_atTop (Real.log 2))
    simpa only [sub_zero] using h
  have hupperlim : Tendsto (fun n : ℕ => Real.log 2 / 2 +
      C * ((Real.sqrt n * (Real.log ((n : ℝ) + 2)) ^ 3) / n))
      atTop (𝓝 (Real.log 2 / 2)) := by
    have h := (tendsto_const_nhds (x := Real.log 2 / 2)).add
      (tendsto_sqrt_log_cube_div.const_mul C)
    simpa only [mul_zero, add_zero] using h
  apply hlowlim.squeeze' hupperlim
  · filter_upwards [hlower, eventually_ge_atTop 1] with n hn hn1
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_lt_of_lt hn1)
    apply (le_div_iff₀ hn0).mpr
    calc
      _ = (n : ℝ) * (Real.log 2 / 2) - Real.log 2 := by field_simp
      _ ≤ Real.log (a n) := hn
  · filter_upwards [hupper, eventually_ge_atTop 1] with n hn hn1
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_lt_of_lt hn1)
    apply (div_le_iff₀ hn0).mpr
    calc
      Real.log (a n) ≤ (n : ℝ) * (Real.log 2 / 2) +
          C * (Real.sqrt n * (Real.log ((n : ℝ) + 2)) ^ 3) := hn
      _ = _ := by field_simp

/-- The root limit follows from the logarithmic sandwich for any eventually
positive sequence. No group-theoretic input occurs in this lemma. -/
theorem tendsto_root_of_log_sandwich {a : ℕ → ℝ} {C : ℝ}
    (hpos : ∀ᶠ n : ℕ in atTop, 0 < a n)
    (hlower : ∀ᶠ n : ℕ in atTop,
      (n : ℝ) * (Real.log 2 / 2) - Real.log 2 ≤ Real.log (a n))
    (hupper : ∀ᶠ n : ℕ in atTop,
      Real.log (a n) ≤ (n : ℝ) * (Real.log 2 / 2) +
        C * (Real.sqrt n * (Real.log ((n : ℝ) + 2)) ^ 3)) :
    Tendsto (fun n : ℕ => (a n) ^ (1 / (n : ℝ))) atTop (𝓝 (Real.sqrt 2)) := by
  have hlog := tendsto_log_div_of_sandwich hlower hupper
  have hroot := (Real.continuous_exp.tendsto (Real.log 2 / 2)).comp hlog
  have heq : Real.exp (Real.log 2 / 2) = Real.sqrt 2 := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    congr 1
    ring
  rw [heq] at hroot
  apply hroot.congr'
  filter_upwards [hpos] with n hn
  change Real.exp (Real.log (a n) / n) = (a n) ^ (1 / (n : ℝ))
  rw [Real.rpow_def_of_pos hn]
  congr 1
  ring

end Erdos117
