/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Absorption of logarithmic factors in the endpoint probability estimates.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.EndpointScale

namespace Erdos521

open Filter Asymptotics
open scoped Topology

theorem eventually_nat_le_rpow_of_isLittleO {f : ℝ → ℝ} {p : ℝ}
    (h : f =o[atTop] (fun x : ℝ ↦ x ^ p)) :
    ∀ᶠ n : ℕ in atTop, f n ≤ (n : ℝ) ^ p := by
  have hb := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually h.eventuallyLE
  filter_upwards [hb] with n hn
  exact (le_abs_self (f n)).trans (by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) p)] using hn)

theorem eventually_const_mul_log_le_rpow (C : ℝ) {p : ℝ} (hp : 0 < p) :
    ∀ᶠ n : ℕ in atTop, C * Real.log n ≤ (n : ℝ) ^ p :=
  eventually_nat_le_rpow_of_isLittleO ((isLittleO_log_rpow_atTop hp).const_mul_left C)

theorem eventually_const_le_rpow (C : ℝ) {p : ℝ} (hp : 0 < p) :
    ∀ᶠ n : ℕ in atTop, C ≤ (n : ℝ) ^ p :=
  ((tendsto_rpow_atTop hp).comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_ge_atTop C

theorem eventually_const_mul_rpow_le_rpow (C : ℝ) {s t : ℝ} (hst : s < t) :
    ∀ᶠ n : ℕ in atTop, C * (n : ℝ) ^ s ≤ (n : ℝ) ^ t := by
  filter_upwards [eventually_const_le_rpow C (sub_pos.mpr hst), eventually_ge_atTop 1]
    with n h hn
  have hn₀ : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  calc
    C * (n : ℝ) ^ s ≤ (n : ℝ) ^ (t - s) * (n : ℝ) ^ s :=
      mul_le_mul_of_nonneg_right h (Real.rpow_nonneg hn₀.le s)
    _ = _ := by rw [← Real.rpow_add hn₀]; congr 1; ring

theorem eventually_const_mul_one_add_log_le_rpow {C p : ℝ} (hC : 0 ≤ C) (hp : 0 < p) :
    ∀ᶠ n : ℕ in atTop, C * (1 + Real.log (2 * n + 1)) ≤ (n : ℝ) ^ p := by
  filter_upwards [eventually_const_mul_log_le_rpow (2 * C) hp,
    eventually_const_le_rpow (2 * C * (1 + Real.log 3)) hp, eventually_ge_atTop 1]
    with n hlog hconst hn
  have hn₀ : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlog' : Real.log (2 * (n : ℝ) + 1) ≤ Real.log 3 + Real.log n := by
    rw [← Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) hn₀.ne']
    apply Real.log_le_log (by positivity)
    have hn₁ : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hmul := mul_le_mul_of_nonneg_left hlog' hC
  linarith

theorem eventually_exp_neg_rpow_le_rpow {c q : ℝ} (hc : 0 < c) (hq : 0 < q) (p : ℝ) :
    ∀ᶠ n : ℕ in atTop, Real.exp (-c * (n : ℝ) ^ q) ≤ (n : ℝ) ^ p := by
  have h := (isLittleO_exp_neg_mul_rpow_atTop hc (p / q)).eventuallyLE
  have ht := (tendsto_rpow_atTop hq).comp (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [ht.eventually h, eventually_ge_atTop 1] with n hn hn₁
  have hn₀ : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  dsimp only [Function.comp_apply] at hn
  simp only [Real.norm_of_nonneg (Real.exp_pos _).le,
    Real.norm_of_nonneg (Real.rpow_nonneg (Real.rpow_nonneg hn₀.le q) (p / q))] at hn
  rw [← Real.rpow_mul hn₀.le] at hn
  rwa [show q * (p / q) = p by field_simp] at hn

theorem eventually_rpow_le_div_log {C q : ℝ} (hC : 0 < C) (hq : q < 1) :
    ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ q ≤ (n : ℝ) / (C * Real.log n) := by
  filter_upwards [eventually_const_mul_log_le_rpow C (sub_pos.mpr hq), eventually_ge_atTop 2]
    with n hlog hn
  have hn₀ : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlog₀ : 0 < Real.log n := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  apply (le_div_iff₀ (mul_pos hC hlog₀)).mpr
  calc
    (n : ℝ) ^ q * (C * Real.log n) ≤ (n : ℝ) ^ q * (n : ℝ) ^ (1 - q) :=
      mul_le_mul_of_nonneg_left hlog (Real.rpow_nonneg hn₀.le q)
    _ = n := by
      rw [← Real.rpow_add hn₀, add_sub_cancel, Real.rpow_one]

end Erdos521
