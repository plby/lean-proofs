import ErdosProblems.Erdos421.RoughCountAsymptotic
import ErdosProblems.Erdos421.FrozenBuchstabMain

/-! # Uniform rough counts with the density frozen at a fixed left endpoint -/

namespace Erdos421

theorem rough_count_frozen_asymptotic (n : ℕ) {A ε : ℝ} (hA : 0 ≤ A) (hε : 0 < ε) :
    ∃ B > 1, ∀ x : ℝ, B ≤ x → ∀ t : ℝ, x ≤ t → t ≤ 2 * x →
      ∀ z : ℕ, 2 ≤ z → (z : ℝ) ^ 2 ≤ x → t ≤ (z : ℝ) ^ (n + 3) →
      |((roughInRealInterval x t z).card : ℝ) -
        (t - x) * finiteBuchstab (n + 1) (Real.log x / Real.log z) / Real.log z| ≤
        ε * x / (Real.log x) ^ A +
          (roughCountErrorConstant (n + 1) + ((n : ℝ) + 3) ^ 2) *
            (t - x) ^ 2 / (x * (Real.log x) ^ 2) := by
  obtain ⟨B, hB, hcount⟩ := rough_count_asymptotic (n + 1) hA (by positivity : 0 < ε / 2)
  refine ⟨B, hB, ?_⟩
  intro x hx t hxt htx z hz hzsq htz
  have hx1 := hB.trans_le hx
  have hxp : 0 < x := by linarith
  have htp : 0 < t := hxp.trans_le hxt
  have hLx := Real.log_pos hx1
  have hLt := Real.log_pos (hx1.trans_le hxt)
  have hzx : (z : ℝ) ≤ x := by
    have hz2 : (2 : ℝ) ≤ z := by exact_mod_cast hz
    nlinarith
  have hz1 : (1 : ℝ) < z := by exact_mod_cast (show 1 < z by omega)
  have hzp : (0 : ℝ) < z := by linarith
  have hLz := Real.log_pos hz1
  have hlogxt := Real.log_le_log hxp hxt
  have hu : 2 ≤ Real.log x / Real.log z := by
    have h := Real.log_le_log (pow_pos hzp 2) hzsq
    rw [Real.log_pow] at h
    norm_num only [Nat.cast_ofNat] at h
    exact (le_div_iff₀ hLz).mpr h
  have hscale : Real.log x ≤ ((n : ℝ) + 3) * Real.log z := by
    have h := log_le_nat_power_scale htp htz
    norm_num only [Nat.cast_add, Nat.cast_ofNat] at h
    exact hlogxt.trans h
  have hraw := hcount t (hx.trans hxt) x (by linarith) hxt z hz (hzx.trans hxt) htz
  have hfrozen := frozen_buchstab_main_error n hx1 hxt hz hzx hu
  have hmain : (ε / 2) * t / (Real.log t) ^ A ≤ ε * x / (Real.log x) ^ A := by
    calc
      _ ≤ (ε / 2) * (2 * x) / (Real.log x) ^ A := by gcongr
      _ = _ := by ring
  have hD := roughCountErrorConstant_nonneg (n + 1)
  have hquad : roughCountErrorConstant (n + 1) * (t - x) ^ 2 /
      (t * (Real.log t) ^ 2) ≤ roughCountErrorConstant (n + 1) * (t - x) ^ 2 /
        (x * (Real.log x) ^ 2) := by gcongr
  have hK : 0 < (n : ℝ) + 3 := by positivity
  have hinv : 1 / (Real.log z) ^ (2 : ℕ) ≤
      ((n : ℝ) + 3) ^ (2 : ℕ) / (Real.log x) ^ (2 : ℕ) := by
    have h := inverse_rpow_of_lower_scale hK hLx hLz (by norm_num : (0 : ℝ) ≤ 2)
      ((div_le_iff₀ hK).mpr (by simpa only [mul_comm] using hscale))
    norm_num only [Real.rpow_ofNat] at h
    exact h
  have hfreeze : (t - x) ^ 2 / (x * (Real.log z) ^ 2) ≤
      ((n : ℝ) + 3) ^ 2 * (t - x) ^ 2 / (x * (Real.log x) ^ 2) := by
    calc
      _ = ((t - x) ^ 2 / x) * (1 / (Real.log z) ^ 2) := by ring
      _ ≤ ((t - x) ^ 2 / x) * (((n : ℝ) + 3) ^ 2 / (Real.log x) ^ 2) :=
        mul_le_mul_of_nonneg_left hinv (by positivity)
      _ = _ := by ring
  calc
    _ = |(((roughInRealInterval x t z).card : ℝ) - roughCountMain (n + 1) x t z) +
        (roughCountMain (n + 1) x t z -
          (t - x) * finiteBuchstab (n + 1) (Real.log x / Real.log z) / Real.log z)| := by
      congr 1
      ring
    _ ≤ |((roughInRealInterval x t z).card : ℝ) - roughCountMain (n + 1) x t z| +
        |roughCountMain (n + 1) x t z -
          (t - x) * finiteBuchstab (n + 1) (Real.log x / Real.log z) / Real.log z| := abs_add_le _ _
    _ ≤ (ε * x / (Real.log x) ^ A + roughCountErrorConstant (n + 1) * (t - x) ^ 2 /
        (x * (Real.log x) ^ 2)) +
        ((n : ℝ) + 3) ^ 2 * (t - x) ^ 2 / (x * (Real.log x) ^ 2) :=
      add_le_add (hraw.trans (add_le_add hmain hquad)) (hfrozen.trans hfreeze)
    _ = _ := by ring

end Erdos421
