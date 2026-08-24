import ErdosProblems.Erdos587.CommonFactorPowerScales
import ErdosProblems.Erdos587.WideTerminal
import ErdosProblems.Erdos587.FinalAssembly

/-! Properness, local width, and growth of the reduced ambient scale. -/

namespace Erdos587

theorem common_factor_ambient_budgets {g u v t H J T : ℕ}
    (hg : 0 < g) (hu : 0 < u) (hv : 0 < v) (huv : u.Coprime v)
    (hambient : g * (t + u * H + v * J) ≤ T)
    (hproper : ∀ x₁ ≤ H, ∀ y₁ ≤ J, ∀ x₂ ≤ H, ∀ y₂ ≤ J,
      t + u * x₁ + v * y₁ = t + u * x₂ + v * y₂ → x₁ = x₂ ∧ y₁ = y₂) :
    g * (H * J) ≤ T ∧ (g.gcd u) * u * H ≤ T := by
  have hprod : H * J ≤ u * H + v * J := by
    simpa only [huv.gcd_eq_one, one_mul] using
      NVGeneration.gcd_mul_side_product_le_span_of_injective hu hv hproper
  have hdg : g.gcd u ≤ g := Nat.gcd_le_left u hg
  constructor
  · calc
      g * (H * J) ≤ g * (u * H + v * J) := Nat.mul_le_mul_left g hprod
      _ ≤ g * (t + u * H + v * J) := Nat.mul_le_mul_left g (by omega)
      _ ≤ T := hambient
  · calc
      (g.gcd u) * u * H ≤ g * u * H := Nat.mul_le_mul_right H (Nat.mul_le_mul_right u hdg)
      _ = g * (u * H) := by ring
      _ ≤ g * (t + u * H + v * J) := Nat.mul_le_mul_left g (by omega)
      _ ≤ T := hambient

theorem common_factor_reduced_max_lower {T g V T₀ : ℝ}
    (hT : 0 < T) (hg : 0 < g) (hproper : g * V ≤ T) (hprod : T ^ (3 / 4 : ℝ) ≤ V)
    (hT₀lower : T / (4 * g ^ 2) ≤ T₀) : Real.sqrt T / 4 ≤ T₀ := by
  have hgBound : g ≤ T ^ (1 / 4 : ℝ) := by
    apply (mul_le_mul_iff_left₀ (Real.rpow_pos_of_pos hT (3 / 4 : ℝ))).mp
    calc
      g * T ^ (3 / 4 : ℝ) ≤ g * V := mul_le_mul_of_nonneg_left hprod hg.le
      _ ≤ T := hproper
      _ = T ^ (1 / 4 : ℝ) * T ^ (3 / 4 : ℝ) := by rw [← Real.rpow_add hT]; norm_num
  have hgSq : g ^ 2 ≤ Real.sqrt T := by
    have hh := pow_le_pow_left₀ hg.le hgBound 2
    rwa [quarter_power_sq hT.le] at hh
  apply le_trans _ hT₀lower
  apply (le_div_iff₀ (by positivity : 0 < 4 * g ^ 2)).mpr
  have hh := mul_le_mul_of_nonneg_left hgSq (Real.sqrt_nonneg T)
  have hrootSq := Real.sq_sqrt hT.le
  nlinarith

theorem common_factor_local_width_budget {q H J T A : ℝ} {B : ℕ}
    (hq : 0 ≤ q) (hH : 0 < H) (hJ : 0 ≤ J) (hT : 1 ≤ T) (hB : 0 < B)
    (hA : A ≤ 1 + Real.log T) (hqH : q * H ≤ T)
    (hside : T ^ (1 / 4 : ℝ) * (1 + Real.log T) ^ B ≤ J)
    (hprod : T ^ (3 / 4 : ℝ) * (1 + Real.log T) ^ B ≤ H * J) :
    A * Real.sqrt q ≤ J := by
  have hTpos : 0 < T := by linarith
  have hΛ : 1 ≤ 1 + Real.log T := by have := Real.log_nonneg hT; linarith
  have hh := primitive_width_density_budget hq hJ hH hTpos (by linarith) hqH hside
    (by simpa only [mul_comm H J] using hprod)
  have hlogpow : 1 + Real.log T ≤ (1 + Real.log T) ^ B := by
    simpa only [pow_one] using pow_le_pow_right₀ hΛ (show 1 ≤ B by omega)
  calc
    A * Real.sqrt q ≤ (1 + Real.log T) ^ B * Real.sqrt q :=
      mul_le_mul_of_nonneg_right (hA.trans hlogpow) (Real.sqrt_nonneg q)
    _ = Real.sqrt q * (1 + Real.log T) ^ B := mul_comm _ _
    _ ≤ J := hh

end Erdos587
