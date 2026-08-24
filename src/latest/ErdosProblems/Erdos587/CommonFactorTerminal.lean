import ErdosProblems.Erdos587.CommonFactorGeometry
import ErdosProblems.Erdos587.CommonFactorParameters
import ErdosProblems.Erdos587.CommonFactorLogScales
import ErdosProblems.Erdos587.NonprimitiveLongSide
import ErdosProblems.Erdos587.PrimitiveTerminal

/-! The full terminal theorem for homogeneous proper rank-two progressions. -/

open Filter

namespace Erdos587

theorem exists_ordered_common_factor_terminal (C : ℝ) (hC : 0 < C) :
    ∃ B : ℕ, 0 < B ∧ ∃ Tmin : ℝ, ∀ (g t u v H J T : ℕ), Tmin ≤ (T : ℝ) →
      0 < g → 0 < u → 0 < v → 0 < H → 0 < J → u.Coprime v → J ≤ H →
      T = g * (t + u * H + v * J) →
      (T : ℝ) ≤ C * g * ((u : ℝ) * H + v * J) →
      (∀ x₁ ≤ H, ∀ y₁ ≤ J, ∀ x₂ ≤ H, ∀ y₂ ≤ J,
        t + u * x₁ + v * y₁ = t + u * x₂ + v * y₂ → x₁ = x₂ ∧ y₁ = y₂) →
      (T : ℝ) ^ (1 / 4 : ℝ) * (1 + Real.log T) ^ B ≤ J →
      (T : ℝ) ^ (3 / 4 : ℝ) * (1 + Real.log T) ^ B ≤ (H : ℝ) * J →
      ∃ x ≤ H, ∃ y ≤ J, ∃ z : ℕ, 0 < z ∧ z ^ 2 = g * (t + u * x + v * y) := by
  obtain ⟨B, hB, Tprim, hprimitive⟩ := exists_primitive_terminal_unoriented (256 * C) (by positivity)
  obtain ⟨A, hA, hlongSide⟩ := exists_nonprimitive_long_side
  have hevent := (eventually_ge_atTop (1 : ℝ)).and
    ((Real.tendsto_log_atTop.eventually_ge_atTop (max 8192 A)).and
      ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).eventually_ge_atTop (4 * max 1 Tprim)))
  obtain ⟨Tmin, hTmin⟩ := eventually_atTop.mp hevent
  refine ⟨B + 1, by omega, Tmin, ?_⟩
  intro g t u v H J T hbig hg hu hv hH hJ huv hJH hTdef hspan hproper hside hprod
  obtain ⟨hT1, hlog, hrootLarge⟩ := hTmin (T : ℝ) hbig
  rw [← Real.sqrt_eq_rpow] at hrootLarge
  have hTR : (0 : ℝ) < T := by linarith
  have hTN : 0 < T := by exact_mod_cast hTR
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg
  have hg1 : (1 : ℝ) ≤ g := by exact_mod_cast hg
  have hHR : (0 : ℝ) < H := by exact_mod_cast hH
  have hJR : (0 : ℝ) < J := by exact_mod_cast hJ
  have hΛ1 : 1 ≤ 1 + Real.log T := by have := Real.log_nonneg hT1; linarith
  have hΛlarge : 8192 ≤ 1 + Real.log T := by have := le_max_left (8192 : ℝ) A; linarith
  have hΛA : A ≤ 1 + Real.log T := by have := le_max_right (8192 : ℝ) A; linarith
  have hW1 : 1 ≤ (1 + Real.log T) ^ (B + 1) := one_le_pow₀ hΛ1
  have hWlarge : 8192 ≤ (1 + Real.log T) ^ (B + 1) := by
    have hh : 1 + Real.log T ≤ (1 + Real.log T) ^ (B + 1) := by
      simpa only [pow_one] using pow_le_pow_right₀ hΛ1 (show 1 ≤ B + 1 by omega)
    exact hΛlarge.trans hh
  have hambient : g * (t + u * H + v * J) ≤ T := hTdef.symm.le
  obtain ⟨hprodNat, hlocalNat⟩ := common_factor_ambient_budgets hg hu hv huv hambient hproper
  have hproperR : (g : ℝ) * ((H : ℝ) * J) ≤ T := by exact_mod_cast hprodNat
  have hlocalR : ((g.gcd u : ℝ) * (u : ℝ)) * H ≤ T := by exact_mod_cast hlocalNat
  have hlocalWidth : A * Real.sqrt ((g.gcd u : ℝ) * u) ≤ J :=
    common_factor_local_width_budget (by positivity) hHR hJR.le hT1 (by omega)
      hΛA hlocalR hside hprod
  by_cases hlong : 4 * Real.sqrt T ≤ (H : ℝ) * (g.gcd u : ℝ)
  · exact hlongSide g t u v H J T hg hu hH hTN huv.symm hambient hlocalWidth hlong
  · have hshort : (H : ℝ) * (g.gcd u : ℝ) ≤ 4 * Real.sqrt T := (lt_of_not_ge hlong).le
    have hratio := common_factor_width_ratio hTR hHR hJR (by positivity) hgR.le hproperR hside hprod
    have hJstrong : 256 * g ≤ J := by
      have hWsq : (256 : ℝ) ≤ ((1 + Real.log T) ^ (B + 1)) ^ 2 := by nlinarith
      have hh := mul_le_mul_of_nonneg_left hWsq hgR.le
      have hbound : 256 * (g : ℝ) ≤ J := by nlinarith
      exact_mod_cast hbound
    obtain ⟨r, a, b, H₀, J₀, T₀, ha, hb, hH₀, hJ₀, hab, hT₀def, hproper₀, himage,
      hT₀lo, hT₀hi, hspan₀, hvolume, hwidth₀, hheight₀⟩ :=
      exists_primitive_subrectangle hg hH hJ huv hJH hJstrong hTN hTdef hC.le hspan hshort hproper
    have hprodPlain : (T : ℝ) ^ (3 / 4 : ℝ) ≤ (H : ℝ) * J :=
      (le_mul_of_one_le_right (Real.rpow_nonneg hTR.le _) hW1).trans hprod
    have hmaxLower := common_factor_reduced_max_lower hTR hgR hproperR hprodPlain hT₀lo
    have hT₀large : max 1 Tprim ≤ (T₀ : ℝ) := by linarith
    have hT₀one : (1 : ℝ) ≤ T₀ := (le_max_left _ _).trans hT₀large
    have hT₀T : (T₀ : ℝ) ≤ T := hT₀hi.trans (div_le_self hTR.le (by nlinarith : 1 ≤ (g : ℝ) ^ 2))
    obtain ⟨hH₀budget, hJ₀budget, hprod₀budget⟩ := common_factor_geometric_size_budgets hTR hg1
      hHR hJR (by exact_mod_cast hJH) (by positivity) hproperR hprod
      (Nat.cast_nonneg T₀) hT₀hi hvolume hwidth₀ hheight₀
    have hsideH₀ := absorb_geometric_log_loss B hT₀one hT₀T hΛlarge hH₀budget
    have hsideJ₀ := absorb_geometric_log_loss B hT₀one hT₀T hΛlarge hJ₀budget
    have hprod₀ := absorb_geometric_log_loss B hT₀one hT₀T hΛlarge hprod₀budget
    obtain ⟨x, hx, y, hy, z, hz, heq⟩ := hprimitive r a b H₀ J₀ T₀
      ((le_max_right _ _).trans hT₀large) ha hb hH₀ hJ₀ hab hT₀def.symm.le
      (by simpa only [Nat.cast_add, Nat.cast_mul] using hspan₀) hproper₀
      hsideH₀ hsideJ₀ hprod₀
    obtain ⟨X, hX, Y, hY, hmap⟩ := himage x hx y hy
    refine ⟨X, hX, Y, hY, g * z, Nat.mul_pos hg hz, ?_⟩
    calc
      (g * z) ^ 2 = g ^ 2 * z ^ 2 := by ring
      _ = g ^ 2 * (r + a * x + b * y) := by rw [heq]
      _ = g * (t + u * X + v * Y) := hmap

theorem exists_common_factor_terminal (C : ℝ) (hC : 0 < C) :
    ∃ B : ℕ, 0 < B ∧ ∃ Tmin : ℝ, ∀ (g t u v H J T : ℕ), Tmin ≤ (T : ℝ) →
      0 < g → 0 < u → 0 < v → 0 < H → 0 < J → u.Coprime v →
      T = g * (t + u * H + v * J) →
      (T : ℝ) ≤ C * g * ((u : ℝ) * H + v * J) →
      (∀ x₁ ≤ H, ∀ y₁ ≤ J, ∀ x₂ ≤ H, ∀ y₂ ≤ J,
        t + u * x₁ + v * y₁ = t + u * x₂ + v * y₂ → x₁ = x₂ ∧ y₁ = y₂) →
      (T : ℝ) ^ (1 / 4 : ℝ) * (1 + Real.log T) ^ B ≤ H →
      (T : ℝ) ^ (1 / 4 : ℝ) * (1 + Real.log T) ^ B ≤ J →
      (T : ℝ) ^ (3 / 4 : ℝ) * (1 + Real.log T) ^ B ≤ (H : ℝ) * J →
      ∃ x ≤ H, ∃ y ≤ J, ∃ z : ℕ, 0 < z ∧ z ^ 2 = g * (t + u * x + v * y) := by
  obtain ⟨B, hB, Tmin, hterminal⟩ := exists_ordered_common_factor_terminal C hC
  refine ⟨B, hB, Tmin, ?_⟩
  intro g t u v H J T hbig hg hu hv hH hJ huv hTdef hspan hproper hsideH hsideJ hprod
  by_cases hJH : J ≤ H
  · exact hterminal g t u v H J T hbig hg hu hv hH hJ huv hJH hTdef hspan hproper hsideJ hprod
  · have hTdef' : T = g * (t + v * J + u * H) := by
      simpa only [Nat.add_assoc, Nat.add_comm (v * J) (u * H)] using hTdef
    have hspan' : (T : ℝ) ≤ C * g * ((v : ℝ) * J + u * H) := by
      simpa only [add_comm ((v : ℝ) * J) ((u : ℝ) * H)] using hspan
    have hproper' : ∀ x₁ ≤ J, ∀ y₁ ≤ H, ∀ x₂ ≤ J, ∀ y₂ ≤ H,
        t + v * x₁ + u * y₁ = t + v * x₂ + u * y₂ → x₁ = x₂ ∧ y₁ = y₂ := by
      intro x₁ hx₁ y₁ hy₁ x₂ hx₂ y₂ hy₂ heq
      have hh := hproper y₁ hy₁ x₁ hx₁ y₂ hy₂ x₂ hx₂ (by
        simpa only [Nat.add_assoc, Nat.add_comm (v * x₁) (u * y₁),
          Nat.add_comm (v * x₂) (u * y₂)] using heq)
      exact ⟨hh.2, hh.1⟩
    have hprod' : (T : ℝ) ^ (3 / 4 : ℝ) * (1 + Real.log T) ^ B ≤ (J : ℝ) * H := by
      simpa only [mul_comm (J : ℝ) (H : ℝ)] using hprod
    obtain ⟨x, hx, y, hy, z, hz, heq⟩ := hterminal g t v u J H T hbig hg hv hu hJ hH huv.symm
      (by omega) hTdef' hspan' hproper' hsideH hprod'
    refine ⟨y, hy, x, hx, z, hz, ?_⟩
    simpa only [Nat.add_assoc, Nat.add_comm (v * x) (u * y)] using heq

end Erdos587
