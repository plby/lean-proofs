import ErdosProblems.Erdos4.FGKMTFiniteCovering

/-! A generous exponential lower bound for the explicit finite covering threshold. -/

namespace Erdos4.FGKMT

theorem add_cube_le_fourth {E : ℝ} (hE : 2 ≤ E) : E + E ^ 3 ≤ E ^ 4 := by
  have hE1 : 1 ≤ E := by linarith
  have hh : E ≤ E ^ 3 := by
    simpa only [pow_one] using pow_le_pow_right₀ hE1 (by norm_num : 1 ≤ 3)
  calc
    _ ≤ E ^ 3 + E ^ 3 := add_le_add hh le_rfl
    _ = 2 * E ^ 3 := by ring
    _ ≤ E * E ^ 3 := mul_le_mul_of_nonneg_right hE (by positivity)
    _ = _ := by ring

theorem propagationCoefficient_exp_bound {r : ℕ} (hr : 1 ≤ r)
    {κ D : ℝ} (hκ : 0 < κ) (hκr : 1 / (r : ℝ) ≤ κ)
    (hD0 : 0 ≤ D) (hD1 : D ≤ 1) :
    2 * propagationCoefficient r (2 * r) κ D ≤ Real.exp (64 * (r : ℝ) ^ 2) := by
  let E := Real.exp (4 * (r : ℝ) ^ 2)
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hr0 : (0 : ℝ) < r := lt_of_lt_of_le (by norm_num) hrR
  have hEbase : 1 + 4 * (r : ℝ) ^ 2 ≤ E := by
    simpa only [E, add_comm] using Real.add_one_le_exp (4 * (r : ℝ) ^ 2)
  have hE5 : 5 ≤ E := by nlinarith
  have hE4 : 4 ≤ E := by linarith
  have hE2 : 2 ≤ E := by linarith
  have hE1 : 1 ≤ E := by linarith
  have hE0 : 0 ≤ E := by linarith
  have hrE : (r : ℝ) ≤ E := by nlinarith
  have hAE : ((2 * r : ℕ) : ℝ) ≤ E := by push_cast; nlinarith
  have hrecip : 1 / κ ≤ (r : ℝ) := by
    apply (div_le_iff₀ hκ).mpr
    have hh := (div_le_iff₀ hr0).mp hκr
    nlinarith
  have hrExp : (r : ℝ) ≤ Real.exp (r : ℝ) := by
    have hh := Real.add_one_le_exp (r : ℝ)
    linarith
  have hinv : ∀ n : ℕ, n ≤ 4 * r → 1 / κ ^ n ≤ E := by
    intro n hn
    have hnR : (n : ℝ) ≤ 4 * (r : ℝ) := by exact_mod_cast hn
    calc
      _ = (1 / κ) ^ n := (one_div_pow κ n).symm
      _ ≤ Real.exp (r : ℝ) ^ n :=
        pow_le_pow_left₀ (by positivity) (hrecip.trans hrExp) n
      _ = Real.exp ((n : ℝ) * r) := (Real.exp_nat_mul (r : ℝ) n).symm
      _ ≤ E := Real.exp_le_exp.mpr (by nlinarith)
  have hir := hinv r (by omega)
  have hiA := hinv (2 * r) (by omega)
  have hir1 := hinv (r + 1) (by omega)
  have hnorm : normalizerCoefficient r κ ≤ E ^ 4 := by
    calc
      _ = 5 + 2 * (r : ℝ) * (1 / κ ^ r) := by unfold normalizerCoefficient; ring
      _ ≤ E + E * E * E := by gcongr
      _ = E + E ^ 3 := by ring
      _ ≤ _ := add_cube_le_fourth hE2
  have hdeg : degreeCoefficient r κ D ≤ E ^ 4 := by
    have hDsq : D ^ 2 ≤ 1 := pow_le_one₀ hD0 hD1
    calc
      _ = (1 + 3 * D ^ 2) + 2 * (r : ℝ) * D * (1 / κ ^ (r + 1)) := by
        unfold degreeCoefficient
        ring
      _ ≤ 4 + 2 * (r : ℝ) * 1 * (1 / κ ^ (r + 1)) := by gcongr; linarith
      _ ≤ E + E * E * 1 * E := by gcongr
      _ = E + E ^ 3 := by ring
      _ ≤ _ := add_cube_le_fourth hE2
  have hnorm0 := normalizerCoefficient_nonneg r hκ
  have hdeg0 : 0 ≤ degreeCoefficient r κ D :=
    zero_le_one.trans (degreeCoefficient_ge_one r hκ hD0)
  have hfirst : 2 * (normalizerCoefficient r κ * ((2 * r : ℕ) : ℝ) * D / κ ^ r) /
      κ ^ (2 * r) ≤ E ^ 8 := by
    calc
      _ = 2 * normalizerCoefficient r κ * ((2 * r : ℕ) : ℝ) * D *
          (1 / κ ^ r) * (1 / κ ^ (2 * r)) := by ring
      _ ≤ E * E ^ 4 * E * 1 * E * E := by gcongr
      _ = _ := by ring
  have hsecond : ((2 * r : ℕ) : ℝ) ^ 2 / κ ^ r ≤ E ^ 3 := by
    calc
      _ = ((2 * r : ℕ) : ℝ) ^ 2 * (1 / κ ^ r) := by ring
      _ ≤ E ^ 2 * E := by gcongr
      _ = _ := by ring
  have hthird : ((2 * r : ℕ) : ℝ) *
      (2 * degreeCoefficient r κ D / κ ^ (2 * r)) ≤ E ^ 7 := by
    calc
      _ = ((2 * r : ℕ) : ℝ) * 2 * degreeCoefficient r κ D *
          (1 / κ ^ (2 * r)) := by ring
      _ ≤ E * E * E ^ 4 * E := by gcongr
      _ = _ := by ring
  have hfourth : 4 * ((2 * r : ℕ) : ℝ) ^ 2 / κ ^ (2 * r) ≤ E ^ 4 := by
    calc
      _ = 4 * ((2 * r : ℕ) : ℝ) ^ 2 * (1 / κ ^ (2 * r)) := by ring
      _ ≤ E * E ^ 2 * E := by gcongr
      _ = _ := by ring
  have hloss : lossCoefficient r (2 * r) κ D ≤ E ^ 9 := by
    calc
      _ ≤ E ^ 8 + E ^ 3 + E ^ 7 + E ^ 4 := by
        unfold lossCoefficient
        exact add_le_add (add_le_add (add_le_add hfirst hsecond) hthird) hfourth
      _ ≤ E ^ 8 + E ^ 8 + E ^ 8 + E ^ 8 := by
        exact add_le_add (add_le_add (add_le_add le_rfl
          (pow_le_pow_right₀ hE1 (by norm_num : 3 ≤ 8)))
          (pow_le_pow_right₀ hE1 (by norm_num : 7 ≤ 8)))
          (pow_le_pow_right₀ hE1 (by norm_num : 4 ≤ 8))
      _ = 4 * E ^ 8 := by ring
      _ ≤ E * E ^ 8 := mul_le_mul_of_nonneg_right hE4 (pow_nonneg hE0 _)
      _ = _ := by ring
  have hexp : Real.exp (((2 * r : ℕ) : ℝ) * D) ≤ E := by
    apply Real.exp_le_exp.mpr
    have hh : ((2 * r : ℕ) : ℝ) * D ≤ ((2 * r : ℕ) : ℝ) * 1 := by gcongr
    push_cast at hh
    push_cast
    nlinarith
  have hloss0 := lossCoefficient_nonneg r (2 * r) hκ hD0
  have hprop : propagationCoefficient r (2 * r) κ D ≤ E ^ 12 := by
    calc
      _ = 1 + 2 * Real.exp (((2 * r : ℕ) : ℝ) * D) * lossCoefficient r (2 * r) κ D := rfl
      _ ≤ 1 + E * E * E ^ 9 := by gcongr
      _ = 1 + E ^ 11 := by ring
      _ ≤ E ^ 11 + E ^ 11 := add_le_add (one_le_pow₀ hE1) le_rfl
      _ = 2 * E ^ 11 := by ring
      _ ≤ E * E ^ 11 := mul_le_mul_of_nonneg_right hE2 (pow_nonneg hE0 _)
      _ = _ := by ring
  calc
    _ ≤ E * E ^ 12 := mul_le_mul hE2 hprop
      (zero_le_one.trans (propagationCoefficient_ge_one r (2 * r) hκ hD0)) hE0
    _ = E ^ 13 := by ring
    _ = Real.exp (52 * (r : ℝ) ^ 2) := by
      change Real.exp (4 * (r : ℝ) ^ 2) ^ 13 = _
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith [sq_nonneg (r : ℝ)])

theorem coveringThreshold_exp_lower {r : ℕ} (hr : 1 ≤ r)
    {κ D : ℝ} (hκ : 0 < κ) (hκr : 1 / (r : ℝ) ≤ κ)
    (hD0 : 0 ≤ D) (hD1 : D ≤ 1) :
    Real.exp (-(64 * (r : ℝ) ^ 2)) ≤ coveringThreshold r (2 * r) κ D := by
  have hbound := propagationCoefficient_exp_bound hr hκ hκr hD0 hD1
  have hpos : 0 < 2 * propagationCoefficient r (2 * r) κ D := by
    have hh := propagationCoefficient_ge_one r (2 * r) hκ hD0
    positivity
  have hh := one_div_le_one_div_of_le hpos hbound
  simpa only [coveringThreshold, Real.exp_neg, one_div] using hh

end Erdos4.FGKMT
