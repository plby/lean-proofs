import Arxiv.Arxiv2411_18291.ShiftedChooseBounds

/-! # A finite scalar criterion for simultaneous clique sampling -/

namespace Arxiv2411_18291

theorem clique_sampling_failure_of_scalar_bounds (r m n : ℕ) {κ α : ℝ}
    (hκ : 0 ≤ κ) (hn : 1 ≤ n) (hfactor : (m.factorial : ℝ) ≤ (n : ℝ) ^ α)
    (hexp : 2 * α ≤ (m : ℝ) - 2 * κ)
    (htail : 6 * (n : ℝ) ^ r * Real.exp (-((n : ℝ) ^ α / 12)) < 1) :
    (n.choose r : ℝ) * (2 * Real.exp (-((((n : ℝ) ^ m / m.factorial) / 2) *
      ((n : ℝ) ^ (-κ)) ^ 2 / (2 * (1 + 2 * (n : ℝ) ^ (-κ)))))) < 1 := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  let c : ℝ := (n : ℝ) ^ (-κ)
  let μ : ℝ := ((n : ℝ) ^ m / m.factorial) / 2
  have hc : 0 ≤ c := Real.rpow_nonneg hnpos.le _
  have hc1 : c ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos
    (by exact_mod_cast hn) (neg_nonpos.mpr hκ)
  have heq : (n : ℝ) ^ m * c ^ 2 = (n : ℝ) ^ ((m : ℝ) - 2 * κ) := by
    dsimp only [c]
    rw [← Real.rpow_natCast (n : ℝ) m, ← Real.rpow_mul_natCast hnpos.le (-κ) 2,
      ← Real.rpow_add hnpos]
    congr 1
    push_cast
    ring
  have hmajor : (n : ℝ) ^ α * m.factorial ≤ (n : ℝ) ^ m * c ^ 2 := by
    calc
      _ ≤ (n : ℝ) ^ α * (n : ℝ) ^ α :=
        mul_le_mul_of_nonneg_left hfactor (Real.rpow_nonneg hnpos.le _)
      _ ≤ _ := by
        rw [heq, ← Real.rpow_add hnpos]
        exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn)
          (by linarith only [hexp])
  have hbudget : (n : ℝ) ^ α / 2 ≤ μ * c ^ 2 := by
    have hid : μ * c ^ 2 = ((n : ℝ) ^ m * c ^ 2) / (2 * m.factorial) := by
      dsimp only [μ]
      ring
    rw [hid]
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * m.factorial)).mpr
    nlinarith only [hmajor]
  have hnum : (n : ℝ) ^ α / 12 ≤ μ * c ^ 2 / (2 * (1 + 2 * c)) := by
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * (1 + 2 * c))).mpr
    have hden : 2 * (1 + 2 * c) ≤ 6 := by linarith only [hc1]
    have hh := mul_le_mul_of_nonneg_left hden
      (by positivity : (0 : ℝ) ≤ (n : ℝ) ^ α / 12)
    nlinarith only [hh, hbudget]
  have hprob := Real.exp_le_exp.mpr (neg_le_neg hnum)
  have hcount : (n.choose r : ℝ) ≤ (n : ℝ) ^ r := by exact_mod_cast Nat.choose_le_pow n r
  change (n.choose r : ℝ) * (2 * Real.exp (-(μ * c ^ 2 / (2 * (1 + 2 * c))))) < 1
  calc
    _ ≤ (n : ℝ) ^ r * (2 * Real.exp (-((n : ℝ) ^ α / 12))) :=
      mul_le_mul hcount (mul_le_mul_of_nonneg_left hprob (by norm_num))
        (by positivity) (by positivity)
    _ < 1 := by
      have hh : 0 ≤ (n : ℝ) ^ r * Real.exp (-((n : ℝ) ^ α / 12)) := by positivity
      nlinarith only [hh, htail]

end Arxiv2411_18291
