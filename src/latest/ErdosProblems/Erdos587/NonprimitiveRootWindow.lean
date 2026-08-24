import ErdosProblems.Erdos587.FiberIntegral

/-! Archimedean root windows for a progression with a common factor. -/

namespace Erdos587

theorem nonprimitive_root_window_length {g w D T : ℝ}
    (hg : 0 < g) (hw : 0 ≤ w) (hD : 0 < D) (hT : 0 < T)
    (hambient : g * (w + D) ≤ T) :
    D / (2 * Real.sqrt T) ≤ Real.sqrt ((w + D) / g) - Real.sqrt (w / g) := by
  have hroot : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT
  have hupper : w / g + (D / g) * 1 ≤ (Real.sqrt T / g) ^ 2 := by
    have hh : w + D ≤ T / g := (le_div_iff₀ hg).mpr (by nlinarith)
    calc
      _ = (w + D) / g := by ring
      _ ≤ (T / g) / g := div_le_div_of_nonneg_right hh hg.le
      _ = _ := by rw [div_pow, Real.sq_sqrt hT.le]; ring
  have hh := quadratic_root_interval_length (div_pos hroot hg) (div_pos hD hg)
    (div_nonneg hw hg.le) (by norm_num : (0 : ℝ) ≤ 0) (by norm_num : (0 : ℝ) ≤ 1) hupper
  simp only [sub_zero, mul_one, mul_zero, add_zero] at hh
  rw [← add_div] at hh
  have hcancel : (D / g) / (2 * (Real.sqrt T / g)) = D / (2 * Real.sqrt T) := by field_simp
  rwa [hcancel] at hh

lemma nonprimitive_root_window_square_bounds {g w D z : ℝ}
    (hg : 0 < g) (hw : 0 ≤ w) (hD : 0 ≤ D) (hz : 0 ≤ z)
    (hlo : Real.sqrt (w / g) ≤ z) (hhi : z ≤ Real.sqrt ((w + D) / g)) :
    w ≤ g * z ^ 2 ∧ g * z ^ 2 ≤ w + D := by
  have hlowSq : w / g ≤ z ^ 2 := by
    have hh := pow_le_pow_left₀ (Real.sqrt_nonneg (w / g)) hlo 2
    rwa [Real.sq_sqrt (div_nonneg hw hg.le)] at hh
  have hhighSq : z ^ 2 ≤ (w + D) / g := by
    have hh := pow_le_pow_left₀ hz hhi 2
    rwa [Real.sq_sqrt (div_nonneg (add_nonneg hw hD) hg.le)] at hh
  constructor
  · have hh := (div_le_iff₀ hg).mp hlowSq
    nlinarith
  · have hh := (le_div_iff₀ hg).mp hhighSq
    nlinarith

lemma reduced_period_root_window_budget {u g H : ℕ} {T : ℝ}
    (_hu : 0 < u) (hT : 0 < T) (hwidth : 4 * Real.sqrt T ≤ (H : ℝ) * (g.gcd u : ℝ)) :
    2 * ((u / g.gcd u : ℕ) : ℝ) ≤ (u : ℝ) * H / (2 * Real.sqrt T) := by
  have hroot : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT
  have hfactor : (g.gcd u : ℝ) * ((u / g.gcd u : ℕ) : ℝ) = u := by
    exact_mod_cast Nat.mul_div_cancel' (Nat.gcd_dvd_right g u)
  have hh := mul_le_mul_of_nonneg_right hwidth (Nat.cast_nonneg (u / g.gcd u))
  apply (le_div_iff₀ (by positivity : 0 < 2 * Real.sqrt T)).mpr
  nlinarith [congrArg (fun x : ℝ => (H : ℝ) * x) hfactor]

end Erdos587
