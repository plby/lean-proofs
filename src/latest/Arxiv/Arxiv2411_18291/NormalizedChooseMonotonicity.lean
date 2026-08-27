import Arxiv.Arxiv2411_18291.NibbleBinomialScales
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # Monotonicity of binomial coefficients divided by a fractional power -/

namespace Arxiv2411_18291

theorem choose_eq_vertex_factor {n d : ℕ} (hn : 0 < n) (hd : 0 < d) :
    (n.choose d : ℝ) = (n : ℝ) * ((n - 1).choose (d - 1) : ℝ) / d := by
  have h := Nat.add_one_mul_choose_eq (n - 1) (d - 1)
  rw [Nat.sub_add_cancel hn, Nat.sub_add_cancel hd] at h
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  apply (eq_div_iff hd0).mpr
  exact_mod_cast h.symm

theorem normalized_choose_mono {m n d : ℕ} (hm : 0 < m) (hmn : m ≤ n) (hd : 0 < d)
    {α : ℝ} (hα : α ≤ 1) :
    (m : ℝ) ^ (-α) * (m.choose d : ℝ) ≤ (n : ℝ) ^ (-α) * (n.choose d : ℝ) := by
  have hn : 0 < n := hm.trans_le hmn
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hid (x : ℕ) (hx : 0 < x) :
      (x : ℝ) ^ (-α) * (x.choose d : ℝ) =
        (x : ℝ) ^ (1 - α) * ((x - 1).choose (d - 1) : ℝ) / d := by
    have hx0 : (0 : ℝ) < x := by exact_mod_cast hx
    rw [choose_eq_vertex_factor hx hd,
      show 1 - α = -α + 1 by ring, Real.rpow_add hx0, Real.rpow_one]
    ring
  rw [hid m hm, hid n hn]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg d)
  apply mul_le_mul
  · exact Real.rpow_le_rpow hm0.le (by exact_mod_cast hmn) (by linarith only [hα])
  · exact_mod_cast Nat.choose_le_choose (d - 1) (Nat.sub_le_sub_right hmn 1)
  · exact Nat.cast_nonneg _
  · exact Real.rpow_nonneg hn0.le _

end Arxiv2411_18291
