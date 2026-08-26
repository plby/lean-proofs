import ErdosProblems.Erdos421.AdditiveKernelCalculus
import ErdosProblems.Erdos421.WeightedRoughCount
import ErdosProblems.Erdos421.SmoothSieveWindows

/-! # Normalization and finite support of the actual additive rough window -/

namespace Erdos421

open MeasureTheory

theorem oneSidedRealWindow_interval_integral :
    (∫ t in (-1 : ℝ)..0, oneSidedRealWindow t) = 1 := by
  rw [intervalIntegral.integral_eq_integral_of_support_subset (by
    intro t ht
    obtain ⟨hlo, hhi⟩ := oneSidedRealWindow_nonzero ht
    exact ⟨hlo, hhi.le⟩), oneSidedRealWindow_integral]

theorem realAdditiveKernel_integral {Y : ℝ} (hY : 0 < Y) (x : ℝ) :
    (∫ t in x..x + Y, realAdditiveKernel Y x t) = 1 := by
  have harg : (fun t : ℝ ↦ oneSidedRealWindow ((x - t) / Y)) =
      (fun t : ℝ ↦ oneSidedRealWindow (x / Y - t / Y)) := by
    funext t
    congr 1
    ring
  unfold realAdditiveKernel
  rw [intervalIntegral.integral_const_mul, harg,
    intervalIntegral.integral_comp_sub_div (oneSidedRealWindow : ℝ → ℝ) hY.ne' (x / Y)]
  have hlo : x / Y - (x + Y) / Y = -1 := by field_simp; ring
  rw [hlo, sub_self, oneSidedRealWindow_interval_integral, smul_eq_mul]
  field_simp

theorem additiveRoughWindow_interval_sum {Y x : ℝ} (hY : 0 < Y) (hx : 0 ≤ x)
    {B : ℕ} (hB : x + Y ≤ (B : ℝ) + 1) (z : ℕ) :
    additiveRoughWindow B z Y x =
      ∑ n ∈ roughInRealInterval x (x + Y) z, realAdditiveKernel Y x n := by
  classical
  have hxy : x ≤ x + Y := by linarith
  unfold additiveRoughWindow
  simp_rw [← realAdditiveKernel_nat]
  rw [← roughIndicator_weighted_interval_sum]
  apply Finset.sum_congr_of_eq_on_inter
  · intro n hn hnot
    by_contra hne
    have hsup := realAdditiveKernel_nonzero hY (mul_ne_zero_iff.mp hne).1
    exact hnot ((mem_integer_real_interval hx hxy n).mpr ⟨hsup.1, hsup.2.le⟩)
  · intro n hn hnot
    by_contra hne
    have hsup := realAdditiveKernel_nonzero hY (mul_ne_zero_iff.mp hne).1
    have hn0 : 0 < n := by exact_mod_cast hx.trans_lt hsup.1
    have hnB : n < B + 1 := by exact_mod_cast hsup.2.trans_le hB
    exact hnot (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
  · intro n hn hm
    rfl

end Erdos421
