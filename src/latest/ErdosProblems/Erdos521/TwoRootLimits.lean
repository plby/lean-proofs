/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Asymptotic two-root bounds for intervals of fixed relative width.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.SmallBallLimits
import ErdosProblems.Erdos521.NormalizedTwoRoots

namespace Erdos521

open MeasureTheory Filter
open scoped Topology

theorem two_interval_roots_normalized_error (n : ℕ) {a b d t : ℝ}
    (ha : 0 ≤ a) (hab : a < b) (hb₀ : 1 / 2 ≤ b) (hb₁ : b < 1)
    (ht : 0 < t) (hd : 0 ≤ d) (hwidth : b - a ≤ d * (1 - b))
    (htail : b ^ (2 * (n + 1)) ≤ 1 / 2) :
    sequenceLaw.real {ε | 2 ≤ intervalRootCount ε n a b} ≤
      normalizedSmallBallConstant * t + normalizedSmallBallError (geometricVariance b (n + 1)) t +
        96 * d ^ 4 / t ^ 2 := by
  have hV := geometricVariance_succ_pos b n
  have hδ : 0 < t * Real.sqrt (geometricVariance b (n + 1)) := mul_pos ht (Real.sqrt_pos.mpr hV)
  have hlower := geometricVariance_lower hb₁ (n + 1) htail
  rw [inv_eq_one_div, div_le_iff₀ (by positivity : 0 < 4 * (1 - b))] at hlower
  have hscale : 1 / 4 ≤ geometricVariance b (n + 1) * (1 - b) := by nlinarith
  apply (two_interval_roots_probability_split n ha hab hb₁ hδ).trans
  exact add_le_add (powerSum_smallBall_normalized_error n hb₀ hb₁.le ht)
    (two_root_energy_normalized_le hab hb₁ ht hV hd hwidth hscale)

theorem balanced_two_root_energy {d : ℝ} (hd : 0 < d) :
    96 * d ^ 4 / (d ^ (4 / 3 : ℝ)) ^ 2 = 96 * d ^ (4 / 3 : ℝ) := by
  have hsq : (d ^ (4 / 3 : ℝ)) ^ 2 = d ^ (8 / 3 : ℝ) := by
    rw [← Real.rpow_natCast (d ^ (4 / 3 : ℝ)) 2, ← Real.rpow_mul hd.le]
    norm_num
  rw [hsq, ← Real.rpow_natCast d 4, mul_div_assoc, ← Real.rpow_sub hd]
  norm_num

theorem eventually_two_interval_roots_probability (n : ℕ → ℕ) (a b : ℕ → ℝ)
    (hn : Tendsto n atTop atTop) (hb : Tendsto b atTop (𝓝 1)) {d : ℝ} (hd : 0 < d)
    (hI : ∀ᶠ j : ℕ in atTop, 0 ≤ a j ∧ a j < b j ∧ b j < 1 ∧
      b j - a j ≤ d * (1 - b j) ∧ (b j) ^ (2 * (n j + 1)) ≤ 1 / 2)
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ j : ℕ in atTop,
      sequenceLaw.real {ε | 2 ≤ intervalRootCount ε (n j) (a j) (b j)} ≤
        (normalizedSmallBallConstant + 96) * d ^ (4 / 3 : ℝ) + η := by
  have hV : Tendsto (fun j ↦ geometricVariance (b j) (n j + 1)) atTop atTop :=
    geometricVariance_tendsto_atTop _ b ((tendsto_add_atTop_nat 1).comp hn) hb
  have ht : 0 < d ^ (4 / 3 : ℝ) := Real.rpow_pos_of_pos hd _
  filter_upwards [hI, hb.eventually (lt_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1)),
    (normalizedSmallBallError_tendsto_zero _ hV ht).eventually (gt_mem_nhds hη)] with j hj hjb hjerr
  have h := two_interval_roots_normalized_error (n j) hj.1 hj.2.1 hjb.le hj.2.2.1 ht hd.le
    hj.2.2.2.1 hj.2.2.2.2
  rw [balanced_two_root_energy hd] at h
  nlinarith

end Erdos521
