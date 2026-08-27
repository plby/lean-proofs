import ErdosProblems.Erdos4.TiltedMoments

/-! Variance and lost mass control the exponential probability of remaining uncovered. -/

namespace Erdos4.Tilted

open FGKMT

theorem retained_exponential_mean_le {Ω : Type*} [Fintype Ω] (ν : FiniteLaw Ω)
    (W loss degree : Ω → ℝ) (d : ℝ) (hloss : ∀ o, 0 ≤ loss o) (hdegree : ∀ o, 0 ≤ degree o)
    (hgood : ∀ o, 0 < ν.weight o → 1 / 2 ≤ W o → loss o ≤ 1 / 4 → d ≤ degree o) :
    ν.mean (fun o => Real.exp (-degree o)) ≤
      4 * ν.mean (fun o => (W o - 1) ^ 2) + 4 * ν.mean loss + Real.exp (-d) := by
  classical
  have hbad : ν.prob (fun o => W o < 1 / 2) ≤ 4 * ν.mean (fun o => (W o - 1) ^ 2) := by
    calc
      _ ≤ ν.prob (fun o => (1 / 2 : ℝ) ≤ |W o - 1|) := by
        apply ν.prob_mono
        intro o ho
        have hh := neg_le_abs (W o - 1)
        linarith
      _ ≤ ν.mean (fun o => (W o - 1) ^ 2) / (1 / 2 : ℝ) ^ 2 := ν.chebyshev W 1 (by norm_num)
      _ = _ := by ring
  have hpoint : ν.mean (fun o => Real.exp (-degree o)) ≤
      ν.mean (fun o => (if W o < 1 / 2 then (1 : ℝ) else 0) + 4 * loss o + Real.exp (-d)) := by
    apply ν.mean_mono_support
    intro o ho
    have he1 : Real.exp (-degree o) ≤ 1 := by
      simpa only [Real.exp_zero] using Real.exp_le_exp.mpr (neg_nonpos.mpr (hdegree o))
    have hexp := (Real.exp_pos (-d)).le
    by_cases hw : W o < 1 / 2
    · rw [if_pos hw]
      linarith [hloss o]
    · rw [if_neg hw, zero_add]
      by_cases hl : loss o ≤ 1 / 4
      · have he := Real.exp_le_exp.mpr (neg_le_neg (hgood o ho (le_of_not_gt hw) hl))
        linarith [hloss o]
      · have hh : 1 / 4 < loss o := lt_of_not_ge hl
        linarith
  rw [FiniteLaw.mean_add, FiniteLaw.mean_add, ← FiniteLaw.prob_eq_mean,
    FiniteLaw.mean_const_mul, FiniteLaw.mean_const] at hpoint
  exact hpoint.trans (add_le_add (add_le_add hbad le_rfl) le_rfl)

end Erdos4.Tilted
