import Arxiv.Arxiv2407_19026.NumericalProfilesChecks.Defs

/-!
# Kernel-checked elementary bounds

Reusable analytic estimates for replacing native numerical certificates with
proofs checked entirely by the Lean kernel.
-/

open Set

namespace Arxiv2407_19026
namespace KernelBounds

noncomputable section

/-- A rational lower bound for `log x` on `(0, 1]`. -/
lemma log_lower_of_le_one {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) :
    (x - x⁻¹) / 2 ≤ Real.log x := by
  let f : ℝ → ℝ := fun t => Real.log t - (t - t⁻¹) / 2
  have hcont : ContinuousOn f (Icc x 1) := by
    intro t ht
    have ht0 : t ≠ 0 := ne_of_gt (lt_of_lt_of_le hx ht.1)
    exact ((Real.continuousAt_log ht0).sub
      ((continuousAt_id.sub (continuousAt_inv₀ ht0)).div_const 2)).continuousWithinAt
  have hderiv :
      ∀ t ∈ interior (Icc x 1),
        HasDerivWithinAt f (-(t - 1) ^ 2 / (2 * t ^ 2))
          (interior (Icc x 1)) t := by
    intro t ht
    have htmem : t ∈ Ioo x 1 := by simpa [interior_Icc] using ht
    have ht0 : t ≠ 0 := ne_of_gt (lt_trans hx htmem.1)
    have hlog := Real.hasDerivAt_log ht0
    have hinv := (hasDerivAt_id t).inv ht0
    have hraw := hlog.sub (((hasDerivAt_id t).sub hinv).div_const 2)
    change HasDerivAt (fun s : ℝ => Real.log s - (s - s⁻¹) / 2)
      (t⁻¹ - (1 - -1 / t ^ 2) / 2) t at hraw
    have hcoeff :
        t⁻¹ - (1 - -1 / t ^ 2) / 2 =
          -(t - 1) ^ 2 / (2 * t ^ 2) := by
      field_simp [ht0]
      ring
    rw [hcoeff] at hraw
    exact hraw.hasDerivWithinAt
  have hanti : AntitoneOn f (Icc x 1) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc x 1) hcont hderiv
    intro t ht
    have htmem : t ∈ Ioo x 1 := by simpa [interior_Icc] using ht
    have ht0 : 0 < t := lt_trans hx htmem.1
    exact div_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr (sq_nonneg (t - 1))) (by positivity)
  have h := hanti (by exact ⟨le_rfl, hx1⟩) (by exact ⟨hx1, le_rfl⟩) hx1
  simpa [f] using h

/-- The first two positive terms of the atanh series bound `log x` from
below when `1 ≤ x`. -/
lemma log_lower_of_one_le {x : ℝ} (hx : 1 ≤ x) :
    let y := (x - 1) / (x + 1)
    2 * (y + y ^ 3 / 3) ≤ Real.log x := by
  dsimp only
  let y := (x - 1) / (x + 1)
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hxp1 : 0 < x + 1 := by positivity
  have hy0 : 0 ≤ y := div_nonneg (sub_nonneg.mpr hx) hxp1.le
  have hy1 : y < 1 := by
    rw [div_lt_one hxp1]
    linarith
  have hyabs : |y| < 1 := by simpa [abs_of_nonneg hy0] using hy1
  have hs := Real.hasSum_log_sub_log_of_abs_lt_one hyabs
  have hpartial :=
    hs.summable.sum_le_tsum (Finset.range 2) (by
      intro i hi
      positivity)
  rw [hs.tsum_eq] at hpartial
  have hlog :
      Real.log x = Real.log (1 + y) - Real.log (1 - y) := by
    rw [← Real.log_div]
    · congr 1
      dsimp [y]
      field_simp
      ring
    · dsimp [y]
      field_simp
      linarith
    · dsimp [y]
      field_simp
      linarith
  rw [hlog]
  norm_num [Finset.sum_range_succ] at hpartial ⊢
  nlinarith

/-- The degree-nine Taylor polynomial for `exp (-z)`. -/
def expNegTaylor9 (z : ℝ) : ℝ :=
  1 - z + z ^ 2 / 2 - z ^ 3 / 6 + z ^ 4 / 24 -
    z ^ 5 / 120 + z ^ 6 / 720 - z ^ 7 / 5040 +
    z ^ 8 / 40320 - z ^ 9 / 362880

/-- A rigorous error term for `expNegTaylor9` on `[0, 1]`. -/
def expNegError10 (z : ℝ) : ℝ :=
  z ^ 10 * 11 / (Nat.factorial 10 * 10)

/-- The Taylor polynomial `expNegTaylor9` approximates `exp (-z)` within
`expNegError10` on `[0, 1]`. -/
lemma exp_neg_approx {z : ℝ} (hz : z ∈ Set.Icc 0 1) :
    |Real.exp (-z) - expNegTaylor9 z| ≤ expNegError10 z := by
  have h := Real.exp_bound (x := -z) (n := 10) (by
    rw [abs_neg, abs_of_nonneg hz.1]
    exact hz.2) (by norm_num)
  norm_num [expNegTaylor9, expNegError10, Finset.sum_range_succ,
    Nat.factorial, abs_neg, abs_of_nonneg hz.1] at h ⊢
  convert h using 1 <;> ring_nf

/-- A Bernstein expansion with nonnegative coefficients is nonnegative on
the unit interval. -/
lemma bernstein_sum_nonneg (n : ℕ) (coeffs : List ℕ)
    {z : ℝ} (hz : z ∈ Set.Icc 0 1) :
    0 ≤ ∑ i ∈ Finset.range (n + 1),
      (coeffs.getD i 0 : ℝ) * z ^ i * (1 - z) ^ (n - i) := by
  apply Finset.sum_nonneg
  intro i hi
  exact mul_nonneg
    (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hz.1 _))
    (pow_nonneg (sub_nonneg.mpr hz.2) _)

end
end KernelBounds
end Arxiv2407_19026
