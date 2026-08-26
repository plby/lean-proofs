import ErdosProblems.Erdos788.CodeLengthBounds
import ErdosProblems.Erdos788.SuffixSlackDesign

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Explicit analytic size bound for the suffix-slack design
-/

namespace Erdos788

private theorem designTail_log_factor_le
    {ell : ℕ} {u : ℝ} (hu : 1 ≤ u)
    (hell : (ell : ℝ) ≤ 100 * u) :
    ((Nat.log 2 (SuffixDesign.designTailScale ell) + 1 : ℕ) : ℝ) ≤
      19 + 4 * Real.log u := by
  have hu0 : 0 < u := zero_lt_one.trans_le hu
  have hlogu : 0 ≤ Real.log u := Real.log_nonneg hu
  have hell3 : (ell + 3 : ℕ) ≤ (103 : ℝ) * u := by
    push_cast
    nlinarith
  have hlogell : Real.log (ell + 3 : ℕ) ≤ Real.log (103 * u) := by
    apply Real.log_le_log (by positivity)
    exact hell3
  have hlog103 : Real.log 103 ≤ 7 * Real.log 2 := by
    have hnat : (103 : ℕ) ≤ 2 ^ 7 := by norm_num
    have hreal : (103 : ℝ) ≤ (2 : ℝ) ^ 7 := by exact_mod_cast hnat
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 103) hreal
    simpa [Real.log_pow] using! h
  have hlogell' : Real.log (ell + 3 : ℕ) ≤
      7 * Real.log 2 + Real.log u := by
    rw [Real.log_mul (by norm_num : (103 : ℝ) ≠ 0) (ne_of_gt hu0)] at hlogell
    linarith
  have hscale :
      Real.log (SuffixDesign.designTailScale ell : ℕ) ≤
        18 * Real.log 2 + 2 * Real.log u := by
    rw [SuffixDesign.designTailScale]
    have hexpand : Real.log ((16 * (ell + 3) ^ 2 : ℕ) : ℝ) =
        4 * Real.log 2 + 2 * Real.log (ell + 3 : ℕ) := by
      push_cast
      rw [Real.log_mul (by norm_num : (16 : ℝ) ≠ 0) (by positivity),
        show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow, Real.log_pow]
      ring
    rw [hexpand]
    nlinarith
  have hnat := Real.natLog_le_logb (SuffixDesign.designTailScale ell) 2
  have hlogtwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hquot : Real.log (SuffixDesign.designTailScale ell : ℕ) /
      Real.log 2 ≤ 18 + 4 * Real.log u := by
    apply (div_le_iff₀ hlogtwo).2
    nlinarith [Real.log_two_gt_d9]
  rw [Real.logb] at hnat
  have hmain : (Nat.log 2 (SuffixDesign.designTailScale ell) : ℝ) ≤
      18 + 4 * Real.log u := hnat.trans hquot
  push_cast
  linarith

/-- Combining the short-code estimate with the strong recursive design
bound gives the two terms used in the paper's parameter calculation. -/
theorem builtDesign_coordCard_le_log_bound
    {p r : ℕ} [Fact p.Prime]
    (hp : 2 < p) (hr : 0 < r)
    (C : ShortLinearCode p (2 * r) (trevisanEta p r)) :
    (((SuffixDesign.build C.ell r).coordCard : ℕ) : ℝ) ≤
      1000 * Real.log ((p * r : ℕ) : ℝ) * Real.sqrt r +
        2000000 * Real.log ((p * r : ℕ) : ℝ) ^ 2 *
          (1 + Real.log (Real.log ((p * r : ℕ) : ℝ))) := by
  let u : ℝ := Real.log ((p * r : ℕ) : ℝ)
  have hpr : 3 ≤ p * r := by
    have hp3 : 3 ≤ p := by omega
    have hr1 : 1 ≤ r := by omega
    simpa using! Nat.mul_le_mul hp3 hr1
  have hu : 1 ≤ u := by
    dsimp [u]
    exact ((Real.lt_log_iff_exp_lt
      (by positivity : (0 : ℝ) < (p * r : ℕ))).2
        (Real.exp_one_lt_three.trans_le (by exact_mod_cast hpr))).le
  have hu0 : 0 < u := zero_lt_one.trans_le hu
  have hlogu : 0 ≤ Real.log u := Real.log_nonneg hu
  have hell : (C.ell : ℝ) ≤ 100 * u :=
    (shortLinearCode_ell_lt_log_mul hp hr C).le
  have hell3 : (C.ell : ℝ) + 3 ≤ 103 * u := by nlinarith
  have htail := designTail_log_factor_le hu hell
  have hD := SuffixDesign.build_coordCard_le_designStrongBound C.ell r
  rw [SuffixDesign.designStrongBound] at hD
  have hsqrt : 0 ≤ Real.sqrt (r : ℝ) := Real.sqrt_nonneg _
  have hfirst : 10 * (C.ell : ℝ) * Real.sqrt r ≤
      1000 * u * Real.sqrt r := by
    exact mul_le_mul_of_nonneg_right
      (by nlinarith : 10 * (C.ell : ℝ) ≤ 1000 * u) hsqrt
  have hpair : (C.ell : ℝ) * (C.ell + 3) ≤ 10300 * u ^ 2 := by
    nlinarith [mul_nonneg (show 0 ≤ (C.ell : ℝ) by positivity)
      (show 0 ≤ (C.ell : ℝ) + 3 by positivity)]
  have htail0 : 0 ≤
      ((Nat.log 2 (SuffixDesign.designTailScale C.ell) + 1 : ℕ) : ℝ) := by
    exact_mod_cast
      (Nat.zero_le (Nat.log 2 (SuffixDesign.designTailScale C.ell) + 1))
  have htailUpper0 : 0 ≤ 19 + 4 * Real.log u := by linarith
  have hsecondRaw :
      (C.ell : ℝ) * (C.ell + 3) *
          ((Nat.log 2 (SuffixDesign.designTailScale C.ell) + 1 : ℕ) : ℝ) ≤
        (10300 * u ^ 2) * (19 + 4 * Real.log u) :=
    mul_le_mul hpair htail htail0 (by positivity)
  have hsecond :
      10 * (C.ell : ℝ) * (C.ell + 3) *
          ((Nat.log 2 (SuffixDesign.designTailScale C.ell) + 1 : ℕ) : ℝ) ≤
        2000000 * u ^ 2 * (1 + Real.log u) := by
    have hscaled := mul_le_mul_of_nonneg_left hsecondRaw (by norm_num : (0 : ℝ) ≤ 10)
    have hcoef : 103000 * (19 + 4 * Real.log u) ≤
        2000000 * (1 + Real.log u) := by linarith
    calc
      10 * (C.ell : ℝ) * (C.ell + 3) *
          ((Nat.log 2 (SuffixDesign.designTailScale C.ell) + 1 : ℕ) : ℝ) =
          10 * ((C.ell : ℝ) * (C.ell + 3) *
            ((Nat.log 2 (SuffixDesign.designTailScale C.ell) + 1 : ℕ) : ℝ)) := by ring
      _ ≤ 10 * ((10300 * u ^ 2) * (19 + 4 * Real.log u)) := hscaled
      _ = u ^ 2 * (103000 * (19 + 4 * Real.log u)) := by ring
      _ ≤ u ^ 2 * (2000000 * (1 + Real.log u)) :=
        mul_le_mul_of_nonneg_left hcoef (sq_nonneg u)
      _ = 2000000 * u ^ 2 * (1 + Real.log u) := by ring
  push_cast at hsecond
  change ((SuffixDesign.build C.ell r).coordCard : ℝ) ≤ _
  change _ ≤ 1000 * u * Real.sqrt r +
    2000000 * u ^ 2 * (1 + Real.log u)
  exact hD.trans (add_le_add hfirst hsecond)

end Erdos788
