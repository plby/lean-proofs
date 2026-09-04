/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.RoundedScales
import ErdosProblems.Erdos547b.StabilityPropertyRichEntry

/-!
# Quantitative large-cluster scale in the Section 6 hierarchy

The literal reservoir quota is the upward-rounded value `2 * rho * m`,
where `m` is the degree-form cluster size.  Subtracting one cancels the
ceiling error exactly.  Consequently a reduced density cutoff strictly
larger than `4 * rho` rules out every pair of quantitatively non-large
clusters.
-/

noncomputable section

namespace Erdos547b.ZhaoSection6RichHierarchy

open Erdos547b.ZhaoRoundedScales

/-- Integer reservoir quota corresponding to Zhao's `2 * rho * N`. -/
def richQuota (rho : ℝ) (m : ℕ) : ℕ :=
  upperScale (2 * rho * m)

theorem richQuota_pos {rho : ℝ} {m : ℕ}
    (hrho : 0 < rho) (hm : 0 < m) :
    0 < richQuota rho m := by
  have htarget : (0 : ℝ) < 2 * rho * m := by positivity
  have hle : 2 * rho * m ≤ (richQuota rho m : ℝ) :=
    le_upperScale_cast _
  have hcast : (0 : ℝ) < (richQuota rho m : ℝ) := htarget.trans_le hle
  exact_mod_cast hcast

/-- The `-1` in the non-large reservoir bound removes all upward-rounding
loss. -/
theorem richQuota_sub_one_cast_lt {rho : ℝ} {m : ℕ}
    (hrho : 0 < rho) (hm : 0 < m) :
    ((richQuota rho m - 1 : ℕ) : ℝ) < 2 * rho * m := by
  have hqpos := richQuota_pos hrho hm
  have hceil := upperScale_cast_lt_add_one
    (show (0 : ℝ) ≤ 2 * rho * m by positivity)
  have hqone : 1 ≤ richQuota rho m := by omega
  rw [Nat.cast_sub hqone, Nat.cast_one]
  simpa only [richQuota] using (show
    (richQuota rho m : ℝ) - 1 < 2 * rho * m by
      dsimp only [richQuota] at hceil ⊢
      linarith)

/-- The exact rational inequality consumed by
`claim6_1_rich_full`.  It follows from the scale-level separation
`4 * rho < d`; no exact product or no-rounding hypothesis is used. -/
theorem richQuota_density_separation
    {rho : ℝ} {d : ℚ} {m : ℕ}
    (hrho : 0 < rho) (hm : 0 < m)
    (hcutoff : 4 * rho < (d : ℝ)) :
    (((2 * (richQuota rho m - 1) * m : ℕ) : ℚ)) <
      d * (m : ℚ) * (m : ℚ) := by
  have hquota := richQuota_sub_one_cast_lt hrho hm
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hreal :
      ((2 * (richQuota rho m - 1) * m : ℕ) : ℝ) <
        (d : ℝ) * (m : ℝ) * (m : ℝ) := by
    push_cast
    have hleft :
        (2 : ℝ) * ((richQuota rho m - 1 : ℕ) : ℝ) * m <
          4 * rho * m * m := by
      have hmul := mul_lt_mul_of_pos_right hquota
        (show (0 : ℝ) < 2 * m by positivity)
      calc
        (2 : ℝ) * ((richQuota rho m - 1 : ℕ) : ℝ) * m =
            ((richQuota rho m - 1 : ℕ) : ℝ) * (2 * m) := by ring
        _ < (2 * rho * m) * (2 * m) := hmul
        _ = 4 * rho * m * m := by ring
    have hright : 4 * rho * m * m < (d : ℝ) * m * m := by
      have hmul := mul_lt_mul_of_pos_right hcutoff
        (show (0 : ℝ) < m * m by positivity)
      simpa only [mul_assoc] using hmul
    exact hleft.trans hright
  exact_mod_cast hreal

/-- Deterministic bound for the total high-vertex loss from all non-large
clusters.  With `K*m ≤ 2*q`, it is strictly below `4*rho*q`. -/
theorem richQuota_total_error_lt
    {rho : ℝ} {K m q : ℕ}
    (hrho : 0 < rho) (hm : 0 < m) (hq : 0 < q)
    (hKm : K * m ≤ 2 * q) :
    ((K * (richQuota rho m - 1) : ℕ) : ℝ) < 4 * rho * q := by
  have hquota := richQuota_sub_one_cast_lt hrho hm
  have hKmR : (K : ℝ) * m ≤ 2 * q := by exact_mod_cast hKm
  have hK0 : (0 : ℝ) ≤ K := by positivity
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  push_cast
  by_cases hK : K = 0
  · simp only [gt_iff_lt]
    positivity
  · have hKR : (0 : ℝ) < K := by positivity
    have hleft :
        (K : ℝ) * ((richQuota rho m - 1 : ℕ) : ℝ) <
          2 * rho * (K * m) := by
      calc
        (K : ℝ) * ((richQuota rho m - 1 : ℕ) : ℝ) <
            K * (2 * rho * m) := mul_lt_mul_of_pos_left hquota hKR
        _ = 2 * rho * (K * m) := by ring
    have hright : 2 * rho * ((K : ℝ) * m) ≤
        2 * rho * (2 * q) := by
      exact mul_le_mul_of_nonneg_left hKmR (by positivity)
    calc
      (K : ℝ) * ((richQuota rho m - 1 : ℕ) : ℝ) <
          2 * rho * (K * m) := hleft
      _ ≤ 2 * rho * (2 * q) := hright
      _ = 4 * rho * q := by ring

end Erdos547b.ZhaoSection6RichHierarchy
