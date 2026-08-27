/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Local factors for the growing-dimensional FGKMT sieve

These are the literal rational factors of the common coefficient system
in `tex/4.tex`. In particular the pinned harmonic denominator is slightly
smaller than `p - k`; its distance from `p` is bounded by `2 * k`, not `k`.
No prime-distribution or covering conclusion is assumed here.
-/

namespace Erdos4b.FGKMT

noncomputable section

/-- The Euler factor obtained by summing the unpinned coordinates in the
pinned transform. -/
def pinnedLocalFactor (k p : ℝ) : ℝ :=
  1 - (k - 1) / ((p - 1) * (p - k))

/-- The denominator of the one-dimensional prime weight after pinning. -/
def pinnedLocalDenominator (k p : ℝ) : ℝ :=
  (p - k) * pinnedLocalFactor k p

theorem rough_real_bounds {k p : ℝ} (hk : 2 ≤ k) (hp : 2 * k ^ 2 < p) :
    1 < p ∧ k + 1 < p / 2 := by
  have hsq : 2 * k ≤ k ^ 2 := by nlinarith [sq_nonneg (k - 2)]
  constructor <;> nlinarith

theorem pinnedLocalFactor_eq {k p : ℝ} (hp1 : p ≠ 1) (hpk : p ≠ k) :
    pinnedLocalFactor k p = p / (p - 1) - 1 / (p - k) := by
  unfold pinnedLocalFactor
  field_simp [sub_ne_zero.mpr hp1, sub_ne_zero.mpr hpk]
  ring

theorem pinnedLocalDenominator_eq {k p : ℝ} (hp1 : p ≠ 1) (hpk : p ≠ k) :
    pinnedLocalDenominator k p = p - k - (k - 1) / (p - 1) := by
  unfold pinnedLocalDenominator pinnedLocalFactor
  field_simp [sub_ne_zero.mpr hp1, sub_ne_zero.mpr hpk]

theorem pinnedLocalDenominator_bounds {k p : ℝ}
    (hk : 2 ≤ k) (hp : 2 * k ^ 2 < p) :
    p / 2 < pinnedLocalDenominator k p ∧
      |pinnedLocalDenominator k p - p| ≤ 2 * k := by
  obtain ⟨hp1, hhalf⟩ := rough_real_bounds hk hp
  have hpk : k < p := by linarith
  have hquot0 : 0 ≤ (k - 1) / (p - 1) :=
    div_nonneg (by linarith) (by linarith)
  have hquot1 : (k - 1) / (p - 1) < 1 := by
    apply (div_lt_one (by linarith : 0 < p - 1)).2
    linarith
  rw [pinnedLocalDenominator_eq (ne_of_gt hp1) (ne_of_gt hpk)]
  constructor
  · linarith
  · rw [abs_of_nonpos (by linarith : p - k - (k - 1) / (p - 1) - p ≤ 0)]
    linarith

theorem pinnedLocalFactor_pos {k p : ℝ}
    (hk : 2 ≤ k) (hp : 2 * k ^ 2 < p) :
    0 < pinnedLocalFactor k p := by
  obtain ⟨hp1, hhalf⟩ := rough_real_bounds hk hp
  have hpk : 0 < p - k := by linarith
  have hden : 0 < pinnedLocalDenominator k p :=
    (by linarith : 0 < p / 2).trans (pinnedLocalDenominator_bounds hk hp).1
  exact (mul_pos_iff_of_pos_left hpk).mp hden

theorem pinnedLocalFactor_lt_one {k p : ℝ}
    (hk : 2 ≤ k) (hp : 2 * k ^ 2 < p) :
    pinnedLocalFactor k p < 1 := by
  obtain ⟨hp1, hhalf⟩ := rough_real_bounds hk hp
  have hpk : 0 < p - k := by linarith
  have hq : 0 < (k - 1) / ((p - 1) * (p - k)) :=
    div_pos (by linarith) (mul_pos (by linarith) hpk)
  unfold pinnedLocalFactor
  linarith

/-- The exact cancellation that makes the pinned face normalization
independent of its remaining divisor tuple. -/
theorem pinnedLocal_normalization {k p : ℝ}
    (hk : 2 ≤ k) (hp : 2 * k ^ 2 < p) :
    (1 + 1 / pinnedLocalDenominator k p) * (1 - 1 / p) =
      1 / pinnedLocalFactor k p := by
  obtain ⟨hp1, hhalf⟩ := rough_real_bounds hk hp
  have hp0 : p ≠ 0 := ne_of_gt (by linarith : 0 < p)
  have hpk : p - k ≠ 0 := ne_of_gt (by linarith : 0 < p - k)
  have ha : pinnedLocalFactor k p ≠ 0 := (pinnedLocalFactor_pos hk hp).ne'
  have hcancel :
      (1 + 1 / pinnedLocalDenominator k p) * pinnedLocalFactor k p =
        pinnedLocalFactor k p + 1 / (p - k) := by
    unfold pinnedLocalDenominator
    field_simp [hpk, ha]
  have hid : pinnedLocalFactor k p + 1 / (p - k) = p / (p - 1) := by
    rw [pinnedLocalFactor_eq (ne_of_gt hp1) (sub_ne_zero.mp hpk)]
    ring
  apply (eq_div_iff ha).2
  calc
    (1 + 1 / pinnedLocalDenominator k p) * (1 - 1 / p) *
        pinnedLocalFactor k p =
        ((1 + 1 / pinnedLocalDenominator k p) * pinnedLocalFactor k p) *
          (1 - 1 / p) := by ring
    _ = (p / (p - 1)) * (1 - 1 / p) := by rw [hcancel, hid]
    _ = 1 := by field_simp [hp0, (sub_pos.mpr hp1).ne']

theorem totalLocal_normalization {k p : ℝ} (hp : p ≠ 0) (hpk : p ≠ k) :
    1 + k / (p - k) = 1 / (1 - k / p) := by
  have hden : 1 - k / p ≠ 0 := by
    intro h
    apply hpk
    have he : k / p = 1 := by linarith
    exact ((div_eq_one_iff_eq hp).mp he).symm
  field_simp [hp, sub_ne_zero.mpr hpk, hden]
  ring

theorem faceLocal_normalization {k p : ℝ} (hp : p ≠ 0) (hpk : p ≠ k) :
    1 + (k - 1) / (p - k) = (1 - 1 / p) / (1 - k / p) := by
  have hden : 1 - k / p ≠ 0 := by
    intro h
    apply hpk
    have he : k / p = 1 := by linarith
    exact ((div_eq_one_iff_eq hp).mp he).symm
  field_simp [hp, sub_ne_zero.mpr hpk, hden]
  ring

/-- Prime coefficients of the correction to the harmonic function have
a reciprocal-square majorant uniform in the growing rank. -/
theorem harmonicCorrection_prime_bound {k p g : ℝ}
    (hk : 0 ≤ k) (hp : 0 < p) (hg : p / 2 ≤ g) (hclose : |g - p| ≤ 2 * k) :
    |1 / g - 1 / p| ≤ 4 * k / p ^ 2 := by
  have hg0 : 0 < g := (by linarith : 0 < p / 2).trans_le hg
  have hidentity : 1 / g - 1 / p = (p - g) / (g * p) := by
    field_simp [hg0.ne', hp.ne']
  rw [hidentity, abs_div, abs_of_pos (mul_pos hg0 hp), abs_sub_comm p g]
  calc
    |g - p| / (g * p) ≤ (2 * k) / (g * p) :=
      div_le_div_of_nonneg_right hclose (mul_nonneg hg0.le hp.le)
    _ ≤ (2 * k) / ((p / 2) * p) :=
      div_le_div_of_nonneg_left (by positivity)
        (mul_pos (by linarith : 0 < p / 2) hp)
        (mul_le_mul_of_nonneg_right hg hp.le)
    _ = 4 * k / p ^ 2 := by
      field_simp [hp.ne']
      ring

theorem harmonicCorrection_primeSquare_bound {p g : ℝ}
    (hp : 0 < p) (hg : p / 2 ≤ g) :
    |-(1 / (p * g))| ≤ 2 / p ^ 2 := by
  have hg0 : 0 < g := (by linarith : 0 < p / 2).trans_le hg
  rw [abs_neg, abs_of_pos (one_div_pos.mpr (mul_pos hp hg0))]
  calc
    1 / (p * g) ≤ 1 / (p * (p / 2)) :=
      one_div_le_one_div_of_le (mul_pos hp (by linarith))
        (mul_le_mul_of_nonneg_left hg hp.le)
    _ = 2 / p ^ 2 := by field_simp [hp.ne']

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.pinnedLocal_normalization
#print axioms Erdos4b.FGKMT.harmonicCorrection_prime_bound
