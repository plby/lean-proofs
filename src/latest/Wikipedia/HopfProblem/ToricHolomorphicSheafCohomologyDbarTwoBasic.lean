import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationLocalDbar

/-!
# Actual top-degree antiholomorphic primitives: strip corrections

For arbitrary smooth data on the complex plane squared, Cauchy--Green
in the second coordinate gives a primitive on each horizontal strip.
Successive strip primitives differ by a function holomorphic in the
second variable on the smaller strip. A first-coordinate Cauchy--Green
integral therefore gives an exact correction on the smaller bidisc.

These are actual smooth functions and actual coordinate derivatives.
There is no compact-support or closedness assumption on the input.
-/

noncomputable section

open Set Metric
open scoped ContDiff

namespace Wikipedia.HopfProblem.HolomorphicSheafCohomology.DbarTwo

open PeriodTorusLineBundleClassification

/-- Radii for the actual bidisc exhaustion. -/
def radius (n : ℕ) : ℝ := (n : ℝ) + 1

theorem radius_pos (n : ℕ) : 0 < radius n := by
  dsimp [radius]
  positivity

theorem radius_mono {m n : ℕ} (h : m ≤ n) : radius m ≤ radius n := by
  exact add_le_add (Nat.cast_le.mpr h) (le_refl 1)

/-- A genuine compact smooth cutoff, constructed by the proved bump
function theorem, equal to one on the indicated closed disc. -/
def cutoff (n : ℕ) : ℂ → ℂ :=
  Classical.choose (exists_complex_cutoff (radius n) (radius_pos n))

theorem cutoff_smooth (n : ℕ) : ContDiff ℝ ∞ (cutoff n) :=
  (Classical.choose_spec (exists_complex_cutoff (radius n) (radius_pos n))).1

theorem cutoff_compact (n : ℕ) : HasCompactSupport (cutoff n) :=
  (Classical.choose_spec (exists_complex_cutoff (radius n) (radius_pos n))).2.1

theorem cutoff_eq_one (n : ℕ) {z : ℂ} (hz : z ∈ closedBall 0 (radius n)) :
    cutoff n z = 1 :=
  (Classical.choose_spec (exists_complex_cutoff (radius n) (radius_pos n))).2.2 z hz

/-- The actual second-coordinate integral with the nth cutoff. -/
def initial (w : ℂ × ℂ → ℂ) (n : ℕ) : ℂ × ℂ → ℂ :=
  firstCorrection (cutoff n) w

theorem initial_smooth {w : ℂ × ℂ → ℂ} (hw : ContDiff ℝ ∞ w) (n : ℕ) :
    ContDiff ℝ ∞ (initial w n) :=
  contDiff_firstCorrection (cutoff_smooth n) (cutoff_compact n) hw

theorem dbarSecond_initial {w : ℂ × ℂ → ℂ} (hw : ContDiff ℝ ∞ w)
    (n : ℕ) (q : ℂ × ℂ) :
    dbarSecond (initial w n) q = cutoff n q.2 * w q :=
  dbarSecond_firstCorrection (cutoff_smooth n) (cutoff_compact n) hw q

/-- The difference of successive actual strip primitives. -/
def difference (w : ℂ × ℂ → ℂ) (n : ℕ) (q : ℂ × ℂ) : ℂ :=
  initial w (n + 1) q - initial w n q

theorem difference_smooth {w : ℂ × ℂ → ℂ} (hw : ContDiff ℝ ∞ w) (n : ℕ) :
    ContDiff ℝ ∞ (difference w n) :=
  (initial_smooth hw (n + 1)).sub (initial_smooth hw n)

theorem dbarSecond_difference_eq_zero {w : ℂ × ℂ → ℂ}
    (hw : ContDiff ℝ ∞ w) (n : ℕ) (q : ℂ × ℂ)
    (hq : q.2 ∈ closedBall 0 (radius n)) :
    dbarSecond (difference w n) q = 0 := by
  have hq' : q.2 ∈ closedBall 0 (radius (n + 1)) :=
    closedBall_subset_closedBall (radius_mono (Nat.le_succ n)) hq
  change dbarSecond (fun x => initial w (n + 1) x - initial w n x) q = 0
  rw [dbarSecond_sub ((initial_smooth hw (n + 1)).differentiable (by simp) q)
    ((initial_smooth hw n).differentiable (by simp) q),
    dbarSecond_initial hw, dbarSecond_initial hw,
    cutoff_eq_one (n + 1) hq', cutoff_eq_one n hq, one_mul, sub_self]

/-- First-coordinate localized correction data. -/
def correctionData (w : ℂ × ℂ → ℂ) (n : ℕ) (q : ℂ × ℂ) : ℂ :=
  cutoff n q.1 * difference w n q

theorem correctionData_smooth {w : ℂ × ℂ → ℂ}
    (hw : ContDiff ℝ ∞ w) (n : ℕ) : ContDiff ℝ ∞ (correctionData w n) :=
  ((cutoff_smooth n).comp contDiff_fst).mul (difference_smooth hw n)

theorem correctionData_eq_zero (w : ℂ × ℂ → ℂ) (n : ℕ) (z t : ℂ)
    (hz : z ∉ tsupport (cutoff n)) : correctionData w n (z, t) = 0 := by
  rw [correctionData, image_eq_zero_of_notMem_tsupport hz, zero_mul]

theorem dbarSecond_correctionData_eq_zero {w : ℂ × ℂ → ℂ}
    (hw : ContDiff ℝ ∞ w) (n : ℕ) (z t : ℂ)
    (ht : t ∈ closedBall 0 (radius n)) :
    dbarSecond (correctionData w n) (z, t) = 0 := by
  change dbarSecond (fun q => cutoff n q.1 * difference w n q) (z, t) = 0
  rw [dbarSecond_mul (f := fun q : ℂ × ℂ => cutoff n q.1)
      (((cutoff_smooth n).comp contDiff_fst).differentiable
      (by simp) (z, t)) ((difference_smooth hw n).differentiable (by simp) (z, t)),
    dbarSecond_fst, dbarSecond_difference_eq_zero hw n (z, t) ht]
  simp only [mul_zero, add_zero]

/-- The actual first-coordinate Cauchy--Green correction. -/
def correction (w : ℂ × ℂ → ℂ) (n : ℕ) : ℂ × ℂ → ℂ :=
  cauchyFirst (correctionData w n)

theorem correction_smooth {w : ℂ × ℂ → ℂ} (hw : ContDiff ℝ ∞ w) (n : ℕ) :
    ContDiff ℝ ∞ (correction w n) :=
  contDiff_cauchyFirst (correctionData_smooth hw n) (cutoff_compact n)
    (correctionData_eq_zero w n)

theorem dbarFirst_correction {w : ℂ × ℂ → ℂ} (hw : ContDiff ℝ ∞ w)
    (n : ℕ) (q : ℂ × ℂ) (hq : q.1 ∈ closedBall 0 (radius n)) :
    dbarFirst (correction w n) q = difference w n q := by
  rw [correction, dbarFirst_cauchyFirst
    ((correctionData_smooth hw n).of_le (by simp)) (cutoff_compact n)
    (correctionData_eq_zero w n), correctionData, cutoff_eq_one n hq, one_mul]

theorem dbarSecond_correction {w : ℂ × ℂ → ℂ} (hw : ContDiff ℝ ∞ w)
    (n : ℕ) (q : ℂ × ℂ) (hq : q.2 ∈ closedBall 0 (radius n)) :
    dbarSecond (correction w n) q = 0 :=
  dbarSecond_cauchyFirst_eq_zero ((correctionData_smooth hw n).of_le (by simp))
    (cutoff_compact n) (correctionData_eq_zero w n)
    (dbarSecond_correctionData_eq_zero hw n) q.1 hq

end Wikipedia.HopfProblem.HolomorphicSheafCohomology.DbarTwo
