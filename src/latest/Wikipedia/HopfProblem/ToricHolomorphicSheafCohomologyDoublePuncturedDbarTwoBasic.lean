import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyDoublePuncturedDbarTwoCutoff

/-!
# Actual scalar corrections on the double-annulus exhaustion

Smooth representatives away from both axes give Cauchy--Green
primitives on larger double annuli. The two-sided cutoff localizes each
successive difference inside that larger region. The first Cauchy--Green
integral then corrects it exactly on the smaller double annulus.
-/

noncomputable section

open Set Metric Filter
open scoped ContDiff Topology

namespace Wikipedia.HopfProblem.HolomorphicSheafCohomology.DoublePuncturedDbarTwo

open PeriodTorusLineBundleClassification

def representative {w : ℂ × ℂ → ℂ} (hw : ContDiffOn ℝ ∞ w domain) (n : ℕ) :
    ℂ × ℂ → ℂ :=
  Classical.choose (DoublePuncturedDbarOne.exists_smooth_representative_away_axes hw
    (radius (n + 1))⁻¹ (inv_pos.mpr (radius_pos (n + 1))))

theorem representative_smooth {w : ℂ × ℂ → ℂ}
    (hw : ContDiffOn ℝ ∞ w domain) (n : ℕ) : ContDiff ℝ ∞ (representative hw n) :=
  (Classical.choose_spec (DoublePuncturedDbarOne.exists_smooth_representative_away_axes hw
    (radius (n + 1))⁻¹ (inv_pos.mpr (radius_pos (n + 1))))).1

theorem representative_eq {w : ℂ × ℂ → ℂ} (hw : ContDiffOn ℝ ∞ w domain)
    (n : ℕ) (q : ℂ × ℂ) (hq₁ : (radius (n + 1))⁻¹ ≤ ‖q.1‖)
    (hq₂ : (radius (n + 1))⁻¹ ≤ ‖q.2‖) : representative hw n q = w q :=
  ((Classical.choose_spec (DoublePuncturedDbarOne.exists_smooth_representative_away_axes hw
    (radius (n + 1))⁻¹ (inv_pos.mpr (radius_pos (n + 1))))).2 q hq₁ hq₂).eq_of_nhds

def initial {w : ℂ × ℂ → ℂ} (hw : ContDiffOn ℝ ∞ w domain) (n : ℕ) : ℂ × ℂ → ℂ :=
  firstCorrection (PuncturedDbarTwo.cutoff (n + 1)) (representative hw n)

theorem initial_smooth {w : ℂ × ℂ → ℂ} (hw : ContDiffOn ℝ ∞ w domain) (n : ℕ) :
    ContDiff ℝ ∞ (initial hw n) :=
  contDiff_firstCorrection (DbarTwo.cutoff_smooth (n + 2))
    (DbarTwo.cutoff_compact (n + 2)) (representative_smooth hw n)

theorem dbarSecond_initial {w : ℂ × ℂ → ℂ} (hw : ContDiffOn ℝ ∞ w domain)
    (n : ℕ) (q : ℂ × ℂ) (hq₁ : q.1 ∈ strip (n + 1)) (hq₂ : q.2 ∈ strip (n + 1)) :
    dbarSecond (initial hw n) q = w q := by
  change dbarSecond (firstCorrection (PuncturedDbarTwo.cutoff (n + 1))
    (representative hw n)) q = w q
  rw [dbarSecond_firstCorrection (DbarTwo.cutoff_smooth (n + 2))
    (DbarTwo.cutoff_compact (n + 2)) (representative_smooth hw n),
    secondLocalizedData, DbarTwo.cutoff_eq_one (n + 2) hq₂.1, one_mul]
  apply representative_eq hw n q
  · simpa only [mem_ball, dist_zero_right, not_lt] using hq₁.2
  · simpa only [mem_ball, dist_zero_right, not_lt] using hq₂.2

def difference {w : ℂ × ℂ → ℂ} (hw : ContDiffOn ℝ ∞ w domain)
    (n : ℕ) (q : ℂ × ℂ) : ℂ := initial hw (n + 1) q - initial hw n q

theorem difference_smooth {w : ℂ × ℂ → ℂ} (hw : ContDiffOn ℝ ∞ w domain) (n : ℕ) :
    ContDiff ℝ ∞ (difference hw n) :=
  (initial_smooth hw (n + 1)).sub (initial_smooth hw n)

theorem dbarSecond_difference {w : ℂ × ℂ → ℂ} (hw : ContDiffOn ℝ ∞ w domain)
    (n : ℕ) (q : ℂ × ℂ) (hq₁ : q.1 ∈ strip (n + 1)) (hq₂ : q.2 ∈ strip (n + 1)) :
    dbarSecond (difference hw n) q = 0 := by
  change dbarSecond (fun x => initial hw (n + 1) x - initial hw n x) q = 0
  rw [dbarSecond_sub ((initial_smooth hw (n + 1)).differentiable (by simp) q)
    ((initial_smooth hw n).differentiable (by simp) q),
    dbarSecond_initial hw (n + 1) q (strip_mono (Nat.le_succ _) hq₁)
      (strip_mono (Nat.le_succ _) hq₂), dbarSecond_initial hw n q hq₁ hq₂, sub_self]

def correctionData {w : ℂ × ℂ → ℂ} (hw : ContDiffOn ℝ ∞ w domain)
    (n : ℕ) (q : ℂ × ℂ) : ℂ := cutoff n q.1 * difference hw n q

theorem correctionData_smooth {w : ℂ × ℂ → ℂ}
    (hw : ContDiffOn ℝ ∞ w domain) (n : ℕ) : ContDiff ℝ ∞ (correctionData hw n) :=
  ((cutoff_smooth n).comp contDiff_fst).mul (difference_smooth hw n)

theorem correctionData_eq_zero {w : ℂ × ℂ → ℂ} (hw : ContDiffOn ℝ ∞ w domain)
    (n : ℕ) (z t : ℂ) (hz : z ∉ tsupport (cutoff n)) :
    correctionData hw n (z, t) = 0 := by
  rw [correctionData, image_eq_zero_of_notMem_tsupport hz, zero_mul]

theorem dbarSecond_correctionData {w : ℂ × ℂ → ℂ} (hw : ContDiffOn ℝ ∞ w domain)
    (n : ℕ) (z t : ℂ) (ht : t ∈ strip (n + 1)) :
    dbarSecond (correctionData hw n) (z, t) = 0 := by
  change dbarSecond (fun q => cutoff n q.1 * difference hw n q) (z, t) = 0
  rw [dbarSecond_mul (f := fun q : ℂ × ℂ => cutoff n q.1)
    (((cutoff_smooth n).comp contDiff_fst).differentiable (by simp) (z, t))
    ((difference_smooth hw n).differentiable (by simp) (z, t)), dbarSecond_fst]
  by_cases hz : cutoff n z = 0
  · simp only [hz, zero_mul, mul_zero, add_zero]
  · rw [dbarSecond_difference hw n (z, t) (mem_strip_succ_of_cutoff_ne_zero n hz) ht]
    simp only [mul_zero, add_zero]

def correction {w : ℂ × ℂ → ℂ} (hw : ContDiffOn ℝ ∞ w domain) (n : ℕ) : ℂ × ℂ → ℂ :=
  cauchyFirst (correctionData hw n)

theorem correction_smooth {w : ℂ × ℂ → ℂ} (hw : ContDiffOn ℝ ∞ w domain) (n : ℕ) :
    ContDiff ℝ ∞ (correction hw n) :=
  contDiff_cauchyFirst (correctionData_smooth hw n) (cutoff_compact n)
    (correctionData_eq_zero hw n)

theorem dbarFirst_correction {w : ℂ × ℂ → ℂ} (hw : ContDiffOn ℝ ∞ w domain)
    (n : ℕ) (q : ℂ × ℂ) (hq : q.1 ∈ strip n) :
    dbarFirst (correction hw n) q = difference hw n q := by
  rw [correction, dbarFirst_cauchyFirst ((correctionData_smooth hw n).of_le (by simp))
    (cutoff_compact n) (correctionData_eq_zero hw n),
    correctionData, cutoff_eq_one n hq, one_mul]

theorem dbarSecond_correction {w : ℂ × ℂ → ℂ} (hw : ContDiffOn ℝ ∞ w domain)
    (n : ℕ) (q : ℂ × ℂ) (hq : q.2 ∈ strip (n + 1)) :
    dbarSecond (correction hw n) q = 0 :=
  dbarSecond_cauchyFirst_eq_zero ((correctionData_smooth hw n).of_le (by simp))
    (cutoff_compact n) (correctionData_eq_zero hw n)
    (dbarSecond_correctionData hw n) q.1 hq

end Wikipedia.HopfProblem.HolomorphicSheafCohomology.DoublePuncturedDbarTwo
