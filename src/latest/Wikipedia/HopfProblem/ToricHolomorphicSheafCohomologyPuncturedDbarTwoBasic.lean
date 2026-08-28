import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyPuncturedDbarOneCutoff
import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyDbarTwoBasic

/-!
# Actual top-degree strip corrections on `ℂ × ℂ*`

The given smooth coefficient is extended across the deleted axis using
the proved inner cutoff, separately at each stage. Actual Cauchy--Green
integrals solve the second derivative on a growing annular strip.
Successive primitives differ holomorphically in that strip, so the
first-coordinate integral gives an exact smooth correction.
-/

noncomputable section

open Set Metric Filter Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.HolomorphicSheafCohomology.PuncturedDbarTwo

open PeriodTorusLineBundleClassification

abbrev domain : Set (ℂ × ℂ) := PuncturedDbarOne.domain

def radius (n : ℕ) : ℝ := DbarTwo.radius (n + 1)

theorem radius_pos (n : ℕ) : 0 < radius n := DbarTwo.radius_pos (n + 1)

theorem radius_eq (n : ℕ) : radius n = (n : ℝ) + 2 := by
  simp only [radius, DbarTwo.radius, Nat.cast_add, Nat.cast_one]
  ring

theorem radius_mono {m n : ℕ} (h : m ≤ n) : radius m ≤ radius n :=
  DbarTwo.radius_mono (Nat.succ_le_succ h)

abbrev cutoff (n : ℕ) : ℂ → ℂ := DbarTwo.cutoff (n + 1)

theorem cutoff_eq_one (n : ℕ) {z : ℂ} (hz : z ∈ closedBall 0 (radius n)) :
    cutoff n z = 1 := DbarTwo.cutoff_eq_one (n + 1) hz

def strip (n : ℕ) : Set ℂ := closedBall 0 (radius n) \ ball 0 (radius n)⁻¹

theorem strip_mono {m n : ℕ} (h : m ≤ n) : strip m ⊆ strip n := by
  have hi : (radius n)⁻¹ ≤ (radius m)⁻¹ :=
    (inv_le_inv₀ (radius_pos n) (radius_pos m)).mpr (radius_mono h)
  intro z hz
  exact ⟨closedBall_subset_closedBall (radius_mono h) hz.1,
    fun hn => hz.2 (ball_subset_ball hi hn)⟩

/-- The actual globally smooth representative at the nth annular scale. -/
def representative {w : ℂ × ℂ → ℂ} (hw : ContDiffOn ℝ ∞ w domain) (n : ℕ) :
    ℂ × ℂ → ℂ :=
  Classical.choose (PuncturedDbarOne.exists_smooth_representative_away_zero hw
    (radius n)⁻¹ (inv_pos.mpr (radius_pos n)))

theorem representative_smooth {w : ℂ × ℂ → ℂ}
    (hw : ContDiffOn ℝ ∞ w domain) (n : ℕ) : ContDiff ℝ ∞ (representative hw n) :=
  (Classical.choose_spec (PuncturedDbarOne.exists_smooth_representative_away_zero hw
    (radius n)⁻¹ (inv_pos.mpr (radius_pos n)))).1

theorem representative_eq {w : ℂ × ℂ → ℂ} (hw : ContDiffOn ℝ ∞ w domain)
    (n : ℕ) (q : ℂ × ℂ) (hq : (radius n)⁻¹ ≤ ‖q.2‖) :
    representative hw n q = w q :=
  ((Classical.choose_spec (PuncturedDbarOne.exists_smooth_representative_away_zero hw
    (radius n)⁻¹ (inv_pos.mpr (radius_pos n)))).2 q hq).eq_of_nhds

def initial {w : ℂ × ℂ → ℂ} (hw : ContDiffOn ℝ ∞ w domain) (n : ℕ) : ℂ × ℂ → ℂ :=
  firstCorrection (cutoff n) (representative hw n)

theorem initial_smooth {w : ℂ × ℂ → ℂ} (hw : ContDiffOn ℝ ∞ w domain) (n : ℕ) :
    ContDiff ℝ ∞ (initial hw n) :=
  contDiff_firstCorrection (DbarTwo.cutoff_smooth (n + 1))
    (DbarTwo.cutoff_compact (n + 1)) (representative_smooth hw n)

theorem dbarSecond_initial {w : ℂ × ℂ → ℂ} (hw : ContDiffOn ℝ ∞ w domain)
    (n : ℕ) (q : ℂ × ℂ) (hq : q.2 ∈ strip n) :
    dbarSecond (initial hw n) q = w q := by
  change dbarSecond (firstCorrection (cutoff n) (representative hw n)) q = w q
  rw [dbarSecond_firstCorrection (DbarTwo.cutoff_smooth (n + 1))
    (DbarTwo.cutoff_compact (n + 1)) (representative_smooth hw n),
    secondLocalizedData, DbarTwo.cutoff_eq_one (n + 1) hq.1, one_mul]
  exact representative_eq hw n q (by
    simpa only [mem_ball, dist_zero_right, not_lt] using hq.2)

def difference {w : ℂ × ℂ → ℂ} (hw : ContDiffOn ℝ ∞ w domain)
    (n : ℕ) (q : ℂ × ℂ) : ℂ := initial hw (n + 1) q - initial hw n q

theorem difference_smooth {w : ℂ × ℂ → ℂ} (hw : ContDiffOn ℝ ∞ w domain) (n : ℕ) :
    ContDiff ℝ ∞ (difference hw n) :=
  (initial_smooth hw (n + 1)).sub (initial_smooth hw n)

theorem dbarSecond_difference {w : ℂ × ℂ → ℂ} (hw : ContDiffOn ℝ ∞ w domain)
    (n : ℕ) (q : ℂ × ℂ) (hq : q.2 ∈ strip n) :
    dbarSecond (difference hw n) q = 0 := by
  change dbarSecond (fun x => initial hw (n + 1) x - initial hw n x) q = 0
  rw [dbarSecond_sub ((initial_smooth hw (n + 1)).differentiable (by simp) q)
    ((initial_smooth hw n).differentiable (by simp) q),
    dbarSecond_initial hw (n + 1) q (strip_mono (Nat.le_succ n) hq),
    dbarSecond_initial hw n q hq, sub_self]

def correctionData {w : ℂ × ℂ → ℂ} (hw : ContDiffOn ℝ ∞ w domain)
    (n : ℕ) (q : ℂ × ℂ) : ℂ := cutoff n q.1 * difference hw n q

theorem correctionData_smooth {w : ℂ × ℂ → ℂ}
    (hw : ContDiffOn ℝ ∞ w domain) (n : ℕ) : ContDiff ℝ ∞ (correctionData hw n) :=
  ((DbarTwo.cutoff_smooth (n + 1)).comp contDiff_fst).mul (difference_smooth hw n)

theorem correctionData_eq_zero {w : ℂ × ℂ → ℂ} (hw : ContDiffOn ℝ ∞ w domain)
    (n : ℕ) (z t : ℂ) (hz : z ∉ tsupport (cutoff n)) :
    correctionData hw n (z, t) = 0 := by
  rw [correctionData, image_eq_zero_of_notMem_tsupport hz, zero_mul]

theorem dbarSecond_correctionData {w : ℂ × ℂ → ℂ} (hw : ContDiffOn ℝ ∞ w domain)
    (n : ℕ) (z t : ℂ) (ht : t ∈ strip n) :
    dbarSecond (correctionData hw n) (z, t) = 0 := by
  change dbarSecond (fun q => cutoff n q.1 * difference hw n q) (z, t) = 0
  rw [dbarSecond_mul (f := fun q : ℂ × ℂ => cutoff n q.1)
    (((DbarTwo.cutoff_smooth (n + 1)).comp contDiff_fst).differentiable (by simp) (z, t))
    ((difference_smooth hw n).differentiable (by simp) (z, t)),
    dbarSecond_fst, dbarSecond_difference hw n (z, t) ht]
  simp only [mul_zero, add_zero]

def correction {w : ℂ × ℂ → ℂ} (hw : ContDiffOn ℝ ∞ w domain) (n : ℕ) : ℂ × ℂ → ℂ :=
  cauchyFirst (correctionData hw n)

theorem correction_smooth {w : ℂ × ℂ → ℂ} (hw : ContDiffOn ℝ ∞ w domain) (n : ℕ) :
    ContDiff ℝ ∞ (correction hw n) :=
  contDiff_cauchyFirst (correctionData_smooth hw n) (DbarTwo.cutoff_compact (n + 1))
    (correctionData_eq_zero hw n)

theorem dbarFirst_correction {w : ℂ × ℂ → ℂ} (hw : ContDiffOn ℝ ∞ w domain)
    (n : ℕ) (q : ℂ × ℂ) (hq : q.1 ∈ closedBall 0 (radius n)) :
    dbarFirst (correction hw n) q = difference hw n q := by
  rw [correction, dbarFirst_cauchyFirst ((correctionData_smooth hw n).of_le (by simp))
    (DbarTwo.cutoff_compact (n + 1)) (correctionData_eq_zero hw n),
    correctionData, cutoff_eq_one n hq, one_mul]

theorem dbarSecond_correction {w : ℂ × ℂ → ℂ} (hw : ContDiffOn ℝ ∞ w domain)
    (n : ℕ) (q : ℂ × ℂ) (hq : q.2 ∈ strip n) :
    dbarSecond (correction hw n) q = 0 :=
  dbarSecond_cauchyFirst_eq_zero ((correctionData_smooth hw n).of_le (by simp))
    (DbarTwo.cutoff_compact (n + 1)) (correctionData_eq_zero hw n)
    (dbarSecond_correctionData hw n) q.1 hq

end Wikipedia.HopfProblem.HolomorphicSheafCohomology.PuncturedDbarTwo
