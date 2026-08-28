import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Linarith

/-!
# A smooth cutoff around the original elliptic boundary radius

The parameter `a` is the original positive root radius, while the argument
of `radialCutoff a` is the squared radius.  The two explicit smooth
transitions give a plateau around `a ^ 2` and compact support strictly
inside `(0, 1)`.  In particular, a caller can use squared norm without
requiring differentiability of the norm at the origin.

The cutoff is constructed from Mathlib's `Real.smoothTransition`; no
cutoff, collar, isotopy, or recognition result is assumed.
-/

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.ConstructionSphereRecognition.GaugeIsotopy

/-- A cutoff in squared radius, equal to one around the radius `a`. -/
def radialCutoff (a s : ℝ) : ℝ :=
  Real.smoothTransition ((s - a ^ 2 / 4) / (a ^ 2 / 4)) *
    Real.smoothTransition (((3 + a ^ 2) / 4 - s) / ((1 - a ^ 2) / 4))

/-- Smoothness holds for every fixed parameter, even outside the geometric range. -/
theorem radialCutoff_contDiff (a : ℝ) : ContDiff ℝ ∞ (radialCutoff a) :=
  (Real.smoothTransition.contDiff.comp
    ((contDiff_id.sub contDiff_const).div_const (a ^ 2 / 4))).mul
      (Real.smoothTransition.contDiff.comp
        ((contDiff_const.sub contDiff_id).div_const ((1 - a ^ 2) / 4)))

theorem radialCutoff_nonneg (a s : ℝ) : 0 ≤ radialCutoff a s :=
  mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)

theorem radialCutoff_le_one (a s : ℝ) : radialCutoff a s ≤ 1 := by
  unfold radialCutoff
  calc
    _ ≤ 1 * Real.smoothTransition (((3 + a ^ 2) / 4 - s) / ((1 - a ^ 2) / 4)) :=
      mul_le_mul_of_nonneg_right (Real.smoothTransition.le_one _)
        (Real.smoothTransition.nonneg _)
    _ ≤ 1 := by
      simpa only [one_mul] using Real.smoothTransition.le_one
        (((3 + a ^ 2) / 4 - s) / ((1 - a ^ 2) / 4))

theorem radialCutoff_mem_Icc (a s : ℝ) : radialCutoff a s ∈ Icc (0 : ℝ) 1 :=
  ⟨radialCutoff_nonneg a s, radialCutoff_le_one a s⟩

/-- The cutoff vanishes on and inside half the original root radius. -/
theorem radialCutoff_eq_zero_of_le (a s : ℝ) (hs : s ≤ a ^ 2 / 4) :
    radialCutoff a s = 0 := by
  have h : (s - a ^ 2 / 4) / (a ^ 2 / 4) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hs)
      (div_nonneg (sq_nonneg a) (by norm_num))
  rw [radialCutoff, Real.smoothTransition.zero_of_nonpos h, zero_mul]

/-- The outer transition vanishes before the boundary of the original unit disc. -/
theorem radialCutoff_eq_zero_of_ge {a s : ℝ} (ha : 0 < a) (ha1 : a < 1)
    (hs : (3 + a ^ 2) / 4 ≤ s) : radialCutoff a s = 0 := by
  have ha2 : a ^ 2 < 1 := pow_lt_one₀ ha.le ha1 two_ne_zero
  have h : ((3 + a ^ 2) / 4 - s) / ((1 - a ^ 2) / 4) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hs)
      (div_nonneg (sub_nonneg.mpr ha2.le) (by norm_num))
  rw [radialCutoff, Real.smoothTransition.zero_of_nonpos h, mul_zero]

/-- Both transitions are exactly one throughout this explicit closed plateau. -/
theorem radialCutoff_eq_one {a s : ℝ} (ha : 0 < a) (ha1 : a < 1)
    (hs0 : a ^ 2 / 2 ≤ s) (hs1 : s ≤ (1 + a ^ 2) / 2) :
    radialCutoff a s = 1 := by
  have ha2 : 0 < a ^ 2 := sq_pos_of_pos ha
  have ha2lt : a ^ 2 < 1 := pow_lt_one₀ ha.le ha1 two_ne_zero
  have hin : 1 ≤ (s - a ^ 2 / 4) / (a ^ 2 / 4) :=
    (one_le_div (div_pos ha2 (by norm_num))).mpr (by linarith)
  have hout : 1 ≤ ((3 + a ^ 2) / 4 - s) / ((1 - a ^ 2) / 4) :=
    (one_le_div (div_pos (sub_pos.mpr ha2lt) (by norm_num))).mpr (by linarith)
  rw [radialCutoff, Real.smoothTransition.one_of_one_le hin,
    Real.smoothTransition.one_of_one_le hout, one_mul]

/-- The original boundary radius lies in the plateau. -/
theorem radialCutoff_at_radius_sq {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    radialCutoff a (a ^ 2) = 1 := by
  have ha2 : a ^ 2 < 1 := pow_lt_one₀ ha.le ha1 two_ne_zero
  exact radialCutoff_eq_one ha ha1 (by nlinarith [sq_nonneg a]) (by linarith)

/-- The cutoff is identically one on an actual neighborhood of the boundary radius. -/
theorem radialCutoff_eventually_eq_one {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    ∀ᶠ s in 𝓝 (a ^ 2), radialCutoff a s = 1 := by
  have ha2 : 0 < a ^ 2 := sq_pos_of_pos ha
  have ha2lt : a ^ 2 < 1 := pow_lt_one₀ ha.le ha1 two_ne_zero
  have h0 : a ^ 2 / 2 < a ^ 2 := by linarith
  have h1 : a ^ 2 < (1 + a ^ 2) / 2 := by linarith
  filter_upwards [Ioo_mem_nhds h0 h1] with s hs
  exact radialCutoff_eq_one ha ha1 hs.1.le hs.2.le

theorem radialCutoff_eq_zero_of_nonpos (a : ℝ) {s : ℝ} (hs : s ≤ 0) :
    radialCutoff a s = 0 :=
  radialCutoff_eq_zero_of_le a s (hs.trans (div_nonneg (sq_nonneg a) (by norm_num)))

theorem radialCutoff_eq_zero_of_one_le {a s : ℝ} (ha : 0 < a) (ha1 : a < 1)
    (hs : 1 ≤ s) : radialCutoff a s = 0 := by
  have ha2 : a ^ 2 < 1 := pow_lt_one₀ ha.le ha1 two_ne_zero
  exact radialCutoff_eq_zero_of_ge ha ha1 (by linarith)

/-- Even the ordinary support stays between the explicit transition endpoints. -/
theorem radialCutoff_support_subset {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    Function.support (radialCutoff a) ⊆ Ioo (a ^ 2 / 4) ((3 + a ^ 2) / 4) := by
  intro s hs
  change radialCutoff a s ≠ 0 at hs
  constructor
  · exact lt_of_not_ge (fun h => hs (radialCutoff_eq_zero_of_le a s h))
  · exact lt_of_not_ge (fun h => hs (radialCutoff_eq_zero_of_ge ha ha1 h))

/-- The closed support retains positive distance from both ends of the root interval. -/
theorem radialCutoff_tsupport_subset {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    tsupport (radialCutoff a) ⊆ Icc (a ^ 2 / 4) ((3 + a ^ 2) / 4) := by
  exact closure_minimal
    ((radialCutoff_support_subset ha ha1).trans Ioo_subset_Icc_self) isClosed_Icc

theorem radialCutoff_hasCompactSupport {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    HasCompactSupport (radialCutoff a) :=
  IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport _)
    (radialCutoff_tsupport_subset ha ha1)

/-- Compact support is genuinely contained in the interior of the original radius interval. -/
theorem radialCutoff_tsupport_subset_unit {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    tsupport (radialCutoff a) ⊆ Ioo (0 : ℝ) 1 := by
  have ha2 : 0 < a ^ 2 := sq_pos_of_pos ha
  have ha2lt : a ^ 2 < 1 := pow_lt_one₀ ha.le ha1 two_ne_zero
  intro s hs
  have h := radialCutoff_tsupport_subset ha ha1 hs
  constructor <;> linarith [h.1, h.2]

end Wikipedia.HopfProblem.ConstructionSphereRecognition.GaugeIsotopy
