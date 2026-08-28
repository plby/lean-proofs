import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Tactic.Linarith

/-!
# A smooth scalar time profile for surgery away from a zero level

The profile is the identity below half the positive attachment margin and
is one above the margin. It preserves sign and has exactly the original
zero. This makes the old and new surgery patches agree without changing
the defining function on a whole neighborhood of the retained boundary.
-/

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.SurgeryTimeProfile

def weight (δ t : ℝ) : ℝ := Real.smoothTransition (2 * t / δ - 1)

def profile (δ t : ℝ) : ℝ := (1 - weight δ t) * t + weight δ t

theorem contDiff_weight (δ : ℝ) : ContDiff ℝ ∞ (weight δ) :=
  Real.smoothTransition.contDiff.comp
    (((contDiff_const.mul contDiff_id).div_const δ).sub contDiff_const)

theorem contDiff_profile (δ : ℝ) : ContDiff ℝ ∞ (profile δ) :=
  ((contDiff_const.sub (contDiff_weight δ)).mul contDiff_id).add (contDiff_weight δ)

theorem profile_eq_self {δ t : ℝ} (hδ : 0 < δ) (ht : t ≤ δ / 2) :
    profile δ t = t := by
  have hw : weight δ t = 0 := Real.smoothTransition.zero_of_nonpos (by
    have h : 2 * t / δ ≤ 1 := (div_le_iff₀ hδ).mpr (by linarith)
    linarith)
  simp only [profile, hw, sub_zero, one_mul, add_zero]

theorem profile_eq_one {δ t : ℝ} (hδ : 0 < δ) (ht : δ ≤ t) :
    profile δ t = 1 := by
  have hw : weight δ t = 1 := Real.smoothTransition.one_of_one_le (by
    have h : 2 ≤ 2 * t / δ := (le_div_iff₀ hδ).mpr (by linarith)
    linarith)
  simp only [profile, hw, sub_self, zero_mul, zero_add]

theorem profile_pos {δ t : ℝ} (ht : 0 < t) : 0 < profile δ t := by
  have hw₀ := Real.smoothTransition.nonneg (2 * t / δ - 1)
  have hw₁ := Real.smoothTransition.le_one (2 * t / δ - 1)
  change 0 ≤ weight δ t at hw₀
  change weight δ t ≤ 1 at hw₁
  by_cases hw : weight δ t = 1
  · simp only [profile, hw, sub_self, zero_mul, zero_add, zero_lt_one]
  · exact add_pos_of_pos_of_nonneg
      (mul_pos (sub_pos.mpr (lt_of_le_of_ne hw₁ hw)) ht) hw₀

theorem profile_pos_iff {δ : ℝ} (hδ : 0 < δ) (t : ℝ) :
    0 < profile δ t ↔ 0 < t := by
  constructor
  · intro hp
    by_contra ht
    have ht' : t ≤ 0 := le_of_not_gt ht
    rw [profile_eq_self hδ (ht'.trans (half_pos hδ).le)] at hp
    exact (not_lt_of_ge ht') hp
  · exact profile_pos

theorem profile_eq_zero_iff {δ : ℝ} (hδ : 0 < δ) (t : ℝ) :
    profile δ t = 0 ↔ t = 0 := by
  constructor
  · intro hp
    have ht : t ≤ 0 := by
      by_contra ht
      have hpos := profile_pos (δ := δ) (lt_of_not_ge ht)
      rw [hp] at hpos
      exact (lt_irrefl 0) hpos
    exact (profile_eq_self hδ (ht.trans (half_pos hδ).le)).symm.trans hp
  · rintro rfl
    exact profile_eq_self hδ (half_pos hδ).le

theorem profile_nonneg_iff {δ : ℝ} (hδ : 0 < δ) (t : ℝ) :
    0 ≤ profile δ t ↔ 0 ≤ t := by
  rw [le_iff_lt_or_eq, profile_pos_iff hδ, eq_comm, profile_eq_zero_iff hδ,
    eq_comm, ← le_iff_lt_or_eq]

theorem profile_germ {δ : ℝ} (hδ : 0 < δ) : profile δ =ᶠ[𝓝 (0 : ℝ)] id := by
  filter_upwards [isOpen_Iio.mem_nhds (half_pos hδ)] with t ht
  exact profile_eq_self hδ ht.le

end Wikipedia.HopfProblem.DegreeCollapse.SurgeryTimeProfile
