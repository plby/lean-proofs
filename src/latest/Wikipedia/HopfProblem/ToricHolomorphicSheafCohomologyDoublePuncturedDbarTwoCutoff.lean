import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyDoublePuncturedDbarOneCutoff
import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyPuncturedDbarTwoBasic

/-!
# Two-sided compact cutoffs for the actual double annulus

The cutoff equals one on a prescribed closed annulus and is supported
inside a strictly larger annulus. This controls both the deleted axis
and infinity in the genuine Cauchy--Green correction.
-/

noncomputable section

open Set Metric
open scoped ContDiff Topology

namespace Wikipedia.HopfProblem.HolomorphicSheafCohomology.DoublePuncturedDbarTwo

open PeriodTorusLineBundleClassification

abbrev domain : Set (ℂ × ℂ) := DoublePuncturedDbarOne.domain
abbrev radius (n : ℕ) : ℝ := PuncturedDbarTwo.radius n
abbrev strip (n : ℕ) : Set ℂ := DoublePuncturedDbarOne.closedAnnulus (radius n)

theorem radius_pos (n : ℕ) : 0 < radius n := PuncturedDbarTwo.radius_pos n

theorem radius_lt_succ (n : ℕ) : radius n < radius (n + 1) := by
  simp only [PuncturedDbarTwo.radius_eq, Nat.cast_add, Nat.cast_one]
  linarith

theorem strip_mono {m n : ℕ} (h : m ≤ n) : strip m ⊆ strip n :=
  DoublePuncturedDbarOne.closedAnnulus_mono (radius_pos m)
    (PuncturedDbarTwo.radius_mono h)

def outerBump (n : ℕ) : ContDiffBump (0 : ℂ) where
  rIn := radius n
  rOut := radius (n + 1)
  rIn_pos := radius_pos n
  rIn_lt_rOut := radius_lt_succ n

def innerBump (n : ℕ) : ContDiffBump (0 : ℂ) where
  rIn := (radius (n + 1))⁻¹
  rOut := (radius n)⁻¹
  rIn_pos := inv_pos.mpr (radius_pos (n + 1))
  rIn_lt_rOut := (inv_lt_inv₀ (radius_pos (n + 1)) (radius_pos n)).mpr
    (radius_lt_succ n)

def cutoff (n : ℕ) (z : ℂ) : ℂ :=
  (outerBump n z : ℂ) * (1 - (innerBump n z : ℂ))

theorem cutoff_smooth (n : ℕ) : ContDiff ℝ ∞ (cutoff n) :=
  (Complex.ofRealCLM.contDiff.comp (outerBump n).contDiff).mul
    (contDiff_const.sub (Complex.ofRealCLM.contDiff.comp (innerBump n).contDiff))

theorem cutoff_compact (n : ℕ) : HasCompactSupport (cutoff n) := by
  have ho : HasCompactSupport (fun z : ℂ => (outerBump n z : ℂ)) :=
    (outerBump n).hasCompactSupport.comp_left Complex.ofReal_zero
  exact ho.mul_right

theorem cutoff_eq_one (n : ℕ) {z : ℂ} (hz : z ∈ strip n) : cutoff n z = 1 := by
  have houter : outerBump n z = 1 := (outerBump n).one_of_mem_closedBall hz.1
  have hinner : innerBump n z = 0 := (innerBump n).zero_of_le_dist (by
    change (radius n)⁻¹ ≤ dist z 0
    simpa only [mem_ball, dist_zero_right, not_lt] using hz.2)
  simp only [cutoff, houter, hinner, Complex.ofReal_one, Complex.ofReal_zero,
    sub_zero, mul_one]

theorem mem_strip_succ_of_cutoff_ne_zero (n : ℕ) {z : ℂ} (hz : cutoff n z ≠ 0) :
    z ∈ strip (n + 1) := by
  have ho : ‖z‖ < radius (n + 1) := by
    by_contra h
    have he : outerBump n z = 0 := (outerBump n).zero_of_le_dist (by
      change radius (n + 1) ≤ dist z 0
      simpa only [dist_zero_right] using not_lt.mp h)
    exact hz (by simp only [cutoff, he, Complex.ofReal_zero, zero_mul])
  have hi : (radius (n + 1))⁻¹ < ‖z‖ := by
    by_contra h
    have he : innerBump n z = 1 := (innerBump n).one_of_mem_closedBall
      (mem_closedBall_zero_iff.mpr (not_lt.mp h))
    exact hz (by simp only [cutoff, he, Complex.ofReal_one, sub_self, mul_zero])
  exact ⟨mem_closedBall_zero_iff.mpr ho.le, by
    simpa only [mem_ball, dist_zero_right, not_lt] using hi.le⟩

end Wikipedia.HopfProblem.HolomorphicSheafCohomology.DoublePuncturedDbarTwo
