import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Overlap profiles for intervals and circular arcs

This file isolates the elementary geometry behind the circle
rearrangement step.  `lineArcOverlap r s d` is the overlap length of two
real intervals of radii `r` and `s` whose centers are distance `d` apart.
On a circle of circumference `2 * π`, the corresponding overlap profile
on the half-circle is the real-line overlap, truncated below by the
unavoidable overlap of two long arcs.

Both formulae are manifestly antitone in the center distance.  The final
lemmas record the center-distance comparison needed when two terminal
shells with a common outer endpoint are compressed to centered arcs.
-/

open Set MeasureTheory

namespace Erdos1038

noncomputable section

/-- The length of overlap of real intervals of radii `r` and `s` whose
centers are a nonnegative distance `d` apart.  The formula is meaningful
for all real inputs, which makes its global antitonicity convenient. -/
def lineArcOverlap (r s d : ℝ) : ℝ :=
  max 0 (min (2 * r) (min (2 * s) (r + s - d)))

lemma lineArcOverlap_nonneg (r s d : ℝ) :
    0 ≤ lineArcOverlap r s d := by
  exact le_max_left _ _

lemma lineArcOverlap_comm (r s d : ℝ) :
    lineArcOverlap r s d = lineArcOverlap s r d := by
  unfold lineArcOverlap
  rw [add_comm r s, min_left_comm]

theorem lineArcOverlap_antitone (r s : ℝ) :
    Antitone (lineArcOverlap r s) := by
  intro d e hde
  unfold lineArcOverlap
  apply max_le_max_left
  apply min_le_min_left
  apply min_le_min_left
  linarith

theorem lineArcOverlap_mono_distance {r s d e : ℝ} (hde : d ≤ e) :
    lineArcOverlap r s e ≤ lineArcOverlap r s d :=
  lineArcOverlap_antitone r s hde

/-- Exact Lebesgue-measure formula for the overlap of two real closed
intervals. -/
theorem volume_inter_centeredIntervals {r s d : ℝ}
    (hd : 0 ≤ d) :
    volume (Icc (-r) r ∩ Icc (d - s) (d + s)) =
      ENNReal.ofReal (lineArcOverlap r s d) := by
  rw [Icc_inter_Icc, Real.volume_Icc]
  calc
    ENNReal.ofReal (min r (d + s) - max (-r) (d - s)) =
        ENNReal.ofReal
          (max 0 (min r (d + s) - max (-r) (d - s))) := by
      simp only [ENNReal.ofReal_max, ENNReal.ofReal_zero, max_eq_right, zero_le]
    _ = ENNReal.ofReal (lineArcOverlap r s d) := by
      congr 1
      unfold lineArcOverlap
      rcases le_total r s with hrs | hsr
      · rcases le_total d (s - r) with hdsmall | hdlarge
        · have hleft : max (-r) (d - s) = -r := by
            apply max_eq_left
            linarith
          have hright : min r (d + s) = r := by
            apply min_eq_left
            linarith
          have hmin : min (2 * r) (min (2 * s) (r + s - d)) = 2 * r := by
            apply min_eq_left
            exact le_min (by linarith) (by linarith)
          rw [hleft, hright, hmin]
          congr 1
          ring
        · have hleft : max (-r) (d - s) = d - s := by
            apply max_eq_right
            linarith
          have hright : min r (d + s) = r := by
            apply min_eq_left
            linarith
          have hmin : min (2 * r) (min (2 * s) (r + s - d)) = r + s - d := by
            rw [min_eq_right (by linarith : r + s - d ≤ 2 * s)]
            exact min_eq_right (by linarith : r + s - d ≤ 2 * r)
          rw [hleft, hright, hmin]
          congr 1
          ring
      · rcases le_total d (r - s) with hdsmall | hdlarge
        · have hleft : max (-r) (d - s) = d - s := by
            apply max_eq_right
            linarith
          have hright : min r (d + s) = d + s := by
            apply min_eq_right
            linarith
          have hmin : min (2 * r) (min (2 * s) (r + s - d)) = 2 * s := by
            rw [min_eq_left (by linarith : 2 * s ≤ r + s - d)]
            exact min_eq_right (by linarith)
          rw [hleft, hright, hmin]
          congr 1
          ring
        · have hleft : max (-r) (d - s) = d - s := by
            apply max_eq_right
            linarith
          have hright : min r (d + s) = r := by
            apply min_eq_left
            linarith
          have hmin : min (2 * r) (min (2 * s) (r + s - d)) = r + s - d := by
            rw [min_eq_right (by linarith : r + s - d ≤ 2 * s)]
            exact min_eq_right (by linarith : r + s - d ≤ 2 * r)
          rw [hleft, hright, hmin]
          congr 1
          ring

/-- The overlap-length profile for two centered arcs of radii `r` and `s`
on a circle of circumference `2 * π`, expressed as a function of the
circular distance `d ∈ [0, π]` between their centers. -/
def circleArcOverlap (r s d : ℝ) : ℝ :=
  max (2 * (r + s - Real.pi)) (lineArcOverlap r s d)

lemma circleArcOverlap_nonneg (r s d : ℝ) :
    0 ≤ circleArcOverlap r s d := by
  exact lineArcOverlap_nonneg r s d |>.trans (le_max_right _ _)

lemma circleArcOverlap_comm (r s d : ℝ) :
    circleArcOverlap r s d = circleArcOverlap s r d := by
  simp [circleArcOverlap, lineArcOverlap_comm, add_comm]

theorem circleArcOverlap_antitone (r s : ℝ) :
    Antitone (circleArcOverlap r s) := by
  intro d e hde
  unfold circleArcOverlap
  exact max_le_max_left _ (lineArcOverlap_antitone r s hde)

theorem circleArcOverlap_mono_distance {r s d e : ℝ} (hde : d ≤ e) :
    circleArcOverlap r s e ≤ circleArcOverlap r s d :=
  circleArcOverlap_antitone r s hde

/-- On the half-circle, the circular overlap profile is exactly the sum
of the direct real-line overlap and its single wraparound translate. -/
theorem circleArcOverlap_eq_line_add_wrap {r s d : ℝ}
    (hr0 : 0 ≤ r) (hrpi : r ≤ Real.pi)
    (hs0 : 0 ≤ s) (hspi : s ≤ Real.pi)
    (_hd0 : 0 ≤ d) (hdpi : d ≤ Real.pi) :
    circleArcOverlap r s d =
      lineArcOverlap r s d + lineArcOverlap r s (2 * Real.pi - d) := by
  rcases le_total (r + s) Real.pi with hrs | hpi
  · have hbase : 2 * (r + s - Real.pi) ≤ 0 := by linarith
    have hwrapTail : r + s - (2 * Real.pi - d) ≤ 0 := by linarith
    have hwrap : lineArcOverlap r s (2 * Real.pi - d) = 0 := by
      unfold lineArcOverlap
      rw [min_eq_right (by linarith : r + s - (2 * Real.pi - d) ≤ 2 * s)]
      rw [min_eq_right (by linarith : r + s - (2 * Real.pi - d) ≤ 2 * r)]
      exact max_eq_left hwrapTail
    rw [hwrap, add_zero]
    unfold circleArcOverlap
    exact max_eq_right (hbase.trans (lineArcOverlap_nonneg r s d))
  · have hbase0 : 0 ≤ 2 * (r + s - Real.pi) := by linarith
    rcases le_total d (2 * Real.pi - (r + s)) with hd | hd
    · have hwrapTail : r + s - (2 * Real.pi - d) ≤ 0 := by linarith
      have hwrap : lineArcOverlap r s (2 * Real.pi - d) = 0 := by
        unfold lineArcOverlap
        rw [min_eq_right (by linarith : r + s - (2 * Real.pi - d) ≤ 2 * s)]
        rw [min_eq_right (by linarith : r + s - (2 * Real.pi - d) ≤ 2 * r)]
        exact max_eq_left hwrapTail
      have hbase_le_line :
          2 * (r + s - Real.pi) ≤ lineArcOverlap r s d := by
        unfold lineArcOverlap
        apply le_max_of_le_right
        apply le_min
        · linarith
        · apply le_min <;> linarith
      rw [hwrap, add_zero]
      unfold circleArcOverlap
      exact max_eq_right hbase_le_line
    · have hdirect0 : 0 ≤ r + s - d := by linarith
      have hwrap0 : 0 ≤ r + s - (2 * Real.pi - d) := by linarith
      have hdirect : lineArcOverlap r s d = r + s - d := by
        unfold lineArcOverlap
        rw [min_eq_right (by linarith : r + s - d ≤ 2 * s)]
        rw [min_eq_right (by linarith : r + s - d ≤ 2 * r)]
        exact max_eq_right hdirect0
      have hwrap :
          lineArcOverlap r s (2 * Real.pi - d) =
            r + s - (2 * Real.pi - d) := by
        unfold lineArcOverlap
        rw [min_eq_right
          (by linarith : r + s - (2 * Real.pi - d) ≤ 2 * s)]
        rw [min_eq_right
          (by linarith : r + s - (2 * Real.pi - d) ≤ 2 * r)]
        exact max_eq_right hwrap0
      rw [hdirect, hwrap]
      have hsum :
          (r + s - d) + (r + s - (2 * Real.pi - d)) =
            2 * (r + s - Real.pi) := by ring
      rw [hsum]
      unfold circleArcOverlap
      rw [hdirect]
      exact max_eq_left (by linarith)

/-- When terminal shells with lower radii `a,c` and common upper radius
`b` are compressed to centered arcs, the separation of the opposite-sign
interval components cannot increase. -/
theorem compressedShell_crossDistance_le {a b c : ℝ}
    (ha : 0 ≤ a) (hc : 0 ≤ c) (hbpi : b ≤ Real.pi) :
    b - (a + c) / 2 ≤
      min (b + (a + c) / 2) (2 * Real.pi - (b + (a + c) / 2)) := by
  apply le_min
  · linarith
  · linarith

/-- The overlap profile comparison corresponding to compression of the
opposite-sign components of two terminal shells. -/
theorem circleArcOverlap_compressedShell_ge {a b c r s : ℝ}
    (ha : 0 ≤ a) (hc : 0 ≤ c) (hbpi : b ≤ Real.pi) :
    circleArcOverlap r s
        (min (b + (a + c) / 2) (2 * Real.pi - (b + (a + c) / 2))) ≤
      circleArcOverlap r s (b - (a + c) / 2) := by
  exact circleArcOverlap_antitone r s
    (compressedShell_crossDistance_le ha hc hbpi)

end

end Erdos1038
