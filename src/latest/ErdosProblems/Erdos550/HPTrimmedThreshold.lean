import Mathlib

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Trimmed endpoint thresholds

The raw head weight of a matching endpoint can equal its entire cluster size.
The stateful embedding also reserves an `ε`-fraction for vertices that are not
retained toward the head.  Subtracting two `ε`-fractions from every raw weight
and truncating at zero produces a nonnegative packedness threshold which lies
below the common retained cap.  The total loss is explicit and additive.
-/

open Finset

namespace Erdos550

noncomputable def hpTrimmedThreshold
    (weight ε size : ℝ) : ℝ :=
  max 0 (weight - 2 * ε * size)

lemma hpTrimmedThreshold_nonneg
    (weight ε size : ℝ) :
    0 ≤ hpTrimmedThreshold weight ε size :=
  le_max_left _ _

lemma hpTrimmedThreshold_lower
    (weight ε size : ℝ) :
    weight - 2 * ε * size ≤ hpTrimmedThreshold weight ε size :=
  le_max_right _ _

lemma hpTrimmedThreshold_le_weight
    (weight ε size : ℝ)
    (hweight0 : 0 ≤ weight) (hε0 : 0 ≤ ε) (hsize0 : 0 ≤ size) :
    hpTrimmedThreshold weight ε size ≤ weight := by
  rw [hpTrimmedThreshold, max_le_iff]
  exact ⟨hweight0, by nlinarith [mul_nonneg hε0 hsize0]⟩

lemma hpTrimmedThreshold_le_retained_cap
    (weight ε size : ℝ)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hsize : 0 ≤ size) (hweight : weight ≤ size) :
    hpTrimmedThreshold weight ε size ≤ (1 - ε) * size := by
  rw [hpTrimmedThreshold, max_le_iff]
  constructor
  · exact mul_nonneg (sub_nonneg.mpr hε1) hsize
  · nlinarith

/-- A unit equipartition rounding gap is absorbed once the trimming loss on
the smaller part is at least one vertex. -/
lemma hpTrimmedThreshold_le_rounded_cap
    (weight ε size cap : ℝ)
    (hweight : weight ≤ size)
    (hε0 : 0 ≤ ε) (hcap0 : 0 ≤ cap)
    (hcap : cap ≤ size) (hsize : size ≤ cap + 1)
    (hround : 1 ≤ 2 * ε * cap) :
    hpTrimmedThreshold weight ε size ≤ cap := by
  rw [hpTrimmedThreshold, max_le_iff]
  constructor
  · exact hcap0
  · have htrim :
        weight - 2 * ε * size ≤ size - 2 * ε * size := by
      linarith
    have hεsize : 2 * ε * cap ≤ 2 * ε * size :=
      mul_le_mul_of_nonneg_left hcap (mul_nonneg (by norm_num) hε0)
    linarith

lemma sum_hpTrimmedThreshold_lower
    {κ : Type*} [Fintype κ]
    (weight size : κ → ℝ) (ε : ℝ) :
    (∑ k, weight k) - 2 * ε * ∑ k, size k ≤
      ∑ k, hpTrimmedThreshold (weight k) ε (size k) := by
  calc
    (∑ k, weight k) - 2 * ε * ∑ k, size k =
        ∑ k, (weight k - 2 * ε * size k) := by
      rw [Finset.sum_sub_distrib, Finset.mul_sum]
    _ ≤ ∑ k, hpTrimmedThreshold (weight k) ε (size k) :=
      Finset.sum_le_sum fun k _ =>
        hpTrimmedThreshold_lower (weight k) ε (size k)

lemma sum_hpTrimmedThreshold_lower_on
    {κ : Type*} [DecidableEq κ]
    (K : Finset κ) (weight size : κ → ℝ) (ε : ℝ) :
    (∑ k ∈ K, weight k) - 2 * ε * ∑ k ∈ K, size k ≤
      ∑ k ∈ K, hpTrimmedThreshold (weight k) ε (size k) := by
  calc
    (∑ k ∈ K, weight k) - 2 * ε * ∑ k ∈ K, size k =
        ∑ k ∈ K, (weight k - 2 * ε * size k) := by
      rw [Finset.sum_sub_distrib, Finset.mul_sum]
    _ ≤ ∑ k ∈ K, hpTrimmedThreshold (weight k) ε (size k) :=
      Finset.sum_le_sum fun k _ =>
        hpTrimmedThreshold_lower (weight k) ε (size k)

/-- A raw typical degree with one `ε` loss dominates the twice-trimmed
threshold.  When the raw expression is negative, nonnegativity of the actual
degree handles the zero truncation. -/
lemma hpTrimmedThreshold_typical_degree
    (weight ε size degree : ℝ)
    (hε0 : 0 ≤ ε) (hsize : 0 ≤ size)
    (hdegree0 : 0 ≤ degree)
    (hdegree : weight - ε * size ≤ degree) :
    hpTrimmedThreshold weight ε size ≤ degree := by
  rw [hpTrimmedThreshold]
  by_cases h : 0 ≤ weight - 2 * ε * size
  · rw [max_eq_right h]
    nlinarith
  · rw [max_eq_left (le_of_not_ge h)]
    exact hdegree0

end Erdos550
