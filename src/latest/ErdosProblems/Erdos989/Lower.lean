/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import ErdosProblems.Erdos989.Core

/-!
# A conditional reduction for the literal square-root lower target

This file develops the elementary cutoff and averaging reductions for the
literal square-root claim in the problem-page note.  The required Fourier
input is isolated in `FixedRadiusSpectralEscape`: its radius is the prescribed
radius `r`, not a radius averaged over an interval.

The cited Beck proof supplies an epsilon-loss energy estimate rather than
`FixedRadiusSpectralEscape`; consequently this file proves only the explicit
conditional implication at its end and does not declare the spectral input as
a theorem.

The point set is first cut off by a large disk.  On the concentric interior
disk every radius-`r` disk is contained in the cutoff, so the truncated and
untruncated discrepancies agree exactly.  A strict lower bound for the
mean-square truncated discrepancy then supplies a center with discrepancy at
least a fixed multiple of `sqrt r`.
-/

namespace Erdos989

open MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- Signed disk discrepancy.  Its absolute value is `diskError`. -/
def signedDiskError (A : Set Plane) (x : Plane) (r : ℝ) : ℝ :=
  (diskCount A x r : ℝ) - Real.pi * r ^ 2

@[simp]
theorem abs_signedDiskError (A : Set Plane) (x : Plane) (r : ℝ) :
    |signedDiskError A x r| = diskError A x r := by
  rfl

/-- Cut a point set off at distance `M` from the origin. -/
def truncate (A : Set Plane) (M : ℝ) : Set Plane :=
  A ∩ Metric.closedBall 0 M

/-- Signed discrepancy after cutting the point set off at distance `M`. -/
def truncatedSignedDiskError (A : Set Plane) (M : ℝ) (x : Plane) (r : ℝ) : ℝ :=
  signedDiskError (truncate A M) x r

/-- Centers whose radius-`r` disks lie inside the radius-`M` cutoff. -/
def interiorCenters (M r : ℝ) : Set Plane :=
  Metric.closedBall 0 (M - r)

/-- The cutoff contains only finitely many points of an admissible set. -/
theorem truncate_finite {A : Set Plane} (hA : IsAdmissible A) (M : ℝ) :
    (truncate A M).Finite := by
  simpa only [truncate] using hA.inter_closedBall_finite 0 M

/-- The finite point set in the cutoff, used to expand disk counts as finite
sums of measurable indicator functions. -/
def truncationFinset (A : Set Plane) (hA : IsAdmissible A) (M : ℝ) : Finset Plane :=
  (truncate_finite hA M).toFinset

@[simp]
theorem mem_truncationFinset {A : Set Plane} (hA : IsAdmissible A) (M : ℝ)
    (z : Plane) : z ∈ truncationFinset A hA M ↔ z ∈ truncate A M := by
  simp [truncationFinset]

/-- Real-valued count obtained from a finite point set by summing the
indicators of all disks that contain the center. -/
def finiteDiskCount (P : Finset Plane) (x : Plane) (r : ℝ) : ℝ :=
  ∑ z ∈ P, (Metric.closedBall z r).indicator (fun _ : Plane ↦ (1 : ℝ)) x

/-- The finite-sum count is measurable as a function of the center. -/
theorem measurable_finiteDiskCount (P : Finset Plane) (r : ℝ) :
    Measurable (fun x ↦ finiteDiskCount P x r) := by
  apply Finset.measurable_fun_sum
  intro z hz
  apply Measurable.indicator measurable_const
  exact measurableSet_closedBall

theorem finiteDiskCount_nonneg (P : Finset Plane) (x : Plane) (r : ℝ) :
    0 ≤ finiteDiskCount P x r := by
  apply Finset.sum_nonneg
  intro z hz
  simp only [Set.indicator, Metric.mem_closedBall]
  split <;> positivity

theorem finiteDiskCount_le_card (P : Finset Plane) (x : Plane) (r : ℝ) :
    finiteDiskCount P x r ≤ P.card := by
  have h := Finset.sum_le_card_nsmul P
    (fun z ↦ (Metric.closedBall z r).indicator (fun _ : Plane ↦ (1 : ℝ)) x)
    (1 : ℝ) (by
      intro z hz
      simp only [Set.indicator, Metric.mem_closedBall]
      split <;> norm_num)
  simpa [finiteDiskCount, nsmul_eq_mul] using h

/-- A finite point count is integrable on every finite-volume center set. -/
theorem integrableOn_finiteDiskCount (P : Finset Plane) {s : Set Plane}
    (hsvol : volume s ≠ ∞) (r : ℝ) :
    IntegrableOn (fun x ↦ finiteDiskCount P x r) s := by
  refine IntegrableOn.of_bound hsvol.lt_top
    (measurable_finiteDiskCount P r).aestronglyMeasurable (P.card : ℝ) ?_
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_nonneg (finiteDiskCount_nonneg P x r)]
  exact finiteDiskCount_le_card P x r

/-- Expanding a truncated disk count as a finite sum of disk indicators. -/
theorem finiteDiskCount_truncationFinset_eq {A : Set Plane} (hA : IsAdmissible A)
    (M r : ℝ) (x : Plane) :
    finiteDiskCount (truncationFinset A hA M) x r =
      (diskCount (truncate A M) x r : ℝ) := by
  classical
  let S : Set Plane := truncate A M ∩ Metric.closedBall x r
  have hS : S.Finite := (truncate_finite hA M).inter_of_left _
  have hfilter :
      (truncationFinset A hA M).filter (fun z ↦ z ∈ Metric.closedBall x r) =
        hS.toFinset := by
    ext z
    simp only [Finset.mem_filter, mem_truncationFinset, Set.Finite.mem_toFinset]
    rfl
  rw [finiteDiskCount, diskCount, Set.ncard_eq_toFinset_card S hS]
  rw [← hfilter, Finset.card_filter]
  simp only [Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  apply Finset.sum_congr rfl
  intro z hz
  simp only [Set.indicator, Metric.mem_closedBall]
  rw [dist_comm]

/-- A truncated signed discrepancy is measurable in its center. -/
theorem measurable_truncatedSignedDiskError {A : Set Plane} (hA : IsAdmissible A)
    (M r : ℝ) : Measurable (fun x ↦ truncatedSignedDiskError A M x r) := by
  have hcount := measurable_finiteDiskCount (truncationFinset A hA M) r
  rw [show (fun x ↦ truncatedSignedDiskError A M x r) =
      fun x ↦ finiteDiskCount (truncationFinset A hA M) x r - Real.pi * r ^ 2 by
    funext x
    rw [finiteDiskCount_truncationFinset_eq hA]
    rfl]
  fun_prop

/-- A truncated disk cannot contain more points than the whole cutoff. -/
theorem diskCount_truncate_le_ncard {A : Set Plane} (hA : IsAdmissible A)
    (M r : ℝ) (x : Plane) :
    diskCount (truncate A M) x r ≤ (truncate A M).ncard := by
  unfold diskCount
  exact Set.ncard_le_ncard inter_subset_left (truncate_finite hA M)

/-- The square of the truncated signed discrepancy is integrable on every
interior center disk.  Thus integrability is not part of the Fourier input. -/
theorem integrableOn_truncatedSignedDiskError_sq {A : Set Plane}
    (hA : IsAdmissible A) (M r : ℝ) :
    IntegrableOn (fun x ↦ truncatedSignedDiskError A M x r ^ 2)
      (interiorCenters M r) := by
  let C : ℝ := ((truncate A M).ncard : ℝ) + |Real.pi * r ^ 2|
  refine IntegrableOn.of_bound measure_closedBall_lt_top ?_ (C ^ 2) ?_
  · exact ((measurable_truncatedSignedDiskError hA M r).pow_const 2).aestronglyMeasurable
  · filter_upwards [] with x
    have hcountNat := diskCount_truncate_le_ncard hA M r x
    have hcount : (diskCount (truncate A M) x r : ℝ) ≤
        ((truncate A M).ncard : ℝ) := by
      exact_mod_cast hcountNat
    have hcount0 : 0 ≤ (diskCount (truncate A M) x r : ℝ) := by positivity
    have hC0 : 0 ≤ C := by
      dsimp [C]
      positivity
    have habs : |truncatedSignedDiskError A M x r| ≤ C := by
      dsimp [truncatedSignedDiskError, signedDiskError, C]
      calc
        |(diskCount (truncate A M) x r : ℝ) - Real.pi * r ^ 2| ≤
            |(diskCount (truncate A M) x r : ℝ)| + |Real.pi * r ^ 2| :=
              abs_sub _ _
        _ = (diskCount (truncate A M) x r : ℝ) + |Real.pi * r ^ 2| := by
              rw [abs_of_nonneg hcount0]
        _ ≤ ((truncate A M).ncard : ℝ) + |Real.pi * r ^ 2| :=
              add_le_add hcount le_rfl
    have hsquare : truncatedSignedDiskError A M x r ^ 2 ≤ C ^ 2 := by
      rw [sq_le_sq]
      simpa only [abs_of_nonneg hC0] using habs
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hsquare

/-- The average, over any finite-volume set of centers, of the number of
points from a finite set in a radius-`r` disk is at most the number of points
times the area of one disk.  This is the Tonelli/averaging estimate used in
Beck's low-density alternative. -/
theorem integral_finiteDiskCount_le (P : Finset Plane) {s : Set Plane}
    (hsvol : volume s ≠ ∞) {r : ℝ} (hr : 0 ≤ r) :
    (∫ x in s, finiteDiskCount P x r) ≤
      (P.card : ℝ) * (Real.pi * r ^ 2) := by
  change (∫ x in s,
    ∑ z ∈ P, (Metric.closedBall z r).indicator (fun _ : Plane ↦ (1 : ℝ)) x) ≤ _
  rw [integral_finsetSum P]
  · calc
      (∑ z ∈ P,
          ∫ x in s, (Metric.closedBall z r).indicator (fun _ : Plane ↦ (1 : ℝ)) x) =
          ∑ z ∈ P, volume.real (s ∩ Metric.closedBall z r) := by
            apply Finset.sum_congr rfl
            intro z hz
            rw [setIntegral_indicator measurableSet_closedBall]
            simp
      _ ≤ ∑ _z ∈ P, Real.pi * r ^ 2 := by
            apply Finset.sum_le_sum
            intro z hz
            calc
              volume.real (s ∩ Metric.closedBall z r) ≤
                  volume.real (Metric.closedBall z r) :=
                measureReal_mono inter_subset_right measure_closedBall_lt_top.ne
              _ = Real.pi * r ^ 2 := volume_closedBall_plane z hr
      _ = (P.card : ℝ) * (Real.pi * r ^ 2) := by simp
  · intro z hz
    exact (integrableOn_const hsvol).indicator measurableSet_closedBall

/-- Exact averaging when the center set contains every radius-`r` disk around
the points of `P`. -/
theorem integral_finiteDiskCount_eq_card_mul (P : Finset Plane) {s : Set Plane}
    (hsvol : volume s ≠ ∞) {r : ℝ} (hr : 0 ≤ r)
    (hsub : ∀ z ∈ P, Metric.closedBall z r ⊆ s) :
    (∫ x in s, finiteDiskCount P x r) =
      (P.card : ℝ) * (Real.pi * r ^ 2) := by
  change (∫ x in s,
    ∑ z ∈ P, (Metric.closedBall z r).indicator (fun _ : Plane ↦ (1 : ℝ)) x) = _
  rw [integral_finsetSum P]
  · calc
      (∑ z ∈ P,
          ∫ x in s, (Metric.closedBall z r).indicator (fun _ : Plane ↦ (1 : ℝ)) x) =
          ∑ z ∈ P, volume.real (Metric.closedBall z r) := by
            apply Finset.sum_congr rfl
            intro z hz
            rw [setIntegral_indicator measurableSet_closedBall,
              inter_eq_right.mpr (hsub z hz)]
            simp
      _ = ∑ _z ∈ P, Real.pi * r ^ 2 := by
            apply Finset.sum_congr rfl
            intro z hz
            exact volume_closedBall_plane z hr
      _ = (P.card : ℝ) * (Real.pi * r ^ 2) := by simp
  · intro z hz
    exact (integrableOn_const hsvol).indicator measurableSet_closedBall

/-- If the integral of a real function is below `B` times the volume, some
point of the center set has value below `B`. -/
theorem exists_mem_lt_of_integral_lt
    {s : Set Plane} (hs : MeasurableSet s) (hsvol : volume s ≠ ∞)
    {f : Plane → ℝ} (hf : IntegrableOn f s) {B : ℝ}
    (havg : (∫ x in s, f x) < volume.real s * B) :
    ∃ x ∈ s, f x < B := by
  by_contra h
  push Not at h
  have hlower : B * volume.real s ≤ ∫ x in s, f x :=
    setIntegral_ge_of_const_le_real hs hsvol (fun x hx ↦ h x hx) hf
  rw [mul_comm] at hlower
  exact (not_lt_of_ge hlower) havg

/-- The dual mean-value principle for an integral above a constant average. -/
theorem exists_mem_gt_of_integral_gt
    {s : Set Plane} (hs : MeasurableSet s) (hsvol : volume s ≠ ∞)
    {f : Plane → ℝ} (hf : IntegrableOn f s) {B : ℝ}
    (havg : volume.real s * B < ∫ x in s, f x) :
    ∃ x ∈ s, B < f x := by
  by_contra h
  push Not at h
  have hupper : (∫ x in s, f x) ≤ ∫ _x in s, B :=
    setIntegral_mono_on hf (integrableOn_const hsvol) hs (fun x hx ↦ h x hx)
  have hconst : (∫ _x : Plane in s, B) = volume.real s * B := by simp
  rw [hconst] at hupper
  exact (not_lt_of_ge hupper) havg

/-- A radius-`r` disk centered in the radius-`M-r` disk lies in the
radius-`M` disk. -/
theorem closedBall_subset_cutoff {M r : ℝ} (_hr : 0 ≤ r) {x : Plane}
    (hx : x ∈ interiorCenters M r) :
    Metric.closedBall x r ⊆ Metric.closedBall (0 : Plane) M := by
  intro y hy
  change x ∈ Metric.closedBall (0 : Plane) (M - r) at hx
  rw [Metric.mem_closedBall] at hx hy ⊢
  rw [dist_zero_right] at hx ⊢
  calc
    ‖y‖ = dist y 0 := by rw [dist_zero_right]
    _ ≤ dist y x + ‖x‖ := by simpa [dist_zero_right] using dist_triangle y x 0
    _ ≤ r + (M - r) := add_le_add hy hx
    _ = M := by ring

/-- On interior centers, truncation does not change the disk count. -/
theorem diskCount_truncate_eq {A : Set Plane} {M r : ℝ} (hr : 0 ≤ r)
    {x : Plane} (hx : x ∈ interiorCenters M r) :
    diskCount (truncate A M) x r = diskCount A x r := by
  have hsub := closedBall_subset_cutoff hr hx
  unfold diskCount
  congr 1
  ext y
  simp only [truncate, mem_inter_iff]
  constructor
  · rintro ⟨⟨hyA, -⟩, hyball⟩
    exact ⟨hyA, hyball⟩
  · rintro ⟨hyA, hyball⟩
    exact ⟨⟨hyA, hsub hyball⟩, hyball⟩

/-- On interior centers, truncation does not change the signed discrepancy. -/
theorem truncatedSignedDiskError_eq {A : Set Plane} {M r : ℝ} (hr : 0 ≤ r)
    {x : Plane} (hx : x ∈ interiorCenters M r) :
    truncatedSignedDiskError A M x r = signedDiskError A x r := by
  simp only [truncatedSignedDiskError, signedDiskError, diskCount_truncate_eq hr hx]

/-- Beck's low-density alternative.  If the cutoff has fewer than half as
many points as the volume of the admissible center disk, averaging produces a
radius-`r` disk with discrepancy greater than half its area. -/
theorem exists_large_diskError_of_sparse_cutoff {A : Set Plane}
    (hA : IsAdmissible A) {M r : ℝ} (hr : 0 < r)
    (hsparse : 2 * ((truncate A M).ncard : ℝ) <
      volume.real (interiorCenters M r)) :
    ∃ x ∈ interiorCenters M r,
      Real.pi * r ^ 2 / 2 < diskError A x r := by
  let P := truncationFinset A hA M
  let s := interiorCenters M r
  have hsmeas : MeasurableSet s := measurableSet_closedBall
  have hsvol : volume s ≠ ∞ := measure_closedBall_lt_top.ne
  have harea : 0 < Real.pi * r ^ 2 := mul_pos Real.pi_pos (sq_pos_of_pos hr)
  have hcardNat : P.card = (truncate A M).ncard := by
    dsimp [P, truncationFinset]
    exact (Set.ncard_eq_toFinset_card (truncate A M) (truncate_finite hA M)).symm
  have hcard : (P.card : ℝ) = ((truncate A M).ncard : ℝ) := by
    exact_mod_cast hcardNat
  have havg_le : (∫ x in s, finiteDiskCount P x r) ≤
      (P.card : ℝ) * (Real.pi * r ^ 2) :=
    integral_finiteDiskCount_le P hsvol hr.le
  have havg_lt : (∫ x in s, finiteDiskCount P x r) <
      volume.real s * (Real.pi * r ^ 2 / 2) := by
    apply havg_le.trans_lt
    rw [hcard]
    nlinarith
  rcases exists_mem_lt_of_integral_lt hsmeas hsvol
      (integrableOn_finiteDiskCount P hsvol r) havg_lt with ⟨x, hx, hxcount⟩
  refine ⟨x, hx, ?_⟩
  have hfiniteCount : finiteDiskCount P x r =
      (diskCount (truncate A M) x r : ℝ) :=
    finiteDiskCount_truncationFinset_eq hA M r x
  rw [hfiniteCount] at hxcount
  have hfull := diskCount_truncate_eq (A := A) hr.le hx
  rw [hfull] at hxcount
  rw [diskError, abs_of_nonpos]
  · nlinarith
  · exact sub_nonpos.mpr (hxcount.le.trans (by linarith))

/-- A convenient numerical form of the density alternative.  When `M ≥ 4r`,
the radius-`M-r` center disk has enough volume that fewer than
`π M² / 8` cutoff points imply the hypothesis of
`exists_large_diskError_of_sparse_cutoff`. -/
theorem exists_large_diskError_of_very_sparse_cutoff {A : Set Plane}
    (hA : IsAdmissible A) {M r : ℝ} (hr : 0 < r) (hM : 4 * r ≤ M)
    (hcount : 8 * ((truncate A M).ncard : ℝ) < Real.pi * M ^ 2) :
    ∃ x ∈ interiorCenters M r,
      Real.pi * r ^ 2 / 2 < diskError A x r := by
  apply exists_large_diskError_of_sparse_cutoff hA hr
  have hM0 : 0 < M := by nlinarith
  have hthree0 : 0 ≤ 3 * M / 4 := by positivity
  have hinner0 : 0 ≤ M - r := by nlinarith
  have hthree : 3 * M / 4 ≤ M - r := by nlinarith
  have hsquare : (3 * M / 4) ^ 2 ≤ (M - r) ^ 2 := by
    nlinarith [mul_self_le_mul_self hthree0 hthree]
  have hquarter : M ^ 2 / 4 < (M - r) ^ 2 := by
    nlinarith [sq_pos_of_pos hM0]
  have hpi : Real.pi * (M ^ 2 / 4) < Real.pi * (M - r) ^ 2 :=
    mul_lt_mul_of_pos_left hquarter Real.pi_pos
  rw [interiorCenters, volume_closedBall_plane 0 hinner0]
  nlinarith

/-- The radius-`r` disk of centers around a point of the radius-`M` cutoff is
contained in the expanded radius-`M+r` center disk. -/
theorem closedBall_subset_expandedCutoff {M r : ℝ} {z : Plane}
    (hz : z ∈ Metric.closedBall (0 : Plane) M) :
    Metric.closedBall z r ⊆ Metric.closedBall (0 : Plane) (M + r) := by
  intro x hx
  rw [Metric.mem_closedBall] at hz hx ⊢
  rw [dist_zero_right] at hz ⊢
  calc
    ‖x‖ = dist x 0 := by rw [dist_zero_right]
    _ ≤ dist x z + ‖z‖ := by simpa [dist_zero_right] using dist_triangle x z 0
    _ ≤ r + M := add_le_add hx hz
    _ = M + r := add_comm _ _

/-- The high-density counterpart of the sparse-cutoff alternative.  If the
cutoff has more than twice as many points as the volume of the expanded
center disk, some prescribed-radius disk has discrepancy greater than its
whole area. -/
theorem exists_large_diskError_of_dense_cutoff {A : Set Plane}
    (hA : IsAdmissible A) {M r : ℝ} (hr : 0 < r)
    (hdense : 2 * volume.real (Metric.closedBall (0 : Plane) (M + r)) <
      ((truncate A M).ncard : ℝ)) :
    ∃ x ∈ Metric.closedBall (0 : Plane) (M + r),
      Real.pi * r ^ 2 < diskError A x r := by
  let P := truncationFinset A hA M
  let s : Set Plane := Metric.closedBall 0 (M + r)
  have hsmeas : MeasurableSet s := measurableSet_closedBall
  have hsvol : volume s ≠ ∞ := measure_closedBall_lt_top.ne
  have harea : 0 < Real.pi * r ^ 2 := mul_pos Real.pi_pos (sq_pos_of_pos hr)
  have hcardNat : P.card = (truncate A M).ncard := by
    dsimp [P, truncationFinset]
    exact (Set.ncard_eq_toFinset_card (truncate A M) (truncate_finite hA M)).symm
  have hcard : (P.card : ℝ) = ((truncate A M).ncard : ℝ) := by
    exact_mod_cast hcardNat
  have hsub : ∀ z ∈ P, Metric.closedBall z r ⊆ s := by
    intro z hz
    have hz' : z ∈ truncate A M := (mem_truncationFinset hA M z).mp hz
    exact closedBall_subset_expandedCutoff hz'.2
  have havgEq : (∫ x in s, finiteDiskCount P x r) =
      (P.card : ℝ) * (Real.pi * r ^ 2) :=
    integral_finiteDiskCount_eq_card_mul P hsvol hr.le hsub
  have havgGt : volume.real s * (2 * (Real.pi * r ^ 2)) <
      ∫ x in s, finiteDiskCount P x r := by
    rw [havgEq, hcard]
    nlinarith
  rcases exists_mem_gt_of_integral_gt hsmeas hsvol
      (integrableOn_finiteDiskCount P hsvol r) havgGt with ⟨x, hx, hxcount⟩
  refine ⟨x, hx, ?_⟩
  have hfiniteCount : finiteDiskCount P x r =
      (diskCount (truncate A M) x r : ℝ) :=
    finiteDiskCount_truncationFinset_eq hA M r x
  rw [hfiniteCount] at hxcount
  have hcountNat : diskCount (truncate A M) x r ≤ diskCount A x r := by
    unfold diskCount
    apply Set.ncard_le_ncard
    · intro z hz
      exact ⟨hz.1.1, hz.2⟩
    · exact hA.inter_closedBall_finite x r
  have hcount : (diskCount (truncate A M) x r : ℝ) ≤ (diskCount A x r : ℝ) := by
    exact_mod_cast hcountNat
  have hfull : 2 * (Real.pi * r ^ 2) < (diskCount A x r : ℝ) :=
    hxcount.trans_le hcount
  rw [diskError, abs_of_nonneg]
  · nlinarith
  · exact sub_nonneg.mpr (by nlinarith)

/-- A simple numerical sufficient condition for the high-density alternative.
For `r ≤ M`, the expanded center disk has volume at most `4πM²`. -/
theorem exists_large_diskError_of_very_dense_cutoff {A : Set Plane}
    (hA : IsAdmissible A) {M r : ℝ} (hr : 0 < r) (hM : r ≤ M)
    (hcount : 8 * Real.pi * M ^ 2 < ((truncate A M).ncard : ℝ)) :
    ∃ x ∈ Metric.closedBall (0 : Plane) (M + r),
      Real.pi * r ^ 2 < diskError A x r := by
  apply exists_large_diskError_of_dense_cutoff hA hr
  have hM0 : 0 ≤ M := hr.le.trans hM
  have hsum0 : 0 ≤ M + r := add_nonneg hM0 hr.le
  have hsum : M + r ≤ 2 * M := by linarith
  have hsquare : (M + r) ^ 2 ≤ (2 * M) ^ 2 := by
    nlinarith [mul_self_le_mul_self hsum0 hsum]
  rw [volume_closedBall_plane 0 hsum0]
  have hpi : Real.pi * (M + r) ^ 2 ≤ Real.pi * (2 * M) ^ 2 :=
    mul_le_mul_of_nonneg_left hsquare Real.pi_nonneg
  nlinarith

/-- A strict mean-square lower bound forces a pointwise lower bound.

This is the final averaging step in the lower-bound proof.  It is deliberately
stated for an arbitrary finite-measure measurable set and an arbitrary real
function, so no Fourier-analysis details are hidden in it. -/
theorem exists_mem_abs_ge_of_integral_sq_gt
    {s : Set Plane} (hs : MeasurableSet s) (hvol : volume s ≠ ∞)
    {e : Plane → ℝ} (he : IntegrableOn (fun x ↦ e x ^ 2) s)
    {B : ℝ} (hB : 0 ≤ B)
    (henergy : volume.real s * B ^ 2 < ∫ x in s, e x ^ 2) :
    ∃ x ∈ s, B ≤ |e x| := by
  by_contra h
  push Not at h
  have hpoint : ∀ x ∈ s, e x ^ 2 ≤ B ^ 2 := by
    intro x hx
    have habs := h x hx
    nlinarith [sq_nonneg (e x), abs_nonneg (e x), sq_abs (e x)]
  have hle : (∫ x in s, e x ^ 2) ≤ ∫ _x in s, B ^ 2 :=
    setIntegral_mono_on he (integrableOn_const hvol) hs hpoint
  have hconst : (∫ _x : Plane in s, B ^ 2) = volume.real s * B ^ 2 := by
    simp [mul_comm]
  rw [hconst] at hle
  exact (not_lt_of_ge hle) henergy

/-- The exact fixed-radius spectral statement that would imply the literal
square-root target from the problem-page note.

The quantified `r` is used unchanged in the integrand and in the lower bound;
there is no existentially chosen or averaged radius.  The analytic work is to
prove this proposition.  Beck's verified estimate loses an auxiliary factor
and therefore does not establish this stronger proposition. -/
def FixedRadiusSpectralEscape : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ R : ℝ, ∀ A : Set Plane, IsAdmissible A →
    ∀ r : ℝ, R ≤ r → 0 ≤ r →
      ∃ M : ℝ,
        4 * r ≤ M ∧
        (Real.pi * M ^ 2 ≤ 8 * ((truncate A M).ncard : ℝ) ∧
          ((truncate A M).ncard : ℝ) ≤ 8 * Real.pi * M ^ 2 →
          volume.real (interiorCenters M r) * (c * Real.sqrt r) ^ 2 <
            ∫ x in interiorCenters M r, truncatedSignedDiskError A M x r ^ 2)

/-- The stronger fixed-radius spectral escape proposition implies the
universal square-root lower bound stated on the problem page. -/
theorem universalSqrtLowerBound_of_fixedRadiusSpectralEscape
    (hescape : FixedRadiusSpectralEscape) : HasUniversalSqrtLowerBound := by
  rcases hescape with ⟨c, hc, R, hescape⟩
  let c₀ := min c 1
  have hc₀ : 0 < c₀ := lt_min hc zero_lt_one
  refine ⟨c₀, hc₀, max R 1, ?_⟩
  intro A hA r hr
  have hR : R ≤ r := (le_max_left R 1).trans hr
  have hr1 : 1 ≤ r := (le_max_right R 1).trans hr
  have hr0 : 0 ≤ r := zero_le_one.trans hr1
  rcases hescape A hA r hR hr0 with ⟨M, hM, hescapeDense⟩
  have hc₀le : c₀ ≤ 1 := min_le_right c 1
  have hsqrt : Real.sqrt r ≤ r := Real.sqrt_le_self_iff.mpr (Or.inr hr1)
  have hrr : r ≤ r ^ 2 := by
    have := mul_nonneg hr0 (sub_nonneg.mpr hr1)
    nlinarith
  have hsmallTarget : c₀ * Real.sqrt r ≤ Real.pi * r ^ 2 / 2 := by
    calc
      c₀ * Real.sqrt r ≤ 1 * Real.sqrt r :=
        mul_le_mul_of_nonneg_right hc₀le (Real.sqrt_nonneg r)
      _ ≤ r := by simpa using hsqrt
      _ ≤ Real.pi * r ^ 2 / 2 := by nlinarith [Real.pi_gt_three]
  by_cases hsparse : 8 * ((truncate A M).ncard : ℝ) < Real.pi * M ^ 2
  · rcases exists_large_diskError_of_very_sparse_cutoff hA
      (zero_lt_one.trans_le hr1) hM hsparse with
      ⟨x, hx, hhuge⟩
    refine ⟨x, ?_⟩
    exact hsmallTarget.trans hhuge.le
  have hdense : Real.pi * M ^ 2 ≤ 8 * ((truncate A M).ncard : ℝ) :=
    le_of_not_gt hsparse
  by_cases hveryDense : 8 * Real.pi * M ^ 2 < ((truncate A M).ncard : ℝ)
  · have hrM : r ≤ M := by nlinarith
    rcases exists_large_diskError_of_very_dense_cutoff hA
        (zero_lt_one.trans_le hr1) hrM hveryDense with ⟨x, hx, hhuge⟩
    refine ⟨x, ?_⟩
    have hhalf : Real.pi * r ^ 2 / 2 ≤ Real.pi * r ^ 2 := by
      have : 0 ≤ Real.pi * r ^ 2 := mul_nonneg Real.pi_nonneg (sq_nonneg r)
      linarith
    exact hsmallTarget.trans (hhalf.trans hhuge.le)
  have hupper : ((truncate A M).ncard : ℝ) ≤ 8 * Real.pi * M ^ 2 :=
    le_of_not_gt hveryDense
  have henergy := hescapeDense ⟨hdense, hupper⟩
  have hmeas : MeasurableSet (interiorCenters M r) := measurableSet_closedBall
  have hvol : volume (interiorCenters M r) ≠ ∞ := measure_closedBall_lt_top.ne
  have hint := integrableOn_truncatedSignedDiskError_sq hA M r
  have htarget : 0 ≤ c * Real.sqrt r :=
    mul_nonneg hc.le (Real.sqrt_nonneg r)
  rcases exists_mem_abs_ge_of_integral_sq_gt hmeas hvol hint htarget henergy with
    ⟨x, hx, hbound⟩
  refine ⟨x, ?_⟩
  rw [truncatedSignedDiskError_eq hr0 hx, abs_signedDiskError] at hbound
  exact (mul_le_mul_of_nonneg_right (min_le_left c 1) (Real.sqrt_nonneg r)).trans hbound

end

end Erdos989
