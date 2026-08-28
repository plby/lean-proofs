import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# A six-dimensional local Whitney pair model

Two three-dimensional sheets meet at two points. In the two distinguished
coordinates they are the line `t = 0` and the graph `t = h (1 - s²)`; the
remaining two pairs of coordinates are the separate sheet directions.
A nonnegative compact smooth cutoff is one along the interval between the
two intersection points on the first sheet.
-/

noncomputable section

open Set
open scoped ContDiff

namespace Wikipedia.SmoothSixDPoincare.WhitneyPairModel

abbrev Plane := EuclideanSpace ℝ (Fin 2)
abbrev Space := (ℝ × ℝ) × (Plane × Plane)
abbrev Sheet := ℝ × Plane

def firstSheet (p : Sheet) : Space := ((p.1, 0), (p.2, 0))

def secondSheet (h : ℝ) (p : Sheet) : Space := ((p.1, h * (1 - p.1 ^ 2)), (0, p.2))

def moveVector (h : ℝ) : Space := ((0, 2 * h), (0, 0))

def realBump : ContDiffBump (0 : ℝ) where
  rIn := 1
  rOut := 2
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

def planeBump : ContDiffBump (0 : Plane) where
  rIn := 1
  rOut := 2
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

def cutoff (q : Space) : ℝ :=
  (realBump q.1.1 * realBump q.1.2) * (planeBump q.2.1 * planeBump q.2.2)

theorem contDiff_cutoff : ContDiff ℝ ∞ cutoff :=
  ((realBump.contDiff.comp (contDiff_fst.comp contDiff_fst)).mul
    (realBump.contDiff.comp (contDiff_snd.comp contDiff_fst))).mul
      ((planeBump.contDiff.comp (contDiff_fst.comp contDiff_snd)).mul
        (planeBump.contDiff.comp (contDiff_snd.comp contDiff_snd)))

theorem cutoff_nonneg (q : Space) : 0 ≤ cutoff q :=
  mul_nonneg (mul_nonneg realBump.nonneg realBump.nonneg)
    (mul_nonneg planeBump.nonneg planeBump.nonneg)

theorem hasCompactSupport_cutoff : HasCompactSupport cutoff := by
  let K : Set Space := (tsupport realBump ×ˢ tsupport realBump) ×ˢ
    (tsupport planeBump ×ˢ tsupport planeBump)
  have hK : IsCompact K :=
    (realBump.hasCompactSupport.isCompact.prod realBump.hasCompactSupport.isCompact).prod
      (planeBump.hasCompactSupport.isCompact.prod planeBump.hasCompactSupport.isCompact)
  have hs : Function.support cutoff ⊆ K := by
    intro q hq
    change (realBump q.1.1 * realBump q.1.2) * (planeBump q.2.1 * planeBump q.2.2) ≠ 0 at hq
    obtain ⟨h₁, h₂⟩ := mul_ne_zero_iff.mp hq
    obtain ⟨h₁₁, h₁₂⟩ := mul_ne_zero_iff.mp h₁
    obtain ⟨h₂₁, h₂₂⟩ := mul_ne_zero_iff.mp h₂
    exact ⟨⟨subset_tsupport realBump h₁₁, subset_tsupport realBump h₁₂⟩,
      ⟨subset_tsupport planeBump h₂₁, subset_tsupport planeBump h₂₂⟩⟩
  exact hK.of_isClosed_subset isClosed_closure (closure_minimal hs hK.isClosed)

/-- The whole segment between the intersection points is in the exact cutoff plateau. -/
theorem cutoff_firstSheet_zero {s : ℝ} (hs : |s| ≤ 1) : cutoff (firstSheet (s, 0)) = 1 := by
  have hsB : realBump s = 1 := by
    apply realBump.one_of_mem_closedBall
    change dist s 0 ≤ 1
    simpa only [dist_zero_right, Real.norm_eq_abs] using hs
  have hr0 : realBump 0 = 1 :=
    realBump.one_of_mem_closedBall (Metric.mem_closedBall_self zero_le_one)
  have hp0 : planeBump 0 = 1 :=
    planeBump.one_of_mem_closedBall (Metric.mem_closedBall_self zero_le_one)
  change (realBump s * realBump 0) * (planeBump 0 * planeBump 0) = 1
  rw [hsB, hr0, hp0]
  norm_num

theorem norm_moveVector {h : ℝ} (hh : 0 ≤ h) : ‖moveVector h‖ = 2 * h := by
  simpa [moveVector, Prod.norm_def] using hh

/-- These are exactly the two intersections of the actual model sheet maps. -/
theorem firstSheet_eq_secondSheet_iff {h : ℝ} (hh : 0 < h) (p q : Sheet) :
    firstSheet p = secondSheet h q ↔
      p.1 = q.1 ∧ p.2 = 0 ∧ q.2 = 0 ∧ (q.1 = -1 ∨ q.1 = 1) := by
  rcases p with ⟨s, u⟩
  rcases q with ⟨t, v⟩
  constructor
  · intro heq
    have hst : s = t := congrArg (fun z : Space => z.1.1) heq
    have ht : 0 = h * (1 - t ^ 2) := congrArg (fun z : Space => z.1.2) heq
    have hu : u = 0 := congrArg (fun z : Space => z.2.1) heq
    have hv : v = 0 := (congrArg (fun z : Space => z.2.2) heq).symm
    have hsq : t ^ 2 = 1 := by
      have hz := (mul_eq_zero.mp ht.symm).resolve_left hh.ne'
      linarith
    have hprod : (t + 1) * (t - 1) = 0 := by nlinarith
    refine ⟨hst, hu, hv, ?_⟩
    rcases mul_eq_zero.mp hprod with hm | hp
    · left
      linarith
    · right
      linarith
  · rintro ⟨hst, hu, hv, ht⟩
    change s = t at hst
    change u = 0 at hu
    change v = 0 at hv
    subst s
    subst u
    subst v
    rcases ht with ht | ht
    · change t = -1 at ht
      subst t
      simp [firstSheet, secondSheet]
    · change t = 1 at ht
      subst t
      simp [firstSheet, secondSheet]

end Wikipedia.SmoothSixDPoincare.WhitneyPairModel
