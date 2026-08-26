import ErdosProblems.Erdos906.FinalExtraction
import ErdosProblems.Erdos906.FockGrowth
import ErdosProblems.Erdos906.HoleBound
import ErdosProblems.Erdos906.Summability

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open Filter MeasureTheory Metric Set
open scoped ENNReal Polynomial

namespace CofiniteDerivatives

noncomputable section

private theorem eventually_disk_saddle_ready (j : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      PointwiseSaddleReady n (diskNormLower j) (diskNormUpper j) := by
  have hlower : 0 < diskNormLower j := diskNormLower_pos j
  have hsqrt : Tendsto (fun n : ℕ => Real.sqrt n) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hsqrt.eventually_ge_atTop ((diskNormLower j)⁻¹),
    hsqrt.eventually_ge_atTop (diskNormUpper j)] with n hnLower hnUpper
  constructor
  · calc
      1 = diskNormLower j * (diskNormLower j)⁻¹ := by
        simp [ne_of_gt hlower]
      _ ≤ diskNormLower j * Real.sqrt n :=
        mul_le_mul_of_nonneg_left hnLower hlower.le
  · exact hnUpper

private theorem eventually_holeThreshold_ge_eight (j : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      8 ≤ holeThreshold n (diskCenter j) (diskRadius j / 2) := by
  let a := normCircleGap (diskCenter j) (diskRadius j / 2)
  have hr : 0 < diskRadius j / 2 := half_pos (diskRadius_pos j)
  have ha : 0 < a := normCircleGap_pos (diskCenter j) hr
  have hmain := eventually_half_mul_sqrt_le_threshold
    (a := a) (C0 := centerUpperConstant (diskCenter j)) ha
  have hsqrt : Tendsto (fun n : ℕ => (a / 2) * Real.sqrt n) atTop atTop :=
    (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop
      (half_pos ha)
  filter_upwards [hmain, hsqrt.eventually_ge_atTop 8] with n hn h8
  rw [holeThreshold]
  dsimp only [pointwiseSaddleLoss]
  nlinarith

private theorem randomFockDiskHole_subset (j n : ℕ) :
    randomFockDiskHole j n ⊆
      randomFockHoleEvent n (diskCenter j) (diskRadius j) := by
  intro ω hω z hz
  have hmiss : ¬(randomFockZeroSet ω n ∩ diskBasis j).Nonempty := by
    exact hω
  intro hzero
  apply hmiss
  exact ⟨z, hzero, by simpa [diskBasis] using! hz⟩

private theorem eventually_randomFockDiskHole_measure_le (j : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      P (randomFockDiskHole j n) ≤
        ENNReal.ofReal
          (2 * Real.exp
            (-(normCircleGap (diskCenter j) (diskRadius j / 2) * Real.sqrt n -
              Real.log n / 2 -
              (centerUpperConstant (diskCenter j) + 2)) / 8)) := by
  filter_upwards [eventually_disk_saddle_ready j,
    eventually_holeThreshold_ge_eight j,
    eventually_ne_atTop 0] with n hsaddle hthreshold hn
  have hr : 0 < diskRadius j / 2 := half_pos (diskRadius_pos j)
  have hrR : diskRadius j / 2 < diskRadius j := by
    linarith [diskRadius_pos j]
  have hnorm : ∀ z ∈ sphere (diskCenter j) (diskRadius j / 2),
      diskNormLower j ≤ ‖z‖ ∧ ‖z‖ ≤ diskNormUpper j :=
    fun z hz => norm_mem_sphere_half_bounds j hz
  have houter := P_outerMeasure_holeEvent_le_two_mul_exp_neg_eighth
    n (diskCenter j) hr hrR hsaddle hnorm hthreshold
  have hmeasure : P (randomFockDiskHole j n) ≤
      P.toOuterMeasure (randomFockHoleEvent n (diskCenter j) (diskRadius j)) := by
    exact P.toOuterMeasure.mono (randomFockDiskHole_subset j n)
  calc
    P (randomFockDiskHole j n) ≤
        P.toOuterMeasure (randomFockHoleEvent n (diskCenter j) (diskRadius j)) := hmeasure
    _ ≤ ENNReal.ofReal (2 * Real.exp
          (-holeThreshold n (diskCenter j) (diskRadius j / 2) / 8)) := houter
    _ = ENNReal.ofReal
          (2 * Real.exp
            (-(normCircleGap (diskCenter j) (diskRadius j / 2) * Real.sqrt n -
              Real.log n / 2 -
              (centerUpperConstant (diskCenter j) + 2)) / 8)) := by
      congr 2
      rw [holeThreshold]
      simp only [pointwiseSaddleLoss]
      ring_nf

/-- For each rational basis disk, the probabilities that a derivative misses the disk have finite
sum. This is the final probabilistic input to Borel--Cantelli. -/
theorem randomFockDiskHole_tsum_lt_top (j : ℕ) :
    (∑' n, P (randomFockDiskHole j n)) < ∞ := by
  let a := normCircleGap (diskCenter j) (diskRadius j / 2)
  let C0 := centerUpperConstant (diskCenter j) + 2
  have hr : 0 < diskRadius j / 2 := half_pos (diskRadius_pos j)
  have ha : 0 < a := normCircleGap_pos (diskCenter j) hr
  have hreal : Summable (fun n : ℕ =>
      2 * Real.exp (-(a * Real.sqrt n - Real.log n / 2 - C0) / 8)) :=
    (summable_exp_neg_sqrt_sub_log ha).mul_left 2
  have hbound : ∀ᶠ n : ℕ in atTop,
      P (randomFockDiskHole j n) ≤
        ENNReal.ofReal
          (2 * Real.exp (-(a * Real.sqrt n - Real.log n / 2 - C0) / 8)) := by
    simpa only [a, C0] using! eventually_randomFockDiskHole_measure_le j
  obtain ⟨N, hN⟩ := eventually_atTop.mp hbound
  let majorant : ℕ → ℝ := fun n =>
    if n < N then 1
    else 2 * Real.exp (-(a * Real.sqrt n - Real.log n / 2 - C0) / 8)
  have hmajorant : Summable majorant := by
    apply hreal.congr_atTop
    filter_upwards [eventually_ge_atTop N] with n hn
    simp [majorant, not_lt_of_ge hn]
  have hmajorant_nonneg : ∀ n, 0 ≤ majorant n := by
    intro n
    simp only [majorant]
    split_ifs
    · norm_num
    · positivity
  have hterm : ∀ n, P (randomFockDiskHole j n) ≤ ENNReal.ofReal (majorant n) := by
    intro n
    by_cases hn : n < N
    · simp only [majorant, if_pos hn, ENNReal.ofReal_one]
      exact (measure_mono (subset_univ _)).trans_eq measure_univ
    · simp only [majorant, if_neg hn]
      exact hN n (Nat.le_of_not_gt hn)
  exact (ENNReal.tsum_le_tsum hterm).trans_lt hmajorant.tsum_ofReal_lt_top

/-- There exists a nonpolynomial entire function whose sufficiently high derivatives have a zero
in every nonempty open subset of the complex plane. Equivalently, every strictly increasing
subsequence of derivative orders has zero sets with dense union. -/
theorem exists_transcendental_entire_with_cofinite_derivative_zeros :
    ∃ f : ℂ → ℂ,
      AnalyticOnNhd ℂ f Set.univ ∧
      (¬ ∃ p : ℂ[X], ∀ z : ℂ, p.eval z = f z) ∧
      DerivativesCofinitelyHit f ∧
      EveryDerivativeSubsequenceDense f := by
  obtain ⟨ω, hentire, hnonpoly, hcofinite, hdense⟩ :=
    exists_randomFock_final_of_summable_holes
      (fun j => randomFockDiskHole_tsum_lt_top j)
  exact ⟨randomFock ω, hentire, hnonpoly, hcofinite, hdense⟩

/-- The bounded Fock witness also has an explicit quadratic exponential majorant. -/
theorem exists_transcendental_entire_with_cofinite_derivative_zeros_and_growth :
    ∃ f : ℂ → ℂ,
      AnalyticOnNhd ℂ f Set.univ ∧
      (¬ ∃ p : ℂ[X], ∀ z : ℂ, p.eval z = f z) ∧
      DerivativesCofinitelyHit f ∧
      EveryDerivativeSubsequenceDense f ∧
      (∀ z : ℂ, ‖f z‖ ≤ Real.sqrt 2 * Real.exp (‖z‖ ^ 2)) := by
  obtain ⟨ω, hentire, hnonpoly, hcofinite, hdense⟩ :=
    exists_randomFock_final_of_summable_holes
      (fun j => randomFockDiskHole_tsum_lt_top j)
  exact ⟨randomFock ω, hentire, hnonpoly, hcofinite, hdense,
    fun z => norm_fockFunction_le_sqrt_two_mul_exp_sq
      (fun k => clipDisk (ω k)) (fun k => norm_clipDisk_le_one (ω k)) z⟩

/-- The final theorem with the growth bound and all project definitions expanded into the
quantifier order of the original statement. -/
theorem exists_transcendental_entire_with_explicit_derivative_zeros_and_growth :
    ∃ f : ℂ → ℂ,
      f ≠ 0 ∧
      AnalyticOnNhd ℂ f Set.univ ∧
      Differentiable ℂ f ∧
      (¬ ∃ p : ℂ[X], ∀ z : ℂ, p.eval z = f z) ∧
      (∀ z : ℂ, ‖f z‖ ≤ Real.sqrt 2 * Real.exp (‖z‖ ^ 2)) ∧
      (∀ U : Set ℂ, IsOpen U → U.Nonempty →
        ∃ N, ∀ n ≥ N, ∃ z ∈ U, iteratedDeriv n f z = 0) ∧
      (∀ s : ℕ → ℕ, StrictMono s →
        Dense {z : ℂ | ∃ k, iteratedDeriv (s k) f z = 0}) := by
  obtain ⟨f, hentire, hnonpoly, hcofinite, hdense, hgrowth⟩ :=
    exists_transcendental_entire_with_cofinite_derivative_zeros_and_growth
  have hnonzero : f ≠ 0 := by
    intro hf
    apply hnonpoly
    refine ⟨0, fun z => ?_⟩
    rw [hf]
    simp
  have hquantifiers := (derivativesCofinitelyHit_iff f).mp hcofinite
  have hsubsequences : ∀ s : ℕ → ℕ, StrictMono s →
      Dense {z : ℂ | ∃ k, iteratedDeriv (s k) f z = 0} := by
    intro s hs
    have hD : Dense (⋃ k, derivativeZeroSet f (s k)) := hdense s hs
    have heq : (⋃ k, derivativeZeroSet f (s k)) =
        {z : ℂ | ∃ k, iteratedDeriv (s k) f z = 0} := by
      ext z
      simp [derivativeZeroSet]
    rwa [heq] at hD
  have hdifferentiable : Differentiable ℂ f := by
    intro z
    exact (hentire z (Set.mem_univ z)).differentiableAt
  exact ⟨f, hnonzero, hentire, hdifferentiable,
    hnonpoly, hgrowth, hquantifiers, hsubsequences⟩

/-- Compatibility wrapper for the original fully expanded theorem statement. -/
theorem exists_transcendental_entire_with_explicit_derivative_zeros :
    ∃ f : ℂ → ℂ,
      f ≠ 0 ∧
      AnalyticOnNhd ℂ f Set.univ ∧
      Differentiable ℂ f ∧
      (¬ ∃ p : ℂ[X], ∀ z : ℂ, p.eval z = f z) ∧
      (∀ U : Set ℂ, IsOpen U → U.Nonempty →
        ∃ N, ∀ n ≥ N, ∃ z ∈ U, iteratedDeriv n f z = 0) ∧
      (∀ s : ℕ → ℕ, StrictMono s →
        Dense {z : ℂ | ∃ k, iteratedDeriv (s k) f z = 0}) := by
  obtain ⟨f, hnonzero, hentire, hdifferentiable, hnonpoly, _hgrowth,
      hquantifiers, hsubsequences⟩ :=
    exists_transcendental_entire_with_explicit_derivative_zeros_and_growth
  exact ⟨f, hnonzero, hentire, hdifferentiable, hnonpoly, hquantifiers, hsubsequences⟩

end

end CofiniteDerivatives
