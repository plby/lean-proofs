import ErdosProblems.Erdos421.LogLocalComparison
import ErdosProblems.Erdos421.LogBoxOverlap
import ErdosProblems.Erdos421.IntegralOverlap

/-! # A mean-value bound for actual short logarithmic sums -/

namespace Erdos421

open MeasureTheory

noncomputable local instance logMomentCircleMeasure : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩

local instance logMomentCircleHaar : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance logMomentCircleProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem localLogSum_integrated_box {k M : ℕ} (hk : 0 < k) (hM : 0 < M)
    {t z : ℝ} (hz : 0 < z) (hscale : |t| * (M : ℝ) ^ (k + 1) ≤ z ^ (k + 1)) (p : ℕ) :
    volume.real (logFrequencyBox k t M z) * ‖localLogSum M t z‖ ^ p ≤
      ∫ a in logFrequencyBox k t M z, (3 : ℝ) ^ p * polynomialPrefixMoment k M p a := by
  have hconst : IntegrableOn (fun _ : UnitAddTorus (Fin k) ↦ ‖localLogSum M t z‖ ^ p)
      (logFrequencyBox k t M z) := (integrable_const _).integrableOn
  have hF : IntegrableOn (fun a ↦ (3 : ℝ) ^ p * polynomialPrefixMoment k M p a)
      (logFrequencyBox k t M z) :=
    ((integrable_polynomialPrefixMoment k M p).const_mul ((3 : ℝ) ^ p)).integrableOn
  have h := setIntegral_mono_on hconst hF (measurableSet_logFrequencyBox k t M z)
    (fun a ha ↦ localLogSum_box_bound hk hM hz hscale a ha p)
  simpa only [setIntegral_const, smul_eq_mul] using h

theorem sum_localLogSum_moments {k M : ℕ} (hk : 0 < k) (hM : 0 < M) (s N : ℕ)
    {t A : ℝ} (ht : t ≠ 0) (hA : 0 < A) (htA : |t| ≤ A ^ k)
    (hscale : |t| * (M : ℝ) ^ (k + 1) ≤ A ^ (k + 1)) :
    (∑ n ∈ Finset.range N, ‖localLogSum M t (A + n)‖ ^ (2 * s)) ≤
      (Real.pi * k) ^ k * k.factorial * (M : ℝ) ^ (k + meanValueTriangle k) *
        (1 + 2 * (A + N) ^ (k + 1) / ((k : ℝ) ^ 2 * |t| * (M : ℝ) ^ k)) *
          (3 : ℝ) ^ (2 * s) * (M + 1 : ℕ) * (vinogradovCount s k M : ℝ) := by
  classical
  let C : ℝ := (Real.pi * k) ^ k * k.factorial * (M : ℝ) ^ (k + meanValueTriangle k)
  let W : ℝ := 1 + 2 * (A + N) ^ (k + 1) / ((k : ℝ) ^ 2 * |t| * (M : ℝ) ^ k)
  let F : UnitAddTorus (Fin k) → ℝ := fun a ↦ (3 : ℝ) ^ (2 * s) *
    polynomialPrefixMoment k M (2 * s) a
  let E : ℕ → Set (UnitAddTorus (Fin k)) := fun n ↦ logFrequencyBox k t M (A + n)
  have hMR : (0 : ℝ) < M := Nat.cast_pos.mpr hM
  have hMone : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hkR : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have hf : (0 : ℝ) < k.factorial := Nat.cast_pos.mpr (Nat.factorial_pos k)
  have hC : 0 < C := by dsimp [C]; positivity
  have hW : 0 ≤ W := by dsimp [W]; positivity
  have hF : Integrable F := (integrable_polynomialPrefixMoment k M (2 * s)).const_mul _
  have hFnonneg (a : UnitAddTorus (Fin k)) : 0 ≤ F a :=
    mul_nonneg (by positivity) (polynomialPrefixMoment_nonneg k M (2 * s) a)
  have hcover (a : UnitAddTorus (Fin k)) :
      (((Finset.range N).filter (fun n ↦ a ∈ E n)).card : ℝ) ≤ W := by
    exact logFrequencyBoxes_overlap hk N ht hMR hA htA a
  have hlocal : ∀ n ∈ Finset.range N, (1 / C) * ‖localLogSum M t (A + n)‖ ^ (2 * s) ≤
      ∫ a in E n, F a := by
    intro n _
    have hz : 0 < A + (n : ℝ) := by positivity
    have hs : |t| * (M : ℝ) ^ (k + 1) ≤ (A + n) ^ (k + 1) :=
      hscale.trans (pow_le_pow_left₀ hA.le
        (le_add_of_nonneg_right (Nat.cast_nonneg n)) _)
    have h := localLogSum_integrated_box hk hM hz hs (2 * s)
    rw [logFrequencyBox_volume_real hk t (A + n) hMone] at h
    exact h
  have hsum := sum_le_of_local_integral_bound volume (Finset.range N) E F
    (fun n ↦ ‖localLogSum M t (A + n)‖ ^ (2 * s))
    (fun n _ ↦ measurableSet_logFrequencyBox k t M (A + n)) hF hFnonneg hcover hlocal
  have hFint : (∫ a, F a) ≤ (3 : ℝ) ^ (2 * s) *
      ((M + 1 : ℕ) * (vinogradovCount s k M : ℝ)) := by
    dsimp only [F]
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left (integral_polynomialPrefixMoment_le s k M) (by positivity)
  calc
    _ = C * ((1 / C) * ∑ n ∈ Finset.range N, ‖localLogSum M t (A + n)‖ ^ (2 * s)) := by
      field_simp
    _ ≤ C * (W * ∫ a, F a) := mul_le_mul_of_nonneg_left hsum hC.le
    _ ≤ C * (W * ((3 : ℝ) ^ (2 * s) * ((M + 1 : ℕ) * (vinogradovCount s k M : ℝ)))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hFint hW) hC.le
    _ = _ := by dsimp only [C, W]; ring

end Erdos421
