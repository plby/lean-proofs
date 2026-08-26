import ErdosProblems.Erdos67b.MRRamarePerronProjection
import ErdosProblems.Erdos67b.Section4ConcreteWeightWindow
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Quantitative decay of the Mellin--Perron projection error

At Mellin real part one, a one-bounded coefficient has size at most `1/n`.
The near-diagonal Perron kernel is therefore bounded by a reciprocal-distance
sum, while the absolute coefficient mass on the translated line is bounded
by the positive real zeta series.  This file makes both bounds finite and
explicit for the two endpoints `X` and `2X`.
-/

open scoped BigOperators ComplexConjugate
open Finset

namespace Erdos67b.MRPerronProjectionErrorBound

noncomputable section

open BoundedGaps.Maynard
open EulerResidue ShiftedResidueSeries

/-- Reciprocal distance from a natural endpoint, with the endpoint itself
removed. -/
def perronReciprocalDistance (x n : ℕ) : ℝ :=
  if n = x then 0 else |(x : ℝ) - n|⁻¹

theorem perronReciprocalDistance_nonneg (x n : ℕ) :
    0 ≤ perronReciprocalDistance x n := by
  unfold perronReciprocalDistance
  split <;> positivity

/-- The reciprocal distances in the whole Perron central range have at
most two copies of the harmonic sum. -/
theorem sum_range_two_mul_perronReciprocalDistance_le
    (x : ℕ) (hx : 0 < x) :
    (∑ n ∈ Finset.range (2 * x), perronReciprocalDistance x n) ≤
      2 * (harmonic x : ℝ) := by
  have hleft :
      (∑ n ∈ Finset.range x, perronReciprocalDistance x n) =
        (harmonic x : ℝ) := by
    calc
      (∑ n ∈ Finset.range x, perronReciprocalDistance x n) =
          ∑ n ∈ Finset.Ico 0 x, (((x - n : ℕ) : ℝ))⁻¹ := by
        rw [Finset.range_eq_Ico]
        apply Finset.sum_congr rfl
        intro n hn
        have hnx : n < x := (Finset.mem_Ico.mp hn).2
        have hnex : n ≠ x := ne_of_lt hnx
        rw [perronReciprocalDistance, if_neg hnex]
        have hcast : (x : ℝ) - n = ((x - n : ℕ) : ℝ) := by
          rw [Nat.cast_sub hnx.le]
        rw [hcast, abs_of_nonneg (Nat.cast_nonneg _)]
      _ = ∑ n ∈ Finset.Icc 1 x, ((n : ℝ))⁻¹ := by
        have hreflect :=
          Finset.sum_Ico_reflect (fun n : ℕ ↦ ((n : ℝ))⁻¹)
            0 (m := x) (n := x) (Nat.le_succ x)
        simp only [Nat.add_sub_cancel_left, Nat.sub_zero] at hreflect
        rw [Finset.Ico_add_one_right_eq_Icc] at hreflect
        exact hreflect
      _ = (harmonic x : ℝ) := by
        simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv,
          Rat.cast_natCast]
  have hright :
      (∑ n ∈ Finset.range x, perronReciprocalDistance x (x + n)) ≤
        (harmonic x : ℝ) := by
    rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem
      (Finset.mem_range.mpr hx)]
    have hdiff : Finset.range x \ {0} = Finset.Ico 1 x := by
      ext n
      simp only [Finset.mem_sdiff, Finset.mem_range, Finset.mem_singleton,
        Finset.mem_Ico]
      omega
    rw [hdiff]
    have hzero : perronReciprocalDistance x (x + 0) = 0 := by
      simp [perronReciprocalDistance]
    rw [hzero, zero_add]
    calc
      (∑ n ∈ Finset.Ico 1 x, perronReciprocalDistance x (x + n)) =
          ∑ n ∈ Finset.Ico 1 x, ((n : ℝ))⁻¹ := by
        apply Finset.sum_congr rfl
        intro n hn
        have hnpos : 0 < n := (Finset.mem_Ico.mp hn).1
        rw [perronReciprocalDistance, if_neg (by omega)]
        have habs : |(x : ℝ) - (x + n : ℕ)| = (n : ℝ) := by
          push_cast
          rw [show (x : ℝ) - ((x : ℝ) + n) = -(n : ℝ) by ring,
            abs_neg, abs_of_nonneg (Nat.cast_nonneg n)]
        rw [habs]
      _ ≤ ∑ n ∈ Finset.Icc 1 x, ((n : ℝ))⁻¹ := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro n hn
          simp only [Finset.mem_Ico, Finset.mem_Icc] at hn ⊢
          exact ⟨hn.1, hn.2.le⟩
        · intro n hn hnot
          positivity
      _ = (harmonic x : ℝ) := by
        simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv,
          Rat.cast_natCast]
  have hsplit :
      (∑ n ∈ Finset.range (2 * x), perronReciprocalDistance x n) =
        (∑ n ∈ Finset.range x, perronReciprocalDistance x n) +
          ∑ n ∈ Finset.range x,
            perronReciprocalDistance x (x + n) := by
    rw [show 2 * x = x + x by omega, Finset.sum_range_add]
  rw [hsplit, hleft]
  linarith

/-- Pointwise reciprocal-distance domination of the near-diagonal summand
for a one-bounded coefficient at Mellin real part one. -/
theorem mellin_one_near_summand_le
    {a : ℕ → ℂ} (ha : ∀ n, 0 < n → ‖a n‖ ≤ 1)
    {x n : ℕ} (hx : 0 < x) {t U : ℝ} (hU : 0 < U) :
    ‖mrMellinShiftedCoefficient a 1 t n‖ *
        dirichletPerronNearError x U n ≤
      (4 / U) * perronReciprocalDistance x n := by
  rw [dirichletPerronNearError]
  split_ifs with hcentral
  · rcases hcentral with ⟨hn, hlower, hupper, hnex⟩
    have hxR : (0 : ℝ) < x := by exact_mod_cast hx
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hdist : (0 : ℝ) < |(x : ℝ) - n| := by
      apply abs_pos.mpr
      rw [sub_ne_zero]
      exact_mod_cast hnex.symm
    have hnorm : ‖mrMellinShiftedCoefficient a 1 t n‖ ≤ (n : ℝ)⁻¹ := by
      rw [norm_mrMellinShiftedCoefficient_eq a 1 t hn, Real.rpow_one]
      simpa [div_eq_mul_inv] using
        mul_le_mul_of_nonneg_right (ha n hn) (inv_nonneg.mpr hnR.le)
    have hnear0 : 0 ≤ min 1
        (2 * (x : ℝ) / (U * |(x : ℝ) - n|)) := by
      exact le_min (by norm_num) (by positivity)
    have hnear : min 1
        (2 * (x : ℝ) / (U * |(x : ℝ) - n|)) ≤
        2 * (x : ℝ) / (U * |(x : ℝ) - n|) := min_le_right _ _
    have hxn : (x : ℝ) / n < 2 := by
      rw [div_lt_iff₀ hnR]
      nlinarith
    calc
      ‖mrMellinShiftedCoefficient a 1 t n‖ *
          min 1 (2 * (x : ℝ) / (U * |(x : ℝ) - n|)) ≤
          (n : ℝ)⁻¹ *
            min 1 (2 * (x : ℝ) / (U * |(x : ℝ) - n|)) :=
        mul_le_mul_of_nonneg_right hnorm hnear0
      _ ≤ (n : ℝ)⁻¹ *
            (2 * (x : ℝ) / (U * |(x : ℝ) - n|)) :=
        mul_le_mul_of_nonneg_left hnear (inv_nonneg.mpr hnR.le)
      _ ≤ (4 / U) * |(x : ℝ) - n|⁻¹ := by
        have hden : 0 < U * |(x : ℝ) - n| := mul_pos hU hdist
        rw [inv_eq_one_div]
        field_simp [ne_of_gt hnR, ne_of_gt hU, ne_of_gt hdist]
        nlinarith
      _ = (4 / U) * perronReciprocalDistance x n := by
        rw [perronReciprocalDistance, if_neg hnex]
  · have h4U : 0 ≤ (4 : ℝ) / U := div_nonneg (by norm_num) hU.le
    rw [mul_zero]
    exact mul_nonneg h4U (perronReciprocalDistance_nonneg x n)

/-- The complete near-diagonal Perron mass is `O(H_x/U)`, uniformly in the
outer vertical parameter. -/
theorem dirichletPerronNearMass_mellin_one_le_harmonic
    {a : ℕ → ℂ} (ha : ∀ n, 0 < n → ‖a n‖ ≤ 1)
    {x : ℕ} (hx : 0 < x) (t : ℝ) {U : ℝ} (hU : 0 < U) :
    dirichletPerronNearMass (mrMellinShiftedCoefficient a 1 t) x U ≤
      8 * (harmonic x : ℝ) / U := by
  unfold dirichletPerronNearMass
  rw [tsum_eq_sum (s := Finset.range (2 * x))]
  · calc
      (∑ n ∈ Finset.range (2 * x),
          ‖mrMellinShiftedCoefficient a 1 t n‖ *
            dirichletPerronNearError x U n) ≤
          ∑ n ∈ Finset.range (2 * x),
            (4 / U) * perronReciprocalDistance x n := by
        apply Finset.sum_le_sum
        intro n hn
        exact mellin_one_near_summand_le ha hx hU
      _ = (4 / U) *
          ∑ n ∈ Finset.range (2 * x), perronReciprocalDistance x n := by
        rw [Finset.mul_sum]
      _ ≤ (4 / U) * (2 * (harmonic x : ℝ)) := by
        apply mul_le_mul_of_nonneg_left
          (sum_range_two_mul_perronReciprocalDistance_le x hx)
        exact div_nonneg (by norm_num) hU.le
      _ = 8 * (harmonic x : ℝ) / U := by ring
  · intro n hn
    have hnLower : 2 * x ≤ n := by simpa using hn
    have hnLowerR : (2 : ℝ) * x ≤ n := by exact_mod_cast hnLower
    rw [dirichletPerronNearError, if_neg]
    · simp
    · intro h
      exact (not_lt_of_ge hnLowerR) h.2.2.1

/-- On the translated line `delta = taoExponent Y - 1`, the absolute
coefficient mass of a Mellin-one one-bounded coefficient is at most the
elementary zeta envelope `1 + log Y`. -/
theorem dirichletPerronCoefficientMass_mellin_one_tao_le
    {a : ℕ → ℂ} (ha : ∀ n, 0 < n → ‖a n‖ ≤ 1)
    {Y : ℕ} (hY : 1 < Y) (t : ℝ) :
    dirichletPerronCoefficientMass
        (mrMellinShiftedCoefficient a 1 t)
        (taoExponent Y - 1) ≤
      1 + Real.log (Y : ℝ) := by
  let delta : ℝ := taoExponent Y - 1
  have hdelta : 0 < delta := by
    dsimp only [delta]
    linarith [one_lt_taoExponent hY]
  have ha' : ∀ n ≠ 0, ‖a n‖ ≤ 1 := by
    intro n hn
    exact ha n (Nat.pos_of_ne_zero hn)
  have hleft : Summable (fun n : ℕ ↦
      ‖LSeries.term (mrMellinShiftedCoefficient a 1 t) (delta : ℂ) n‖) := by
    simpa using (mrMellinShiftedCoefficient_one_LSeriesSummable
      (a := a) ha' (t := t) (u := 0) hdelta).norm
  have hright : Summable (realDirichletWeight (taoExponent Y)) :=
    summable_realDirichletWeight (one_lt_taoExponent hY)
  have hpoint : ∀ n : ℕ,
      ‖LSeries.term (mrMellinShiftedCoefficient a 1 t) (delta : ℂ) n‖ ≤
        realDirichletWeight (taoExponent Y) n := by
    intro n
    have hterm := congrArg norm
      (LSeries_term_mrMellinShiftedCoefficient a 1 t delta 0 n)
    have hline : (1 : ℝ) + delta = taoExponent Y := by
      dsimp only [delta]
      ring
    have hterm' :
        ‖LSeries.term (mrMellinShiftedCoefficient a 1 t) (delta : ℂ) n‖ =
          ‖LSeries.term a
            ((taoExponent Y : ℝ) + Complex.I * (t : ℂ)) n‖ := by
      simpa [hline] using hterm
    rw [hterm', LSeries.norm_term_eq]
    by_cases hn : n = 0
    · subst n
      simpa only [ite_true] using
        (realDirichletWeight_nonneg (taoExponent Y) 0)
    · rw [if_neg hn]
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
        Complex.I_re, Complex.I_im, zero_mul, Complex.ofReal_im, mul_zero,
        sub_zero, add_zero]
      rw [realDirichletWeight,
        Real.rpow_neg (Nat.cast_nonneg n)]
      simpa [div_eq_mul_inv] using
        mul_le_mul_of_nonneg_right (ha n (Nat.pos_of_ne_zero hn))
          (inv_nonneg.mpr (Real.rpow_nonneg (Nat.cast_nonneg n) _))
  unfold dirichletPerronCoefficientMass
  calc
    (∑' n : ℕ,
        ‖LSeries.term (mrMellinShiftedCoefficient a 1 t)
          ((taoExponent Y - 1 : ℝ) : ℂ) n‖) =
        ∑' n : ℕ,
          ‖LSeries.term (mrMellinShiftedCoefficient a 1 t)
            (delta : ℂ) n‖ := by rfl
    _ ≤ ∑' n : ℕ, realDirichletWeight (taoExponent Y) n :=
      Summable.tsum_le_tsum hpoint hleft hright
    _ ≤ 1 + Real.log (Y : ℝ) := by
      simpa only [taoWindowWeight] using
        (tsum_taoWindowWeight_le_one_add_log hY)

/-- Explicit two-endpoint envelope for the projection error at Mellin real
part one and on Tao's translated line. -/
def mrMellinOneTaoProjectionErrorBound (X Y : ℕ) (U : ℝ) : ℝ :=
  let delta := taoExponent Y - 1
  (8 * (harmonic (2 * X) : ℝ) / U +
      (32 * ((2 * X : ℕ) : ℝ) ^ delta / U) *
        (1 + Real.log (Y : ℝ))) +
    (8 * (harmonic X : ℝ) / U +
      (32 * (X : ℝ) ^ delta / U) *
        (1 + Real.log (Y : ℝ))) +
    (1 / 2 : ℝ) * (((2 * X : ℕ) : ℝ)⁻¹ + (X : ℝ)⁻¹)

/-- A one-bounded coefficient has an explicit, height-uniform dyadic
projection error.  The first and third terms are the two harmonic
near-diagonal masses, the second and fourth are the translated absolute
coefficient masses, and the last term is the exact endpoint envelope. -/
theorem mrDyadicPerronProjectionError_mellin_one_tao_le
    {a : ℕ → ℂ} (ha : ∀ n, 0 < n → ‖a n‖ ≤ 1)
    {X Y : ℕ} (hX : 0 < X) (hY : 1 < Y)
    (t : ℝ) {U : ℝ} (hU : 0 < U) :
    mrDyadicPerronProjectionError a X 1 t
        (taoExponent Y - 1) U ≤
      mrMellinOneTaoProjectionErrorBound X Y U := by
  let delta : ℝ := taoExponent Y - 1
  let b : ℕ → ℂ := mrMellinShiftedCoefficient a 1 t
  have h2X : 0 < 2 * X := by omega
  have hnear2 : dirichletPerronNearMass b (2 * X) U ≤
      8 * (harmonic (2 * X) : ℝ) / U := by
    dsimp only [b]
    exact dirichletPerronNearMass_mellin_one_le_harmonic ha h2X t hU
  have hnear1 : dirichletPerronNearMass b X U ≤
      8 * (harmonic X : ℝ) / U := by
    dsimp only [b]
    exact dirichletPerronNearMass_mellin_one_le_harmonic ha hX t hU
  have hmass : dirichletPerronCoefficientMass b delta ≤
      1 + Real.log (Y : ℝ) := by
    dsimp only [b, delta]
    exact dirichletPerronCoefficientMass_mellin_one_tao_le ha hY t
  have hfactor2 : 0 ≤
      32 * (((2 * X : ℕ) : ℝ) ^ delta) / U := by positivity
  have hfactor1 : 0 ≤
      32 * ((X : ℝ) ^ delta) / U := by positivity
  have htail2 :
      (32 * (((2 * X : ℕ) : ℝ) ^ delta) / U) *
          dirichletPerronCoefficientMass b delta ≤
        (32 * (((2 * X : ℕ) : ℝ) ^ delta) / U) *
          (1 + Real.log (Y : ℝ)) :=
    mul_le_mul_of_nonneg_left hmass hfactor2
  have htail1 :
      (32 * ((X : ℝ) ^ delta) / U) *
          dirichletPerronCoefficientMass b delta ≤
        (32 * ((X : ℝ) ^ delta) / U) *
          (1 + Real.log (Y : ℝ)) :=
    mul_le_mul_of_nonneg_left hmass hfactor1
  have hnorm2 : ‖b (2 * X)‖ ≤ (((2 * X : ℕ) : ℝ))⁻¹ := by
    dsimp only [b]
    rw [norm_mrMellinShiftedCoefficient_eq a 1 t h2X,
      Real.rpow_one]
    simpa only [one_div] using
      div_le_div_of_nonneg_right (ha (2 * X) h2X)
        (Nat.cast_nonneg (2 * X))
  have hnorm1 : ‖b X‖ ≤ (X : ℝ)⁻¹ := by
    dsimp only [b]
    rw [norm_mrMellinShiftedCoefficient_eq a 1 t hX,
      Real.rpow_one]
    simpa only [one_div] using
      div_le_div_of_nonneg_right (ha X hX) (Nat.cast_nonneg X)
  have hend :
      (1 / 2 : ℝ) * (‖b (2 * X)‖ + ‖b X‖) ≤
        (1 / 2 : ℝ) *
          ((((2 * X : ℕ) : ℝ))⁻¹ + (X : ℝ)⁻¹) := by
    exact mul_le_mul_of_nonneg_left (add_le_add hnorm2 hnorm1) (by norm_num)
  unfold mrDyadicPerronProjectionError MRHalaszPerron.perronTruncationError
  dsimp only [b, delta, mrMellinOneTaoProjectionErrorBound]
  exact add_le_add
    (add_le_add (add_le_add hnear2 htail2) (add_le_add hnear1 htail1)) hend

/-- On the same Tao scale, every positive endpoint at most `2X` contributes
at most the absolute constant `exp 2` to the Perron power factor. -/
theorem rpow_taoExponent_sub_one_le_exp_two
    {Z X : ℕ} (hZ : 0 < Z) (hZX : Z ≤ 2 * X) (hX : 2 ≤ X) :
    (Z : ℝ) ^ (taoExponent X - 1) ≤ Real.exp 2 := by
  have hXR : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hZR : (0 : ℝ) < Z := by exact_mod_cast hZ
  have h2XR : (0 : ℝ) < (2 * X : ℕ) := by positivity
  have hlogX : 0 < Real.log (X : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have hlogTwoLe : Real.log 2 ≤ Real.log (X : ℝ) :=
    Real.strictMonoOn_log.monotoneOn (by norm_num) hXR
      (by exact_mod_cast hX)
  have hlogZle : Real.log (Z : ℝ) ≤
      Real.log ((2 * X : ℕ) : ℝ) :=
    Real.strictMonoOn_log.monotoneOn hZR h2XR (by exact_mod_cast hZX)
  have hlog2X : Real.log ((2 * X : ℕ) : ℝ) =
      Real.log 2 + Real.log (X : ℝ) := by
    rw [Nat.cast_mul, Nat.cast_ofNat, Real.log_mul] <;> positivity
  have hlogZ : Real.log (Z : ℝ) ≤ 2 * Real.log (X : ℝ) := by
    rw [hlog2X] at hlogZle
    linarith
  have hdelta : taoExponent X - 1 = (Real.log (X : ℝ))⁻¹ := by
    unfold taoExponent
    ring
  rw [Real.rpow_def_of_pos hZR, hdelta]
  apply Real.exp_le_exp.mpr
  rw [← div_eq_mul_inv, div_le_iff₀ hlogX]
  nlinarith

/-- A same-scale envelope involving only logarithms divided by `X`. -/
def mrMellinOneTaoSameScaleErrorBound (X : ℕ) : ℝ :=
  (8 * (1 + Real.log ((2 * X : ℕ) : ℝ)) / X +
      (32 * Real.exp 2 / X) * (1 + Real.log (X : ℝ))) +
    (8 * (1 + Real.log (X : ℝ)) / X +
      (32 * Real.exp 2 / X) * (1 + Real.log (X : ℝ))) +
    (X : ℝ)⁻¹

/-- Taking both the Tao scale and Perron height equal to `X` reduces the
complete projection error to an explicit `O(log X / X)` expression. -/
theorem mrDyadicPerronProjectionError_mellin_one_sameScale_le
    {a : ℕ → ℂ} (ha : ∀ n, 0 < n → ‖a n‖ ≤ 1)
    {X : ℕ} (hX : 2 ≤ X) (t : ℝ) :
    mrDyadicPerronProjectionError a X 1 t
        (taoExponent X - 1) (X : ℝ) ≤
      mrMellinOneTaoSameScaleErrorBound X := by
  have hXpos : 0 < X := by omega
  have hXR : (0 : ℝ) < X := by exact_mod_cast hXpos
  have hlogX : 0 < Real.log (X : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have hlogTerm : 0 ≤ 1 + Real.log (X : ℝ) := by linarith
  have hbase := mrDyadicPerronProjectionError_mellin_one_tao_le
    ha hXpos (show 1 < X by omega) t hXR
  have hharm2 : (harmonic (2 * X) : ℝ) ≤
      1 + Real.log ((2 * X : ℕ) : ℝ) :=
    harmonic_le_one_add_log (2 * X)
  have hharm1 : (harmonic X : ℝ) ≤
      1 + Real.log (X : ℝ) := harmonic_le_one_add_log X
  have hpow2 : (((2 * X : ℕ) : ℝ) ^ (taoExponent X - 1)) ≤
      Real.exp 2 :=
    rpow_taoExponent_sub_one_le_exp_two (by omega) le_rfl hX
  have hpow1 : ((X : ℝ) ^ (taoExponent X - 1)) ≤ Real.exp 2 :=
    rpow_taoExponent_sub_one_le_exp_two hXpos (by omega) hX
  have hnear2 : 8 * (harmonic (2 * X) : ℝ) / X ≤
      8 * (1 + Real.log ((2 * X : ℕ) : ℝ)) / X := by
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hharm2 (by norm_num)) hXR.le
  have hnear1 : 8 * (harmonic X : ℝ) / X ≤
      8 * (1 + Real.log (X : ℝ)) / X := by
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hharm1 (by norm_num)) hXR.le
  have htail2 :
      (32 * (((2 * X : ℕ) : ℝ) ^ (taoExponent X - 1)) / X) *
          (1 + Real.log (X : ℝ)) ≤
        (32 * Real.exp 2 / X) * (1 + Real.log (X : ℝ)) := by
    apply mul_le_mul_of_nonneg_right _ hlogTerm
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hpow2 (by norm_num)) hXR.le
  have htail1 :
      (32 * ((X : ℝ) ^ (taoExponent X - 1)) / X) *
          (1 + Real.log (X : ℝ)) ≤
        (32 * Real.exp 2 / X) * (1 + Real.log (X : ℝ)) := by
    apply mul_le_mul_of_nonneg_right _ hlogTerm
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hpow1 (by norm_num)) hXR.le
  have hend :
      (1 / 2 : ℝ) *
          ((((2 * X : ℕ) : ℝ))⁻¹ + (X : ℝ)⁻¹) ≤
        (X : ℝ)⁻¹ := by
    rw [Nat.cast_mul, Nat.cast_ofNat]
    field_simp [ne_of_gt hXR]
    nlinarith
  apply hbase.trans
  unfold mrMellinOneTaoProjectionErrorBound
    mrMellinOneTaoSameScaleErrorBound
  dsimp only
  exact add_le_add
    (add_le_add (add_le_add hnear2 htail2) (add_le_add hnear1 htail1)) hend

/-- The scalar same-scale envelope really tends to zero.  Thus the preceding
pointwise estimate is uniform in the outer vertical parameter and vanishes
at both Perron endpoints. -/
theorem tendsto_mrMellinOneTaoSameScaleErrorBound :
    Filter.Tendsto mrMellinOneTaoSameScaleErrorBound Filter.atTop (nhds 0) := by
  have hinv : Filter.Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹)
      Filter.atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hlogdiv : Filter.Tendsto
      (fun n : ℕ ↦ Real.log (n : ℝ) / (n : ℝ))
      Filter.atTop (nhds 0) := by
    simpa [Function.comp_def] using
      Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp
        tendsto_natCast_atTop_atTop
  have honeLog : Filter.Tendsto
      (fun n : ℕ ↦ (1 + Real.log (n : ℝ)) / (n : ℝ))
      Filter.atTop (nhds 0) := by
    have hraw : Filter.Tendsto
        (fun n : ℕ ↦ (n : ℝ)⁻¹ + Real.log (n : ℝ) / (n : ℝ))
        Filter.atTop (nhds 0) := by
      simpa only [zero_add] using hinv.add hlogdiv
    refine hraw.congr' (Filter.Eventually.of_forall fun n ↦ ?_)
    symm
    exact by
      change (1 + Real.log (n : ℝ)) / (n : ℝ) =
        (n : ℝ)⁻¹ + Real.log (n : ℝ) / (n : ℝ)
      rw [add_div, one_div]
  have htwoLog : Filter.Tendsto
      (fun n : ℕ ↦
        (1 + Real.log ((2 * n : ℕ) : ℝ)) / (n : ℝ))
      Filter.atTop (nhds 0) := by
    have hraw : Filter.Tendsto
        (fun n : ℕ ↦
          (1 + Real.log 2) * (n : ℝ)⁻¹ +
            Real.log (n : ℝ) / (n : ℝ))
        Filter.atTop (nhds 0) := by
      simpa only [mul_zero, zero_add] using
        (hinv.const_mul (1 + Real.log 2)).add hlogdiv
    refine hraw.congr' ?_
    filter_upwards [Filter.eventually_gt_atTop (0 : ℕ)] with n hn
    symm
    rw [Nat.cast_mul, Nat.cast_ofNat,
      Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
        (by exact_mod_cast hn.ne')]
    field_simp [show (n : ℝ) ≠ 0 by exact_mod_cast hn.ne']
    ring
  have htotal :=
    (((htwoLog.const_mul 8).add
      (honeLog.const_mul (32 * Real.exp 2))).add
      (honeLog.const_mul 8)).add
      (honeLog.const_mul (32 * Real.exp 2)) |>.add hinv
  have htotal' : Filter.Tendsto
      (fun n : ℕ ↦
        8 * ((1 + Real.log ((2 * n : ℕ) : ℝ)) / (n : ℝ)) +
          32 * Real.exp 2 * ((1 + Real.log (n : ℝ)) / (n : ℝ)) +
          8 * ((1 + Real.log (n : ℝ)) / (n : ℝ)) +
          32 * Real.exp 2 * ((1 + Real.log (n : ℝ)) / (n : ℝ)) +
          (n : ℝ)⁻¹)
      Filter.atTop (nhds 0) := by
    simpa only [mul_zero, add_zero, zero_add] using htotal
  refine htotal'.congr' (Filter.Eventually.of_forall fun n ↦ ?_)
  symm
  exact by
    unfold mrMellinOneTaoSameScaleErrorBound
    ring

/-- Uniform vanishing form: after one threshold, the same-scale projection
error is below `epsilon` for every outer vertical parameter `t`. -/
theorem eventually_forall_mrDyadicPerronProjectionError_mellin_one_sameScale_lt
    {a : ℕ → ℂ} (ha : ∀ n, 0 < n → ‖a n‖ ≤ 1)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ X : ℕ in Filter.atTop, ∀ t : ℝ,
      mrDyadicPerronProjectionError a X 1 t
        (taoExponent X - 1) (X : ℝ) < epsilon := by
  have hbound := tendsto_mrMellinOneTaoSameScaleErrorBound.eventually
    (Iio_mem_nhds hepsilon)
  filter_upwards [hbound, Filter.eventually_ge_atTop 2] with X hsmall hX
  intro t
  exact (mrDyadicPerronProjectionError_mellin_one_sameScale_le
    ha hX t).trans_lt hsmall

/-- A convenient explicit envelope when the Perron truncation height is
`X / 2`.  The four terms carrying the truncation denominator double, while
doubling the complete same-scale envelope also harmlessly doubles the
endpoint term. -/
def mrMellinOneTaoHalfHeightErrorBound (X : ℕ) : ℝ :=
  2 * mrMellinOneTaoSameScaleErrorBound X

/-- At Tao's translated line, truncating the Perron integral at half the
outer dyadic scale still gives a uniform `O(log X / X)` projection error. -/
theorem mrDyadicPerronProjectionError_mellin_one_halfHeight_le
    {a : ℕ → ℂ} (ha : ∀ n, 0 < n → ‖a n‖ ≤ 1)
    {X : ℕ} (hX : 2 ≤ X) (t : ℝ) :
    mrDyadicPerronProjectionError a X 1 t
        (taoExponent X - 1) ((X : ℝ) / 2) ≤
      mrMellinOneTaoHalfHeightErrorBound X := by
  have hXpos : 0 < X := by omega
  have hXR : (0 : ℝ) < X := by exact_mod_cast hXpos
  have hU : (0 : ℝ) < (X : ℝ) / 2 := by positivity
  have hlogX : 0 < Real.log (X : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have hlogTerm : 0 ≤ 1 + Real.log (X : ℝ) := by linarith
  have hbase := mrDyadicPerronProjectionError_mellin_one_tao_le
    ha hXpos (show 1 < X by omega) t hU
  have hharm2 : (harmonic (2 * X) : ℝ) ≤
      1 + Real.log ((2 * X : ℕ) : ℝ) :=
    harmonic_le_one_add_log (2 * X)
  have hharm1 : (harmonic X : ℝ) ≤
      1 + Real.log (X : ℝ) := harmonic_le_one_add_log X
  have hpow2 : (((2 * X : ℕ) : ℝ) ^ (taoExponent X - 1)) ≤
      Real.exp 2 :=
    rpow_taoExponent_sub_one_le_exp_two (by omega) le_rfl hX
  have hpow1 : ((X : ℝ) ^ (taoExponent X - 1)) ≤ Real.exp 2 :=
    rpow_taoExponent_sub_one_le_exp_two hXpos (by omega) hX
  have hnear2 :
      8 * (harmonic (2 * X) : ℝ) / ((X : ℝ) / 2) ≤
        2 * (8 * (1 + Real.log ((2 * X : ℕ) : ℝ)) / X) := by
    calc
      8 * (harmonic (2 * X) : ℝ) / ((X : ℝ) / 2) =
          16 * (harmonic (2 * X) : ℝ) / X := by
            field_simp [ne_of_gt hXR]
            all_goals ring
      _ ≤ 16 * (1 + Real.log ((2 * X : ℕ) : ℝ)) / X :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hharm2 (by norm_num)) hXR.le
      _ = 2 * (8 * (1 + Real.log ((2 * X : ℕ) : ℝ)) / X) := by ring
  have hnear1 :
      8 * (harmonic X : ℝ) / ((X : ℝ) / 2) ≤
        2 * (8 * (1 + Real.log (X : ℝ)) / X) := by
    calc
      8 * (harmonic X : ℝ) / ((X : ℝ) / 2) =
          16 * (harmonic X : ℝ) / X := by
            field_simp [ne_of_gt hXR]
            all_goals ring
      _ ≤ 16 * (1 + Real.log (X : ℝ)) / X :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hharm1 (by norm_num)) hXR.le
      _ = 2 * (8 * (1 + Real.log (X : ℝ)) / X) := by ring
  have htail2 :
      (32 * (((2 * X : ℕ) : ℝ) ^ (taoExponent X - 1)) /
          ((X : ℝ) / 2)) * (1 + Real.log (X : ℝ)) ≤
        2 * ((32 * Real.exp 2 / X) *
          (1 + Real.log (X : ℝ))) := by
    calc
      (32 * (((2 * X : ℕ) : ℝ) ^ (taoExponent X - 1)) /
          ((X : ℝ) / 2)) * (1 + Real.log (X : ℝ)) =
          (64 * (((2 * X : ℕ) : ℝ) ^ (taoExponent X - 1)) / X) *
            (1 + Real.log (X : ℝ)) := by
              field_simp [ne_of_gt hXR]
              all_goals ring
      _ ≤ (64 * Real.exp 2 / X) * (1 + Real.log (X : ℝ)) := by
        apply mul_le_mul_of_nonneg_right _ hlogTerm
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hpow2 (by norm_num)) hXR.le
      _ = 2 * ((32 * Real.exp 2 / X) *
          (1 + Real.log (X : ℝ))) := by ring
  have htail1 :
      (32 * ((X : ℝ) ^ (taoExponent X - 1)) /
          ((X : ℝ) / 2)) * (1 + Real.log (X : ℝ)) ≤
        2 * ((32 * Real.exp 2 / X) *
          (1 + Real.log (X : ℝ))) := by
    calc
      (32 * ((X : ℝ) ^ (taoExponent X - 1)) /
          ((X : ℝ) / 2)) * (1 + Real.log (X : ℝ)) =
          (64 * ((X : ℝ) ^ (taoExponent X - 1)) / X) *
            (1 + Real.log (X : ℝ)) := by
              field_simp [ne_of_gt hXR]
              all_goals ring
      _ ≤ (64 * Real.exp 2 / X) * (1 + Real.log (X : ℝ)) := by
        apply mul_le_mul_of_nonneg_right _ hlogTerm
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hpow1 (by norm_num)) hXR.le
      _ = 2 * ((32 * Real.exp 2 / X) *
          (1 + Real.log (X : ℝ))) := by ring
  have hend :
      (1 / 2 : ℝ) *
          ((((2 * X : ℕ) : ℝ))⁻¹ + (X : ℝ)⁻¹) ≤
        2 * (X : ℝ)⁻¹ := by
    rw [Nat.cast_mul, Nat.cast_ofNat]
    field_simp [ne_of_gt hXR]
    nlinarith
  apply hbase.trans
  unfold mrMellinOneTaoProjectionErrorBound
    mrMellinOneTaoHalfHeightErrorBound
    mrMellinOneTaoSameScaleErrorBound
  dsimp only
  calc
    (8 * (harmonic (2 * X) : ℝ) / ((X : ℝ) / 2) +
          (32 * (((2 * X : ℕ) : ℝ) ^ (taoExponent X - 1)) /
            ((X : ℝ) / 2)) *
            (1 + Real.log (X : ℝ))) +
        (8 * (harmonic X : ℝ) / ((X : ℝ) / 2) +
          (32 * ((X : ℝ) ^ (taoExponent X - 1)) / ((X : ℝ) / 2)) *
            (1 + Real.log (X : ℝ))) +
        (1 / 2 : ℝ) * ((((2 * X : ℕ) : ℝ))⁻¹ + (X : ℝ)⁻¹) ≤
        (2 * (8 * (1 + Real.log ((2 * X : ℕ) : ℝ)) / X) +
          2 * ((32 * Real.exp 2 / X) * (1 + Real.log (X : ℝ)))) +
        (2 * (8 * (1 + Real.log (X : ℝ)) / X) +
          2 * ((32 * Real.exp 2 / X) * (1 + Real.log (X : ℝ)))) +
        2 * (X : ℝ)⁻¹ :=
      add_le_add
        (add_le_add (add_le_add hnear2 htail2)
          (add_le_add hnear1 htail1)) hend
    _ = 2 *
        ((8 * (1 + Real.log ((2 * X : ℕ) : ℝ)) / X +
            (32 * Real.exp 2 / X) * (1 + Real.log (X : ℝ))) +
          (8 * (1 + Real.log (X : ℝ)) / X +
            (32 * Real.exp 2 / X) * (1 + Real.log (X : ℝ))) +
          (X : ℝ)⁻¹) := by ring

/-- The half-height envelope tends to zero. -/
theorem tendsto_mrMellinOneTaoHalfHeightErrorBound :
    Filter.Tendsto mrMellinOneTaoHalfHeightErrorBound
      Filter.atTop (nhds 0) := by
  unfold mrMellinOneTaoHalfHeightErrorBound
  simpa only [mul_zero] using
    tendsto_mrMellinOneTaoSameScaleErrorBound.const_mul 2

/-- Uniform vanishing at half height: after one threshold, the projection
error is below `epsilon` for every outer vertical parameter. -/
theorem eventually_forall_mrDyadicPerronProjectionError_mellin_one_halfHeight_lt
    {a : ℕ → ℂ} (ha : ∀ n, 0 < n → ‖a n‖ ≤ 1)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ X : ℕ in Filter.atTop, ∀ t : ℝ,
      mrDyadicPerronProjectionError a X 1 t
        (taoExponent X - 1) ((X : ℝ) / 2) < epsilon := by
  have hbound := tendsto_mrMellinOneTaoHalfHeightErrorBound.eventually
    (Iio_mem_nhds hepsilon)
  filter_upwards [hbound, Filter.eventually_ge_atTop 2] with X hsmall hX
  intro t
  exact (mrDyadicPerronProjectionError_mellin_one_halfHeight_le
    ha hX t).trans_lt hsmall

end

end Erdos67b.MRPerronProjectionErrorBound
