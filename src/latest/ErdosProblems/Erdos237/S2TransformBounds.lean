import ErdosProblems.Erdos237.SieveCollisionLimits
import BoundedGaps.Maynard.MaynardS2RestrictedYComparison
import BoundedGaps.Maynard.MaynardS2RestrictedStarredCorrectionBound

/-!
# S2 transform envelopes for bounded supported weights

Retaining the reciprocal-totient mean makes the pre-sieve density cancel
against the normalization. All estimates apply in arbitrary dimension.
-/

namespace Erdos237

open Finset Filter BoundedGaps.Maynard
open scoped BigOperators

theorem squarefreeCoprimeInvTotientMean_nonneg (W R : ℕ) :
    0 ≤ squarefreeCoprimeInvTotientMean W R := by
  unfold squarefreeCoprimeInvTotientMean
  exact sum_nonneg fun _ _ => by split_ifs <;> positivity

noncomputable def s2FiberErrorFactor (k D : ℕ) : ℝ :=
  8 / (D : ℝ) + (8 * Real.exp 8 / D) * (1 + 8 * Real.exp 8 / D) ^ (k - 1)

theorem s2FiberErrorFactor_nonneg (k D : ℕ) : 0 ≤ s2FiberErrorFactor k D := by
  unfold s2FiberErrorFactor
  positivity

theorem tendsto_s2FiberErrorFactor (k : ℕ) :
    Tendsto (fun N : ℕ => s2FiberErrorFactor k (tripleLogCutoff (N - 1)))
      atTop (nhds 0) := by
  have h₁ : Tendsto (fun N : ℕ => (8 : ℝ) / tripleLogCutoff (N - 1)) atTop (nhds 0) :=
    (tendsto_const_div_atTop_nhds_zero_nat (8 : ℝ)).comp tendsto_shifted_tripleLogCutoff
  have h₂ : Tendsto (fun N : ℕ => 8 * Real.exp 8 / tripleLogCutoff (N - 1))
      atTop (nhds 0) :=
    (tendsto_const_div_atTop_nhds_zero_nat (8 * Real.exp 8)).comp
      tendsto_shifted_tripleLogCutoff
  simpa [s2FiberErrorFactor] using h₁.add (h₂.mul ((tendsto_const_nhds.add h₂).pow (k - 1)))

noncomputable def s2TransformEnvelope (k R D : ℕ) (B : ℝ) : ℝ :=
  B * squarefreeCoprimeInvTotientMean (primorial D) R *
    (1 + (k : ℝ) * s2FiberErrorFactor k D)

theorem s2TransformEnvelope_nonneg (k R D : ℕ) {B : ℝ} (hB : 0 ≤ B) :
    0 ≤ s2TransformEnvelope k R D B := by
  have := s2FiberErrorFactor_nonneg k D
  have := squarefreeCoprimeInvTotientMean_nonneg (primorial D) R
  unfold s2TransformEnvelope
  positivity

theorem abs_s2Fiber_le_mean {H : Finset ℕ} {R D : ℕ} {y : (H → ℕ) → ℝ}
    (m : H) (r : H → ℕ) {B : ℝ} (hB : 0 ≤ B) (hbound : ∀ u, |y u| ≤ B) :
    |maynardS2CoordinateFiberSum H R (primorial D) y m r| ≤
      B * squarefreeCoprimeInvTotientMean (primorial D) R := by
  apply (abs_maynardS2CoordinateFiberSum_le m r hB hbound).trans
  apply mul_le_mul_of_nonneg_left ?_ hB
  exact preSievedCoordinateInvTotientSum_le (primorial D) R

theorem abs_s2Transform_sub_fiber_le_mean {H : Finset ℕ} {R D : ℕ}
    {y : (H → ℕ) → ℝ} (hy : IsSupportedMaynardY H R (primorial D) y)
    (m : H) {r : H → ℕ} (hD : 0 < D)
    (hr : IsMaynardDivisorTuple H R (primorial D) r) (hrm : r m = 1)
    {B : ℝ} (hB : 0 ≤ B) (hbound : ∀ u, |y u| ≤ B) :
    |maynardS2RestrictedYFromCoefficients H (maynardDivisorTupleSupport H R (primorial D))
        (maynardCoefficientFromY H R (primorial D) y) m r -
      maynardS2CoordinateFiberSum H R (primorial D) y m r| ≤
      B * squarefreeCoprimeInvTotientMean (primorial D) R *
        ((univ.erase m).card : ℝ) * s2FiberErrorFactor (univ.erase m).card D := by
  have hb := abs_maynardS2RestrictedY_sub_coordinateFiber_le hy m hD hr hrm hB hbound
  have hp : preSievedCoordinateInvTotientMass (primorial D) R ≤
      squarefreeCoprimeInvTotientMean (primorial D) R :=
    preSievedCoordinateInvTotientSum_le (primorial D) R
  have hf := s2FiberErrorFactor_nonneg (univ.erase m).card D
  calc
    _ ≤ _ := hb
    _ = B * preSievedCoordinateInvTotientMass (primorial D) R *
        ((univ.erase m).card : ℝ) * s2FiberErrorFactor (univ.erase m).card D := by
      unfold s2FiberErrorFactor
      ring
    _ ≤ _ := by gcongr

theorem abs_s2Transform_le_envelope {H : Finset ℕ} {R D : ℕ} {y : (H → ℕ) → ℝ}
    (hy : IsSupportedMaynardY H R (primorial D) y) (m : H) {r : H → ℕ}
    (hD : 0 < D) (hr : IsMaynardDivisorTuple H R (primorial D) r) (hrm : r m = 1)
    {B : ℝ} (hB : 0 ≤ B) (hbound : ∀ u, |y u| ≤ B) :
    |maynardS2RestrictedYFromCoefficients H (maynardDivisorTupleSupport H R (primorial D))
      (maynardCoefficientFromY H R (primorial D) y) m r| ≤
      s2TransformEnvelope (univ.erase m).card R D B := by
  have hd := abs_s2Transform_sub_fiber_le_mean hy m hD hr hrm hB hbound
  have hf := abs_s2Fiber_le_mean (R := R) (D := D) m r hB hbound
  have htri (a b : ℝ) : |a| ≤ |a - b| + |b| := by
    simpa only [sub_add_cancel] using abs_add_le (a - b) b
  calc
    _ ≤ |maynardS2RestrictedYFromCoefficients H
          (maynardDivisorTupleSupport H R (primorial D))
          (maynardCoefficientFromY H R (primorial D) y) m r -
          maynardS2CoordinateFiberSum H R (primorial D) y m r| +
        |maynardS2CoordinateFiberSum H R (primorial D) y m r| := htri _ _
    _ ≤ _ := add_le_add hd hf
    _ = _ := by unfold s2TransformEnvelope; ring

theorem tendsto_s2TransformEnvelope_div_scale (k : ℕ) {alpha : ℝ} (halpha : 0 < alpha)
    (B : ℝ) :
    Tendsto (fun N : ℕ => s2TransformEnvelope k (engelsmaMaynardRadius alpha N)
      (tripleLogCutoff (N - 1)) B / sieveCoordinateScale alpha N) atTop (nhds B) := by
  have hmean := tendsto_mean_div_sieveCoordinateScale halpha
  have hfac := (tendsto_s2FiberErrorFactor k).const_mul (k : ℝ)
  have hlim := (hmean.const_mul B).mul (hfac.const_add 1)
  simp only [mul_zero, add_zero, mul_one] at hlim
  apply hlim.congr'
  filter_upwards [] with N
  unfold s2TransformEnvelope
  change _ = B * squarefreeCoprimeInvTotientMean (engelsmaMaynardModulus N)
    (engelsmaMaynardRadius alpha N) * _ / sieveCoordinateScale alpha N
  ring

end Erdos237
