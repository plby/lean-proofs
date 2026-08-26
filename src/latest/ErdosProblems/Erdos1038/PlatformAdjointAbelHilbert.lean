import ErdosProblems.Erdos1038.PlatformAdjointAbelSeries
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Interior Abel Hilbert series for the platform adjoint

For a bounded cosine-coefficient sequence, the Abel factor makes the
second-kind Hilbert modes absolutely and uniformly summable on compact
intervals.  This file defines the infinite Hilbert series and proves that
the paired finite Hilbert transforms converge to it.
-/

set_option warningAsError false

open Filter Set
open scoped BigOperators Topology

namespace Erdos1038

noncomputable section

def platformAbelEvenHilbertTerm
    (r : ℝ) (coefficient : ℕ → ℝ) (lambda : ℝ) (m : ℕ)
    (theta : ℝ) : ℝ :=
  (lambda ^ (2 * (m + 1)) * coefficient (2 * (m + 1))) *
    ((2 / r) * (-oddSecondKindAngularMode (m + 1) theta))

def platformAbelOddHilbertTerm
    (r : ℝ) (coefficient : ℕ → ℝ) (lambda : ℝ) (m : ℕ)
    (theta : ℝ) : ℝ :=
  (lambda ^ (2 * m + 1) * coefficient (2 * m + 1)) *
    ((2 / r) * (-evenSecondKindAngularMode m theta))

lemma continuous_platformAbelEvenHilbertTerm
    (r : ℝ) (coefficient : ℕ → ℝ) (lambda : ℝ) (m : ℕ) :
    Continuous (platformAbelEvenHilbertTerm r coefficient lambda m) := by
  unfold platformAbelEvenHilbertTerm
  exact continuous_const.mul
    (continuous_const.mul
      (continuous_oddSecondKindAngularMode (m + 1)).neg)

lemma continuous_platformAbelOddHilbertTerm
    (r : ℝ) (coefficient : ℕ → ℝ) (lambda : ℝ) (m : ℕ) :
    Continuous (platformAbelOddHilbertTerm r coefficient lambda m) := by
  unfold platformAbelOddHilbertTerm
  exact continuous_const.mul
    (continuous_const.mul
      (continuous_evenSecondKindAngularMode m).neg)

private lemma abelHilbertEvenFrequency_injective :
    Function.Injective (fun m : ℕ ↦ 2 * (m + 1)) := by
  intro m n h
  have h' : m + 1 = n + 1 :=
    Nat.mul_left_cancel (by norm_num : 0 < 2) h
  omega

private lemma abelHilbertOddFrequency_injective :
    Function.Injective (fun m : ℕ ↦ 2 * m + 1) := by
  intro m n h
  have h' : 2 * m = 2 * n := Nat.add_right_cancel h
  exact Nat.mul_left_cancel (by norm_num : 0 < 2) h'

private lemma summable_frequency_mul_absLambda_pow
    {lambda : ℝ} (hlambda : |lambda| < 1) :
    Summable (fun n : ℕ ↦ (n : ℝ) * |lambda| ^ n) := by
  have hnorm : ‖|lambda|‖ < (1 : ℝ) := by
    simpa only [Real.norm_eq_abs, abs_abs] using! hlambda
  simpa only [pow_one, Real.norm_eq_abs, abs_abs] using!
    (summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1
      (r := |lambda|) hnorm)

private lemma summable_evenFrequency_mul_absLambda_pow
    {lambda : ℝ} (hlambda : |lambda| < 1) :
    Summable (fun m : ℕ ↦
      ((2 * (m + 1) : ℕ) : ℝ) * |lambda| ^ (2 * (m + 1))) := by
  exact (summable_frequency_mul_absLambda_pow hlambda).comp_injective
    abelHilbertEvenFrequency_injective

private lemma summable_oddFrequency_mul_absLambda_pow
    {lambda : ℝ} (hlambda : |lambda| < 1) :
    Summable (fun m : ℕ ↦
      ((2 * m + 1 : ℕ) : ℝ) * |lambda| ^ (2 * m + 1)) := by
  exact (summable_frequency_mul_absLambda_pow hlambda).comp_injective
    abelHilbertOddFrequency_injective

lemma abs_platformAbelEvenHilbertTerm_le
    {coefficient : ℕ → ℝ} {C : ℝ}
    (hbound : RealSequenceBoundedBy coefficient C)
    (r lambda : ℝ) (m : ℕ) (theta : ℝ) :
    |platformAbelEvenHilbertTerm r coefficient lambda m theta| ≤
      (|2 / r| * C) *
        (((2 * (m + 1) : ℕ) : ℝ) * |lambda| ^ (2 * (m + 1))) := by
  have hmode :
      |oddSecondKindAngularMode (m + 1) theta| ≤
        ((2 * (m + 1) : ℕ) : ℝ) := by
    calc
      |oddSecondKindAngularMode (m + 1) theta| ≤
          2 * ((m + 1 : ℕ) : ℝ) :=
        abs_oddSecondKindAngularMode_le (m + 1) theta
      _ = ((2 * (m + 1) : ℕ) : ℝ) := by norm_num
  have hcoefficient :
      |lambda| ^ (2 * (m + 1)) * |coefficient (2 * (m + 1))| ≤
        |lambda| ^ (2 * (m + 1)) * C :=
    mul_le_mul_of_nonneg_left (hbound _)
      (pow_nonneg (abs_nonneg lambda) _)
  have hmodeFactor :
      |2 / r| * |oddSecondKindAngularMode (m + 1) theta| ≤
        |2 / r| * (((2 * (m + 1) : ℕ) : ℝ)) :=
    mul_le_mul_of_nonneg_left hmode (abs_nonneg _)
  unfold platformAbelEvenHilbertTerm
  rw [abs_mul, abs_mul, abs_pow, abs_mul, abs_neg]
  calc
    |lambda| ^ (2 * (m + 1)) * |coefficient (2 * (m + 1))| *
          (|2 / r| * |oddSecondKindAngularMode (m + 1) theta|) ≤
        |lambda| ^ (2 * (m + 1)) * C *
          (|2 / r| * (((2 * (m + 1) : ℕ) : ℝ)) ) := by
      exact mul_le_mul hcoefficient hmodeFactor
        (mul_nonneg (abs_nonneg _) (abs_nonneg _))
        (mul_nonneg (pow_nonneg (abs_nonneg lambda) _) hbound.nonneg)
    _ = (|2 / r| * C) *
        (((2 * (m + 1) : ℕ) : ℝ) * |lambda| ^ (2 * (m + 1))) := by
      ring

lemma abs_platformAbelOddHilbertTerm_le
    {coefficient : ℕ → ℝ} {C : ℝ}
    (hbound : RealSequenceBoundedBy coefficient C)
    (r lambda : ℝ) (m : ℕ) (theta : ℝ) :
    |platformAbelOddHilbertTerm r coefficient lambda m theta| ≤
      (|2 / r| * C) *
        (((2 * m + 1 : ℕ) : ℝ) * |lambda| ^ (2 * m + 1)) := by
  have hmode :
      |evenSecondKindAngularMode m theta| ≤ ((2 * m + 1 : ℕ) : ℝ) := by
    calc
      |evenSecondKindAngularMode m theta| ≤ 2 * (m : ℝ) + 1 :=
        abs_evenSecondKindAngularMode_le m theta
      _ = ((2 * m + 1 : ℕ) : ℝ) := by norm_num
  have hcoefficient :
      |lambda| ^ (2 * m + 1) * |coefficient (2 * m + 1)| ≤
        |lambda| ^ (2 * m + 1) * C :=
    mul_le_mul_of_nonneg_left (hbound _)
      (pow_nonneg (abs_nonneg lambda) _)
  have hmodeFactor :
      |2 / r| * |evenSecondKindAngularMode m theta| ≤
        |2 / r| * (((2 * m + 1 : ℕ) : ℝ)) :=
    mul_le_mul_of_nonneg_left hmode (abs_nonneg _)
  unfold platformAbelOddHilbertTerm
  rw [abs_mul, abs_mul, abs_pow, abs_mul, abs_neg]
  calc
    |lambda| ^ (2 * m + 1) * |coefficient (2 * m + 1)| *
          (|2 / r| * |evenSecondKindAngularMode m theta|) ≤
        |lambda| ^ (2 * m + 1) * C *
          (|2 / r| * (((2 * m + 1 : ℕ) : ℝ))) := by
      exact mul_le_mul hcoefficient hmodeFactor
        (mul_nonneg (abs_nonneg _) (abs_nonneg _))
        (mul_nonneg (pow_nonneg (abs_nonneg lambda) _) hbound.nonneg)
    _ = (|2 / r| * C) *
        (((2 * m + 1 : ℕ) : ℝ) * |lambda| ^ (2 * m + 1)) := by
      ring

lemma summable_platformAbelEvenHilbertTerm
    {coefficient : ℕ → ℝ} {lambda C : ℝ}
    (hlambda : |lambda| < 1)
    (hbound : RealSequenceBoundedBy coefficient C)
    (r theta : ℝ) :
    Summable (fun m : ℕ ↦
      platformAbelEvenHilbertTerm r coefficient lambda m theta) := by
  have hmajor :=
    (summable_evenFrequency_mul_absLambda_pow hlambda).mul_left
      (|2 / r| * C)
  apply Summable.of_norm_bounded hmajor
  intro m
  rw [Real.norm_eq_abs]
  exact abs_platformAbelEvenHilbertTerm_le hbound r lambda m theta

lemma summable_platformAbelOddHilbertTerm
    {coefficient : ℕ → ℝ} {lambda C : ℝ}
    (hlambda : |lambda| < 1)
    (hbound : RealSequenceBoundedBy coefficient C)
    (r theta : ℝ) :
    Summable (fun m : ℕ ↦
      platformAbelOddHilbertTerm r coefficient lambda m theta) := by
  have hmajor :=
    (summable_oddFrequency_mul_absLambda_pow hlambda).mul_left
      (|2 / r| * C)
  apply Summable.of_norm_bounded hmajor
  intro m
  rw [Real.norm_eq_abs]
  exact abs_platformAbelOddHilbertTerm_le hbound r lambda m theta

def platformAbelEvenHilbertContinuousTerm
    (r : ℝ) (coefficient : ℕ → ℝ) (lambda : ℝ) (m : ℕ) : C(ℝ, ℝ) where
  toFun := platformAbelEvenHilbertTerm r coefficient lambda m
  continuous_toFun :=
    continuous_platformAbelEvenHilbertTerm r coefficient lambda m

def platformAbelOddHilbertContinuousTerm
    (r : ℝ) (coefficient : ℕ → ℝ) (lambda : ℝ) (m : ℕ) : C(ℝ, ℝ) where
  toFun := platformAbelOddHilbertTerm r coefficient lambda m
  continuous_toFun :=
    continuous_platformAbelOddHilbertTerm r coefficient lambda m

lemma platformAbelEvenHilbertContinuousTerm_norm_restrict_le
    {coefficient : ℕ → ℝ} {C : ℝ}
    (hbound : RealSequenceBoundedBy coefficient C)
    (r lambda : ℝ) (K : TopologicalSpace.Compacts ℝ) (m : ℕ) :
    ‖(platformAbelEvenHilbertContinuousTerm
        r coefficient lambda m).restrict K‖ ≤
      (|2 / r| * C) *
        (((2 * (m + 1) : ℕ) : ℝ) * |lambda| ^ (2 * (m + 1))) := by
  apply (ContinuousMap.norm_le _
    (mul_nonneg
      (mul_nonneg (abs_nonneg _) hbound.nonneg)
      (mul_nonneg (by positivity) (pow_nonneg (abs_nonneg lambda) _)))).2
  intro theta
  change |platformAbelEvenHilbertTerm
    r coefficient lambda m theta.1| ≤ _
  exact abs_platformAbelEvenHilbertTerm_le hbound r lambda m theta.1

lemma platformAbelOddHilbertContinuousTerm_norm_restrict_le
    {coefficient : ℕ → ℝ} {C : ℝ}
    (hbound : RealSequenceBoundedBy coefficient C)
    (r lambda : ℝ) (K : TopologicalSpace.Compacts ℝ) (m : ℕ) :
    ‖(platformAbelOddHilbertContinuousTerm
        r coefficient lambda m).restrict K‖ ≤
      (|2 / r| * C) *
        (((2 * m + 1 : ℕ) : ℝ) * |lambda| ^ (2 * m + 1)) := by
  apply (ContinuousMap.norm_le _
    (mul_nonneg
      (mul_nonneg (abs_nonneg _) hbound.nonneg)
      (mul_nonneg (by positivity) (pow_nonneg (abs_nonneg lambda) _)))).2
  intro theta
  change |platformAbelOddHilbertTerm
    r coefficient lambda m theta.1| ≤ _
  exact abs_platformAbelOddHilbertTerm_le hbound r lambda m theta.1

theorem summable_platformAbelEvenHilbertContinuousTerm_restrict_norm
    {coefficient : ℕ → ℝ} {lambda C : ℝ}
    (hlambda : |lambda| < 1)
    (hbound : RealSequenceBoundedBy coefficient C)
    (r : ℝ) (K : TopologicalSpace.Compacts ℝ) :
    Summable (fun m : ℕ ↦
      ‖(platformAbelEvenHilbertContinuousTerm
        r coefficient lambda m).restrict K‖) := by
  have hmajor :=
    (summable_evenFrequency_mul_absLambda_pow hlambda).mul_left
      (|2 / r| * C)
  apply Summable.of_norm_bounded hmajor
  intro m
  rw [Real.norm_of_nonneg (norm_nonneg _)]
  exact platformAbelEvenHilbertContinuousTerm_norm_restrict_le
    hbound r lambda K m

theorem summable_platformAbelOddHilbertContinuousTerm_restrict_norm
    {coefficient : ℕ → ℝ} {lambda C : ℝ}
    (hlambda : |lambda| < 1)
    (hbound : RealSequenceBoundedBy coefficient C)
    (r : ℝ) (K : TopologicalSpace.Compacts ℝ) :
    Summable (fun m : ℕ ↦
      ‖(platformAbelOddHilbertContinuousTerm
        r coefficient lambda m).restrict K‖) := by
  have hmajor :=
    (summable_oddFrequency_mul_absLambda_pow hlambda).mul_left
      (|2 / r| * C)
  apply Summable.of_norm_bounded hmajor
  intro m
  rw [Real.norm_of_nonneg (norm_nonneg _)]
  exact platformAbelOddHilbertContinuousTerm_norm_restrict_le
    hbound r lambda K m

/-- The exact interior Abel Hilbert series, split by parity. -/
def platformAbelHilbertSeries
    (r : ℝ) (coefficient : ℕ → ℝ) (lambda theta : ℝ) : ℝ :=
  (∑' m : ℕ, platformAbelEvenHilbertTerm
      r coefficient lambda m theta) +
    ∑' m : ℕ, platformAbelOddHilbertTerm
      r coefficient lambda m theta

/-- For an interior Abel parameter the Hilbert series is a continuous
function of the angular variable.  This is the global Weierstrass estimate
behind the measurability clause in the finite-jump passage. -/
theorem continuous_platformAbelHilbertSeries
    {coefficient : ℕ → ℝ} {lambda C : ℝ}
    (hlambda : |lambda| < 1)
    (hbound : RealSequenceBoundedBy coefficient C) (r : ℝ) :
    Continuous (platformAbelHilbertSeries r coefficient lambda) := by
  have hevenMajorant : Summable (fun m : ℕ ↦
      (|2 / r| * C) *
        (((2 * (m + 1) : ℕ) : ℝ) * |lambda| ^ (2 * (m + 1)))) :=
    (summable_evenFrequency_mul_absLambda_pow hlambda).mul_left
      (|2 / r| * C)
  have hoddMajorant : Summable (fun m : ℕ ↦
      (|2 / r| * C) *
        (((2 * m + 1 : ℕ) : ℝ) * |lambda| ^ (2 * m + 1))) :=
    (summable_oddFrequency_mul_absLambda_pow hlambda).mul_left
      (|2 / r| * C)
  have heven : Continuous (fun theta : ℝ ↦
      ∑' m : ℕ, platformAbelEvenHilbertTerm
        r coefficient lambda m theta) := by
    apply continuous_tsum
    · exact continuous_platformAbelEvenHilbertTerm r coefficient lambda
    · exact hevenMajorant
    · intro m theta
      rw [Real.norm_eq_abs]
      exact abs_platformAbelEvenHilbertTerm_le hbound r lambda m theta
  have hodd : Continuous (fun theta : ℝ ↦
      ∑' m : ℕ, platformAbelOddHilbertTerm
        r coefficient lambda m theta) := by
    apply continuous_tsum
    · exact continuous_platformAbelOddHilbertTerm r coefficient lambda
    · exact hoddMajorant
    · intro m theta
      rw [Real.norm_eq_abs]
      exact abs_platformAbelOddHilbertTerm_le hbound r lambda m theta
  exact heven.add hodd

/-- Multiplying the even second-kind mode by `sin theta` recovers its
ordinary odd-frequency sine mode. -/
theorem evenSecondKindAngularMode_mul_sin
    (m : ℕ) (theta : ℝ) :
    evenSecondKindAngularMode m theta * Real.sin theta =
      Real.sin (((2 * m + 1 : ℕ) : ℝ) * theta) := by
  rw [evenSecondKindAngularMode_eq_chebyshevU,
    Polynomial.Chebyshev.U_real_cos]
  congr 1
  simp [evenSecondKindIndex]

/-- Multiplying the odd second-kind mode by `sin theta` recovers its
ordinary positive even-frequency sine mode (and gives zero at `m = 0`). -/
theorem oddSecondKindAngularMode_mul_sin
    (m : ℕ) (theta : ℝ) :
    oddSecondKindAngularMode m theta * Real.sin theta =
      Real.sin (((2 * m : ℕ) : ℝ) * theta) := by
  rw [oddSecondKindAngularMode_eq_chebyshevU,
    Polynomial.Chebyshev.U_real_cos]
  congr 1
  simp [oddSecondKindIndex]

/-- The positive-frequency sine summand corresponding to the cosine data.
Its index is shifted so `n = 0` is frequency one. -/
def platformAbelSineTerm
    (coefficient : ℕ → ℝ) (lambda : ℝ) (n : ℕ) (theta : ℝ) : ℝ :=
  lambda ^ (n + 1) * coefficient (n + 1) *
    Real.sin (((n + 1 : ℕ) : ℝ) * theta)

lemma summable_platformAbelSineTerm
    {coefficient : ℕ → ℝ} {lambda C theta : ℝ}
    (hlambda : |lambda| < 1)
    (hbound : RealSequenceBoundedBy coefficient C) :
    Summable (fun n : ℕ ↦ platformAbelSineTerm
      coefficient lambda n theta) := by
  have hgeom : Summable (fun n : ℕ ↦ |lambda| ^ (n + 1)) :=
    (summable_geometric_of_lt_one (abs_nonneg lambda) hlambda).comp_injective
      Nat.succ_injective
  have hmajor := hgeom.mul_left C
  apply Summable.of_norm_bounded hmajor
  intro n
  rw [Real.norm_eq_abs]
  unfold platformAbelSineTerm
  rw [abs_mul, abs_mul, abs_pow]
  have hsine := Real.abs_sin_le_one (((n + 1 : ℕ) : ℝ) * theta)
  have hcoefficient :
      |lambda| ^ (n + 1) * |coefficient (n + 1)| ≤
        |lambda| ^ (n + 1) * C :=
    mul_le_mul_of_nonneg_left (hbound _) (pow_nonneg (abs_nonneg _) _)
  calc
    |lambda| ^ (n + 1) * |coefficient (n + 1)| *
          |Real.sin (((n + 1 : ℕ) : ℝ) * theta)| ≤
        (|lambda| ^ (n + 1) * C) * 1 :=
      mul_le_mul hcoefficient hsine (abs_nonneg _)
        (mul_nonneg (pow_nonneg (abs_nonneg _) _) hbound.nonneg)
    _ = C * |lambda| ^ (n + 1) := by ring

/-- After multiplication by `sin theta`, the parity-split second-kind Abel
series is exactly the ordinary positive-frequency conjugate sine series. -/
theorem platformAbelHilbertSeries_mul_sin_eq_tsum_sine
    {coefficient : ℕ → ℝ} {lambda C : ℝ}
    (hlambda : |lambda| < 1)
    (hbound : RealSequenceBoundedBy coefficient C)
    (r theta : ℝ) :
    platformAbelHilbertSeries r coefficient lambda theta * Real.sin theta =
      -(2 / r) *
        ∑' n : ℕ, platformAbelSineTerm coefficient lambda n theta := by
  let g : ℕ → ℝ := fun n ↦
    platformAbelSineTerm coefficient lambda n theta
  have hg : Summable g := by
    simpa only [g] using!
      summable_platformAbelSineTerm (theta := theta) hlambda hbound
  have hevenIndex : Function.Injective (fun m : ℕ ↦ 2 * m) := by
    intro m n h
    exact Nat.mul_left_cancel (by norm_num : 0 < 2) h
  have hoddIndex : Function.Injective (fun m : ℕ ↦ 2 * m + 1) := by
    intro m n h
    have h' : 2 * m = 2 * n := Nat.add_right_cancel h
    exact Nat.mul_left_cancel (by norm_num : 0 < 2) h'
  have hsplit :
      (∑' m : ℕ, g (2 * m + 1)) + (∑' m : ℕ, g (2 * m)) =
        ∑' n : ℕ, g n := by
    rw [add_comm]
    exact tsum_even_add_odd (hg.comp_injective hevenIndex)
      (hg.comp_injective hoddIndex)
  have hevenTerm (m : ℕ) :
      platformAbelEvenHilbertTerm r coefficient lambda m theta *
          Real.sin theta =
        -(2 / r) * g (2 * m + 1) := by
    unfold platformAbelEvenHilbertTerm g platformAbelSineTerm
    calc
      lambda ^ (2 * (m + 1)) * coefficient (2 * (m + 1)) *
            (2 / r * -oddSecondKindAngularMode (m + 1) theta) *
            Real.sin theta =
          -(2 / r) *
            (lambda ^ (2 * (m + 1)) * coefficient (2 * (m + 1)) *
              (oddSecondKindAngularMode (m + 1) theta * Real.sin theta)) := by
        ring
      _ = -(2 / r) *
          (lambda ^ (2 * (m + 1)) * coefficient (2 * (m + 1)) *
            Real.sin (((2 * (m + 1) : ℕ) : ℝ) * theta)) := by
        rw [oddSecondKindAngularMode_mul_sin]
      _ = -(2 / r) *
          (lambda ^ (2 * m + 1 + 1) * coefficient (2 * m + 1 + 1) *
            Real.sin (((2 * m + 1 + 1 : ℕ) : ℝ) * theta)) := by
        have hfreq : 2 * (m + 1) = 2 * m + 1 + 1 := by omega
        rw [hfreq]
  have hoddTerm (m : ℕ) :
      platformAbelOddHilbertTerm r coefficient lambda m theta *
          Real.sin theta =
        -(2 / r) * g (2 * m) := by
    unfold platformAbelOddHilbertTerm g platformAbelSineTerm
    calc
      lambda ^ (2 * m + 1) * coefficient (2 * m + 1) *
            (2 / r * -evenSecondKindAngularMode m theta) * Real.sin theta =
          -(2 / r) *
            (lambda ^ (2 * m + 1) * coefficient (2 * m + 1) *
              (evenSecondKindAngularMode m theta * Real.sin theta)) := by
        ring
      _ = -(2 / r) *
          (lambda ^ (2 * m + 1) * coefficient (2 * m + 1) *
            Real.sin (((2 * m + 1 : ℕ) : ℝ) * theta)) := by
        rw [evenSecondKindAngularMode_mul_sin]
  have heven :=
    (summable_platformAbelEvenHilbertTerm hlambda hbound r theta).hasSum
      |>.mul_right (Real.sin theta)
  have hodd :=
    (summable_platformAbelOddHilbertTerm hlambda hbound r theta).hasSum
      |>.mul_right (Real.sin theta)
  have hevenEq :
      (∑' m : ℕ, platformAbelEvenHilbertTerm
          r coefficient lambda m theta) * Real.sin theta =
        -(2 / r) * ∑' m : ℕ, g (2 * m + 1) := by
    rw [← heven.tsum_eq, ← tsum_mul_left]
    apply tsum_congr
    exact hevenTerm
  have hoddEq :
      (∑' m : ℕ, platformAbelOddHilbertTerm
          r coefficient lambda m theta) * Real.sin theta =
        -(2 / r) * ∑' m : ℕ, g (2 * m) := by
    rw [← hodd.tsum_eq, ← tsum_mul_left]
    apply tsum_congr
    exact hoddTerm
  unfold platformAbelHilbertSeries
  rw [add_mul, hevenEq, hoddEq, ← mul_add, hsplit]

lemma platformAbelFiniteHilbertTransform_eq_range_sums
    (r : ℝ) (coefficient : ℕ → ℝ) (lambda : ℝ) (N : ℕ)
    (theta : ℝ) :
    platformAbelFiniteHilbertTransform r coefficient lambda N theta =
      (∑ m ∈ Finset.range N,
        platformAbelEvenHilbertTerm r coefficient lambda m theta) +
      ∑ m ∈ Finset.range N,
        platformAbelOddHilbertTerm r coefficient lambda m theta := by
  have heven :
      (∑ m : Fin N,
        platformAbelEvenHilbertTerm r coefficient lambda m.1 theta) =
        ∑ m ∈ Finset.range N,
          platformAbelEvenHilbertTerm r coefficient lambda m theta :=
    Fin.sum_univ_eq_sum_range
      (fun m : ℕ ↦ platformAbelEvenHilbertTerm
        r coefficient lambda m theta) N
  have hodd :
      (∑ m : Fin N,
        platformAbelOddHilbertTerm r coefficient lambda m.1 theta) =
        ∑ m ∈ Finset.range N,
          platformAbelOddHilbertTerm r coefficient lambda m theta :=
    Fin.sum_univ_eq_sum_range
      (fun m : ℕ ↦ platformAbelOddHilbertTerm
        r coefficient lambda m theta) N
  change
    (∑ m : Fin N,
        platformAbelEvenHilbertTerm r coefficient lambda m.1 theta) +
      (∑ m : Fin N,
        platformAbelOddHilbertTerm r coefficient lambda m.1 theta) = _
  rw [heven, hodd]

theorem tendsto_platformAbelFiniteHilbertTransform
    {coefficient : ℕ → ℝ} {lambda C : ℝ}
    (hlambda : |lambda| < 1)
    (hbound : RealSequenceBoundedBy coefficient C)
    (r theta : ℝ) :
    Tendsto
      (fun N ↦ platformAbelFiniteHilbertTransform
        r coefficient lambda N theta)
      atTop (nhds (platformAbelHilbertSeries
        r coefficient lambda theta)) := by
  have heven :=
    (summable_platformAbelEvenHilbertTerm hlambda hbound r theta).hasSum
      |>.tendsto_sum_nat
  have hodd :=
    (summable_platformAbelOddHilbertTerm hlambda hbound r theta).hasSum
      |>.tendsto_sum_nat
  have hsum := heven.add hodd
  simpa only [platformAbelFiniteHilbertTransform_eq_range_sums,
    platformAbelHilbertSeries] using! hsum

end

end Erdos1038
