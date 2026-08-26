import ErdosProblems.Erdos1038.PlatformAdjointAbelFinite
import Mathlib.Topology.ContinuousMap.Compact

/-!
# Interior Abel cosine series for the platform adjoint

This file begins the infinite-series passage from the paired finite Abel
truncations.  For a bounded coefficient sequence and `|lambda| < 1`, both
parity subseries are absolutely summable.  We define their exact sum and
prove convergence of the finite cosine polynomials and of the endpoint
values used by the correction term.
-/

set_option warningAsError false

open Filter Set
open scoped BigOperators Topology

namespace Erdos1038

noncomputable section

/-- A uniform absolute bound for a real coefficient sequence. -/
def RealSequenceBoundedBy (coefficient : ℕ → ℝ) (C : ℝ) : Prop :=
  ∀ n, |coefficient n| ≤ C

lemma RealSequenceBoundedBy.nonneg
    {coefficient : ℕ → ℝ} {C : ℝ}
    (hbound : RealSequenceBoundedBy coefficient C) : 0 ≤ C := by
  exact (abs_nonneg (coefficient 0)).trans (hbound 0)

/-- Elementary global bound for `U_(2m)(cos theta)`. -/
theorem abs_evenSecondKindAngularMode_le (m : ℕ) (theta : ℝ) :
    |evenSecondKindAngularMode m theta| ≤ 2 * m + 1 := by
  unfold evenSecondKindAngularMode
  have hsum :
      |∑ l ∈ Finset.range m,
          2 * Real.cos (((2 * (l + 1) : ℕ) : ℝ) * theta)| ≤
        ∑ l ∈ Finset.range m,
          |2 * Real.cos (((2 * (l + 1) : ℕ) : ℝ) * theta)| :=
    Finset.abs_sum_le_sum_abs _ _
  calc
    |1 + ∑ l ∈ Finset.range m,
          2 * Real.cos (((2 * (l + 1) : ℕ) : ℝ) * theta)| ≤
        1 + |∑ l ∈ Finset.range m,
          2 * Real.cos (((2 * (l + 1) : ℕ) : ℝ) * theta)| := by
      simpa using! abs_add_le (1 : ℝ)
        (∑ l ∈ Finset.range m,
          2 * Real.cos (((2 * (l + 1) : ℕ) : ℝ) * theta))
    _ ≤ 1 + ∑ l ∈ Finset.range m,
          |2 * Real.cos (((2 * (l + 1) : ℕ) : ℝ) * theta)| :=
      by simpa [add_comm] using! add_le_add_left hsum 1
    _ ≤ 1 + ∑ _l ∈ Finset.range m, (2 : ℝ) := by
      gcongr with l hl
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      nlinarith [Real.abs_cos_le_one
        (((2 * (l + 1) : ℕ) : ℝ) * theta)]
    _ = 2 * m + 1 := by simp; ring

/-- Elementary global bound for `U_(2m-1)(cos theta)`. -/
theorem abs_oddSecondKindAngularMode_le (m : ℕ) (theta : ℝ) :
    |oddSecondKindAngularMode m theta| ≤ 2 * m := by
  unfold oddSecondKindAngularMode
  calc
    |∑ l ∈ Finset.range m,
        2 * Real.cos (((2 * l + 1 : ℕ) : ℝ) * theta)| ≤
      ∑ l ∈ Finset.range m,
        |2 * Real.cos (((2 * l + 1 : ℕ) : ℝ) * theta)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _l ∈ Finset.range m, (2 : ℝ) := by
      gcongr with l hl
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      nlinarith [Real.abs_cos_le_one
        (((2 * l + 1 : ℕ) : ℝ) * theta)]
    _ = 2 * m := by
      simp
      ring

private lemma evenFrequency_injective :
    Function.Injective (fun m : ℕ ↦ 2 * (m + 1)) := by
  intro m n h
  have h' : m + 1 = n + 1 :=
    Nat.mul_left_cancel (by norm_num : 0 < 2) h
  omega

private lemma oddFrequency_injective :
    Function.Injective (fun m : ℕ ↦ 2 * m + 1) := by
  intro m n h
  have h' : 2 * m = 2 * n := Nat.add_right_cancel h
  exact Nat.mul_left_cancel (by norm_num : 0 < 2) h'

private lemma summable_absLambda_evenFrequency
    {lambda : ℝ} (hlambda : |lambda| < 1) :
    Summable (fun m : ℕ ↦ |lambda| ^ (2 * (m + 1))) := by
  exact (summable_geometric_of_lt_one (abs_nonneg lambda) hlambda).comp_injective
    evenFrequency_injective

private lemma summable_absLambda_oddFrequency
    {lambda : ℝ} (hlambda : |lambda| < 1) :
    Summable (fun m : ℕ ↦ |lambda| ^ (2 * m + 1)) := by
  exact (summable_geometric_of_lt_one (abs_nonneg lambda) hlambda).comp_injective
    oddFrequency_injective

lemma summable_platformAbelEvenCoefficient
    {coefficient : ℕ → ℝ} {lambda C : ℝ}
    (hlambda : |lambda| < 1)
    (hbound : RealSequenceBoundedBy coefficient C) :
    Summable (fun m : ℕ ↦
      lambda ^ (2 * (m + 1)) * coefficient (2 * (m + 1))) := by
  have hmajor := (summable_absLambda_evenFrequency hlambda).mul_left C
  apply Summable.of_norm_bounded hmajor
  intro m
  rw [Real.norm_eq_abs, abs_mul, abs_pow]
  calc
    |lambda| ^ (2 * (m + 1)) * |coefficient (2 * (m + 1))| ≤
        |lambda| ^ (2 * (m + 1)) * C :=
      mul_le_mul_of_nonneg_left (hbound _) (pow_nonneg (abs_nonneg lambda) _)
    _ = C * |lambda| ^ (2 * (m + 1)) := by ring

lemma summable_platformAbelOddCoefficient
    {coefficient : ℕ → ℝ} {lambda C : ℝ}
    (hlambda : |lambda| < 1)
    (hbound : RealSequenceBoundedBy coefficient C) :
    Summable (fun m : ℕ ↦
      lambda ^ (2 * m + 1) * coefficient (2 * m + 1)) := by
  have hmajor := (summable_absLambda_oddFrequency hlambda).mul_left C
  apply Summable.of_norm_bounded hmajor
  intro m
  rw [Real.norm_eq_abs, abs_mul, abs_pow]
  calc
    |lambda| ^ (2 * m + 1) * |coefficient (2 * m + 1)| ≤
        |lambda| ^ (2 * m + 1) * C :=
      mul_le_mul_of_nonneg_left (hbound _) (pow_nonneg (abs_nonneg lambda) _)
    _ = C * |lambda| ^ (2 * m + 1) := by ring

def platformAbelEvenCosineTerm
    (coefficient : ℕ → ℝ) (lambda : ℝ) (m : ℕ) (theta : ℝ) : ℝ :=
  2 * (lambda ^ (2 * (m + 1)) * coefficient (2 * (m + 1))) *
    Real.cos (((2 * (m + 1) : ℕ) : ℝ) * theta)

def platformAbelOddCosineTerm
    (coefficient : ℕ → ℝ) (lambda : ℝ) (m : ℕ) (theta : ℝ) : ℝ :=
  2 * (lambda ^ (2 * m + 1) * coefficient (2 * m + 1)) *
    Real.cos (((2 * m + 1 : ℕ) : ℝ) * theta)

lemma continuous_platformAbelEvenCosineTerm
    (coefficient : ℕ → ℝ) (lambda : ℝ) (m : ℕ) :
    Continuous (platformAbelEvenCosineTerm coefficient lambda m) := by
  unfold platformAbelEvenCosineTerm
  fun_prop

lemma continuous_platformAbelOddCosineTerm
    (coefficient : ℕ → ℝ) (lambda : ℝ) (m : ℕ) :
    Continuous (platformAbelOddCosineTerm coefficient lambda m) := by
  unfold platformAbelOddCosineTerm
  fun_prop

lemma summable_platformAbelEvenCosineTerm
    {coefficient : ℕ → ℝ} {lambda C theta : ℝ}
    (hlambda : |lambda| < 1)
    (hbound : RealSequenceBoundedBy coefficient C) :
    Summable (fun m : ℕ ↦
      platformAbelEvenCosineTerm coefficient lambda m theta) := by
  have hmajor :=
    ((summable_absLambda_evenFrequency hlambda).mul_left (2 * C))
  apply Summable.of_norm_bounded hmajor
  intro m
  rw [Real.norm_eq_abs]
  unfold platformAbelEvenCosineTerm
  rw [abs_mul, abs_mul, abs_mul, abs_pow,
    abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hcos := Real.abs_cos_le_one
    (((2 * (m + 1) : ℕ) : ℝ) * theta)
  have hcoefficient :
      |lambda| ^ (2 * (m + 1)) *
          |coefficient (2 * (m + 1))| ≤
        |lambda| ^ (2 * (m + 1)) * C :=
    mul_le_mul_of_nonneg_left (hbound _) (pow_nonneg (abs_nonneg lambda) _)
  have hcoefficientTwo :
      2 * (|lambda| ^ (2 * (m + 1)) *
          |coefficient (2 * (m + 1))|) ≤
        2 * (|lambda| ^ (2 * (m + 1)) * C) :=
    mul_le_mul_of_nonneg_left hcoefficient (by norm_num)
  have hmajorNonneg :
      0 ≤ 2 * (|lambda| ^ (2 * (m + 1)) * C) :=
    mul_nonneg (by norm_num)
      (mul_nonneg (pow_nonneg (abs_nonneg lambda) _) hbound.nonneg)
  calc
    2 * (|lambda| ^ (2 * (m + 1)) *
          |coefficient (2 * (m + 1))|) *
        |Real.cos (((2 * (m + 1) : ℕ) : ℝ) * theta)| ≤
      2 * (|lambda| ^ (2 * (m + 1)) * C) * 1 := by
        exact (mul_le_mul_of_nonneg_right hcoefficientTwo
          (abs_nonneg _)).trans
            (mul_le_mul_of_nonneg_left hcos hmajorNonneg)
    _ = (2 * C) * |lambda| ^ (2 * (m + 1)) := by ring

lemma summable_platformAbelOddCosineTerm
    {coefficient : ℕ → ℝ} {lambda C theta : ℝ}
    (hlambda : |lambda| < 1)
    (hbound : RealSequenceBoundedBy coefficient C) :
    Summable (fun m : ℕ ↦
      platformAbelOddCosineTerm coefficient lambda m theta) := by
  have hmajor :=
    ((summable_absLambda_oddFrequency hlambda).mul_left (2 * C))
  apply Summable.of_norm_bounded hmajor
  intro m
  rw [Real.norm_eq_abs]
  unfold platformAbelOddCosineTerm
  rw [abs_mul, abs_mul, abs_mul, abs_pow,
    abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hcos := Real.abs_cos_le_one
    (((2 * m + 1 : ℕ) : ℝ) * theta)
  have hcoefficient :
      |lambda| ^ (2 * m + 1) * |coefficient (2 * m + 1)| ≤
        |lambda| ^ (2 * m + 1) * C :=
    mul_le_mul_of_nonneg_left (hbound _) (pow_nonneg (abs_nonneg lambda) _)
  have hcoefficientTwo :
      2 * (|lambda| ^ (2 * m + 1) * |coefficient (2 * m + 1)|) ≤
        2 * (|lambda| ^ (2 * m + 1) * C) :=
    mul_le_mul_of_nonneg_left hcoefficient (by norm_num)
  have hmajorNonneg : 0 ≤ 2 * (|lambda| ^ (2 * m + 1) * C) :=
    mul_nonneg (by norm_num)
      (mul_nonneg (pow_nonneg (abs_nonneg lambda) _) hbound.nonneg)
  calc
    2 * (|lambda| ^ (2 * m + 1) *
          |coefficient (2 * m + 1)|) *
        |Real.cos (((2 * m + 1 : ℕ) : ℝ) * theta)| ≤
      2 * (|lambda| ^ (2 * m + 1) * C) * 1 := by
        exact (mul_le_mul_of_nonneg_right hcoefficientTwo
          (abs_nonneg _)).trans
            (mul_le_mul_of_nonneg_left hcos hmajorNonneg)
    _ = (2 * C) * |lambda| ^ (2 * m + 1) := by ring

lemma abs_platformAbelEvenCosineTerm_le
    {coefficient : ℕ → ℝ} {C : ℝ}
    (hbound : RealSequenceBoundedBy coefficient C)
    (lambda : ℝ) (m : ℕ) (theta : ℝ) :
    |platformAbelEvenCosineTerm coefficient lambda m theta| ≤
      (2 * C) * |lambda| ^ (2 * (m + 1)) := by
  unfold platformAbelEvenCosineTerm
  rw [abs_mul, abs_mul, abs_mul, abs_pow,
    abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hcoefficient :
      |lambda| ^ (2 * (m + 1)) *
          |coefficient (2 * (m + 1))| ≤
        |lambda| ^ (2 * (m + 1)) * C :=
    mul_le_mul_of_nonneg_left (hbound _)
      (pow_nonneg (abs_nonneg lambda) _)
  calc
    2 * (|lambda| ^ (2 * (m + 1)) *
          |coefficient (2 * (m + 1))|) *
        |Real.cos (((2 * (m + 1) : ℕ) : ℝ) * theta)| ≤
      2 * (|lambda| ^ (2 * (m + 1)) * C) * 1 := by
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left hcoefficient (by norm_num))
          (Real.abs_cos_le_one _)
          (abs_nonneg _)
          (mul_nonneg (by norm_num)
            (mul_nonneg (pow_nonneg (abs_nonneg lambda) _)
              hbound.nonneg))
    _ = (2 * C) * |lambda| ^ (2 * (m + 1)) := by ring

lemma abs_platformAbelOddCosineTerm_le
    {coefficient : ℕ → ℝ} {C : ℝ}
    (hbound : RealSequenceBoundedBy coefficient C)
    (lambda : ℝ) (m : ℕ) (theta : ℝ) :
    |platformAbelOddCosineTerm coefficient lambda m theta| ≤
      (2 * C) * |lambda| ^ (2 * m + 1) := by
  unfold platformAbelOddCosineTerm
  rw [abs_mul, abs_mul, abs_mul, abs_pow,
    abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hcoefficient :
      |lambda| ^ (2 * m + 1) * |coefficient (2 * m + 1)| ≤
        |lambda| ^ (2 * m + 1) * C :=
    mul_le_mul_of_nonneg_left (hbound _)
      (pow_nonneg (abs_nonneg lambda) _)
  calc
    2 * (|lambda| ^ (2 * m + 1) *
          |coefficient (2 * m + 1)|) *
        |Real.cos (((2 * m + 1 : ℕ) : ℝ) * theta)| ≤
      2 * (|lambda| ^ (2 * m + 1) * C) * 1 := by
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left hcoefficient (by norm_num))
          (Real.abs_cos_le_one _)
          (abs_nonneg _)
          (mul_nonneg (by norm_num)
            (mul_nonneg (pow_nonneg (abs_nonneg lambda) _)
              hbound.nonneg))
    _ = (2 * C) * |lambda| ^ (2 * m + 1) := by ring

def platformAbelEvenCosineContinuousTerm
    (coefficient : ℕ → ℝ) (lambda : ℝ) (m : ℕ) : C(ℝ, ℝ) where
  toFun := platformAbelEvenCosineTerm coefficient lambda m
  continuous_toFun :=
    continuous_platformAbelEvenCosineTerm coefficient lambda m

def platformAbelOddCosineContinuousTerm
    (coefficient : ℕ → ℝ) (lambda : ℝ) (m : ℕ) : C(ℝ, ℝ) where
  toFun := platformAbelOddCosineTerm coefficient lambda m
  continuous_toFun :=
    continuous_platformAbelOddCosineTerm coefficient lambda m

lemma platformAbelEvenCosineContinuousTerm_norm_restrict_le
    {coefficient : ℕ → ℝ} {C : ℝ}
    (hbound : RealSequenceBoundedBy coefficient C)
    (lambda : ℝ) (K : TopologicalSpace.Compacts ℝ) (m : ℕ) :
    ‖(platformAbelEvenCosineContinuousTerm
        coefficient lambda m).restrict K‖ ≤
      (2 * C) * |lambda| ^ (2 * (m + 1)) := by
  apply (ContinuousMap.norm_le _
    (mul_nonneg (mul_nonneg (by norm_num) hbound.nonneg)
      (pow_nonneg (abs_nonneg lambda) _))).2
  intro theta
  change |platformAbelEvenCosineTerm
    coefficient lambda m theta.1| ≤ _
  exact abs_platformAbelEvenCosineTerm_le hbound lambda m theta.1

lemma platformAbelOddCosineContinuousTerm_norm_restrict_le
    {coefficient : ℕ → ℝ} {C : ℝ}
    (hbound : RealSequenceBoundedBy coefficient C)
    (lambda : ℝ) (K : TopologicalSpace.Compacts ℝ) (m : ℕ) :
    ‖(platformAbelOddCosineContinuousTerm
        coefficient lambda m).restrict K‖ ≤
      (2 * C) * |lambda| ^ (2 * m + 1) := by
  apply (ContinuousMap.norm_le _
    (mul_nonneg (mul_nonneg (by norm_num) hbound.nonneg)
      (pow_nonneg (abs_nonneg lambda) _))).2
  intro theta
  change |platformAbelOddCosineTerm
    coefficient lambda m theta.1| ≤ _
  exact abs_platformAbelOddCosineTerm_le hbound lambda m theta.1

theorem summable_platformAbelEvenCosineContinuousTerm_restrict_norm
    {coefficient : ℕ → ℝ} {lambda C : ℝ}
    (hlambda : |lambda| < 1)
    (hbound : RealSequenceBoundedBy coefficient C)
    (K : TopologicalSpace.Compacts ℝ) :
    Summable (fun m : ℕ ↦
      ‖(platformAbelEvenCosineContinuousTerm
        coefficient lambda m).restrict K‖) := by
  have hmajor :=
    (summable_absLambda_evenFrequency hlambda).mul_left (2 * C)
  apply Summable.of_norm_bounded hmajor
  intro m
  rw [Real.norm_of_nonneg (norm_nonneg _)]
  exact platformAbelEvenCosineContinuousTerm_norm_restrict_le
    hbound lambda K m

theorem summable_platformAbelOddCosineContinuousTerm_restrict_norm
    {coefficient : ℕ → ℝ} {lambda C : ℝ}
    (hlambda : |lambda| < 1)
    (hbound : RealSequenceBoundedBy coefficient C)
    (K : TopologicalSpace.Compacts ℝ) :
    Summable (fun m : ℕ ↦
      ‖(platformAbelOddCosineContinuousTerm
        coefficient lambda m).restrict K‖) := by
  have hmajor :=
    (summable_absLambda_oddFrequency hlambda).mul_left (2 * C)
  apply Summable.of_norm_bounded hmajor
  intro m
  rw [Real.norm_of_nonneg (norm_nonneg _)]
  exact platformAbelOddCosineContinuousTerm_norm_restrict_le
    hbound lambda K m

/-- The exact interior Abel cosine series, split by parity. -/
def platformAbelCosineSeries
    (f0 : ℝ) (coefficient : ℕ → ℝ) (lambda theta : ℝ) : ℝ :=
  f0 +
    ∑' m : ℕ, platformAbelEvenCosineTerm coefficient lambda m theta +
    ∑' m : ℕ, platformAbelOddCosineTerm coefficient lambda m theta

/-- Boundary endpoint value of the interior Abel cosine series. -/
def platformAbelEndpointSeriesValue
    (f0 : ℝ) (coefficient : ℕ → ℝ) (lambda : ℝ) : ℝ :=
  f0 +
    ∑' m : ℕ,
      2 * (lambda ^ (2 * (m + 1)) * coefficient (2 * (m + 1))) -
    ∑' m : ℕ,
      2 * (lambda ^ (2 * m + 1) * coefficient (2 * m + 1))

lemma platformAbelFiniteCosinePolynomial_eq_fin_sums
    (f0 : ℝ) (coefficient : ℕ → ℝ) (lambda : ℝ) (N : ℕ)
    (theta : ℝ) :
    platformAbelFiniteCosinePolynomial f0 coefficient lambda N theta =
      f0 +
        ∑ m : Fin N,
          platformAbelEvenCosineTerm coefficient lambda m.1 theta +
        ∑ m : Fin N,
          platformAbelOddCosineTerm coefficient lambda m.1 theta := by
  unfold platformAbelFiniteCosinePolynomial
    finiteEndpointCosinePolynomial platformAbelEvenCosineTerm
    platformAbelOddCosineTerm platformAbelEvenCoefficient
    platformAbelOddCoefficient
  rw [Finset.mul_sum, Finset.mul_sum]
  simp only [mul_assoc]

lemma platformAbelFiniteCosinePolynomial_eq_range_sums
    (f0 : ℝ) (coefficient : ℕ → ℝ) (lambda : ℝ) (N : ℕ)
    (theta : ℝ) :
    platformAbelFiniteCosinePolynomial f0 coefficient lambda N theta =
      f0 +
        ∑ m ∈ Finset.range N,
          platformAbelEvenCosineTerm coefficient lambda m theta +
        ∑ m ∈ Finset.range N,
          platformAbelOddCosineTerm coefficient lambda m theta := by
  have heven :
      (∑ m : Fin N,
        platformAbelEvenCosineTerm coefficient lambda m.1 theta) =
        ∑ m ∈ Finset.range N,
          platformAbelEvenCosineTerm coefficient lambda m theta :=
    Fin.sum_univ_eq_sum_range
      (fun m : ℕ ↦ platformAbelEvenCosineTerm
        coefficient lambda m theta) N
  have hodd :
      (∑ m : Fin N,
        platformAbelOddCosineTerm coefficient lambda m.1 theta) =
        ∑ m ∈ Finset.range N,
          platformAbelOddCosineTerm coefficient lambda m theta :=
    Fin.sum_univ_eq_sum_range
      (fun m : ℕ ↦ platformAbelOddCosineTerm
        coefficient lambda m theta) N
  rw [platformAbelFiniteCosinePolynomial_eq_fin_sums, heven, hodd]

lemma platformAbelFiniteCosinePolynomial_at_pi_eq_range_sums
    (f0 : ℝ) (coefficient : ℕ → ℝ) (lambda : ℝ) (N : ℕ) :
    platformAbelFiniteCosinePolynomial f0 coefficient lambda N Real.pi =
      f0 +
        ∑ m ∈ Finset.range N,
          2 * (lambda ^ (2 * (m + 1)) * coefficient (2 * (m + 1))) -
        ∑ m ∈ Finset.range N,
          2 * (lambda ^ (2 * m + 1) * coefficient (2 * m + 1)) := by
  have heven :
      (∑ m : Fin N,
        2 * (lambda ^ (2 * (m.1 + 1)) *
          coefficient (2 * (m.1 + 1)))) =
        ∑ m ∈ Finset.range N,
          2 * (lambda ^ (2 * (m + 1)) * coefficient (2 * (m + 1))) :=
    Fin.sum_univ_eq_sum_range
      (fun m : ℕ ↦ 2 * (lambda ^ (2 * (m + 1)) *
        coefficient (2 * (m + 1)))) N
  have hodd :
      (∑ m : Fin N,
        2 * (lambda ^ (2 * m.1 + 1) * coefficient (2 * m.1 + 1))) =
        ∑ m ∈ Finset.range N,
          2 * (lambda ^ (2 * m + 1) * coefficient (2 * m + 1)) :=
    Fin.sum_univ_eq_sum_range
      (fun m : ℕ ↦ 2 * (lambda ^ (2 * m + 1) *
        coefficient (2 * m + 1))) N
  rw [platformAbelFiniteCosinePolynomial_at_pi,
    Finset.mul_sum, Finset.mul_sum, heven, hodd]

theorem tendsto_platformAbelFiniteCosinePolynomial
    {coefficient : ℕ → ℝ} {lambda C : ℝ}
    (hlambda : |lambda| < 1)
    (hbound : RealSequenceBoundedBy coefficient C)
    (f0 theta : ℝ) :
    Tendsto
      (fun N ↦ platformAbelFiniteCosinePolynomial
        f0 coefficient lambda N theta)
      atTop (nhds (platformAbelCosineSeries
        f0 coefficient lambda theta)) := by
  have heven :=
    (summable_platformAbelEvenCosineTerm
      (theta := theta) hlambda hbound).hasSum.tendsto_sum_nat
  have hodd :=
    (summable_platformAbelOddCosineTerm
      (theta := theta) hlambda hbound).hasSum.tendsto_sum_nat
  have hconst : Tendsto (fun _N : ℕ ↦ f0) atTop (nhds f0) :=
    tendsto_const_nhds
  have hsum := (hconst.add heven).add hodd
  simpa only [platformAbelFiniteCosinePolynomial_eq_range_sums,
    platformAbelCosineSeries] using! hsum

theorem tendsto_platformAbelFiniteCosinePolynomial_at_pi
    {coefficient : ℕ → ℝ} {lambda C : ℝ}
    (hlambda : |lambda| < 1)
    (hbound : RealSequenceBoundedBy coefficient C)
    (f0 : ℝ) :
    Tendsto
      (fun N ↦ platformAbelFiniteCosinePolynomial
        f0 coefficient lambda N Real.pi)
      atTop (nhds (platformAbelEndpointSeriesValue
        f0 coefficient lambda)) := by
  have hevenSummable :=
    (summable_platformAbelEvenCoefficient hlambda hbound).mul_left 2
  have hoddSummable :=
    (summable_platformAbelOddCoefficient hlambda hbound).mul_left 2
  have heven := hevenSummable.hasSum.tendsto_sum_nat
  have hodd := hoddSummable.hasSum.tendsto_sum_nat
  have hconst : Tendsto (fun _N : ℕ ↦ f0) atTop (nhds f0) :=
    tendsto_const_nhds
  have hsum := (hconst.add heven).sub hodd
  simpa only [platformAbelFiniteCosinePolynomial_at_pi_eq_range_sums,
    platformAbelEndpointSeriesValue] using! hsum

end

end Erdos1038
