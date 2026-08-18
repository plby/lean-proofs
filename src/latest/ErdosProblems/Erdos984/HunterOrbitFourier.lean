/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos984.HunterGeometricSum
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction

/-!
# Fourier expansion along a finite arithmetic orbit
-/

open Set Function MeasureTheory AddCircle
open scoped BigOperators ComplexConjugate

namespace Erdos984

noncomputable section

@[fun_prop] lemma continuous_torusFourier {D : Type*} [Fintype D]
    (xi : D → ℤ) :
    Continuous (fun x : UnitAddTorus D ↦ torusFourier xi x) :=
  (UnitAddTorus.mFourier xi).continuous

lemma integrable_of_continuous_unitAddTorus
    {D : Type*} [Fintype D] {f : UnitAddTorus D → ℂ}
    (hf : Continuous f) : Integrable f := by
  let cf : C(UnitAddTorus D, ℂ) := ⟨f, hf⟩
  let bf := ContinuousMap.linearIsometryBoundedOfCompact
    (UnitAddTorus D) ℂ ℂ cf
  have hbf := BoundedContinuousFunction.integrable
    (volume : Measure (UnitAddTorus D)) bf
  apply hbf.congr
  filter_upwards with x
  exact ContinuousMap.linearIsometryBoundedOfCompact_apply_apply cf x

lemma torusFourier_neg_point {D : Type*} [Fintype D]
    (xi : D → ℤ) (x : UnitAddTorus D) :
    torusFourier xi (-x) = conj (torusFourier xi x) := by
  simp [torusFourier, map_prod]

/-- The sum of the localized kernel along the progression with start `a`
and step `d`, viewed as a function of its translated center. -/
def hunterOrbitKernelSum (D : ℕ) (theta : UnitAddTorus (Fin D))
    (a d : ℕ) (center : UnitAddTorus (Fin D)) : ℂ :=
  ∑ t ∈ Finset.range (hunterX D),
    hunterLocalizedKernel D (center - (a + t * d) • theta)

/-- Fourier coefficient of `hunterOrbitKernelSum`. -/
def hunterOrbitCoeff (D : ℕ) (theta : UnitAddTorus (Fin D))
    (a d : ℕ)
    (q : Fin D → HunterKernelDigit (hunterKernelPower D)) : ℂ :=
  (hunterLocalizedCoeff D q : ℂ) *
    conj (torusFourier (kernelFrequency (hunterKernelPower D) q) (a • theta)) *
    conj (hunterGeomSum D theta d q)

lemma torusFourier_progression_neg
    (D : ℕ) (theta : UnitAddTorus (Fin D)) (a d t : ℕ)
    (q : Fin D → HunterKernelDigit (hunterKernelPower D)) :
    torusFourier (kernelFrequency (hunterKernelPower D) q)
        (-((a + t * d) • theta)) =
      conj (torusFourier (kernelFrequency (hunterKernelPower D) q) (a • theta)) *
        conj (torusFourier (kernelFrequency (hunterKernelPower D) q)
          (t • (d • theta))) := by
  rw [torusFourier_neg_point]
  rw [add_nsmul, mul_nsmul, torusFourier_add_point, map_mul]
  congr 2
  rw [← mul_nsmul, ← mul_nsmul, Nat.mul_comm]

/-- Exact Fourier expansion of the orbit kernel sum. -/
lemma hunterOrbitKernelSum_eq_fourier
    (D : ℕ) (theta : UnitAddTorus (Fin D)) (a d : ℕ)
    (center : UnitAddTorus (Fin D)) :
    hunterOrbitKernelSum D theta a d center =
      ∑ q : Fin D → HunterKernelDigit (hunterKernelPower D),
        hunterOrbitCoeff D theta a d q *
          torusFourier (kernelFrequency (hunterKernelPower D) q) center := by
  classical
  rw [hunterOrbitKernelSum]
  simp_rw [← sum_hunterLocalizedCoeff_torusFourier]
  simp_rw [sub_eq_add_neg, torusFourier_add_point,
    torusFourier_progression_neg]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q _hq
  rw [hunterOrbitCoeff, hunterGeomSum, map_sum]
  rw [Finset.mul_sum]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro t _ht
  ring

/-- Orthogonality for a finite Fourier polynomial with injective frequency
parametrization. -/
lemma integral_fourierPolynomial_mul_conj
    {D Q : Type*} [Fintype D] [Fintype Q]
    (frequency : Q → D → ℤ) (hfrequency : Injective frequency)
    (coeff : Q → ℂ) :
    ∫ x : UnitAddTorus D,
        (∑ q, coeff q * torusFourier (frequency q) x) *
          conj (∑ q, coeff q * torusFourier (frequency q) x) =
      ∑ q, coeff q * conj (coeff q) := by
  classical
  have hinter (q r : Q) : Integrable (fun x : UnitAddTorus D ↦
      (coeff q * conj (coeff r)) *
        (torusFourier (frequency q) x * conj (torusFourier (frequency r) x))) := by
    apply integrable_of_continuous_unitAddTorus
    fun_prop
  calc
    ∫ x : UnitAddTorus D,
        (∑ q, coeff q * torusFourier (frequency q) x) *
          conj (∑ q, coeff q * torusFourier (frequency q) x) =
      ∫ x : UnitAddTorus D, ∑ q, ∑ r,
        (coeff q * conj (coeff r)) *
          (torusFourier (frequency q) x *
            conj (torusFourier (frequency r) x)) := by
      congr 1
      funext x
      simp only [map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro q _hq
      apply Finset.sum_congr rfl
      intro r _hr
      ring
    _ = ∑ q, ∑ r, ∫ x : UnitAddTorus D,
        (coeff q * conj (coeff r)) *
          (torusFourier (frequency q) x *
            conj (torusFourier (frequency r) x)) := by
      rw [integral_finsetSum]
      · apply Finset.sum_congr rfl
        intro q _hq
        rw [integral_finsetSum]
        intro r _hr
        exact hinter q r
      · intro q _hq
        exact integrable_finsetSum Finset.univ fun r _hr ↦ hinter q r
    _ = ∑ q, ∑ r,
        (coeff q * conj (coeff r)) *
          (if frequency q = frequency r then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro q _hq
      apply Finset.sum_congr rfl
      intro r _hr
      rw [integral_const_mul, integral_torusFourier_mul_conj]
    _ = ∑ q, coeff q * conj (coeff q) := by
      apply Finset.sum_congr rfl
      intro q _hq
      rw [Finset.sum_eq_single q]
      · simp
      · intro r _hr hrq
        rw [if_neg]
        · ring
        · exact fun h ↦ hrq (hfrequency h).symm
      · simp

lemma integral_hunterOrbitKernelSum_mul_conj
    (D : ℕ) (theta : UnitAddTorus (Fin D)) (a d : ℕ) :
    ∫ center : UnitAddTorus (Fin D),
        hunterOrbitKernelSum D theta a d center *
          conj (hunterOrbitKernelSum D theta a d center) =
      ∑ q : Fin D → HunterKernelDigit (hunterKernelPower D),
        hunterOrbitCoeff D theta a d q *
          conj (hunterOrbitCoeff D theta a d q) := by
  simp_rw [hunterOrbitKernelSum_eq_fourier]
  exact integral_fourierPolynomial_mul_conj _
    (kernelFrequency_injective (hunterKernelPower D)) _

lemma integrable_hunterOrbitKernelSum
    (D : ℕ) (theta : UnitAddTorus (Fin D)) (a d : ℕ) :
    Integrable (hunterOrbitKernelSum D theta a d) := by
  have hp : Integrable (fun center : UnitAddTorus (Fin D) ↦
    ∑ q : Fin D → HunterKernelDigit (hunterKernelPower D),
      hunterOrbitCoeff D theta a d q *
        torusFourier (kernelFrequency (hunterKernelPower D) q) center) := by
    apply integrable_of_continuous_unitAddTorus
    fun_prop
  apply hp.congr
  filter_upwards with center
  exact (hunterOrbitKernelSum_eq_fourier D theta a d center).symm

@[simp] lemma hunterOrbitCoeff_zero
    (D : ℕ) (theta : UnitAddTorus (Fin D)) (a d : ℕ) :
    hunterOrbitCoeff D theta a d
      (kernelZeroTuple (D := Fin D) (hunterKernelPower D)) =
      (hunterKernelMean D / 2 : ℝ) * hunterX D := by
  have hstart : torusFourier
      (kernelFrequency (hunterKernelPower D)
        (kernelZeroTuple (D := Fin D) (hunterKernelPower D))) (a • theta) = 1 := by
    rw [kernelFrequency_zeroTuple]
    exact torusFourier_zero _
  have hsum : hunterGeomSum D theta d
      (kernelZeroTuple (D := Fin D) (hunterKernelPower D)) = hunterX D := by
    rw [hunterGeomSum]
    simp only [kernelFrequency_zeroTuple]
    have hzero (x : UnitAddTorus (Fin D)) :
        torusFourier (0 : Fin D → ℤ) x = 1 := torusFourier_zero x
    simp_rw [hzero]
    simp
  rw [hunterOrbitCoeff, hunterLocalizedCoeff_zero, hstart, hsum]
  simp

lemma integral_hunterOrbitKernelSum
    (D : ℕ) (theta : UnitAddTorus (Fin D)) (a d : ℕ) :
    ∫ center : UnitAddTorus (Fin D), hunterOrbitKernelSum D theta a d center =
      (hunterKernelMean D / 2 : ℝ) * hunterX D := by
  classical
  simp_rw [hunterOrbitKernelSum_eq_fourier]
  rw [integral_finsetSum]
  · rw [Finset.sum_eq_single
      (kernelZeroTuple (D := Fin D) (hunterKernelPower D))]
    · rw [integral_const_mul, integral_torusFourier]
      simp
    · intro q _hq hq
      rw [integral_const_mul, integral_torusFourier, if_neg]
      · ring
      · intro hzero
        apply hq
        apply kernelFrequency_injective (hunterKernelPower D)
        simpa using hzero
    · simp
  · intro q _hq
    apply (integrable_of_continuous_unitAddTorus
      (continuous_torusFourier (kernelFrequency (hunterKernelPower D) q))).const_mul

lemma normSq_hunterOrbitCoeff
    (D : ℕ) (theta : UnitAddTorus (Fin D)) (a d : ℕ)
    (q : Fin D → HunterKernelDigit (hunterKernelPower D)) :
    Complex.normSq (hunterOrbitCoeff D theta a d q) =
      hunterLocalizedCoeff D q ^ 2 *
        Complex.normSq (hunterGeomSum D theta d q) := by
  rw [hunterOrbitCoeff, Complex.normSq_mul, Complex.normSq_mul,
    Complex.normSq_ofReal, Complex.normSq_conj, Complex.normSq_conj,
    Complex.normSq_eq_norm_sq, norm_torusFourier]
  ring

lemma integral_normSq_hunterOrbitKernelSum
    (D : ℕ) (theta : UnitAddTorus (Fin D)) (a d : ℕ) :
    ∫ center : UnitAddTorus (Fin D),
        Complex.normSq (hunterOrbitKernelSum D theta a d center) =
      ∑ q : Fin D → HunterKernelDigit (hunterKernelPower D),
        hunterLocalizedCoeff D q ^ 2 *
          Complex.normSq (hunterGeomSum D theta d q) := by
  have h := integral_hunterOrbitKernelSum_mul_conj D theta a d
  simp_rw [Complex.mul_conj, normSq_hunterOrbitCoeff] at h
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  convert h using 1
  push_cast
  rfl

end

end Erdos984
