import ErdosProblems.Erdos232.CertificateData

open LeanCert.Core
open Filter MeasureTheory Metric intervalIntegral
open scoped ENNReal Topology Interval

namespace Erdos232

theorem besselDerivative_lipschitz (r : ℕ) : LipschitzWith 1 (besselDerivative r) := by
  apply lipschitzWith_of_nnnorm_deriv_le (besselDerivative_differentiable r)
  intro x
  rw [deriv_besselDerivative]
  exact_mod_cast abs_besselDerivative_le_one (r + 1) x

def besselAtRationalPoint (i : Fin 367) (r n : ℕ) (y : ℚ) : IntervalRat :=
  let q : ℚ := i.val * 157 / 50
  let e : ℚ := |y - q| ^ (n + 1) / (n + 1).factorial
  if i.val = 0 then
    widenInterval e (IntervalRat.singleton (besselZeroTransition y r n))
  else
    let T := besselTransition q (y - q) r n
    widenInterval e (linearInterval T.1 T.2 (besselGridStateAt i))

theorem mem_besselAtRationalPoint (i : Fin 367) (r n : ℕ) (y : ℚ) :
    besselDerivative r (y : ℝ) ∈ besselAtRationalPoint i r n y := by
  let q : ℚ := i.val * 157 / 50
  let e : ℚ := |y - q| ^ (n + 1) / (n + 1).factorial
  by_cases hi : i.val = 0
  · have hieq : i = 0 := Fin.ext hi
    subst i
    rw [besselAtRationalPoint]
    simp only [Fin.val_zero, Nat.cast_zero, zero_mul, zero_div, ↓reduceIte]
    apply mem_widenInterval (IntervalRat.mem_singleton (besselZeroTransition y r n))
    have hb := besselTaylor_bound r n 0 (y : ℝ)
    rw [besselTaylor_zero_eq_transition] at hb
    have heQ : 0 ≤ |y - 0| ^ (n + 1) / ((n + 1).factorial : ℚ) := by positivity
    have heAbs : |((|y - 0| ^ (n + 1) / (n + 1).factorial : ℚ) : ℝ)| =
        ((|y - 0| ^ (n + 1) / (n + 1).factorial : ℚ) : ℝ) :=
      abs_of_nonneg (Rat.cast_nonneg.mpr heQ)
    rw [heAbs]
    simpa using hb
  · have hq : q ≠ 0 := by
      dsimp [q]
      positivity
    rw [besselAtRationalPoint]
    simp only [hi, ↓reduceIte]
    have hs := besselGridStateAt_valid i
    have hm0 := mem_linearInterval
      (a := (besselTransition q (y - q) r n).1)
      (b := (besselTransition q (y - q) r n).2) hs.1 hs.2
    have hm : besselTaylor r n (q : ℝ) (y : ℝ) ∈
        linearInterval (besselTransition q (y - q) r n).1
          (besselTransition q (y - q) r n).2 (besselGridStateAt i) := by
      have ht := besselTaylor_eq_transition q (y - q) hq r n
      have hy : (q : ℝ) + ((y - q : ℚ) : ℝ) = (y : ℝ) := by push_cast; ring
      rw [hy] at ht
      rw [ht]
      simpa [q] using hm0
    apply mem_widenInterval hm
    have hb := besselTaylor_bound r n (q : ℝ) (y : ℝ)
    have heQ : 0 ≤ |y - q| ^ (n + 1) / ((n + 1).factorial : ℚ) := by positivity
    have heAbs : |((|y - q| ^ (n + 1) / (n + 1).factorial : ℚ) : ℝ)| =
        ((|y - q| ^ (n + 1) / (n + 1).factorial : ℚ) : ℝ) :=
      abs_of_nonneg (Rat.cast_nonneg.mpr heQ)
    rw [heAbs]
    simpa [q] using hb

def besselNearInterval (i : Fin 367) (r n : ℕ) (y : ℚ)
    (Y : IntervalRat) : IntervalRat :=
  widenInterval (intervalMaxAbs (intervalSub Y (IntervalRat.singleton y)))
    (besselAtRationalPoint i r n y)

theorem mem_besselNearInterval (i : Fin 367) (r n : ℕ) (y : ℚ)
    (Y : IntervalRat) {x : ℝ} (hx : x ∈ Y) :
    besselDerivative r x ∈ besselNearInterval i r n y Y := by
  apply mem_widenInterval (mem_besselAtRationalPoint i r n y)
  have hy : (y : ℝ) ∈ IntervalRat.singleton y := IntervalRat.mem_singleton y
  have hxy : x - (y : ℝ) ∈ intervalSub Y (IntervalRat.singleton y) :=
    IntervalRat.mem_sub hx hy
  have hm := abs_le_intervalMaxAbs hxy
  have hl := (besselDerivative_lipschitz r).dist_le_mul x (y : ℝ)
  simp only [NNReal.coe_one, one_mul, Real.dist_eq] at hl
  have hmax : 0 ≤ (intervalMaxAbs (intervalSub Y (IntervalRat.singleton y)) : ℝ) := by
    exact Rat.cast_nonneg.mpr <| (abs_nonneg _).trans (le_max_left _ _)
  exact (hl.trans hm).trans_eq (abs_of_nonneg hmax).symm

def besselStateAtRationalPoint (i : Fin 367) (n : ℕ) (y : ℚ) :
    IntervalRat × IntervalRat :=
  let q : ℚ := i.val * 157 / 50
  if i.val = 0 then besselIntervalStepZero y n
  else besselIntervalStep q (y - q) n (besselGridStateAt i)

theorem besselStateAtRationalPoint_valid (i : Fin 367) (n : ℕ) (y : ℚ) :
    BesselStateValid y (besselStateAtRationalPoint i n y) := by
  by_cases hi : i.val = 0
  · have hieq : i = 0 := Fin.ext hi
    subst i
    simpa [besselStateAtRationalPoint] using besselIntervalStepZero_valid y n
  · have hq : ((i.val : ℚ) * 157 / 50 : ℚ) ≠ 0 := by positivity
    have hv := besselIntervalStep_valid ((i.val : ℚ) * 157 / 50)
      (y - (i.val : ℚ) * 157 / 50) hq n (besselGridStateAt i)
      (besselGridStateAt_valid i)
    simpa [besselStateAtRationalPoint, hi] using hv

def besselDerivativeNearFromState (y : ℚ) (r : ℕ) (Y : IntervalRat)
    (S : IntervalRat × IntervalRat) : IntervalRat :=
  let D := if y = 0 then IntervalRat.singleton (besselInitial r)
    else linearInterval (besselCoefficients y r).1 (besselCoefficients y r).2 S
  widenInterval (intervalMaxAbs (intervalSub Y (IntervalRat.singleton y))) D

theorem mem_besselDerivativeNearFromState (y : ℚ) (r : ℕ) (Y : IntervalRat)
    (S : IntervalRat × IntervalRat) (hS : BesselStateValid y S)
    {x : ℝ} (hx : x ∈ Y) : besselDerivative r x ∈
      besselDerivativeNearFromState y r Y S := by
  have hpoint : besselDerivative r (y : ℝ) ∈
      if y = 0 then IntervalRat.singleton (besselInitial r)
      else linearInterval (besselCoefficients y r).1 (besselCoefficients y r).2 S := by
    by_cases hy : y = 0
    · subst y
      simp only [↓reduceIte]
      norm_num only [Rat.cast_zero]
      rw [besselDerivative_zero_eq_initial]
      exact IntervalRat.mem_singleton _
    · simp only [hy, ↓reduceIte]
      rw [besselDerivative_eq_coefficients y hy r]
      exact mem_linearInterval hS.1 hS.2
  apply mem_widenInterval hpoint
  have hyI : (y : ℝ) ∈ IntervalRat.singleton y := IntervalRat.mem_singleton y
  have hxy := IntervalRat.mem_sub hx hyI
  have hm := abs_le_intervalMaxAbs hxy
  have hl := (besselDerivative_lipschitz r).dist_le_mul x (y : ℝ)
  simp only [NNReal.coe_one, one_mul, Real.dist_eq] at hl
  have hmax : 0 ≤ (intervalMaxAbs (intervalSub Y (IntervalRat.singleton y)) : ℝ) := by
    exact Rat.cast_nonneg.mpr <| (abs_nonneg _).trans (le_max_left _ _)
  exact (hl.trans hm).trans_eq (abs_of_nonneg hmax).symm

end Erdos232
