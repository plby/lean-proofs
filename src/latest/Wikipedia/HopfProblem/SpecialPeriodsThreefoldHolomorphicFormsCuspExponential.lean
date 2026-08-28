import Wikipedia.HopfProblem.CuspPuncturedExponentialCharts
import Wikipedia.HopfProblem.ToricSpace
import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# Logarithmic coordinates in the reference cusp chart

The reference triangle has rays `(0,0,1)`, `(1,0,1)`, and `(0,1,1)`.
Its inverse logarithmic coordinates are therefore `(s - ζ₀ - ζ₁, ζ₀, ζ₁)`.
We compute their exponential map and its derivative, including the three
curves meeting the coordinate divisors.
-/

noncomputable section

open scoped ContDiff Matrix

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.HolomorphicForms.Cusp

open CuspUniformization ToricCharts ToricFan ToricSpace

/-- The linear logarithmic coordinates of the reference toric chart. -/
def refLogLinear : LogModel →L[ℂ] CoordinateSpace 3 :=
  ContinuousLinearMap.pi
    ![ContinuousLinearMap.fst ℂ ℂ ComplexPlane₂ -
        (ContinuousLinearMap.proj 0).comp (ContinuousLinearMap.snd ℂ ℂ ComplexPlane₂) -
        (ContinuousLinearMap.proj 1).comp (ContinuousLinearMap.snd ℂ ℂ ComplexPlane₂),
      (ContinuousLinearMap.proj 0).comp (ContinuousLinearMap.snd ℂ ℂ ComplexPlane₂),
      (ContinuousLinearMap.proj 1).comp (ContinuousLinearMap.snd ℂ ℂ ComplexPlane₂)]

@[simp] theorem refLogLinear_apply (p : LogModel) :
    refLogLinear p = ![p.1 - p.2 0 - p.2 1, p.2 0, p.2 1] := by
  ext i
  fin_cases i <;> rfl

/-- The actual exponential in the reference triangle's affine coordinates. -/
def refExp (p : LogModel) : CoordinateSpace 3 :=
  ![exponential (p.1 - p.2 0 - p.2 1), exponential (p.2 0), exponential (p.2 1)]

theorem refExp_apply (p : LogModel) (i : Fin 3) :
    refExp p i = exponential (refLogLinear p i) := by
  fin_cases i <;> rfl

private theorem refExp_eq_exponential_refLog :
    refExp = fun p i => exponential (refLogLinear p i) := by
  funext p i
  exact refExp_apply p i

theorem refExp_mem_torus (p : LogModel) : refExp p ∈ torus := by
  intro i
  rw [refExp_apply]
  exact exponential_ne_zero _

theorem refExp_holomorphic : ContDiff ℂ ω refExp := by
  rw [refExp_eq_exponential_refLog]
  apply contDiff_pi.mpr
  intro i
  exact exponential_holomorphic.comp
    (((ContinuousLinearMap.proj i).comp refLogLinear).contDiff)

/-- The forward toric monomial is the existing total exponential map. -/
theorem monomial_reference_refExp (p : LogModel) :
    monomial referenceTriangle.rays (refExp p) = totalExponentialCoordinates p := by
  have hprod : exponential (p.1 - p.2 0 - p.2 1) * exponential (p.2 0) *
      exponential (p.2 1) = exponential p.1 := by
    rw [← exponential_add, ← exponential_add]
    congr 1
    ring
  ext i
  fin_cases i
  · simp [monomial, referenceTriangle, Triangle.rays, refExp,
      totalExponentialCoordinates, Fin.prod_univ_succ]
  · simp [monomial, referenceTriangle, Triangle.rays, refExp,
      totalExponentialCoordinates, Fin.prod_univ_succ]
  · simpa [monomial, referenceTriangle, Triangle.rays, refExp,
      totalExponentialCoordinates, Fin.prod_univ_succ, mul_assoc] using hprod

theorem monomial_reference_dual_totalExponential (p : LogModel) :
    monomial referenceTriangle.dual (totalExponentialCoordinates p) = refExp p := by
  rw [← monomial_reference_refExp p,
    monomial_mul_on_torus _ _ (refExp_mem_torus p), Triangle.dual_rays, monomial_one]

@[simp] theorem time_refExp (p : LogModel) :
    Triangle.time (refExp p) = exponential p.1 := by
  have h := congrFun (monomial_reference_refExp p) 2
  simpa only [Triangle.monomial_rays_height, totalExponentialCoordinates_two] using h

/-- The complex derivative, with the native normalized exponential factor. -/
def refExpDerivative (p : LogModel) : LogModel →L[ℂ] CoordinateSpace 3 :=
  ContinuousLinearMap.pi fun i =>
    (exponential (refLogLinear p i) * (2 * Real.pi * Complex.I)) •
      ((ContinuousLinearMap.proj i).comp refLogLinear)

theorem refExp_hasFDerivAt (p : LogModel) :
    HasFDerivAt refExp (refExpDerivative p) p := by
  rw [refExp_eq_exponential_refLog]
  exact hasFDerivAt_pi.mpr fun i =>
    (exponential_hasDerivAt (refLogLinear p i)).comp_hasFDerivAt p
      (((ContinuousLinearMap.proj i).comp refLogLinear).hasFDerivAt)

@[simp] theorem fderiv_refExp (p : LogModel) :
    fderiv ℂ refExp p = refExpDerivative p :=
  (refExp_hasFDerivAt p).fderiv

theorem refExpDerivative_apply (p h : LogModel) :
    refExpDerivative p h = (2 * Real.pi * Complex.I : ℂ) •
      ![refExp p 0 * (h.1 - h.2 0 - h.2 1),
        refExp p 1 * h.2 0, refExp p 2 * h.2 1] := by
  ext i
  fin_cases i <;>
    simp [refExpDerivative, refLogLinear, refExp, smul_eq_mul] <;> ring

@[simp] theorem refExp_zero_fibre (s : ℂ) :
    refExp (s, 0) = ![exponential s, 1, 1] := by
  simp [refExp]

theorem refExpDerivative_base (s : ℂ) :
    refExpDerivative (s, 0) (1, 0) =
      ![(2 * Real.pi * Complex.I : ℂ) * exponential s, 0, 0] := by
  rw [refExpDerivative_apply, refExp_zero_fibre]
  ext i
  fin_cases i <;> simp [smul_eq_mul]

theorem refExpDerivative_fibre_zero (s : ℂ) :
    refExpDerivative (s, 0) (0, ![1, 0]) =
      ![-(2 * Real.pi * Complex.I : ℂ) * exponential s,
        2 * Real.pi * Complex.I, 0] := by
  rw [refExpDerivative_apply, refExp_zero_fibre]
  ext i
  fin_cases i <;> simp [smul_eq_mul]

theorem refExpDerivative_fibre_one (s : ℂ) :
    refExpDerivative (s, 0) (0, ![0, 1]) =
      ![-(2 * Real.pi * Complex.I : ℂ) * exponential s,
        0, 2 * Real.pi * Complex.I] := by
  rw [refExpDerivative_apply, refExp_zero_fibre]
  ext i
  fin_cases i <;> simp [smul_eq_mul]

@[simp] theorem refExp_logCurve_one (s : ℂ) :
    refExp (s, ![s, 0]) = ![1, exponential s, 1] := by
  simp [refExp]

@[simp] theorem refExp_logCurve_two (s : ℂ) :
    refExp (s, ![0, s]) = ![1, 1, exponential s] := by
  simp [refExp]

theorem refExpDerivative_logCurve_one (s : ℂ) :
    refExpDerivative (s, ![s, 0]) (1, ![1, 0]) =
      ![0, (2 * Real.pi * Complex.I : ℂ) * exponential s, 0] := by
  rw [refExpDerivative_apply, refExp_logCurve_one]
  ext i
  fin_cases i <;> simp [smul_eq_mul]

theorem refExpDerivative_logCurve_two (s : ℂ) :
    refExpDerivative (s, ![0, s]) (1, ![0, 1]) =
      ![0, 0, (2 * Real.pi * Complex.I : ℂ) * exponential s] := by
  rw [refExpDerivative_apply, refExp_logCurve_two]
  ext i
  fin_cases i <;> simp [smul_eq_mul]

theorem refExp_logCurve_zero_hasDerivAt (s : ℂ) :
    HasDerivAt (fun t : ℂ => refExp (t, 0))
      ![(2 * Real.pi * Complex.I : ℂ) * exponential s, 0, 0] s := by
  simp only [refExp_zero_fibre]
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · simpa [mul_comm] using exponential_hasDerivAt s
  · exact hasDerivAt_const s 1
  · exact hasDerivAt_const s 1

theorem refExp_logCurve_one_hasDerivAt (s : ℂ) :
    HasDerivAt (fun t : ℂ => refExp (t, ![t, 0]))
      ![0, (2 * Real.pi * Complex.I : ℂ) * exponential s, 0] s := by
  simp only [refExp_logCurve_one]
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · exact hasDerivAt_const s 1
  · simpa [mul_comm] using exponential_hasDerivAt s
  · exact hasDerivAt_const s 1

theorem refExp_logCurve_two_hasDerivAt (s : ℂ) :
    HasDerivAt (fun t : ℂ => refExp (t, ![0, t]))
      ![0, 0, (2 * Real.pi * Complex.I : ℂ) * exponential s] s := by
  simp only [refExp_logCurve_two]
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · exact hasDerivAt_const s 1
  · exact hasDerivAt_const s 1
  · simpa [mul_comm] using exponential_hasDerivAt s

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.HolomorphicForms.Cusp
