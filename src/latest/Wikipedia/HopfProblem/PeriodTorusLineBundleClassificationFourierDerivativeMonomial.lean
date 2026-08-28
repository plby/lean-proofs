import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.MeasureTheory.Group.Integral

/-!
# Translation and differentiation of torus Fourier monomials

These formulas use the probability Haar measure already built into
`UnitAddTorus.mFourierCoeff`. A positive translation multiplies the Fourier
coefficient by the positive Fourier character.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassification

variable {d : Type*} [Fintype d]

@[simp]
theorem mFourier_zero_argument (k : d → ℤ) :
    UnitAddTorus.mFourier k (0 : UnitAddTorus d) = 1 := by
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, Pi.zero_apply,
    fourier_eval_zero, Finset.prod_const_one]

@[simp]
theorem mFourier_norm_apply (k : d → ℤ) (x : UnitAddTorus d) :
    ‖UnitAddTorus.mFourier k x‖ = 1 := by
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, norm_prod,
    fourier_apply, Circle.norm_coe, Finset.prod_const_one]

theorem mFourier_add_argument (k : d → ℤ) (x y : UnitAddTorus d) :
    UnitAddTorus.mFourier k (x + y) =
      UnitAddTorus.mFourier k x * UnitAddTorus.mFourier k y := by
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, Pi.add_apply,
    fourier_apply, zsmul_add, AddCircle.toCircle_add, Circle.coe_mul,
    Finset.prod_mul_distrib]

theorem mFourier_neg_argument (k : d → ℤ) (x : UnitAddTorus d) :
    UnitAddTorus.mFourier k (-x) = UnitAddTorus.mFourier (-k) x := by
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, Pi.neg_apply,
    fourier_apply, smul_neg, neg_smul]

theorem mFourier_mul_neg (k : d → ℤ) (x : UnitAddTorus d) :
    UnitAddTorus.mFourier k x * UnitAddTorus.mFourier (-k) x = 1 := by
  rw [← UnitAddTorus.mFourier_add, add_neg_cancel, UnitAddTorus.mFourier_zero]
  rfl

/-- The exact exponential formula on the real universal cover. -/
theorem mFourier_real_argument (k : d → ℤ) (x : d → ℝ) :
    UnitAddTorus.mFourier k (fun i => (x i : UnitAddCircle)) =
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
        ∑ i, (k i : ℂ) * (x i : ℂ)) := by
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, fourier_coe_apply,
    Complex.ofReal_one, div_one]
  rw [← Complex.exp_sum]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Translation of a genuine Haar Fourier coefficient, with the positive sign. -/
theorem mFourierCoeff_translate (f : C(UnitAddTorus d, ℂ))
    (a : UnitAddTorus d) (k : d → ℤ) :
    UnitAddTorus.mFourierCoeff (fun t => f (t + a)) k =
      UnitAddTorus.mFourier k a * UnitAddTorus.mFourierCoeff f k := by
  change (∫ t, UnitAddTorus.mFourier (-k) t * f (t + a)) =
    UnitAddTorus.mFourier k a * ∫ t, UnitAddTorus.mFourier (-k) t * f t
  have hpoint (t : UnitAddTorus d) :
      UnitAddTorus.mFourier (-k) t * f (t + a) =
        UnitAddTorus.mFourier k a *
          (UnitAddTorus.mFourier (-k) (t + a) * f (t + a)) := by
    rw [mFourier_add_argument]
    calc
      _ = (UnitAddTorus.mFourier k a * UnitAddTorus.mFourier (-k) a) *
          (UnitAddTorus.mFourier (-k) t * f (t + a)) := by
        rw [mFourier_mul_neg, one_mul]
      _ = _ := by ring
  calc
    _ = ∫ t, UnitAddTorus.mFourier k a *
        (UnitAddTorus.mFourier (-k) (t + a) * f (t + a)) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall hpoint
    _ = ∫ t, UnitAddTorus.mFourier k a *
        (UnitAddTorus.mFourier (-k) t * f t) :=
      integral_add_right_eq_self (μ := (volume : Measure (UnitAddTorus d)))
        (fun t => UnitAddTorus.mFourier k a * (UnitAddTorus.mFourier (-k) t * f t)) a
    _ = _ := integral_const_mul _ _

/-- The derivative along an arbitrary real line in the covering space. -/
theorem hasDerivAt_mFourier_line (k : d → ℤ) (v : d → ℝ) (s : ℝ) :
    HasDerivAt
      (fun r : ℝ => UnitAddTorus.mFourier k (fun i => (r * v i : UnitAddCircle)))
      ((2 * (Real.pi : ℂ) * Complex.I * ∑ i, (k i : ℂ) * (v i : ℂ)) *
        UnitAddTorus.mFourier k (fun i => (s * v i : UnitAddCircle))) s := by
  let A : ℂ := 2 * (Real.pi : ℂ) * Complex.I * ∑ i, (k i : ℂ) * (v i : ℂ)
  have hformula (r : ℝ) :
      UnitAddTorus.mFourier k (fun i => (r * v i : UnitAddCircle)) =
        Complex.exp (A * (r : ℂ)) := by
    rw [mFourier_real_argument]
    congr 1
    simp only [A, Complex.ofReal_mul, Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  simp_rw [hformula]
  change HasDerivAt (fun r : ℝ => Complex.exp (A * (r : ℂ)))
    (A * Complex.exp (A * (s : ℂ))) s
  convert (((hasDerivAt_id (s : ℂ)).const_mul A).cexp).comp_ofReal using 1 <;>
    simp [mul_comm]

end Wikipedia.HopfProblem.PeriodTorusLineBundleClassification
