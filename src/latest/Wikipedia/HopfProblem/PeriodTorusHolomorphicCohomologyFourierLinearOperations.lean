import Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomologyFourierLinearBasic

/-!
# Complex linearity of the genuine Fourier Dolbeault operator

The derivative is the previously constructed actual coordinate
antiholomorphic derivative. Linearity follows from its proved Fourier
coefficients and genuine reconstruction, with no formal-symbol replacement.
-/

noncomputable section

open UnitAddTorus

namespace Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomology.FourierLinear

open PeriodTorusLineBundleClassification

variable {d : Type*} [Fintype d]

theorem coefficient_add (f g : SmoothTorusFunction d) (k : d → ℤ) :
    mFourierCoeff (f + g) k = mFourierCoeff f k + mFourierCoeff g k :=
  (coefficientLinear k).map_add f g

theorem coefficient_smul (c : ℂ) (f : SmoothTorusFunction d) (k : d → ℤ) :
    mFourierCoeff (c • f) k = c * mFourierCoeff f k :=
  (coefficientLinear k).map_smul c f

theorem coefficient_zero (k : d → ℤ) :
    mFourierCoeff (0 : SmoothTorusFunction d) k = 0 := (coefficientLinear k).map_zero

theorem dbar_add (p : PeriodDomain) (f g : SmoothTorusFunction (Fin 4)) (i : Fin 2) :
    torusDbar p (f + g) i = torusDbar p f i + torusDbar p g i := by
  apply smooth_ext
  apply smoothTorus_apply_eq_of_coeff_eq
  intro k
  rw [mFourierCoeff_torusDbar, coefficient_add, coefficient_add,
    mFourierCoeff_torusDbar, mFourierCoeff_torusDbar, mul_add]

theorem dbar_smul (p : PeriodDomain) (c : ℂ) (f : SmoothTorusFunction (Fin 4))
    (i : Fin 2) : torusDbar p (c • f) i = c • torusDbar p f i := by
  apply smooth_ext
  apply smoothTorus_apply_eq_of_coeff_eq
  intro k
  rw [mFourierCoeff_torusDbar, coefficient_smul, coefficient_smul,
    mFourierCoeff_torusDbar, mul_left_comm]

/-- Each genuine coordinate derivative is complex linear on actual smooth functions. -/
def dbarLinear (p : PeriodDomain) (i : Fin 2) :
    SmoothTorusFunction (Fin 4) →ₗ[ℂ] SmoothTorusFunction (Fin 4) where
  toFun f := torusDbar p f i
  map_add' f g := dbar_add p f g i
  map_smul' c f := dbar_smul p c f i

@[simp] theorem dbarLinear_apply (p : PeriodDomain) (i : Fin 2)
    (f : SmoothTorusFunction (Fin 4)) : dbarLinear p i f = torusDbar p f i := rfl

theorem dbar_constant (p : PeriodDomain) (c : ℂ) (i : Fin 2) :
    dbarLinear p i (constantLinear c) = 0 := by
  apply smooth_ext
  apply smoothTorus_apply_eq_of_coeff_eq
  intro k
  rw [dbarLinear_apply, mFourierCoeff_torusDbar, coefficient_zero]
  change dolbeaultSymbol p (integerFrequency k) i *
    mFourierCoeff (fun _ : UnitAddTorus (Fin 4) => c) k = 0
  rw [mFourierCoeff_const]
  split_ifs with hk
  · subst k
    simp
  · exact mul_zero _

/-- All genuine coordinate derivatives have zero probability Haar mean. -/
@[simp] theorem mean_dbar (p : PeriodDomain) (i : Fin 2)
    (f : SmoothTorusFunction (Fin 4)) : meanLinear (dbarLinear p i f) = 0 :=
  torusFourierMean_torusDbar p f i

end Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomology.FourierLinear
