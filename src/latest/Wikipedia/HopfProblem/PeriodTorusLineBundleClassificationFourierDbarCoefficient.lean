import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationFourierDbarBasic

/-!
# Actual Fourier coefficients and the constant mode

Orthogonality of the actual Haar Fourier basis gives the coefficients of
monomials and constants. The proved smooth Fourier reconstruction gives
coefficient injectivity and identifies subtraction of the actual zero mode.
-/

noncomputable section

open UnitAddTorus
open scoped ContDiff

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassification

variable {d : Type*} [Fintype d]

theorem mFourierCoeff_mFourier (m k : d → ℤ) :
    mFourierCoeff (mFourier m) k = if k = m then 1 else 0 := by
  classical
  calc
    mFourierCoeff (mFourier m) k = mFourierCoeff (mFourierLp 2 m) k :=
      (mFourierCoeff_toLp (mFourier m) k).symm
    _ = mFourierBasis.repr (mFourierLp 2 m) k := (mFourierBasis_repr _ k).symm
    _ = _ := by
      rw [HilbertBasis.repr_apply_apply, coe_mFourierBasis]
      split_ifs with hk
      · subst k
        rw [inner_self_eq_norm_sq_to_K, (orthonormal_mFourier (d := d)).1 m]
        simp
      · rw [(orthonormal_mFourier (d := d)).2 hk]

theorem mFourierCoeff_const (c : ℂ) (k : d → ℤ) :
    mFourierCoeff (fun _ : UnitAddTorus d => c) k = if k = 0 then c else 0 := by
  classical
  have he : (fun _ : UnitAddTorus d => c) =
      (fun x => c * mFourier (0 : d → ℤ) x) := by
    funext x
    simp only [mFourier_zero, ContinuousMap.one_apply, mul_one]
  rw [he, torusFourierCoeff_const_mul, mFourierCoeff_mFourier]
  split_ifs <;> simp

theorem smoothTorus_eq_of_coeff_eq (f g : SmoothTorusFunction d)
    (h : ∀ k : d → ℤ, mFourierCoeff f k = mFourierCoeff g k) :
    f.toContinuousMap = g.toContinuousMap := by
  apply ContinuousMap.ext
  intro x
  rw [← smoothTorus_fourier_tsum f x, ← smoothTorus_fourier_tsum g x]
  apply tsum_congr
  intro k
  rw [h k]

theorem smoothTorus_apply_eq_of_coeff_eq (f g : SmoothTorusFunction d)
    (h : ∀ k : d → ℤ, mFourierCoeff f k = mFourierCoeff g k) (x : UnitAddTorus d) :
    f x = g x :=
  congrArg (fun F : C(UnitAddTorus d, ℂ) => F x) (smoothTorus_eq_of_coeff_eq f g h)

/-- The mean is the actual zero Fourier coefficient, not a chosen constant. -/
def torusFourierMean (f : SmoothTorusFunction d) : ℂ := mFourierCoeff f 0

def smoothTorusConst (c : ℂ) : SmoothTorusFunction d where
  toContinuousMap := ContinuousMap.const _ c
  smooth_lift := contDiff_const

@[simp]
theorem smoothTorusConst_apply (c : ℂ) (x : UnitAddTorus d) :
    smoothTorusConst c x = c := rfl

/-- Subtract exactly the zero Fourier mode from the actual smooth function. -/
def torusRemoveMean (f : SmoothTorusFunction d) : SmoothTorusFunction d where
  toContinuousMap := f.toContinuousMap -
    (smoothTorusConst (d := d) (torusFourierMean f)).toContinuousMap
  smooth_lift := f.smooth_lift.sub contDiff_const

@[simp]
theorem torusRemoveMean_apply (f : SmoothTorusFunction d) (x : UnitAddTorus d) :
    torusRemoveMean f x = f x - torusFourierMean f := rfl

theorem mFourierCoeff_torusRemoveMean (f : SmoothTorusFunction d) (k : d → ℤ) :
    mFourierCoeff (torusRemoveMean f) k = mFourierCoeff f k -
      if k = 0 then mFourierCoeff f 0 else 0 := by
  change mFourierCoeff (f.toContinuousMap -
    (smoothTorusConst (d := d) (torusFourierMean f)).toContinuousMap) k = _
  rw [torusFourierCoeff_sub]
  change mFourierCoeff f k - mFourierCoeff (fun _ : UnitAddTorus d => torusFourierMean f) k = _
  rw [mFourierCoeff_const]
  rfl

end Wikipedia.HopfProblem.PeriodTorusLineBundleClassification
