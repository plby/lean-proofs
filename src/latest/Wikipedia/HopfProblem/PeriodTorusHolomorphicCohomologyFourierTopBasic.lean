import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationFourierDbarSolver

/-!
# The actual top Dolbeault differential on a period torus

A smooth `(0,1)` form is represented by its two actual torus coefficients.
Its top differential is the difference of the actual Dolbeault derivatives,
not a formal operation on Fourier sequences.  Its Fourier multiplier and
vanishing probability Haar integral follow from the proved derivative theorem.
-/

noncomputable section

open MeasureTheory UnitAddTorus

namespace Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomology.FourierTop

open PeriodTorusLineBundleClassification

/-- Equality of the actual values determines a bundled smooth torus function. -/
theorem smoothFunction_ext {d : Type*} [Fintype d]
    {f g : SmoothTorusFunction d} (h : ∀ x, f x = g x) : f = g := by
  cases f with
  | mk f hf =>
    cases g with
    | mk g hg =>
      have hfg : f = g := ContinuousMap.ext h
      cases hfg
      rfl

/-- The actual smooth coefficient of the top Dolbeault differential. -/
def topDifferential (p : PeriodDomain)
    (a : Fin 2 → SmoothTorusFunction (Fin 4)) : SmoothTorusFunction (Fin 4) where
  toContinuousMap := (torusDbar p (a 1) 0).toContinuousMap -
    (torusDbar p (a 0) 1).toContinuousMap
  smooth_lift := (torusDbar p (a 1) 0).smooth_lift.sub
    (torusDbar p (a 0) 1).smooth_lift

@[simp]
theorem topDifferential_apply (p : PeriodDomain)
    (a : Fin 2 → SmoothTorusFunction (Fin 4)) (x : UnitAddTorus (Fin 4)) :
    topDifferential p a x = torusDbar p (a 1) 0 x - torusDbar p (a 0) 1 x := rfl

/-- The top symbol is the row `(-symbol₁, symbol₀)`. -/
theorem mFourierCoeff_topDifferential (p : PeriodDomain)
    (a : Fin 2 → SmoothTorusFunction (Fin 4)) (k : Fin 4 → ℤ) :
    mFourierCoeff (topDifferential p a) k =
      dolbeaultSymbol p (integerFrequency k) 0 * mFourierCoeff (a 1) k -
        dolbeaultSymbol p (integerFrequency k) 1 * mFourierCoeff (a 0) k := by
  change mFourierCoeff ((torusDbar p (a 1) 0).toContinuousMap -
    (torusDbar p (a 0) 1).toContinuousMap) k = _
  rw [torusFourierCoeff_sub]
  rw [mFourierCoeff_torusDbar, mFourierCoeff_torusDbar]

/-- Every top differential has zero actual zero-mode coefficient. -/
@[simp]
theorem topDifferential_mean (p : PeriodDomain)
    (a : Fin 2 → SmoothTorusFunction (Fin 4)) :
    torusFourierMean (topDifferential p a) = 0 := by
  rw [torusFourierMean, mFourierCoeff_topDifferential]
  simp

/-- In particular the actual probability Haar integral of a top differential
vanishes. -/
theorem topDifferential_haarMean (p : PeriodDomain)
    (a : Fin 2 → SmoothTorusFunction (Fin 4)) :
    (∫ x : UnitAddTorus (Fin 4), topDifferential p a x
      ∂Measure.pi (fun _ : Fin 4 => AddCircle.haarAddCircle)) = 0 :=
  (torusFourierMean_eq_haarIntegral _).symm.trans (topDifferential_mean p a)

theorem dbar_difference_haarMean (p : PeriodDomain)
    (a : Fin 2 → SmoothTorusFunction (Fin 4)) :
    (∫ x : UnitAddTorus (Fin 4), torusDbar p (a 1) 0 x - torusDbar p (a 0) 1 x
      ∂Measure.pi (fun _ : Fin 4 => AddCircle.haarAddCircle)) = 0 :=
  topDifferential_haarMean p a

/-- The two consecutive actual Dolbeault differentials compose to zero. -/
theorem topDifferential_torusDbar (p : PeriodDomain)
    (f : SmoothTorusFunction (Fin 4)) (x : UnitAddTorus (Fin 4)) :
    topDifferential p (fun i => torusDbar p f i) x = 0 :=
  sub_eq_zero.mpr (torusDbar_commute p f 0 1 x)

end Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomology.FourierTop
