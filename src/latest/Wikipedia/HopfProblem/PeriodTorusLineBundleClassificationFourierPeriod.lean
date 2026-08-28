import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationFourierBasic
import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationFourierDerivative
import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationFourierSymbolMode

/-!
# Fourier differentiation in the actual complex period coordinates

The inverse period isomorphism transports genuine smooth torus functions to
the complex covering plane. The Dolbeault operator is assembled from actual
directional derivatives, and its Fourier multiplier follows from the proved
directional coefficient formula.
-/

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassification

open Complex UnitAddTorus
open scoped BigOperators ContDiff

/-- The standard torus monomial is the actual exponential mode in complex
period coordinates. -/
theorem mFourier_period_argument (p : PeriodDomain) (k : Fin 4 → ℤ)
    (z : ComplexPlane₂) :
    mFourier k (torusQuotient ((PeriodTorusTypeOneOne.periodEquiv p).symm z)) =
      frequencyMode p (integerFrequency k) z := by
  change mFourier k
    (fun i => (((PeriodTorusTypeOneOne.periodEquiv p).symm z) i : UnitAddCircle)) = _
  rw [mFourier_real_argument, frequencyMode_apply, frequencyFunctional_apply]
  simp only [integerFrequency_apply, Complex.ofReal_sum, Complex.ofReal_mul,
    Complex.ofReal_intCast]

@[simp]
theorem torusQuotient_integerFrequency (n : Fin 4 → ℤ) :
    torusQuotient (integerFrequency n) = 0 := by
  ext i
  simp [torusQuotient, integerFrequency]

@[simp]
theorem periodEquiv_symm_periodVector (p : PeriodDomain) (n : Fin 4 → ℤ) :
    (PeriodTorusTypeOneOne.periodEquiv p).symm (p.periodVector n) =
      integerFrequency n := by
  rw [← PeriodTorusTypeOneOne.periodEquiv_integer_eq_periodVector,
    LinearEquiv.symm_apply_apply]
  rfl

/-- The actual lift from the marked real torus to the complex period plane. -/
noncomputable def periodTorusLift (p : PeriodDomain)
    (f : SmoothTorusFunction (Fin 4)) (z : ComplexPlane₂) : ℂ :=
  torusLift f ((PeriodTorusTypeOneOne.periodEquiv p).symm z)

@[simp]
theorem periodTorusLift_apply (p : PeriodDomain) (f : SmoothTorusFunction (Fin 4))
    (z : ComplexPlane₂) :
    periodTorusLift p f z =
      f (torusQuotient ((PeriodTorusTypeOneOne.periodEquiv p).symm z)) := rfl

theorem contDiff_periodTorusLift (p : PeriodDomain) (f : SmoothTorusFunction (Fin 4)) :
    ContDiff ℝ ∞ (periodTorusLift p f) :=
  f.smooth_lift.comp
    (PeriodTorusTypeOneOne.periodEquiv p).symm.toLinearMap.toContinuousLinearMap.contDiff

@[simp]
theorem periodTorusLift_periodEquiv (p : PeriodDomain)
    (f : SmoothTorusFunction (Fin 4)) (x : Fin 4 → ℝ) :
    periodTorusLift p f (PeriodTorusTypeOneOne.periodEquiv p x) = torusLift f x := by
  simp only [periodTorusLift, LinearEquiv.symm_apply_apply]

theorem periodTorusLift_add_integer_period (p : PeriodDomain)
    (f : SmoothTorusFunction (Fin 4)) (z : ComplexPlane₂) (n : Fin 4 → ℤ) :
    periodTorusLift p f (z + p.periodVector n) = periodTorusLift p f z := by
  simp only [periodTorusLift_apply, map_add, periodEquiv_symm_periodVector,
    torusQuotient_add, torusQuotient_integerFrequency, add_zero]

/-- The transported smooth function is periodic under the genuine period
lattice, without any extra periodicity assumption. -/
theorem periodTorusLift_add_lattice (p : PeriodDomain)
    (f : SmoothTorusFunction (Fin 4)) (z a : ComplexPlane₂) (ha : a ∈ p.lattice) :
    periodTorusLift p f (z + a) = periodTorusLift p f z := by
  obtain ⟨n, rfl⟩ := (p.mem_lattice_iff a).mp ha
  exact periodTorusLift_add_integer_period p f z n

theorem fderiv_periodTorusLift_apply (p : PeriodDomain)
    (f : SmoothTorusFunction (Fin 4)) (z w : ComplexPlane₂) :
    fderiv ℝ (periodTorusLift p f) z w =
      fderiv ℝ (torusLift f) ((PeriodTorusTypeOneOne.periodEquiv p).symm z)
        ((PeriodTorusTypeOneOne.periodEquiv p).symm w) := by
  let e : ComplexPlane₂ →L[ℝ] (Fin 4 → ℝ) :=
    (PeriodTorusTypeOneOne.periodEquiv p).symm.toLinearMap.toContinuousLinearMap
  have hf := ((contDiff_infty_iff_fderiv.mp f.smooth_lift).1 (e z)).hasFDerivAt
  exact congrArg (fun L : ComplexPlane₂ →L[ℝ] ℂ => L w)
    (hf.comp z e.hasFDerivAt).fderiv

/-- The real coordinate direction in the actual lattice marking. -/
noncomputable def periodRealDirection (p : PeriodDomain) (i : Fin 2) : Fin 4 → ℝ :=
  (PeriodTorusTypeOneOne.periodEquiv p).symm (Pi.single i 1)

/-- The imaginary coordinate direction in the actual lattice marking. -/
noncomputable def periodImagDirection (p : PeriodDomain) (i : Fin 2) : Fin 4 → ℝ :=
  (PeriodTorusTypeOneOne.periodEquiv p).symm (I • Pi.single i 1)

/-- The genuine torus Dolbeault coordinate derivative, bundled with smoothness. -/
noncomputable def torusDbar (p : PeriodDomain) (f : SmoothTorusFunction (Fin 4))
    (i : Fin 2) : SmoothTorusFunction (Fin 4) where
  toContinuousMap := (1 / (2 : ℂ)) •
    ((torusDirectionalDerivative f (periodRealDirection p i)).toContinuousMap +
      I • (torusDirectionalDerivative f (periodImagDirection p i)).toContinuousMap)
  smooth_lift := by
    change ContDiff ℝ ∞ (fun x => (1 / (2 : ℂ)) *
      (torusLift (torusDirectionalDerivative f (periodRealDirection p i)) x +
        I * torusLift (torusDirectionalDerivative f (periodImagDirection p i)) x))
    exact contDiff_const.mul
      ((torusDirectionalDerivative f (periodRealDirection p i)).smooth_lift.add
        (contDiff_const.mul
          (torusDirectionalDerivative f (periodImagDirection p i)).smooth_lift))

@[simp]
theorem torusDbar_apply (p : PeriodDomain) (f : SmoothTorusFunction (Fin 4))
    (i : Fin 2) (t : UnitAddTorus (Fin 4)) :
    torusDbar p f i t =
      (torusDirectionalDerivative f (periodRealDirection p i) t +
        I * torusDirectionalDerivative f (periodImagDirection p i) t) / 2 := by
  change (1 / (2 : ℂ)) * (_ + I * _) = _
  ring

/-- Lifting the torus operator gives the actual complex-coordinate Dolbeault
combination of the real Fréchet derivative. -/
theorem periodTorusLift_torusDbar (p : PeriodDomain) (f : SmoothTorusFunction (Fin 4))
    (i : Fin 2) (z : ComplexPlane₂) :
    periodTorusLift p (torusDbar p f i) z =
      (fderiv ℝ (periodTorusLift p f) z (Pi.single i 1) +
        I * fderiv ℝ (periodTorusLift p f) z (I • Pi.single i 1)) / 2 := by
  rw [fderiv_periodTorusLift_apply, fderiv_periodTorusLift_apply,
    periodTorusLift_apply, torusDbar_apply]
  change (torusLift (torusDirectionalDerivative f (periodRealDirection p i))
      ((PeriodTorusTypeOneOne.periodEquiv p).symm z) +
    I * torusLift (torusDirectionalDerivative f (periodImagDirection p i))
      ((PeriodTorusTypeOneOne.periodEquiv p).symm z)) / 2 = _
  rw [torusDirectionalDerivative_lift, torusDirectionalDerivative_lift]
  rfl

/-- The exact Dolbeault coefficient identity, derived from the actual
directional derivatives and the actual Haar Fourier coefficients. -/
theorem mFourierCoeff_torusDbar (p : PeriodDomain) (f : SmoothTorusFunction (Fin 4))
    (i : Fin 2) (k : Fin 4 → ℤ) :
    mFourierCoeff (torusDbar p f i) k =
      dolbeaultSymbol p (integerFrequency k) i * mFourierCoeff f k := by
  have hRe : (∑ j : Fin 4, (k j : ℂ) * (periodRealDirection p i j : ℂ)) =
      (frequencyFunctional p (integerFrequency k) (Pi.single i 1) : ℂ) := by
    simp [frequencyFunctional_apply, integerFrequency, periodRealDirection]
  have hIm : (∑ j : Fin 4, (k j : ℂ) * (periodImagDirection p i j : ℂ)) =
      (frequencyFunctional p (integerFrequency k) (I • Pi.single i 1) : ℂ) := by
    simp [frequencyFunctional_apply, integerFrequency, periodImagDirection]
  change mFourierCoeff ((1 / (2 : ℂ)) •
    ((torusDirectionalDerivative f (periodRealDirection p i)).toContinuousMap +
      I • (torusDirectionalDerivative f (periodImagDirection p i)).toContinuousMap)) k = _
  rw [torusFourierCoeff_smul, torusFourierCoeff_add, torusFourierCoeff_smul]
  rw [mFourierCoeff_torusDirectionalDerivative, mFourierCoeff_torusDirectionalDerivative,
    hRe, hIm, dolbeaultSymbol_apply]
  simp only [smul_eq_mul]
  ring_nf
  simp only [Complex.I_sq]
  ring

end Wikipedia.HopfProblem.PeriodTorusLineBundleClassification
