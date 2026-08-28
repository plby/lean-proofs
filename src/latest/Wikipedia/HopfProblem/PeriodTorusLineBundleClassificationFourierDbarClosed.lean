import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationFourierDbarCoefficient
import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationFourierDescent
import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationFourierPeriodCoordinates

/-!
# Closed periodic `(0,1)` forms and their actual Fourier coefficients

Closedness is stated using the actual torus Dolbeault derivatives, and its
frequency compatibility is derived by taking actual Fourier coefficients.
Smooth functions periodic under the actual period lattice are descended here
without assuming a torus representative or any coefficient identity.
-/

noncomputable section

open UnitAddTorus
open scoped ContDiff

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassification

/-- The actual coordinate closedness equation for a smooth torus `(0,1)` form. -/
def TorusDbarClosed (p : PeriodDomain) (a : Fin 2 → SmoothTorusFunction (Fin 4)) : Prop :=
  ∀ x, torusDbar p (a 1) 0 x = torusDbar p (a 0) 1 x

theorem TorusDbarClosed.coefficient_compatibility {p : PeriodDomain}
    {a : Fin 2 → SmoothTorusFunction (Fin 4)} (ha : TorusDbarClosed p a)
    (k : Fin 4 → ℤ) :
    dolbeaultSymbol p (integerFrequency k) 0 * mFourierCoeff (a 1) k =
      dolbeaultSymbol p (integerFrequency k) 1 * mFourierCoeff (a 0) k := by
  have he : (torusDbar p (a 1) 0).toContinuousMap =
      (torusDbar p (a 0) 1).toContinuousMap := ContinuousMap.ext ha
  have h : mFourierCoeff (torusDbar p (a 1) 0) k =
      mFourierCoeff (torusDbar p (a 0) 1) k :=
    congrArg (fun f : C(UnitAddTorus (Fin 4), ℂ) => mFourierCoeff f k) he
  simpa only [mFourierCoeff_torusDbar] using h

theorem TorusDbarClosed.coefficient_compatibility_all {p : PeriodDomain}
    {a : Fin 2 → SmoothTorusFunction (Fin 4)} (ha : TorusDbarClosed p a)
    (k : Fin 4 → ℤ) (i j : Fin 2) :
    dolbeaultSymbol p (integerFrequency k) i * mFourierCoeff (a j) k =
      dolbeaultSymbol p (integerFrequency k) j * mFourierCoeff (a i) k := by
  fin_cases i <;> fin_cases j
  · rfl
  · exact ha.coefficient_compatibility k
  · exact (ha.coefficient_compatibility k).symm
  · rfl

theorem torusFourierMean_torusDbar (p : PeriodDomain)
    (f : SmoothTorusFunction (Fin 4)) (i : Fin 2) :
    torusFourierMean (torusDbar p f i) = 0 := by
  rw [torusFourierMean, mFourierCoeff_torusDbar]
  simp [integerFrequency]

/-- Commutation also follows from the proved Fourier multiplier identity and
actual smooth reconstruction, rather than an assumed formal calculus. -/
theorem torusDbar_commute (p : PeriodDomain) (f : SmoothTorusFunction (Fin 4))
    (i j : Fin 2) (x : UnitAddTorus (Fin 4)) :
    torusDbar p (torusDbar p f j) i x = torusDbar p (torusDbar p f i) j x := by
  apply smoothTorus_apply_eq_of_coeff_eq
  intro k
  simp only [mFourierCoeff_torusDbar]
  ring

theorem torusDbarClosed_of_latticeClosed (p : PeriodDomain)
    (f g : ComplexPlane₂ → ℂ) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hpf : ∀ z : ComplexPlane₂, ∀ l : p.lattice, f (z + l) = f z)
    (hpg : ∀ z : ComplexPlane₂, ∀ l : p.lattice, g (z + l) = g z)
    (hclosed : ∀ z, dbarCoordinate g 0 z = dbarCoordinate f 1 z) :
    TorusDbarClosed p
      ![smoothTorusOfLatticePeriodic p f hf hpf, smoothTorusOfLatticePeriodic p g hg hpg] := by
  let fT := smoothTorusOfLatticePeriodic p f hf hpf
  let gT := smoothTorusOfLatticePeriodic p g hg hpg
  have heF : periodTorusLift p fT = f :=
    funext (periodTorusLift_smoothTorusOfLatticePeriodic p f hf hpf)
  have heG : periodTorusLift p gT = g :=
    funext (periodTorusLift_smoothTorusOfLatticePeriodic p g hg hpg)
  intro t
  obtain ⟨x, rfl⟩ := torusQuotient_surjective t
  change torusDbar p gT 0 (torusQuotient x) = torusDbar p fT 1 (torusQuotient x)
  have h := hclosed (PeriodTorusTypeOneOne.periodEquiv p x)
  rw [← heF, ← heG, dbarCoordinate_periodTorusLift, dbarCoordinate_periodTorusLift,
    periodTorusLift_periodEquiv, periodTorusLift_periodEquiv] at h
  exact h

end Wikipedia.HopfProblem.PeriodTorusLineBundleClassification
