import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationFourierDbarClosed
import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationFourierDbarInverse
import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationFourierDbarSeriesSmooth

/-!
# The normalized periodic Dolbeault primitive

The constant part of a smooth torus function is its integral for the product
probability Haar measure.  Rapid Fourier synthesis of the constructed inverse
coefficients gives a smooth primitive, with that constant part removed.
-/

noncomputable section

open MeasureTheory UnitAddTorus

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassification

/-- The zero Fourier coefficient is the actual probability Haar integral. -/
theorem torusFourierMean_eq_haarIntegral {d : Type*} [Fintype d]
    (f : SmoothTorusFunction d) :
    torusFourierMean f =
      ∫ t : UnitAddTorus d, f t ∂Measure.pi (fun _ : d => AddCircle.haarAddCircle) := by
  simp only [torusFourierMean, mFourierCoeff, neg_zero, mFourier_zero,
    ContinuousMap.one_apply, one_smul]
  rfl

/-- The explicit zero-mean potential obtained by dividing every nonzero
Fourier mode and synthesizing the resulting proved rapid sequence. -/
def torusDbarPotential (p : PeriodDomain)
    (a : Fin 2 → SmoothTorusFunction (Fin 4)) : SmoothTorusFunction (Fin 4) :=
  smoothFourierSynthesis
    (dolbeaultPotentialCoefficients p (fun i => mFourierCoeff (a i)))
    (dolbeaultPotentialCoefficients_rapid p (fun i => mFourierCoeff (a i))
      (rapidFourierCoefficients_actual (a 0))
      (rapidFourierCoefficients_actual (a 1)))

theorem mFourierCoeff_torusDbarPotential (p : PeriodDomain)
    (a : Fin 2 → SmoothTorusFunction (Fin 4)) (k : Fin 4 → ℤ) :
    mFourierCoeff (torusDbarPotential p a) k =
      dolbeaultPotentialCoefficients p (fun i => mFourierCoeff (a i)) k :=
  mFourierCoeff_smoothFourierSynthesis _ _ k

@[simp]
theorem torusFourierMean_torusDbarPotential (p : PeriodDomain)
    (a : Fin 2 → SmoothTorusFunction (Fin 4)) :
    torusFourierMean (torusDbarPotential p a) = 0 := by
  rw [torusFourierMean, mFourierCoeff_torusDbarPotential,
    dolbeaultPotentialCoefficients_zero]

/-- The constructed potential solves the actual Dolbeault equations, with
exactly the actual Haar means removed from the given closed form. -/
theorem torusDbar_torusDbarPotential (p : PeriodDomain)
    (a : Fin 2 → SmoothTorusFunction (Fin 4)) (ha : TorusDbarClosed p a)
    (i : Fin 2) (x : UnitAddTorus (Fin 4)) :
    torusDbar p (torusDbarPotential p a) i x = a i x - torusFourierMean (a i) := by
  change torusDbar p (torusDbarPotential p a) i x = torusRemoveMean (a i) x
  apply smoothTorus_apply_eq_of_coeff_eq
  intro k
  rw [mFourierCoeff_torusDbar, mFourierCoeff_torusDbarPotential,
    mFourierCoeff_torusRemoveMean]
  exact dolbeaultPotentialCoefficients_mul p (fun j => mFourierCoeff (a j))
    ha.coefficient_compatibility i k

theorem exists_torus_dbar_primitive (p : PeriodDomain)
    (a : Fin 2 → SmoothTorusFunction (Fin 4)) (ha : TorusDbarClosed p a) :
    ∃ u : SmoothTorusFunction (Fin 4), torusFourierMean u = 0 ∧
      ∀ (i : Fin 2) (x : UnitAddTorus (Fin 4)),
        torusDbar p u i x = a i x - torusFourierMean (a i) :=
  ⟨torusDbarPotential p a, torusFourierMean_torusDbarPotential p a,
    torusDbar_torusDbarPotential p a ha⟩

end Wikipedia.HopfProblem.PeriodTorusLineBundleClassification
