import Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomologyFourierTopBasic
import Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomologyFourierTopInverse

/-!
# A normalized smooth solver for top Dolbeault forms

For an arbitrary smooth coefficient on the actual period torus, synthesize
the two proved rapid inverse-symbol sequences.  The actual Fourier derivative
and reconstruction theorems give the top Dolbeault equation.  The only
obstruction is the actual probability Haar mean; no closedness is required.
-/

noncomputable section

open MeasureTheory UnitAddTorus

namespace Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomology.FourierTop

open PeriodTorusLineBundleClassification

/-- The explicit two smooth potential coefficients, both with zero constant mode. -/
def potential (p : PeriodDomain) (h : SmoothTorusFunction (Fin 4))
    (i : Fin 2) : SmoothTorusFunction (Fin 4) :=
  smoothFourierSynthesis (potentialCoefficients p (mFourierCoeff h) i)
    (potentialCoefficients_rapid p (mFourierCoeff h) (rapidFourierCoefficients_actual h) i)

theorem mFourierCoeff_potential (p : PeriodDomain) (h : SmoothTorusFunction (Fin 4))
    (i : Fin 2) (k : Fin 4 → ℤ) :
    mFourierCoeff (potential p h i) k = potentialCoefficients p (mFourierCoeff h) i k :=
  mFourierCoeff_smoothFourierSynthesis _ _ k

@[simp]
theorem potential_mean (p : PeriodDomain) (h : SmoothTorusFunction (Fin 4)) (i : Fin 2) :
    torusFourierMean (potential p h i) = 0 := by
  rw [torusFourierMean, mFourierCoeff_potential, potentialCoefficients_zero]

theorem potential_haarMean (p : PeriodDomain) (h : SmoothTorusFunction (Fin 4))
    (i : Fin 2) :
    (∫ x : UnitAddTorus (Fin 4), potential p h i x
      ∂Measure.pi (fun _ : Fin 4 => AddCircle.haarAddCircle)) = 0 :=
  (torusFourierMean_eq_haarIntegral _).symm.trans (potential_mean p h i)

/-- Exact equality of actual smooth functions, proved mode by mode. -/
theorem topDifferential_potential (p : PeriodDomain) (h : SmoothTorusFunction (Fin 4)) :
    topDifferential p (potential p h) = torusRemoveMean h := by
  apply smoothFunction_ext
  apply smoothTorus_apply_eq_of_coeff_eq
  intro k
  rw [mFourierCoeff_topDifferential, mFourierCoeff_potential,
    mFourierCoeff_potential, mFourierCoeff_torusRemoveMean]
  exact potentialCoefficients_equation p (mFourierCoeff h) k

/-- The constructed pair solves the actual top Dolbeault equation at every point. -/
theorem potential_equation (p : PeriodDomain) (h : SmoothTorusFunction (Fin 4))
    (x : UnitAddTorus (Fin 4)) :
    torusDbar p (potential p h 1) 0 x - torusDbar p (potential p h 0) 1 x =
      h x - torusFourierMean h :=
  congrArg (fun f : SmoothTorusFunction (Fin 4) => f x) (topDifferential_potential p h)

/-- The removed constant is literally the probability Haar integral. -/
theorem potential_haar_equation (p : PeriodDomain) (h : SmoothTorusFunction (Fin 4))
    (x : UnitAddTorus (Fin 4)) :
    torusDbar p (potential p h 1) 0 x - torusDbar p (potential p h 0) 1 x =
      h x - ∫ t : UnitAddTorus (Fin 4), h t
        ∂Measure.pi (fun _ : Fin 4 => AddCircle.haarAddCircle) := by
  rw [← torusFourierMean_eq_haarIntegral h]
  exact potential_equation p h x

theorem mean_decomposition (p : PeriodDomain) (h : SmoothTorusFunction (Fin 4))
    (x : UnitAddTorus (Fin 4)) :
    h x = topDifferential p (potential p h) x + torusFourierMean h := by
  rw [topDifferential_potential, torusRemoveMean_apply, sub_add_cancel]

/-- Every top coefficient has a normalized smooth primitive after its mean is removed. -/
theorem exists_normalized_potential (p : PeriodDomain) (h : SmoothTorusFunction (Fin 4)) :
    ∃ a : Fin 2 → SmoothTorusFunction (Fin 4),
      (∀ i, torusFourierMean (a i) = 0) ∧
      ∀ x, torusDbar p (a 1) 0 x - torusDbar p (a 0) 1 x = h x - torusFourierMean h :=
  ⟨potential p h, potential_mean p h, potential_equation p h⟩

/-- Vanishing Haar mean is exactly the obstruction to being an actual top differential. -/
theorem exists_top_primitive_iff (p : PeriodDomain) (h : SmoothTorusFunction (Fin 4)) :
    (∃ a : Fin 2 → SmoothTorusFunction (Fin 4), topDifferential p a = h) ↔
      torusFourierMean h = 0 := by
  constructor
  · rintro ⟨a, rfl⟩
    exact topDifferential_mean p a
  · intro hh
    refine ⟨potential p h, ?_⟩
    apply smoothFunction_ext
    intro x
    simpa only [topDifferential_apply, hh, sub_zero] using potential_equation p h x

theorem exists_normalized_top_primitive_iff (p : PeriodDomain)
    (h : SmoothTorusFunction (Fin 4)) :
    (∃ a : Fin 2 → SmoothTorusFunction (Fin 4),
      (∀ i, torusFourierMean (a i) = 0) ∧ topDifferential p a = h) ↔
      torusFourierMean h = 0 := by
  constructor
  · rintro ⟨a, _, ha⟩
    exact (exists_top_primitive_iff p h).mp ⟨a, ha⟩
  · intro hh
    refine ⟨potential p h, potential_mean p h, ?_⟩
    apply smoothFunction_ext
    intro x
    simpa only [topDifferential_apply, hh, sub_zero] using potential_equation p h x

end Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomology.FourierTop
