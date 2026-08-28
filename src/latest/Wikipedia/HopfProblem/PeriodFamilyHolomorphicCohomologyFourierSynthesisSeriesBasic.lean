import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyFourierSynthesisModes
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyFourierSynthesisCoefficientsPointwise
import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationFourierDbarSeriesContinuous

/-!
# The literal Fourier sum over the original parameter space

These are the actual pointwise Fourier series on the real covering space
and its original unit-torus quotient. The proved rapid coefficient bounds
give absolute summability at every base point. The ambient representative
of the quotient sum agrees with the covering sum on the given open base;
no regularity across the boundary of that base is asserted.
-/

noncomputable section

open TopologicalSpace UnitAddTorus

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.FourierSynthesis

open PeriodTorusLineBundleClassification

/-- The literal pointwise Fourier sum on the joint real covering space. -/
def jointSynthesis (c : Coefficients) (x : ℂ × (Fin 4 → ℝ)) : ℂ :=
  ∑' k, jointFourierMode c k x

/-- The same literal series on the original base and the unit torus. -/
def synthesis {U : Opens ℂ} (c : Coefficients) (x : U × UnitAddTorus (Fin 4)) : ℂ :=
  ∑' k, c k (x.1 : ℂ) * mFourier k x.2

@[simp] theorem norm_jointFourierMode (c : Coefficients) (k : Frequency)
    (x : ℂ × (Fin 4 → ℝ)) : ‖jointFourierMode c k x‖ = ‖c k x.1‖ := by
  simp only [jointFourierMode, norm_mul, mFourier_norm_apply, mul_one]

/-- Every actual mode series is absolutely summable over the original base. -/
theorem summable_norm_jointFourierMode {U : Opens ℂ} {c : Coefficients}
    (hc : SmoothRapidCoefficients U c) (x : ℂ × (Fin 4 → ℝ)) (hx : x.1 ∈ U) :
    Summable (fun k => ‖jointFourierMode c k x‖) := by
  simpa only [norm_jointFourierMode] using hc.summable_norm ⟨x.1, hx⟩

theorem summable_jointFourierMode {U : Opens ℂ} {c : Coefficients}
    (hc : SmoothRapidCoefficients U c) (x : ℂ × (Fin 4 → ℝ)) (hx : x.1 ∈ U) :
    Summable (fun k => jointFourierMode c k x) :=
  (summable_norm_jointFourierMode hc x hx).of_norm

/-- Each original torus slice equals the actual Banach-space Fourier sum. -/
theorem synthesis_eq_continuousFourierSynthesis {U : Opens ℂ} {c : Coefficients}
    (hc : SmoothRapidCoefficients U c) (b : U) (t : UnitAddTorus (Fin 4)) :
    synthesis c (b, t) = continuousFourierSynthesis (fun k => c k (b : ℂ)) t :=
  (continuousFourierSynthesis_apply _ (hc.summable b) t).symm

/-- The covering representative and original quotient sum agree literally
on the original base. -/
theorem ambientLift_synthesis_eqOn {U : Opens ℂ} (c : Coefficients) :
    Set.EqOn (FourierParameter.ambientLift (synthesis (U := U) c))
      (jointSynthesis c) (Smooth.baseProductDomain U (Fin 4 → ℝ)) := by
  intro x hx
  change x.1 ∈ U at hx
  simp only [FourierParameter.ambientLift, dif_pos hx, synthesis, jointSynthesis,
    jointFourierMode]

@[simp] theorem jointSynthesis_apply {U : Opens ℂ} (c : Coefficients)
    (b : U) (x : Fin 4 → ℝ) :
    jointSynthesis c ((b : ℂ), x) = synthesis c (b, torusQuotient x) := rfl

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.FourierSynthesis
