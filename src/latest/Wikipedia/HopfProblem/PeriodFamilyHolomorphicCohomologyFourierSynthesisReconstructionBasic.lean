import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyFourierSynthesisSeriesBasic
import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationFourierDbarSeriesCoefficient

/-!
# Exact coefficients and reconstruction on the original family

The literal parameterized Fourier series has the supplied Haar coefficients
on every actual base fibre. Conversely, the coefficients of an original
smooth family reconstruct that same function, using the proved smooth-torus
Fourier reconstruction. No alternate quotient or assumed Fourier identity is
introduced.
-/

noncomputable section

open TopologicalSpace UnitAddTorus

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.FourierSynthesis

open PeriodTorusLineBundleClassification FourierParameter

variable {U : Opens ℂ} {c d : Coefficients}

/-- Recovery uses the literal Haar Fourier coefficient of the original slice. -/
theorem mFourierCoeff_synthesis (hc : SmoothRapidCoefficients U c)
    (b : U) (k : Frequency) :
    mFourierCoeff (fun t => synthesis c (b, t)) k = c k (b : ℂ) := by
  have hslice : (fun t => synthesis c (b, t)) =
      (continuousFourierSynthesis (fun m => c m (b : ℂ)) :
        UnitAddTorus (Fin 4) → ℂ) := by
    funext t
    exact synthesis_eq_continuousFourierSynthesis hc b t
  rw [hslice]
  exact mFourierCoeff_continuousFourierSynthesis _ (hc.summable b) k

/-- The original Haar coefficients reconstruct the actual original family. -/
theorem synthesis_coefficientValue (f : SmoothFamily U (Fin 4))
    (x : U × UnitAddTorus (Fin 4)) :
    synthesis f.coefficientValue x = f x := by
  rcases x with ⟨b, t⟩
  simp only [synthesis, SmoothFamily.coefficientValue_apply]
  change (∑' k, mFourierCoeff (f.slice b) k * mFourier k t) = f.slice b t
  simpa only [smul_eq_mul] using smoothTorus_fourier_tsum (f.slice b) t

/-- The corresponding literal sum on the real covering space reconstructs
the original lift, on the original open base. -/
theorem jointSynthesis_coefficientValue (f : SmoothFamily U (Fin 4))
    (b : U) (x : Fin 4 → ℝ) :
    jointSynthesis f.coefficientValue ((b : ℂ), x) = f (b, torusQuotient x) := by
  rw [jointSynthesis_apply]
  exact synthesis_coefficientValue f (b, torusQuotient x)

/-- Coefficients are determined on the given base by the actual synthesized family.
No assertion is made about their unused values outside that base. -/
theorem synthesis_eq_iff (hc : SmoothRapidCoefficients U c)
    (hd : SmoothRapidCoefficients U d) :
    synthesis (U := U) c = synthesis (U := U) d ↔
      ∀ (b : U) (k : Frequency), c k (b : ℂ) = d k (b : ℂ) := by
  constructor
  · intro h b k
    rw [← mFourierCoeff_synthesis hc b k, ← mFourierCoeff_synthesis hd b k, h]
  · intro h
    funext x
    apply tsum_congr
    intro k
    rw [h x.1 k]

/-- The actual Haar coefficients separate genuinely smooth original families. -/
theorem smoothFamily_ext_coefficients {f g : SmoothFamily U (Fin 4)}
    (h : ∀ (b : U) (k : Frequency),
      f.coefficientValue k (b : ℂ) = g.coefficientValue k (b : ℂ)) :
    (f : U × UnitAddTorus (Fin 4) → ℂ) = g := by
  funext x
  rw [← synthesis_coefficientValue f x, ← synthesis_coefficientValue g x]
  exact congrFun ((synthesis_eq_iff (smoothRapidCoefficients_actual f)
    (smoothRapidCoefficients_actual g)).mpr h) x

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.FourierSynthesis
