import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyFourierSynthesisSeriesBasic

/-!
# Linearity of the actual parameterized Fourier sum

All sums below are the literal series on the original base and unit torus.
The addition and finite-sum identities use the proved absolute convergence
of the original coefficient families. Multiplication by a base function is
factored out at each original base point, with no extra regularity premise.
-/

noncomputable section

open TopologicalSpace UnitAddTorus

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.FourierSynthesis

open PeriodTorusLineBundleClassification

variable {U : Opens ℂ} {c d : Coefficients}

/-- The original series on every quotient slice is genuinely summable. -/
theorem summable_synthesisModes (hc : SmoothRapidCoefficients U c)
    (x : U × UnitAddTorus (Fin 4)) :
    Summable (fun k => c k (x.1 : ℂ) * mFourier k x.2) :=
  (continuousFourierSynthesis_hasSum_apply _ (hc.summable x.1) x.2).summable

@[simp] theorem synthesis_zero (x : U × UnitAddTorus (Fin 4)) :
    synthesis (0 : Coefficients) x = 0 := by
  simp only [synthesis, Pi.zero_apply, zero_mul, tsum_zero]

/-- Addition commutes with the original series by its proved convergence. -/
theorem synthesis_add (hc : SmoothRapidCoefficients U c)
    (hd : SmoothRapidCoefficients U d) (x : U × UnitAddTorus (Fin 4)) :
    synthesis (c + d) x = synthesis c x + synthesis d x := by
  simp only [synthesis, Pi.add_apply, add_mul]
  exact Summable.tsum_add (summable_synthesisModes hc x) (summable_synthesisModes hd x)

/-- Any scalar depending only on the base factors out of the literal slice series. -/
theorem synthesis_base_mul (g : ℂ → ℂ) (c : Coefficients)
    (x : U × UnitAddTorus (Fin 4)) :
    synthesis (fun k z => g z * c k z) x = g (x.1 : ℂ) * synthesis c x := by
  simp only [synthesis, mul_assoc, tsum_mul_left]

theorem synthesis_const_mul (a : ℂ) (c : Coefficients)
    (x : U × UnitAddTorus (Fin 4)) :
    synthesis (fun k z => a * c k z) x = a * synthesis c x :=
  synthesis_base_mul (fun _ => a) c x

@[simp] theorem synthesis_smul (a : ℂ) (c : Coefficients)
    (x : U × UnitAddTorus (Fin 4)) :
    synthesis (a • c) x = a • synthesis c x := by
  simp only [synthesis, Pi.smul_apply, smul_eq_mul, mul_assoc, tsum_mul_left]

@[simp] theorem synthesis_neg (c : Coefficients)
    (x : U × UnitAddTorus (Fin 4)) :
    synthesis (-c) x = -synthesis c x := by
  simp only [synthesis, Pi.neg_apply, neg_mul, tsum_neg]

theorem synthesis_sub (hc : SmoothRapidCoefficients U c)
    (hd : SmoothRapidCoefficients U d) (x : U × UnitAddTorus (Fin 4)) :
    synthesis (c - d) x = synthesis c x - synthesis d x := by
  simp only [synthesis, Pi.sub_apply, sub_mul]
  exact Summable.tsum_sub (summable_synthesisModes hc x) (summable_synthesisModes hd x)

/-- Every finite combination is synthesized termwise, using the actual summability. -/
theorem synthesis_finset_sum {ι : Type*} (s : Finset ι) (c : ι → Coefficients)
    (hc : ∀ i ∈ s, SmoothRapidCoefficients U (c i))
    (x : U × UnitAddTorus (Fin 4)) :
    synthesis (∑ i ∈ s, c i) x = ∑ i ∈ s, synthesis (c i) x := by
  simp only [synthesis, Finset.sum_apply, Finset.sum_mul]
  exact Summable.tsum_finsetSum (fun i hi => summable_synthesisModes (hc i hi) x)

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.FourierSynthesis
