import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyFourierSynthesisModes
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyFourierSynthesisOpNorm
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyFourierSynthesisCoefficients

/-!
# Compact-uniform bounds for the genuine joint mode derivatives

Every fixed-direction derivative has a summable majorant by the proved
closure of the original coefficient class. A finite real basis then
provides a summable bound for the actual operator norms, uniformly over
each compact subset of the original base and every covering coordinate.
-/

noncomputable section

open TopologicalSpace UnitAddTorus

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.FourierSynthesis

open PeriodTorusLineBundleClassification

/-- The actual derivatives have compact-uniform summable operator-norm
bounds; no derivative estimate is an additional input. -/
theorem jointFourierModeDerivative_majorant {U : Opens ℂ} {c : Coefficients}
    (hc : SmoothRapidCoefficients U c) (K : Set U) (hK : IsCompact K) :
    ∃ u : Frequency → ℝ, (∀ k, 0 ≤ u k) ∧ Summable u ∧
      ∀ b ∈ K, ∀ t : Fin 4 → ℝ, ∀ k,
        ‖jointFourierModeDerivative c k ((b : ℂ), t)‖ ≤ u k := by
  obtain ⟨u, hnonneg, hsum, hbound⟩ := exists_summable_opNorm_bound
    (K ×ˢ (Set.univ : Set (Fin 4 → ℝ)))
    (fun k (x : U × (Fin 4 → ℝ)) =>
      jointFourierModeDerivative c k ((x.1 : ℂ), x.2)) (by
        intro v
        obtain ⟨u, hnonneg, hsum, hbound⟩ :=
          (hc.jointDerivative v).majorant [] K hK 0
        refine ⟨u, hnonneg, hsum, ?_⟩
        intro x hx k
        rw [jointFourierModeDerivative_apply_coefficients]
        simp only [norm_mul, mFourier_norm_apply, mul_one]
        simpa only [pow_zero, one_mul, FourierParameter.iteratedDirectionalDerivativeList]
          using hbound x.1 hx.1 k)
  refine ⟨u, hnonneg, hsum, ?_⟩
  intro b hb t k
  exact hbound (b, t) ⟨hb, Set.mem_univ t⟩ k

/-- At each original base point the actual derivative series converges
in the space of continuous real linear maps. -/
theorem summable_jointFourierModeDerivative {U : Opens ℂ} {c : Coefficients}
    (hc : SmoothRapidCoefficients U c) (x : ℂ × (Fin 4 → ℝ)) (hx : x.1 ∈ U) :
    Summable (fun k => jointFourierModeDerivative c k x) := by
  let b : U := ⟨x.1, hx⟩
  obtain ⟨u, _, hsum, hbound⟩ := jointFourierModeDerivative_majorant hc {b}
    isCompact_singleton
  exact Summable.of_norm_bounded hsum (fun k => hbound b (Set.mem_singleton b) x.2 k)

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.FourierSynthesis
