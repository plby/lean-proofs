/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.InitialBandsTypicality
import ErdosProblems.Erdos207.InitialPatternAnalyticData
import ErdosProblems.Erdos207.InitialPatternCoupledNibble

/-! # Exact typicality of an initial coupled outcome on the constructed power vortex -/

namespace Erdos207

open Finset
open scoped Classical NNReal

noncomputable section

def IsInitialTypicalPatternOutcome
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (q h b B k t : ℕ) (H : SimpleGraph V) (bank : TripleSystemOn V) (W : Vortex V ell) (S : GreedyStateOn V) : Prop :=
  let S₀ := absorberGreedyInitialState (absorberErdosForbiddenConfigurationsOn q bank) (outsideAvailableTriangles H bank)
  let E : ℝ := (initialResidualPairs H).card
  let a := initialErdosTrajectoryCoefficient V (S₀.available.card : ℝ)
  let time := ksssDensityHorizon E (1 / (t : ℝ) ^ b)
  IsInitialPatternOutcome q h b B k t H bank W S ∧
    IsIterationTypical W 0
      (graphDifference (graphDifference (SimpleGraph.completeGraph V) H) (coveredGraph S.chosen))
      S.available (Real.toNNReal (ksssEdgeDensity E time))
      (Real.toNNReal (Real.exp (-ksssPoissonExponent (ksssOrders q) a time)))
      (17 / (t : ℝ≥0)) h

theorem InitialPowerVortexPackage.initial_pattern_outcome_typical
    {q h n ell t rootPower step : ℕ}
    (P : InitialPowerVortexPackage q h n ell t rootPower step)
    (b B k : ℕ) (S : GreedyStateOn (Fin n))
    (hS : IsInitialPatternOutcome q h b B k t P.H P.B P.W S)
    (hb : 1 ≤ b) (ht : 1 ≤ t) (hh : h ≤ t)
    (hc : powerAbsorberCoefficient q ≤ t)
    (hlarge : 6 * t ^ initialSupportPower rootPower + 4 ≤ n)
    (hroot : b * h + h ^ 2 + 2 ≤ rootPower)
    (hexp : Real.exp (∑ d ∈ ksssOrders q, initialErdosCoefficientBound q d) ≤ t) :
    IsInitialTypicalPatternOutcome q h b B k t P.H P.B P.W S := by
  let S₀ := absorberGreedyInitialState (absorberErdosForbiddenConfigurationsOn q P.B) (outsideAvailableTriangles P.H P.B)
  let E : ℝ := (initialResidualPairs P.H).card
  let a := initialErdosTrajectoryCoefficient (Fin n) (S₀.available.card : ℝ)
  let time := ksssDensityHorizon E (1 / (t : ℝ) ^ b)
  obtain ⟨hdegree, _, hbank⟩ := P.support_power_bounds hc
  have hdata := initial_absorber_pattern_analytic_data q (t ^ initialSupportPower rootPower)
    P.H P.B hdegree hbank (by simpa only [Fintype.card_fin] using hlarge)
  have htR : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have htime := ksssDensityHorizon_bounds E (1 / (t : ℝ) ^ b) hdata.1 (by positivity)
    ((div_le_one (by positivity : (0 : ℝ) < (t : ℝ) ^ b)).mpr (one_le_pow₀ htR))
  refine ⟨hS, ?_⟩
  exact initial_bands_isIterationTypical P.W P.H S q b B t h a (initialErdosCoefficientBound q) E time
    ht hb hh (Nat.cast_nonneg _) htime.1 (htime.2.1 time le_rfl) hdata.2.2.1 hdata.2.2.2 hexp
    P.nonempty (fun i ↦ (pow_le_pow_right₀ htR hroot).trans (by exact_mod_cast P.level_card_lower i))
    hS.2.1 hS.2.2

end

end Erdos207
