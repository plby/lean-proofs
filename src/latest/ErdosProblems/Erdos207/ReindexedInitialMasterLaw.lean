/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.InitialResidualCompression
import ErdosProblems.Erdos207.VortexReindexInitialBands

/-! # Initial master laws on a retained vortex, with their original error bound -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem InitialPowerVortexPackage.residual_master_of_initial_typical_support
    {q h n ell length t rootPower step b B k : ℕ} {C error : ℝ≥0}
    (P : InitialPowerVortexPackage q h n ell t rootPower step) (hadmissible : Admissible n)
    (law : FiniteLaw (GreedyStateOn (Fin n)))
    (W : Vortex (Fin n) length)
    (hsupport : law.SupportedOn (IsInitialTypicalPatternOutcome q h b B k t P.H P.B W))
    (hgraph : IsInitialGraphProductBound law (fun S ↦ S.chosen)
      (graphDifference (SimpleGraph.completeGraph (Fin n)) P.H)
      (Real.toNNReal (ksssEdgeDensity (initialResidualPairs P.H).card
        (ksssDensityHorizon (initialResidualPairs P.H).card (1 / (t : ℝ) ^ b)))) C error) :
    let G₀ := graphDifference (SimpleGraph.completeGraph (Fin n)) P.H
    let F := absorberErdosForbiddenConfigurationsOn q P.B
    let S₀ := absorberGreedyInitialState F (outsideAvailableTriangles P.H P.B)
    let E : ℝ := (initialResidualPairs P.H).card
    let time := ksssDensityHorizon E (1 / (t : ℝ) ^ b)
    let p := Real.toNNReal (ksssEdgeDensity E time)
    let eta := Real.toNNReal (Real.exp (-ksssPoissonExponent (ksssOrders q)
      (initialErdosTrajectoryCoefficient (Fin n) (S₀.available.card : ℝ)) time))
    IsResidualMasterIterationGood law W 0 G₀ F
      (fun S ↦ graphDifference G₀ (coveredGraph S.chosen)) (fun S ↦ S.available)
      (fun S ↦ S.chosen) (fun _ ↦ ∅) p eta (17 / (t : ℝ≥0))
      C error h := by
  dsimp only
  let G₀ := graphDifference (SimpleGraph.completeGraph (Fin n)) P.H
  let F := absorberErdosForbiddenConfigurationsOn q P.B
  let S₀ := absorberGreedyInitialState F (outsideAvailableTriangles P.H P.B)
  have htri₀ : ConsistsOfTriangles G₀ S₀.available :=
    (initialMasterStagePointwiseGood_of_typical P.typical).2.2.2.2.2.1
  have heven₀ := initialRemainder_even_of_admissible_absorber hadmissible P.absorption
  refine ⟨?_, ?_, ?_⟩
  · intro S hS v
    have hs := hsupport S hS
    have hInv := hs.1.1.1
    have hcontained := hs.1.1.2.1
    exact hInv.1.residual_even (fun T hT ↦ htri₀ T (hcontained.1 hT)) heven₀ v
  · exact hgraph.toResidualGraphStronglyWellDistributed W 0
  · have hgood : law.SupportedOn (fun S ↦ IsMasterStagePointwiseGood W 0 F
        (graphDifference G₀ (coveredGraph S.chosen)) S.available S.chosen ∅
        (Real.toNNReal (ksssEdgeDensity (initialResidualPairs P.H).card
          (ksssDensityHorizon (initialResidualPairs P.H).card (1 / (t : ℝ) ^ b))))
        (Real.toNNReal (Real.exp (-ksssPoissonExponent (ksssOrders q)
          (initialErdosTrajectoryCoefficient (Fin n) (S₀.available.card : ℝ))
          (ksssDensityHorizon (initialResidualPairs P.H).card (1 / (t : ℝ) ^ b)))))
        (17 / (t : ℝ≥0)) h) := by
      intro S hS
      have hs := hsupport S hS
      exact hs.1.1.1.masterPointwiseGood_of_residual_typical
        (fun T hT ↦ htri₀ T (hs.1.1.2.1.2 hT)) hs.2
    calc
      _ ≤ 1 := tsub_le_self
      _ = _ := (law.probability_eq_one_of_supported _ hgood).symm

def IsInitialResidualCompressedMasterLawWithError
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (q h b t : ℕ) (H : SimpleGraph V) (bank : TripleSystemOn V) (W : Vortex V ell)
    (C error : ℝ≥0) (law : FiniteLaw (MasterStateOn V)) : Prop :=
  let G₀ := graphDifference (SimpleGraph.completeGraph V) H
  let F := absorberErdosForbiddenConfigurationsOn q bank
  let S₀ := absorberGreedyInitialState F (outsideAvailableTriangles H bank)
  let E : ℝ := (initialResidualPairs H).card
  let time := ksssDensityHorizon E (1 / (t : ℝ) ^ b)
  let p := Real.toNNReal (ksssEdgeDensity E time)
  let eta := Real.toNNReal (Real.exp (-ksssPoissonExponent (ksssOrders q)
    (initialErdosTrajectoryCoefficient V (S₀.available.card : ℝ)) time))
  IsResidualCompressedMasterLaw law W 0 F G₀ (outsideAvailableTriangles H bank)
    p eta (17 / (t : ℝ≥0))
    C error h

theorem InitialPowerVortexPackage.compressed_residual_master_of_initial_typical_support
    {q h n ell length t rootPower step b B k : ℕ} {C error : ℝ≥0}
    (P : InitialPowerVortexPackage q h n ell t rootPower step) (hadmissible : Admissible n)
    (law : FiniteLaw (GreedyStateOn (Fin n)))
    (W : Vortex (Fin n) length)
    (hsupport : law.SupportedOn (IsInitialTypicalPatternOutcome q h b B k t P.H P.B W))
    (hgraph : IsInitialGraphProductBound law (fun S ↦ S.chosen)
      (graphDifference (SimpleGraph.completeGraph (Fin n)) P.H)
      (Real.toNNReal (ksssEdgeDensity (initialResidualPairs P.H).card
        (ksssDensityHorizon (initialResidualPairs P.H).card (1 / (t : ℝ) ^ b)))) C error) :
    IsInitialResidualCompressedMasterLawWithError q h b t P.H P.B W C error
      (law.map (packMasterState
        (fun S ↦ graphDifference (graphDifference (SimpleGraph.completeGraph (Fin n)) P.H)
          (coveredGraph S.chosen)) (fun S ↦ S.available) (fun S ↦ S.chosen) (fun _ ↦ ∅))) := by
  have hgood := P.residual_master_of_initial_typical_support hadmissible law W hsupport hgraph
  dsimp only at hgood
  have hinit : (absorberGreedyInitialState (absorberErdosForbiddenConfigurationsOn q P.B)
      (outsideAvailableTriangles P.H P.B)).available ⊆ outsideAvailableTriangles P.H P.B :=
    legalAvailable_subset_right _ _ _
  have hav : law.SupportedOn (fun S ↦ S.available ⊆ outsideAvailableTriangles P.H P.B) := by
    intro S hS
    exact (hsupport S hS).1.1.2.1.2.trans hinit
  have hsel : law.SupportedOn (fun S ↦ S.chosen ∪ ∅ ⊆ outsideAvailableTriangles P.H P.B) := by
    intro S hS
    simpa only [union_empty] using (hsupport S hS).1.1.2.1.1.trans hinit
  dsimp only [IsInitialResidualCompressedMasterLawWithError]
  apply hgood.compress hav hsel
  · intro S _hS u v huv
    by_cases hcov : (coveredGraph S.chosen).Adj u v
    · left
      simpa only [union_empty] using hcov
    · exact Or.inr ⟨huv, huv.ne, hcov⟩
  · intro S _hS
    exact graphDifference_le_left _ _
  · intro S _hS u v _huv
    simp only [W.root, coe_univ, Set.mem_univ, and_self]

end

end Erdos207
