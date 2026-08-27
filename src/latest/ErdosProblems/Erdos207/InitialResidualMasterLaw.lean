/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.ResidualMasterIteration
import ErdosProblems.Erdos207.InitialPatternGraphLaw

/-! # The constructed initial pattern law starts the compatible master iteration -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem IsPackingOn.residual_even
    {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {M : TripleSystemOn V}
    (hM : IsPackingOn M) (htri : ConsistsOfTriangles G M)
    (heven : ∀ v, Even ((neighborsIn G univ v).card)) :
    ∀ v, Even ((neighborsIn (graphDifference G (coveredGraph M)) univ v).card) := by
  have hstep : IsMasterCoverStep (∅ : ForbiddenFamilyOn V) G univ M ∅ ∅ M := by
    refine ⟨Subset.rfl, by simp, ?_, ?_, ?_⟩
    · simpa only [empty_union] using hM
    · intro C hC
      simp at hC
    · intro u v _ hout
      simp at hout
  have heq : updatedStageGraph G univ M = graphDifference G (coveredGraph M) := by
    ext u v
    simp [updatedStageGraph, graphRestrictedTo, graphDifference]
  simpa only [heq] using hstep.updated_even heven htri

theorem GreedyInvariant.masterPointwiseGood_of_residual_typical
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    {W : Vortex V ell} {stage : Fin (ell + 1)} {F : ForbiddenFamilyOn V}
    {G : SimpleGraph V} {S : GreedyStateOn V} {p eta xi : ℝ≥0} {h : ℕ}
    (hInv : GreedyInvariant F S) (htri : ConsistsOfTriangles G S.available)
    (htyp : IsIterationTypical W stage (graphDifference G (coveredGraph S.chosen)) S.available p eta xi h) :
    IsMasterStagePointwiseGood W stage F (graphDifference G (coveredGraph S.chosen))
      S.available S.chosen ∅ p eta xi h := by
  refine ⟨by simp, by simpa only [union_empty] using hInv.1,
    by simpa only [union_empty] using hInv.2.1, htyp, ?_, ?_, ?_⟩
  · intro u v huv
    simpa only [union_empty, leaveGraph] using huv.2
  · intro T hT u hu v hv huv
    have hlegal := hInv.2.2 T hT
    have hav := (packing_insert_iff_avoids_coveredGraph hInv.1 T hlegal.1).mp hlegal.2.1
    exact ⟨htri T hT u hu v hv huv, huv, hav u hu v hv huv⟩
  · intro T hT
    simpa only [union_empty] using
      (avoidsForbidden_insert_iff_not_completes hInv.2.1 T).mp (hInv.2.2 T hT).2.2

theorem InitialPowerVortexPackage.residual_master_of_initial_pattern_law
    {q h n ell t rootPower step b B k : ℕ}
    (P : InitialPowerVortexPackage q h n ell t rootPower step) (hadmissible : Admissible n)
    (law : FiniteLaw (GreedyStateOn (Fin n)))
    (hlaw : IsInitialTypicalPatternLaw q h b B k t P.H P.B P.W law) :
    let G₀ := graphDifference (SimpleGraph.completeGraph (Fin n)) P.H
    let F := absorberErdosForbiddenConfigurationsOn q P.B
    let S₀ := absorberGreedyInitialState F (outsideAvailableTriangles P.H P.B)
    let E : ℝ := (initialResidualPairs P.H).card
    let time := ksssDensityHorizon E (1 / (t : ℝ) ^ b)
    let p := Real.toNNReal (ksssEdgeDensity E time)
    let eta := Real.toNNReal (Real.exp (-ksssPoissonExponent (ksssOrders q)
      (initialErdosTrajectoryCoefficient (Fin n) (S₀.available.card : ℝ)) time))
    IsResidualMasterIterationGood law P.W 0 G₀ F
      (fun S ↦ graphDifference G₀ (coveredGraph S.chosen)) (fun S ↦ S.available)
      (fun S ↦ S.chosen) (fun _ ↦ ∅) p eta (17 / (t : ℝ≥0))
      (2 * ksssInitialGraphProductConstant q (initialErdosCoefficientBound q))
      (initialPatternGraphError q h ell n t) h := by
  dsimp only
  let G₀ := graphDifference (SimpleGraph.completeGraph (Fin n)) P.H
  let F := absorberErdosForbiddenConfigurationsOn q P.B
  let S₀ := absorberGreedyInitialState F (outsideAvailableTriangles P.H P.B)
  have htri₀ : ConsistsOfTriangles G₀ S₀.available :=
    (initialMasterStagePointwiseGood_of_typical P.typical).2.2.2.2.2.1
  have heven₀ := initialRemainder_even_of_admissible_absorber hadmissible P.absorption
  refine ⟨?_, ?_, ?_⟩
  · intro S hS v
    have hs := hlaw.1 S hS
    have hInv := hs.1.1.1
    have hcontained := hs.1.1.2.1
    exact hInv.1.residual_even (fun T hT ↦ htri₀ T (hcontained.1 hT)) heven₀ v
  · simpa only [Fintype.card_fin] using hlaw.2.toResidualGraphStronglyWellDistributed P.W 0
  · have hgood : law.SupportedOn (fun S ↦ IsMasterStagePointwiseGood P.W 0 F
        (graphDifference G₀ (coveredGraph S.chosen)) S.available S.chosen ∅
        (Real.toNNReal (ksssEdgeDensity (initialResidualPairs P.H).card
          (ksssDensityHorizon (initialResidualPairs P.H).card (1 / (t : ℝ) ^ b))))
        (Real.toNNReal (Real.exp (-ksssPoissonExponent (ksssOrders q)
          (initialErdosTrajectoryCoefficient (Fin n) (S₀.available.card : ℝ))
          (ksssDensityHorizon (initialResidualPairs P.H).card (1 / (t : ℝ) ^ b)))))
        (17 / (t : ℝ≥0)) h) := by
      intro S hS
      have hs := hlaw.1 S hS
      exact hs.1.1.1.masterPointwiseGood_of_residual_typical
        (fun T hT ↦ htri₀ T (hs.1.1.2.1.2 hT)) hs.2
    calc
      _ ≤ 1 := tsub_le_self
      _ = _ := (law.probability_eq_one_of_supported _ hgood).symm

end

end Erdos207
