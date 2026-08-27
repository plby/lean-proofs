/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.InitialResidualMasterLaw
import ErdosProblems.Erdos207.ResidualMasterCompression

/-! # The constructed initial law gives the compressed residual base -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

def IsInitialResidualCompressedMasterLaw
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (q h b t : ℕ) (H : SimpleGraph V) (bank : TripleSystemOn V) (W : Vortex V ell)
    (law : FiniteLaw (MasterStateOn V)) : Prop :=
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
    (2 * ksssInitialGraphProductConstant q (initialErdosCoefficientBound q))
    (initialPatternGraphError q h ell (Fintype.card V) t) h

theorem InitialPowerVortexPackage.compressed_residual_master_of_initial_pattern_law
    {q h n ell t rootPower step b B k : ℕ}
    (P : InitialPowerVortexPackage q h n ell t rootPower step) (hadmissible : Admissible n)
    (law : FiniteLaw (GreedyStateOn (Fin n)))
    (hlaw : IsInitialTypicalPatternLaw q h b B k t P.H P.B P.W law) :
    IsInitialResidualCompressedMasterLaw q h b t P.H P.B P.W
      (law.map (packMasterState
        (fun S ↦ graphDifference (graphDifference (SimpleGraph.completeGraph (Fin n)) P.H)
          (coveredGraph S.chosen)) (fun S ↦ S.available) (fun S ↦ S.chosen) (fun _ ↦ ∅))) := by
  have hgood := P.residual_master_of_initial_pattern_law hadmissible law hlaw
  dsimp only at hgood
  have hinit : (absorberGreedyInitialState (absorberErdosForbiddenConfigurationsOn q P.B)
      (outsideAvailableTriangles P.H P.B)).available ⊆ outsideAvailableTriangles P.H P.B :=
    legalAvailable_subset_right _ _ _
  have hav : law.SupportedOn (fun S ↦ S.available ⊆ outsideAvailableTriangles P.H P.B) := by
    intro S hS
    exact (hlaw.1 S hS).1.1.2.1.2.trans hinit
  have hsel : law.SupportedOn (fun S ↦ S.chosen ∪ ∅ ⊆ outsideAvailableTriangles P.H P.B) := by
    intro S hS
    simpa only [union_empty] using (hlaw.1 S hS).1.1.2.1.1.trans hinit
  simp only [IsInitialResidualCompressedMasterLaw, Fintype.card_fin]
  apply hgood.compress hav hsel
  · intro S _hS u v huv
    by_cases hcov : (coveredGraph S.chosen).Adj u v
    · left
      simpa only [union_empty] using hcov
    · exact Or.inr ⟨huv, huv.ne, hcov⟩
  · intro S _hS
    exact graphDifference_le_left _ _
  · intro S _hS u v _huv
    simp only [P.W.root, coe_univ, Set.mem_univ, and_self]

end

end Erdos207
