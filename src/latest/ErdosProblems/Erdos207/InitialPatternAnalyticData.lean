/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.InitialKSSSPowerParameters

/-! # The analytic pattern inputs follow from the actual initial absorber densities -/

namespace Erdos207

open Finset

noncomputable section

theorem initial_absorber_pattern_analytic_data
    {V : Type*} [Fintype V] [DecidableEq V]
    (q C : ℕ) (H : SimpleGraph V) [DecidableRel H.Adj] (bank : TripleSystemOn V)
    (hdegree : ∀ x, H.degree x ≤ C) (hsupport : (verticesOn bank).card ≤ C)
    (hlarge : 6 * C + 4 ≤ Fintype.card V) :
    let S₀ := absorberGreedyInitialState (absorberErdosForbiddenConfigurationsOn q bank) (outsideAvailableTriangles H bank)
    let E : ℝ := (initialResidualPairs H).card
    let A : ℝ := S₀.available.card
    0 < E ∧ 0 < A ∧
      (∀ d ∈ ksssOrders q, 0 ≤ initialErdosTrajectoryCoefficient V A d) ∧
      (∀ d ∈ ksssOrders q, initialErdosTrajectoryCoefficient V A d * E ^ d ≤ initialErdosCoefficientBound q d) := by
  dsimp only
  let S₀ := absorberGreedyInitialState (absorberErdosForbiddenConfigurationsOn q bank) (outsideAvailableTriangles H bank)
  let N : ℝ := Fintype.card V
  let E : ℝ := (initialResidualPairs H).card
  let A : ℝ := S₀.available.card
  have hN : 0 < N := by dsimp only [N]; exact_mod_cast (show 0 < Fintype.card V by omega)
  have hE : 0 < E := (by positivity : 0 < N ^ 2 / 16).trans_le
    (initialResidualPairs_density_lower (q := q) hdegree hsupport hlarge)
  have hcube : N ^ 3 ≤ 48 * A := by
    dsimp only [N, A, S₀]
    exact_mod_cast initial_globalAvailability_cube_le (q := q) hdegree hsupport hlarge
  have hA : 0 < A := by have hp := pow_pos hN 3; nlinarith only [hp, hcube]
  have hratio := (initial_pair_relative_degree_interval (q := q) hdegree hsupport hlarge).1
  have hAcard : (0 : ℝ) < S₀.available.card := hA
  obtain ⟨T, _⟩ : S₀.available.Nonempty := card_pos.mp (by exact_mod_cast hAcard)
  refine ⟨hE, hA, fun d _ ↦ initialErdosTrajectoryCoefficient_nonneg V A hA.le d, ?_⟩
  intro d hd
  have hd' : d + 3 ≤ q := by
    have hmem := mem_Icc.mp hd
    change 1 ≤ d ∧ d ≤ q - 3 at hmem
    omega
  exact initialErdosTrajectoryCoefficient_fixed_bound q d T E A 6 hd'
    (by exact_mod_cast (show 1 ≤ Fintype.card V by omega)) hE hA (by norm_num) hratio

end

end Erdos207
