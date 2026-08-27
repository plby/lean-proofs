/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.InitialPatternOutcomeTypicality
import ErdosProblems.Erdos207.TerminalJumpChain

/-! # Transfer global initial bands to a retained vortex before recursion -/

namespace Erdos207

open Finset
open scoped Classical NNReal

noncomputable section

def Vortex.reindex
    {V : Type*} [Fintype V] [DecidableEq V] {ell length : ℕ}
    (W : Vortex V ell) (stage : Fin (length + 1) → Fin (ell + 1))
    (hmono : Monotone stage) (hzero : stage 0 = 0) : Vortex V length where
  U i := W.U (stage i)
  root := by rw [hzero, W.root]
  antitone := fun i j hij ↦ W.antitone (stage i) (stage j) (hmono hij)

theorem AllUncoveredNeighborBands.reindex
    {I J V : Type*} [Fintype V] [DecidableEq V]
    {sets : I → Finset V} {Q : Finset (Finset V)} {E t time : ℝ} {s B : ℕ}
    {S : GreedyStateOn V} (h : AllUncoveredNeighborBands sets Q E t s B time S) (f : J → I) :
    AllUncoveredNeighborBands (fun j ↦ sets (f j)) Q E t s B time S :=
  fun j v ↦ h (f j) v

theorem AllProperPatternBands.reindex
    {I J K V : Type*} [Fintype V] [DecidableEq V]
    {sets : I → Finset V} {patterns : J → SimpleGraph V}
    {q s B : ℕ} {a : ℕ → ℝ} {E t time : ℝ} {S : GreedyStateOn V}
    (h : AllProperPatternBands sets patterns q a E t s B time S) (f : K → I) :
    AllProperPatternBands (fun k ↦ sets (f k)) patterns q a E t s B time S :=
  fun k j ↦ h (f k) j

theorem IsInitialPatternOutcome.reindex
    {V : Type*} [Fintype V] [DecidableEq V] {ell length q h b B k t : ℕ}
    {H : SimpleGraph V} {bank : TripleSystemOn V} {W : Vortex V ell} {S : GreedyStateOn V}
    (hS : IsInitialPatternOutcome q h b B k t H bank W S)
    (stage : Fin (length + 1) → Fin (ell + 1)) (hmono : Monotone stage) (hzero : stage 0 = 0) :
    IsInitialPatternOutcome q h b B k t H bank (W.reindex stage hmono hzero) S :=
  ⟨hS.1, hS.2.1.reindex stage, hS.2.2.reindex stage⟩

theorem InitialPowerVortexPackage.initial_pattern_outcome_typical_reindex
    {q h n ell length t rootPower step : ℕ}
    (P : InitialPowerVortexPackage q h n ell t rootPower step)
    (stage : Fin (length + 1) → Fin (ell + 1)) (hmono : Monotone stage) (hzero : stage 0 = 0)
    (b B k : ℕ) (S : GreedyStateOn (Fin n))
    (hS : IsInitialPatternOutcome q h b B k t P.H P.B P.W S)
    (hb : 1 ≤ b) (ht : 1 ≤ t) (hh : h ≤ t)
    (hc : powerAbsorberCoefficient q ≤ t)
    (hlarge : 6 * t ^ initialSupportPower rootPower + 4 ≤ n)
    (hroot : b * h + h ^ 2 + 2 ≤ rootPower)
    (hexp : Real.exp (∑ d ∈ ksssOrders q, initialErdosCoefficientBound q d) ≤ t) :
    IsInitialTypicalPatternOutcome q h b B k t P.H P.B (P.W.reindex stage hmono hzero) S := by
  let S₀ := absorberGreedyInitialState (absorberErdosForbiddenConfigurationsOn q P.B)
    (outsideAvailableTriangles P.H P.B)
  let E : ℝ := (initialResidualPairs P.H).card
  let a := initialErdosTrajectoryCoefficient (Fin n) (S₀.available.card : ℝ)
  let time := ksssDensityHorizon E (1 / (t : ℝ) ^ b)
  obtain ⟨hdegree, _, hbank⟩ := P.support_power_bounds hc
  have hdata := initial_absorber_pattern_analytic_data q (t ^ initialSupportPower rootPower)
    P.H P.B hdegree hbank (by simpa only [Fintype.card_fin] using hlarge)
  have htR : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have htime := ksssDensityHorizon_bounds E (1 / (t : ℝ) ^ b) hdata.1 (by positivity)
    ((div_le_one (by positivity : (0 : ℝ) < (t : ℝ) ^ b)).mpr (one_le_pow₀ htR))
  have hS' := hS.reindex stage hmono hzero
  refine ⟨hS', ?_⟩
  exact initial_bands_isIterationTypical (P.W.reindex stage hmono hzero) P.H S q b B t h a
    (initialErdosCoefficientBound q) E time ht hb hh (Nat.cast_nonneg _) htime.1
    (htime.2.1 time le_rfl) hdata.2.2.1 hdata.2.2.2 hexp
    (fun i ↦ P.nonempty (stage i))
    (fun i ↦ (pow_le_pow_right₀ htR hroot).trans (by exact_mod_cast P.level_card_lower (stage i)))
    hS'.2.1 hS'.2.2

end

end Erdos207
