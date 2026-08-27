/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.HybridVortexTransitionData
import ErdosProblems.Erdos207.CompressedRelativeExtensionSelection
import ErdosProblems.Erdos207.LocalizedNewRootedThreatProbability

/-!
# Selecting the terminal hybrid state with all relative rooted bounds

At the first positive hybrid level, the old packing is still random.  The
terminal transition needs a rooted extension bound relative to that packing,
simultaneously for every ordered pair.  We combine the pair-indexed witness
families into one dependent sum, select one positive-mass master state, then
project the combined relative estimate back to each pair.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

/-- The dependent union of localized rooted witnesses over all ordered
distinct vertex pairs at a hybrid transition. -/
abbrev HybridLocalizedRootedThreatWitness
    {q h n t rootPower : ℕ}
    (P : InitialHybridVortexPackage q h n t rootPower) (i : Fin 2) :=
  Σ e : DistinctPair (Fin n),
    LocalizedRootedThreatWitness (Fin n)
      (absorberErdosForbiddenConfigurationsOn q P.B)
      e.1.1 e.1.2 (P.W.U i.succ)

/-- The configuration family on the preceding dependent witness union. -/
def hybridLocalizedRootedThreatRemainder
    {q h n t rootPower : ℕ}
    (P : InitialHybridVortexPackage q h n t rootPower) (i : Fin 2)
    (z : HybridLocalizedRootedThreatWitness P i) : TripleSystem n :=
  localizedRootedThreatRemainder z.2

/-- The dependent-sum extension coefficient supplied by hybrid A2. -/
def hybridLocalizedMasterKappa
    {q h n t rootPower : ℕ}
    (P : InitialHybridVortexPackage q h n t rootPower) (i : Fin 2) : ℝ≥0 :=
  (Fintype.card (DistinctPair (Fin n)) : ℝ≥0) *
    (((P.W.U i.succ).card : ℝ≥0) *
      localizedRootedThreatVortexA2LargeCoefficient
        (P.W.prefix i.succ) q (12 * (q + 2) ^ 2) 3 0)

/-- The pairwise A2 estimates combined over the dependent witness union. -/
theorem InitialHybridVortexPackage.hybridLocalizedMasterExtensionBound
    {q h n t rootPower : ℕ}
    (P : InitialHybridVortexPackage q h n t rootPower)
    (i : Fin 2) (p : ℝ≥0) (hp : p ≤ 1)
    (hbank : (subsetsUpToCard P.B q).card ≤ (P.W.U 0).card) :
    HasExtensionBound (hybridLocalizedRootedThreatRemainder P i)
      (fun T ↦ masterUnionTriangleWeight P.W i.succ p T +
        (n : ℝ≥0)⁻¹) (hybridLocalizedMasterKappa P i) := by
  classical
  unfold hybridLocalizedRootedThreatRemainder hybridLocalizedMasterKappa
  exact hasExtensionBound_sigma
    (E := DistinctPair (Fin n))
    (I := fun e ↦ LocalizedRootedThreatWitness (Fin n)
      (absorberErdosForbiddenConfigurationsOn q P.B)
      e.1.1 e.1.2 (P.W.U i.succ))
    (fun _e z ↦ localizedRootedThreatRemainder z)
    (fun T ↦ masterUnionTriangleWeight P.W i.succ p T +
      (n : ℝ≥0)⁻¹)
    (((P.W.U i.succ).card : ℝ≥0) *
      localizedRootedThreatVortexA2LargeCoefficient
        (P.W.prefix i.succ) q (12 * (q + 2) ^ 2) 3 0)
    (fun e ↦ P.localizedMasterExtensionBound_add_ambient i p hp hbank e)

/-- The union-bound error in the support-aware terminal-state selection. -/
def hybridTerminalSelectionError
    {q h n t rootPower : ℕ}
    (P : InitialHybridVortexPackage q h n t rootPower) (i : Fin 2)
    (xi C kappaOut : ℝ≥0) : ℝ≥0 :=
  xi + (configurationRoots
      (hybridLocalizedRootedThreatRemainder P i)).card *
    (((2 * (2 * C) ^ (q - 1)) * hybridLocalizedMasterKappa P i) /
      kappaOut)

/-- A frozen positive-mass hybrid master state together with all pairwise
relative extension bounds needed by the terminal transition. -/
structure HybridTerminalRelativeState
    {q h n t rootPower : ℕ}
    (P : InitialHybridVortexPackage q h n t rootPower)
    (i : Fin 2) (law : FiniteLaw (MasterStateOn (Fin n)))
    (p eta xi kappaOut : ℝ≥0) where
  state : MasterStateOn (Fin n)
  mass_pos : 0 < law.mass state
  pointwise : IsMasterStagePointwiseGood P.W i.succ
    (absorberErdosForbiddenConfigurationsOn q P.B)
    state.graph state.available state.initial state.later p eta xi h
  pure : IsCompressedMasterLaw (FiniteLaw.pure state) P.W i.succ
    (absorberErdosForbiddenConfigurationsOn q P.B)
    (graphDifference (SimpleGraph.completeGraph (Fin n)) P.H)
    (outsideAvailableTriangles P.H P.B) p eta xi 1 1 h
  relative : ∀ e : DistinctPair (Fin n),
    HasExtensionBound
      (fun z : LocalizedNewRootedThreatWitness (Fin n)
          (absorberErdosForbiddenConfigurationsOn q P.B)
          (state.initial ∪ state.later) e.1.1 e.1.2 (P.W.U i.succ) ↦
        localizedNewRootedThreatRemainder z)
      (fun _ ↦ (n : ℝ≥0)⁻¹) kappaOut

/-- Select a positive-mass first-level state which is pointwise good and has
the ambient-inverse relative extension bound required for every pair in the
terminal newly-active rooted argument.  The selected state is also frozen as
a one-point compressed master law with additive error one. -/
theorem InitialHybridVortexPackage.exists_terminalRelativeState
    {q h n t rootPower : ℕ}
    (P : InitialHybridVortexPackage q h n t rootPower)
    (i : Fin 2) {law : FiniteLaw (MasterStateOn (Fin n))}
    {p eta xi C b : ℝ≥0}
    (hmaster : IsCompressedMasterLaw law P.W i.succ
      (absorberErdosForbiddenConfigurationsOn q P.B)
      (graphDifference (SimpleGraph.completeGraph (Fin n)) P.H)
      (outsideAvailableTriangles P.H P.B) p eta xi C b h)
    (hC : 1 ≤ C) (hp : p ≤ 1)
    (hbank : (subsetsUpToCard P.B q).card ≤ (P.W.U 0).card)
    (hb : ∀ S : TripleSystem n, S.card ≤ q - 1 →
      b ≤ setWeight (masterUnionTriangleWeight P.W i.succ p) S)
    (kappaOut : ℝ≥0) (hkappaOut : 0 < kappaOut)
    (hsmall : hybridTerminalSelectionError P i xi C kappaOut < 1) :
    Nonempty (HybridTerminalRelativeState P i law p eta xi kappaOut) := by
  classical
  let F := absorberErdosForbiddenConfigurationsOn q P.B
  let configurations := hybridLocalizedRootedThreatRemainder P i
  let baseKappa : ℝ≥0 :=
    ((P.W.U i.succ).card : ℝ≥0) *
      localizedRootedThreatVortexA2LargeCoefficient
        (P.W.prefix i.succ) q (12 * (q + 2) ^ 2) 3 0
  have hfamily : ∀ S ∈ F, S.card ≤ q := by
    intro S hS
    exact card_le_cutoff_of_mem_absorberErdosForbidden hS
  have hcard : ∀ z : HybridLocalizedRootedThreatWitness P i,
      (configurations z).card ≤ q - 1 := by
    intro z
    exact card_localizedRootedThreatRemainder_le hfamily z.2
  have hall : HasExtensionBound configurations
      (fun T ↦ masterUnionTriangleWeight P.W i.succ p T +
        (n : ℝ≥0)⁻¹)
      ((Fintype.card (DistinctPair (Fin n)) : ℝ≥0) * baseKappa) := by
    simpa only [configurations, hybridLocalizedMasterKappa, baseKappa] using
      P.hybridLocalizedMasterExtensionBound i p hp hbank
  obtain ⟨state, hmass, hpoint, hrelative⟩ :=
    hmaster.exists_supported_pointwise_relativeExtensionBound
      hC (q - 1) configurations hcard hb (fun _ ↦ (n : ℝ≥0)⁻¹)
      ((Fintype.card (DistinctPair (Fin n)) : ℝ≥0) * baseKappa)
      kappaOut hall hkappaOut (by
        simpa only [hybridTerminalSelectionError,
          hybridLocalizedMasterKappa, baseKappa, configurations] using hsmall)
  refine ⟨⟨state, hmass, hpoint,
    hmaster.pure_of_supported_pointwise state hmass hpoint, ?_⟩⟩
  intro e
  have hcomponent : HasExtensionBound
      (fun z : LocalizedRootedThreatWitness (Fin n) F
          e.1.1 e.1.2 (P.W.U i.succ) ↦
        localizedRootedThreatRemainder z \
          (state.initial ∪ state.later))
      (fun _ ↦ (n : ℝ≥0)⁻¹) kappaOut := by
    exact HasExtensionBound.sigma_component
      (E := DistinctPair (Fin n))
      (I := fun e ↦ LocalizedRootedThreatWitness (Fin n) F
        e.1.1 e.1.2 (P.W.U i.succ))
      (fun e (z : LocalizedRootedThreatWitness (Fin n) F
        e.1.1 e.1.2 (P.W.U i.succ)) ↦
          localizedRootedThreatRemainder z \
            (state.initial ∪ state.later))
      (fun _ ↦ (n : ℝ≥0)⁻¹) hrelative e
  simpa only [F] using
    localizedNewRootedThreatRemainder_hasExtensionBound hcomponent

end

end Erdos207
