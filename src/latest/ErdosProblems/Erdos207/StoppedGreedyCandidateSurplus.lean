/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.StoppedGreedyGoodState
import ErdosProblems.Erdos207.OutsideCandidateCount
import ErdosProblems.Erdos207.CompatibleCandidateDegree

/-!
# Candidate surplus in a stopped constrained-greedy state

Initial outside candidates are lost only to the absorber bank, absorber
edges, or edges already covered by the packing.  The first two losses are
deterministic, while the last is bounded by the selected vertex stars.  This
file combines that accounting with the rooted-threat bound.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

/-- The numerical common-leave surplus, without an exhaustion requirement.
This is the part of `IsKSSSCountGoodState` preserved during a stopped phase. -/
def HasKSSSCountSurplus
    {V : Type*} [Fintype V] [DecidableEq V]
    (q : ℕ) (H : SimpleGraph V) (X : Finset V)
    (B : TripleSystemOn V) (S : GreedyStateOn V) : Prop :=
  ∀ ⦃u v : V⦄
    (huv : (graphDifference (leaveGraph S.chosen) H).Adj u v),
    (u ∉ X ∨ v ∉ X) →
    (rootedActiveForbiddenConfigurations
        (absorberErdosForbiddenConfigurationsOn q B)
        S.chosen u v).card * q <
      (packingCompatibleThirdVertices
        (outsideAvailableTriangles H B) S.chosen huv.1.ne).card

/-- Star and rooted-threat cutoffs imply the exact compatible-candidate
surplus whenever their deterministic loss budget fits below `|V|-2`. -/
theorem hasKSSSCountSurplus_of_star_root_bounds
    {V : Type*} [Fintype V] [DecidableEq V]
    {q d r : ℕ} {H : SimpleGraph V} [DecidableRel H.Adj]
    {X : Finset V} {B : TripleSystemOn V} {S : GreedyStateOn V}
    (hpacking : IsPackingOn S.chosen)
    (hstar : ∀ v : V, (triplesThrough S.chosen v).card < d)
    (hroot : ∀ e : DistinctPair V,
      (rootedActiveForbiddenConfigurations
        (absorberErdosForbiddenConfigurationsOn q B)
        S.chosen e.1.1 e.1.2).card < r)
    (hbudget : ∀ u v : V, u ≠ v → ¬H.Adj u v →
      H.degree u + H.degree v + B.card + (4 * d + r * q) ≤
        Fintype.card V - 2) :
    HasKSSSCountSurplus q H X B S := by
  intro u v huv _houtside
  let e : DistinctPair V := ⟨(u, v), huv.1.ne⟩
  let R := (rootedActiveForbiddenConfigurations
    (absorberErdosForbiddenConfigurationsOn q B)
    S.chosen u v).card
  let C := (packingCompatibleThirdVertices
    (outsideAvailableTriangles H B) S.chosen huv.1.ne).card
  let su := (triplesThrough S.chosen u).card
  let sv := (triplesThrough S.chosen v).card
  let hLoss := H.degree u + H.degree v + B.card
  have huvH : ¬H.Adj u v := by
    have hc : u ≠ v ∧ ¬H.Adj u v := by simpa using huv.2
    exact hc.2
  have htotal := card_sub_two_le_outside_candidate_add_absorber_losses
    (H := H) (B := B) huv.1.ne huvH
  have hcand := card_candidate_le_compatible_add_starCounts
    (A := outsideAvailableTriangles H B) hpacking huv.1
  have htotal' : Fintype.card V - 2 ≤ C + (2 * su + 2 * sv) + hLoss := by
    dsimp [C, su, sv, hLoss]
    omega
  have hsu : su < d := hstar u
  have hsv : sv < d := hstar v
  have hR : R < r := hroot e
  have hstars : 2 * su + 2 * sv < 4 * d := by omega
  have hRmul : R * q ≤ r * q := by
    exact Nat.mul_le_mul_right q (Nat.le_of_lt hR)
  have hvariable : (2 * su + 2 * sv) + R * q < 4 * d + r * q :=
    Nat.add_lt_add_of_lt_of_le hstars hRmul
  have hfixed : hLoss + (4 * d + r * q) ≤ Fintype.card V - 2 := by
    simpa [hLoss, Nat.add_assoc] using
      hbudget u v huv.1.ne huvH
  have hactual : hLoss + ((2 * su + 2 * sv) + R * q) <
      Fintype.card V - 2 :=
    (Nat.add_lt_add_left hvariable hLoss).trans_le hfixed
  dsimp [R, C] at htotal' hactual ⊢
  omega

/-- The simultaneous stopped-process event yields an invariant state with
the exact KSSS numerical surplus. -/
theorem exists_stoppedAbsorberGreedy_invariant_countSurplus
    {V : Type*} [Fintype V] [DecidableEq V]
    {q M D fuel s d r : ℕ} {H : SimpleGraph V} [DecidableRel H.Adj]
    {X : Finset V} {B A : TripleSystemOn V}
    (hA2 : HasAbsorberLocalization q M H X B)
    (hD : 0 < D) (hd : 0 < d) (hr : 0 < r)
    (hratio : (fuel : ℝ≥0) * (D : ℝ≥0)⁻¹ ≤
      (Fintype.card V + 1 : ℝ≥0)⁻¹)
    (hsmall :
      (Fintype.card V : ℝ≥0) *
          stoppedVertexStarTailEnvelope V s (d : ℝ≥0) +
        (Fintype.card (DistinctPair V) : ℝ≥0) *
          stoppedRootedThreatTailEnvelope q M s H X B (r : ℝ≥0) < 1)
    (hbudget : ∀ u v : V, u ≠ v → ¬H.Adj u v →
      H.degree u + H.degree v + B.card + (4 * d + r * q) ≤
        Fintype.card V - 2) :
    ∃ S : GreedyStateOn V,
      AbsorberGreedyInvariant
          (absorberErdosForbiddenConfigurationsOn q B) A S ∧
        HasKSSSCountSurplus q H X B S := by
  have hdNN : (0 : ℝ≥0) < (d : ℝ≥0) := by exact_mod_cast hd
  have hrNN : (0 : ℝ≥0) < (r : ℝ≥0) := by exact_mod_cast hr
  obtain ⟨S, hInv, hstarNN, hrootNN⟩ :=
    exists_stoppedAbsorberGreedy_invariant_star_root_bounds
      (A := A) (s := s) (d : ℝ≥0) (r : ℝ≥0)
      hA2 hD hdNN hrNN hratio hsmall
  have hstar : ∀ v : V, (triplesThrough S.chosen v).card < d := by
    intro v
    exact_mod_cast hstarNN v
  have hroot : ∀ e : DistinctPair V,
      (rootedActiveForbiddenConfigurations
        (absorberErdosForbiddenConfigurationsOn q B)
        S.chosen e.1.1 e.1.2).card < r := by
    intro e
    exact_mod_cast hrootNN e
  exact ⟨S, hInv,
    hasKSSSCountSurplus_of_star_root_bounds
      hInv.1.1 hstar hroot hbudget⟩

end

end Erdos207
