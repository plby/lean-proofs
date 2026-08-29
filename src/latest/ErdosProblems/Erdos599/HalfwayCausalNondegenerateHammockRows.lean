/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayCausalGlobalHammockClosure
import ErdosProblems.Erdos599.CoherentNondegenerateHammockLimit
import ErdosProblems.Erdos599.FilteredNondegenerateHammockClosure

/-!
# Actual causal nondegenerate-hammock closure

The extra tracker vertices are already part of `CausalSection9Rows.rule`.
Prefix causality identifies those choices with the final ladder tracker,
and its restricted limiting maximality therefore takes place inside the
actual global carrier. No additional closure premise is supplied here.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599.Blueprint.LinkageBlueprint.CausalSection9Rows

open DirectedPath _root_.Erdos599.Alternating Ladder
open CardinalInduction.RegularRows

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

def coherentNondegenerateHammockAt
    (Gamma : DWeb V) (kappa : Cardinal.{u})
    (hkappa : aleph0 ≤ kappa) (hGamma : Gamma.IsNormalized)
    (seed : Set V) (hseed : #seed ≤ succ kappa)
    (x v : V) (a : Ladder.Stage (succ kappa)) :
    Set (AltPath Gamma.graph) :=
  let L := finalLadder Gamma kappa hkappa hGamma seed hseed
  CoherentNondegenerateHammockTracker.chosenAt Gamma kappa L.warpAt
    (fun b ↦ Gamma.roof (L.frontier b)) x v a

theorem prior_frontier_eq_final_of_le
    (hkappa : aleph0 ≤ kappa) (hGamma : Gamma.IsNormalized)
    {seed : Set V} (hseed : #seed ≤ succ kappa)
    {b a : Ladder.Stage (succ kappa)} (hba : b ≤ a) :
    (priorCore Gamma a (fun c _hca ↦
      (rule Gamma kappa hkappa hGamma seed hseed).state
        (hkappa.trans (le_succ kappa)) c)).frontier b =
      (finalLadder Gamma kappa hkappa hGamma seed hseed).frontier b := by
  rcases hba.lt_or_eq with hba | rfl
  · exact (prior_geometry_eq_final_of_lt
      (Gamma := Gamma) (kappa := kappa) hkappa hGamma hseed hba).2
  · exact (prior_geometry_eq_final
      (Gamma := Gamma) (kappa := kappa) hkappa hGamma hseed b).2

theorem coherentNondegenerateHammockAt_eq_prior
    (hkappa : aleph0 ≤ kappa) (hGamma : Gamma.IsNormalized)
    {seed : Set V} (hseed : #seed ≤ succ kappa)
    (x v : V) (a : Ladder.Stage (succ kappa)) :
    coherentNondegenerateHammockAt Gamma kappa hkappa hGamma seed hseed x v a =
      let L := priorCore Gamma a (fun c _hca ↦
        (rule Gamma kappa hkappa hGamma seed hseed).state
          (hkappa.trans (le_succ kappa)) c)
      CoherentNondegenerateHammockTracker.chosenAt Gamma kappa L.warpAt
        (fun b ↦ Gamma.roof (L.frontier b)) x v a := by
  dsimp only [coherentNondegenerateHammockAt]
  symm
  apply CoherentNondegenerateHammockTracker.at_congr_le Gamma kappa
  · intro b hba
    exact prior_warpAt_eq_final_of_le
      (Gamma := Gamma) (kappa := kappa) hkappa hGamma hseed hba
  · intro b hba
    rw [prior_frontier_eq_final_of_le
      (Gamma := Gamma) (kappa := kappa) hkappa hGamma hseed hba]

theorem coherentNondegenerateHammockAt_contained
    (hkappa : aleph0 ≤ kappa) (hGamma : Gamma.IsNormalized)
    {seed : Set V} (hseed : #seed ≤ succ kappa)
    (a : Ladder.Stage (succ kappa)) (x v : V)
    (helig : HammockEligible
      (priorCarrier a (fun b _hba ↦
        (rule Gamma kappa hkappa hGamma seed hseed).state
          (hkappa.trans (le_succ kappa)) b))
      (Gamma.strictRoof
        ((finalLadder Gamma kappa hkappa hGamma seed hseed).frontier a))
      (Gamma.roof
        ((finalLadder Gamma kappa hkappa hGamma seed hseed).frontier a))
      x (.vertex v)) :
    HammockContained
      (coherentNondegenerateHammockAt Gamma kappa hkappa hGamma seed hseed x v a)
      (globalCarrier Gamma kappa hkappa hGamma seed hseed) := by
  apply Set.Subset.trans ?_
    ((coherentHammockIncrement_subset_rowAt hkappa hGamma hseed a).trans
      (rowAt_subset_globalCarrier hkappa hGamma hseed a))
  unfold coherentHammockIncrement
  apply Set.Subset.trans ?_ Set.subset_union_right
  apply Set.Subset.trans ?_ Set.subset_union_left
  unfold coherentNondegenerateHammockIncrement
  dsimp only
  have hfrontier := (prior_geometry_eq_final
    (Gamma := Gamma) (kappa := kappa) hkappa hGamma hseed a).2
  rw [hfrontier]
  let q : EligiblePair _ _ _ := ⟨(x, .vertex v), helig⟩
  apply Set.subset_iUnion_of_subset q
  dsimp only [q]
  rw [← coherentNondegenerateHammockAt_eq_prior
    (Gamma := Gamma) (kappa := kappa) hkappa hGamma hseed x v a]

/-- The final causal carrier has the required filtered closure for every
eligible distinct finite pair, with no global maximal-family premise. -/
theorem finiteFilteredHammockClosed_limitWarp
    (hkappa : aleph0 ≤ kappa) (hGamma : Gamma.IsNormalized)
    {seed : Set V} (hseed : #seed ≤ succ kappa) :
    FiniteFilteredHammockClosedUpTo Gamma
      (finalLadder Gamma kappa hkappa hGamma seed hseed).limitWarp
      (globalCarrier Gamma kappa hkappa hGamma seed hseed)
      (globalCarrier Gamma kappa hkappa hGamma seed hseed)
      (finalLadder Gamma kappa hkappa hGamma seed hseed).limitStrictRoof
      (finalLadder Gamma kappa hkappa hGamma seed hseed).limitRoof
      (CoherentNondegenerateHammockTracker.CapturedByStageRoof
        (finalLadder Gamma kappa hkappa hGamma seed hseed)) kappa := by
  intro x v hne helig
  let L := finalLadder Gamma kappa hkappa hGamma seed hseed
  have hlegal := finalLadder_halfwayGeometry
    (Gamma := Gamma) (kappa := kappa) hkappa hGamma hseed
  let zero : Ladder.Stage (succ kappa) :=
    ⟨0, (Cardinal.isRegular_succ hkappa).ord_pos⟩
  obtain ⟨b, _hzeroB, heligB⟩ := exists_later_hammockEligible
    (Gamma := Gamma) (kappa := kappa) hkappa hGamma hseed zero helig
  apply CoherentNondegenerateHammockTracker.exists_contained_limit_filteredMaximalUpTo
    hkappa hlegal hne b
  intro a hba
  exact coherentNondegenerateHammockAt_contained hkappa hGamma hseed a x v
    (hammockEligible_mono
      (Gamma := Gamma) (kappa := kappa) hkappa hGamma hseed hba heligB)

#print axioms coherentNondegenerateHammockAt_eq_prior
#print axioms coherentNondegenerateHammockAt_contained
#print axioms finiteFilteredHammockClosed_limitWarp

end Erdos599.Blueprint.LinkageBlueprint.CausalSection9Rows
