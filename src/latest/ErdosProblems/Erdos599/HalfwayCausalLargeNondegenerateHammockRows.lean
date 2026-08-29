/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayCausalNondegenerateHammockRows
import ErdosProblems.Erdos599.CoherentNondegenerateHammockLargeLimit

/-!
# Large filtered hammocks inside the actual causal carrier

The successor-sized diagnostic belongs to the causal rule, not a later
enlargement. Together with the capped coherent tracker it replaces every
large roof-filtered limiting hammock by one contained in the global carrier.
The filter is retained in both the input and output.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599.Blueprint.LinkageBlueprint.CausalSection9Rows

open DirectedPath _root_.Erdos599.Alternating Ladder
open CardinalInduction.RegularRows

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

def largeNondegenerateHammockAt
    (Gamma : DWeb V) (kappa : Cardinal.{u})
    (hkappa : aleph0 ≤ kappa) (hGamma : Gamma.IsNormalized)
    (seed : Set V) (hseed : #seed ≤ succ kappa)
    (x v : V) (a : Ladder.Stage (succ kappa)) :
    Set (AltPath Gamma.graph) :=
  let L := finalLadder Gamma kappa hkappa hGamma seed hseed
  CoherentNondegenerateHammockLargeDiagnostic.chosenAt Gamma kappa L.warpAt
    (fun b ↦ Gamma.roof (L.frontier b)) x v a

theorem largeNondegenerateHammockAt_eq_prior
    (hkappa : aleph0 ≤ kappa) (hGamma : Gamma.IsNormalized)
    {seed : Set V} (hseed : #seed ≤ succ kappa)
    (x v : V) (a : Ladder.Stage (succ kappa)) :
    largeNondegenerateHammockAt Gamma kappa hkappa hGamma seed hseed x v a =
      let L := priorCore Gamma a (fun c _hca ↦
        (rule Gamma kappa hkappa hGamma seed hseed).state
          (hkappa.trans (le_succ kappa)) c)
      CoherentNondegenerateHammockLargeDiagnostic.chosenAt Gamma kappa L.warpAt
        (fun b ↦ Gamma.roof (L.frontier b)) x v a := by
  dsimp only [largeNondegenerateHammockAt]
  symm
  apply CoherentNondegenerateHammockLargeDiagnostic.chosenAt_congr_le Gamma kappa
  · intro b hba
    exact prior_warpAt_eq_final_of_le
      (Gamma := Gamma) (kappa := kappa) hkappa hGamma hseed hba
  · intro b hba
    rw [prior_frontier_eq_final_of_le
      (Gamma := Gamma) (kappa := kappa) hkappa hGamma hseed hba]

theorem largeNondegenerateHammockAt_contained
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
      (largeNondegenerateHammockAt Gamma kappa hkappa hGamma seed hseed x v a)
      (globalCarrier Gamma kappa hkappa hGamma seed hseed) := by
  apply Set.Subset.trans ?_
    ((coherentHammockIncrement_subset_rowAt hkappa hGamma hseed a).trans
      (rowAt_subset_globalCarrier hkappa hGamma hseed a))
  unfold coherentHammockIncrement
  apply Set.Subset.trans ?_ Set.subset_union_right
  apply Set.Subset.trans ?_ Set.subset_union_right
  apply Set.Subset.trans ?_ Set.subset_union_left
  unfold largeNondegenerateHammockIncrement
  dsimp only
  have hfrontier := (prior_geometry_eq_final
    (Gamma := Gamma) (kappa := kappa) hkappa hGamma hseed a).2
  rw [hfrontier]
  let q : EligiblePair _ _ _ := ⟨(x, .vertex v), helig⟩
  apply Set.subset_iUnion_of_subset q
  dsimp only [q]
  rw [← largeNondegenerateHammockAt_eq_prior
    (Gamma := Gamma) (kappa := kappa) hkappa hGamma hseed x v a]

/-- The two actual causal rows provide a contained successor-sized filtered
replacement for every eligible distinct finite pair with such a witness. -/
theorem exists_contained_limit_largeFilteredHammock
    (hkappa : aleph0 ≤ kappa) (hGamma : Gamma.IsNormalized)
    {seed : Set V} (hseed : #seed ≤ succ kappa)
    {x v : V} (hne : x ≠ v)
    (helig : HammockEligible
      (globalCarrier Gamma kappa hkappa hGamma seed hseed)
      (finalLadder Gamma kappa hkappa hGamma seed hseed).limitStrictRoof
      (finalLadder Gamma kappa hkappa hGamma seed hseed).limitRoof
      x (.vertex v))
    (hlarge : HasFilteredNondegenerateHammockCard Gamma
      (finalLadder Gamma kappa hkappa hGamma seed hseed).limitWarp
      x (.vertex v) (CoherentNondegenerateHammockTracker.CapturedByStageRoof
        (finalLadder Gamma kappa hkappa hGamma seed hseed)) (succ kappa)) :
    ∃ K : Set (AltPath Gamma.graph),
      FilteredNondegenerateHammock Gamma
        (finalLadder Gamma kappa hkappa hGamma seed hseed).limitWarp
        x (.vertex v) (CoherentNondegenerateHammockTracker.CapturedByStageRoof
          (finalLadder Gamma kappa hkappa hGamma seed hseed)) K ∧
      #K = succ kappa ∧
      HammockContained K (globalCarrier Gamma kappa hkappa hGamma seed hseed) := by
  have hlegal := finalLadder_halfwayGeometry
    (Gamma := Gamma) (kappa := kappa) hkappa hGamma hseed
  let zero : Ladder.Stage (succ kappa) :=
    ⟨0, (Cardinal.isRegular_succ hkappa).ord_pos⟩
  obtain ⟨b, _hzeroB, heligB⟩ := exists_later_hammockEligible
    (Gamma := Gamma) (kappa := kappa) hkappa hGamma hseed zero helig
  apply CoherentNondegenerateHammockTracker.exists_contained_limit_largeFilteredHammock
    hkappa hlegal hne b ?_ ?_ hlarge
  · intro a hba
    exact coherentNondegenerateHammockAt_contained hkappa hGamma hseed a x v
      (hammockEligible_mono
        (Gamma := Gamma) (kappa := kappa) hkappa hGamma hseed hba heligB)
  · intro a hba
    exact largeNondegenerateHammockAt_contained hkappa hGamma hseed a x v
      (hammockEligible_mono
        (Gamma := Gamma) (kappa := kappa) hkappa hGamma hseed hba heligB)

/-- Cardinal avoidance inside the actual global carrier, preserving both
nondegeneracy and the ordinary-stage roof certificate. -/
theorem exists_nondegenerate_path_in_globalCarrier_disjoint
    (hkappa : aleph0 ≤ kappa) (hGamma : Gamma.IsNormalized)
    {seed : Set V} (hseed : #seed ≤ succ kappa)
    {x v : V} (hne : x ≠ v)
    (helig : HammockEligible
      (globalCarrier Gamma kappa hkappa hGamma seed hseed)
      (finalLadder Gamma kappa hkappa hGamma seed hseed).limitStrictRoof
      (finalLadder Gamma kappa hkappa hGamma seed hseed).limitRoof
      x (.vertex v))
    (hlarge : HasFilteredNondegenerateHammockCard Gamma
      (finalLadder Gamma kappa hkappa hGamma seed hseed).limitWarp
      x (.vertex v) (CoherentNondegenerateHammockTracker.CapturedByStageRoof
        (finalLadder Gamma kappa hkappa hGamma seed hseed)) (succ kappa))
    {F : Set V} (hF : #F ≤ kappa) :
    ∃ Q : AltPath Gamma.graph,
      Q.vertexSet ⊆ globalCarrier Gamma kappa hkappa hGamma seed hseed ∧
      IsSafe (finalLadder Gamma kappa hkappa hGamma seed hseed).limitWarp Q ∧
      Q.initial = x ∧ HasEnd Q (.vertex v) ∧
      ¬IsDegenerate
        (finalLadder Gamma kappa hkappa hGamma seed hseed).limitWarp Q (.vertex v) ∧
      CoherentNondegenerateHammockTracker.CapturedByStageRoof
        (finalLadder Gamma kappa hkappa hGamma seed hseed) Q ∧
      Disjoint (hammockInterior x (.vertex v) Q) F := by
  obtain ⟨K, hK, hcard, hcontained⟩ :=
    exists_contained_limit_largeFilteredHammock hkappa hGamma hseed hne helig hlarge
  obtain ⟨Q, hQK, hsafe, hstart, hend, hnondeg, hdisj⟩ :=
    exists_mem_nondegenerateHammock_disjoint_of_mk_eq hK.1 hcard hF
  refine ⟨Q, ?_, hsafe, hstart, hend, hnondeg, hK.2 Q hQK, hdisj⟩
  intro w hw
  exact hcontained (Set.mem_iUnion.2 ⟨Q, Set.mem_iUnion.2 ⟨hQK, hw⟩⟩)

#print axioms largeNondegenerateHammockAt_eq_prior
#print axioms largeNondegenerateHammockAt_contained
#print axioms exists_contained_limit_largeFilteredHammock
#print axioms exists_nondegenerate_path_in_globalCarrier_disjoint

end Erdos599.Blueprint.LinkageBlueprint.CausalSection9Rows
