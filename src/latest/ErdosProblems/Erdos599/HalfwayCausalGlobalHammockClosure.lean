/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayCausalGlobalLargeHammockClosure
import ErdosProblems.Erdos599.CoherentHammockLimit
import ErdosProblems.Erdos599.CoherentHammockLargeLimit

/-!
# Full limiting hammock closure of the causal Section 9 carrier

The coherent `kappa`-tracker added to every causal row turns the stagewise
maximal choices into a genuinely maximal-up-to-`kappa` hammock for the
limiting reference.  Once an endpoint pair becomes eligible, prior-row
membership and both roof conditions persist at all later stages.  Hence
every member of the coherent tail is inserted in the causal global carrier,
and `CoherentHammockLimit` supplies the required limiting maximal family.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599.Blueprint.LinkageBlueprint

open DirectedPath _root_.Erdos599.Alternating Ladder Blueprint
open CardinalInduction.RegularRows

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

namespace CausalSection9Rows

/-- Eligibility for the concrete strict-prior row geometry persists along
the final causal ladder. -/
theorem hammockEligible_mono
    (hkappa : aleph0 ≤ kappa) (hGamma : Gamma.IsNormalized)
    {seed : Set V} (hseed : #seed ≤ succ kappa)
    {b a : Ladder.Stage (succ kappa)} (hba : b ≤ a)
    {u : V} {e : AltEnd V}
    (helig : HammockEligible
      (priorCarrier b (fun c _hcb ↦
        (rule Gamma kappa hkappa hGamma seed hseed).state
          (hkappa.trans (le_succ kappa)) c))
      (Gamma.strictRoof
        ((finalLadder Gamma kappa hkappa hGamma seed hseed).frontier b))
      (Gamma.roof
        ((finalLadder Gamma kappa hkappa hGamma seed hseed).frontier b))
      u e) :
    HammockEligible
      (priorCarrier a (fun c _hca ↦
        (rule Gamma kappa hkappa hGamma seed hseed).state
          (hkappa.trans (le_succ kappa)) c))
      (Gamma.strictRoof
        ((finalLadder Gamma kappa hkappa hGamma seed hseed).frontier a))
      (Gamma.roof
        ((finalLadder Gamma kappa hkappa hGamma seed hseed).frontier a))
      u e := by
  let L := finalLadder Gamma kappa hkappa hGamma seed hseed
  have hlegal := finalLadder_halfwayGeometry
    (Gamma := Gamma) (kappa := kappa) hkappa hGamma hseed
  have hprior_mono :
      priorCarrier b (fun c _hcb ↦
        (rule Gamma kappa hkappa hGamma seed hseed).state
          (hkappa.trans (le_succ kappa)) c) ⊆
      priorCarrier a (fun c _hca ↦
        (rule Gamma kappa hkappa hGamma seed hseed).state
          (hkappa.trans (le_succ kappa)) c) := by
    intro x hx
    obtain ⟨c, hxc⟩ := Set.mem_iUnion.1 hx
    exact Set.mem_iUnion.2 ⟨⟨c.1, c.2.trans_le hba⟩, hxc⟩
  have hstrict_mono :
      Gamma.strictRoof (L.frontier b) ⊆
        Gamma.strictRoof (L.frontier a) := by
    rcases hba.lt_or_eq with hba | rfl
    · intro x hx
      refine ⟨Gamma.roof_cut (hlegal.frontierChronology hba) hx.1, ?_⟩
      intro hxEssential
      have hxFrontier : x ∈ L.frontier a := by
        rw [← hlegal.frontiersEssential a]
        exact hxEssential
      exact Set.disjoint_left.1 (hlegal.strictFrontierChronology hba)
        hx hxFrontier
    · exact fun _ hx ↦ hx
  have hroof_mono :
      Gamma.roof (L.frontier b) ⊆ Gamma.roof (L.frontier a) := by
    rcases hba.lt_or_eq with hba | rfl
    · exact Gamma.roof_cut (hlegal.frontierChronology hba)
    · exact fun _ hx ↦ hx
  cases e with
  | infinity =>
      exact ⟨⟨hprior_mono helig.1.1, hstrict_mono helig.1.2⟩, trivial⟩
  | vertex v =>
      exact ⟨⟨hprior_mono helig.1.1, hstrict_mono helig.1.2⟩,
        ⟨hprior_mono helig.2.1, hroof_mono helig.2.2⟩⟩

/-- The causal Section 9 carrier satisfies the full limiting-reference
hammock closure from Assertion 9.22, with no external roof-hammock premise. -/
theorem hammockClosed_limitWarp
    (hkappa : aleph0 ≤ kappa) (hGamma : Gamma.IsNormalized)
    {seed : Set V} (hseed : #seed ≤ succ kappa) :
    HammockClosedUpTo Gamma
      (finalLadder Gamma kappa hkappa hGamma seed hseed).limitWarp
      (globalCarrier Gamma kappa hkappa hGamma seed hseed)
      (globalCarrier Gamma kappa hkappa hGamma seed hseed)
      (finalLadder Gamma kappa hkappa hGamma seed hseed).limitStrictRoof
      (finalLadder Gamma kappa hkappa hGamma seed hseed).limitRoof
      kappa := by
  intro u e helig
  let L := finalLadder Gamma kappa hkappa hGamma seed hseed
  have hlegal := finalLadder_halfwayGeometry
    (Gamma := Gamma) (kappa := kappa) hkappa hGamma hseed
  let zero : Ladder.Stage (succ kappa) :=
    ⟨0, (Cardinal.isRegular_succ hkappa).ord_pos⟩
  obtain ⟨b, _hzeroB, heligB⟩ := exists_later_hammockEligible
    (Gamma := Gamma) (kappa := kappa) hkappa hGamma hseed zero helig
  apply CoherentHammockTracker.exists_contained_limit_maximalUpTo
    hkappa hlegal u e b
  intro a hba
  have heligA := hammockEligible_mono
    (Gamma := Gamma) (kappa := kappa) hkappa hGamma hseed hba heligB
  let q : EligiblePair
      (priorCarrier a (fun c _hca ↦
        (rule Gamma kappa hkappa hGamma seed hseed).state
          (hkappa.trans (le_succ kappa)) c))
      (Gamma.strictRoof (L.frontier a)) (Gamma.roof (L.frontier a)) :=
    ⟨(u, e), heligA⟩
  exact coherentHammockAt_contained
    (Gamma := Gamma) (kappa := kappa) hkappa hGamma hseed a q

/-- The same actual carrier retains a successor-sized limiting hammock for
every globally eligible pair which has one.  The old `kappa^+` stage
selection supplies the local large replacement required by the coherent
limit argument. -/
theorem largeHammockClosed_limitWarp_succ
    (hkappa : aleph0 ≤ kappa) (hGamma : Gamma.IsNormalized)
    {seed : Set V} (hseed : #seed ≤ succ kappa) :
    LargeHammockClosed Gamma
      (finalLadder Gamma kappa hkappa hGamma seed hseed).limitWarp
      (globalCarrier Gamma kappa hkappa hGamma seed hseed)
      (globalCarrier Gamma kappa hkappa hGamma seed hseed)
      (finalLadder Gamma kappa hkappa hGamma seed hseed).limitStrictRoof
      (finalLadder Gamma kappa hkappa hGamma seed hseed).limitRoof
      (succ kappa) := by
  intro u e helig hGlobalLarge
  let L := finalLadder Gamma kappa hkappa hGamma seed hseed
  have hlegal := finalLadder_halfwayGeometry
    (Gamma := Gamma) (kappa := kappa) hkappa hGamma hseed
  let zero : Ladder.Stage (succ kappa) :=
    ⟨0, (Cardinal.isRegular_succ hkappa).ord_pos⟩
  obtain ⟨b, _hzeroB, heligB⟩ := exists_later_hammockEligible
    (Gamma := Gamma) (kappa := kappa) hkappa hGamma hseed zero helig
  apply CoherentHammockTracker.exists_contained_limit_largeHammock
    hkappa hlegal u e b
  · intro a hba
    have heligA := hammockEligible_mono
      (Gamma := Gamma) (kappa := kappa) hkappa hGamma hseed hba heligB
    let q : EligiblePair
        (priorCarrier a (fun c _hca ↦
          (rule Gamma kappa hkappa hGamma seed hseed).state
            (hkappa.trans (le_succ kappa)) c))
        (Gamma.strictRoof (L.frontier a)) (Gamma.roof (L.frontier a)) :=
      ⟨(u, e), heligA⟩
    exact coherentHammockAt_contained
      (Gamma := Gamma) (kappa := kappa) hkappa hGamma hseed a q
  · intro a hba hLocalLarge
    have heligA := hammockEligible_mono
      (Gamma := Gamma) (kappa := kappa) hkappa hGamma hseed hba heligB
    let q : EligiblePair
        (priorCarrier a (fun c _hca ↦
          (rule Gamma kappa hkappa hGamma seed hseed).state
            (hkappa.trans (le_succ kappa)) c))
        (Gamma.strictRoof (L.frontier a)) (Gamma.roof (L.frontier a)) :=
      ⟨(u, e), heligA⟩
    let K : Set (AltPath Gamma.graph) :=
      chosenHammock Gamma (L.warpAt a) (succ kappa) q
    refine ⟨K,
      (chosenHammock_spec Gamma (L.warpAt a) (succ kappa) q).isHammock,
      chosenHammock_card_eq_of_hasHammockCard Gamma (L.warpAt a)
        (succ kappa) q hLocalLarge, ?_⟩
    exact (chosenHammock_contained_all Gamma (L.warpAt a)
        (succ kappa) q).mono
      ((selectedHammocksSucc_subset_rowAt hkappa hGamma hseed a).trans
        (rowAt_subset_globalCarrier hkappa hGamma hseed a))
  · exact hGlobalLarge

#print axioms CausalSection9Rows.hammockEligible_mono
#print axioms CausalSection9Rows.hammockClosed_limitWarp
#print axioms CausalSection9Rows.largeHammockClosed_limitWarp_succ

end CausalSection9Rows
end Erdos599.Blueprint.LinkageBlueprint
