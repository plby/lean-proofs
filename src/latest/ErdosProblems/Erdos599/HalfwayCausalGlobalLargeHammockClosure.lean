/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayCausalSection9Rows
import ErdosProblems.Erdos599.DeferredStageHammockTransport

/-!
# Global large-hammock closure of the causal Section 9 carrier

The causal rows select maximal hammocks for the full reference visible at
each stage.  A fixed `kappa`-sized limiting hammock is small relative to
the `kappa^+`-long ladder, so all of its paths become safe at one common
stage.  After also waiting for the two endpoints and their roof witnesses,
the stage selection has cardinality exactly `kappa`; uniform endpoint
transport then makes that selected hammock a limiting-reference hammock.

This proves the exact large-hammock closure needed for imaginary-edge
arguments.  It deliberately does not claim full limiting maximality in the
small branch of `MaximalUpTo`; that branch requires coherent, seeded
maximal choices rather than the independent stage choices used here.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599.Blueprint.LinkageBlueprint

open DirectedPath _root_.Erdos599.Alternating Ladder Blueprint
open CardinalInduction.RegularRows

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

namespace CausalSection9Rows

private def laterThanThree {rho : Cardinal.{u}}
    (hrho : aleph0 ≤ rho) (a b c : Ladder.Stage rho) :
    Ladder.Stage rho :=
  ⟨max (max a.1 b.1) c.1 + 1,
    (Cardinal.isSuccLimit_ord hrho).succ_lt
      (max_lt (max_lt a.2 b.2) c.2)⟩

private theorem first_lt_laterThanThree {rho : Cardinal.{u}}
    (hrho : aleph0 ≤ rho) (a b c : Ladder.Stage rho) :
    a < laterThanThree hrho a b c := by
  change a.1 < max (max a.1 b.1) c.1 + 1
  exact (le_max_left a.1 b.1).trans (le_max_left _ c.1)
    |>.trans_lt (lt_add_one _)

private theorem second_lt_laterThanThree {rho : Cardinal.{u}}
    (hrho : aleph0 ≤ rho) (a b c : Ladder.Stage rho) :
    b < laterThanThree hrho a b c := by
  change b.1 < max (max a.1 b.1) c.1 + 1
  exact (le_max_right a.1 b.1).trans (le_max_left _ c.1)
    |>.trans_lt (lt_add_one _)

private theorem third_lt_laterThanThree {rho : Cardinal.{u}}
    (hrho : aleph0 ≤ rho) (a b c : Ladder.Stage rho) :
    c < laterThanThree hrho a b c := by
  change c.1 < max (max a.1 b.1) c.1 + 1
  exact (le_max_right (max a.1 b.1) c.1).trans_lt (lt_add_one _)

/-- Actual one-sided geometry of the final ladder driven by the seeded rows. -/
theorem finalLadder_halfwayGeometry
    (hkappa : aleph0 ≤ kappa) (hGamma : Gamma.IsNormalized)
    {seed : Set V} (hseed : #seed ≤ succ kappa) :
    DWeb.KappaLadder.Deferred.HalfwayGeometry
      (finalLadder Gamma kappa hkappa hGamma seed hseed) := by
  have hNoEnter : Gamma.NoEdgeEnters Gamma.source := by
    intro x y hxy hy
    exact (hGamma hxy).1 hy
  exact UnroofedHalfwayRowLadder.deferred_halfwayGeometry
    ((rule Gamma kappa hkappa hGamma seed hseed).preferred
      (hkappa.trans (le_succ kappa)))
    (Cardinal.isRegular_succ hkappa) (hkappa.trans_lt (lt_succ kappa)) hNoEnter

/-- A globally eligible endpoint pair becomes eligible for the actual
strict-prior row geometry at some stage above any prescribed threshold. -/
theorem exists_later_hammockEligible
    (hkappa : aleph0 ≤ kappa) (hGamma : Gamma.IsNormalized)
    {seed : Set V} (hseed : #seed ≤ succ kappa)
    (a0 : Ladder.Stage (succ kappa)) {u : V} {e : AltEnd V}
    (helig : HammockEligible
      (globalCarrier Gamma kappa hkappa hGamma seed hseed)
      (finalLadder Gamma kappa hkappa hGamma seed hseed).limitStrictRoof
      (finalLadder Gamma kappa hkappa hGamma seed hseed).limitRoof u e) :
    ∃ b : Ladder.Stage (succ kappa), a0 < b ∧
      HammockEligible
        (priorCarrier b (fun c _hcb ↦
          (rule Gamma kappa hkappa hGamma seed hseed).state
            (hkappa.trans (le_succ kappa)) c))
        (Gamma.strictRoof
          ((finalLadder Gamma kappa hkappa hGamma seed hseed).frontier b))
        (Gamma.roof
          ((finalLadder Gamma kappa hkappa hGamma seed hseed).frontier b))
        u e := by
  let hsucc : aleph0 ≤ succ kappa := hkappa.trans (le_succ kappa)
  let Q := rule Gamma kappa hkappa hGamma seed hseed
  let L := finalLadder Gamma kappa hkappa hGamma seed hseed
  have hlegal := finalLadder_halfwayGeometry
    (Gamma := Gamma) (kappa := kappa) hkappa hGamma hseed
  have huCarrier : u ∈ (Q.rowSystem hsucc).carrier := helig.1.1
  obtain ⟨cu, hucu⟩ := RowSystem.mem_carrier.mp huCarrier
  obtain ⟨du, hudu⟩ := Set.mem_iUnion.1 helig.1.2
  have hroof_mono {i j : Ladder.Stage (succ kappa)} (hij : i ≤ j) :
      Gamma.roof (L.frontier i) ⊆ Gamma.roof (L.frontier j) := by
    rcases hij.lt_or_eq with hij | rfl
    · exact Gamma.roof_cut (hlegal.frontierChronology hij)
    · exact fun _ hx ↦ hx
  have hstrict_mono {i j : Ladder.Stage (succ kappa)} (hij : i ≤ j) :
      Gamma.strictRoof (L.frontier i) ⊆
        Gamma.strictRoof (L.frontier j) := by
    rcases hij.lt_or_eq with hij | rfl
    · intro x hx
      refine ⟨Gamma.roof_cut (hlegal.frontierChronology hij) hx.1, ?_⟩
      intro hxEssential
      have hxFrontier : x ∈ L.frontier j := by
        rw [← hlegal.frontiersEssential j]
        exact hxEssential
      exact Set.disjoint_left.1 (hlegal.strictFrontierChronology hij)
        hx hxFrontier
    · exact fun _ hx ↦ hx
  cases e with
  | infinity =>
      let b := laterThanThree hsucc a0 cu du
      have ha0b := first_lt_laterThanThree hsucc a0 cu du
      have hcub := second_lt_laterThanThree hsucc a0 cu du
      have hdub := third_lt_laterThanThree hsucc a0 cu du
      refine ⟨b, ha0b, ⟨⟨?_, ?_⟩, trivial⟩⟩
      · exact Set.mem_iUnion.2 ⟨⟨cu, hcub⟩, hucu⟩
      · exact hstrict_mono hdub.le hudu
  | vertex v =>
      have hvCarrier : v ∈ (Q.rowSystem hsucc).carrier := helig.2.1
      obtain ⟨cv, hvcv⟩ := RowSystem.mem_carrier.mp hvCarrier
      obtain ⟨dv, hvdv⟩ := Set.mem_iUnion.1 helig.2.2
      let b1 := laterThanThree hsucc a0 cu du
      let b := laterThanThree hsucc b1 cv dv
      have ha0b1 := first_lt_laterThanThree hsucc a0 cu du
      have hcub1 := second_lt_laterThanThree hsucc a0 cu du
      have hdub1 := third_lt_laterThanThree hsucc a0 cu du
      have hb1b := first_lt_laterThanThree hsucc b1 cv dv
      have hcvb := second_lt_laterThanThree hsucc b1 cv dv
      have hdvb := third_lt_laterThanThree hsucc b1 cv dv
      refine ⟨b, ha0b1.trans hb1b, ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩⟩
      · exact Set.mem_iUnion.2 ⟨⟨cu, hcub1.trans hb1b⟩, hucu⟩
      · exact hstrict_mono (hdub1.trans hb1b).le hudu
      · exact Set.mem_iUnion.2 ⟨⟨cv, hcvb⟩, hvcv⟩
      · exact hroof_mono hdvb.le hvdv

/-- The actual causal carrier is closed under every exact-`kappa` limiting
hammock requirement.  This is the large branch of Assertion 9.22 and is
the branch used to retain witnesses of imaginary edges. -/
theorem largeHammockClosed_limitWarp
    (hkappa : aleph0 ≤ kappa) (hGamma : Gamma.IsNormalized)
    {seed : Set V} (hseed : #seed ≤ succ kappa) :
    LargeHammockClosed Gamma
      (finalLadder Gamma kappa hkappa hGamma seed hseed).limitWarp
      (globalCarrier Gamma kappa hkappa hGamma seed hseed)
      (globalCarrier Gamma kappa hkappa hGamma seed hseed)
      (finalLadder Gamma kappa hkappa hGamma seed hseed).limitStrictRoof
      (finalLadder Gamma kappa hkappa hGamma seed hseed).limitRoof
      kappa := by
  intro u e helig hlarge
  let L := finalLadder Gamma kappa hkappa hGamma seed hseed
  have hlegal := finalLadder_halfwayGeometry
    (Gamma := Gamma) (kappa := kappa) hkappa hGamma hseed
  obtain ⟨H, hH, hHcard⟩ := hlarge
  have hHsmall : #H < succ kappa := by
    rw [hHcard]
    exact lt_succ kappa
  obtain ⟨aSafe, hSafe⟩ :=
    hlegal.exists_eventually_hammock_warpAt hH hHsmall
  obtain ⟨aGlobal, hGlobal⟩ :=
    hlegal.exists_eventually_hammock_limitWarp u e
  let a0 : Ladder.Stage (succ kappa) := max aSafe aGlobal
  obtain ⟨b, ha0b, heligStage⟩ := exists_later_hammockEligible
    (Gamma := Gamma) (kappa := kappa) hkappa hGamma hseed a0 helig
  have haSafeB : aSafe ≤ b :=
    (le_max_left aSafe aGlobal).trans ha0b.le
  have haGlobalB : aGlobal ≤ b :=
    (le_max_right aSafe aGlobal).trans ha0b.le
  have hHstage : Hammock Gamma (L.warpAt b) u e H :=
    hSafe b haSafeB
  let q : EligiblePair
      (priorCarrier b (fun c _hcb ↦
        (rule Gamma kappa hkappa hGamma seed hseed).state
          (hkappa.trans (le_succ kappa)) c))
      (Gamma.strictRoof (L.frontier b)) (Gamma.roof (L.frontier b)) :=
    ⟨(u, e), heligStage⟩
  let K : Set (AltPath Gamma.graph) := chosenHammock Gamma
    (L.warpAt b) kappa q
  have hKstage : Hammock Gamma (L.warpAt b) u e K :=
    (chosenHammock_spec Gamma (L.warpAt b) kappa q).isHammock
  have hKcard : #K = kappa :=
    chosenHammock_card_eq_of_hasHammockCard Gamma (L.warpAt b) kappa q
      ⟨H, hHstage, hHcard⟩
  have hKglobal : Hammock Gamma L.limitWarp u e K :=
    hGlobal b haGlobalB K hKstage
  refine ⟨K, hKglobal, hKcard, ?_⟩
  exact (chosenHammock_contained_all Gamma (L.warpAt b) kappa q).mono
    ((selectedHammocks_subset_rowAt hkappa hGamma hseed b).trans
      (rowAt_subset_globalCarrier hkappa hGamma hseed b))

#print axioms CausalSection9Rows.exists_later_hammockEligible
#print axioms CausalSection9Rows.largeHammockClosed_limitWarp

end CausalSection9Rows
end Erdos599.Blueprint.LinkageBlueprint
