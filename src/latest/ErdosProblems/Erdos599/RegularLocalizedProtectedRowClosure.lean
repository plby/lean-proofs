/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.RegularLocalizedProtectedRows
import ErdosProblems.Erdos599.RegularExtension

/-!
# Closure of the localized protected causal row

The repaired pair table retains the ordinary two-warp registration, while
the repaired triple table retains the complete weak-candidate registration.
Consequently its carrier has exactly the closure properties needed by the
canonical selected-successor recursion.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction
namespace RegularLocalizedProtectedRowClosure

universe u

variable {V : Type u}

open RegularLocalizedProtectedRows

private theorem pathsMeeting_eq_rowPathsMeeting
    (G : DWeb V) (F : Set G.DPath) (S : Set V) :
    RegularExtension.pathsMeeting G F S =
      RegularRows.CausalRegular.rowPathsMeeting G F S := by
  ext p
  constructor
  · rintro ⟨hpF, x, hxp, hxS⟩
    exact ⟨hpF, Set.not_disjoint_iff.2 ⟨x, hxp, hxS⟩⟩
  · rintro ⟨hpF, hpS⟩
    obtain ⟨x, hxp, hxS⟩ := Set.not_disjoint_iff.1 hpS
    exact ⟨hpF, x, hxp, hxS⟩

private theorem regularExtension_twoWarpRowRegistration_eq
    (G : DWeb V) (F Y : Set G.DPath) (S : Set V) :
    RegularExtension.twoWarpRowRegistration G F Y S =
      RegularRows.CausalRegular.twoWarpRowRegistration G F Y S := by
  unfold RegularExtension.twoWarpRowRegistration
    RegularRows.CausalRegular.twoWarpRowRegistration
  rw [pathsMeeting_eq_rowPathsMeeting G F S,
    pathsMeeting_eq_rowPathsMeeting G Y S]

/-- Every complete protected pair entry belongs to the final carrier. -/
theorem protectedPairEntry_subset_carrier
    (G : DWeb V) {kappa : Cardinal.{u}}
    (hregular : kappa.IsRegular) (huncountable : aleph0 < kappa)
    (hNorm : G.IsNormalized) (F : Set G.DPath) (hF : G.IsWarp F)
    (base : Set V) (hbase : #base ≤ kappa)
    (a : RegularCardinal.Stage kappa) (delta gamma : Set.Iio a) :
    let Q := rowRule G hregular huncountable hNorm F hF base hbase
    RegularLocalizedProtectedRegistration.protectedPairEntry G
        huncountable F a
          (fun b _hba ↦ Q.state hregular.aleph0_le b) delta gamma ⊆
      (Q.rowSystem hregular.aleph0_le).carrier := by
  dsimp only
  let Q := rowRule G hregular huncountable hNorm F hF base hbase
  let prior := fun b (_hba : b < a) ↦ Q.state hregular.aleph0_le b
  have hentry :
      RegularLocalizedProtectedRegistration.protectedPairEntry G
          huncountable F a prior delta gamma ⊆
        RegularRows.pairRegistrations a
          (RegularLocalizedProtectedRegistration.protectedPairEntry G
            huncountable F a prior) :=
    RegularRows.pair_entry_subset_registrations a _ delta gamma
  have hrow :
      RegularLocalizedProtectedRegistration.protectedPairEntry G
          huncountable F a prior delta gamma ⊆
        (Q.state hregular.aleph0_le a).row := by
    rw [RegularRows.CausalRowRule.state_row_eq]
    change _ ⊆
      (base ∪ RegularRows.pairRegistrations a
        (RegularLocalizedProtectedRegistration.protectedPairEntry G
          huncountable F a prior)) ∪
        RegularRows.tripleRegistrations a
          (protectedTripleEntry G hregular.aleph0_le a prior)
    exact hentry.trans (Set.subset_union_right.trans Set.subset_union_left)
  exact hrow.trans
    ((Q.rowSystem hregular.aleph0_le).row_subset_carrier a)

/-- The fixed base belongs to the repaired causal carrier. -/
theorem base_subset_carrier
    (G : DWeb V) {kappa : Cardinal.{u}}
    (hregular : kappa.IsRegular) (huncountable : aleph0 < kappa)
    (hNorm : G.IsNormalized) (F : Set G.DPath) (hF : G.IsWarp F)
    (base : Set V) (hbase : #base ≤ kappa) :
    let Q := rowRule G hregular huncountable hNorm F hF base hbase
    base ⊆ (Q.rowSystem hregular.aleph0_le).carrier := by
  dsimp only
  let Q := rowRule G hregular huncountable hNorm F hF base hbase
  let a : RegularCardinal.Stage kappa := ⟨0, hregular.ord_pos⟩
  have hrow : base ⊆ (Q.state hregular.aleph0_le a).row := by
    rw [RegularRows.CausalRowRule.state_row_eq]
    exact Set.subset_union_left.trans Set.subset_union_left
  exact hrow.trans
    ((Q.rowSystem hregular.aleph0_le).row_subset_carrier a)

/-- Every fixed-old-warp/current-row closure is registered at a later
causal owner. -/
theorem twoWarpRowRegistration_subset_carrier
    (G : DWeb V) {kappa : Cardinal.{u}}
    (hregular : kappa.IsRegular) (huncountable : aleph0 < kappa)
    (hNorm : G.IsNormalized) (F : Set G.DPath) (hF : G.IsWarp F)
    (base : Set V) (hbase : #base ≤ kappa)
    (i gamma : RegularCardinal.Stage kappa) :
    let Q := rowRule G hregular huncountable hNorm F hF base hbase
    RegularExtension.twoWarpRowRegistration G F
        ((G.canonicalLadderCore kappa
          (Q.preferred hregular.aleph0_le)).warpAt gamma)
        (Q.state hregular.aleph0_le i).row ⊆
      (Q.rowSystem hregular.aleph0_le).carrier := by
  dsimp only
  let Q := rowRule G hregular huncountable hNorm F hF base hbase
  let owner := ownerStage hregular.aleph0_le i gamma
  have hi : i < owner := left_lt_ownerStage hregular.aleph0_le i gamma
  have hgamma : gamma < owner :=
    right_lt_ownerStage hregular.aleph0_le i gamma
  let prior := fun c (_hca : c < owner) ↦ Q.state hregular.aleph0_le c
  have hpref : ∀ b, b < gamma →
      RegularRows.CausalRegular.preferredOfPrior owner prior b =
        Q.preferred hregular.aleph0_le b := by
    intro b hb
    simp only [RegularRows.CausalRegular.preferredOfPrior, prior,
      dif_pos (hb.trans hgamma), RegularRows.CausalRowRule.preferred]
  have hwarp :
      (RegularRows.CausalRegular.priorLadder G owner prior).warpAt gamma =
        (G.canonicalLadderCore kappa
          (Q.preferred hregular.aleph0_le)).warpAt gamma :=
    RegularRows.LadderPrefix.canonicalLadderCore_warpAt_eq_of_forall_lt
      G _ _ gamma hpref
  have hentry := protectedPairEntry_subset_carrier G hregular huncountable
    hNorm F hF base hbase owner
      (⟨i, hi⟩ : Set.Iio owner) (⟨gamma, hgamma⟩ : Set.Iio owner)
  intro x hx
  apply hentry
  apply Set.mem_union_left
  rw [← regularExtension_twoWarpRowRegistration_eq]
  rw [hwarp]
  simpa only [prior] using hx

/-- The repaired carrier closes the original complementary linkage around
every emitted row. -/
theorem carrier_registersOldLinkage
    (G : DWeb V) {kappa : Cardinal.{u}}
    (hregular : kappa.IsRegular) (huncountable : aleph0 < kappa)
    (hNorm : G.IsNormalized) (F : Set G.DPath) (hF : G.IsWarp F)
    (base : Set V) (hbase : #base ≤ kappa) :
    let Q := rowRule G hregular huncountable hNorm F hF base hbase
    let R := Q.rowSystem hregular.aleph0_le
    ∀ i, G.vertexSet (RegularExtension.pathsMeeting G F (R.row i)) ⊆
      R.carrier := by
  dsimp only
  let Q := rowRule G hregular huncountable hNorm F hF base hbase
  let R := Q.rowSystem hregular.aleph0_le
  let gamma : RegularCardinal.Stage kappa := ⟨0, hregular.ord_pos⟩
  intro i
  change G.vertexSet
      (RegularExtension.pathsMeeting G F
        (Q.state hregular.aleph0_le i).row) ⊆ R.carrier
  apply (RegularExtension.vertexSet_pathsMeeting_left_subset_twoWarpRowRegistration
    G F ((G.canonicalLadderCore kappa
      (Q.preferred hregular.aleph0_le)).warpAt gamma)
        (Q.state hregular.aleph0_le i).row).trans
  exact twoWarpRowRegistration_subset_carrier G hregular huncountable
    hNorm F hF base hbase i gamma

/-- The repaired carrier is closed under the limiting canonical warp. -/
theorem carrier_isLimitWarpClosed
    (G : DWeb V) {kappa : Cardinal.{u}}
    (hregular : kappa.IsRegular) (huncountable : aleph0 < kappa)
    (hNorm : G.IsNormalized) (F : Set G.DPath) (hF : G.IsWarp F)
    (base : Set V) (hbase : #base ≤ kappa) :
    let Q := rowRule G hregular huncountable hNorm F hF base hbase
    let R := Q.rowSystem hregular.aleph0_le
    let L := DWeb.KappaLadder.canonicalLadder G kappa
      (Q.preferred hregular.aleph0_le)
    SliceSplice.IsLimitWarpClosed G L R.carrier := by
  dsimp only
  let Q := rowRule G hregular huncountable hNorm F hF base hbase
  let R := Q.rowSystem hregular.aleph0_le
  let L := DWeb.KappaLadder.canonicalLadder G kappa
    (Q.preferred hregular.aleph0_le)
  have hNoEnter : G.NoEdgeEnters G.source := by
    intro x y hxy hy
    exact (hNorm hxy).1 hy
  have hsplit : L.IsSplitLegal :=
    DWeb.KappaLadder.canonicalLadder_isSplitLegal
      (Q.preferred hregular.aleph0_le) hregular huncountable hNoEnter
  have hgeometry : SliceSpliceConstructor.SpliceLadderGeometry G L :=
    ⟨hsplit.regular, hsplit.initialStage, hsplit.limitStages,
      hsplit.warpStages, hsplit.frontiersEssential,
      hsplit.frontierChronology, hsplit.strictFrontierChronology⟩
  change SliceSplice.IsLimitWarpClosed G L R.carrier
  apply RegularExtension.isLimitWarpClosed_of_rowRegistrations G hgeometry R
  intro i a
  change G.vertexSet
      (RegularExtension.pathsMeeting G (L.warpAt a)
        (Q.state hregular.aleph0_le i).row) ⊆ R.carrier
  exact
    (RegularExtension.vertexSet_pathsMeeting_right_subset_twoWarpRowRegistration
      G F (L.warpAt a) (Q.state hregular.aleph0_le i).row).trans
        (twoWarpRowRegistration_subset_carrier G hregular huncountable
          hNorm F hF base hbase i a)

/-- Every completed-ladder weak coordinate was inserted at its causal triple
owner. -/
theorem registeredVerticesAt_subset_carrier
    (G : DWeb V) {kappa : Cardinal.{u}}
    (hregular : kappa.IsRegular) (huncountable : aleph0 < kappa)
    (hNorm : G.IsNormalized) (F : Set G.DPath) (hF : G.IsWarp F)
    (base : Set V) (hbase : #base ≤ kappa)
    (delta beta gamma : RegularCardinal.Stage kappa) :
    let Q := rowRule G hregular huncountable hNorm F hF base hbase
    let L := G.canonicalLadderCore kappa
      (Q.preferred hregular.aleph0_le)
    RegularWeakSplitCandidate.registeredVerticesAt G L
        (RegularRows.CausalRegular.finalRequest G Q hregular.aleph0_le)
          delta beta gamma ⊆
      (Q.rowSystem hregular.aleph0_le).carrier := by
  dsimp only
  let Q := rowRule G hregular huncountable hNorm F hF base hbase
  let middle := ownerStage hregular.aleph0_le delta beta
  let owner := ownerStage hregular.aleph0_le middle gamma
  have hmiddle : middle < owner :=
    left_lt_ownerStage hregular.aleph0_le middle gamma
  have hdelta : delta < owner :=
    (left_lt_ownerStage hregular.aleph0_le delta beta).trans hmiddle
  have hbeta : beta < owner :=
    (right_lt_ownerStage hregular.aleph0_le delta beta).trans hmiddle
  have hgamma : gamma < owner :=
    right_lt_ownerStage hregular.aleph0_le middle gamma
  let prior := fun c (_hca : c < owner) ↦ Q.state hregular.aleph0_le c
  let Lprior := RegularRows.CausalRegular.priorLadder G owner prior
  let Lfinal := G.canonicalLadderCore kappa
    (Q.preferred hregular.aleph0_le)
  have hpref (a : RegularCardinal.Stage kappa) (ha : a < owner) :
      ∀ b, b < a → RegularRows.CausalRegular.preferredOfPrior
          owner prior b = Q.preferred hregular.aleph0_le b := by
    intro b hb
    simp only [RegularRows.CausalRegular.preferredOfPrior, prior,
      dif_pos (hb.trans ha), RegularRows.CausalRowRule.preferred]
  have hwarpDelta : Lprior.warpAt delta = Lfinal.warpAt delta :=
    RegularRows.LadderPrefix.canonicalLadderCore_warpAt_eq_of_forall_lt
      G _ _ delta (hpref delta hdelta)
  have hwarpBeta : Lprior.warpAt beta = Lfinal.warpAt beta :=
    RegularRows.LadderPrefix.canonicalLadderCore_warpAt_eq_of_forall_lt
      G _ _ beta (hpref beta hbeta)
  have hfrontierDelta : Lprior.frontier delta = Lfinal.frontier delta :=
    RegularRows.LadderPrefix.canonicalLadderCore_frontier_eq_of_forall_lt
      G _ _ delta (hpref delta hdelta)
  have hfrontierBeta : Lprior.frontier beta = Lfinal.frontier beta :=
    RegularRows.LadderPrefix.canonicalLadderCore_frontier_eq_of_forall_lt
      G _ _ beta (hpref beta hbeta)
  have hrequest : RegularRows.CausalRegular.priorRequest G
      hregular.aleph0_le owner prior delta gamma =
      RegularRows.CausalRegular.finalRequest G Q hregular.aleph0_le
        delta gamma :=
    priorRequest_eq_finalRequest_of_lt Q hregular.aleph0_le hdelta hgamma
  have hcoordinate :=
    RegularWeakSplitCandidate.registeredVerticesAt_congr_stageData
      hwarpDelta hwarpBeta hfrontierDelta hfrontierBeta hrequest
  have hentry : protectedTripleEntry G hregular.aleph0_le owner prior
      (⟨delta, hdelta⟩ : Set.Iio owner)
      (⟨beta, hbeta⟩ : Set.Iio owner)
      (⟨gamma, hgamma⟩ : Set.Iio owner) ⊆
      (Q.rowSystem hregular.aleph0_le).carrier := by
    have hregistered : protectedTripleEntry G hregular.aleph0_le owner prior
        (⟨delta, hdelta⟩ : Set.Iio owner)
        (⟨beta, hbeta⟩ : Set.Iio owner)
        (⟨gamma, hgamma⟩ : Set.Iio owner) ⊆
        RegularRows.tripleRegistrations owner
          (protectedTripleEntry G hregular.aleph0_le owner prior) :=
      RegularRows.triple_entry_subset_registrations owner _ _ _ _
    have hrow : protectedTripleEntry G hregular.aleph0_le owner prior
        (⟨delta, hdelta⟩ : Set.Iio owner)
        (⟨beta, hbeta⟩ : Set.Iio owner)
        (⟨gamma, hgamma⟩ : Set.Iio owner) ⊆
        (Q.state hregular.aleph0_le owner).row := by
      rw [RegularRows.CausalRowRule.state_row_eq]
      exact hregistered.trans Set.subset_union_right
    exact hrow.trans
      ((Q.rowSystem hregular.aleph0_le).row_subset_carrier owner)
  intro x hx
  apply hentry
  apply Set.mem_union_right
  change x ∈ RegularWeakSplitCandidate.registeredVerticesAt G Lprior
    (RegularRows.CausalRegular.priorRequest G hregular.aleph0_le owner prior)
      delta beta gamma
  rw [hcoordinate]
  exact hx

#print axioms carrier_isLimitWarpClosed
#print axioms registeredVerticesAt_subset_carrier

end RegularLocalizedProtectedRowClosure
end CardinalInduction
end Erdos599
