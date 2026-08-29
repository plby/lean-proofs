/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.UnroofedRegularRows

/-!
# Exact transport of actual unroofed closing-up registrations

Every pair or triple of final coordinates has a strict-prior causal owner.
The visible warp, frontier and request equal the final data at that owner,
so the exact chosen registrations belong to the actual completed carrier.
-/

noncomputable section

namespace Erdos599.CardinalInduction.UnroofedRegularRows

open Set Cardinal RegularRows RegularLocalizedProtectedRows

universe u

variable {V : Type u} (G : DWeb V) {kappa : Cardinal.{u}}
  (hregular : kappa.IsRegular) (huncountable : aleph0 < kappa)
  (hNorm : G.IsNormalized) (F : Set G.DPath) (hF : G.IsWarp F)
  (base : Set V) (hbase : #base ≤ kappa)

theorem registrationAt_subset_carrier (delta gamma : Ladder.Stage kappa) :
    let Q := rowRule G hregular huncountable hNorm F hF base hbase
    let L := DWeb.UnroofedMarker.causalLadder G Q hregular.aleph0_le
    RegularLocalizedProtectedRegistration.registrationAt L
        (finalRequest G Q hregular.aleph0_le) delta gamma ⊆
      (Q.rowSystem hregular.aleph0_le).carrier := by
  dsimp only
  let Q := rowRule G hregular huncountable hNorm F hF base hbase
  let owner := ownerStage hregular.aleph0_le delta gamma
  have hdelta : delta < owner := left_lt_ownerStage hregular.aleph0_le delta gamma
  have hgamma : gamma < owner := right_lt_ownerStage hregular.aleph0_le delta gamma
  have hcoordinate := RegularLocalizedProtectedRegistration.registrationAt_congr_stageData
    (DWeb.UnroofedMarker.priorCausalLadder_warpAt G Q hregular.aleph0_le
      owner delta hdelta.le)
    (priorRequest_eq_finalRequest_of_lt G Q hregular.aleph0_le hdelta hgamma)
  have hentry := pairEntry_subset_carrier G hregular huncountable hNorm F hF base hbase
    owner (⟨delta, hdelta⟩ : Set.Iio owner) (⟨gamma, hgamma⟩ : Set.Iio owner)
  intro x hx
  apply hentry
  apply Set.mem_union_right
  rw [← hcoordinate] at hx
  exact hx

theorem twoWarpRowRegistration_subset_carrier (i gamma : Ladder.Stage kappa) :
    let Q := rowRule G hregular huncountable hNorm F hF base hbase
    CausalRegular.twoWarpRowRegistration G F
        ((DWeb.UnroofedMarker.causalLadder G Q hregular.aleph0_le).warpAt gamma)
        (Q.state hregular.aleph0_le i).row ⊆
      (Q.rowSystem hregular.aleph0_le).carrier := by
  dsimp only
  let Q := rowRule G hregular huncountable hNorm F hF base hbase
  let owner := ownerStage hregular.aleph0_le i gamma
  have hi : i < owner := left_lt_ownerStage hregular.aleph0_le i gamma
  have hgamma : gamma < owner := right_lt_ownerStage hregular.aleph0_le i gamma
  have hwarp := DWeb.UnroofedMarker.priorCausalLadder_warpAt G Q hregular.aleph0_le
    owner gamma hgamma.le
  have hentry := pairEntry_subset_carrier G hregular huncountable hNorm F hF base hbase
    owner (⟨i, hi⟩ : Set.Iio owner) (⟨gamma, hgamma⟩ : Set.Iio owner)
  intro x hx
  apply hentry
  apply Set.mem_union_left
  rw [← hwarp] at hx
  exact hx

theorem finalTripleEntry_subset_carrier (delta beta gamma : Ladder.Stage kappa) :
    let Q := rowRule G hregular huncountable hNorm F hF base hbase
    let L := DWeb.UnroofedMarker.causalLadder G Q hregular.aleph0_le
    SliceCandidate.candidateVerticesAt G L (finalRequest G Q hregular.aleph0_le)
        delta beta gamma ∪
      RegularWeakSplitCandidate.registeredVerticesAt G L
        (finalRequest G Q hregular.aleph0_le) delta beta gamma ⊆
      (Q.rowSystem hregular.aleph0_le).carrier := by
  dsimp only
  let Q := rowRule G hregular huncountable hNorm F hF base hbase
  let middle := ownerStage hregular.aleph0_le delta beta
  let owner := ownerStage hregular.aleph0_le middle gamma
  have hmiddle : middle < owner := left_lt_ownerStage hregular.aleph0_le middle gamma
  have hdelta : delta < owner :=
    (left_lt_ownerStage hregular.aleph0_le delta beta).trans hmiddle
  have hbeta : beta < owner :=
    (right_lt_ownerStage hregular.aleph0_le delta beta).trans hmiddle
  have hgamma : gamma < owner := right_lt_ownerStage hregular.aleph0_le middle gamma
  have hwarpDelta := DWeb.UnroofedMarker.priorCausalLadder_warpAt G Q hregular.aleph0_le
    owner delta hdelta.le
  have hwarpBeta := DWeb.UnroofedMarker.priorCausalLadder_warpAt G Q hregular.aleph0_le
    owner beta hbeta.le
  have hfrontierDelta := DWeb.UnroofedMarker.priorCausalLadder_frontier G Q hregular.aleph0_le
    owner delta hdelta.le
  have hfrontierBeta := DWeb.UnroofedMarker.priorCausalLadder_frontier G Q hregular.aleph0_le
    owner beta hbeta.le
  have hrequest := priorRequest_eq_finalRequest_of_lt G Q hregular.aleph0_le hdelta hgamma
  have hordinary := SliceCandidate.candidateVerticesAt_congr_stageData
    hwarpDelta hwarpBeta hfrontierDelta hfrontierBeta hrequest
  have hweak := RegularWeakSplitCandidate.registeredVerticesAt_congr_stageData
    hwarpDelta hwarpBeta hfrontierDelta hfrontierBeta hrequest
  have hentry := tripleEntry_subset_carrier G hregular huncountable hNorm F hF base hbase
    owner (⟨delta, hdelta⟩ : Set.Iio owner) (⟨beta, hbeta⟩ : Set.Iio owner)
      (⟨gamma, hgamma⟩ : Set.Iio owner)
  intro x hx
  apply hentry
  rw [← hordinary, ← hweak] at hx
  exact hx

theorem candidateVerticesAt_subset_carrier (delta beta gamma : Ladder.Stage kappa) :
    let Q := rowRule G hregular huncountable hNorm F hF base hbase
    let L := DWeb.UnroofedMarker.causalLadder G Q hregular.aleph0_le
    SliceCandidate.candidateVerticesAt G L (finalRequest G Q hregular.aleph0_le)
        delta beta gamma ⊆ (Q.rowSystem hregular.aleph0_le).carrier :=
  Set.subset_union_left.trans (finalTripleEntry_subset_carrier G hregular huncountable
    hNorm F hF base hbase delta beta gamma)

theorem registeredVerticesAt_subset_carrier (delta beta gamma : Ladder.Stage kappa) :
    let Q := rowRule G hregular huncountable hNorm F hF base hbase
    let L := DWeb.UnroofedMarker.causalLadder G Q hregular.aleph0_le
    RegularWeakSplitCandidate.registeredVerticesAt G L (finalRequest G Q hregular.aleph0_le)
        delta beta gamma ⊆ (Q.rowSystem hregular.aleph0_le).carrier :=
  Set.subset_union_right.trans (finalTripleEntry_subset_carrier G hregular huncountable
    hNorm F hF base hbase delta beta gamma)

#print axioms registrationAt_subset_carrier
#print axioms twoWarpRowRegistration_subset_carrier
#print axioms candidateVerticesAt_subset_carrier
#print axioms registeredVerticesAt_subset_carrier

end Erdos599.CardinalInduction.UnroofedRegularRows
