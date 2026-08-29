/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.UnroofedMarkerCausal
import ErdosProblems.Erdos599.RegularLocalizedProtectedRows

/-!
# Actual protected rows for the unroofed-marker protocol

All registrations are evaluated on the new strict-prior ladder. The old
row rule is not identified with this rule. Only its already proved
cardinality bounds for visible registrations and its owner stages are reused.
-/

noncomputable section

namespace Erdos599.CardinalInduction.UnroofedRegularRows

open Set Cardinal RegularRows

universe u

variable {V : Type u} (G : DWeb V) {kappa : Cardinal.{u}}

def priorLadder (a : Ladder.Stage kappa)
    (prior : ∀ b : Ladder.Stage kappa, b < a → CausalState kappa V) :
    G.KappaLadder kappa :=
  DWeb.UnroofedMarker.ladder G kappa (CausalRegular.preferredOfPrior a prior)

def priorRequest (hkappa : aleph0 ≤ kappa) (a : Ladder.Stage kappa)
    (prior : ∀ b : Ladder.Stage kappa, b < a → CausalState kappa V) :
    Ladder.Stage kappa → Ladder.Stage kappa → Set V :=
  ControlledSlices.diagonalRequest (priorLadder G a prior).frontier
    (CausalRegular.priorEnumeration hkappa a prior)

def finalRequest (Q : CausalRowRule kappa V) (hkappa : aleph0 ≤ kappa) :
    Ladder.Stage kappa → Ladder.Stage kappa → Set V :=
  ControlledSlices.diagonalRequest (DWeb.UnroofedMarker.causalLadder G Q hkappa).frontier
    (CausalRegular.actualEnumeration Q hkappa)

def pairEntry (hkappa : aleph0 ≤ kappa) (F : Set G.DPath) (a : Ladder.Stage kappa)
    (prior : ∀ b : Ladder.Stage kappa, b < a → CausalState kappa V)
    (delta gamma : Set.Iio a) : Set V :=
  CausalRegular.twoWarpRowRegistration G F ((priorLadder G a prior).warpAt gamma.1)
      (prior delta.1 delta.2).row ∪
    RegularLocalizedProtectedRegistration.registrationAt (priorLadder G a prior)
      (priorRequest G hkappa a prior) delta.1 gamma.1

theorem mk_pairEntry_le (hregular : kappa.IsRegular) (huncountable : aleph0 < kappa)
    (hNorm : G.IsNormalized) (F : Set G.DPath) (hF : G.IsWarp F) (a : Ladder.Stage kappa)
    (prior : ∀ b : Ladder.Stage kappa, b < a → CausalState kappa V)
    (delta gamma : Set.Iio a) :
    #(pairEntry G hregular.aleph0_le F a prior delta gamma) ≤ kappa := by
  have hNoEnter : G.NoEdgeEnters G.source := by
    intro x y hxy hy
    exact (hNorm hxy).1 hy
  apply (Cardinal.mk_union_le _ _).trans
  apply Cardinal.add_le_of_le hregular.aleph0_le
  · exact CausalRegular.mk_twoWarpRowRegistration_le G hregular.aleph0_le hF
      ((DWeb.UnroofedMarker.ladder_geometry G kappa
        (CausalRegular.preferredOfPrior a prior) hNoEnter).warpStages
          (Ladder.Stage.toExtended gamma.1)) (prior delta.1 delta.2).row_mk_le
  · exact (RegularLocalizedProtectedRegistration.mk_registration_lt hregular huncountable
      (RegularCandidateProvider.stageWeb_isNormalized hNorm
        (priorLadder G a prior) delta.1)).le

def tripleEntry (hkappa : aleph0 ≤ kappa) (a : Ladder.Stage kappa)
    (prior : ∀ b : Ladder.Stage kappa, b < a → CausalState kappa V)
    (delta beta gamma : Set.Iio a) : Set V :=
  SliceCandidate.candidateVerticesAt G (priorLadder G a prior)
      (priorRequest G hkappa a prior) delta.1 beta.1 gamma.1 ∪
    RegularWeakSplitCandidate.registeredVerticesAt G (priorLadder G a prior)
      (priorRequest G hkappa a prior) delta.1 beta.1 gamma.1

theorem mk_tripleEntry_le (hregular : kappa.IsRegular) (a : Ladder.Stage kappa)
    (prior : ∀ b : Ladder.Stage kappa, b < a → CausalState kappa V)
    (delta beta gamma : Set.Iio a) :
    #(tripleEntry G hregular.aleph0_le a prior delta beta gamma) ≤ kappa := by
  exact (Cardinal.mk_union_le _ _).trans (Cardinal.add_le_of_le hregular.aleph0_le
    (SliceCandidate.mk_candidateVerticesAt_le hregular (priorLadder G a prior)
      (priorRequest G hregular.aleph0_le a prior) delta.1 beta.1 gamma.1)
    (RegularWeakSplitCandidate.mk_registeredVerticesAt_le hregular.aleph0_le G
      (priorLadder G a prior) (priorRequest G hregular.aleph0_le a prior)
        delta.1 beta.1 gamma.1))

def rowRule (hregular : kappa.IsRegular) (huncountable : aleph0 < kappa)
    (hNorm : G.IsNormalized) (F : Set G.DPath) (hF : G.IsWarp F)
    (base : Set V) (hbase : #base ≤ kappa) : CausalRowRule kappa V :=
  ofRegistrationTables hregular.aleph0_le base hbase
    (pairEntry G hregular.aleph0_le F) (tripleEntry G hregular.aleph0_le)
    (mk_pairEntry_le G hregular huncountable hNorm F hF) (mk_tripleEntry_le G hregular)

theorem priorRequest_eq_finalRequest_of_lt (Q : CausalRowRule kappa V)
    (hkappa : aleph0 ≤ kappa) {c delta gamma : Ladder.Stage kappa}
    (hdelta : delta < c) (hgamma : gamma < c) :
    priorRequest G hkappa c (fun b _hbc ↦ Q.state hkappa b) delta gamma =
      finalRequest G Q hkappa delta gamma := by
  have hfrontier :
      (priorLadder G c (fun b _hbc ↦ Q.state hkappa b)).frontier delta =
        (DWeb.UnroofedMarker.causalLadder G Q hkappa).frontier delta :=
    DWeb.UnroofedMarker.priorCausalLadder_frontier G Q hkappa c delta hdelta.le
  ext x
  simp only [priorRequest, finalRequest, ControlledSlices.diagonalRequest,
    Set.mem_inter_iff, hfrontier]
  constructor
  · rintro ⟨hxfrontier, theta, eta, htheta, heta, hx⟩
    refine ⟨hxfrontier, theta, eta, htheta, heta, ?_⟩
    rw [CausalRegular.priorEnumeration_eq_actual_of_lt Q hkappa (htheta.trans hgamma)] at hx
    exact hx
  · rintro ⟨hxfrontier, theta, eta, htheta, heta, hx⟩
    refine ⟨hxfrontier, theta, eta, htheta, heta, ?_⟩
    rw [CausalRegular.priorEnumeration_eq_actual_of_lt Q hkappa (htheta.trans hgamma)]
    exact hx

variable (hregular : kappa.IsRegular) (huncountable : aleph0 < kappa)
  (hNorm : G.IsNormalized) (F : Set G.DPath) (hF : G.IsWarp F)
  (base : Set V) (hbase : #base ≤ kappa)

theorem base_subset_carrier :
    let Q := rowRule G hregular huncountable hNorm F hF base hbase
    base ⊆ (Q.rowSystem hregular.aleph0_le).carrier := by
  dsimp only
  let Q := rowRule G hregular huncountable hNorm F hF base hbase
  let a : Ladder.Stage kappa := ⟨0, hregular.ord_pos⟩
  have hrow : base ⊆ (Q.state hregular.aleph0_le a).row := by
    rw [CausalRowRule.state_row_eq]
    exact Set.subset_union_left.trans Set.subset_union_left
  exact hrow.trans ((Q.rowSystem hregular.aleph0_le).row_subset_carrier a)

theorem pairEntry_subset_carrier (a : Ladder.Stage kappa) (delta gamma : Set.Iio a) :
    let Q := rowRule G hregular huncountable hNorm F hF base hbase
    pairEntry G hregular.aleph0_le F a (fun b _hba ↦ Q.state hregular.aleph0_le b)
        delta gamma ⊆ (Q.rowSystem hregular.aleph0_le).carrier := by
  dsimp only
  let Q := rowRule G hregular huncountable hNorm F hF base hbase
  let prior := fun b (_hba : b < a) ↦ Q.state hregular.aleph0_le b
  have hrow : pairEntry G hregular.aleph0_le F a prior delta gamma ⊆
      (Q.state hregular.aleph0_le a).row := by
    rw [CausalRowRule.state_row_eq]
    exact (pair_entry_subset_registrations a _ delta gamma).trans
      (Set.subset_union_right.trans Set.subset_union_left)
  exact hrow.trans ((Q.rowSystem hregular.aleph0_le).row_subset_carrier a)

theorem tripleEntry_subset_carrier (a : Ladder.Stage kappa) (delta beta gamma : Set.Iio a) :
    let Q := rowRule G hregular huncountable hNorm F hF base hbase
    tripleEntry G hregular.aleph0_le a (fun b _hba ↦ Q.state hregular.aleph0_le b)
        delta beta gamma ⊆ (Q.rowSystem hregular.aleph0_le).carrier := by
  dsimp only
  let Q := rowRule G hregular huncountable hNorm F hF base hbase
  let prior := fun b (_hba : b < a) ↦ Q.state hregular.aleph0_le b
  have hrow : tripleEntry G hregular.aleph0_le a prior delta beta gamma ⊆
      (Q.state hregular.aleph0_le a).row := by
    rw [CausalRowRule.state_row_eq]
    exact (triple_entry_subset_registrations a _ delta beta gamma).trans Set.subset_union_right
  exact hrow.trans ((Q.rowSystem hregular.aleph0_le).row_subset_carrier a)

#print axioms mk_pairEntry_le
#print axioms mk_tripleEntry_le
#print axioms priorRequest_eq_finalRequest_of_lt
#print axioms pairEntry_subset_carrier
#print axioms tripleEntry_subset_carrier

end Erdos599.CardinalInduction.UnroofedRegularRows
