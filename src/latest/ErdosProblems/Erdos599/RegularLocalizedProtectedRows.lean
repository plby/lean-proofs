/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.RegularLocalizedProtectedRegistration
import ErdosProblems.Erdos599.RegularWeakSplitCandidate

/-!
# Causal rows for localized protected half-way choices

This row rule replaces the legacy half-way registration by the visible
localized protected registration.  Its pair table stores the whole
completed target carrier and a stopover-height witness before any later
roof is selected.  Its triple table retains the existing weak-candidate
target and clean-maverick registrations.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction
namespace RegularLocalizedProtectedRows

universe u

variable {V : Type u}

/-- A causal owner strictly above two visible coordinates. -/
def ownerStage {kappa : Cardinal.{u}} (hkappa : aleph0 ≤ kappa)
    (a b : RegularCardinal.Stage kappa) : RegularCardinal.Stage kappa :=
  ⟨max a.1 b.1 + 1,
    (Cardinal.isSuccLimit_ord hkappa).succ_lt (max_lt a.2 b.2)⟩

theorem left_lt_ownerStage {kappa : Cardinal.{u}}
    (hkappa : aleph0 ≤ kappa) (a b : RegularCardinal.Stage kappa) :
    a < ownerStage hkappa a b :=
  (le_max_left a.1 b.1).trans_lt (lt_add_one _)

theorem right_lt_ownerStage {kappa : Cardinal.{u}}
    (hkappa : aleph0 ≤ kappa) (a b : RegularCardinal.Stage kappa) :
    b < ownerStage hkappa a b :=
  (le_max_right a.1 b.1).trans_lt (lt_add_one _)

/-- Existing annular registration together with the repaired weak-split
registration owned by the same causal triple. -/
noncomputable def protectedTripleEntry
    (G : DWeb V) {kappa : Cardinal.{u}} (hkappa : aleph0 ≤ kappa)
    (a : RegularCardinal.Stage kappa)
    (prior : ∀ b : RegularCardinal.Stage kappa,
      b < a → RegularRows.CausalState kappa V)
    (delta beta gamma : Set.Iio a) : Set V :=
  RegularRows.CausalRegular.tripleEntry G hkappa a prior delta beta gamma ∪
    RegularWeakSplitCandidate.registeredVerticesAt G
      (RegularRows.CausalRegular.priorLadder G a prior)
      (RegularRows.CausalRegular.priorRequest G hkappa a prior)
      delta.1 beta.1 gamma.1

theorem mk_protectedTripleEntry_le
    (G : DWeb V) {kappa : Cardinal.{u}} (hregular : kappa.IsRegular)
    (a : RegularCardinal.Stage kappa)
    (prior : ∀ b : RegularCardinal.Stage kappa,
      b < a → RegularRows.CausalState kappa V)
    (delta beta gamma : Set.Iio a) :
    #(protectedTripleEntry G hregular.aleph0_le a prior
      delta beta gamma) ≤ kappa := by
  exact (Cardinal.mk_union_le _ _).trans
    (Cardinal.add_le_of_le hregular.aleph0_le
      (RegularRows.CausalRegular.mk_tripleEntry_le G hregular a prior
        delta beta gamma)
      (RegularWeakSplitCandidate.mk_registeredVerticesAt_le
        hregular.aleph0_le G
          (RegularRows.CausalRegular.priorLadder G a prior)
          (RegularRows.CausalRegular.priorRequest G hregular.aleph0_le a prior)
            delta.1 beta.1 gamma.1))

/-- The repaired source-shaped row rule.  Its assumptions contain no
half-way induction clause. -/
noncomputable def rowRule
    (G : DWeb V) {kappa : Cardinal.{u}}
    (hregular : kappa.IsRegular) (huncountable : aleph0 < kappa)
    (hNorm : G.IsNormalized) (F : Set G.DPath) (hF : G.IsWarp F)
    (base : Set V) (hbase : #base ≤ kappa) :
    RegularRows.CausalRowRule kappa V :=
  RegularRows.ofRegistrationTables hregular.aleph0_le base hbase
    (RegularLocalizedProtectedRegistration.protectedPairEntry G
      huncountable F)
    (protectedTripleEntry G hregular.aleph0_le)
    (RegularLocalizedProtectedRegistration.mk_protectedPairEntry_le G
      hregular huncountable hNorm F hF)
    (mk_protectedTripleEntry_le G hregular)

/-- A protected registration in a strict-prefix pair entry belongs to the
completed carrier of the repaired row rule. -/
theorem pairRegistration_subset_carrier
    (G : DWeb V) {kappa : Cardinal.{u}}
    (hregular : kappa.IsRegular) (huncountable : aleph0 < kappa)
    (hNorm : G.IsNormalized) (F : Set G.DPath) (hF : G.IsWarp F)
    (base : Set V) (hbase : #base ≤ kappa)
    (a : RegularCardinal.Stage kappa) (delta gamma : Set.Iio a) :
    let Q := rowRule G hregular huncountable hNorm F hF base hbase
    RegularLocalizedProtectedRegistration.registrationAt
        (RegularRows.CausalRegular.priorLadder G a
          (fun b _hba ↦ Q.state hregular.aleph0_le b))
        (RegularRows.CausalRegular.priorRequest G hregular.aleph0_le a
          (fun b _hba ↦ Q.state hregular.aleph0_le b))
        delta.1 gamma.1 ⊆
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
  intro x hx
  apply (hrow.trans
    ((Q.rowSystem hregular.aleph0_le).row_subset_carrier a))
  exact Set.mem_union_right _ hx

/-- The request computed from a strict causal prefix agrees at a visible
pair coordinate with the completed request table. -/
theorem priorRequest_eq_finalRequest_of_lt
    {G : DWeb V} {kappa : Cardinal.{u}}
    (Q : RegularRows.CausalRowRule kappa V) (hkappa : aleph0 ≤ kappa)
    {c delta gamma : Ladder.Stage kappa}
    (hdelta : delta < c) (hgamma : gamma < c) :
    RegularRows.CausalRegular.priorRequest G hkappa c
        (fun b _hbc ↦ Q.state hkappa b) delta gamma =
      RegularRows.CausalRegular.finalRequest G Q hkappa delta gamma := by
  have hfrontier :
      (RegularRows.CausalRegular.priorLadder G c
        (fun b _hbc ↦ Q.state hkappa b)).frontier delta =
      (G.canonicalLadderCore kappa
        (Q.preferred hkappa)).frontier delta := by
    apply RegularRows.LadderPrefix.canonicalLadderCore_frontier_eq_of_forall_lt
    intro b hb
    exact Q.priorPreferred_eq_preferred_of_lt hkappa (hb.trans hdelta)
  ext x
  simp only [RegularRows.CausalRegular.priorRequest,
    RegularRows.CausalRegular.finalRequest,
    ControlledSlices.diagonalRequest, Set.mem_inter_iff, hfrontier]
  constructor
  · rintro ⟨hxfrontier, theta, eta, htheta, heta, hx⟩
    refine ⟨hxfrontier, theta, eta, htheta, heta, ?_⟩
    rw [RegularRows.CausalRegular.priorEnumeration_eq_actual_of_lt
      Q hkappa (htheta.trans hgamma)] at hx
    exact hx
  · rintro ⟨hxfrontier, theta, eta, htheta, heta, hx⟩
    refine ⟨hxfrontier, theta, eta, htheta, heta, ?_⟩
    rw [RegularRows.CausalRegular.priorEnumeration_eq_actual_of_lt
      Q hkappa (htheta.trans hgamma)]
    exact hx

/-- Every completed-ladder protected pair coordinate was already inserted
at its causal owner.  This is the exact prefix-transport theorem needed
before choosing a later roof. -/
theorem registrationAt_subset_rowRule_carrier
    (G : DWeb V) {kappa : Cardinal.{u}}
    (hregular : kappa.IsRegular) (huncountable : aleph0 < kappa)
    (hNorm : G.IsNormalized) (F : Set G.DPath) (hF : G.IsWarp F)
    (base : Set V) (hbase : #base ≤ kappa)
    (delta gamma : RegularCardinal.Stage kappa) :
    let Q := rowRule G hregular huncountable hNorm F hF base hbase
    let L := G.canonicalLadderCore kappa
      (Q.preferred hregular.aleph0_le)
    RegularLocalizedProtectedRegistration.registrationAt L
        (RegularRows.CausalRegular.finalRequest G Q hregular.aleph0_le)
        delta gamma ⊆
      (Q.rowSystem hregular.aleph0_le).carrier := by
  dsimp only
  let Q := rowRule G hregular huncountable hNorm F hF base hbase
  let owner := ownerStage hregular.aleph0_le delta gamma
  have hdelta : delta < owner :=
    left_lt_ownerStage hregular.aleph0_le delta gamma
  have hgamma : gamma < owner :=
    right_lt_ownerStage hregular.aleph0_le delta gamma
  let prior := fun c (_hca : c < owner) ↦ Q.state hregular.aleph0_le c
  let Lprior := RegularRows.CausalRegular.priorLadder G owner prior
  let Lfinal := G.canonicalLadderCore kappa
    (Q.preferred hregular.aleph0_le)
  have hpref : ∀ b, b < delta →
      RegularRows.CausalRegular.preferredOfPrior owner prior b =
        Q.preferred hregular.aleph0_le b := by
    intro b hb
    simp only [RegularRows.CausalRegular.preferredOfPrior, prior,
      dif_pos (hb.trans hdelta), RegularRows.CausalRowRule.preferred]
  have hwarp : Lprior.warpAt delta = Lfinal.warpAt delta :=
    RegularRows.LadderPrefix.canonicalLadderCore_warpAt_eq_of_forall_lt
      G _ _ delta hpref
  have hrequest :
      RegularRows.CausalRegular.priorRequest G hregular.aleph0_le owner
          prior delta gamma =
        RegularRows.CausalRegular.finalRequest G Q hregular.aleph0_le
          delta gamma :=
    priorRequest_eq_finalRequest_of_lt Q hregular.aleph0_le hdelta hgamma
  have hcoordinate :=
    RegularLocalizedProtectedRegistration.registrationAt_congr_stageData
      hwarp hrequest
  have hentry := pairRegistration_subset_carrier G hregular huncountable
    hNorm F hF base hbase owner
      (⟨delta, hdelta⟩ : Set.Iio owner)
      (⟨gamma, hgamma⟩ : Set.Iio owner)
  intro x hx
  apply hentry
  change x ∈ RegularLocalizedProtectedRegistration.registrationAt
    Lprior
      (RegularRows.CausalRegular.priorRequest G hregular.aleph0_le owner
        prior) delta gamma
  rw [hcoordinate]
  exact hx

end RegularLocalizedProtectedRows
end CardinalInduction
end Erdos599
