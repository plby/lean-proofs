/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.RegularWeakSplitRows

/-!
# Source-9.15 registrations in the weak causal row

The enhanced weak-split row retains the original pair table unchanged.
Consequently the half-way height chosen at a final coordinate was already
registered at its causal owner.  This is the roof-capture input for the
unconditional weak candidate construction.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction
namespace RegularRows.CausalRegular

universe u

variable {V : Type u}

/-- Every final half-way height coordinate belongs to the carrier of the
enhanced weak-split row. -/
theorem heightVerticesAt_subset_weakSplitRowRule_carrier
    (G : DWeb V) {kappa : Cardinal.{u}}
    (hkappa : kappa.IsRegular) (hkappaUncountable : aleph0 < kappa)
    (hG : G.IsNormalized)
    (hlower : UniversalCardinalInductionBelow V kappa)
    (F : Set G.DPath) (hF : G.IsWarp F)
    (base : Set V) (hbase : #base ≤ kappa)
    (delta gamma : RegularCardinal.Stage kappa) :
    let Q := weakSplitRowRule G hkappa hkappaUncountable hG hlower
      F hF base hbase
    let L := G.canonicalLadderCore kappa
      (Q.preferred hkappa.aleph0_le)
    SliceCandidate.heightVerticesAt hlower hkappaUncountable L
        (finalRequest G Q hkappa.aleph0_le) delta gamma ⊆
      (Q.rowSystem hkappa.aleph0_le).carrier := by
  dsimp only
  let Q := weakSplitRowRule G hkappa hkappaUncountable hG hlower
    F hF base hbase
  let owner := ownerStage hkappa.aleph0_le delta gamma
  have hdelta : delta < owner :=
    left_lt_ownerStage hkappa.aleph0_le delta gamma
  have hgamma : gamma < owner :=
    right_lt_ownerStage hkappa.aleph0_le delta gamma
  let prior := fun c (_hca : c < owner) ↦ Q.state hkappa.aleph0_le c
  let Lprior := priorLadder G owner prior
  let Lfinal := G.canonicalLadderCore kappa
    (Q.preferred hkappa.aleph0_le)
  have hpref : ∀ b, b < delta →
      preferredOfPrior owner prior b =
        Q.preferred hkappa.aleph0_le b := by
    intro b hb
    simp only [preferredOfPrior, prior, dif_pos (hb.trans hdelta),
      CausalRowRule.preferred]
  have hwarp : Lprior.warpAt delta = Lfinal.warpAt delta :=
    LadderPrefix.canonicalLadderCore_warpAt_eq_of_forall_lt
      G _ _ delta hpref
  have hrequest : priorRequest G hkappa.aleph0_le owner prior delta gamma =
      finalRequest G Q hkappa.aleph0_le delta gamma :=
    RegularExtension.priorRequest_eq_finalRequest_of_lt
      (G := G) Q hkappa.aleph0_le hdelta hgamma
  have hcoordinate := SliceCandidate.heightVerticesAt_congr_stageData
    hlower hkappaUncountable Lprior Lfinal
      (priorRequest G hkappa.aleph0_le owner prior)
      (finalRequest G Q hkappa.aleph0_le) delta gamma hwarp hrequest
  have hentry := pairEntry_subset_weakSplitRowRule_carrier G hkappa
    hkappaUncountable hG hlower F hF base hbase owner
      (⟨delta, hdelta⟩ : Set.Iio owner)
      (⟨gamma, hgamma⟩ : Set.Iio owner)
  intro x hx
  apply hentry
  apply Set.mem_union_right
  change x ∈ SliceCandidate.heightVerticesAt hlower hkappaUncountable
    Lprior (priorRequest G hkappa.aleph0_le owner prior) delta gamma
  rw [hcoordinate]
  exact hx

/-- The completed-ladder half-way registration, including the carrier of
the selected request components, was already inserted at its causal owner. -/
theorem halfwayRegistrationAt_subset_weakSplitRowRule_carrier
    (G : DWeb V) {kappa : Cardinal.{u}}
    (hkappa : kappa.IsRegular) (hkappaUncountable : aleph0 < kappa)
    (hG : G.IsNormalized)
    (hlower : UniversalCardinalInductionBelow V kappa)
    (F : Set G.DPath) (hF : G.IsWarp F)
    (base : Set V) (hbase : #base ≤ kappa)
    (delta gamma : RegularCardinal.Stage kappa) :
    let Q := weakSplitRowRule G hkappa hkappaUncountable hG hlower
      F hF base hbase
    let L := G.canonicalLadderCore kappa
      (Q.preferred hkappa.aleph0_le)
    RegularWeakHalfwayRegistration.registrationAt hlower
        hkappaUncountable L (finalRequest G Q hkappa.aleph0_le)
        delta gamma ⊆
      (Q.rowSystem hkappa.aleph0_le).carrier := by
  dsimp only
  let Q := weakSplitRowRule G hkappa hkappaUncountable hG hlower
    F hF base hbase
  let owner := ownerStage hkappa.aleph0_le delta gamma
  have hdelta : delta < owner :=
    left_lt_ownerStage hkappa.aleph0_le delta gamma
  have hgamma : gamma < owner :=
    right_lt_ownerStage hkappa.aleph0_le delta gamma
  let prior := fun c (_hca : c < owner) ↦ Q.state hkappa.aleph0_le c
  let Lprior := priorLadder G owner prior
  let Lfinal := G.canonicalLadderCore kappa
    (Q.preferred hkappa.aleph0_le)
  have hpref : ∀ b, b < delta →
      preferredOfPrior owner prior b =
        Q.preferred hkappa.aleph0_le b := by
    intro b hb
    simp only [preferredOfPrior, prior, dif_pos (hb.trans hdelta),
      CausalRowRule.preferred]
  have hwarp : Lprior.warpAt delta = Lfinal.warpAt delta :=
    LadderPrefix.canonicalLadderCore_warpAt_eq_of_forall_lt
      G _ _ delta hpref
  have hrequest : priorRequest G hkappa.aleph0_le owner prior delta gamma =
      finalRequest G Q hkappa.aleph0_le delta gamma :=
    RegularExtension.priorRequest_eq_finalRequest_of_lt
      (G := G) Q hkappa.aleph0_le hdelta hgamma
  have hcoordinate :=
    RegularWeakHalfwayRegistration.registrationAt_congr_stageData
      hlower hkappaUncountable hwarp hrequest
  have hentry := registrationAt_subset_weakSplitRowRule_carrier G hkappa
    hkappaUncountable hG hlower F hF base hbase owner
      (⟨delta, hdelta⟩ : Set.Iio owner)
      (⟨gamma, hgamma⟩ : Set.Iio owner)
  intro x hx
  apply hentry
  change x ∈ RegularWeakHalfwayRegistration.registrationAt hlower
    hkappaUncountable Lprior
    (priorRequest G hkappa.aleph0_le owner prior) delta gamma
  rw [hcoordinate]
  exact hx

/-- At an eligible completed coordinate, recover one half-way payload and
simultaneously capture both its height witness and selected carrier in the
weak causal row. -/
theorem exists_halfwayPayload_registration_subset_carrier
    (G : DWeb V) {kappa : Cardinal.{u}}
    (hkappa : kappa.IsRegular) (hkappaUncountable : aleph0 < kappa)
    (hG : G.IsNormalized)
    (hlower : UniversalCardinalInductionBelow V kappa)
    (F : Set G.DPath) (hF : G.IsWarp F)
    (base : Set V) (hbase : #base ≤ kappa)
    (delta gamma : RegularCardinal.Stage kappa) :
    let Q := weakSplitRowRule G hkappa hkappaUncountable hG hlower
      F hF base hbase
    let L := G.canonicalLadderCore kappa
      (Q.preferred hkappa.aleph0_le)
    SliceCandidate.HalfwayChoiceEligible L delta
        (finalRequest G Q hkappa.aleph0_le delta gamma) →
      ∃ D : SliceCandidate.HalfwayPayload L delta
          (finalRequest G Q hkappa.aleph0_le delta gamma),
        D.X ∪ (L.stageWeb delta).vertexSet
            (SliceSpliceSource.initialRestriction (L.stageWeb delta) D.W
              (finalRequest G Q hkappa.aleph0_le delta gamma)) ⊆
          (Q.rowSystem hkappa.aleph0_le).carrier := by
  dsimp only
  let Q := weakSplitRowRule G hkappa hkappaUncountable hG hlower
    F hF base hbase
  let L := G.canonicalLadderCore kappa
    (Q.preferred hkappa.aleph0_le)
  intro heligible
  obtain ⟨D, hregistration⟩ :=
    RegularWeakHalfwayRegistration.exists_halfwayPayload_with_registration
      hlower hkappaUncountable L (finalRequest G Q hkappa.aleph0_le)
      delta gamma heligible
  refine ⟨D, ?_⟩
  rw [← hregistration]
  exact halfwayRegistrationAt_subset_weakSplitRowRule_carrier G hkappa
    hkappaUncountable hG hlower F hF base hbase delta gamma

end RegularRows.CausalRegular
end CardinalInduction
end Erdos599
