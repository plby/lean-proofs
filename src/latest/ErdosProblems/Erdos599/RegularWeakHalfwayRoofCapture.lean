/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.RegularWeakHalfwayRegistration

/-!
# Roof capture for the registered half-way target carrier

The causal pair coordinate records both the half-way height witness and the
carrier of the request-rooted components of the half-way row.  Both pieces
are strictly smaller than the regular induction cardinal.  Consequently one
later member of any prescribed club roofs the entire registered coordinate.

This is the quantifier exchange needed before the later weak split coordinate
is chosen: the selected target ears are registered first and the later
frontier is selected only afterwards.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction
namespace RegularWeakHalfwayRoofCapture

universe u

variable {V : Type u}

/-- The combined height-and-requested-component registration is strictly
smaller than the regular induction cardinal.  The weaker `≤` estimate used
by the row cardinality calculation loses information needed for club roof
capture; this theorem retains the source strict bound. -/
theorem mk_registrationAt_lt
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    (hregular : kappa.IsRegular)
    (hlower : UniversalCardinalInductionBelow V kappa)
    (huncountable : aleph0 < kappa)
    (L : Gamma.KappaLadder kappa)
    (request : Ladder.Stage kappa → Ladder.Stage kappa → Set V)
    (delta gamma : Ladder.Stage kappa) :
    #(RegularWeakHalfwayRegistration.registrationAt
        hlower huncountable L request delta gamma) < kappa := by
  by_cases heligible : SliceCandidate.HalfwayChoiceEligible L delta
      (request delta gamma)
  · obtain ⟨D, hregistration⟩ :=
      RegularWeakHalfwayRegistration.exists_halfwayPayload_with_registration
        hlower huncountable L request delta gamma heligible
    rw [hregistration]
    exact RegularCardinal.mk_union_lt hregular D.heightSmall
      (RegularWeakHalfwayRegistration.mk_selectedCarrier_lt
        huncountable D heligible.request_subset heligible.request_small)
  · have hpreferredEmpty : ¬
        (RegularWeakHalfwayRegistration.preferredHalfwayRegistrationSets
          L delta (request delta gamma)).Nonempty := by
      rintro ⟨Z, hZ⟩
      exact heligible hZ.1.1
    simp only [RegularWeakHalfwayRegistration.registrationAt,
      SliceCandidate.chooseVertexSet, dif_neg hpreferredEmpty,
      Cardinal.mk_emptyCollection]
    exact Cardinal.aleph0_pos.trans huncountable

/-- If the causal carrier is contained in the ladder limit roof, the whole
pre-registered half-way coordinate is roofed by one strictly later member of
any prescribed club. -/
theorem exists_later_club_roof_superset_registrationAt
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    (hregular : kappa.IsRegular)
    (hlower : UniversalCardinalInductionBelow V kappa)
    {L : Gamma.KappaLadder kappa} (hL : L.IsSplitLegal)
    {Sigma : Set (Ladder.Stage kappa)}
    (hSigma : Stationary.IsClubBelow kappa Sigma)
    (request : Ladder.Stage kappa → Ladder.Stage kappa → Set V)
    {Z : Set V} (hZroof : Z ⊆ L.limitRoof)
    (delta gamma : Ladder.Stage kappa)
    (hregistered :
      RegularWeakHalfwayRegistration.registrationAt
        hlower hL.uncountable L request delta gamma ⊆ Z) :
    ∃ beta ∈ Sigma, delta < beta ∧
      RegularWeakHalfwayRegistration.registrationAt
          hlower hL.uncountable L request delta gamma ⊆
        Gamma.roof (L.frontier beta) := by
  let S := RegularWeakHalfwayRegistration.registrationAt
    hlower hL.uncountable L request delta gamma
  have hgeometry : SliceSpliceConstructor.SpliceLadderGeometry Gamma L :=
    ⟨hL.regular, hL.initialStage, hL.limitStages, hL.warpStages,
      hL.frontiersEssential, hL.frontierChronology,
      hL.strictFrontierChronology⟩
  have hroofed : SliceSpliceConstructor.IsEventuallyRoofed Gamma L Z :=
    SliceSpliceConstructor.isEventuallyRoofed_of_subset_limitRoof
      hgeometry hZroof
  obtain ⟨a, ha, hSa⟩ :=
    SliceSpliceConstructor.exists_club_roof_superset hregular hSigma
      hroofed hregistered
        (mk_registrationAt_lt hregular hlower hL.uncountable
          L request delta gamma)
  let beta := RegularCardinal.aboveInClub hregular Sigma hSigma delta a
  have hbeta : beta ∈ Sigma :=
    RegularCardinal.aboveInClub_mem hregular Sigma hSigma delta a
  have hdeltaBeta : delta < beta :=
    RegularCardinal.left_lt_aboveInClub hregular Sigma hSigma delta a
  have haBeta : a < beta :=
    RegularCardinal.right_lt_aboveInClub hregular Sigma hSigma delta a
  exact ⟨beta, hbeta, hdeltaBeta,
    hSa.trans (Gamma.roof_cut (hL.frontierChronology haBeta))⟩

end RegularWeakHalfwayRoofCapture
end CardinalInduction
end Erdos599
