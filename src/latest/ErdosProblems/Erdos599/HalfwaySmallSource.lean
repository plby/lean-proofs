/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayClause

/-!
# The small-source consequence of the half-way construction

This file isolates exactly what the simultaneous induction hypotheses give
when the whole source of an unhindered auxiliary web has cardinality at most
the current cardinal.  They give a full source--target linkage.  Applying the
hybrid construction from `HalfwayClause` to that linkage supplies every field
of a bounded half-way linkage except unhinderedness of the quotient by the
hybrid stop-over.

The final results also record two situations in which a genuine half-way
clause follows:

* the hybrid quotient is known to be unhindered; or
* the non-source part of the target has cardinality at most the current
  cardinal, in which case the original full linkage, with the whole target as
  stop-over, has the required altitude.

Thus the small-source shortcut does not silently assert quotient stability,
which is not a consequence of the definitions for an arbitrary full
linkage.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction

open DirectedPath

universe u

variable {V : Type u}

/-! ## A direct height bound for the target -/

/-- The non-source target vertices themselves witness the height of the
whole target.  After quotienting by `target \ source`, the quotient source is
the target, so its trivial wave has target as terminal frontier. -/
theorem target_heightAtMost_of_nonSourceTarget_mk_le
    (Gamma : DWeb V) {kappa : Cardinal.{u}}
    (hcard : #(Gamma.target \ Gamma.source) <= kappa) :
    HeightAtMost Gamma Gamma.target kappa := by
  let X : Set V := Gamma.target \ Gamma.source
  refine <| Exists.intro X <| And.intro ?_ hcard
  refine And.intro ?_ <| Exists.intro
    (Gamma.quotient X).trivialWave <| And.intro
      (Gamma.quotient X).isWave_trivialWave ?_
  · intro x hx
    exact hx.2
  · rw [(Gamma.quotient X).terminalFrontier_trivialWave,
      DWeb.quotient_source]
    have hunion : Gamma.source ∪ X =
        Gamma.source ∪ Gamma.target := by
      ext x
      by_cases hx : x ∈ Gamma.source <;> simp [X, hx]
    rw [hunion, essential_source_union_target, roof_target]
    exact Set.subset_univ Gamma.target

/-- A full linkage is already a bounded-altitude half-way linkage whenever
the non-source part of the target has size at most the desired bound. -/
theorem halfwayLinkageOfAltitude_of_fullLinkage_of_nonSourceTarget_mk_le
    {Gamma : DWeb V} {L : Set Gamma.DPath} {A0 : Set V}
    {kappa : Cardinal.{u}}
    (hL : IsLinkageBetween Gamma Gamma.source Gamma.target L)
    (hA0 : A0 ⊆ Gamma.source)
    (hcard : #(Gamma.target \ Gamma.source) <= kappa) :
    IsHalfwayLinkageOfAltitude Gamma A0 kappa L := by
  apply halfwayLinkageOfAltitude_of_stopover
      (C := Gamma.target)
  · exact
      { linkage := hL
        minimal := target_subset_isTrimmedSeparator Set.Subset.rfl
        quotient_unhindered := quotient_target_isUnhindered Gamma }
  · exact fullLinkage_linksToTarget hL hA0
  · exact target_heightAtMost_of_nonSourceTarget_mk_le Gamma hcard

/-- Linkability plus a small non-source target gives the complete half-way
clause, without any additional quotient-stability premise. -/
theorem halfwayClauseAt_of_isLinkable_of_nonSourceTarget_mk_le
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    (hlinkable : IsLinkable Gamma)
    (hcard : #(Gamma.target \ Gamma.source) <= kappa) :
    HalfwayClauseAt Gamma kappa := by
  intro A0 hA0 _hA0card
  obtain ⟨L, hL⟩ := hlinkable
  exact ⟨L,
    halfwayLinkageOfAltitude_of_fullLinkage_of_nonSourceTarget_mk_le
      hL hA0 hcard⟩

/-! ## The exact output of the small-source induction shortcut -/

/-- The lower induction hypotheses and current extension clause link every
unhindered web whose whole source has size at most the current cardinal.
For every designated source set, the hybrid family then has finite linkage,
trimmedness, target-linking, and the optimal cardinal height bound.  This is
the complete half-way certificate except for unhinderedness of the quotient
by the hybrid stop-over. -/
theorem exists_fullLinkage_with_hybrid_preHalfway_of_source_mk_le_current
    {kappa : Cardinal.{u}}
    (hlower : UniversalCardinalInductionBelow V kappa)
    (hext : UniversalExtensionClauseAt V kappa)
    (Gamma : DWeb V) (hGamma : Gamma.IsUnhindered)
    (hsource : #Gamma.source <= kappa) :
    ∃ L : Set Gamma.DPath,
      IsLinkageBetween Gamma Gamma.source Gamma.target L /\
      ∀ A0 : Set V, A0 ⊆ Gamma.source →
        IsLinkageBetween Gamma Gamma.source (Hybrid.stopover Gamma L A0)
          (Hybrid.warp Gamma L A0) /\
        IsTrimmedSeparator Gamma (Hybrid.stopover Gamma L A0) /\
        LinksToTarget Gamma (Hybrid.warp Gamma L A0) A0 /\
        HeightAtMost Gamma (Hybrid.stopover Gamma L A0) (#A0) := by
  obtain ⟨L, hL⟩ :=
    isLinkable_of_source_mk_le_current hlower hext Gamma hGamma hsource
  refine ⟨L, hL, ?_⟩
  intro A0 hA0
  exact ⟨Hybrid.warp_isLinkageBetween Gamma hL,
    Hybrid.stopover_isTrimmed Gamma hL,
    Hybrid.warp_linksToTarget Gamma hL hA0,
    Hybrid.stopover_heightAtMost Gamma hL⟩

/-- If the missing hybrid-quotient invariant is supplied for one full
linkage obtained from the small-source induction shortcut, the exact
half-way clause follows.  The existential formulation is the weakest useful
quotient-stability premise: it does not require every full linkage to work. -/
theorem halfwayClauseAt_of_source_mk_le_current_of_exists_hybridQuotient
    {kappa : Cardinal.{u}}
    (hlower : UniversalCardinalInductionBelow V kappa)
    (hext : UniversalExtensionClauseAt V kappa)
    (Gamma : DWeb V) (hGamma : Gamma.IsUnhindered)
    (hsource : #Gamma.source <= kappa)
    (hquotient : ∃ L : Set Gamma.DPath,
      IsLinkageBetween Gamma Gamma.source Gamma.target L /\
      ∀ A0 : Set V, A0 ⊆ Gamma.source → #A0 = kappa →
        (Gamma.quotient (Hybrid.stopover Gamma L A0)).IsUnhindered) :
    HalfwayClauseAt Gamma kappa := by
  intro A0 hA0 hA0card
  obtain ⟨L, hL, hquot⟩ := hquotient
  exact ⟨Hybrid.warp Gamma L A0,
    Hybrid.halfwayLinkageOfAltitude_hybrid_of_mk_le Gamma hL hA0
      (hquot A0 hA0 hA0card) hA0card.le⟩

/-- Concrete small-source corollary: if both the source and the non-source
part of the target have size at most the current cardinal, the simultaneous
induction hypotheses prove the exact half-way clause. -/
theorem halfwayClauseAt_of_source_and_nonSourceTarget_mk_le_current
    {kappa : Cardinal.{u}}
    (hlower : UniversalCardinalInductionBelow V kappa)
    (hext : UniversalExtensionClauseAt V kappa)
    (Gamma : DWeb V) (hGamma : Gamma.IsUnhindered)
    (hsource : #Gamma.source <= kappa)
    (htarget : #(Gamma.target \ Gamma.source) <= kappa) :
    HalfwayClauseAt Gamma kappa := by
  apply halfwayClauseAt_of_isLinkable_of_nonSourceTarget_mk_le
    (isLinkable_of_source_mk_le_current hlower hext Gamma hGamma hsource)
    htarget

end CardinalInduction
end Erdos599
