/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SplitGroundingReduction

/-!
# Successor chronology for the split grounding auxiliary

The successor-normalized ladder may record the singleton marker born at the
same stage.  Consequently the auxiliary chronology available for the sound
split bookkeeping is non-strict: a target marker can have the same stage as
the record at the source, but it cannot have a later stage.

This file isolates the geometric input of source Lemma 7.17 from its ordinal
consequence.  The two transport fields are exactly the finite-record and
proxy cases required by the path decoder.  Once they are known, marker
freshness and frontier chronology prove `Nonincreasing` for the split
auxiliary.  In particular the remaining equality branch is explicit; no
false strict-provenance claim is used.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace DWeb

open _root_.Erdos599.DirectedPath

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

namespace KappaLadder

/-- The stage immediately following `a`, constructed from split legality. -/
def splitSuccessorStage (L : Gamma.KappaLadder kappa)
    (hlegal : L.IsSplitLegal) (a : Ladder.Stage kappa) :
    Ladder.Stage kappa :=
  ⟨a.1 + 1, by
    have hone : #(PUnit) < kappa := by
      simpa only [mk_punit] using
        (lt_trans Cardinal.one_lt_aleph0 hlegal.uncountable)
    have hbound := Stationary.iSup_add_one_lt_ord_of_lt
      hlegal.regular (f := fun _ : PUnit ↦ a.1) hone (fun _ ↦ a.2)
    exact lt_of_le_of_lt
      (Ordinal.le_iSup (fun _ : PUnit ↦ a.1 + 1) PUnit.unit) hbound⟩

@[simp]
theorem splitSuccessorStage_val (L : Gamma.KappaLadder kappa)
    (hlegal : L.IsSplitLegal) (a : Ladder.Stage kappa) :
    (L.splitSuccessorStage hlegal a).1 = a.1 + 1 :=
  rfl

theorem splitSuccessorStage_le_iff_lt
    (L : Gamma.KappaLadder kappa) (hlegal : L.IsSplitLegal)
    {a b : Ladder.Stage kappa} :
    L.splitSuccessorStage hlegal a ≤ b ↔ a < b := by
  change a.1 + 1 ≤ b.1 ↔ a.1 < b.1
  exact Order.add_one_le_iff

/-- A fresh marker is outside the roof of its stage frontier under split
legality.  This is the split counterpart of
`marker_not_mem_roof_frontier`; its proof uses no provenance field. -/
theorem splitMarker_not_mem_roof_frontier
    (L : Gamma.KappaLadder kappa) (hlegal : L.IsSplitLegal)
    {a : Ladder.Stage kappa} {y : V} (hy : L.marker a = some y) :
    y ∉ Gamma.roof (L.frontier a) := by
  have hyCandidate : y ∈ L.markerCandidates a :=
    (hlegal.freshMarkers.2 a y hy).1
  have hyNotFrontier : y ∉ L.frontier a := by
    intro hyFrontier
    exact hyCandidate.2 (Or.inl hyFrontier)
  have hyNotStrictOld :
      y ∉ Gamma.strictRoof (Gamma.terminalFrontier (L.warpAt a)) := by
    have hyQuotient : y ∈ Gamma.quotientVertexSet
        (Gamma.terminalFrontier (L.warpAt a)) := hyCandidate.1.2
    exact hyQuotient
  intro hyRoof
  have hyNotEssential : y ∉ Gamma.essential (L.frontier a) := by
    rw [hlegal.frontiersEssential a]
    exact hyNotFrontier
  have hyStrict : y ∈ Gamma.strictRoof (L.frontier a) :=
    ⟨hyRoof, hyNotEssential⟩
  apply hyNotStrictOld
  rw [L.frontier_eq_essential_terminalFrontier
    hlegal.roofsSourceAtStages a, Gamma.strictRoof_essential] at hyStrict
  exact hyStrict

/-- The successor-corrected geometric content of Lemma 7.17 for the split
auxiliary.  Infinite proxies range over every infinite obstruction record,
including the genuine same-stage branch. -/
structure SplitLemma717SuccessorRoofTransport
    (L : Gamma.KappaLadder kappa) (hlegal : L.IsSplitLegal) : Prop where
  finite : ∀
      (q : FinitePath (L.splitPopularAuxiliaryInput hlegal).lambda.graph)
      (hs : q.start ∈ (L.splitPopularAuxiliaryInput hlegal).lambda.source)
      (ht : q.finish ∈ (L.splitPopularAuxiliaryInput hlegal).lambda.target)
      (x : L.finiteTerminalSet) (y : V),
      q.start = .old x.1 → q.finish = .old y →
      y ∈ Gamma.roof
        (L.frontier
          (L.splitSuccessorStage hlegal (L.finiteTerminalStage x)))
  proxy : ∀
      (q : FinitePath (L.splitPopularAuxiliaryInput hlegal).lambda.graph)
      (hs : q.start ∈ (L.splitPopularAuxiliaryInput hlegal).lambda.source)
      (ht : q.finish ∈ (L.splitPopularAuxiliaryInput hlegal).lambda.target)
      (i : L.splitInfiniteRecords) (y : V),
      q.start = .proxy i → q.finish = .old y →
      y ∈ Gamma.roof
        (L.frontier
          (L.splitSuccessorStage hlegal (L.splitInfiniteStage i)))

/-- Successor-roof transport implies nonincreasing chronology for the sound
split auxiliary.  Equality is deliberately retained. -/
theorem splitPopularAuxiliary_nonincreasing_of_successorRoofTransport
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance)
    (H : L.SplitLemma717SuccessorRoofTransport hL.legal) :
    (L.splitPopularAuxiliaryIndexed hL).Nonincreasing := by
  let I := L.splitPopularAuxiliaryInput hL.legal
  intro q hs ht
  obtain ⟨y, hyTarget, hqy⟩ := I.finish_of_mem_lambda_target q ht
  have hyMarker : y ∈ L.markerSet := hyTarget.1
  let b : Ladder.Stage kappa := L.markerStage ⟨y, hyMarker⟩
  have hmarker : L.marker b = some y := L.markerStage_spec ⟨y, hyMarker⟩
  have hyNotRoof : y ∉ Gamma.roof (L.frontier b) :=
    L.splitMarker_not_mem_roof_frontier hL.legal hmarker
  rcases I.start_of_mem_lambda_source q hs with
      ⟨x, hxSource, hqx⟩ | ⟨i, hqi⟩
  · let xs : L.finiteTerminalSet := ⟨x, hxSource⟩
    let a : Ladder.Stage kappa := L.finiteTerminalStage xs
    have hyRoofSucc : y ∈ Gamma.roof
        (L.frontier (L.splitSuccessorStage hL.legal a)) :=
      H.finite q hs ht xs y hqx hqy
    have hba : b ≤ a := by
      by_contra hnot
      have hab : a < b := lt_of_not_ge hnot
      have hsuccle : L.splitSuccessorStage hL.legal a ≤ b :=
        (L.splitSuccessorStage_le_iff_lt hL.legal).2 hab
      apply hyNotRoof
      rcases hsuccle.lt_or_eq with hlt | heq
      · exact Gamma.roof_cut (hL.legal.frontierChronology hlt) hyRoofSucc
      · rwa [heq] at hyRoofSucc
    have htargetSubtype :
        (⟨q.finish, ht⟩ : I.lambda.target) =
          ⟨.old y, (I.mem_lambda_target_old y).2 hyTarget⟩ :=
      Subtype.ext hqy
    have hsourceSubtype :
        (⟨q.start, hs⟩ : I.lambda.source) =
          ⟨.old x, (I.mem_lambda_source_old x).2 hxSource⟩ :=
      Subtype.ext hqx
    rw [htargetSubtype, hsourceSubtype]
    exact hba
  · let a : Ladder.Stage kappa := L.splitInfiniteStage i
    have hyRoofSucc : y ∈ Gamma.roof
        (L.frontier (L.splitSuccessorStage hL.legal a)) :=
      H.proxy q hs ht i y hqi hqy
    have hba : b ≤ a := by
      by_contra hnot
      have hab : a < b := lt_of_not_ge hnot
      have hsuccle : L.splitSuccessorStage hL.legal a ≤ b :=
        (L.splitSuccessorStage_le_iff_lt hL.legal).2 hab
      apply hyNotRoof
      rcases hsuccle.lt_or_eq with hlt | heq
      · exact Gamma.roof_cut (hL.legal.frontierChronology hlt) hyRoofSucc
      · rwa [heq] at hyRoofSucc
    have htargetSubtype :
        (⟨q.finish, ht⟩ : I.lambda.target) =
          ⟨.old y, (I.mem_lambda_target_old y).2 hyTarget⟩ :=
      Subtype.ext hqy
    have hsourceSubtype :
        (⟨q.start, hs⟩ : I.lambda.source) =
          ⟨.proxy i, I.mem_lambda_source_proxy i⟩ :=
      Subtype.ext hqi
    rw [htargetSubtype, hsourceSubtype]
    exact hba

/-- The split auxiliary therefore has the exact strict/equal/separator
trichotomy once the geometric successor transport is installed. -/
theorem splitPopularAuxiliary_strict_or_equal_or_separator_of_transport
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance)
    (H : L.SplitLemma717SuccessorRoofTransport hL.legal) :
    (∃ P : Popular.XSWarp
        (L.splitPopularAuxiliaryInput hL.legal).lambda
        (L.splitPopularAuxiliaryInput hL.legal).lambda.target,
      Stationary.IsStationaryBelow kappa
        (Popular.initialIndicesOf (L.splitPopularAuxiliaryIndexed hL)
          ((L.splitPopularAuxiliaryIndexed hL).strictSubwarp P).paths
          ((L.splitPopularAuxiliaryIndexed hL).strictSubwarp P).starts_in_source)) ∨
      (∃ P : Popular.XSWarp
          (L.splitPopularAuxiliaryInput hL.legal).lambda
          (L.splitPopularAuxiliaryInput hL.legal).lambda.target,
        Stationary.IsStationaryBelow kappa
          (Popular.initialIndicesOf (L.splitPopularAuxiliaryIndexed hL)
            ((L.splitPopularAuxiliaryIndexed hL).equalSubwarp P).paths
            ((L.splitPopularAuxiliaryIndexed hL).equalSubwarp P).starts_in_source)) ∨
        Nonempty
          (Popular.PopularSeparator (L.splitPopularAuxiliaryIndexed hL)) :=
  L.splitPopularAuxiliary_strict_or_equal_or_separator hL
    (L.splitPopularAuxiliary_nonincreasing_of_successorRoofTransport hL H)

/-- After the equal-target same-stage elimination, the same geometric
transport has only the two grounded stationary outputs or a popular
separator.  This is the closest chronology-level input to the final
grounding switch. -/
theorem splitPopularAuxiliary_prior_or_fresh_or_separator_of_transport
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance)
    (H : L.SplitLemma717SuccessorRoofTransport hL.legal) :
    Stationary.IsStationaryBelow kappa
        L.priorInessentialGroundStages ∨
      Stationary.IsStationaryBelow kappa
          L.freshInessentialGroundStages ∨
        Nonempty
          (Popular.PopularSeparator (L.splitPopularAuxiliaryIndexed hL)) :=
  L.splitPopularAuxiliary_prior_or_fresh_or_separator hL
    (L.splitPopularAuxiliary_nonincreasing_of_successorRoofTransport hL H)

end KappaLadder
end DWeb
end Erdos599
