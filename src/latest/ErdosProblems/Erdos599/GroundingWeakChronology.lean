/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingIndexDichotomy

/-!
# Successor-corrected chronology for the grounding auxiliary web

The literal Section 7 bookkeeping selects a path from `IE(Y_(a+1))` at
stage `a`.  Thus the geometric form of Lemma 7.17 which is compatible with
that bookkeeping transports the endpoint of a Lambda path to the roof at
the *successor* of the source index.  This gives the weak inequality
`targetIndex <= sourceIndex`; equality is the genuine marker-created case
isolated by `GroundingIndexDichotomy`.

This file discharges the ordinal part of that correction.  It deliberately
keeps the two successor-roof transport statements as a structure: proving
them is the graph-theoretic decoder/switching step, whereas turning them
into weak chronology is formal frontier arithmetic.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace DWeb

open DirectedPath

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

namespace KappaLadder

/-- The ordinary stage immediately following `a`.  Regularity and
uncountability ensure that the successor is still below `kappa`; using an
extended stage here would be insufficient for frontier chronology. -/
def successorStage (L : Gamma.KappaLadder kappa) (hlegal : L.IsLegal)
    (a : Ladder.Stage kappa) : Ladder.Stage kappa :=
  ⟨a.1 + 1, by
    have hone : #(PUnit) < kappa := by
      simpa only [mk_punit] using
        (lt_trans Cardinal.one_lt_aleph0 hlegal.uncountable)
    have hbound := Stationary.iSup_add_one_lt_ord_of_lt
      hlegal.regular (f := fun _ : PUnit ↦ a.1) hone (fun _ ↦ a.2)
    show a.1 + 1 < kappa.ord
    exact lt_of_le_of_lt
      (Ordinal.le_iSup (fun _ : PUnit ↦ a.1 + 1) PUnit.unit) hbound⟩

@[simp]
theorem successorStage_val (L : Gamma.KappaLadder kappa)
    (hlegal : L.IsLegal) (a : Ladder.Stage kappa) :
    (L.successorStage hlegal a).1 = a.1 + 1 :=
  rfl

theorem successorStage_le_iff_lt
    (L : Gamma.KappaLadder kappa) (hlegal : L.IsLegal)
    {a b : Ladder.Stage kappa} :
    L.successorStage hlegal a ≤ b ↔ a < b := by
  change a.1 + 1 ≤ b.1 ↔ a.1 < b.1
  exact Order.add_one_le_iff

/-- The successor-corrected geometric content needed from Lemma 7.17.

For a finite record selected at `a`, its Lambda endpoint is roofed by
`T_(a+1)`.  For a recorded ray, the same statement holds for any proxy
attachment selected by the decoder. -/
structure Lemma717SuccessorRoofTransport
    (L : Gamma.KappaLadder kappa) (hlegal : L.IsLegal) : Prop where
  finite : ∀
      (q : FinitePath (L.popularAuxiliaryInput hlegal).lambda.graph)
      (hs : q.start ∈ (L.popularAuxiliaryInput hlegal).lambda.source)
      (ht : q.finish ∈ (L.popularAuxiliaryInput hlegal).lambda.target)
      (x : L.finiteTerminalSet) (y : V),
      q.start = .old x.1 → q.finish = .old y →
      y ∈ Gamma.roof
        (L.frontier
          (L.successorStage hlegal (L.finiteTerminalStage x)))
  proxy : ∀
      (q : FinitePath (L.popularAuxiliaryInput hlegal).lambda.graph)
      (hs : q.start ∈ (L.popularAuxiliaryInput hlegal).lambda.source)
      (ht : q.finish ∈ (L.popularAuxiliaryInput hlegal).lambda.target)
      (i : L.groundedInfiniteRecords) (y : V),
      q.start = .proxy i → q.finish = .old y →
      y ∈ Gamma.roof
        (L.frontier
          (L.successorStage hlegal (L.groundedInfiniteStage i)))

/-- Successor-roof transport gives the exact weak chronology of the
literal auxiliary indexing.  If a target marker had stage strictly above
the source record, its own frontier would inherit the successor-roof
membership, contradicting marker freshness. -/
theorem auxiliaryNonincreasing_of_successorRoofTransport
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (H : L.Lemma717SuccessorRoofTransport hL.legal) :
    L.AuxiliaryNonincreasing hL := by
  let I := L.popularAuxiliaryInput hL.legal
  intro q hs ht
  obtain ⟨y, hyTarget, hqy⟩ := I.finish_of_mem_lambda_target q ht
  have hyMarker : y ∈ L.markerSet := hyTarget.1
  let b : Ladder.Stage kappa := L.markerStage ⟨y, hyMarker⟩
  have hmarker : L.marker b = some y := L.markerStage_spec ⟨y, hyMarker⟩
  have hyNotRoof : y ∉ Gamma.roof (L.frontier b) :=
    L.marker_not_mem_roof_frontier hL.legal hmarker
  rcases I.start_of_mem_lambda_source q hs with
      ⟨x, hxSource, hqx⟩ | ⟨i, hqi⟩
  · let xs : L.finiteTerminalSet :=
      ⟨x, L.groundedFiniteTerminalSet_subset_finiteTerminalSet hxSource⟩
    let a : Ladder.Stage kappa := L.finiteTerminalStage xs
    have hyRoofSucc : y ∈ Gamma.roof
        (L.frontier (L.successorStage hL.legal a)) :=
      H.finite q hs ht xs y hqx hqy
    have hba : b ≤ a := by
      by_contra hnot
      have hab : a < b := lt_of_not_ge hnot
      have hsuccle : L.successorStage hL.legal a ≤ b :=
        (L.successorStage_le_iff_lt hL.legal).2 hab
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
  · let a : Ladder.Stage kappa := L.groundedInfiniteStage i
    have hyRoofSucc : y ∈ Gamma.roof
        (L.frontier (L.successorStage hL.legal a)) :=
      H.proxy q hs ht i y hqi hqy
    have hba : b ≤ a := by
      by_contra hnot
      have hab : a < b := lt_of_not_ge hnot
      have hsuccle : L.successorStage hL.legal a ≤ b :=
        (L.successorStage_le_iff_lt hL.legal).2 hab
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

end KappaLadder
end DWeb
end Erdos599
