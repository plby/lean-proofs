/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.DeferredGroundingAuxiliary
import ErdosProblems.Erdos599.DeferredRegularGeometry

/-!
# Successor chronology for the deferred grounding auxiliary

The transport fields isolate the geometric content of source Lemma 7.17.
All ordinal and stationary consequences are proved here for the deferred
source types.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace DWeb

open _root_.Erdos599.DirectedPath

namespace KappaLadder
namespace Deferred

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

/-- Successor-roof transport for finite deferred records and ray proxies. -/
structure Lemma717SuccessorRoofTransport
    (L : Gamma.KappaLadder kappa) (hlegal : IsDeferredLegal L) : Prop where
  finite : ∀
      (q : FinitePath (popularAuxiliaryInput L hlegal).lambda.graph)
      (_hs : q.start ∈ (popularAuxiliaryInput L hlegal).lambda.source)
      (_ht : q.finish ∈ (popularAuxiliaryInput L hlegal).lambda.target)
      (x : finiteTerminalSet L) (y : V),
      q.start = .old x.1 → q.finish = .old y →
      y ∈ Gamma.roof
        (L.frontier (successorStage L hlegal (finiteTerminalStage L x)))
  proxy : ∀
      (q : FinitePath (popularAuxiliaryInput L hlegal).lambda.graph)
      (_hs : q.start ∈ (popularAuxiliaryInput L hlegal).lambda.source)
      (_ht : q.finish ∈ (popularAuxiliaryInput L hlegal).lambda.target)
      (i : infiniteRecords L) (y : V),
      q.start = .proxy i → q.finish = .old y →
      y ∈ Gamma.roof
        (L.frontier (successorStage L hlegal (infiniteStage L i)))

/-- Successor-roof transport gives weakly decreasing source/target stages. -/
theorem popularAuxiliary_nonincreasing_of_successorRoofTransport
    (L : Gamma.KappaLadder kappa) (hL : IsKappaHindrance L)
    (H : Lemma717SuccessorRoofTransport L hL.legal) :
    (popularAuxiliaryIndexed L hL).Nonincreasing := by
  let I := popularAuxiliaryInput L hL.legal
  intro q hs ht
  obtain ⟨y, hyTarget, hqy⟩ := I.finish_of_mem_lambda_target q ht
  have hyMarker : y ∈ L.markerSet := hyTarget.1
  let b : Ladder.Stage kappa := L.markerStage ⟨y, hyMarker⟩
  have hmarker : L.marker b = some y := L.markerStage_spec ⟨y, hyMarker⟩
  have hyNotRoof : y ∉ Gamma.roof (L.frontier b) :=
    marker_not_mem_roof_frontier L hL.legal hmarker
  rcases I.start_of_mem_lambda_source q hs with
      ⟨x, hxSource, hqx⟩ | ⟨i, hqi⟩
  · let xs : finiteTerminalSet L := ⟨x, hxSource⟩
    let a : Ladder.Stage kappa := finiteTerminalStage L xs
    have hyRoofSucc : y ∈ Gamma.roof
        (L.frontier (successorStage L hL.legal a)) :=
      H.finite q hs ht xs y hqx hqy
    have hba : b ≤ a := by
      by_contra hnot
      have hab : a < b := lt_of_not_ge hnot
      have hsuccle : successorStage L hL.legal a ≤ b :=
        (successorStage_le_iff_lt L hL.legal).2 hab
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
  · let a : Ladder.Stage kappa := infiniteStage L i
    have hyRoofSucc : y ∈ Gamma.roof
        (L.frontier (successorStage L hL.legal a)) :=
      H.proxy q hs ht i y hqi hqy
    have hba : b ≤ a := by
      by_contra hnot
      have hab : a < b := lt_of_not_ge hnot
      have hsuccle : successorStage L hL.legal a ≤ b :=
        (successorStage_le_iff_lt L hL.legal).2 hab
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

/-- The complete strong-target/popular-separator reduction after installing
the geometric successor transport. -/
theorem groundEqual_or_separator_of_successorRoofTransport
    (L : Gamma.KappaLadder kappa) (hL : IsKappaHindrance L)
    (H : Lemma717SuccessorRoofTransport L hL.legal) :
    (∃ P : Popular.XSWarp
        (popularAuxiliaryInput L hL.legal).lambda
        (popularAuxiliaryInput L hL.legal).lambda.target,
      Stationary.IsStationaryBelow kappa
        (Popular.initialIndicesOf (popularAuxiliaryIndexed L hL)
            ((popularAuxiliaryIndexed L hL).equalSubwarp P).paths
            ((popularAuxiliaryIndexed L hL).equalSubwarp P).starts_in_source ∩
          phiGround L)) ∨
      Nonempty (Popular.PopularSeparator (popularAuxiliaryIndexed L hL)) :=
  groundEqual_or_separator L hL
    (popularAuxiliary_nonincreasing_of_successorRoofTransport L hL H)

end Deferred
end KappaLadder
end DWeb
end Erdos599
