/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.LadderLemma76
import ErdosProblems.Erdos599.LadderLimitHitClosure
import ErdosProblems.Erdos599.RegularCardinal
import ErdosProblems.Erdos599.LadderRecordCardinal
import ErdosProblems.Erdos599.GroundingObstructionCharacterization

/-!
# Graph-theoretic inputs to the ladder obstruction characterization

This file proves the three local inputs called Lemmas 7.6--7.8 in the
proof of Aharoni--Berger's Lemma 7.27.  The bookkeeping is normalized so
that the choice at `a` is made from `IE(Y_(a+1))`.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace DWeb

open Ladder

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

namespace KappaLadder

/-- Successor-normalized form of source Lemma 7.7 at one stage.  A ray
which belongs to `Y_(a+1)` but to no earlier successor warp is inessential,
unrecorded, and cannot be the finite marker singleton.  It is therefore an
available obstruction at `a`. -/
theorem newRaySuccessor_mem_phi
    (L : Gamma.KappaLadder kappa) (hlegal : L.IsLegal)
    {a : Stage kappa} {p : Gamma.DPath}
    (hp : p ∈ L.successorWarp a) (hpRay : Gamma.terminal? p = none)
    (hpNew : ∀ b : Stage kappa, b < a → p ∉ L.successorWarp b) :
    a ∈ L.phi := by
  have hpIE : p ∈ Gamma.inessentialPaths (L.successorWarp a) := by
    rcases p with p | r
    · simp at hpRay
    · exact Gamma.ray_mem_inessentialPaths hp
  have hpNotRecorded : p ∉ L.bookkeeping.recordedBefore a := by
    rintro ⟨b, hba, hchosen⟩
    have hpAvailable := L.bookkeeping.chosen_mem_available
      hlegal.validBookkeeping hchosen
    exact hpNew b hba hpAvailable.1.1.1
  have hpNotMarker : p ∉ L.markerPathSet a := by
    intro hpMarker
    cases hmarker : L.marker a with
    | none => simpa [markerPathSet, hmarker] using hpMarker
    | some y =>
        have hpy : p = Gamma.trivialPath y := by
          simpa [markerPathSet, hmarker] using hpMarker
        rw [hpy, Gamma.terminal?_trivialPath] at hpRay
        cases hpRay
  exact ⟨p, ⟨⟨hpIE, hpNotRecorded⟩, hpNotMarker⟩⟩

/-- Source Lemma 7.7 with the same successor indexing as the record
choice: every genuinely new successor ray is an obstruction. -/
theorem phiNewRay_subset_phi
    (L : Gamma.KappaLadder kappa) (hlegal : L.IsLegal) :
    L.phiNewRay ⊆ L.phi := by
  rintro a ⟨p, hp, hpRay, hpNew⟩
  exact L.newRaySuccessor_mem_phi hlegal hp hpRay hpNew

/-- Lemmas 7.6 and 7.7 together: under the normalization needed by the
hindrance-rung argument, all exceptional stages are obstruction stages. -/
theorem exceptionalStages_subset_phi
    (L : Gamma.KappaLadder kappa) (hGamma : Gamma.IsNormalized)
    (hlegal : L.IsLegal) :
    L.exceptionalStages ⊆ L.phi := by
  intro a ha
  rcases ha with ha | ha
  · exact L.phiHindrance_subset_phi hGamma hlegal ha
  · exact L.phiNewRay_subset_phi hlegal ha

/-- Diagonal emergence is the exact obstruction to regressivity.  Thus,
once the finite diagonal components have been classified geometrically (the
ray case is automatic), removing the exceptional stages makes the emergence
map genuinely regressive. -/
theorem emergenceIndex_regressive_off_exceptional_of_diagonalClassified
    (L : Gamma.KappaLadder kappa) (hlegal : L.IsLegal)
    (hclassified : L.DiagonalEmergenceClassified hlegal) :
    Stationary.IsRegressiveOn
      (L.phi \ L.exceptionalStages)
      (L.emergenceIndex hlegal.validBookkeeping) := by
  intro a ha
  have hle : L.emergenceIndex hlegal.validBookkeeping a ≤ a :=
    L.emergenceIndex_le hlegal.validBookkeeping ha.1
  exact lt_of_le_of_ne hle fun heq ↦
    ha.2 (hclassified ⟨ha.1, heq⟩)

/-- The same-stage exclusion consists of at most the one marker singleton,
and hence has cardinality below an uncountable `kappa`. -/
theorem mk_markerPathSet_lt
    (L : Gamma.KappaLadder kappa) (huncountable : ℵ₀ < kappa)
    (a : Stage kappa) :
    #(L.markerPathSet a) < kappa := by
  cases hmarker : L.marker a with
  | none =>
      simp [markerPathSet, hmarker,
        (Cardinal.aleph0_pos.trans huncountable)]
  | some y =>
      simpa [markerPathSet, hmarker] using
        Cardinal.one_lt_aleph0.trans huncountable

/-- Inessential successor components persist to every later successor.
For a strict stage inequality, first regard `Y_(a+1)` as an ordinary
stage, use transfinite inessential persistence, and then take the final
successor step at `b`. -/
theorem IsLegal.inessentialSuccessor_mono
    {L : Gamma.KappaLadder kappa} (hlegal : L.IsLegal)
    {a b : Stage kappa} (hab : a ≤ b) :
    Gamma.inessentialPaths (L.successorWarp a) ⊆
      Gamma.inessentialPaths (L.successorWarp b) := by
  intro p hp
  rcases hab.lt_or_eq with hab | rfl
  · have habv : (a.1 : Ordinal.{u}) < b.1 := hab
    let c : Stage kappa :=
      ⟨(a.1 : Ordinal.{u}) + 1,
        ((Order.add_one_le_iff).2 habv).trans_lt b.2⟩
    have hc_le_b : c ≤ b := (Order.add_one_le_iff).2 habv
    have hp_c : p ∈ Gamma.inessentialPaths (L.warpAt c) := by
      change p ∈ Gamma.inessentialPaths (L.successorWarp a)
      exact hp
    exact hlegal.currentInessentialPersists b
      (hlegal.inessentialPaths_mono_stage hc_le_b hp_c)
  · exact hp

/-- Source Lemma 7.8, successor-normalized.  If one successor inessential
family has size at least `kappa`, then at every later stage fewer than
`kappa` old records together with the single excluded marker cannot exhaust
the persistent family, so a new record is available. -/
theorem largeInessentialStages_tail_subset_phi
    (L : Gamma.KappaLadder kappa) (hlegal : L.IsLegal) :
    ∀ a ∈ L.largeInessentialStages, Set.Ici a ⊆ L.phi := by
  intro a ha b hab
  have hmono : Gamma.inessentialPaths (L.successorWarp a) ⊆
      Gamma.inessentialPaths (L.successorWarp b) :=
    hlegal.inessentialSuccessor_mono hab
  by_contra hb
  have hcover : Gamma.inessentialPaths (L.successorWarp b) ⊆
      L.bookkeeping.recordedBefore b ∪ L.markerPathSet b := by
    intro p hp
    by_cases hrecorded : p ∈ L.bookkeeping.recordedBefore b
    · exact Or.inl hrecorded
    · right
      by_contra hexcluded
      apply hb
      exact ⟨p, ⟨⟨hp, hrecorded⟩, hexcluded⟩⟩
  have hsmallUnion :
      #((L.bookkeeping.recordedBefore b ∪ L.markerPathSet b) :
        Set Gamma.DPath) < kappa :=
    RegularCardinal.mk_union_lt hlegal.regular
      (L.mk_recordedBefore_lt b)
      (L.mk_markerPathSet_lt hlegal.uncountable b)
  have hsmall : #(Gamma.inessentialPaths (L.successorWarp b)) < kappa :=
    (Cardinal.mk_subtype_mono hcover).trans_lt hsmallUnion
  have hlarge : kappa ≤
      #(Gamma.inessentialPaths (L.successorWarp a)) := ha
  exact (not_lt_of_ge
    (hlarge.trans (Cardinal.mk_subtype_mono hmono))) hsmall

end KappaLadder
end DWeb
end Erdos599
