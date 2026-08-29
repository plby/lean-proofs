/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.DeferredGroundingSelectedSourceFirstVirtualEscape
import ErdosProblems.Erdos599.DirectedEndpointDuality
import ErdosProblems.Erdos599.SafeLink

/-!
# Finite residual matching behind a protected owner transaction

The strict-prefix residual left by one virtual-owner splice is finite.  A
finite family of individually chosen source paths is not enough: the paths
can meet one another, and can reuse an owner already committed to another
transaction.

Here the unconditional finite-target directed Menger theorem is applied in
the graph obtained by deleting the already protected carrier `Z`.  It gives
an actual pairwise-disjoint source--residual packing avoiding `Z`, together
with a finite orthogonal separator `C`.  Replacing the residual subset of the
source-first frontier by `Z ∪ C` remains an ambient source--target separator.

This is the precise finite residual-owner matching statement.  It assumes
neither a fixed-original occurrence Hall theorem nor simultaneous coverage.
The protected carrier remains explicit, so a later moving transaction must
decide how its rooted part is represented in the final stopping frontier.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace DWeb
namespace KappaLadder
namespace Deferred

open _root_.Erdos599.DirectedPath
open PopularGroundingBridge

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}
variable {L : Gamma.KappaLadder kappa} {hL : IsKappaHindrance L}
variable {S : Popular.PopularSeparator (popularAuxiliaryIndexed L hL)}

local notation "T₁" =>
  reservedStrongSelectedSourceFirstBB (L := L) (hL := hL) (S := S)

/-- Finite-target Menger in the complement of a protected carrier.

The packing is literal in `Gamma.delete Z`, hence its ambient lifts avoid
`Z`.  Its orthogonal set is finite because the residual target is finite.
The last field is the source-faithful separator replacement: every ambient
source--target path either meets an untouched point of `T₁`, meets the
protected carrier, or reaches the residual through the deleted graph and
therefore meets `C`. -/
theorem exists_protectedFiniteResidualMatching
    {R Z : Set V} (hR : R.Finite) (hRT : R ⊆ T₁)
    (hRZ : Disjoint R Z) :
    ∃ (P : Set (Bridge.DirectedABPath (Gamma.delete Z).graph
          (Gamma.source \ Z) R)) (C : Set V),
      Bridge.DirectedIsPathPacking P ∧
      Bridge.DirectedIsABSeparator (Gamma.delete Z).graph
        (Gamma.source \ Z) R C ∧
      Bridge.DirectedIsOrthogonal P C ∧
      P.Finite ∧ C.Finite ∧ Disjoint C Z ∧
      Popular.IsSeparator Gamma ((T₁ \ R) ∪ Z ∪ C) := by
  let H : DWeb V :=
    { graph := (Gamma.delete Z).graph
      source := Gamma.source \ Z
      target := R }
  have htarget : H.target.Countable := by
    simpa only [H] using hR.countable
  obtain ⟨P, C, hpacking, hseparator, horthogonal⟩ :=
    DirectedEndpointDuality.directedMengerConclusion_of_target_countable
      H htarget
  have hPfinite : P.Finite := by
    apply Set.Finite.of_finite_image
        (f := fun p : Bridge.DirectedABPath H.graph H.source H.target ↦
          p.path.finish)
    · apply hR.subset
      rintro x ⟨p, hp, rfl⟩
      exact p.finish_mem
    · intro p hp q hq hfinish
      by_contra hpq
      have hdisjoint := hpacking hp hq hpq
      change p.path.finish = q.path.finish at hfinish
      have hpFinishQ : p.path.finish ∈ q.supportSet := by
        rw [hfinish]
        exact q.finish_mem_supportSet
      exact Set.disjoint_left.mp hdisjoint p.finish_mem_supportSet
        hpFinishQ
  have hCfinite : C.Finite := by
    have hUnion : (⋃ p ∈ P, p.supportSet).Finite :=
      hPfinite.biUnion fun p _hp ↦ p.path.support_finite
    exact hUnion.subset horthogonal.1
  have hCZ : Disjoint C Z := by
    rw [Set.disjoint_left]
    intro c hcC hcZ
    have hcUnion := horthogonal.1 hcC
    simp only [Set.mem_iUnion] at hcUnion
    obtain ⟨p, hpP, hcp⟩ := hcUnion
    have hpStart : p.path.start ∈ Gamma.source \ Z := by
      simpa only [H] using p.start_mem
    have havoid := Gamma.liftDeletePath_avoids Z
      (Sum.inl p.path : (Gamma.delete Z).DPath) hpStart.2
    change c ∈ p.path.support at hcp
    rw [Gamma.support_liftDeletePath] at havoid
    change Disjoint p.path.support Z at havoid
    exact Set.disjoint_left.mp havoid hcp hcZ
  have hreplacement :
      Popular.IsSeparator Gamma ((T₁ \ R) ∪ Z ∪ C) := by
    intro q hqSource hqTarget
    obtain ⟨x, hxq, hxT⟩ :=
      reservedStrongSelectedSourceFirstBB_isSeparator
        (L := L) (hL := hL) (S := S) q hqSource hqTarget
    by_cases hxR : x ∈ R
    · by_cases hqZ : (q.support ∩ Z).Nonempty
      · obtain ⟨z, hzq, hzZ⟩ := hqZ
        exact ⟨z, ⟨hzq, Or.inl (Or.inr hzZ)⟩⟩
      · have hqAvoid : ∀ {z : V}, z ∈ q.support → z ∉ Z := by
          intro z hzq hzZ
          exact hqZ ⟨z, hzq, hzZ⟩
        have hqMeetR : q.walk.Meets R := ⟨x, hxq, hxR⟩
        let pref : FinitePath Gamma.graph := q.firstHit R hqMeetR
        have hprefAvoid : SafeLink.Walk.Avoids pref.walk Z := by
          intro z hz
          exact hqAvoid (q.firstHit_support_subset R hqMeetR hz)
        let deleted : FinitePath (Gamma.delete Z).graph :=
          SafeLink.FinitePath.toDelete Gamma Z pref hprefAvoid
        let aToR : Bridge.DirectedABPath (Gamma.delete Z).graph
            (Gamma.source \ Z) R :=
          { path := deleted
            start_mem := by
              change pref.start ∈ Gamma.source \ Z
              exact ⟨hqSource, hqAvoid q.start_mem_support⟩
            finish_mem := by
              change pref.finish ∈ R
              exact q.firstHit_finish_mem R hqMeetR }
        obtain ⟨c, hcC, hcpref⟩ := hseparator aToR
        refine ⟨c, ⟨?_, Or.inr hcC⟩⟩
        apply q.firstHit_support_subset R hqMeetR
        change c ∈ deleted.support at hcpref
        simpa only [deleted, pref,
          SafeLink.FinitePath.support_toDelete] using hcpref
    · exact ⟨x, ⟨hxq, Or.inl (Or.inl ⟨hxT, hxR⟩)⟩⟩
  refine ⟨P, C, ?_, ?_, horthogonal, hPfinite, hCfinite, hCZ,
    hreplacement⟩
  · simpa only [H] using hpacking
  · simpa only [H] using hseparator

/-- Truncate an orthogonal deleted-web packing at its unique separator
contact and lift it back to the ambient web.  The result is an actual finite
warp whose terminal frontier is exactly the orthogonal separator.  It starts
in the retained ambient source and its whole vertex set avoids the protected
carrier. -/
theorem exists_finiteProtectedOrthogonalWarp
    {R Z C : Set V}
    {P : Set (Bridge.DirectedABPath (Gamma.delete Z).graph
      (Gamma.source \ Z) R)}
    (hpacking : Bridge.DirectedIsPathPacking P)
    (horthogonal : Bridge.DirectedIsOrthogonal P C)
    (hPfinite : P.Finite) :
    ∃ W : Set Gamma.DPath,
      Gamma.IsWarp W ∧ W.Finite ∧ Gamma.HasFiniteCharacter W ∧
      Gamma.initialSet W ⊆ Gamma.source \ Z ∧
      Gamma.terminalFrontier W = C ∧
      Disjoint (Gamma.vertexSet W) Z := by
  have hmeet (p : P) : p.1.path.walk.Meets C := by
    obtain ⟨c, hc, _hunique⟩ := horthogonal.2 p.1 p.2
    exact ⟨c, hc.2, hc.1⟩
  let cutPath (p : P) :
      FinitePath (Gamma.delete Z).graph :=
    p.1.path.firstHit C (hmeet p)
  let Wd : Set (Gamma.delete Z).DPath :=
    Set.range fun p : P ↦
      (Sum.inl (cutPath p) : (Gamma.delete Z).DPath)
  have hWdWarp : (Gamma.delete Z).IsWarp Wd := by
    rintro _ ⟨p, rfl⟩ _ ⟨q, rfl⟩ hpq
    have hpne : p.1 ≠ q.1 := by
      intro hpq'
      apply hpq
      have hpqSubtype : p = q := Subtype.ext hpq'
      exact congrArg (fun r : P ↦
        (Sum.inl (cutPath r) : (Gamma.delete Z).DPath)) hpqSubtype
    change Disjoint (cutPath p).support (cutPath q).support
    exact (hpacking p.2 q.2 hpne).mono
      (p.1.path.firstHit_support_subset C (hmeet p))
      (q.1.path.firstHit_support_subset C (hmeet q))
  have hWdFinite : Wd.Finite := by
    let _ : Fintype P := hPfinite.fintype
    have huniv : (Set.univ : Set P).Finite := Set.finite_univ
    have himage := huniv.image (fun p : P ↦
      (Sum.inl (cutPath p) : (Gamma.delete Z).DPath))
    simpa only [Set.image_univ, Wd] using himage
  have hWdSource :
      (Gamma.delete Z).initialSet Wd ⊆ Gamma.source \ Z := by
    rintro a ⟨q, ⟨p, rfl⟩, hpa⟩
    change p.1.path.start = a at hpa
    simpa only [hpa] using p.1.start_mem
  have hWdTerminal :
      (Gamma.delete Z).terminalFrontier Wd = C := by
    ext c
    constructor
    · rintro ⟨q, ⟨p, rfl⟩, hqc⟩
      change some (cutPath p).finish = some c at hqc
      have hfinish : (cutPath p).finish = c := Option.some.inj hqc
      exact hfinish ▸ p.1.path.firstHit_finish_mem C (hmeet p)
    · intro hcC
      have hcUnion := horthogonal.1 hcC
      simp only [Set.mem_iUnion] at hcUnion
      obtain ⟨p, hpP, hcp⟩ := hcUnion
      let ps : P := ⟨p, hpP⟩
      obtain ⟨v, hv, hvUnique⟩ := horthogonal.2 p hpP
      have hcutC : (cutPath ps).finish ∈ C :=
        p.path.firstHit_finish_mem C (hmeet ps)
      have hcutP : (cutPath ps).finish ∈ p.supportSet :=
        p.path.firstHit_support_subset C (hmeet ps)
          (cutPath ps).finish_mem_support
      have hcutEq : (cutPath ps).finish = c :=
        (hvUnique _ ⟨hcutC, hcutP⟩).trans
          (hvUnique _ ⟨hcC, hcp⟩).symm
      refine ⟨Sum.inl (cutPath ps), ⟨ps, rfl⟩, ?_⟩
      exact congrArg some hcutEq
  let W : Set Gamma.DPath := Gamma.liftDeleteFamily Z Wd
  refine ⟨W, hWdWarp.liftDeleteFamily, ?_, ?_, ?_, ?_, ?_⟩
  · exact hWdFinite.image (Gamma.liftDeletePath Z)
  · apply Gamma.fd_hasFiniteCharacter_liftDeleteFamily
    rintro _ ⟨p, rfl⟩
    exact ⟨cutPath p, rfl⟩
  · simpa only [W, Gamma.initialSet_liftDeleteFamily] using hWdSource
  · simpa only [W, Gamma.terminalFrontier_liftDeleteFamily] using hWdTerminal
  · apply Gamma.vertexSet_liftDeleteFamily_disjoint
    simpa only [Gamma.delete_source] using hWdSource

/-- Canonical specialization to the finite strict prefix left on the
nongrounded owner hit by a virtual transaction.  Pairwise owner non-reuse is
expressed by `Disjoint Y.support Z`: it implies that every residual target
and every selected Menger path avoids the already protected owner carrier.
-/
theorem exists_protectedVirtualStrictPrefixMatching
    (Y : Gamma.DPath) {y : V} (hyY : y ∈ Y.support)
    (Z : Set V) (hYZ : Disjoint Y.support Z) :
    let R : Set V :=
      {z | z ∈ T₁ ∧ GroundingCut.Before Y z y}
    ∃ (P : Set (Bridge.DirectedABPath (Gamma.delete Z).graph
          (Gamma.source \ Z) R)) (C : Set V),
      Bridge.DirectedIsPathPacking P ∧
      Bridge.DirectedIsABSeparator (Gamma.delete Z).graph
        (Gamma.source \ Z) R C ∧
      Bridge.DirectedIsOrthogonal P C ∧
      P.Finite ∧ C.Finite ∧ Disjoint C Z ∧
      Popular.IsSeparator Gamma ((T₁ \ R) ∪ Z ∪ C) := by
  dsimp only
  apply exists_protectedFiniteResidualMatching
  · exact
      ReservedStrongSelectedStartingLastContact.SourceSaturation.virtualOwner_strictPrefixObligations_finite
        Y hyY
  · intro z hz
    exact hz.1
  · apply hYZ.mono_left
    intro z hz
    obtain ⟨m, _n, hm, _hy, _hmn⟩ := hz.2.1
    exact GroundingCut.occursAt_mem_support hm

end Deferred
end KappaLadder
end DWeb
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.Deferred.exists_protectedFiniteResidualMatching
#print axioms
  Erdos599.DWeb.KappaLadder.Deferred.exists_finiteProtectedOrthogonalWarp
#print axioms
  Erdos599.DWeb.KappaLadder.Deferred.exists_protectedVirtualStrictPrefixMatching
