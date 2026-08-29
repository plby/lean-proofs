/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingAssertion818Seed
import ErdosProblems.Erdos599.GroundingLastContactResolution

/-!
# The finite decoder in Assertion 8.18

An arbitrary source--`terminalCut` path is first shortened at its first
terminal-cut vertex.  This gives exactly the terminal-pure path whose
support lies in `roofRegion`.  The terminal construction supplies the first
escape-suffix state, and the last-contact theorem supplies a state at a
strictly smaller position from every state.  The already formalized finite
minimal-position argument therefore produces the forbidden auxiliary
source--target path.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace GroundingAssertion818Decoder

open DirectedPath

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

abbrev Aux (L : Gamma.KappaLadder kappa) (hlegal : L.IsLegal) :=
  L.popularAuxiliaryInput hlegal

abbrev LV (L : Gamma.KappaLadder kappa) (_hlegal : L.IsLegal) :=
  PopularAuxiliary.Input.LambdaVertex V L.groundedInfiniteRecords

/-- The essential terminal frontier of the limiting ladder separates the
original source from the original target. -/
theorem terminalCut_isSeparator
    (L : Gamma.KappaLadder kappa) (hlegal : L.IsLegal) :
    Popular.IsSeparator Gamma (Aux L hlegal).terminalCut := by
  have hroof : Gamma.source ⊆ Gamma.roof
      (Gamma.terminalFrontier (Aux L hlegal).ladder.paths) := by
    simpa only [Aux, DWeb.KappaLadder.popularAuxiliaryInput,
      DWeb.KappaLadder.limitWarp] using
        hlegal.roofsSourceAtStages (Ladder.finalStage kappa)
  have hroofEssential :
      Gamma.source ⊆ Gamma.roof (Aux L hlegal).terminalCut := by
    intro x hx
    rw [PopularAuxiliary.Input.terminalCut,
      PopularAuxiliary.Input.essentialLadder,
      Gamma.terminalFrontier_essentialWarpPart, Gamma.roof_essential]
    exact hroof hx
  intro p hpSource hpTarget
  exact hroofEssential hpSource p ⟨rfl, hpTarget⟩

/-- First-hit truncation preserves avoidance of the original grounding
cut. -/
theorem firstHit_avoids
    (L : Gamma.KappaLadder kappa) (hlegal : L.IsLegal)
    (C : Set (LV L hlegal))
    (R : FinitePath Gamma.graph)
    (havoid : Gamma.Avoids R (GroundingCut.BB (Aux L hlegal) C))
    (hmeet : R.walk.Meets (Aux L hlegal).terminalCut) :
    Gamma.Avoids (R.firstHit (Aux L hlegal).terminalCut hmeet)
      (GroundingCut.BB (Aux L hlegal) C) := by
  change Disjoint
    (R.firstHit (Aux L hlegal).terminalCut hmeet).support
    (GroundingCut.BB (Aux L hlegal) C)
  rw [Set.disjoint_left]
  intro x hx hcut
  exact Set.disjoint_left.1 havoid
    (R.firstHit_support_subset (Aux L hlegal).terminalCut hmeet hx) hcut

/-- A source--frontier path whose finish is its first frontier point lies
under the frontier roof. -/
theorem support_subset_roofRegion_of_no_terminal_before
    (L : Gamma.KappaLadder kappa) (hlegal : L.IsLegal)
    (R : FinitePath Gamma.graph)
    (hsource : R.start ∈ Gamma.source)
    (hfinish : R.finish ∈ (Aux L hlegal).terminalCut)
    (hfirst : ∀ {x : V}, x ∈ R.walk.support.dropLast →
      x ∉ (Aux L hlegal).terminalCut) :
    R.support ⊆ (Aux L hlegal).roofRegion := by
  have hterminalSeparator :
      Popular.IsSeparator Gamma (Aux L hlegal).terminalCut :=
    terminalCut_isSeparator L hlegal
  have hstartRoof :
      R.start ∈ Gamma.roof (Aux L hlegal).terminalCut := by
    intro p hp
    exact hterminalSeparator p (hp.1 ▸ hsource) hp.2
  have hterminal : ∀ t,
      Gamma.terminal? (.inl R : Gamma.DPath) = some t →
        t ∈ (Aux L hlegal).terminalCut := by
    intro t ht
    have hrt : R.finish = t := Option.some.inj ht
    simpa only [hrt] using hfinish
  have hinter :
      (DirectedPath.Path.support (.inl R : Gamma.DPath) ∩
          (Aux L hlegal).terminalCut) ⊆ ({R.finish} : Set V) := by
    intro x hx
    apply Set.mem_singleton_iff.2
    by_contra hxf
    have hxlast : x ≠
        R.walk.support.getLast R.walk.support_ne_nil := by
      simpa only [R.walk.getLast_support] using hxf
    have hxdrop : x ∈ R.walk.support.dropLast :=
      List.mem_dropLast_of_mem_of_ne_getLast hx.1 hxlast
    exact hfirst hxdrop hx.2
  exact Gamma.pathSupportRoof
    (.inl R : Gamma.DPath) (Aux L hlegal).terminalCut
      hstartRoof hterminal hinter

/-- Concrete legal-ladder finite decoder.  No geometric hypothesis remains:
the first-hit path supplies the roof invariant, Assertion 8.17 classifies
each chosen contact fragment, and the blocking-point dichotomy yields the
strict finite descent. -/
theorem finiteDescentDecoder
    (L : Gamma.KappaLadder kappa) (hlegal : L.IsLegal)
    (C : Set (LV L hlegal))
    (hC : Popular.IsSeparator (Aux L hlegal).lambda C) :
    GroundingCut.FiniteDescentDecoder (Aux L hlegal) C := by
  intro R hsource hterminal havoid
  have hmeet : R.walk.Meets (Aux L hlegal).terminalCut :=
    ⟨R.finish, R.finish_mem_support, hterminal⟩
  let Q : FinitePath Gamma.graph :=
    R.firstHit (Aux L hlegal).terminalCut hmeet
  have hQsource : Q.start ∈ Gamma.source := by
    change R.start ∈ Gamma.source
    exact hsource
  have hQterminal : Q.finish ∈ (Aux L hlegal).terminalCut := by
    exact R.firstHit_finish_mem (Aux L hlegal).terminalCut hmeet
  have hQavoid :
      Gamma.Avoids Q (GroundingCut.BB (Aux L hlegal) C) := by
    exact firstHit_avoids L hlegal C R havoid hmeet
  have hQroof : Q.support ⊆ (Aux L hlegal).roofRegion := by
    apply support_subset_roofRegion_of_no_terminal_before
      L hlegal Q hQsource hQterminal
    intro x hx
    exact R.firstHit_no_mem_before
      (Aux L hlegal).terminalCut hmeet hx
  obtain ⟨seed, _hseedLast⟩ :=
    GroundingAssertion818Seed.exists_initialEscapeSuffixState
      L hlegal C Q hQterminal hQavoid
  let D : GroundingFiniteDescent.LastFragmentDescentSystem
      (Aux L hlegal) C Q :=
    { seed := seed
      resolve := fun S ↦ Or.inr
        (GroundingLastContactResolution.exists_strictlyEarlier_escapeSuffixState
          L hlegal C hC Q hQsource hQroof hQavoid S) }
  exact D.exists_avoiding_source_target_path

/-- Assertion 8.18 for the exact legal-ladder auxiliary input. -/
theorem assertion8_18
    (L : Gamma.KappaLadder kappa) (hlegal : L.IsLegal)
    (C : Set (LV L hlegal))
    (hC : Popular.IsSeparator (Aux L hlegal).lambda C) :
    Popular.IsSeparator Gamma (GroundingCut.BB (Aux L hlegal) C) :=
  GroundingCut.assertion8_18 (Aux L hlegal) C hC
    (terminalCut_isSeparator L hlegal)
    (finiteDescentDecoder L hlegal C hC)

end GroundingAssertion818Decoder
end Erdos599
