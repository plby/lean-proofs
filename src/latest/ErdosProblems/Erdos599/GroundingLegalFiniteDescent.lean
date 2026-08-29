/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingFiniteDescent
import ErdosProblems.Erdos599.GroundingEscapeSuffix
import ErdosProblems.Erdos599.GroundingLegalSourceEncoding
import ErdosProblems.Erdos599.GroundingTerminalFragment

/-!
# The legal-ladder interface for finite grounding descent

For the Section 8 input coming from a legal ladder, original sources really
are covered by paths of the limiting ladder warp.  This removes the defect
exhibited by an arbitrary `PopularAuxiliary.Input` with an empty auxiliary
source.

Source coverage by itself does not compile an auxiliary route.  The two
remaining source-geometric operations are stated separately below.  A
`TerminalEscapeGeometry` supplies the paper's initial suffix, running from
the terminal contact backwards through its surviving fragment and then
along an escape to the auxiliary target.  A `LastFragmentResolution`
performs the local step: it either splices a source prefix to the suffix, or
returns a new suffix at the last earlier contact.  The finite
minimal-position argument is then unconditional.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace GroundingLegalFiniteDescent

open DirectedPath

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

abbrev Aux (L : Gamma.KappaLadder kappa) (hlegal : L.IsLegal) :=
  L.popularAuxiliaryInput hlegal

abbrev LV (L : Gamma.KappaLadder kappa) (_hlegal : L.IsLegal) :=
  PopularAuxiliary.Input.LambdaVertex V L.groundedInfiniteRecords

/-! ## What legality supplies unconditionally -/

/-- Every original source is the initial vertex of a grounded parent in the
limiting ladder warp used by the concrete auxiliary input. -/
theorem source_has_grounded_ladder_parent
    (L : Gamma.KappaLadder kappa) (hlegal : L.IsLegal)
    {x : V} (hx : x ∈ Gamma.source) :
    ∃ p ∈ (Aux L hlegal).ladder.paths,
      p.initial = x ∧ p.initial ∈ Gamma.source := by
  have hxInitial : x ∈ Gamma.initialSet L.limitWarp :=
    hlegal.source_subset_initialSet_limitWarp hx
  obtain ⟨p, hp, hpx⟩ := hxInitial
  refine ⟨p, ?_, hpx, hpx ▸ hx⟩
  exact hp

/-- The terminal contact of an original path belongs to a maximal surviving
fragment of an essential limiting-ladder parent. -/
theorem terminal_contact_has_fragment
    (L : Gamma.KappaLadder kappa) (hlegal : L.IsLegal)
    (C : Set (LV L hlegal)) {R : FinitePath Gamma.graph}
    (hterminal : R.finish ∈ (Aux L hlegal).terminalCut) :
    ∃ P : (Aux L hlegal).Fragment,
      P ∈ GroundingCut.fragments (Aux L hlegal) C ∧
        R.finish ∈ P.path.support ∧
          P.parent ∈ (Aux L hlegal).essentialLadder :=
  GroundingFiniteDescent.terminalCut_has_fragment
    (Aux L hlegal) C hterminal

/-- The maximal terminal fragment is genuinely oriented toward the terminal
of its finite essential parent. -/
theorem terminal_contact_has_fragment_with_terminal
    (L : Gamma.KappaLadder kappa) (hlegal : L.IsLegal)
    (C : Set (LV L hlegal)) {t : V}
    (ht : t ∈ (Aux L hlegal).terminalCut) :
    ∃ P : (Aux L hlegal).Fragment,
      P ∈ GroundingCut.fragments (Aux L hlegal) C ∧
        t ∈ P.path.support ∧ P.path.terminal? = some t ∧
          P.parent ∈ (Aux L hlegal).essentialLadder := by
  obtain ⟨p, hpEssential, hpt⟩ := ht
  cases p with
  | inl p =>
      have hpLadder :
          (Sum.inl p : Gamma.DPath) ∈ (Aux L hlegal).ladder.paths :=
        hpEssential.1
      have htSupport : t ∈ p.support := by
        simpa only [DirectedPath.Path.support] using
          Gamma.terminal_mem_support hpt
      obtain ⟨P, hparent, hfragment, htP⟩ :=
        GroundingFragmentPartition.exists_fragment_containing
          (Aux L hlegal) C hpLadder htSupport
      have hterminal : P.path.terminal? = some t := by
        have hparent' : P.parent = (Sum.inl p : Gamma.DPath) := hparent
        have hpFinish : p.finish = t := Option.some.inj hpt
        have hpFinishP : p.finish ∈ P.path.support := by
          simpa only [hpFinish] using htP
        have hterminalParent :=
          (GroundingTerminalFragment.finite_and_terminal_eq_parent_finish
            (Aux L hlegal) C p P hfragment hparent' hpFinishP).2
        simpa only [hpFinish] using hterminalParent
      exact ⟨P, hfragment, htP, hterminal,
        by simpa only [hparent] using hpEssential⟩
  | inr r =>
      change (none : Option V) = some t at hpt
      cases hpt

/-! ## The exact two local source-geometric inputs -/

/-- The exact terminal-fragment classification needed for the source's
initial suffix.  It strengthens the current coarse `G0` classification at
the essential terminal cut: the maximal terminal fragment must genuinely
meet the escape region, not merely be finite. -/
def TerminalFragmentsEscape
    (L : Gamma.KappaLadder kappa) (hlegal : L.IsLegal)
    (C : Set (LV L hlegal)) : Prop :=
  ∀ {t : V}, t ∈ (Aux L hlegal).terminalCut →
    ∃ P : (Aux L hlegal).Fragment,
      P ∈ GroundingCut.fragments (Aux L hlegal) C ∧
        P ∈ GroundingCut.G0 (Aux L hlegal) C ∧
          t ∈ P.path.support ∧ P.path.terminal? = some t ∧
          PopularAuxiliary.Input.Fragment.MeetsEscape
            (Aux L hlegal) C P

/-- The source-faithful terminal state of Assertion 8.18: a cut-avoiding
suffix from the last vertex of the original path to the auxiliary target,
obtained by reversing its terminal fragment to the blocking point and then
following a witnessing escape. -/
def TerminalEscapeGeometry
    (L : Gamma.KappaLadder kappa) (hlegal : L.IsLegal)
    (C : Set (LV L hlegal)) : Prop :=
  ∀ R : FinitePath Gamma.graph,
    R.start ∈ Gamma.source →
      R.finish ∈ (Aux L hlegal).terminalCut →
        Gamma.Avoids R (GroundingCut.BB (Aux L hlegal) C) →
          ∃ S : GroundingFiniteDescent.EscapeSuffixState
              (Aux L hlegal) C R,
            ¬ S.position.1 + 1 < R.walk.support.length

/-- A genuinely escaping terminal fragment supplies the source-faithful
terminal suffix by the concrete reverse-gadget decoder and loop-erased
append construction. -/
theorem terminalEscapeGeometry_of_terminalFragmentsEscape
    (L : Gamma.KappaLadder kappa) (hlegal : L.IsLegal)
    (C : Set (LV L hlegal))
    (Hterminal : TerminalFragmentsEscape L hlegal C) :
    TerminalEscapeGeometry L hlegal C := by
  intro R _ hterminal havoid
  obtain ⟨P, hPfragment, hPG0, hfinishP, hPterminal, hPescape⟩ :=
    Hterminal hterminal
  have hfinishNotBB :
      R.finish ∉ GroundingCut.BB (Aux L hlegal) C := by
    intro hfinishBB
    exact Set.disjoint_left.1 havoid R.finish_mem_support hfinishBB
  obtain ⟨q, hqstart, hqtarget, hqavoid⟩ :=
    GroundingEscapeSuffix.exists_avoiding_terminal_escape_of_not_mem_BB
      (Aux L hlegal) C P ⟨hPfragment, hPG0⟩ hPterminal
        hPescape hfinishNotBB
  let n := R.walk.support.length - 1
  have hn : n < R.walk.support.length := by
    have hpos := R.support_length_pos
    dsimp only [n]
    omega
  let i : Fin R.walk.support.length := ⟨n, hn⟩
  have hilast : ¬ n + 1 < R.walk.support.length := by
    dsimp only [n]
    omega
  have hiFinish : R.walk.support[i] = R.finish :=
    Alternating.RelationComponents.getElem_last_support_eq_finish
      R n hn hilast
  refine ⟨{
    position := i
    fragment := P
    fragment_mem := hPG0
    fragment_escape := hPescape
    contact_mem := by simpa only [hiFinish] using hfinishP
    suffix := q
    suffix_start := hqstart.trans
      (congrArg PopularAuxiliary.Input.LambdaVertex.old hiFinish.symm)
    suffix_target := hqtarget
    suffix_avoids := hqavoid }, ?_⟩
  exact hilast

/-- The literal last-`G`-fragment operation from Assertion 8.18.  At a
compiled contact, the backwards-fragment/escape splice either succeeds, or
its last self-contact supplies another state at a smaller position of `R`.
-/
def LastFragmentResolution
    (L : Gamma.KappaLadder kappa) (hlegal : L.IsLegal)
    (C : Set (LV L hlegal)) : Prop :=
  ∀ R : FinitePath Gamma.graph,
    R.start ∈ Gamma.source →
      R.finish ∈ (Aux L hlegal).terminalCut →
        Gamma.Avoids R (GroundingCut.BB (Aux L hlegal) C) →
          ∀ S : GroundingFiniteDescent.EscapeSuffixState
              (Aux L hlegal) C R,
            S.HasSourcePrefix ∨
              ∃ T : GroundingFiniteDescent.EscapeSuffixState
                  (Aux L hlegal) C R,
                T.position.1 < S.position.1

/-- The terminal escape geometry gives the initial state of the finite
last-fragment iteration. -/
theorem exists_seed_of_terminalEscapeGeometry
    (L : Gamma.KappaLadder kappa) (hlegal : L.IsLegal)
    (C : Set (LV L hlegal))
    (Hseed : TerminalEscapeGeometry L hlegal C)
    (R : FinitePath Gamma.graph)
    (hsource : R.start ∈ Gamma.source)
    (hterminal : R.finish ∈ (Aux L hlegal).terminalCut)
    (havoid : Gamma.Avoids R (GroundingCut.BB (Aux L hlegal) C)) :
    Nonempty
      (GroundingFiniteDescent.EscapeSuffixState
        (Aux L hlegal) C R) := by
  obtain ⟨S, _⟩ := Hseed R hsource hterminal havoid
  exact ⟨S⟩

/-- The two source-geometric operations construct the exact finite contact
descent geometry used by the decoder. -/
theorem finiteContactDescentGeometry_of_legal_lastFragment
    (L : Gamma.KappaLadder kappa) (hlegal : L.IsLegal)
    (C : Set (LV L hlegal))
    (Hseed : TerminalEscapeGeometry L hlegal C)
    (Hstep : LastFragmentResolution L hlegal C) :
    GroundingFiniteDescent.FiniteContactDescentGeometry
      (Aux L hlegal) C := by
  intro R hsource hterminal havoid
  obtain ⟨seed⟩ := exists_seed_of_terminalEscapeGeometry
    L hlegal C Hseed R hsource hterminal havoid
  exact ⟨{
    seed := seed
    resolve := fun S ↦ by
      rcases Hstep R hsource hterminal havoid S with Hprefix | ⟨T, hTS⟩
      · exact Or.inl (S.resolvedRoute_of_hasSourcePrefix Hprefix)
      · exact Or.inr ⟨T, hTS⟩ }⟩

/-- Concrete constructor with the terminal suffix reduced to the exact
terminal-fragment escape classification. -/
theorem finiteContactDescentGeometry_of_terminalFragmentsEscape
    (L : Gamma.KappaLadder kappa) (hlegal : L.IsLegal)
    (C : Set (LV L hlegal))
    (Hterminal : TerminalFragmentsEscape L hlegal C)
    (Hstep : LastFragmentResolution L hlegal C) :
    GroundingFiniteDescent.FiniteContactDescentGeometry
      (Aux L hlegal) C :=
  finiteContactDescentGeometry_of_legal_lastFragment L hlegal C
    (terminalEscapeGeometry_of_terminalFragmentsEscape
      L hlegal C Hterminal) Hstep

/-- Consequently the legal-ladder instance has the exact decoder expected
by Assertion 8.18. -/
theorem finiteDescentDecoder_of_legal_lastFragment
    (L : Gamma.KappaLadder kappa) (hlegal : L.IsLegal)
    (C : Set (LV L hlegal))
    (Hseed : TerminalEscapeGeometry L hlegal C)
    (Hstep : LastFragmentResolution L hlegal C) :
    GroundingCut.FiniteDescentDecoder (Aux L hlegal) C :=
  GroundingFiniteDescent.finiteDescentDecoder_of_contactGeometry
    (Aux L hlegal) C
      (finiteContactDescentGeometry_of_legal_lastFragment
        L hlegal C Hseed Hstep)

/-- Decoder form with no precompiled terminal suffix hypothesis. -/
theorem finiteDescentDecoder_of_terminalFragmentsEscape
    (L : Gamma.KappaLadder kappa) (hlegal : L.IsLegal)
    (C : Set (LV L hlegal))
    (Hterminal : TerminalFragmentsEscape L hlegal C)
    (Hstep : LastFragmentResolution L hlegal C) :
    GroundingCut.FiniteDescentDecoder (Aux L hlegal) C :=
  GroundingFiniteDescent.finiteDescentDecoder_of_contactGeometry
    (Aux L hlegal) C
      (finiteContactDescentGeometry_of_terminalFragmentsEscape
        L hlegal C Hterminal Hstep)

/-- For every contact state, auxiliary separation forces the source route's
contact to lie no later than the fragment's blocking point.  This is the
concrete use of Assertion 8.21 in the last-fragment iteration. -/
theorem contact_beforeEq_blockingPoint
    (L : Gamma.KappaLadder kappa) (hlegal : L.IsLegal)
    (C : Set (LV L hlegal))
    (hC : Popular.IsSeparator (Aux L hlegal).lambda C)
    {R : FinitePath Gamma.graph}
    (S : GroundingFiniteDescent.ContactRoute (Aux L hlegal) C R) :
    GroundingCut.BeforeEq S.fragment.path R.walk.support[S.position]
      (GroundingCut.blockingPoint (Aux L hlegal) C S.fragment) :=
  S.beforeEq_blockingPoint hC

/-- The specialized Assertion 8.18 conclusion once the two literal local
operations have been installed. -/
theorem assertion8_18_of_legal_lastFragment
    (L : Gamma.KappaLadder kappa) (hlegal : L.IsLegal)
    (C : Set (LV L hlegal))
    (hC : Popular.IsSeparator (Aux L hlegal).lambda C)
    (Hseed : TerminalEscapeGeometry L hlegal C)
    (Hstep : LastFragmentResolution L hlegal C) :
    Popular.IsSeparator Gamma (GroundingCut.BB (Aux L hlegal) C) :=
  GroundingCut.assertion8_18 (Aux L hlegal) C hC
    (L.popularAuxiliaryInput_terminalCut_isSeparator hlegal)
    (finiteDescentDecoder_of_legal_lastFragment
      L hlegal C Hseed Hstep)

/-- Fully specialized finite descent with the unconditional terminal-cut
separator and the terminal suffix reduced to the true escaping-fragment
classification.  `Hstep` is now the sole global last-contact splice
invariant. -/
theorem assertion8_18_of_terminalFragmentsEscape
    (L : Gamma.KappaLadder kappa) (hlegal : L.IsLegal)
    (C : Set (LV L hlegal))
    (hC : Popular.IsSeparator (Aux L hlegal).lambda C)
    (Hterminal : TerminalFragmentsEscape L hlegal C)
    (Hstep : LastFragmentResolution L hlegal C) :
    Popular.IsSeparator Gamma (GroundingCut.BB (Aux L hlegal) C) :=
  GroundingCut.assertion8_18 (Aux L hlegal) C hC
    (L.popularAuxiliaryInput_terminalCut_isSeparator hlegal)
    (finiteDescentDecoder_of_terminalFragmentsEscape
      L hlegal C Hterminal Hstep)

end GroundingLegalFiniteDescent
end Erdos599
