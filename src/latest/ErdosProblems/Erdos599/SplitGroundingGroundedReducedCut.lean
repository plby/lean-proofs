/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SplitGroundingGroundedAuxiliary
import ErdosProblems.Erdos599.GroundingRelaxedEscape

/-!
# The source-correct reduced cut for split grounding

The coarse `GroundingCut.G0` retains every blockable surviving fragment.
The source first removes `H_empty`: a *whole* grounded record which is
finite with terminal outside the auxiliary cut, or is an escape-free ray.
Only after that removal is the blocking-point construction applied.

The whole-record condition is essential.  A later fragment of a grounded
record is not the recorded path `H_alpha`, and an arbitrary path whose
initial vertex lies in the ambient source need not be one of the recorded
obstructions.  We also intersect with `IsBlockable`; the published formula
does not prove that every retained hanging ray has a blocking point.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace DWeb.KappaLadder

open _root_.Erdos599.DirectedPath

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

private abbrev ReducedInput (L : Gamma.KappaLadder kappa)
    (hL : L.IsSplitLegal) :=
  L.splitGroundedPopularAuxiliaryInput hL

private abbrev ReducedLV (L : Gamma.KappaLadder kappa)
    (_hL : L.IsSplitLegal) :=
  PopularAuxiliary.Input.LambdaVertex V L.groundedInfiniteRecords

/-- Paths literally chosen at grounded obstruction stages. -/
def splitGroundedRecordedPaths (L : Gamma.KappaLadder kappa) :
    Set Gamma.DPath :=
  {p | ∃ a : Ladder.Stage kappa,
    a ∈ L.phiGround ∧ L.chosen a = some p}

/-- The source's discarded family `H_empty`, specialized to the grounded
split auxiliary.  A member must be the whole surviving chosen record. -/
def splitGroundedHEmpty
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitLegal)
    (C : Set (ReducedLV L hL)) :
    Set (ReducedInput L hL).Fragment :=
  {P | P ∈ GroundingCut.fragments (ReducedInput L hL) C ∧
    P.path = P.parent ∧
    P.parent ∈ L.splitGroundedRecordedPaths ∧
    ((∃ t : V, P.path.terminal? = some t ∧
        t ∉ GroundingCut.CV (ReducedInput L hL) C) ∨
      (¬ P.path.IsFinite ∧
        ¬ P.MeetsEscape (ReducedInput L hL) C))}

/-- Surviving fragments after the literal `H_empty` deletion. -/
def splitGroundedGPrime
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitLegal)
    (C : Set (ReducedLV L hL)) :
    Set (ReducedInput L hL).Fragment :=
  GroundingCut.fragments (ReducedInput L hL) C \
    L.splitGroundedHEmpty hL C

/-- The honest domain of the source blocking-point map.  The extra
`IsBlockable` intersection is necessary because the published `G'` formula
does not eliminate every escape-free hanging ray. -/
def splitGroundedG0
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitLegal)
    (C : Set (ReducedLV L hL)) :
    Set (ReducedInput L hL).Fragment :=
  L.splitGroundedGPrime hL C ∩
    {P | GroundingCut.IsBlockable (ReducedInput L hL) C P}

/-- Blocking points after the source-correct `H_empty` deletion. -/
def splitGroundedBL
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitLegal)
    (C : Set (ReducedLV L hL)) : Set V :=
  GroundingCut.blockingPoint (ReducedInput L hL) C ''
    L.splitGroundedG0 hL C

/-- The source-correct ambient boundary `C_V ∪ BL`. -/
def splitGroundedBB
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitLegal)
    (C : Set (ReducedLV L hL)) : Set V :=
  GroundingCut.CV (ReducedInput L hL) C ∪ L.splitGroundedBL hL C

theorem splitGroundedG0_subset_legacyG0
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitLegal)
    (C : Set (ReducedLV L hL)) :
    L.splitGroundedG0 hL C ⊆ GroundingCut.G0 (ReducedInput L hL) C := by
  rintro P ⟨⟨hfragment, _hnotEmpty⟩, hblockable⟩
  exact ⟨hfragment, hblockable⟩

theorem splitGroundedBL_subset_legacyBL
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitLegal)
    (C : Set (ReducedLV L hL)) :
    L.splitGroundedBL hL C ⊆ GroundingCut.BL (ReducedInput L hL) C := by
  rintro b ⟨P, hP, rfl⟩
  exact ⟨P, L.splitGroundedG0_subset_legacyG0 hL C hP, rfl⟩

theorem splitGroundedBB_subset_legacyBB
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitLegal)
    (C : Set (ReducedLV L hL)) :
    L.splitGroundedBB hL C ⊆ GroundingCut.BB (ReducedInput L hL) C := by
  rintro b (hb | hb)
  · exact GroundingCut.CV_subset_BB (ReducedInput L hL) C hb
  · exact GroundingCut.BL_subset_BB (ReducedInput L hL) C
      (L.splitGroundedBL_subset_legacyBL hL C hb)

theorem splitGroundedCV_subset_BB
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitLegal)
    (C : Set (ReducedLV L hL)) :
    GroundingCut.CV (ReducedInput L hL) C ⊆ L.splitGroundedBB hL C :=
  Set.subset_union_left

theorem splitGroundedBL_subset_BB
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitLegal)
    (C : Set (ReducedLV L hL)) :
    L.splitGroundedBL hL C ⊆ L.splitGroundedBB hL C :=
  Set.subset_union_right

/-! ## Assertion 8.15 for a whole grounded finite record -/

private def oneEdgeFinitePath {W : Type u} {D : Digraph W}
    {x y : W} (hxy : D.Adj x y) (hne : x ≠ y) : FinitePath D where
  start := x
  finish := y
  walk := .cons hxy .nil
  isPath := by
    simp only [Walk.IsPath, Walk.support_cons, Walk.support_nil]
    simp [hne]

@[simp] private theorem oneEdgeFinitePath_support
    {W : Type u} {D : Digraph W} {x y : W}
    (hxy : D.Adj x y) (hne : x ≠ y) :
    (oneEdgeFinitePath hxy hne).support = {x, y} := by
  ext z
  simp [oneEdgeFinitePath, FinitePath.support]

/-- At a finite auxiliary source, the relaxed first step is an actual
`Lambda` edge out of that source. -/
private theorem exists_avoiding_of_relaxedEscape_finiteSource
    {L : Gamma.KappaLadder kappa}
    (J : PopularAuxiliary.Input Gamma L.groundedInfiniteRecords)
    (C : Set (PopularAuxiliary.Input.LambdaVertex V L.groundedInfiniteRecords))
    {t : V} (htSource : t ∈ J.finiteSource)
    (E : J.RelaxedEscape C t) :
    ∃ q : FinitePath J.lambda.graph,
      q.start = .old t ∧ q.finish ∈ J.lambda.target ∧
        J.lambda.Avoids q C := by
  rcases E.start_eq with hordinary | hrelaxed
  · exact ⟨E.route, hordinary, E.target, E.avoids⟩
  · have hadj : J.lambda.graph.Adj (.old t) E.route.start := by
      cases hs : E.route.start with
      | old y =>
          rw [J.lambda_adj_old_old]
          have hy := hrelaxed
          rw [hs] at hy
          exact ⟨Or.inr htSource, hy.1, hy.2⟩
      | edge u y =>
          rw [J.lambda_adj_old_edge]
          have hy := hrelaxed
          rw [hs] at hy
          exact ⟨hy.1, Or.inr ⟨Or.inr htSource, hy.2⟩⟩
      | proxy i =>
          rw [hs] at hrelaxed
          change False at hrelaxed
          exact hrelaxed.elim
    by_cases heq : (PopularAuxiliary.Input.LambdaVertex.old t :
        PopularAuxiliary.Input.LambdaVertex V L.groundedInfiniteRecords) =
        E.route.start
    · exact ⟨E.route, heq.symm, E.target, E.avoids⟩
    · let p : FinitePath J.lambda.graph := oneEdgeFinitePath hadj heq
      have hpAvoid : J.lambda.Avoids p C := by
        change Disjoint p.support C
        rw [Set.disjoint_left]
        intro z hz hzC
        rw [oneEdgeFinitePath_support] at hz
        rcases hz with rfl | rfl
        · exact E.old_not_mem hzC
        · exact Set.disjoint_left.1 E.avoids
            E.route.start_mem_support hzC
      obtain ⟨q, hqstart, hqfinish, hqavoid⟩ :=
        PopularSwitching.exists_avoiding_path_of_avoiding_paths
          p E.route rfl hpAvoid E.avoids
      exact ⟨q, hqstart, hqfinish ▸ E.target, hqavoid⟩

/-- Source Assertion 8.15 in the exact whole-record form: a finite whole
grounded record whose terminal old vertex misses the auxiliary separator
cannot contain an escaping point. -/
theorem splitGrounded_wholeFiniteRecord_not_meetsEscape
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitLegal)
    (C : Set (ReducedLV L hL))
    (hC : Popular.IsSeparator (ReducedInput L hL).lambda C)
    (P : (ReducedInput L hL).Fragment)
    (hfragment : P ∈ GroundingCut.fragments (ReducedInput L hL) C)
    (hwhole : P.path = P.parent)
    (hrecord : P.parent ∈ L.splitGroundedRecordedPaths)
    {t : V} (hterminal : P.path.terminal? = some t)
    (htNotCV : t ∉ GroundingCut.CV (ReducedInput L hL) C) :
    ¬ P.MeetsEscape (ReducedInput L hL) C := by
  rintro ⟨x, hxP, ⟨E⟩⟩
  obtain ⟨a, haGround, hchosen⟩ := hrecord
  have hparentTerminal : Gamma.terminal? P.parent = some t := by
    simpa only [← hwhole] using hterminal
  have haPhi : a ∈ L.phi :=
    (L.bookkeeping.mem_phi_iff_exists_chosen hL.validBookkeeping).2
      ⟨P.parent, hchosen⟩
  have haFinite : a ∈ L.phiFinite := by
    refine ⟨haPhi, ?_⟩
    intro haInfinite
    obtain ⟨q, hq, hqRay⟩ :=
      L.bookkeeping.chosen_isRay_of_mem_phiInfinite
        hL.validBookkeeping haInfinite
    have hqParent : q = P.parent := Option.some.inj (hq.symm.trans hchosen)
    have : Gamma.terminal? q = some t := hqParent ▸ hparentTerminal
    have hnone : (none : Option V) = some t := hqRay.symm.trans this
    cases hnone
  have htSource : t ∈ (ReducedInput L hL).finiteSource := by
    change t ∈ L.groundedFiniteTerminalSet
    exact ⟨a, ⟨haGround, haFinite⟩, P.parent, hchosen,
      hparentTerminal⟩
  have htNotC :
      (PopularAuxiliary.Input.LambdaVertex.old t : ReducedLV L hL) ∉ C := by
    simpa only [GroundingCut.mem_CV] using htNotCV
  have hxt : GroundingCut.BeforeEq P.path x t :=
    GroundingCut.beforeEq_terminal hterminal hxP
  have hroute : ∃ q : FinitePath (ReducedInput L hL).lambda.graph,
      q.start = .old t ∧ q.finish ∈ (ReducedInput L hL).lambda.target ∧
        (ReducedInput L hL).lambda.Avoids q C := by
    by_cases hEq : x = t
    · subst x
      exact exists_avoiding_of_relaxedEscape_finiteSource
        (ReducedInput L hL) C htSource E
    · exact GroundingRelaxedEscape.exists_avoiding_reverse_to_relaxedEscape
        (ReducedInput L hL) C P hfragment ⟨hxt, hEq⟩ htNotC E
  obtain ⟨q, hqstart, hqtarget, hqavoid⟩ := hroute
  exact PopularAuxiliary.Input.no_avoiding_source_target_path
    (ReducedInput L hL).lambda C hC q
      (hqstart ▸ (ReducedInput L hL).mem_lambda_source_old t |>.2 htSource)
      hqtarget hqavoid

/-- Every genuinely escaping surviving fragment remains after the exact
`H_empty` deletion and hence belongs to the reduced blocking domain. -/
theorem splitGrounded_fragment_meeting_escape_mem_G0
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitLegal)
    (C : Set (ReducedLV L hL))
    (hC : Popular.IsSeparator (ReducedInput L hL).lambda C)
    (P : (ReducedInput L hL).Fragment)
    (hfragment : P ∈ GroundingCut.fragments (ReducedInput L hL) C)
    (hescape : P.MeetsEscape (ReducedInput L hL) C) :
    P ∈ L.splitGroundedG0 hL C := by
  refine ⟨⟨hfragment, ?_⟩, Or.inl hescape⟩
  rintro ⟨_hfragment, hwhole, hrecord, hfinite | hinfinite⟩
  · obtain ⟨t, hterminal, htNotCV⟩ := hfinite
    exact L.splitGrounded_wholeFiniteRecord_not_meetsEscape hL C hC P
      hfragment hwhole hrecord hterminal htNotCV hescape
  · exact hinfinite.2 hescape

/-- An essential parent cannot be one of the recorded inessential paths. -/
theorem splitGrounded_essential_not_recorded
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitLegal)
    {p : Gamma.DPath}
    (hp : p ∈ (ReducedInput L hL).essentialLadder) :
    p ∉ L.splitGroundedRecordedPaths := by
  rintro ⟨a, _haGround, hchosen⟩
  have hpInessential : p ∈ Gamma.inessentialPaths L.limitWarp := by
    apply L.recorded_mem_inessential hL.recordedPathsPersist hchosen
    change a.1 + 1 ≤ kappa.ord
    exact (Order.add_one_le_iff).2 a.2
  exact hpInessential.2 hp

end DWeb.KappaLadder
end Erdos599

#print axioms Erdos599.DWeb.KappaLadder.splitGrounded_wholeFiniteRecord_not_meetsEscape
#print axioms Erdos599.DWeb.KappaLadder.splitGrounded_fragment_meeting_escape_mem_G0
