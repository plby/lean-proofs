/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.CardinalInduction
import ErdosProblems.Erdos599.Ladder
import ErdosProblems.Erdos599.RoofQuotient

/-!
# The half-way core of a controlled slice

This file isolates the first input to the controlled-slice construction in
Section 9.  There are two points.

* Passing to a smaller source set preserves unhinderedness when no edge
  enters the ambient source.  The proof adjoins the missing sources as
  trivial paths to any putative hindrance.
* The universal induction hypothesis below `kappa`, applied at `#U`, gives
  a half-way linkage from the whole frontier `T_alpha` whose selected
  components link `U` to the target.  The least-altitude stop-over is
  unpacked together with the quotient wave which witnesses its height.

The latter is the precise part of Assertions 9.5--9.10 which precedes the
replacement of most paths by fragments of the limiting ladder warp.
-/

noncomputable section

open Cardinal Set

namespace Erdos599

open DirectedPath

universe u

variable {V : Type u}

namespace DWeb

/-- Keep the graph and target of a web and replace its source by `U`. -/
def sourceSubweb (Gamma : DWeb V) (U : Set V) : DWeb V where
  graph := Gamma.graph
  source := U
  target := Gamma.target

@[simp]
theorem sourceSubweb_graph (Gamma : DWeb V) (U : Set V) :
    (Gamma.sourceSubweb U).graph = Gamma.graph :=
  rfl

@[simp]
theorem sourceSubweb_source (Gamma : DWeb V) (U : Set V) :
    (Gamma.sourceSubweb U).source = U :=
  rfl

@[simp]
theorem sourceSubweb_target (Gamma : DWeb V) (U : Set V) :
    (Gamma.sourceSubweb U).target = Gamma.target :=
  rfl

@[simp]
theorem sourceSubweb_initialSet (Gamma : DWeb V) (U : Set V)
    (W : Set (Gamma.sourceSubweb U).DPath) :
    (Gamma.sourceSubweb U).initialSet W = Gamma.initialSet W :=
  rfl

@[simp]
theorem sourceSubweb_terminalFrontier (Gamma : DWeb V) (U : Set V)
    (W : Set (Gamma.sourceSubweb U).DPath) :
    (Gamma.sourceSubweb U).terminalFrontier W =
      Gamma.terminalFrontier W :=
  rfl

@[simp]
theorem sourceSubweb_roof (Gamma : DWeb V) (U S : Set V) :
    (Gamma.sourceSubweb U).roof S = Gamma.roof S :=
  rfl

@[simp]
theorem sourceSubweb_isWarp (Gamma : DWeb V) (U : Set V)
    (W : Set (Gamma.sourceSubweb U).DPath) :
    (Gamma.sourceSubweb U).IsWarp W ↔ Gamma.IsWarp W :=
  Iff.rfl

/-- A path starting in a no-incoming source set cannot visit a second
source vertex. -/
theorem path_meets_source_only_at_initial
    (Gamma : DWeb V) (hNoEnter : Gamma.NoEdgeEnters Gamma.source)
    {U : Set V} (hU : U ⊆ Gamma.source)
    {p : (Gamma.sourceSubweb U).DPath} (hp : p.initial ∈ U) :
    p.support ∩ Gamma.source ⊆ {p.initial} := by
  intro x hx
  rcases p with q | r
  · exact Set.mem_singleton_iff.mpr
      (Gamma.targetPath_meets_noEdgeEnters_only_at_start
        hNoEnter q (hU hp) hx.1 hx.2)
  · obtain ⟨n, rfl⟩ := hx.1
    cases n with
    | zero => rfl
    | succ n => exact (hNoEnter (r.adj_succ n) hx.2).elim

/-- Source-set inheritance for unhindered webs.  The no-incoming-source
condition is what makes the trivial paths on `source \ U` disjoint from a
wave in the smaller-source web. -/
theorem IsUnhindered.sourceSubweb
    (Gamma : DWeb V) (hGamma : Gamma.IsUnhindered)
    (hNoEnter : Gamma.NoEdgeEnters Gamma.source)
    {U : Set V} (hU : U ⊆ Gamma.source) :
    (Gamma.sourceSubweb U).IsUnhindered := by
  intro hhindered
  obtain ⟨W, hWwave, hWmissing⟩ := hhindered
  let W0 : Set Gamma.DPath := W
  have hW0wave : Gamma.IsWarp W0 ∧ Gamma.initialSet W0 ⊆ U ∧
      U ⊆ Gamma.roof (Gamma.terminalFrontier W0) := by
    simpa only [W0, DWeb.IsWave, sourceSubweb_isWarp,
      sourceSubweb_initialSet, sourceSubweb_source,
      sourceSubweb_roof, sourceSubweb_terminalFrontier] using hWwave
  have hW0missing : Gamma.initialSet W0 ≠ U := by
    simpa only [W0, sourceSubweb_initialSet,
      sourceSubweb_source] using hWmissing
  let R : Set Gamma.DPath := Gamma.trivialPath '' (Gamma.source \ U)
  let Wplus : Set Gamma.DPath := W0 ∪ R
  have hWinitial : Gamma.initialSet W0 ⊆ U := hW0wave.2.1
  have hWsourceOnly :
      ∀ p ∈ W0, p.support ∩ Gamma.source ⊆ {p.initial} := by
    intro p hp
    exact Gamma.path_meets_source_only_at_initial hNoEnter hU
      (hWinitial ⟨p, hp, rfl⟩)
  have hcross :
      ∀ p ∈ W0, ∀ q ∈ R, p ≠ q → Disjoint p.support q.support := by
    intro p hp q hq _hpq
    obtain ⟨x, hx, rfl⟩ := hq
    rw [Gamma.support_trivialPath]
    apply Set.disjoint_singleton_right.2
    intro hxp
    have hxinitial : x = p.initial := by
      simpa using hWsourceOnly p hp ⟨hxp, hx.1⟩
    exact hx.2 (hxinitial.symm ▸ hWinitial ⟨p, hp, rfl⟩)
  have hWplusWarp : Gamma.IsWarp Wplus := by
    apply Set.PairwiseDisjoint.union hW0wave.1
      (Gamma.isWarp_trivialPaths (Gamma.source \ U))
    exact hcross
  have hWplusInitial :
      Gamma.initialSet Wplus =
        Gamma.initialSet W0 ∪ (Gamma.source \ U) := by
    change Gamma.initialSet
        (W0 ∪ (Gamma.trivialPath '' (Gamma.source \ U))) = _
    rw [Gamma.initialSet_union, Gamma.initialSet_trivialPaths]
  have hWplusInitialSub : Gamma.initialSet Wplus ⊆ Gamma.source := by
    rw [hWplusInitial]
    exact Set.union_subset (hWinitial.trans hU) Set.sdiff_subset
  have hWplusRoof :
      Gamma.source ⊆ Gamma.roof (Gamma.terminalFrontier Wplus) := by
    intro x hx
    by_cases hxU : x ∈ U
    · apply Gamma.roof_mono _ (hW0wave.2.2 hxU)
      change Gamma.terminalFrontier W0 ⊆
        Gamma.terminalFrontier (W0 ∪ R)
      rw [Gamma.terminalFrontier_union]
      exact Set.subset_union_left
    · apply Gamma.subset_roof
      change x ∈ Gamma.terminalFrontier (W0 ∪ R)
      change x ∈ Gamma.terminalFrontier
        (W0 ∪ (Gamma.trivialPath '' (Gamma.source \ U)))
      rw [Gamma.terminalFrontier_union,
        Gamma.terminalFrontier_trivialPaths]
      exact Or.inr ⟨hx, hxU⟩
  have hWplusMissing : Gamma.initialSet Wplus ≠ Gamma.source := by
    intro heq
    apply hW0missing
    apply Set.Subset.antisymm hWinitial
    intro x hxU
    have hxPlus : x ∈ Gamma.initialSet Wplus := heq.symm ▸ hU hxU
    rw [hWplusInitial] at hxPlus
    exact hxPlus.resolve_right (fun hxDiff ↦ hxDiff.2 hxU)
  exact hGamma ⟨Wplus,
    ⟨hWplusWarp, hWplusInitialSub, hWplusRoof⟩, hWplusMissing⟩

namespace KappaLadder

/-- If no edge enters the original source, then no edge enters any ladder
frontier in its essential quotient stage.  Old source vertices are
protected by the ambient hypothesis, while commitment vertices are
protected by the defining edge deletion of the quotient. -/
theorem stageWeb_noEdgeEnters
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    (hNoEnter : Gamma.NoEdgeEnters Gamma.source)
    (L : Gamma.KappaLadder kappa) (alpha : Ladder.Stage kappa) :
    (L.stageWeb alpha).NoEdgeEnters (L.frontier alpha) := by
  intro x y hxy hy
  have hxyQuotient :
      (Gamma.quotient
        (Gamma.terminalFrontier (L.warpAt alpha))).graph.Adj x y :=
    hxy.1
  have hySourceOrCommitment :
      y ∈ Gamma.source ∪ Gamma.terminalFrontier (L.warpAt alpha) :=
    hy.1.1
  rcases hySourceOrCommitment with hySource | hyCommitment
  · exact hNoEnter hxyQuotient.1 hySource
  · exact hxyQuotient.2.2.2 hyCommitment

/-- A source subset of an unhindered ladder stage is unhindered as soon
as the ambient web satisfies the standard no-incoming-source condition. -/
theorem stageSourceSubweb_isUnhindered
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    (hNoEnter : Gamma.NoEdgeEnters Gamma.source)
    (L : Gamma.KappaLadder kappa) (alpha : Ladder.Stage kappa)
    (hstage : (L.stageWeb alpha).IsUnhindered)
    {U : Set V} (hU : U ⊆ L.frontier alpha) :
    ((L.stageWeb alpha).sourceSubweb U).IsUnhindered := by
  exact IsUnhindered.sourceSubweb (L.stageWeb alpha) hstage
    (L.stageWeb_noEdgeEnters hNoEnter alpha) hU

end KappaLadder

end DWeb

namespace CardinalInduction

namespace SliceHalfwayCore

/-- The immediate half-way conclusion at a strictly smaller designated
source cardinal. -/
theorem exists_halfwayLinkageOfAltitude_of_lower
    {kappa : Cardinal.{u}}
    (hlower : UniversalCardinalInductionBelow V kappa)
    (Q : DWeb V) (hQ : Q.IsUnhindered)
    {U : Set V} (hUsub : U ⊆ Q.source) (hUInfinite : aleph0 ≤ #U)
    (hU : #U < kappa) :
    ∃ W : Set Q.DPath,
      IsHalfwayLinkageOfAltitude Q U (#U) W := by
  exact (hlower #U hU Q hQ).halfway hUInfinite U hUsub rfl

/-- Choose a stop-over realizing the altitude of the half-way family,
retaining its witness-bearing height bound. -/
theorem exists_halfwayStopover_heightAtMost_of_lower
    {kappa : Cardinal.{u}}
    (hlower : UniversalCardinalInductionBelow V kappa)
    (Q : DWeb V) (hQ : Q.IsUnhindered)
    {U : Set V} (hUsub : U ⊆ Q.source) (hUInfinite : aleph0 ≤ #U)
    (hU : #U < kappa) :
    ∃ (W : Set Q.DPath) (C : Set V),
      IsHalfwayLinkageOfAltitude Q U (#U) W ∧
      IsHalfwayStopover Q W C ∧ HeightAtMost Q C (#U) := by
  obtain ⟨W, hW⟩ :=
    exists_halfwayLinkageOfAltitude_of_lower hlower Q hQ hUsub hUInfinite hU
  obtain ⟨C, hC, hheight⟩ := hW.exists_stopover
  exact ⟨W, C, hW, hC, hheight⟩

/-- Fully unpacked controlled-slice core.  In addition to the
`T_alpha`--`C` linkage and the paths which carry `U` to the original
target, this exposes the set `X` and quotient wave `R` witnessing the
height of `C`.  Its carrier has size at most `#U`, hence strictly less than
the ambient induction cardinal. -/
theorem exists_explicit_halfwayData_of_lower
    {kappa : Cardinal.{u}}
    (hlower : UniversalCardinalInductionBelow V kappa)
    (Q : DWeb V) (hQ : Q.IsUnhindered)
    {U : Set V} (hUsub : U ⊆ Q.source) (hUInfinite : aleph0 ≤ #U)
    (hU : #U < kappa) :
    ∃ (W : Set Q.DPath) (C X : Set V)
        (R : Set (Q.quotient X).DPath),
      IsLinkageBetween Q Q.source C W ∧
      IsTrimmedSeparator Q C ∧
      (Q.quotient C).IsUnhindered ∧
      LinksToTarget Q W U ∧
      X ⊆ Q.sourceᶜ ∧
      (Q.quotient X).IsWave R ∧
      C ⊆ Q.roof ((Q.quotient X).terminalFrontier R) ∧
      #X ≤ #U ∧ #X < kappa := by
  obtain ⟨W, C, hW, hC, X, hX, hXcard⟩ :=
    exists_halfwayStopover_heightAtMost_of_lower hlower Q hQ hUsub
      hUInfinite hU
  obtain ⟨hXsource, R, hR, hroof⟩ := hX
  exact ⟨W, C, X, R, hC.linkage, hC.minimal,
    hC.quotient_unhindered, hW.2.1, hXsource, hR, hroof,
    hXcard, hXcard.trans_lt hU⟩

/-- Stage-web specialization: `Q.source` is definitionally the frontier
`T_alpha`, so the linkage furnished above starts at the entire frontier,
while its selected components link `U` onward to the target. -/
theorem exists_stageExplicitHalfwayData_of_lower
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    (hlower : UniversalCardinalInductionBelow V kappa)
    (L : Gamma.KappaLadder kappa) (alpha : Ladder.Stage kappa)
    (hstage : (L.stageWeb alpha).IsUnhindered)
    {U : Set V} (hUsub : U ⊆ L.frontier alpha)
    (hUInfinite : aleph0 ≤ #U) (hU : #U < kappa) :
    ∃ (W : Set (L.stageWeb alpha).DPath) (C X : Set V)
        (R : Set ((L.stageWeb alpha).quotient X).DPath),
      IsLinkageBetween (L.stageWeb alpha) (L.frontier alpha) C W ∧
      IsTrimmedSeparator (L.stageWeb alpha) C ∧
      ((L.stageWeb alpha).quotient C).IsUnhindered ∧
      LinksToTarget (L.stageWeb alpha) W U ∧
      X ⊆ (L.frontier alpha)ᶜ ∧
      ((L.stageWeb alpha).quotient X).IsWave R ∧
      C ⊆ (L.stageWeb alpha).roof
        (((L.stageWeb alpha).quotient X).terminalFrontier R) ∧
      #X ≤ #U ∧ #X < kappa := by
  change U ⊆ (L.stageWeb alpha).source at hUsub
  simpa only [Erdos599.DWeb.KappaLadder.frontier] using
    (exists_explicit_halfwayData_of_lower
      hlower (L.stageWeb alpha) hstage hUsub hUInfinite hU)

end SliceHalfwayCore
end CardinalInduction
end Erdos599
