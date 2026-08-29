/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.Ladder
import ErdosProblems.Erdos599.QuotientRoofTransport

/-!
# Self-roofing of the canonical ladder successor

This file proves the local roof invariant needed by the transfinite ladder
construction.  If an old accumulated warp is self-roofing and its frontier
roofs the original source, then the concrete successor obtained by arrowing
with the canonical maximal rung and adjoining the optional trivial marker is
again self-roofing.  Its frontier also continues to roof the original source.
-/

noncomputable section

namespace Erdos599

open Set DirectedPath

universe u

namespace DWeb

variable {V : Type u} (G : DWeb V)

/-- The two canonical lifts of a stage warp are still pairwise disjoint. -/
theorem isWarp_liftedLadderRungOfState'
    (s : G.LadderAccumulationState) :
    G.IsWarp (G.liftedLadderRungOfState s) := by
  rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩ hpq
  have hpq' : p ≠ q := fun h ↦
    hpq (congrArg (G.liftLadderStagePathOf s.1) h)
  have hdisj :=
    (G.stageWebOf s.1).chosenMaximalWave.property.1 hp hq hpq'
  have hpSupport :
      (G.liftLadderStagePathOf s.1 p).support = p.support := by
    unfold liftLadderStagePathOf
    rw [G.support_liftQuotientPath]
    simpa only [stageWebOf] using
      (G.quotient (G.terminalFrontier s.1)).support_liftEssentialPartPath p
  have hqSupport :
      (G.liftLadderStagePathOf s.1 q).support = q.support := by
    unfold liftLadderStagePathOf
    rw [G.support_liftQuotientPath]
    simpa only [stageWebOf] using
      (G.quotient (G.terminalFrontier s.1)).support_liftEssentialPartPath q
  simpa only [Function.onFun, hpSupport, hqSupport] using hdisj

/-- Initial vertices are vertices of the same path family. -/
theorem initialSet_subset_vertexSet' (W : Set G.DPath) :
    G.initialSet W ⊆ G.vertexSet W := by
  rintro x ⟨p, hp, rfl⟩
  exact ⟨p, hp, p.initial_mem_support⟩

/-- The candidate-extraction argument for a self-roofing warp.  The usual
library statement assumes a wave and a source vertex; the construction only
uses the resulting roof membership and self-roofing, so this is the precise
local form needed for ladder stages. -/
theorem exists_arrow_candidate_ending_of_self_roofing
    {U W : Set G.DPath}
    (hUself : G.vertexSet U ⊆ G.roof (G.terminalFrontier U))
    {q : FinitePath G.graph} (hqW : (Sum.inl q : G.DPath) ∈ W)
    (hqRoof : q.start ∈ G.roof (G.terminalFrontier U))
    {r : FinitePath G.graph} (hrStart : r.start = q.finish)
    (hrTarget : r.finish ∈ G.target)
    (hrAvoid : G.Avoids r (G.terminalFrontier U)) :
    ∃ f : FinitePath G.graph, ∃ hfU : (Sum.inl f : G.DPath) ∈ U,
      ∃ c : G.ArrowCandidate U W f,
        c.path = (.inl q : G.DPath) ∧
        (Path.appendAt f c.path c.finish_mem (c.appendable hfU)).terminal? =
          some q.finish := by
  let rwlk : Walk G.graph q.finish r.finish :=
    RelationalRoof.castStart G.graph.Adj hrStart r.walk
  let whole := q.walk.append rwlk
  have hmeet : whole.Meets (G.terminalFrontier U) :=
    RelationalRoof.roof_meets_walk G.graph.Adj G.target hqRoof whole hrTarget
  have hqmeet : q.walk.Meets (G.terminalFrontier U) := by
    obtain ⟨z, hzwhole, hzU⟩ := hmeet
    rw [Walk.support_append] at hzwhole
    rcases List.mem_append.mp hzwhole with hzq | hzr
    · exact ⟨z, hzq, hzU⟩
    · exfalso
      apply Set.disjoint_left.1 hrAvoid
      · change z ∈ r.walk.support
        simpa [rwlk, RelationalRoof.support_castStart] using
          List.mem_of_mem_tail hzr
      · exact hzU
  let L := q.walk.lastHit (G.terminalFrontier U) hqmeet
  obtain ⟨up, hupU, hupTerm⟩ := L.startpoint_mem
  rcases up with f | ray
  · have hfinish : f.finish = L.startpoint := Option.some.inj hupTerm
    let sf := q.suffixData L.startpoint
      (L.support_subset L.walk.start_mem_support)
    have hsfL : sf.walk.support = L.walk.support := by
      apply G.suffix_support_eq_of_same_start q.walk q.isPath
      · exact q.suffixData_support_suffix _ _
      · exact L.support_suffix
    have hclean :
        (Path.suffixFrom (Sum.inl q : Path G.graph)
          L.startpoint (L.support_subset L.walk.start_mem_support)).support ∩
            G.vertexSet U = {L.startpoint} := by
      ext x
      constructor
      · rintro ⟨hxs, hxU⟩
        change x ∈ sf.walk.support at hxs
        rw [hsfL] at hxs
        rcases RelationalRoof.mem_support_iff_start_or_mem_tail
            G.graph.Adj L.walk |>.1 hxs with hxeq | hxtail
        · simpa [hxeq]
        · exfalso
          have hxRoof : x ∈ G.roof (G.terminalFrontier U) :=
            hUself hxU
          let X := L.walk.lastHit ({x} : Set V) ⟨x, hxs, by simp⟩
          have hXstart : X.startpoint = x := by
            simpa using X.startpoint_mem
          let xwalk : Walk G.graph x r.finish :=
            (RelationalRoof.castStart G.graph.Adj hXstart X.walk).append rwlk
          have hxwalkAvoid : ∀ {y}, y ∈ xwalk.support →
              y ∉ G.terminalFrontier U := by
            intro y hy hyA
            dsimp only [xwalk] at hy
            rw [Walk.support_append] at hy
            rcases List.mem_append.mp hy with hyX | hyr
            · have hyL : y ∈ L.walk.support := X.support_subset (by
                simpa [RelationalRoof.support_castStart] using hyX)
              rcases RelationalRoof.mem_support_iff_start_or_mem_tail
                  G.graph.Adj L.walk |>.1 hyL with hyeq | hytail
              · have hxEq : x = L.startpoint := by
                  have hLXin : L.startpoint ∈ X.walk.support := by
                    have hyX' : y ∈ X.walk.support := by
                      simpa [RelationalRoof.support_castStart] using hyX
                    simpa [hyeq] using hyX'
                  have heqSupports : X.walk.support = L.walk.support :=
                    List.Nodup.eq_of_head_mem_of_suffix
                      (hne := L.walk.support_ne_nil) X.support_suffix
                      (by simpa using hLXin) (L.isPath q.isPath)
                  have heq := congrArg (fun l => l[0]?) heqSupports
                  have hheads : X.startpoint = L.startpoint := by
                    rw [RelationalRoof.getElem?_zero_support G.graph.Adj X.walk,
                      RelationalRoof.getElem?_zero_support G.graph.Adj L.walk]
                      at heq
                    exact Option.some.inj heq
                  exact hXstart.symm.trans hheads
                exact (L.no_mem_after (hxEq ▸ hxtail)) L.startpoint_mem
              · exact L.no_mem_after hytail hyA
            · exact Set.disjoint_left.1 hrAvoid
                (by
                  change y ∈ r.walk.support
                  simpa [rwlk, RelationalRoof.support_castStart] using
                    List.mem_of_mem_tail hyr) hyA
          obtain ⟨y, hy, hyA⟩ :=
            RelationalRoof.roof_meets_walk G.graph.Adj G.target
              hxRoof xwalk hrTarget
          exact hxwalkAvoid hy hyA
      · intro hx
        have hxeq : x = L.startpoint := by simpa using hx
        subst x
        exact ⟨by
          change L.startpoint ∈ sf.walk.support
          rw [hsfL]
          exact L.walk.start_mem_support,
          ⟨.inl f, hupU, by
            change L.startpoint ∈ f.support
            simpa [hfinish] using f.finish_mem_support⟩⟩
    have hfU : (Sum.inl f : G.DPath) ∈ U := hupU
    have hfinishMem : f.finish ∈ Path.support (.inl q : G.DPath) := by
      rw [hfinish]
      exact L.support_subset L.walk.start_mem_support
    let c : G.ArrowCandidate U W f :=
      { path := .inl q
        mem_path := hqW
        finish_mem := hfinishMem
        clean := by simpa [hfinish] using hclean }
    refine ⟨f, hfU, c, rfl, ?_⟩
    rw [Path.terminal?_appendAt]
    rfl
  · simp at hupTerm

/-- Every essential point of the union of two cross-roofed self-roofing
warps is a terminal of their concrete arrow. -/
theorem essential_union_subset_terminalFrontier_arrow_of_crossRoof
    {U W : Set G.DPath} (hUwarp : G.IsWarp U) (hWwarp : G.IsWarp W)
    (hUself : G.vertexSet U ⊆ G.roof (G.terminalFrontier U))
    (hWself : G.vertexSet W ⊆ G.roof (G.terminalFrontier W))
    (hUroof : G.initialSet (U ∪ W) ⊆
      G.roof (G.terminalFrontier U)) :
    G.essential (G.terminalFrontier U ∪ G.terminalFrontier W) ⊆
      G.terminalFrontier (G.arrow U W) := by
  intro z hzEss
  let A := G.terminalFrontier U
  let B := G.terminalFrontier W
  simp only [DWeb.essential] at hzEss
  replace hzEss : z ∈ A ∪ B ∧ z ∉ G.roof ((A ∪ B) \ {z}) := by
    simpa [A, B] using hzEss
  have of_mem_A : z ∈ A → z ∈ G.terminalFrontier (G.arrow U W) := by
    intro hzA
    obtain ⟨p, hpU, hpTerm⟩ := hzA
    rcases p with f | ray
    · have hfFinish : f.finish = z := Option.some.inj hpTerm
      rcases G.arrowPath_finite_cases U W f hpU with heq | ⟨c, heq⟩
      · exact ⟨G.arrowPath U W ⟨.inl f, hpU⟩,
          ⟨⟨.inl f, hpU⟩, rfl⟩, by simpa [heq] using hpTerm⟩
      · by_cases hzB : z ∈ B
        · obtain ⟨q, hqW, hqTerm⟩ := hzB
          have hcq : c.path = q := by
            by_contra hne
            exact Set.disjoint_left.1 (hWwarp c.mem_path hqW hne)
              (hfFinish ▸ c.finish_mem) (G.terminal_mem_support hqTerm)
          have hcTerm : c.path.terminal? = some z := hcq ▸ hqTerm
          exact ⟨G.arrowPath U W ⟨.inl f, hpU⟩,
            ⟨⟨.inl f, hpU⟩, rfl⟩,
            G.terminal_arrowPath_of_candidate hWwarp hpU c hcTerm⟩
        · exfalso
          have hzRoofB : z ∈ G.roof B :=
            hWself ⟨c.path, c.mem_path, hfFinish ▸ c.finish_mem⟩
          have hsub : B ⊆ (A ∪ B) \ {z} := by
            intro x hxB
            exact ⟨Or.inr hxB, by
              intro hxz
              have : x = z := by simpa using hxz
              exact hzB (this ▸ hxB)⟩
          exact hzEss.2 (G.roof_mono hsub hzRoofB)
    · simp at hpTerm
  rcases hzEss.1 with hzA | hzB
  · exact of_mem_A hzA
  · by_cases hzA : z ∈ A
    · exact of_mem_A hzA
    · obtain ⟨q, hqW, hqTerm⟩ := hzB
      rcases q with q | ray
      · have hqFinish : q.finish = z := Option.some.inj hqTerm
        have hqInitial : q.start ∈ G.initialSet (U ∪ W) := by
          rw [G.initialSet_union]
          exact Or.inr ⟨.inl q, hqW, rfl⟩
        have hqRoof : q.start ∈ G.roof A := hUroof hqInitial
        obtain ⟨r, hrTarget, hrAvoid⟩ :=
          (G.not_mem_roof_iff ((A ∪ B) \ {z}) z).1 hzEss.2
        have hrStart : r.start = q.finish := hrTarget.1.trans hqFinish.symm
        have hrAvoidA : G.Avoids r A := by
          unfold DWeb.Avoids at hrAvoid ⊢
          rw [Set.disjoint_left] at hrAvoid ⊢
          intro x hxr hxA
          apply hrAvoid hxr
          exact ⟨Or.inl hxA, by
            intro hxz
            have : x = z := by simpa using hxz
            exact hzA (this ▸ hxA)⟩
        obtain ⟨f, hfU, c, hcPath, _⟩ :=
          G.exists_arrow_candidate_ending_of_self_roofing
            hUself hqW hqRoof hrStart hrTarget.2 hrAvoidA
        have hcTerm : c.path.terminal? = some z := by
          rw [hcPath]
          exact hqTerm
        exact ⟨G.arrowPath U W ⟨.inl f, hfU⟩,
          ⟨⟨.inl f, hfU⟩, rfl⟩,
          G.terminal_arrowPath_of_candidate hWwarp hfU c hcTerm⟩
      · simp at hqTerm

/-- Source-free form of the arrow roof calculation.  The two input warps
need only roof the union of their initial sets. -/
theorem roof_terminalFrontier_arrow_eq_union_of_crossRoof'
    {U W : Set G.DPath} (hUwarp : G.IsWarp U) (hWwarp : G.IsWarp W)
    (hUself : G.vertexSet U ⊆ G.roof (G.terminalFrontier U))
    (hWself : G.vertexSet W ⊆ G.roof (G.terminalFrontier W))
    (hUroof : G.initialSet (U ∪ W) ⊆
      G.roof (G.terminalFrontier U))
    (hWroof : G.initialSet (U ∪ W) ⊆
      G.roof (G.terminalFrontier W)) :
    G.roof (G.terminalFrontier (G.arrow U W)) =
      G.roof (G.terminalFrontier U ∪ G.terminalFrontier W) := by
  have hess :
      G.essential (G.terminalFrontier (G.arrow U W)) =
        G.essential (G.terminalFrontier U ∪ G.terminalFrontier W) :=
    RelationalRoof.essential_sandwich G.graph.Adj G.target
      (G.essential_union_subset_terminalFrontier_arrow_of_crossRoof
        hUwarp hWwarp hUself hWself hUroof)
      (G.terminalFrontier_arrow_subset_union U W)
  calc
    G.roof (G.terminalFrontier (G.arrow U W)) =
        G.roof (G.essential (G.terminalFrontier (G.arrow U W))) :=
      (G.roof_essential _).symm
    _ = G.roof (G.essential
        (G.terminalFrontier U ∪ G.terminalFrontier W)) :=
      congrArg G.roof hess
    _ = G.roof (G.terminalFrontier U ∪ G.terminalFrontier W) :=
      G.roof_essential _

/-- Lifted rung paths start in the old essential terminal frontier. -/
theorem initialSet_liftedLadderRungOfState_subset_essential
    (s : G.LadderAccumulationState)
    (hsource : G.source ⊆ G.roof (G.terminalFrontier s.1)) :
    G.initialSet (G.liftedLadderRungOfState s) ⊆
      G.essential (G.terminalFrontier s.1) := by
  let Q := G.quotient (G.terminalFrontier s.1)
  rintro x ⟨_, ⟨p, hp, rfl⟩, rfl⟩
  have hpSource : p.initial ∈ Q.source := by
    have hpStage : p.initial ∈ (G.stageWebOf s.1).source :=
      (G.stageWebOf s.1).chosenMaximalWave.property.2.1
        ⟨p, hp, rfl⟩
    exact hpStage.1
  rw [G.quotient_source_eq_essential_terminalFrontier_of_roofsSource
    hsource] at hpSource
  rcases p with p | r <;> exact hpSource

/-- The lifted canonical rung roofs the old essential commitment frontier. -/
theorem essential_subset_roof_terminalFrontier_liftedLadderRungOfState
    (hNoEnter : G.NoEdgeEnters G.source)
    (s : G.LadderAccumulationState) :
    G.essential (G.terminalFrontier s.1) ⊆
      G.roof (G.terminalFrontier (G.liftedLadderRungOfState s)) := by
  let Q := G.quotient (G.terminalFrontier s.1)
  let UQ : Set Q.DPath :=
    Q.liftEssentialPartFamily (G.ladderRungOfState s)
  have hUQ : Q.IsWave UQ :=
    Q.isWave_liftEssentialPartFamily
      (G.stageWebOf s.1).chosenMaximalWave.property
  have hroof :=
    G.essential_subset_original_roof_of_quotient_wave_general hNoEnter hUQ
  have hfrontier :
      G.terminalFrontier (G.liftedLadderRungOfState s) =
        Q.terminalFrontier UQ := by
    ext x
    constructor
    · rintro ⟨_, ⟨p, hp, rfl⟩, hterm⟩
      refine ⟨Q.liftEssentialPartPath p, ⟨p, hp, rfl⟩, ?_⟩
      simpa only [Q, stageWebOf, liftLadderStagePathOf,
        G.terminal?_liftQuotientPath,
        (G.quotient (G.terminalFrontier s.1)).terminal?_liftEssentialPartPath]
        using hterm
    · rintro ⟨_, ⟨p, hp, rfl⟩, hterm⟩
      refine ⟨G.liftLadderStagePathOf s.1 p, ⟨p, hp, rfl⟩, ?_⟩
      simpa only [Q, stageWebOf, liftLadderStagePathOf,
        G.terminal?_liftQuotientPath,
        (G.quotient (G.terminalFrontier s.1)).terminal?_liftEssentialPartPath]
        using hterm
  rwa [hfrontier]

/-- The lifted canonical rung is self-roofing in the original web. -/
theorem liftedLadderRungOfState_self_roofing
    (hNoEnter : G.NoEdgeEnters G.source)
    (s : G.LadderAccumulationState) :
    G.vertexSet (G.liftedLadderRungOfState s) ⊆
      G.roof (G.terminalFrontier (G.liftedLadderRungOfState s)) := by
  let Q := G.quotient (G.terminalFrontier s.1)
  let UQ : Set Q.DPath :=
    Q.liftEssentialPartFamily (G.ladderRungOfState s)
  have hUQ : Q.IsWave UQ :=
    Q.isWave_liftEssentialPartFamily
      (G.stageWebOf s.1).chosenMaximalWave.property
  have htransport :=
    G.quotientWave_roof_subset_original_roof_general hNoEnter hUQ
  intro x hx
  obtain ⟨_, ⟨p, hp, rfl⟩, hxp⟩ := hx
  have hxQ : x ∈ Q.vertexSet UQ := by
    refine ⟨Q.liftEssentialPartPath p, ⟨p, hp, rfl⟩, ?_⟩
    simpa only [stageWebOf, liftLadderStagePathOf,
      G.support_liftQuotientPath, Q.support_liftEssentialPartPath]
      using hxp
  have hxRoofQ : x ∈ Q.roof (Q.terminalFrontier UQ) :=
    DWeb.IsWave.self_roofing (Γ := Q) hUQ hxQ
  have hxRoofG : x ∈ G.roof (Q.terminalFrontier UQ) :=
    htransport hxRoofQ
  have hfrontier :
      G.terminalFrontier (G.liftedLadderRungOfState s) =
        Q.terminalFrontier UQ := by
    ext y
    constructor
    · rintro ⟨_, ⟨q, hq, rfl⟩, hterm⟩
      refine ⟨Q.liftEssentialPartPath q, ⟨q, hq, rfl⟩, ?_⟩
      simpa only [Q, stageWebOf, liftLadderStagePathOf,
        G.terminal?_liftQuotientPath,
        (G.quotient (G.terminalFrontier s.1)).terminal?_liftEssentialPartPath]
        using hterm
    · rintro ⟨_, ⟨q, hq, rfl⟩, hterm⟩
      refine ⟨G.liftLadderStagePathOf s.1 q, ⟨q, hq, rfl⟩, ?_⟩
      simpa only [Q, stageWebOf, liftLadderStagePathOf,
        G.terminal?_liftQuotientPath,
        (G.quotient (G.terminalFrontier s.1)).terminal?_liftEssentialPartPath]
        using hterm
  rwa [hfrontier]

/-- The terminal roof of the canonical arrow contains the terminal roof of
the old accumulated family.  The hypotheses are exactly the two inductive
roof invariants: old self-roofing and roofing of the original source. -/
theorem roof_terminalFrontier_subset_canonicalArrow
    (hNoEnter : G.NoEdgeEnters G.source)
    (s : G.LadderAccumulationState)
    (hwarp : G.IsWarp s.1)
    (hself : G.vertexSet s.1 ⊆ G.roof (G.terminalFrontier s.1))
    (hsource : G.source ⊆ G.roof (G.terminalFrontier s.1)) :
    G.roof (G.terminalFrontier s.1) ⊆
      G.roof (G.terminalFrontier
        (G.arrow s.1 (G.liftedLadderRungOfState s))) := by
  let R := G.liftedLadderRungOfState s
  have hRwarp : G.IsWarp R :=
    G.isWarp_liftedLadderRungOfState' s
  have hRself : G.vertexSet R ⊆ G.roof (G.terminalFrontier R) :=
    G.liftedLadderRungOfState_self_roofing hNoEnter s
  have hRinitial : G.initialSet R ⊆
      G.essential (G.terminalFrontier s.1) :=
    G.initialSet_liftedLadderRungOfState_subset_essential s hsource
  have hEssR : G.essential (G.terminalFrontier s.1) ⊆
      G.roof (G.terminalFrontier R) :=
    G.essential_subset_roof_terminalFrontier_liftedLadderRungOfState
      hNoEnter s
  have hOldRoofR : G.roof (G.terminalFrontier s.1) ⊆
      G.roof (G.terminalFrontier R) := by
    rw [← G.roof_essential (G.terminalFrontier s.1)]
    exact G.roof_cut hEssR
  have hOldCross : G.initialSet (s.1 ∪ R) ⊆
      G.roof (G.terminalFrontier s.1) := by
    rw [G.initialSet_union]
    intro x hx
    rcases hx with hxOld | hxR
    · exact hself (G.initialSet_subset_vertexSet' s.1 hxOld)
    · exact (G.essential_subset_roof (G.terminalFrontier s.1))
        (hRinitial hxR)
  have hRcross : G.initialSet (s.1 ∪ R) ⊆
      G.roof (G.terminalFrontier R) := by
    rw [G.initialSet_union]
    intro x hx
    rcases hx with hxOld | hxR
    · exact hOldRoofR
        (hself (G.initialSet_subset_vertexSet' s.1 hxOld))
    · exact hEssR (hRinitial hxR)
  rw [G.roof_terminalFrontier_arrow_eq_union_of_crossRoof'
    hwarp hRwarp hself hRself hOldCross hRcross]
  exact G.roof_mono Set.subset_union_left

/-- The canonical arrow is self-roofing whenever the old warp is. -/
theorem canonicalArrow_self_roofing
    (hNoEnter : G.NoEdgeEnters G.source)
    (s : G.LadderAccumulationState)
    (hwarp : G.IsWarp s.1)
    (hself : G.vertexSet s.1 ⊆ G.roof (G.terminalFrontier s.1))
    (hsource : G.source ⊆ G.roof (G.terminalFrontier s.1)) :
    G.vertexSet (G.arrow s.1 (G.liftedLadderRungOfState s)) ⊆
      G.roof (G.terminalFrontier
        (G.arrow s.1 (G.liftedLadderRungOfState s))) := by
  let R := G.liftedLadderRungOfState s
  have hOldRoof :=
    G.roof_terminalFrontier_subset_canonicalArrow
      hNoEnter s hwarp hself hsource
  have hRself : G.vertexSet R ⊆ G.roof (G.terminalFrontier R) :=
    G.liftedLadderRungOfState_self_roofing hNoEnter s
  have hRwarp : G.IsWarp R :=
    G.isWarp_liftedLadderRungOfState' s
  have hRinitial : G.initialSet R ⊆
      G.essential (G.terminalFrontier s.1) :=
    G.initialSet_liftedLadderRungOfState_subset_essential s hsource
  have hEssR : G.essential (G.terminalFrontier s.1) ⊆
      G.roof (G.terminalFrontier R) :=
    G.essential_subset_roof_terminalFrontier_liftedLadderRungOfState
      hNoEnter s
  have hOldRoofR : G.roof (G.terminalFrontier s.1) ⊆
      G.roof (G.terminalFrontier R) := by
    rw [← G.roof_essential (G.terminalFrontier s.1)]
    exact G.roof_cut hEssR
  have hOldCross : G.initialSet (s.1 ∪ R) ⊆
      G.roof (G.terminalFrontier s.1) := by
    rw [G.initialSet_union]
    intro x hx
    rcases hx with hxOld | hxR
    · exact hself (G.initialSet_subset_vertexSet' s.1 hxOld)
    · exact G.essential_subset_roof _ (hRinitial hxR)
  have hRcross : G.initialSet (s.1 ∪ R) ⊆
      G.roof (G.terminalFrontier R) := by
    rw [G.initialSet_union]
    intro x hx
    rcases hx with hxOld | hxR
    · exact hOldRoofR
        (hself (G.initialSet_subset_vertexSet' s.1 hxOld))
    · exact hEssR (hRinitial hxR)
  intro x hx
  rcases G.vertexSet_arrow_subset s.1 R hx with hxOld | hxR
  · exact hOldRoof (hself hxOld)
  · rw [G.roof_terminalFrontier_arrow_eq_union_of_crossRoof'
        hwarp hRwarp hself hRself hOldCross hRcross]
    exact G.roof_mono Set.subset_union_right (hRself hxR)

/-- The optional marker family consists of at most one trivial path and is
therefore self-roofing. -/
theorem ladderMarkerPathSetOfState_self_roofing
    (preferred : Option V) (s : G.LadderAccumulationState) :
    G.vertexSet (G.ladderMarkerPathSetOfState preferred s) ⊆
      G.roof (G.terminalFrontier
        (G.ladderMarkerPathSetOfState preferred s)) := by
  cases hm : G.ladderMarkerOfState preferred s with
  | none =>
      intro x hx
      rcases hx with ⟨p, hp, _⟩
      simp [ladderMarkerPathSetOfState, hm] at hp
  | some y =>
      intro x hx
      rcases hx with ⟨p, hp, hxp⟩
      have hpEq : p = G.trivialPath y := by
        simpa [ladderMarkerPathSetOfState, hm] using hp
      subst p
      rw [G.support_trivialPath] at hxp
      have hxy : x = y := by simpa using hxp
      subst x
      apply G.subset_roof
      refine ⟨G.trivialPath y, ?_, G.terminal?_trivialPath y⟩
      simp [ladderMarkerPathSetOfState, hm]

/-- The full active successor, including its optional marker, is
self-roofing. -/
theorem activeLadderSuccessor_self_roofing
    (hNoEnter : G.NoEdgeEnters G.source)
    (preferred : Option V) (s : G.LadderAccumulationState)
    (hwarp : G.IsWarp s.1)
    (hself : G.vertexSet s.1 ⊆ G.roof (G.terminalFrontier s.1))
    (hsource : G.source ⊆ G.roof (G.terminalFrontier s.1)) :
    G.vertexSet (G.activeLadderSuccessor preferred s) ⊆
      G.roof (G.terminalFrontier
        (G.activeLadderSuccessor preferred s)) := by
  rw [activeLadderSuccessor, G.vertexSet_union, G.terminalFrontier_union]
  intro x hx
  rcases hx with hxArrow | hxMarker
  · exact G.roof_mono Set.subset_union_left
      (G.canonicalArrow_self_roofing hNoEnter s hwarp hself hsource hxArrow)
  · exact G.roof_mono Set.subset_union_right
      (G.ladderMarkerPathSetOfState_self_roofing preferred s hxMarker)

/-- The full active successor continues to roof the original source. -/
theorem source_subset_roof_activeLadderSuccessor
    (hNoEnter : G.NoEdgeEnters G.source)
    (preferred : Option V) (s : G.LadderAccumulationState)
    (hwarp : G.IsWarp s.1)
    (hself : G.vertexSet s.1 ⊆ G.roof (G.terminalFrontier s.1))
    (hsource : G.source ⊆ G.roof (G.terminalFrontier s.1)) :
    G.source ⊆ G.roof (G.terminalFrontier
      (G.activeLadderSuccessor preferred s)) := by
  rw [activeLadderSuccessor, G.terminalFrontier_union]
  exact hsource.trans
    ((G.roof_terminalFrontier_subset_canonicalArrow
      hNoEnter s hwarp hself hsource).trans
      (G.roof_mono Set.subset_union_left))

/-- The paired local invariant in the form consumed by the unrestricted
ordinal recursion.  On an active state this is the canonical arrow/marker
calculation above; after the construction freezes, the path family is held
fixed and both invariants are preserved literally. -/
theorem ladderSuccessorState_roof_invariants
    (hNoEnter : G.NoEdgeEnters G.source)
    (preferred : Ordinal.{u} → Option V) (o : Ordinal.{u})
    (s : G.LadderAccumulationState)
    (hwarp : G.IsWarp s.1)
    (hself : G.vertexSet s.1 ⊆ G.roof (G.terminalFrontier s.1))
    (hsource : G.source ⊆ G.roof (G.terminalFrontier s.1)) :
    G.vertexSet (G.ladderSuccessorState preferred o s).1 ⊆
        G.roof (G.terminalFrontier
          (G.ladderSuccessorState preferred o s).1) ∧
      G.source ⊆ G.roof (G.terminalFrontier
        (G.ladderSuccessorState preferred o s).1) := by
  classical
  by_cases hs : s.2 = true
  · rw [ladderSuccessorState, dif_pos hs]
    exact ⟨G.activeLadderSuccessor_self_roofing
        hNoEnter (preferred o) s hwarp hself hsource,
      G.source_subset_roof_activeLadderSuccessor
        hNoEnter (preferred o) s hwarp hself hsource⟩
  · rw [ladderSuccessorState, dif_neg hs]
    exact ⟨hself, hsource⟩

end DWeb
end Erdos599
