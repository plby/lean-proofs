/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SafeLink

/-!
# The deletion--quotient arrow (Aharoni--Berger Lemma 3.15)

This file proves the concrete form of the arrow lemma which is used in the
safe-link construction.  The paper works throughout with a normalized web;
our `DWeb` structure deliberately does not bake that convention into its
type.  Consequently the two normalization facts used by Corollary 3.10
(`NoEdgeEnters source` and disjointness of the commitment set from the
source) occur explicitly in the final statement.

There is one further representational detail.  Deletion keeps the original
vertex type, so a deleted vertex belongs vacuously to every deleted-web roof.
Thus "a path meets the roof in `G - X`" is represented by a meeting at a
*retained* vertex, i.e. a point of that roof outside `X`.
-/

namespace Erdos599

open Set
open DirectedPath

universe u

namespace DWeb

variable {V : Type u} (G : DWeb V)

/-- A proper suffix of a finite simple path cannot contain the original
initial vertex. -/
theorem start_not_mem_suffixFromAux_of_ne
    (p : FinitePath G.graph) (x : V) (hx : x ∈ p.support)
    (hne : x ≠ p.start) :
    p.start ∉ (p.suffixFromAux x hx).support := by
  intro hstart
  have heq : (p.suffixData x hx).walk.support = p.walk.support := by
    apply List.Nodup.eq_of_head_mem_of_suffix
      (p.suffixData_support_suffix x hx)
    · rw [p.walk.head_support]
      exact hstart
    · exact p.isPath
  have hheads := congrArg List.head? heq
  apply hne
  rw [List.head?_eq_head (p.suffixData x hx).walk.support_ne_nil,
    (p.suffixData x hx).walk.head_support,
    List.head?_eq_head p.walk.support_ne_nil,
    p.walk.head_support] at hheads
  exact Option.some.inj hheads

/-- A suffix of a quotient path which starts outside the commitment set
avoids that set.  This is the same-type replacement for the paper's implicit
statement that such a suffix is a path in the vertex-deleted web. -/
theorem suffixFrom_liftQuotientPath_avoids_subset
    (X Z : Set V) (hXZ : X ⊆ Z)
    (q : FinitePath (G.quotient Z).graph)
    (u : V) (hu : u ∈ q.support) (huX : u ∉ X) :
    Disjoint
      ((q.lift (fun {_ _} h ↦ G.quotient_adj_imp (X := Z) h)).suffixFrom u
        (by simpa using hu)).support X := by
  let lifted : FinitePath G.graph :=
    q.lift (fun {_ _} h ↦ G.quotient_adj_imp (X := Z) h)
  have huLift : u ∈ lifted.support := by simpa [lifted] using hu
  apply Set.disjoint_left.2
  intro y hys hyX
  have hys' : y ∈ (lifted.suffixFrom u huLift).support := by
    exact hys
  have hyq : y ∈ q.support := by
    have : y ∈ lifted.support :=
      lifted.suffixFrom_support_subset u huLift hys'
    simpa [lifted] using this
  rcases G.quotientPath_support_initial_or_avoids Z (.inl q) hyq with
    hyInit | hyAvoid
  · change y = q.start at hyInit
    subst y
    have heq :
        (lifted.suffixFrom u huLift).walk.support =
          lifted.walk.support := by
      apply List.Nodup.eq_of_head_mem_of_suffix
        ((lifted.walk.lastHit ({u} : Set V)
          ⟨u, huLift, Set.mem_singleton u⟩).support_suffix)
      · have hhead : lifted.walk.support.head lifted.walk.support_ne_nil = q.start := by
          exact lifted.walk.head_support
        rw [hhead]
        exact hys'
      · exact lifted.isPath
    have hheads := congrArg List.head? heq
    have huInit : u = q.start := by
      rw [List.head?_eq_head
          (lifted.suffixFrom u huLift).walk.support_ne_nil,
        (lifted.suffixFrom u huLift).walk.head_support,
        lifted.suffixFrom_start u huLift,
        List.head?_eq_head lifted.walk.support_ne_nil,
        lifted.walk.head_support] at hheads
      exact Option.some.inj hheads
    exact huX (huInit ▸ hyX)
  · exact hyAvoid.2 (hXZ hyX)

/-- The commitment-set specialization of
`suffixFrom_liftQuotientPath_avoids_subset`. -/
theorem suffixFrom_liftQuotientPath_avoids_commitment
    (Z : Set V) (q : FinitePath (G.quotient Z).graph)
    (u : V) (hu : u ∈ q.support) (huZ : u ∉ Z) :
    Disjoint
      ((q.lift (fun {_ _} h ↦ G.quotient_adj_imp (X := Z) h)).suffixFrom u
        (by simpa using hu)).support Z :=
  G.suffixFrom_liftQuotientPath_avoids_subset Z Z Subset.rfl q u hu huZ

/-- If a finite quotient path contains a retained point of the roof of a
deleted-web wave, then the path itself contains a point of that wave's
terminal frontier.  The retainedness condition is essential in our
same-type model of vertex deletion: a deleted vertex belongs vacuously to
every deleted-web roof. -/
theorem quotientFinitePath_meets_deleteWave_terminal
    {X Z : Set V} (hXZ : X ⊆ Z)
    {U : Set (G.delete X).DPath} (hU : (G.delete X).IsWave U)
    (q : FinitePath (G.quotient Z).graph)
    (hmeet : ∃ u ∈ q.support,
      u ∉ X ∧ u ∈ (G.delete X).roof ((G.delete X).terminalFrontier U))
    {r : FinitePath G.graph} (hrStart : r.start = q.finish)
    (hrTarget : r.finish ∈ G.target)
    (hrAvoidX : Disjoint r.support X)
    (hrAvoidU : Disjoint r.support ((G.delete X).terminalFrontier U)) :
    (q.support ∩ (G.delete X).terminalFrontier U).Nonempty := by
  obtain ⟨u, huq, huX, huRoof⟩ := hmeet
  let lifted : FinitePath G.graph :=
    q.lift (fun {_ _} h ↦ G.quotient_adj_imp (X := Z) h)
  have huLift : u ∈ lifted.support := by
    simpa [lifted] using huq
  let suffix : FinitePath G.graph := lifted.suffixFrom u huLift
  have hsuffixX : Disjoint suffix.support X := by
    have h := G.suffixFrom_liftQuotientPath_avoids_subset X Z hXZ q u huq huX
    exact h
  let qdel0 : Walk (G.delete X).graph suffix.start suffix.finish :=
    SafeLink.Walk.toDelete G X suffix.walk (Set.disjoint_left.1 hsuffixX)
  let qdel : Walk (G.delete X).graph u suffix.finish :=
    RelationalRoof.castStart (G.delete X).graph.Adj
      (by simpa [suffix]) qdel0
  have hsuffixFinish : suffix.finish = q.finish := by
    calc
      suffix.finish = lifted.finish := lifted.suffixFrom_finish u huLift
      _ = q.finish := rfl
  let rwalk : Walk G.graph suffix.finish r.finish :=
    RelationalRoof.castStart G.graph.Adj
      (hrStart.trans hsuffixFinish.symm) r.walk
  have hrwalkAvoidX : SafeLink.Walk.Avoids rwalk X := by
    intro x hx
    apply Set.disjoint_left.1 hrAvoidX
    change x ∈ r.walk.support
    simpa [rwalk, RelationalRoof.support_castStart] using hx
  let rdel : Walk (G.delete X).graph suffix.finish r.finish :=
    SafeLink.Walk.toDelete G X rwalk hrwalkAvoidX
  let whole : Walk (G.delete X).graph u r.finish := qdel.append rdel
  obtain ⟨z, hzwhole, hzU⟩ :=
    RelationalRoof.roof_meets_walk (G.delete X).graph.Adj
      (G.delete X).target huRoof whole ⟨hrTarget,
        Set.disjoint_left.1 hrAvoidX r.finish_mem_support⟩
  have hzCases : z ∈ qdel.support ∨ z ∈ rdel.support.tail := by
    simpa only [whole, Walk.support_append, List.mem_append] using hzwhole
  rcases hzCases with hzqdel | hzrdel
  · refine ⟨z, ?_, hzU⟩
    have hzSuffix : z ∈ suffix.support := by
      have hqdelSupport : qdel.support = suffix.walk.support := by
        calc
          qdel.support = qdel0.support := by
            exact RelationalRoof.support_castStart (G.delete X).graph.Adj _ qdel0
          _ = suffix.walk.support := by
            exact SafeLink.Walk.support_toDelete G X suffix.walk _
      rw [hqdelSupport] at hzqdel
      exact hzqdel
    have hzLift : z ∈ lifted.support :=
      lifted.suffixFrom_support_subset u huLift hzSuffix
    simpa [lifted] using hzLift
  · exfalso
    apply Set.disjoint_left.1 hrAvoidU
    · have hzrdel' : z ∈ rdel.support := List.mem_of_mem_tail hzrdel
      have hrdelSupport : rdel.support = rwalk.support := by
        simp [rdel, SafeLink.Walk.support_toDelete]
      have hzrwalk : z ∈ rwalk.support := by
        rw [← hrdelSupport]
        exact hzrdel'
      change z ∈ r.walk.support
      simpa [rwalk, RelationalRoof.support_castStart] using hzrwalk
    · exact hzU

/-- Once a finite quotient path meets the terminal frontier of a
deleted-web wave, its last such meeting point supplies the clean splice
used by the arrow operation.  The continuation hypotheses are precisely
what lets the deleted wave's self-roofing property rule out a later contact
with the lifted left warp. -/
theorem exists_arrowCandidate_liftDelete_liftQuotient
    {X Z : Set V} (hXZ : X ⊆ Z)
    {U : Set (G.delete X).DPath} (hU : (G.delete X).IsWave U)
    {W : Set (G.quotient Z).DPath}
    (q : FinitePath (G.quotient Z).graph) (hqW : (.inl q : (G.quotient Z).DPath) ∈ W)
    (hqMeet : (q.support ∩ (G.delete X).terminalFrontier U).Nonempty)
    {r : FinitePath G.graph} (hrStart : r.start = q.finish)
    (hrTarget : r.finish ∈ G.target)
    (hrAvoidX : Disjoint r.support X)
    (hrAvoidU : Disjoint r.support ((G.delete X).terminalFrontier U)) :
    let L := G.liftDeleteFamily X U
    let R := SafeLink.liftQuotientFamily G Z W
    ∃ f : FinitePath G.graph, ∃ hfL : (.inl f : G.DPath) ∈ L,
      ∃ c : G.ArrowCandidate L R f,
        c.path = G.liftQuotientPath Z (.inl q) ∧
        c.path.terminal? = some q.finish := by
  let L := G.liftDeleteFamily X U
  let R := SafeLink.liftQuotientFamily G Z W
  let lifted : FinitePath G.graph :=
    q.lift (fun {_ _} h ↦ G.quotient_adj_imp (X := Z) h)
  have hlifted : G.liftQuotientPath Z (.inl q) = (.inl lifted : G.DPath) := rfl
  have hmeetLifted : lifted.walk.Meets ((G.delete X).terminalFrontier U) := by
    obtain ⟨z, hzq, hzU⟩ := hqMeet
    have hzLifted : z ∈ lifted.support := by
      simpa [lifted] using hzq
    exact ⟨z, hzLifted, hzU⟩
  let last := lifted.walk.lastHit ((G.delete X).terminalFrontier U) hmeetLifted
  obtain ⟨p, hpU, hpTerm⟩ := last.startpoint_mem
  rcases p with p | ray
  · let f : FinitePath G.graph :=
      p.lift (fun {_ _} h ↦ G.delete_adj_imp (X := X) h)
    have hfFinish : f.finish = last.startpoint := by
      exact Option.some.inj hpTerm
    have hfL : (.inl f : G.DPath) ∈ L := by
      refine ⟨(.inl p : (G.delete X).DPath), hpU, ?_⟩
      rfl
    have hlastSupport : last.startpoint ∈ lifted.support :=
      last.support_subset last.walk.start_mem_support
    have hfinishMem : f.finish ∈ (G.liftQuotientPath Z (.inl q)).support := by
      rw [hfFinish, G.support_liftQuotientPath]
      have : last.startpoint ∈ q.support := by
        rw [← DirectedPath.FinitePath.support_lift
          (fun {_ _} h ↦ G.quotient_adj_imp (X := Z) h) q]
        exact hlastSupport
      exact this
    have hfinishLifted : f.finish ∈ lifted.support := by
      rw [hfFinish]
      exact hlastSupport
    have hclean :
        ((G.liftQuotientPath Z (.inl q)).suffixFrom f.finish hfinishMem).support ∩
            G.vertexSet L = {f.finish} := by
      let sf := lifted.suffixData last.startpoint hlastSupport
      let cs := lifted.suffixData f.finish hfinishLifted
      let cswalk : Walk G.graph last.startpoint lifted.finish :=
        RelationalRoof.castStart G.graph.Adj hfFinish cs.walk
      have hsfSuffix : sf.walk.support <:+ lifted.walk.support :=
        lifted.suffixData_support_suffix last.startpoint hlastSupport
      have hsfLast : sf.walk.support = last.walk.support := by
        apply G.suffix_support_eq_of_same_start lifted.walk lifted.isPath
        · exact hsfSuffix
        · exact last.support_suffix
      have hcsSf : cs.walk.support = sf.walk.support := by
        have hcswalkSuffix : cswalk.support <:+ lifted.walk.support := by
          rw [show cswalk.support = cs.walk.support by
            exact RelationalRoof.support_castStart G.graph.Adj _ cs.walk]
          exact lifted.suffixData_support_suffix f.finish hfinishLifted
        have heq : cswalk.support = sf.walk.support :=
          G.suffix_support_eq_of_same_start lifted.walk lifted.isPath
            cswalk sf.walk hcswalkSuffix hsfSuffix
        calc
          cs.walk.support = cswalk.support := by
            exact (RelationalRoof.support_castStart G.graph.Adj _ cs.walk).symm
          _ = sf.walk.support := heq
      ext x
      constructor
      · rintro ⟨hxs, hxL⟩
        have hxs' : x ∈ sf.walk.support := by
          dsimp only [DWeb.liftQuotientPath, DirectedPath.Path.lift] at hxs
          change x ∈ (lifted.suffixData f.finish hfinishLifted).walk.support at hxs
          change x ∈ cs.walk.support at hxs
          rw [hcsSf] at hxs
          exact hxs
        by_cases hxeq : x = last.startpoint
        · simpa [hfFinish, hxeq]
        · have hxLast : x ∈ last.walk.support := hsfLast ▸ hxs'
          have hxTail : x ∈ last.walk.support.tail :=
            (RelationalRoof.mem_support_iff_start_or_mem_tail
              G.graph.Adj last.walk).1 hxLast |>.resolve_left hxeq
          have hxNotFrontier : x ∉ (G.delete X).terminalFrontier U :=
            last.no_mem_after hxTail
          obtain ⟨v, ⟨v₀, hv₀U, rfl⟩, hxv⟩ := hxL
          have hv₀Initial : v₀.initial ∈ (G.delete X).initialSet U :=
            ⟨v₀, hv₀U, rfl⟩
          have hv₀Source := hU.2.1 hv₀Initial
          have hxNotX : x ∉ X :=
            Set.disjoint_left.1 (G.liftDeletePath_avoids X v₀ hv₀Source.2)
              hxv
          have hxv₀ : x ∈ v₀.support := by
            simpa using hxv
          have hxRoof : x ∈ (G.delete X).roof
              ((G.delete X).terminalFrontier U) :=
            (DWeb.IsWave.self_roofing (Γ := G.delete X) hU)
              ⟨v₀, hv₀U, hxv₀⟩
          have hxq : x ∈ q.support := by
            have hxLift : x ∈ lifted.support := hsfSuffix.subset hxs'
            rw [← DirectedPath.FinitePath.support_lift
              (fun {_ _} h ↦ G.quotient_adj_imp (X := Z) h) q]
            exact hxLift
          have hxLifted : x ∈ lifted.support := by
            rw [DirectedPath.FinitePath.support_lift]
            exact hxq
          let sx : FinitePath G.graph := lifted.suffixFrom x hxLifted
          have hsxAvoidX : Disjoint sx.support X := by
            exact G.suffixFrom_liftQuotientPath_avoids_subset X Z hXZ q x hxq hxNotX
          let sxdel₀ : Walk (G.delete X).graph sx.start sx.finish :=
            SafeLink.Walk.toDelete G X sx.walk (Set.disjoint_left.1 hsxAvoidX)
          let sxdel : Walk (G.delete X).graph x sx.finish :=
            RelationalRoof.castStart (G.delete X).graph.Adj
              (by simpa [sx]) sxdel₀
          have hsxFinish : sx.finish = q.finish := by
            calc
              sx.finish = lifted.finish := lifted.suffixFrom_finish x hxLifted
              _ = q.finish := rfl
          let rwalk : Walk G.graph sx.finish r.finish :=
            RelationalRoof.castStart G.graph.Adj
              (hrStart.trans hsxFinish.symm) r.walk
          have hrwalkAvoidX : SafeLink.Walk.Avoids rwalk X := by
            intro y hyr
            apply Set.disjoint_left.1 hrAvoidX
            change y ∈ r.walk.support
            simpa [rwalk, RelationalRoof.support_castStart] using hyr
          let rdel : Walk (G.delete X).graph sx.finish r.finish :=
            SafeLink.Walk.toDelete G X rwalk hrwalkAvoidX
          let whole : Walk (G.delete X).graph x r.finish := sxdel.append rdel
          obtain ⟨z, hzwhole, hzU⟩ :=
            RelationalRoof.roof_meets_walk (G.delete X).graph.Adj
              (G.delete X).target hxRoof whole ⟨hrTarget,
                Set.disjoint_left.1 hrAvoidX r.finish_mem_support⟩
          have hzCases : z ∈ sxdel.support ∨ z ∈ rdel.support.tail := by
            simpa only [whole, Walk.support_append, List.mem_append] using hzwhole
          rcases hzCases with hzsx | hzr
          · have hzsx' : z ∈ sx.walk.support := by
              have hsupport : sxdel.support = sx.walk.support := by
                calc
                  sxdel.support = sxdel₀.support :=
                    RelationalRoof.support_castStart (G.delete X).graph.Adj _ sxdel₀
                  _ = sx.walk.support := SafeLink.Walk.support_toDelete G X sx.walk _
              rw [hsupport] at hzsx
              exact hzsx
            have hsxSuffix : sx.walk.support <:+ lifted.walk.support :=
              (lifted.walk.lastHit ({x} : Set V)
                ⟨x, hxLifted, Set.mem_singleton x⟩).support_suffix
            have hsxLast : sx.walk.support <:+ last.walk.support := by
              rcases List.suffix_total hsxSuffix last.support_suffix with h | h
              · exact h
              · have heq : last.walk.support = sx.walk.support := by
                  apply List.Nodup.eq_of_head_mem_of_suffix
                    (hne := sx.walk.support_ne_nil) h
                  · rw [sx.walk.head_support]
                    have hsxStart : sx.start = x := by simp [sx]
                    rw [hsxStart]
                    exact hxLast
                  · exact (hsxSuffix.nodup lifted.isPath)
                have hhead := congrArg List.head? heq
                have : last.startpoint = x := by
                  rw [List.head?_eq_head last.walk.support_ne_nil,
                    last.walk.head_support,
                    List.head?_eq_head sx.walk.support_ne_nil,
                    sx.walk.head_support] at hhead
                  have hsxStart : sx.start = x := by simp [sx]
                  rw [hsxStart] at hhead
                  exact Option.some.inj hhead
                exact (hxeq this.symm).elim
            have hzLast : z ∈ last.walk.support := hsxLast.subset hzsx'
            have hzNe : z ≠ last.startpoint := by
              intro hzeq
              subst z
              have heq : sx.walk.support = last.walk.support := by
                apply List.Nodup.eq_of_head_mem_of_suffix
                  (hne := last.walk.support_ne_nil) hsxLast
                · rw [last.walk.head_support]
                  exact hzsx'
                · exact last.isPath lifted.isPath
              have hhead := congrArg List.head? heq
              have : x = last.startpoint := by
                rw [List.head?_eq_head sx.walk.support_ne_nil,
                  sx.walk.head_support,
                  List.head?_eq_head last.walk.support_ne_nil,
                  last.walk.head_support] at hhead
                have hsxStart : sx.start = x := by simp [sx]
                rw [hsxStart] at hhead
                exact Option.some.inj hhead
              exact hxeq this
            exact (last.no_mem_after
              ((RelationalRoof.mem_support_iff_start_or_mem_tail
                G.graph.Adj last.walk).1 hzLast |>.resolve_left hzNe)) hzU |>.elim
          · exfalso
            apply Set.disjoint_left.1 hrAvoidU
            · have hzr' : z ∈ rdel.support := List.mem_of_mem_tail hzr
              have hrdelSupport : rdel.support = rwalk.support :=
                SafeLink.Walk.support_toDelete G X rwalk _
              have hzrwalk : z ∈ rwalk.support := by
                rw [← hrdelSupport]
                exact hzr'
              change z ∈ r.walk.support
              simpa [rwalk, RelationalRoof.support_castStart] using hzrwalk
            · exact hzU
      · intro hx
        have hxeq : x = f.finish := by simpa using hx
        subst x
        refine ⟨?_, ?_⟩
        · dsimp only [DWeb.liftQuotientPath, DirectedPath.Path.lift]
          change f.finish ∈ (lifted.suffixData f.finish hfinishLifted).walk.support
          exact (lifted.suffixData f.finish hfinishLifted).walk.start_mem_support
        · exact ⟨.inl f, hfL, f.finish_mem_support⟩
    let c : G.ArrowCandidate L R f :=
      { path := G.liftQuotientPath Z (.inl q)
        mem_path := ⟨(.inl q : (G.quotient Z).DPath), hqW, rfl⟩
        finish_mem := hfinishMem
        clean := hclean }
    refine ⟨f, hfL, c, rfl, ?_⟩
    rfl
  · simp at hpTerm

/-- The essential-frontier part of source Lemma 3.15.  This is the exact
specialization of the general arrow lemma to a left wave in `G - X` and a
right wave in `G / Z`. -/
theorem essential_union_subset_terminalFrontier_arrow_delete_quotient
    {X Z : Set V} (hXZ : X ⊆ Z)
    (hNoEnter : G.NoEdgeEnters G.source)
    (hSourceZ : Disjoint G.source Z)
    {U : Set (G.delete X).DPath} (hU : (G.delete X).IsWave U)
    {W : Set (G.quotient Z).DPath} (hW : (G.quotient Z).IsWave W)
    (hmeet : ∀ q ∈ W, ∃ u ∈ q.support,
      u ∉ X ∧ u ∈ (G.delete X).roof ((G.delete X).terminalFrontier U)) :
    let L := G.liftDeleteFamily X U
    let R := SafeLink.liftQuotientFamily G Z W
    G.essential (G.terminalFrontier L ∪ G.terminalFrontier R) ⊆
      G.terminalFrontier (G.arrow L R) := by
  let L := G.liftDeleteFamily X U
  let R := SafeLink.liftQuotientFamily G Z W
  have hRwarp : G.IsWarp R := SafeLink.isWarp_liftQuotientFamily G Z hW.1
  have hRself : G.vertexSet R ⊆ G.roof (G.terminalFrontier R) := by
    rw [SafeLink.vertexSet_liftQuotientFamily,
      SafeLink.terminalFrontier_liftQuotientFamily]
    exact SafeLink.quotientWave_vertexSet_subset_original_roof
      G hNoEnter hSourceZ hW
  have hEssZ : G.essential Z ⊆ G.roof (G.terminalFrontier R) := by
    rw [SafeLink.terminalFrontier_liftQuotientFamily]
    exact G.essential_subset_original_roof_of_quotient_wave
      hNoEnter hSourceZ hW
  have hRoofZ : G.roof Z ⊆ G.roof (G.terminalFrontier R) := by
    rw [← G.roof_essential Z]
    exact G.roof_cut hEssZ
  dsimp only
  intro z hzEss
  let A := G.terminalFrontier L
  let B := G.terminalFrontier R
  change z ∈ A ∪ B ∧ z ∉ G.roof ((A ∪ B) \ {z}) at hzEss
  have of_mem_A : z ∈ A → z ∈ G.terminalFrontier (G.arrow L R) := by
    intro hzA
    obtain ⟨p, hpL, hpTerm⟩ := hzA
    rcases p with f | ray
    · have hfFinish : f.finish = z := Option.some.inj hpTerm
      rcases G.arrowPath_finite_cases L R f hpL with heq | ⟨c, _heq⟩
      · exact ⟨G.arrowPath L R ⟨.inl f, hpL⟩,
          ⟨⟨.inl f, hpL⟩, rfl⟩, by simpa [heq] using hpTerm⟩
      · by_cases hzB : z ∈ B
        · obtain ⟨q, hqR, hqTerm⟩ := hzB
          have hcq : c.path = q := by
            by_contra hne
            exact Set.disjoint_left.1 (hRwarp c.mem_path hqR hne)
              (hfFinish ▸ c.finish_mem) (G.terminal_mem_support hqTerm)
          have hcTerm : c.path.terminal? = some z := hcq ▸ hqTerm
          exact ⟨G.arrowPath L R ⟨.inl f, hpL⟩,
            ⟨⟨.inl f, hpL⟩, rfl⟩,
            G.terminal_arrowPath_of_candidate hRwarp hpL c hcTerm⟩
        · exfalso
          have hzRoofB : z ∈ G.roof B :=
            hRself ⟨c.path, c.mem_path, hfFinish ▸ c.finish_mem⟩
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
    · obtain ⟨qLift, hqLiftR, hqLiftTerm⟩ := hzB
      obtain ⟨q, hqW, hqEq⟩ := hqLiftR
      subst qLift
      rcases q with q | ray
      · have hqFinish : q.finish = z := Option.some.inj hqLiftTerm
        obtain ⟨r, hrTarget, hrAvoid⟩ :=
          (G.not_mem_roof_iff ((A ∪ B) \ {z}) z).1 hzEss.2
        have hrStart : r.start = q.finish := hrTarget.1.trans hqFinish.symm
        have hrAvoidA : Disjoint r.support A := by
          apply Set.disjoint_left.2
          intro x hxr hxA
          apply Set.disjoint_left.1 hrAvoid hxr
          exact ⟨Or.inl hxA, by
            intro hxz
            have : x = z := by simpa using hxz
            exact hzA (this ▸ hxA)⟩
        have hzNotX : z ∉ X := by
          intro hzX
          have hqFinishX : q.finish ∈ X := by
            rw [hqFinish]
            exact hzX
          obtain ⟨u, huq, huX, _huRoof⟩ := hmeet (.inl q) hqW
          rcases G.quotientPath_support_initial_or_avoids Z (.inl q)
              q.finish_mem_support with hfinishInit | hfinishAvoid
          · change q.finish = q.start at hfinishInit
            have huEq : u = q.start := by
              by_contra hne
              apply (G.quotient Z).start_not_mem_suffixFromAux_of_ne q u huq hne
              rw [← hfinishInit]
              exact (q.suffixFromAux u huq).finish_mem_support
            exact huX (huEq ▸ (hfinishInit ▸ hqFinishX))
          · exact hfinishAvoid.2 (hXZ hqFinishX)
        have hrAvoidX : Disjoint r.support X := by
          apply Set.disjoint_left.2
          intro x hxr hxX
          have hxRoofB : x ∈ G.roof B :=
            hRoofZ (G.subset_roof Z (hXZ hxX))
          let rx := r.suffixFromAux x hxr
          have hrxTarget : G.IsTargetPathFrom x rx := ⟨rfl, hrTarget.2⟩
          obtain ⟨b, hbrx, hbB⟩ := hxRoofB rx hrxTarget
          have hbNe : b ≠ z := by
            intro hbeq
            subst b
            have hxNeStart : x ≠ r.start := by
              intro hxstart
              exact hzNotX (hrTarget.1.symm ▸ hxstart ▸ hxX)
            exact (G.start_not_mem_suffixFromAux_of_ne r x hxr hxNeStart)
              (hrTarget.1 ▸ hbrx)
          exact Set.disjoint_left.1 hrAvoid
            (r.suffixFromAux_support_subset x hxr hbrx)
            ⟨Or.inr hbB, by simpa using hbNe⟩
        have hqMeet := G.quotientFinitePath_meets_deleteWave_terminal
          hXZ hU q (hmeet (.inl q) hqW) hrStart hrTarget.2 hrAvoidX
          (by simpa [A, L] using hrAvoidA)
        obtain ⟨f, hfL, c, hcPath, hcTerm⟩ :=
          G.exists_arrowCandidate_liftDelete_liftQuotient hXZ hU q hqW
            hqMeet hrStart hrTarget.2 hrAvoidX (by simpa [A, L] using hrAvoidA)
        have hcTermZ : c.path.terminal? = some z := by
          simpa [hqFinish] using hcTerm
        exact ⟨G.arrowPath L R ⟨.inl f, hfL⟩,
          ⟨⟨.inl f, hfL⟩, rfl⟩,
          G.terminal_arrowPath_of_candidate hRwarp hfL c hcTermZ⟩
      · simp at hqLiftTerm

/-- Aharoni--Berger Lemma 3.15, in the retained-meeting form required by
the safe-link construction. -/
theorem isWave_arrow_delete_quotient
    {X Z : Set V} (hXZ : X ⊆ Z)
    (hNoEnter : G.NoEdgeEnters G.source)
    (hSourceZ : Disjoint G.source Z)
    {U : Set (G.delete X).DPath} (hU : (G.delete X).IsWave U)
    {W : Set (G.quotient Z).DPath} (hW : (G.quotient Z).IsWave W)
    (hmeet : ∀ q ∈ W, ∃ u ∈ q.support,
      u ∉ X ∧ u ∈ (G.delete X).roof ((G.delete X).terminalFrontier U)) :
    G.IsWave (G.arrow (G.liftDeleteFamily X U)
      (SafeLink.liftQuotientFamily G Z W)) := by
  let L := G.liftDeleteFamily X U
  let R := SafeLink.liftQuotientFamily G Z W
  have hLwarp : G.IsWarp L := hU.1.liftDeleteFamily
  have hLinitial : G.initialSet L ⊆ G.source :=
    hU.liftDeleteFamily_structural.2
  have hRwarp : G.IsWarp R := SafeLink.isWarp_liftQuotientFamily G Z hW.1
  have hEss := G.essential_union_subset_terminalFrontier_arrow_delete_quotient
    hXZ hNoEnter hSourceZ hU hW hmeet
  have hterminal := G.terminalFrontier_arrow_subset_union L R
  have hroofEq : G.roof (G.terminalFrontier (G.arrow L R)) =
      G.roof (G.terminalFrontier L ∪ G.terminalFrontier R) := by
    have hEssEq := RelationalRoof.essential_sandwich
      G.graph.Adj G.target hEss hterminal
    calc
      G.roof (G.terminalFrontier (G.arrow L R)) =
          G.roof (G.essential (G.terminalFrontier (G.arrow L R))) :=
        (G.roof_essential _).symm
      _ = G.roof (G.essential
          (G.terminalFrontier L ∪ G.terminalFrontier R)) :=
        congrArg G.roof hEssEq
      _ = G.roof (G.terminalFrontier L ∪ G.terminalFrontier R) :=
        G.roof_essential _
  have hEssZ : G.essential Z ⊆ G.roof (G.terminalFrontier R) := by
    rw [SafeLink.terminalFrontier_liftQuotientFamily]
    exact G.essential_subset_original_roof_of_quotient_wave
      hNoEnter hSourceZ hW
  have hRoofZ : G.roof Z ⊆ G.roof (G.terminalFrontier R) := by
    rw [← G.roof_essential Z]
    exact G.roof_cut hEssZ
  have hSourceRoof : G.source ⊆
      G.roof (G.terminalFrontier L ∪ G.terminalFrontier R) := by
    intro a ha p hp
    by_cases hpX : G.Meets p X
    · obtain ⟨x, hxp, hxX⟩ := hpX
      have hxRoofR := hRoofZ (G.subset_roof Z (hXZ hxX))
      let px := p.suffixFromAux x hxp
      have hpxTarget : G.IsTargetPathFrom x px := ⟨rfl, hp.2⟩
      obtain ⟨z, hzpx, hzR⟩ := hxRoofR px hpxTarget
      exact ⟨z, p.suffixFromAux_support_subset x hxp hzpx, Or.inr hzR⟩
    · have hpAvoidX : SafeLink.Walk.Avoids p.walk X := by
        intro x hxp hxX
        exact hpX ⟨x, hxp, hxX⟩
      let pd := SafeLink.FinitePath.toDelete G X p hpAvoidX
      have haNotX : a ∉ X := by
        intro haX
        exact Set.disjoint_left.1 hSourceZ ha (hXZ haX)
      have hpdTarget : (G.delete X).IsTargetPathFrom a pd := by
        exact ⟨hp.1, hp.2, hpAvoidX p.finish p.finish_mem_support⟩
      obtain ⟨z, hzpd, hzU⟩ := hU.2.2 ⟨ha, haNotX⟩ pd hpdTarget
      exact ⟨z, by simpa [pd] using hzpd, Or.inl (by simpa [L] using hzU)⟩
  refine ⟨G.isWarp_arrow hLwarp hRwarp, ?_, ?_⟩
  · rw [← G.initialSet_eq_of_forwardExtension (G.forwardExtension_arrow L R)]
    exact hLinitial
  · rw [hroofEq]
    exact hSourceRoof

/-- The general arrow preserves the full roof of its left deleted wave.
The proof is the source-roof argument from Lemma 3.15 with an arbitrary
roofed starting vertex in place of a source vertex. -/
theorem roof_delete_subset_arrow_delete_quotient
    {X Z : Set V} (hXZ : X ⊆ Z)
    (hNoEnter : G.NoEdgeEnters G.source)
    (hSourceZ : Disjoint G.source Z)
    {U : Set (G.delete X).DPath} (hU : (G.delete X).IsWave U)
    {W : Set (G.quotient Z).DPath} (hW : (G.quotient Z).IsWave W)
    (hmeet : ∀ q ∈ W, ∃ u ∈ q.support,
      u ∉ X ∧ u ∈ (G.delete X).roof ((G.delete X).terminalFrontier U)) :
    (G.delete X).roof ((G.delete X).terminalFrontier U) ⊆
      G.roof (G.terminalFrontier (G.arrow (G.liftDeleteFamily X U)
        (SafeLink.liftQuotientFamily G Z W))) := by
  let L := G.liftDeleteFamily X U
  let R := SafeLink.liftQuotientFamily G Z W
  have hEss := G.essential_union_subset_terminalFrontier_arrow_delete_quotient
    hXZ hNoEnter hSourceZ hU hW hmeet
  have hterminal := G.terminalFrontier_arrow_subset_union L R
  have hroofEq : G.roof (G.terminalFrontier (G.arrow L R)) =
      G.roof (G.terminalFrontier L ∪ G.terminalFrontier R) := by
    have hEssEq := RelationalRoof.essential_sandwich
      G.graph.Adj G.target hEss hterminal
    calc
      G.roof (G.terminalFrontier (G.arrow L R)) =
          G.roof (G.essential (G.terminalFrontier (G.arrow L R))) :=
        (G.roof_essential _).symm
      _ = G.roof (G.essential
          (G.terminalFrontier L ∪ G.terminalFrontier R)) :=
        congrArg G.roof hEssEq
      _ = G.roof (G.terminalFrontier L ∪ G.terminalFrontier R) :=
        G.roof_essential _
  have hEssZ : G.essential Z ⊆ G.roof (G.terminalFrontier R) := by
    rw [SafeLink.terminalFrontier_liftQuotientFamily]
    exact G.essential_subset_original_roof_of_quotient_wave
      hNoEnter hSourceZ hW
  have hRoofZ : G.roof Z ⊆ G.roof (G.terminalFrontier R) := by
    rw [← G.roof_essential Z]
    exact G.roof_cut hEssZ
  rw [hroofEq]
  intro y hy p hp
  by_cases hpX : G.Meets p X
  · obtain ⟨x, hxp, hxX⟩ := hpX
    have hxRoofR := hRoofZ (G.subset_roof Z (hXZ hxX))
    let px := p.suffixFromAux x hxp
    have hpxTarget : G.IsTargetPathFrom x px := ⟨rfl, hp.2⟩
    obtain ⟨z, hzpx, hzR⟩ := hxRoofR px hpxTarget
    exact ⟨z, p.suffixFromAux_support_subset x hxp hzpx, Or.inr hzR⟩
  · have hpAvoidX : SafeLink.Walk.Avoids p.walk X := by
      intro x hxp hxX
      exact hpX ⟨x, hxp, hxX⟩
    let pd := SafeLink.FinitePath.toDelete G X p hpAvoidX
    have hpdTarget : (G.delete X).IsTargetPathFrom y pd := by
      exact ⟨hp.1, hp.2, hpAvoidX p.finish p.finish_mem_support⟩
    obtain ⟨z, hzpd, hzU⟩ := hy pd hpdTarget
    exact ⟨z, by simpa [pd] using hzpd, Or.inl (by simpa [L] using hzU)⟩

end DWeb

end Erdos599
