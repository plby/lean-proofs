/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeEndpointNonrealResolution

/-!
# Finite skeleton resolution in the endpoint-pruned graph

Reuse the finite path induction with the actual endpoint nonreal-edge
constructor. The early branch reaches a genuine full frontier terminal.
The connector branch retains the unprocessed suffix, all old full terminals,
and every old edge outside the original skeleton. Accounting and incoming
refinement are composed for the same successive actual blueprints.
-/

noncomputable section

namespace Erdos599.Blueprint.ColouredSafeEndpointBlueprint

open Set Cardinal Order DirectedPath Ladder
open _root_.Erdos599.Alternating
open _root_.Erdos599.ColouredSafeLocalTransactionRealLedger
open _root_.Erdos599.ColouredSafeAugmentedRealReach

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}

/-- Resolve every nonreal edge on a finite simple old path. If the frontier
is not reached early, every old edge outside that path survives. -/
theorem exists_finiteSkeleton_resolution_of_invariant
    (C : LinkageBlueprint.ClubStageGeometry Gamma Y kappa (succ kappa))
    (Inv : Set (web C).DPath → Prop)
    {a : Stage (succ kappa)}
    {W : Set (web C).DPath}
    (hW : IsBlueprint C a W)
    (hInv : Inv W)
    (hresolve : ∀ {W : Set (web C).DPath}, IsBlueprint C a W → Inv W →
      ∀ {s t : V}, s ≠ t → (s, t) ∈ familyEdges W → ¬Gamma.graph.Adj s t →
      ∃ U : Set (web C).DPath, IsBlueprint C a U ∧ Inv U ∧
        RealAdvance Gamma (web C) W U (C.ladder.frontier a) ∧
        ((∃ z ∈ C.ladder.frontier a,
            z ∈ (web C).terminalFrontier U ∧ RealReach Gamma (web C) U s z ∧
            FullAccount Gamma (web C) W U {z}) ∨
          (RealReach Gamma (web C) U s t ∧ FullAccount Gamma (web C) W U {t} ∧
            familyEdges W \ {(s, t)} ⊆ familyEdges U ∧
            (web C).terminalFrontier W ⊆ (web C).terminalFrontier U)) ∧
        (∀ x, IsRealTerminal (Gamma := web C) Gamma.graph.Adj W x → x ≠ s →
          IsRealTerminal (Gamma := web C) Gamma.graph.Adj U x) ∧
        SourcePredecessorRefines Gamma (web C) W U)
    (p : FinitePath (web C).graph)
    (hpV : p.support ⊆ (web C).vertexSet W)
    (hpE : p.edgeSet ⊆ familyEdges W) :
    ∃ U : Set (web C).DPath,
      IsBlueprint C a U ∧ Inv U ∧
      RealAdvance Gamma (web C) W U (C.ladder.frontier a) ∧
      (((∃ z ∈ C.ladder.frontier a,
          z ∈ (web C).terminalFrontier U ∧
          RealReach Gamma (web C) U p.start z ∧ FullAccount Gamma (web C) W U {z}) ∧
          ∀ x, IsRealTerminal (Gamma := web C)
              Gamma.graph.Adj W x →
            IsRealTerminal (Gamma := web C)
                Gamma.graph.Adj U x ∨ RealReaches Gamma (web C) U x (C.ladder.frontier a)) ∨
        (RealReach Gamma (web C) U p.start p.finish ∧ FullAccount Gamma (web C) W U {p.finish} ∧
          familyEdges W \ p.edgeSet ⊆ familyEdges U ∧
          (web C).terminalFrontier W ⊆
            (web C).terminalFrontier U)) ∧
      (∀ x, IsRealTerminal (Gamma := web C)
          Gamma.graph.Adj W x →
        IsRealTerminal (Gamma := web C)
            Gamma.graph.Adj U x ∨
          RealReaches Gamma (web C) U x (C.ladder.frontier a ∪ {p.finish})) ∧
      SourcePredecessorRefines Gamma (web C) W U := by
  let D := web C
  let T := C.ladder.frontier a
  have hwalk : ∀ {s t : V} (q : Walk D.graph s t), q.IsPath →
      ∀ (W : Set D.DPath), IsBlueprint C a W → Inv W →
      (∀ x ∈ q.support, x ∈ D.vertexSet W) → q.edgeSet ⊆ familyEdges W →
      ∃ U : Set D.DPath, IsBlueprint C a U ∧ Inv U ∧
        RealAdvance Gamma (web C) W U T ∧
        (((∃ z ∈ T, z ∈ D.terminalFrontier U ∧
            RealReach Gamma (web C) U s z ∧ FullAccount Gamma (web C) W U {z}) ∧
            ∀ x, IsRealTerminal (Gamma := D) Gamma.graph.Adj W x →
              IsRealTerminal (Gamma := D) Gamma.graph.Adj U x ∨ RealReaches Gamma (web C) U x T) ∨
          (RealReach Gamma (web C) U s t ∧ FullAccount Gamma (web C) W U {t} ∧
            familyEdges W \ q.edgeSet ⊆ familyEdges U ∧
            D.terminalFrontier W ⊆ D.terminalFrontier U)) ∧
        (∀ x, IsRealTerminal (Gamma := D) Gamma.graph.Adj W x →
          IsRealTerminal (Gamma := D) Gamma.graph.Adj U x ∨
            RealReaches Gamma (web C) U x (T ∪ {t})) ∧
        SourcePredecessorRefines Gamma (web C) W U := by
    intro s t q
    induction q with
    | @nil s =>
        intro _ W hW hInv hV _
        exact ⟨W, hW, hInv, RealAdvance.refl W T,
          Or.inr ⟨RealReach.refl (hV s (by simp)), FullAccount.refl hW.isWarp {s},
            Set.sdiff_subset, Subset.rfl⟩,
          (fun _ hx ↦ Or.inl hx), SourcePredecessorRefines.refl W⟩
    | @cons s v t h_adj q ih =>
        intro hpath W hW hInv hV hE
        have hnodup : s ∉ q.support ∧ q.support.Nodup := by
          simpa only [Walk.IsPath, Walk.support_cons, List.nodup_cons] using hpath
        have hqPath : q.IsPath := hnodup.2
        have hsv : s ≠ v := by
          intro heq
          exact hnodup.1 (heq ▸ q.start_mem_support)
        have hhead : (s, v) ∈ familyEdges W := hE (by simp)
        have hqV : ∀ x ∈ q.support, x ∈ D.vertexSet W :=
          fun x hx ↦ hV x (List.mem_cons_of_mem s hx)
        have hqE : q.edgeSet ⊆ familyEdges W := fun e he ↦ hE (by simp [he])
        by_cases hreal : Gamma.graph.Adj s v
        · obtain ⟨U, hU, hInvU, hadv, hresult, haccount, hPred⟩ :=
            ih hqPath W hW hInv hqV hqE
          have hfirst : RealReach Gamma (web C) U s v :=
            ⟨hadv.vertices (hV s (by simp)),
              .single (hadv.edges ⟨hhead, hreal⟩)⟩
          refine ⟨U, hU, hInvU, hadv, ?_, haccount, hPred⟩
          rcases hresult with hearly | ⟨hend, hAccountEnd, hretained, htermRetained⟩
          · obtain ⟨z, hz, hzTerminal, hvz, hAccountEnd⟩ := hearly.1
            exact Or.inl ⟨⟨z, hz, hzTerminal, hfirst.trans hvz, hAccountEnd⟩, hearly.2⟩
          · refine Or.inr ⟨hfirst.trans hend, hAccountEnd, ?_, htermRetained⟩
            intro e he
            exact hretained ⟨he.1, fun heq ↦ he.2 (by simp [heq])⟩
        · obtain ⟨U, hU, hInvU, hadv, hstep, hterms, hPred⟩ :=
            hresolve hW hInv hsv hhead hreal
          rcases hstep with ⟨z, hz, hzTerminal, hsz, hAccountStep⟩ |
            ⟨hsvReal, hAccountStep, hretained, htermRetained⟩
          · have hearly : RealReaches Gamma (web C) U s T := ⟨z, hz, hsz⟩
            have haccountT : ∀ x,
                IsRealTerminal (Gamma := D) Gamma.graph.Adj W x →
                IsRealTerminal (Gamma := D) Gamma.graph.Adj U x ∨
                  RealReaches Gamma (web C) U x T := by
              intro x hx
              by_cases hxs : x = s
              · exact Or.inr (hxs ▸ hearly)
              · exact Or.inl (hterms x hx hxs)
            refine ⟨U, hU, hInvU, hadv,
              Or.inl ⟨⟨z, hz, hzTerminal, hsz, hAccountStep⟩, haccountT⟩,
              ?_, hPred⟩
            intro x hx
            exact (haccountT x hx).imp_right
              (fun h ↦ h.target_mono Set.subset_union_left)
          · have hqEU : q.edgeSet ⊆ familyEdges U := by
              intro e he
              refine hretained ⟨hqE he, ?_⟩
              intro heq
              have hesv : e = (s, v) := Set.mem_singleton_iff.mp heq
              have hsQ : s ∈ q.support := by
                have htail := Walk.edgeSet_subset_support_prod q he
                simpa only [hesv] using htail.1
              exact hnodup.1 hsQ
            obtain ⟨U', hU', hInvU', hadv', hresult, haccount, hPred'⟩ :=
              ih hqPath U hU hInvU (fun x hx ↦ hadv.vertices (hqV x hx)) hqEU
            have hfirst : RealReach Gamma (web C) U' s v := hsvReal.mono hadv'.vertices hadv'.edges
            have hfinal : ((∃ z ∈ T, z ∈ D.terminalFrontier U' ∧
                RealReach Gamma (web C) U' s z ∧ FullAccount Gamma (web C) W U' {z}) ∧
                ∀ x, IsRealTerminal (Gamma := D) Gamma.graph.Adj W x →
                  IsRealTerminal (Gamma := D) Gamma.graph.Adj U' x ∨
                    RealReaches Gamma (web C) U' x T) ∨
                (RealReach Gamma (web C) U' s t ∧ FullAccount Gamma (web C) W U' {t} ∧
                  familyEdges W \ (Walk.cons h_adj q).edgeSet ⊆ familyEdges U' ∧
                  D.terminalFrontier W ⊆ D.terminalFrontier U') := by
              rcases hresult with hearly | ⟨hend, hAccountEnd, hremaining, htermRemaining⟩
              · obtain ⟨z, hz, hzTerminal, hvz, hAccountEnd⟩ := hearly.1
                have hsource : RealReaches Gamma (web C) U' s T := ⟨z, hz, hfirst.trans hvz⟩
                have hAccountFinal := hAccountStep.trans_singleton hU.isWarp hAccountEnd
                  hadv.vertices hadv'.vertices hadv'.edges hvz
                refine Or.inl ⟨⟨z, hz, hzTerminal, hfirst.trans hvz, hAccountFinal⟩, ?_⟩
                intro x hx
                by_cases hxs : x = s
                · exact Or.inr (hxs ▸ hsource)
                · exact hearly.2 x (hterms x hx hxs)
              · have hAccountFinal := hAccountStep.trans_singleton hU.isWarp hAccountEnd
                  hadv.vertices hadv'.vertices hadv'.edges hend
                refine Or.inr ⟨hfirst.trans hend, hAccountFinal, ?_,
                  htermRetained.trans htermRemaining⟩
                intro e he
                apply hremaining
                refine ⟨hretained ⟨he.1, ?_⟩, ?_⟩
                · intro hcut
                  exact he.2 (Or.inl hcut)
                · intro htail
                  exact he.2 (Or.inr htail)
            refine ⟨U', hU', hInvU', hadv.trans hadv', hfinal, ?_,
              hPred.trans hPred' hadv.vertices hadv'.vertices hadv'.edges⟩
            intro x hx
            by_cases hxs : x = s
            · subst x
              right
              rcases hfinal with hearly | ⟨hend, _⟩
              · obtain ⟨z, hz, _hzTerminal, hsz, _⟩ := hearly.1
                exact ⟨z, Or.inl hz, hsz⟩
              · exact ⟨t, Or.inr (Set.mem_singleton t), hend⟩
            · exact haccount x (hterms x hx hxs)
  exact hwalk p.walk p.isPath W hW hInv hpV hpE

/-- The original endpoint skeleton interface is recovered with the
constant invariant and the existing actual edge resolver. -/
theorem exists_finiteSkeleton_resolution
    (C : LinkageBlueprint.ClubStageGeometry Gamma Y kappa (succ kappa))
    {a : Stage (succ kappa)} (ha : a ∈ C.club)
    {W : Set (web C).DPath}
    (hW : IsBlueprint C a W)
    (p : FinitePath (web C).graph)
    (hpV : p.support ⊆ (web C).vertexSet W)
    (hpE : p.edgeSet ⊆ familyEdges W) :
    ∃ U : Set (web C).DPath,
      IsBlueprint C a U ∧
      RealAdvance Gamma (web C) W U (C.ladder.frontier a) ∧
      (((∃ z ∈ C.ladder.frontier a,
          z ∈ (web C).terminalFrontier U ∧
          RealReach Gamma (web C) U p.start z ∧ FullAccount Gamma (web C) W U {z}) ∧
          ∀ x, IsRealTerminal (Gamma := web C)
              Gamma.graph.Adj W x →
            IsRealTerminal (Gamma := web C)
                Gamma.graph.Adj U x ∨ RealReaches Gamma (web C) U x (C.ladder.frontier a)) ∨
        (RealReach Gamma (web C) U p.start p.finish ∧ FullAccount Gamma (web C) W U {p.finish} ∧
          familyEdges W \ p.edgeSet ⊆ familyEdges U ∧
          (web C).terminalFrontier W ⊆ (web C).terminalFrontier U)) ∧
      (∀ x, IsRealTerminal (Gamma := web C)
          Gamma.graph.Adj W x →
        IsRealTerminal (Gamma := web C)
            Gamma.graph.Adj U x ∨
          RealReaches Gamma (web C) U x (C.ladder.frontier a ∪ {p.finish})) ∧
      SourcePredecessorRefines Gamma (web C) W U := by
  obtain ⟨U, hU, _hInv, hrest⟩ :=
    exists_finiteSkeleton_resolution_of_invariant C (fun _ ↦ True) hW trivial
      (by
        intro W hW _ s t hne he hn
        obtain ⟨U, hU, hrest⟩ := hW.exists_nonrealEdge_resolution ha hne he hn
        exact ⟨U, hU, trivial, hrest⟩) p hpV hpE
  exact ⟨U, hU, hrest⟩

#print axioms exists_finiteSkeleton_resolution_of_invariant
#print axioms exists_finiteSkeleton_resolution

end Erdos599.Blueprint.ColouredSafeEndpointBlueprint
