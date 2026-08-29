/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeFiniteRoofCutTransaction
import ErdosProblems.Erdos599.ColouredSafeHammockInsideClosure
import ErdosProblems.Erdos599.ColouredSafeRealReach

/-!
# Finitely resolving an actual native forward skeleton

Each nonreal edge is replaced by the actual finite roof-cut transaction.
The real source component either reaches the stage frontier, ending the
recursion, or reaches the represented head and retains the literal suffix.
The recursion is on a finite simple path, with no infinite switching limit.

The terminal ledger is compositional: an old real terminal either remains
pending or is linked to the frontier or the final skeleton endpoint. It
does not incorrectly claim that only the first scheduled source can lose
real-terminal status during a succession of local transactions.
-/

noncomputable section

namespace Erdos599.Blueprint.ColouredSafeShortcutGraph

open Set Cardinal Order DirectedPath Alternating Ladder
open ColouredSafeAmbientOccurrence ColouredSafeHammock ColouredSafeHammockOmegaClosure
open ColouredSafeLocalTransactionRealLedger

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}

/-- Local finite resolution with its large contained hammock supplied by
actual successor-cap closure, rather than an extra route-filter premise. -/
theorem exists_nonrealEdge_resolution
    (C : LinkageBlueprint.ClubStageGeometry Gamma Y kappa (succ kappa))
    {a : Stage (succ kappa)} (ha : a ∈ C.club)
    {Z persistent : Set V}
    (hZ : ClosedUnderPaths Gamma C.ladder.limitWarp Z)
    (hclosed : OmegaClosed C.ladder.limitWarp (succ kappa) Z)
    {W : Set (imaginaryWeb C.ladder.limitWarp kappa).DPath}
    (hW : IsLinkageBlueprint W (C.ladder.frontier a) Z persistent)
    {s t : V} (hne : s ≠ t) (he : (s, t) ∈ familyEdges W)
    (hn : ¬Gamma.graph.Adj s t) :
    ∃ U : Set (imaginaryWeb C.ladder.limitWarp kappa).DPath,
      IsLinkageBlueprint U (C.ladder.frontier a) Z persistent ∧
      RealAdvance W U (C.ladder.frontier a) ∧
      ((∃ z ∈ C.ladder.frontier a,
          z ∈ (imaginaryWeb C.ladder.limitWarp kappa).terminalFrontier U ∧
          RealReach U s z ∧ FullAccount W U {z}) ∨
        (RealReach U s t ∧ FullAccount W U {t} ∧
          familyEdges W \ {(s, t)} ⊆ familyEdges U ∧
          (imaginaryWeb C.ladder.limitWarp kappa).terminalFrontier W ⊆
            (imaginaryWeb C.ladder.limitWarp kappa).terminalFrontier U)) ∧
      (∀ x, IsRealTerminal (Gamma := imaginaryWeb C.ladder.limitWarp kappa)
          Gamma.graph.Adj W x → x ≠ s →
        IsRealTerminal (Gamma := imaginaryWeb C.ladder.limitWarp kappa)
          Gamma.graph.Adj U x) ∧ SourcePredecessorRefines W U := by
  have hs := (familyEdges_subset_vertexSet_prod W he).1
  have ht := (familyEdges_subset_vertexSet_prod W he).2
  have hadj : (imaginaryWeb C.ladder.limitWarp kappa).graph.Adj s t := by
    have he' := he
    simp only [familyEdges, Set.mem_iUnion] at he'
    obtain ⟨p, _hp, hep⟩ := he'
    exact p.edgeSet_subset_adj hep
  have hi : IsImaginary C.ladder.limitWarp kappa s t :=
    hadj.resolve_left hn
  have hinside := hclosed.finite_hasCard_within C.capacity_infinite
    (hW.vertices_closed hs) (hW.vertices_closed ht) hi
  obtain ⟨p, U, hps, hpEnd, hpE, hpV, hU, hI, hV, hT, hR, hterms,
      _hsNotReal, hretain, hPred, hAccount, hfinishTerminal⟩ :=
    exists_finiteRoofCutBlueprintRealTransaction C ha hZ hW hne he
      (isRealTerminal_of_nonreal_outgoing hW.isWarp he hn) hinside (fun _ h ↦ h)
  have hreach : RealReach U s p.finish := hps ▸ RealReach.of_path p hpV hpE
  refine ⟨U, hU, ⟨hI, hV, hR, hT⟩, ?_, hterms, hPred⟩
  rcases hpEnd with hpT | hpt
  · exact Or.inl ⟨p.finish, hpT, hfinishTerminal hpT, hreach, hAccount⟩
  · exact Or.inr ⟨hpt ▸ hreach, hpt ▸ hAccount, hretain hpt⟩

/-- Resolve every nonreal edge on a finite simple old path. If the frontier
is not reached early, every old edge outside that path survives. -/
theorem exists_finiteSkeleton_resolution
    (C : LinkageBlueprint.ClubStageGeometry Gamma Y kappa (succ kappa))
    {a : Stage (succ kappa)} (ha : a ∈ C.club)
    {Z persistent : Set V}
    (hZ : ClosedUnderPaths Gamma C.ladder.limitWarp Z)
    (hclosed : OmegaClosed C.ladder.limitWarp (succ kappa) Z)
    {W : Set (imaginaryWeb C.ladder.limitWarp kappa).DPath}
    (hW : IsLinkageBlueprint W (C.ladder.frontier a) Z persistent)
    (p : FinitePath (imaginaryWeb C.ladder.limitWarp kappa).graph)
    (hpV : p.support ⊆ (imaginaryWeb C.ladder.limitWarp kappa).vertexSet W)
    (hpE : p.edgeSet ⊆ familyEdges W) :
    ∃ U : Set (imaginaryWeb C.ladder.limitWarp kappa).DPath,
      IsLinkageBlueprint U (C.ladder.frontier a) Z persistent ∧
      RealAdvance W U (C.ladder.frontier a) ∧
      (((∃ z ∈ C.ladder.frontier a,
          z ∈ (imaginaryWeb C.ladder.limitWarp kappa).terminalFrontier U ∧
          RealReach U p.start z ∧ FullAccount W U {z}) ∧
          ∀ x, IsRealTerminal (Gamma := imaginaryWeb C.ladder.limitWarp kappa)
              Gamma.graph.Adj W x →
            IsRealTerminal (Gamma := imaginaryWeb C.ladder.limitWarp kappa)
                Gamma.graph.Adj U x ∨ RealReaches U x (C.ladder.frontier a)) ∨
        (RealReach U p.start p.finish ∧ FullAccount W U {p.finish} ∧
          familyEdges W \ p.edgeSet ⊆ familyEdges U ∧
          (imaginaryWeb C.ladder.limitWarp kappa).terminalFrontier W ⊆
            (imaginaryWeb C.ladder.limitWarp kappa).terminalFrontier U)) ∧
      (∀ x, IsRealTerminal (Gamma := imaginaryWeb C.ladder.limitWarp kappa)
          Gamma.graph.Adj W x →
        IsRealTerminal (Gamma := imaginaryWeb C.ladder.limitWarp kappa)
            Gamma.graph.Adj U x ∨
          RealReaches U x (C.ladder.frontier a ∪ {p.finish})) ∧
      SourcePredecessorRefines W U := by
  let D := imaginaryWeb C.ladder.limitWarp kappa
  let T := C.ladder.frontier a
  have hwalk : ∀ {s t : V} (q : Walk D.graph s t), q.IsPath →
      ∀ (W : Set D.DPath), IsLinkageBlueprint W T Z persistent →
      (∀ x ∈ q.support, x ∈ D.vertexSet W) → q.edgeSet ⊆ familyEdges W →
      ∃ U : Set D.DPath, IsLinkageBlueprint U T Z persistent ∧
        RealAdvance W U T ∧
        (((∃ z ∈ T, z ∈ D.terminalFrontier U ∧
            RealReach U s z ∧ FullAccount W U {z}) ∧
            ∀ x, IsRealTerminal (Gamma := D) Gamma.graph.Adj W x →
              IsRealTerminal (Gamma := D) Gamma.graph.Adj U x ∨ RealReaches U x T) ∨
          (RealReach U s t ∧ FullAccount W U {t} ∧
            familyEdges W \ q.edgeSet ⊆ familyEdges U ∧
            D.terminalFrontier W ⊆ D.terminalFrontier U)) ∧
        (∀ x, IsRealTerminal (Gamma := D) Gamma.graph.Adj W x →
          IsRealTerminal (Gamma := D) Gamma.graph.Adj U x ∨
            RealReaches U x (T ∪ {t})) ∧ SourcePredecessorRefines W U := by
    intro s t q
    induction q with
    | @nil s =>
        intro _ W hW hV _
        exact ⟨W, hW, RealAdvance.refl W T,
          Or.inr ⟨RealReach.refl (hV s (by simp)), FullAccount.refl hW.isWarp {s},
            Set.sdiff_subset, Subset.rfl⟩,
          (fun _ hx ↦ Or.inl hx), SourcePredecessorRefines.refl W⟩
    | @cons s v t h_adj q ih =>
        intro hpath W hW hV hE
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
        · obtain ⟨U, hU, hadv, hresult, haccount, hPred⟩ := ih hqPath W hW hqV hqE
          have hfirst : RealReach U s v :=
            ⟨hadv.vertices (hV s (by simp)),
              .single (hadv.edges ⟨hhead, hreal⟩)⟩
          refine ⟨U, hU, hadv, ?_, haccount, hPred⟩
          rcases hresult with hearly | ⟨hend, hAccountEnd, hretained, htermRetained⟩
          · obtain ⟨z, hz, hzTerminal, hvz, hAccountEnd⟩ := hearly.1
            exact Or.inl ⟨⟨z, hz, hzTerminal, hfirst.trans hvz, hAccountEnd⟩, hearly.2⟩
          · refine Or.inr ⟨hfirst.trans hend, hAccountEnd, ?_, htermRetained⟩
            intro e he
            exact hretained ⟨he.1, fun heq ↦ he.2 (by simp [heq])⟩
        · obtain ⟨U, hU, hadv, hstep, hterms, hPred⟩ :=
            exists_nonrealEdge_resolution C ha hZ hclosed hW hsv hhead hreal
          rcases hstep with ⟨z, hz, hzTerminal, hsz, hAccountStep⟩ |
            ⟨hsvReal, hAccountStep, hretained, htermRetained⟩
          · have hearly : RealReaches U s T := ⟨z, hz, hsz⟩
            have haccountT : ∀ x,
                IsRealTerminal (Gamma := D) Gamma.graph.Adj W x →
                IsRealTerminal (Gamma := D) Gamma.graph.Adj U x ∨
                  RealReaches U x T := by
              intro x hx
              by_cases hxs : x = s
              · exact Or.inr (hxs ▸ hearly)
              · exact Or.inl (hterms x hx hxs)
            refine ⟨U, hU, hadv, Or.inl ⟨⟨z, hz, hzTerminal, hsz, hAccountStep⟩, haccountT⟩,
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
            obtain ⟨U', hU', hadv', hresult, haccount, hPred'⟩ :=
              ih hqPath U hU (fun x hx ↦ hadv.vertices (hqV x hx)) hqEU
            have hfirst : RealReach U' s v := hsvReal.mono hadv'.vertices hadv'.edges
            have hfinal : ((∃ z ∈ T, z ∈ D.terminalFrontier U' ∧
                RealReach U' s z ∧ FullAccount W U' {z}) ∧
                ∀ x, IsRealTerminal (Gamma := D) Gamma.graph.Adj W x →
                  IsRealTerminal (Gamma := D) Gamma.graph.Adj U' x ∨
                    RealReaches U' x T) ∨
                (RealReach U' s t ∧ FullAccount W U' {t} ∧
                  familyEdges W \ (Walk.cons h_adj q).edgeSet ⊆ familyEdges U' ∧
                  D.terminalFrontier W ⊆ D.terminalFrontier U') := by
              rcases hresult with hearly | ⟨hend, hAccountEnd, hremaining, htermRemaining⟩
              · obtain ⟨z, hz, hzTerminal, hvz, hAccountEnd⟩ := hearly.1
                have hsource : RealReaches U' s T := ⟨z, hz, hfirst.trans hvz⟩
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
            refine ⟨U', hU', hadv.trans hadv', hfinal, ?_,
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
  exact hwalk p.walk p.isPath W hW hpV hpE

#print axioms exists_nonrealEdge_resolution
#print axioms exists_finiteSkeleton_resolution

end Erdos599.Blueprint.ColouredSafeShortcutGraph
