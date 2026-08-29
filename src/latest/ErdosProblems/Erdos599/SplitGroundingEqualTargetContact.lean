/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SplitGroundingEqualOrderedContactCore

/-!
# Source-rooted contact with a split equal route's target component

After strict-owner pruning, every backward owner is either already rooted
in the original source or is the route's own target component.  Stopping at
the first self-owned backward link, or otherwise at the target marker,
therefore produces an exact rooted contact.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599

open DirectedPath Alternating

universe u

variable {V : Type u} {Gamma : DWeb V}

namespace DWeb.KappaLadder

open GroundingEqualActiveSelection

variable {kappa : Cardinal.{u}}

private abbrev SplitContactInput
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance) :=
  L.splitPopularAuxiliaryInput hL.legal

/-- Root the entry of the first self-owned backward link; all earlier
backward owners are forced to be original-source rooted. -/
theorem splitStrictCollisionFree_firstSelfOwnedEntry_rooted
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance)
    (P : Popular.XSWarp
      (SplitContactInput L hL).lambda
      (SplitContactInput L hL).lambda.target)
    (p : WarpPath (L.splitStrictCollisionFreeSubwarp hL
      ((L.splitPopularAuxiliaryIndexed hL).equalSubwarp P)))
    (hpure : (SplitContactInput L hL).IsTargetPure p.1)
    (T : L.SplitEqualTargetComponent hL P p.1 p.2.1)
    (l : Link Gamma.graph)
    (hl : l ∈ (canonicalErasedRoute
      (SplitContactInput L hL)
      ((L.splitPopularAuxiliaryIndexed hL).equalSubwarp P)
      ⟨p.1, L.splitStrictCollisionFreeSubwarp_paths_subset hL
        ((L.splitPopularAuxiliaryIndexed hL).equalSubwarp P) p.2⟩).links)
    (hldir : l.direction = .backward)
    (hfirst : ∀ (F : FiniteTrace Gamma.graph)
      (hroute : canonicalErasedRoute
        (SplitContactInput L hL)
        ((L.splitPopularAuxiliaryIndexed hL).equalSubwarp P)
        ⟨p.1, L.splitStrictCollisionFreeSubwarp_paths_subset hL
          ((L.splitPopularAuxiliaryIndexed hL).equalSubwarp P) p.2⟩ = .finite F)
      (bi li : Fin (F.lastIndex + 1)),
      F.link li = l → bi.1 < li.1 →
      (F.link bi).direction = .backward →
      ¬(F.link bi).path.IsSubpathOf T.component)
    {A : Set V} {E : Set (V × V)}
    (hinitial : ∃ a ∈ A,
      Relation.ReflTransGen (fun x y ↦ (x, y) ∈ E) a
        (canonicalErasedRoute
          (SplitContactInput L hL)
          ((L.splitPopularAuxiliaryIndexed hL).equalSubwarp P)
          ⟨p.1, L.splitStrictCollisionFreeSubwarp_paths_subset hL
            ((L.splitPopularAuxiliaryIndexed hL).equalSubwarp P) p.2⟩).initial)
    (hforward : (canonicalErasedRoute
      (SplitContactInput L hL)
      ((L.splitPopularAuxiliaryIndexed hL).equalSubwarp P)
      ⟨p.1, L.splitStrictCollisionFreeSubwarp_paths_subset hL
        ((L.splitPopularAuxiliaryIndexed hL).equalSubwarp P) p.2⟩).directionEdges
          .forward ⊆ E)
    (hgrounded : ∀ (b : Link Gamma.graph),
      b ∈ (canonicalErasedRoute
        (SplitContactInput L hL)
        ((L.splitPopularAuxiliaryIndexed hL).equalSubwarp P)
        ⟨p.1, L.splitStrictCollisionFreeSubwarp_paths_subset hL
          ((L.splitPopularAuxiliaryIndexed hL).equalSubwarp P) p.2⟩).links →
      b.direction = .backward →
      ∀ (parent : Gamma.DPath), parent ∈ L.limitWarp →
      parent.initial ∈ Gamma.source → b.path.IsSubpathOf parent →
        ∃ a ∈ A,
          Relation.ReflTransGen (fun x y ↦ (x, y) ∈ E)
            a b.path.start) :
    ∃ a ∈ A,
      Relation.ReflTransGen (fun x y ↦ (x, y) ∈ E) a l.entry := by
  let Q := (L.splitPopularAuxiliaryIndexed hL).equalSubwarp P
  let pQ : WarpPath Q :=
    ⟨p.1, L.splitStrictCollisionFreeSubwarp_paths_subset hL Q p.2⟩
  apply splitCanonicalErasedRoute_backwardLink_entry_rooted
    (SplitContactInput L hL) Q pQ l hl hldir hinitial hforward
  intro b hb hbdir _hbowner F hroute bi li hbi hli hlt
  obtain ⟨parent, hparent, hsub, hroot | hself⟩ :=
    L.splitStrictCollisionFree_equalSubwarp_backwardLink_groundedOr_selfOwned
      hL P p hpure T b hb hbdir
  · exact hgrounded b hb hbdir parent hparent hroot hsub
  · exfalso
    apply hfirst F hroute bi li hli hlt
    · exact (congrArg (fun c : Link Gamma.graph ↦ c.direction) hbi).trans
        hbdir
    · rw [hbi]
      exact hself ▸ hsub

/-- Every target-pure strict-free split equal route reaches a rooted point
on its own target-marker component. -/
theorem splitStrictCollisionFree_equalSubwarp_exists_sourceRooted_targetComponentContact
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance)
    (P : Popular.XSWarp
      (SplitContactInput L hL).lambda
      (SplitContactInput L hL).lambda.target)
    (p : WarpPath (L.splitStrictCollisionFreeSubwarp hL
      ((L.splitPopularAuxiliaryIndexed hL).equalSubwarp P)))
    (hpure : (SplitContactInput L hL).IsTargetPure p.1)
    (T : L.SplitEqualTargetComponent hL P p.1 p.2.1)
    {E : Set (V × V)}
    (hinitial : ∃ a ∈ Gamma.source,
      Relation.ReflTransGen (fun x y ↦ (x, y) ∈ E) a
        (canonicalErasedRoute
          (SplitContactInput L hL)
          ((L.splitPopularAuxiliaryIndexed hL).equalSubwarp P)
          ⟨p.1, L.splitStrictCollisionFreeSubwarp_paths_subset hL
            ((L.splitPopularAuxiliaryIndexed hL).equalSubwarp P) p.2⟩).initial)
    (hforward : (canonicalErasedRoute
      (SplitContactInput L hL)
      ((L.splitPopularAuxiliaryIndexed hL).equalSubwarp P)
      ⟨p.1, L.splitStrictCollisionFreeSubwarp_paths_subset hL
        ((L.splitPopularAuxiliaryIndexed hL).equalSubwarp P) p.2⟩).directionEdges
          .forward ⊆ E)
    (hgrounded : ∀ (b : Link Gamma.graph),
      b ∈ (canonicalErasedRoute
        (SplitContactInput L hL)
        ((L.splitPopularAuxiliaryIndexed hL).equalSubwarp P)
        ⟨p.1, L.splitStrictCollisionFreeSubwarp_paths_subset hL
          ((L.splitPopularAuxiliaryIndexed hL).equalSubwarp P) p.2⟩).links →
      b.direction = .backward →
      ∀ (parent : Gamma.DPath), parent ∈ L.limitWarp →
      parent.initial ∈ Gamma.source → b.path.IsSubpathOf parent →
        ∃ a ∈ Gamma.source,
          Relation.ReflTransGen (fun x y ↦ (x, y) ∈ E)
            a b.path.start) :
    ∃ x ∈ T.component.support, ∃ a ∈ Gamma.source,
      Relation.ReflTransGen (fun u v ↦ (u, v) ∈ E) a x := by
  classical
  let Q := (L.splitPopularAuxiliaryIndexed hL).equalSubwarp P
  let pQ : WarpPath Q :=
    ⟨p.1, L.splitStrictCollisionFreeSubwarp_paths_subset hL Q p.2⟩
  let J := SplitContactInput L hL
  change ∃ a ∈ Gamma.source,
      Relation.ReflTransGen (fun x y ↦ (x, y) ∈ E) a
        (canonicalErasedRoute J Q pQ).initial at hinitial
  change (canonicalErasedRoute J Q pQ).directionEdges .forward ⊆ E
    at hforward
  let D := J.decodeFinitePath pQ.1
    (Q.starts_in_source pQ.2) (Q.ends_in_target pQ.2)
  have hterminal :
      (canonicalErasedRoute J Q pQ).terminal? = some T.marker.1 := by
    have hDterminal : D.terminal = T.marker.1 :=
      J.splitDecodeFinitePath_terminal_of_finish_old pQ.1
        (Q.starts_in_source pQ.2) (Q.ends_in_target pQ.2)
        T.marker.1 T.finish_eq
    exact D.erasedCompression.terminal_eq.trans (congrArg some hDterminal)
  have hback : BackwardLinksOn J.ladder.paths
      (canonicalErasedRoute J Q pQ) := by
    change BackwardLinksOn J.ladder.paths D.erasedCompression.path
    apply D.runs.erasedSignedRoute.compressionOfValid_backwardLinksOn
      (fun {_s} hs ↦ D.valid _
        (D.runs.erasedSignedRoute.steps_sublist.subset hs))
      J.ladder.disjoint
    intro s hs hdir
    simpa [PopularAuxiliary.Input.familyEdges, Alternating.familyEdges] using
      D.backward_on_ladder s
        (D.runs.erasedSignedRoute.steps_sublist.subset hs) hdir
  by_cases hself : ∃ l ∈ (canonicalErasedRoute J Q pQ).links,
      l.direction = .backward ∧ l.path.IsSubpathOf T.component
  · cases hroute : canonicalErasedRoute J Q pQ with
    | trivial v => simp [hroute, AltPath.links] at hself
    | finite F =>
        obtain ⟨l, hl, hlself, hfirstMin⟩ :=
          F.splitExists_first_link
            (fun l ↦ l.direction = .backward ∧
              l.path.IsSubpathOf T.component) (by
              simpa only [hroute] using hself)
        have hlroute : l ∈ (canonicalErasedRoute J Q pQ).links := by
          simpa only [hroute] using hl
        have hlroot :=
          L.splitStrictCollisionFree_firstSelfOwnedEntry_rooted
            hL P p hpure T l hlroute hlself.1
            (by
              intro F' hroute' bi li hli hbil hbi
              have hFF : F' = F := by
                rw [hroute] at hroute'
                exact AltPath.finite.inj hroute'.symm
              subst F'
              intro hsub
              exact hfirstMin bi li hli hbil ⟨hbi, hsub⟩)
            hinitial hforward hgrounded
        refine ⟨l.entry, ?_, hlroot⟩
        exact splitCanonicalErasedRoute_backwardLink_entry_mem_owner
          J Q pQ l hlroute hlself.1 T.component
          T.component_essential.1 hlself.2
    | infinite R =>
        rw [hroute] at hterminal
        simp [AltPath.terminal?] at hterminal
  · have hbackward : ∀ (l : Link Gamma.graph),
        l ∈ (canonicalErasedRoute J Q pQ).links →
        l.direction = .backward →
        ∀ parent ∈ J.ladder.paths, l.path.IsSubpathOf parent →
          ∃ a ∈ Gamma.source,
            Relation.ReflTransGen (fun x y ↦ (x, y) ∈ E)
              a l.path.start := by
      intro l hl hldir parent hparent hsub
      obtain ⟨owner, howner, hownerSub, hroot | hownerSelf⟩ :=
        L.splitStrictCollisionFree_equalSubwarp_backwardLink_groundedOr_selfOwned
          hL P p hpure T l hl hldir
      · exact hgrounded l hl hldir owner howner hroot hownerSub
      · exfalso
        apply hself
        exact ⟨l, hl, hldir, hownerSelf ▸ hownerSub⟩
    have hmarkerRoot : ∃ a ∈ Gamma.source,
        Relation.ReflTransGen (fun x y ↦ (x, y) ∈ E)
          a T.marker.1 := by
      cases hroute : canonicalErasedRoute J Q pQ with
      | trivial v =>
          have hvm : v = T.marker.1 := by
            simpa [hroute, AltPath.terminal?] using hterminal
          simpa [hroute, AltPath.initial, hvm] using hinitial
      | finite F =>
          have hroot := F.exists_root_reaching_terminal
            (by simpa only [hroute] using hback)
            (by simpa only [hroute] using hforward)
            (by simpa [hroute, AltPath.initial] using hinitial)
            (by
              intro l hl hldir parent hparent hsub
              exact hbackward l (by simpa only [hroute] using hl)
                hldir parent hparent hsub)
          have hFm : F.terminal = T.marker.1 := by
            simpa [hroute, AltPath.terminal?] using hterminal
          simpa only [hFm] using hroot
      | infinite R =>
          rw [hroute] at hterminal
          simp [AltPath.terminal?] at hterminal
    exact ⟨T.marker.1, T.marker_mem_support, hmarkerRoot⟩

end DWeb.KappaLadder
end Erdos599
