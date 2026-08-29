/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingEqualMaximalStrictCollision

/-!
# A rooted contact with the equal route's target component

After strict-collision pruning, a target-pure equal route has only two kinds
of backward owners: components already rooted in the original source, and
the hanging component containing its own target marker.  If there is a
self-owned backward link, stop at the first one.  Its entry is on the rooted
side of the deleted link.  If there is none, the ordinary finite alternating
root lemma roots the terminal marker itself.

This file packages that dichotomy as an exact contact with the target
component.  It deliberately stops at contact; extending the rooted side
through the target component is a separate whole-family closure step.
-/

noncomputable section

open Cardinal Set

namespace Erdos599

open DirectedPath Alternating

universe u

variable {V : Type u} {Gamma : DWeb V}

namespace Alternating.FiniteTrace

/-- Distinct positions of a finite alternating trace carry distinct links.
This follows already from ordered compatibility: a link cannot be compatible
with a second copy of itself because its entry and exit are distinct. -/
theorem link_injective (F : FiniteTrace Gamma.graph) :
    Function.Injective F.link := by
  intro i j hij
  by_contra hne
  have hlt : i < j ∨ j < i := lt_or_gt_of_ne hne
  cases hlt with
  | inl hlt =>
      have hcompat := F.compatible i j hlt
      rw [hij] at hcompat
      cases hd : (F.link j).direction with
      | forward =>
          simp only [CompatibleInOrder, hd] at hcompat
          have hcontact := hcompat
            (F.link j).entry_mem_support
            (F.link j).entry_mem_support
          rcases hcontact with hcontact | hcontact
          · exact (F.link j).entry_ne_exit hcontact.2
          · exact (F.link j).entry_ne_exit hcontact.1
      | backward =>
          simp only [CompatibleInOrder, hd] at hcompat
          have hcontact := hcompat
            (F.link j).entry_mem_support
            (F.link j).entry_mem_support
          rcases hcontact with hcontact | hcontact
          · exact (F.link j).entry_ne_exit hcontact.2
          · exact (F.link j).entry_ne_exit hcontact.1
  | inr hlt =>
      have hji : F.link j = F.link i := hij.symm
      have hcompat := F.compatible j i hlt
      rw [hji] at hcompat
      cases hd : (F.link i).direction with
      | forward =>
          simp only [CompatibleInOrder, hd] at hcompat
          have hcontact := hcompat
            (F.link i).entry_mem_support
            (F.link i).entry_mem_support
          rcases hcontact with hcontact | hcontact
          · exact (F.link i).entry_ne_exit hcontact.2
          · exact (F.link i).entry_ne_exit hcontact.1
      | backward =>
          simp only [CompatibleInOrder, hd] at hcompat
          have hcontact := hcompat
            (F.link i).entry_mem_support
            (F.link i).entry_mem_support
          rcases hcontact with hcontact | hcontact
          · exact (F.link i).entry_ne_exit hcontact.2
          · exact (F.link i).entry_ne_exit hcontact.1

/-- A nonempty finite set of distinguished link positions has a first one,
in the exact occurrence-sensitive form used by the ordered stopping lemma. -/
theorem exists_first_link
    (F : FiniteTrace Gamma.graph) (P : Link Gamma.graph → Prop)
    (hex : ∃ l ∈ (AltPath.finite F).links, P l) :
    ∃ l ∈ (AltPath.finite F).links, P l ∧
      ∀ (bi li : Fin (F.lastIndex + 1)),
        F.link li = l → bi.1 < li.1 → ¬ P (F.link bi) := by
  classical
  let S : Finset (Fin (F.lastIndex + 1)) :=
    Finset.univ.filter (fun i ↦ P (F.link i))
  have hS : S.Nonempty := by
    obtain ⟨l, hl, hPl⟩ := hex
    change l ∈ F.links at hl
    obtain ⟨i, rfl⟩ := hl
    exact ⟨i, by simp [S, hPl]⟩
  let i : Fin (F.lastIndex + 1) := S.min' hS
  have hiS : i ∈ S := Finset.min'_mem S hS
  have hPi : P (F.link i) := (Finset.mem_filter.1 hiS).2
  refine ⟨F.link i, ?_, hPi, ?_⟩
  · change F.link i ∈ F.links
    exact ⟨i, rfl⟩
  · intro bi li hli hbil hPbi
    have hlii : li = i := F.link_injective hli
    subst li
    have hbiS : bi ∈ S := by simp [S, hPbi]
    have hib : i ≤ bi := Finset.min'_le S bi hbiS
    exact (not_lt_of_ge hib) hbil

end Alternating.FiniteTrace

namespace PopularAuxiliary.Input

/-- The full finite decoder ends at the old vertex represented by its
auxiliary target gadget. -/
theorem decodeFinitePath_terminal_of_finish_old
    {I : Type u} (J : PopularAuxiliary.Input Gamma I)
    (p : FinitePath J.lambda.graph)
    (hsource : p.start ∈ J.lambda.source)
    (htarget : p.finish ∈ J.lambda.target)
    (y : V) (hfinish : p.finish = .old y) :
    (J.decodeFinitePath p hsource htarget).terminal = y := by
  classical
  unfold decodeFinitePath
  split
  · rename_i x hx
    unfold decodeFinitePathFromFinite
    apply PopularAuxiliary.Input.LambdaVertex.old.inj
    exact (J.chooseTargetEndpoint p htarget).2.2.symm.trans hfinish
  · rename_i i hi
    unfold decodeFinitePathFromProxy
    apply PopularAuxiliary.Input.LambdaVertex.old.inj
    exact (J.chooseTargetEndpoint p htarget).2.2.symm.trans hfinish

end PopularAuxiliary.Input

namespace DWeb.KappaLadder

open GroundingEqualActiveSelection

variable {kappa : Cardinal.{u}}

/-- Every target-pure equal route surviving strict-collision pruning reaches
a source-rooted point on its own target-marker component.  The proof either
uses the target marker itself (all backward owners are grounded), or stops at
the entry of the first self-owned backward link. -/
theorem strictCollisionFree_equalSubwarp_exists_sourceRooted_targetComponentContact
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (P : Popular.XSWarp
      (L.popularAuxiliaryInput hL.legal).lambda
      (L.popularAuxiliaryInput hL.legal).lambda.target)
    (p : WarpPath (L.strictCollisionFreeSubwarp hL
      ((L.popularAuxiliaryIndexed hL).equalSubwarp P)))
    (hpure : (L.popularAuxiliaryInput hL.legal).IsTargetPure p.1)
    (T : L.EqualTargetComponent hL P p.1 p.2.1)
    {E : Set (V × V)}
    (hinitial : ∃ a ∈ Gamma.source,
      Relation.ReflTransGen (fun x y ↦ (x, y) ∈ E) a
        (canonicalErasedRoute
          (L.popularAuxiliaryInput hL.legal)
          ((L.popularAuxiliaryIndexed hL).equalSubwarp P)
          ⟨p.1, L.strictCollisionFreeSubwarp_paths_subset hL
            ((L.popularAuxiliaryIndexed hL).equalSubwarp P) p.2⟩).initial)
    (hforward : (canonicalErasedRoute
      (L.popularAuxiliaryInput hL.legal)
      ((L.popularAuxiliaryIndexed hL).equalSubwarp P)
      ⟨p.1, L.strictCollisionFreeSubwarp_paths_subset hL
        ((L.popularAuxiliaryIndexed hL).equalSubwarp P) p.2⟩).directionEdges
          .forward ⊆ E)
    (hgrounded : ∀ (parent : Gamma.DPath), parent ∈ L.limitWarp →
      parent.initial ∈ Gamma.source →
      ∀ (b : Link Gamma.graph), b.path.IsSubpathOf parent →
        ∃ a ∈ Gamma.source,
          Relation.ReflTransGen (fun x y ↦ (x, y) ∈ E)
            a b.path.start) :
    ∃ x ∈ T.component.support, ∃ a ∈ Gamma.source,
      Relation.ReflTransGen (fun u v ↦ (u, v) ∈ E) a x := by
  classical
  let Q := (L.popularAuxiliaryIndexed hL).equalSubwarp P
  let pQ : WarpPath Q :=
    ⟨p.1, L.strictCollisionFreeSubwarp_paths_subset hL Q p.2⟩
  let J := L.popularAuxiliaryInput hL.legal
  change ∃ a ∈ Gamma.source,
      Relation.ReflTransGen (fun x y ↦ (x, y) ∈ E) a
        (canonicalErasedRoute J Q pQ).initial at hinitial
  change (canonicalErasedRoute J Q pQ).directionEdges .forward ⊆ E
    at hforward
  let D := J.decodeFinitePath pQ.1
    (Q.starts_in_source pQ.2) (Q.ends_in_target pQ.2)
  have hterminal :
      (canonicalErasedRoute J Q pQ).terminal? = some T.marker.1 := by
    have hDterminal : D.terminal = T.marker.1 := by
      exact J.decodeFinitePath_terminal_of_finish_old pQ.1
        (Q.starts_in_source pQ.2) (Q.ends_in_target pQ.2)
        T.marker.1 T.finish_eq
    exact D.erasedCompression.terminal_eq.trans
      (congrArg some hDterminal)
  have hback : BackwardLinksOn J.ladder.paths
      (canonicalErasedRoute J Q pQ) := by
    change BackwardLinksOn J.ladder.paths D.erasedCompression.path
    exact D.erasedCompression_backwardLinksOn
  by_cases hself : ∃ l ∈ (canonicalErasedRoute J Q pQ).links,
      l.direction = .backward ∧ l.path.IsSubpathOf T.component
  · cases hroute : canonicalErasedRoute J Q pQ with
    | trivial v => simp [hroute, AltPath.links] at hself
    | finite F =>
        obtain ⟨l, hl, hlself, hfirstMin⟩ :=
          F.exists_first_link
            (fun l ↦ l.direction = .backward ∧
              l.path.IsSubpathOf T.component) (by
              simpa only [hroute] using hself)
        have hlroute : l ∈ (canonicalErasedRoute J Q pQ).links := by
          simpa only [hroute] using hl
        have hlroot :=
          L.strictCollisionFree_equalSubwarp_firstSelfOwnedEntry_rooted
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
        exact canonicalErasedRoute_backwardLink_entry_mem_owner
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
        L.strictCollisionFree_equalSubwarp_backwardLink_groundedOr_selfOwned
          hL P p hpure T l hl hldir
      · exact hgrounded owner howner hroot l hownerSub
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

#print axioms Erdos599.Alternating.FiniteTrace.link_injective
#print axioms Erdos599.Alternating.FiniteTrace.exists_first_link
#print axioms Erdos599.PopularAuxiliary.Input.decodeFinitePath_terminal_of_finish_old
#print axioms Erdos599.DWeb.KappaLadder.strictCollisionFree_equalSubwarp_exists_sourceRooted_targetComponentContact
