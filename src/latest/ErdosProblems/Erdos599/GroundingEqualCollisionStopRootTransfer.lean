/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingEqualMaximalCollisionRecursion
import ErdosProblems.Erdos599.GroundingEqualMaximalRouteRoot
import ErdosProblems.Erdos599.GroundingEqualMaximalRouteContact

/-!
# Root transfer to ordered equal-collision stops

The maximal collision forest stores a stop only at an ordered vertex of its
owner route: the route initial, a retained forward vertex, or the entry of a
backward link.  The third case is not a new kind of root.  Chronological
compatibility places every backward entry either at the route initial or on
the preceding forward part of the route.

Consequently one common anchor hypothesis roots all three cases.  This file
packages that reduction both for an arbitrary canonical erased route and for
the literal `collisionStop` chosen by the maximal collision recursion.
-/

noncomputable section

open Cardinal Set

namespace Erdos599

open DirectedPath Alternating

universe u

variable {V : Type u} {Gamma : DWeb V}

namespace Alternating.FiniteTrace

/-- Strictly ordered form of forward-vertex reachability.  A vertex on a
forward link is fed either by the trace initial, or by the ambient start of
the immediately preceding backward link.  In the second case the returned
backward-link index is strictly smaller than the chosen forward-link index.

Keeping the two indices is essential for the equal-stage recursion: it
prevents a later (or the same) deleted anchor from being used to justify an
earlier rooted point. -/
theorem forwardVertex_reached_from_initial_or_priorBackward
    (Q : FiniteTrace Gamma.graph) {Y : Set Gamma.DPath}
    (hback : BackwardLinksOn Y (.finite Q))
    {x : V} (hx : x ∈ (AltPath.finite Q).directionVertices .forward) :
    Relation.ReflTransGen
        (fun u v ↦ (u, v) ∈
          (AltPath.finite Q).directionEdges .forward)
        Q.initial x ∨
      ∃ (b : Link Gamma.graph),
        b ∈ (AltPath.finite Q).links ∧
        b.direction = .backward ∧
        (∃ parent ∈ Y, b.path.IsSubpathOf parent) ∧
        Relation.ReflTransGen
          (fun u v ↦ (u, v) ∈
            (AltPath.finite Q).directionEdges .forward)
          b.path.start x ∧
        ∃ (bi fi : Fin (Q.lastIndex + 1)),
          Q.link bi = b ∧
          x ∈ (Q.link fi).path.support ∧
          (Q.link fi).direction = .forward ∧
          bi.1 < fi.1 := by
  simp only [AltPath.directionVertices, Set.mem_iUnion] at hx
  obtain ⟨l, hl, hldir, hxl⟩ := hx
  change l ∈ Q.links at hl
  rcases hl with ⟨i, rfl⟩
  have hreach := Q.reflTransGen_entry_vertex_of_forward i hldir
    (Set.Subset.rfl) hxl
  cases hi : i.1 with
  | zero =>
      left
      have hizero : i = (0 : Fin (Q.lastIndex + 1)) := by
        apply Fin.ext
        exact hi
      have hinitial : Q.initial = (Q.link i).entry := by
        rw [hizero]
        rfl
      rw [hinitial]
      exact hreach
  | succ n =>
      right
      have hn : n < Q.lastIndex := by omega
      let predShort : Fin Q.lastIndex := ⟨n, hn⟩
      let pred : Fin (Q.lastIndex + 1) := Fin.castSucc predShort
      have hipred : i = predShort.succ := by
        apply Fin.ext
        change i.1 = n + 1
        exact hi
      have hpredDir : (Q.link pred).direction = .backward := by
        have halt := Q.alternates predShort
        change (Q.link pred).direction ≠
          (Q.link predShort.succ).direction at halt
        rw [← hipred, hldir] at halt
        cases hp : (Q.link pred).direction with
        | forward => exact False.elim (halt hp)
        | backward => rfl
      have hpredMem : Q.link pred ∈
          (AltPath.finite Q).links := ⟨pred, rfl⟩
      obtain ⟨parent, hparent, hsub⟩ :=
        hback (Q.link pred) hpredMem hpredDir
      refine ⟨Q.link pred, hpredMem, hpredDir,
        ⟨parent, hparent, hsub⟩, ?_, pred, i, rfl,
        hxl, hldir, ?_⟩
      · have hjoin : (Q.link pred).path.start = (Q.link i).entry := by
          calc
            (Q.link pred).path.start = (Q.link pred).exit := by
              simp [Link.exit, hpredDir]
            _ = (Q.link predShort.succ).entry := Q.joins predShort
            _ = (Q.link i).entry := by rw [hipred]
        simpa only [hjoin] using hreach
      · change n < i.1
        omega

end Alternating.FiniteTrace

namespace DWeb.KappaLadder

open GroundingEqualActiveSelection
open GroundingEqualMaximalCollisionForest
open GroundingEqualMaximalCollisionRecursion

variable {kappa : Cardinal.{u}}

/-- Canonical erased-route form of the strict forward-vertex ordering
lemma.  The finite trace and its equality with the canonical route are
returned so downstream recursion can compare the two literal link indices.
-/
theorem canonicalErasedRoute_forwardVertex_reached_from_initial_or_priorBackward
    {I : Type u} (J : PopularAuxiliary.Input Gamma I)
    (Q : Popular.XSWarp J.lambda J.lambda.target) (p : WarpPath Q)
    {x : V} (hx : x ∈
      (canonicalErasedRoute J Q p).directionVertices .forward) :
    Relation.ReflTransGen
        (fun u v ↦ (u, v) ∈
          (canonicalErasedRoute J Q p).directionEdges .forward)
        (canonicalErasedRoute J Q p).initial x ∨
      ∃ (b : Link Gamma.graph),
        b ∈ (canonicalErasedRoute J Q p).links ∧
        b.direction = .backward ∧
        (∃ parent ∈ J.ladder.paths, b.path.IsSubpathOf parent) ∧
        Relation.ReflTransGen
          (fun u v ↦ (u, v) ∈
            (canonicalErasedRoute J Q p).directionEdges .forward)
          b.path.start x ∧
        ∃ (F : FiniteTrace Gamma.graph)
            (hroute : canonicalErasedRoute J Q p = .finite F)
            (bi fi : Fin (F.lastIndex + 1)),
          F.link bi = b ∧
          x ∈ (F.link fi).path.support ∧
          (F.link fi).direction = .forward ∧
          bi.1 < fi.1 := by
  cases hroute : canonicalErasedRoute J Q p with
  | trivial v =>
      simp [hroute, AltPath.directionVertices, AltPath.links] at hx
  | finite F =>
      let T := J.decodeFinitePath p.1
        (Q.starts_in_source p.2) (Q.ends_in_target p.2)
      have hback : BackwardLinksOn J.ladder.paths (.finite F) := by
        have hfull : BackwardLinksOn J.ladder.paths
            (canonicalErasedRoute J Q p) := by
          simpa only [canonicalErasedRoute, T] using
            T.erasedCompression_backwardLinksOn
        simpa only [hroute] using hfull
      rcases F.forwardVertex_reached_from_initial_or_priorBackward hback
          (by simpa only [hroute] using hx) with
          hroot | ⟨b, hb, hbdir, hbowner, hreach,
            bi, fi, hbi, hxfi, hfdir, hlt⟩
      · left
        simpa only [hroute, AltPath.initial,
          AltPath.directionEdges] using hroot
      · right
        refine ⟨b, ?_, hbdir, hbowner, ?_, F, rfl, bi, fi,
          hbi, hxfi, hfdir, hlt⟩
        · simpa only [hroute] using hb
        · simpa only [hroute, AltPath.directionEdges] using hreach
  | infinite R =>
      let T := J.decodeFinitePath p.1
        (Q.starts_in_source p.2) (Q.ends_in_target p.2)
      have hterminal := T.erasedCompression.terminal_eq
      have hpath : T.erasedCompression.path = .infinite R := by
        simpa only [canonicalErasedRoute, T] using hroute
      rw [hpath] at hterminal
      simp at hterminal

/-- Root transfer to a chosen forward-route vertex only needs anchors for
backward links strictly preceding one concrete forward-link occurrence of
that vertex.  This is the forward analogue of
`canonicalErasedRoute_backwardLink_entry_rooted_of_priorBackward`. -/
theorem canonicalErasedRoute_forwardVertex_rooted_of_priorBackward
    {I : Type u} (J : PopularAuxiliary.Input Gamma I)
    (Q : Popular.XSWarp J.lambda J.lambda.target) (p : WarpPath Q)
    {A : Set V} {E : Set (V × V)}
    (hinitial : ∃ a ∈ A,
      Relation.ReflTransGen (fun u v ↦ (u, v) ∈ E) a
        (canonicalErasedRoute J Q p).initial)
    (hforward :
      (canonicalErasedRoute J Q p).directionEdges .forward ⊆ E)
    {x : V}
    (hx : x ∈ (canonicalErasedRoute J Q p).directionVertices .forward)
    (hprior : ∀ (b : Link Gamma.graph),
      b ∈ (canonicalErasedRoute J Q p).links →
      b.direction = .backward →
      (∃ parent ∈ J.ladder.paths, b.path.IsSubpathOf parent) →
      ∀ (F : FiniteTrace Gamma.graph)
        (hroute : canonicalErasedRoute J Q p = .finite F)
        (bi fi : Fin (F.lastIndex + 1)),
        F.link bi = b →
        x ∈ (F.link fi).path.support →
        (F.link fi).direction = .forward →
        bi.1 < fi.1 →
        ∃ a ∈ A,
          Relation.ReflTransGen (fun u v ↦ (u, v) ∈ E)
            a b.path.start) :
    ∃ a ∈ A,
      Relation.ReflTransGen (fun u v ↦ (u, v) ∈ E) a x := by
  rcases canonicalErasedRoute_forwardVertex_reached_from_initial_or_priorBackward
      J Q p hx with hfromInitial |
        ⟨b, hb, hbdir, hbowner, hfromPrior,
          F, hroute, bi, fi, hbi, hxfi, hfdir, hlt⟩
  · obtain ⟨a, haA, haInitial⟩ := hinitial
    refine ⟨a, haA, haInitial.trans ?_⟩
    exact Relation.ReflTransGen.mono
      (r := fun u v ↦ (u, v) ∈
        (canonicalErasedRoute J Q p).directionEdges .forward)
      (p := fun u v ↦ (u, v) ∈ E)
      (fun _ _ h ↦ hforward h) _ _ hfromInitial
  · obtain ⟨a, haA, haPrior⟩ :=
      hprior b hb hbdir hbowner F hroute bi fi hbi hxfi hfdir hlt
    refine ⟨a, haA, haPrior.trans ?_⟩
    exact Relation.ReflTransGen.mono
      (r := fun u v ↦ (u, v) ∈
        (canonicalErasedRoute J Q p).directionEdges .forward)
      (p := fun u v ↦ (u, v) ∈ E)
      (fun _ _ h ↦ hforward h) _ _ hfromPrior

/-- An ordered point of a canonical erased route is rooted once its initial
and the ambient starts of all of its genuine backward links are rooted.

The backward-entry case is reduced to the initial/forward cases before the
finite alternating-root theorem is invoked.  In particular, no interior
point of a deleted backward run is treated as rooted. -/
theorem canonicalErasedRoute_orderedVertex_rooted_of_anchorReachability
    {I : Type u} (J : PopularAuxiliary.Input Gamma I)
    (Q : Popular.XSWarp J.lambda J.lambda.target) (p : WarpPath Q)
    {A : Set V} {E : Set (V × V)}
    (hinitial : ∃ a ∈ A,
      Relation.ReflTransGen (fun x y ↦ (x, y) ∈ E) a
        (canonicalErasedRoute J Q p).initial)
    (hforward :
      (canonicalErasedRoute J Q p).directionEdges .forward ⊆ E)
    (hbackward : ∀ (l : Link Gamma.graph),
      l ∈ (canonicalErasedRoute J Q p).links →
      l.direction = .backward →
      ∀ parent ∈ J.ladder.paths, l.path.IsSubpathOf parent →
        ∃ a ∈ A,
          Relation.ReflTransGen (fun x y ↦ (x, y) ∈ E)
            a l.path.start)
    {x : V}
    (hx : x = (canonicalErasedRoute J Q p).initial ∨
      x ∈ (canonicalErasedRoute J Q p).directionVertices .forward ∨
      ∃ l : Link Gamma.graph,
        l ∈ (canonicalErasedRoute J Q p).links ∧
        l.direction = .backward ∧ x = l.entry) :
    ∃ a ∈ A,
      Relation.ReflTransGen (fun u v ↦ (u, v) ∈ E) a x := by
  let T := J.decodeFinitePath p.1
    (Q.starts_in_source p.2) (Q.ends_in_target p.2)
  have hback : BackwardLinksOn J.ladder.paths
      (canonicalErasedRoute J Q p) := by
    simpa only [canonicalErasedRoute, T] using
      T.erasedCompression_backwardLinksOn
  have rootForward : ∀ {y : V},
      y ∈ (canonicalErasedRoute J Q p).directionVertices .forward →
        ∃ a ∈ A,
          Relation.ReflTransGen (fun u v ↦ (u, v) ∈ E) a y := by
    intro y hy
    cases hroute : canonicalErasedRoute J Q p with
    | trivial v =>
        simp [hroute, AltPath.directionVertices, AltPath.links] at hy
    | finite F =>
        apply F.exists_root_reaching_forwardVertex
          (by simpa only [hroute] using hback)
          (by simpa only [hroute] using hforward)
          (by simpa [hroute, AltPath.initial] using hinitial)
        · intro b hb hbdir parent hparent hsub
          exact hbackward b (by simpa only [hroute] using hb) hbdir
            parent hparent hsub
        · simpa only [hroute] using hy
    | infinite R =>
        have hterminal := T.erasedCompression.terminal_eq
        have hpath : T.erasedCompression.path = .infinite R := by
          simpa only [canonicalErasedRoute, T] using hroute
        rw [hpath] at hterminal
        simp at hterminal
  rcases hx with rfl | hxforward | ⟨l, hl, hldir, rfl⟩
  · exact hinitial
  · exact rootForward hxforward
  · rcases canonicalErasedRoute_backwardLink_entry_eq_initial_or_mem_forwardVertices
        J Q p l hl hldir with hli | hlforward
    · simpa only [hli] using hinitial
    · exact rootForward hlforward

/-- Specialization to the literal ordered stop selected by the maximal
collision recursion.  This is the exact local root-transfer premise needed
when a node is absorbed through its chosen owner route. -/
theorem collisionStop_rooted_of_ownerAnchorReachability
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {W : Popular.XSWarp
      (L.popularAuxiliaryInput hL.legal).lambda
      (L.popularAuxiliaryInput hL.legal).lambda.target}
    (q : WarpPath W) {A : Set V} {E : Set (V × V)}
    (hinitial : ∃ a ∈ A,
      Relation.ReflTransGen (fun x y ↦ (x, y) ∈ E) a
        (canonicalErasedRoute
          (L.popularAuxiliaryInput hL.legal) W
          (collisionOwner hL W q)).initial)
    (hforward :
      (canonicalErasedRoute
        (L.popularAuxiliaryInput hL.legal) W
        (collisionOwner hL W q)).directionEdges .forward ⊆ E)
    (hbackward : ∀ (l : Link Gamma.graph),
      l ∈ (canonicalErasedRoute
        (L.popularAuxiliaryInput hL.legal) W
        (collisionOwner hL W q)).links →
      l.direction = .backward →
      ∀ parent ∈ (L.popularAuxiliaryInput hL.legal).ladder.paths,
        l.path.IsSubpathOf parent →
          ∃ a ∈ A,
            Relation.ReflTransGen (fun x y ↦ (x, y) ∈ E)
              a l.path.start) :
    ∃ a ∈ A,
      Relation.ReflTransGen (fun x y ↦ (x, y) ∈ E) a
        (collisionStop hL W q) := by
  apply canonicalErasedRoute_orderedVertex_rooted_of_anchorReachability
    (L.popularAuxiliaryInput hL.legal) W (collisionOwner hL W q)
    hinitial hforward hbackward
  rcases collisionStop_ordered (hL := hL) (W := W) q with
      hinitial | hforwardVertex | ⟨l, hl, hldir, _hsub, hentry⟩
  · exact Or.inl hinitial
  · exact Or.inr <| Or.inl hforwardVertex
  · exact Or.inr <| Or.inr ⟨l, hl, hldir, hentry⟩

/-- The literal collision stop is reached along owner-route forward edges
either from the owner-route initial, or from a strictly earlier backward
anchor.  The second alternative records the finite route, the anchor index,
and the stop occurrence index.  It therefore supports an internal induction
on the finite alternating trace without assuming every backward anchor in
advance. -/
theorem collisionStop_reached_from_ownerInitial_or_priorBackward
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {W : Popular.XSWarp
      (L.popularAuxiliaryInput hL.legal).lambda
      (L.popularAuxiliaryInput hL.legal).lambda.target}
    (q : WarpPath W) :
    Relation.ReflTransGen
        (fun u v ↦ (u, v) ∈
          (canonicalErasedRoute
            (L.popularAuxiliaryInput hL.legal) W
            (collisionOwner hL W q)).directionEdges .forward)
        (canonicalErasedRoute
          (L.popularAuxiliaryInput hL.legal) W
          (collisionOwner hL W q)).initial
        (collisionStop hL W q) ∨
      ∃ (b : Link Gamma.graph),
        b ∈ (canonicalErasedRoute
          (L.popularAuxiliaryInput hL.legal) W
          (collisionOwner hL W q)).links ∧
        b.direction = .backward ∧
        (∃ parent ∈ (L.popularAuxiliaryInput hL.legal).ladder.paths,
          b.path.IsSubpathOf parent) ∧
        Relation.ReflTransGen
          (fun u v ↦ (u, v) ∈
            (canonicalErasedRoute
              (L.popularAuxiliaryInput hL.legal) W
              (collisionOwner hL W q)).directionEdges .forward)
          b.path.start (collisionStop hL W q) ∧
        ∃ (F : FiniteTrace Gamma.graph)
            (hroute : canonicalErasedRoute
              (L.popularAuxiliaryInput hL.legal) W
              (collisionOwner hL W q) = .finite F)
            (bi si : Fin (F.lastIndex + 1)),
          F.link bi = b ∧ bi.1 < si.1 ∧
          ((collisionStop hL W q ∈ (F.link si).path.support ∧
              (F.link si).direction = .forward) ∨
            ∃ l : Link Gamma.graph,
              F.link si = l ∧ l.direction = .backward ∧
              collisionStop hL W q = l.entry) := by
  let J := L.popularAuxiliaryInput hL.legal
  let p := collisionOwner hL W q
  rcases collisionStop_ordered (hL := hL) (W := W) q with
      hstop | hforward | ⟨l, hl, hldir, _hsub, hstop⟩
  · left
    rw [hstop]
  · rcases canonicalErasedRoute_forwardVertex_reached_from_initial_or_priorBackward
        J W p hforward with hroot |
        ⟨b, hb, hbdir, hbowner, hreach,
          F, hroute, bi, fi, hbi, hxfi, hfdir, hlt⟩
    · exact Or.inl hroot
    · exact Or.inr ⟨b, hb, hbdir, hbowner, hreach,
        F, hroute, bi, fi, hbi, hlt, Or.inl ⟨hxfi, hfdir⟩⟩
  · rcases canonicalErasedRoute_backwardLink_entry_reached_from_initial_or_priorBackward
        J W p l hl hldir with hroot |
        ⟨b, hb, hbdir, hbowner, hreach,
          F, hroute, bi, li, hbi, hli, hlt⟩
    · simpa only [hstop] using Or.inl hroot
    · exact Or.inr ⟨b, hb, hbdir, hbowner,
        by simpa only [hstop] using hreach,
        F, hroute, bi, li, hbi, hlt,
        Or.inr ⟨l, hli, hldir, hstop⟩⟩

/-- Root-transfer interface extracted from the strict collision-stop
classification.  Unlike `collisionStop_rooted_of_ownerAnchorReachability`,
the callback is invoked only for a backward anchor whose index is strictly
before a concrete occurrence of the stop. -/
theorem collisionStop_rooted_of_ownerInitial_and_priorBackward
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {W : Popular.XSWarp
      (L.popularAuxiliaryInput hL.legal).lambda
      (L.popularAuxiliaryInput hL.legal).lambda.target}
    (q : WarpPath W) {A : Set V} {E : Set (V × V)}
    (hinitial : ∃ a ∈ A,
      Relation.ReflTransGen (fun u v ↦ (u, v) ∈ E) a
        (canonicalErasedRoute
          (L.popularAuxiliaryInput hL.legal) W
          (collisionOwner hL W q)).initial)
    (hforward :
      (canonicalErasedRoute
        (L.popularAuxiliaryInput hL.legal) W
        (collisionOwner hL W q)).directionEdges .forward ⊆ E)
    (hprior : ∀ (b : Link Gamma.graph),
      b ∈ (canonicalErasedRoute
        (L.popularAuxiliaryInput hL.legal) W
        (collisionOwner hL W q)).links →
      b.direction = .backward →
      (∃ parent ∈ (L.popularAuxiliaryInput hL.legal).ladder.paths,
        b.path.IsSubpathOf parent) →
      ∀ (F : FiniteTrace Gamma.graph)
        (hroute : canonicalErasedRoute
          (L.popularAuxiliaryInput hL.legal) W
          (collisionOwner hL W q) = .finite F)
        (bi si : Fin (F.lastIndex + 1)),
        F.link bi = b → bi.1 < si.1 →
        ((collisionStop hL W q ∈ (F.link si).path.support ∧
            (F.link si).direction = .forward) ∨
          ∃ l : Link Gamma.graph,
            F.link si = l ∧ l.direction = .backward ∧
            collisionStop hL W q = l.entry) →
        ∃ a ∈ A,
          Relation.ReflTransGen (fun u v ↦ (u, v) ∈ E)
            a b.path.start) :
    ∃ a ∈ A,
      Relation.ReflTransGen (fun u v ↦ (u, v) ∈ E) a
        (collisionStop hL W q) := by
  rcases collisionStop_reached_from_ownerInitial_or_priorBackward
      (hL := hL) (W := W) q with hfromInitial |
      ⟨b, hb, hbdir, hbowner, hfromPrior,
        F, hroute, bi, si, hbi, hlt, hoccurs⟩
  · obtain ⟨a, haA, haInitial⟩ := hinitial
    refine ⟨a, haA, haInitial.trans ?_⟩
    exact Relation.ReflTransGen.mono
      (r := fun u v ↦ (u, v) ∈
        (canonicalErasedRoute
          (L.popularAuxiliaryInput hL.legal) W
          (collisionOwner hL W q)).directionEdges .forward)
      (p := fun u v ↦ (u, v) ∈ E)
      (fun _ _ h ↦ hforward h) _ _ hfromInitial
  · obtain ⟨a, haA, haPrior⟩ :=
      hprior b hb hbdir hbowner F hroute bi si hbi hlt hoccurs
    refine ⟨a, haA, haPrior.trans ?_⟩
    exact Relation.ReflTransGen.mono
      (r := fun u v ↦ (u, v) ∈
        (canonicalErasedRoute
          (L.popularAuxiliaryInput hL.legal) W
          (collisionOwner hL W q)).directionEdges .forward)
      (p := fun u v ↦ (u, v) ∈ E)
      (fun _ _ h ↦ hforward h) _ _ hfromPrior

end DWeb.KappaLadder
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.canonicalErasedRoute_orderedVertex_rooted_of_anchorReachability
#print axioms
  Erdos599.DWeb.KappaLadder.collisionStop_rooted_of_ownerAnchorReachability
#print axioms
  Erdos599.Alternating.FiniteTrace.forwardVertex_reached_from_initial_or_priorBackward
#print axioms
  Erdos599.DWeb.KappaLadder.canonicalErasedRoute_forwardVertex_reached_from_initial_or_priorBackward
#print axioms
  Erdos599.DWeb.KappaLadder.canonicalErasedRoute_forwardVertex_rooted_of_priorBackward
#print axioms
  Erdos599.DWeb.KappaLadder.collisionStop_reached_from_ownerInitial_or_priorBackward
#print axioms
  Erdos599.DWeb.KappaLadder.collisionStop_rooted_of_ownerInitial_and_priorBackward
