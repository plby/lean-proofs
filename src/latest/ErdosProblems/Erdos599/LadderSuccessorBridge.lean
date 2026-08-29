/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.LadderExistence
import ErdosProblems.Erdos599.LadderExhaustionLoose
import ErdosProblems.Erdos599.LadderMarkerFreshness

/-!
# Concrete successor arrows for a ladder

This file connects the concrete `DWeb.arrow` operation with the exact
successor relation recorded by `KappaLadder.IsRungArrowResult`.  The two
interfaces deliberately have different shapes: `DWeb.arrow` is the range
of a path-valued function, whereas `IsRungArrowResult` is a relational
totality, uniqueness, and provenance assertion.  `ArrowRealizesRung`
states the precise pointwise compatibility needed to pass between them.

The optional marker is handled separately.  A fresh marker is outside the
old warp and the lifted rung, hence outside their arrow; subtracting its
singleton path therefore recovers exactly the arrow part of the successor.
-/

noncomputable section

namespace Erdos599

open Set DirectedPath

universe u

namespace DirectedPath

namespace Walk

/-- The ordered support remembers the initial vertex without a dependent
nonemptiness witness. -/
@[simp]
theorem head?_support {V : Type u} {D : Digraph V} {a b : V}
    (p : Walk D a b) : p.support.head? = some a := by
  cases p <;> rfl

/-- A finite directed walk is determined by its ordered support list.
Adjacency witnesses are propositions, hence proof irrelevance identifies
them once the vertices and the remaining walk agree. -/
theorem eq_of_support_eq {V : Type u} {D : Digraph V} {a b : V}
    (p q : Walk D a b) (h : p.support = q.support) : p = q := by
  induction p with
  | nil =>
      cases q with
      | nil => rfl
      | cons e q => simp at h
  | @cons a x b e p ih =>
      cases q with
      | nil => simp at h
      | @cons _ y _ f q =>
          simp only [support_cons] at h
          have hpqList : p.support = q.support := List.cons.inj h |>.2
          have hxy : x = y := by
            have hhead := congrArg List.head? hpqList
            simpa only [head?_support, Option.some.injEq] using hhead
          subst y
          have hpq' : p = q := ih q hpqList
          subst q
          rfl

/-- Two simple finite walks with the same endpoints and directed-edge set
are equal.  The initial edge is forced: a later edge cannot have the same
first vertex, since that would repeat the initial vertex of the walk. -/
theorem eq_of_edgeSet_eq {V : Type u} {D : Digraph V} {a b : V}
    (p q : Walk D a b) (hp : p.IsPath) (hq : q.IsPath)
    (hedge : p.edgeSet = q.edgeSet) : p = q := by
  induction p with
  | nil =>
      cases q with
      | nil => rfl
      | @cons _ _ _ e q =>
          exfalso
          have hne : (Walk.cons e q).edgeSet.Nonempty := by
            rw [Walk.edgeSet_cons]
            exact Set.Nonempty.mono Set.subset_union_left (Set.singleton_nonempty _)
          rw [← hedge] at hne
          rcases hne with ⟨z, hz⟩
          exact hz
  | @cons a x b e p ih =>
      cases q with
      | nil =>
          exfalso
          have hne : (Walk.cons e p).edgeSet.Nonempty := by
            rw [Walk.edgeSet_cons]
            exact Set.Nonempty.mono Set.subset_union_left (Set.singleton_nonempty _)
          rw [hedge] at hne
          rcases hne with ⟨z, hz⟩
          exact hz
      | @cons _ y _ f q =>
          have hax : (a, x) ∈
              ({(a, y)} : Set (V × V)) ∪ q.edgeSet := by
            have hmem : (a, x) ∈ (Walk.cons f q).edgeSet := by
              rw [← hedge]
              exact Set.mem_union_left _ (Set.mem_singleton (a, x))
            simpa only [Walk.edgeSet_cons] using hmem
          have hxy : x = y := by
            rcases hax with hhead | htail
            · exact congrArg Prod.snd hhead
            · have haTail : a ∈ q.support :=
                (q.edgeSet_subset_support_prod htail).1
              exact (List.nodup_cons.mp hq).1 haTail |>.elim
          subst y
          have hpNoA : a ∉ p.support := (List.nodup_cons.mp hp).1
          have hqNoA : a ∉ q.support := (List.nodup_cons.mp hq).1
          have htail : p.edgeSet = q.edgeSet := by
            apply Set.Subset.antisymm
            · intro z hz
              have hz' : z ∈ ({(a, x)} : Set (V × V)) ∪ q.edgeSet := by
                have hmem : z ∈ (Walk.cons f q).edgeSet := by
                  rw [← hedge]
                  exact Set.mem_union_right _ hz
                simpa only [Walk.edgeSet_cons] using hmem
              rcases hz' with hzhead | hzq
              · have hza : z = (a, x) := by simpa using hzhead
                subst z
                have haP : a ∈ p.support :=
                  (p.edgeSet_subset_support_prod hz).1
                exact (hpNoA haP).elim
              · exact hzq
            · intro z hz
              have hz' : z ∈ ({(a, x)} : Set (V × V)) ∪ p.edgeSet := by
                have hmem : z ∈ (Walk.cons e p).edgeSet := by
                  rw [hedge]
                  exact Set.mem_union_right _ hz
                simpa only [Walk.edgeSet_cons] using hmem
              rcases hz' with hzhead | hzp
              · have hza : z = (a, x) := by simpa using hzhead
                subst z
                have haQ : a ∈ q.support :=
                  (q.edgeSet_subset_support_prod hz).1
                exact (hqNoA haQ).elim
              · exact hzp
          have hpq : p = q := ih q (List.nodup_cons.mp hp).2
            (List.nodup_cons.mp hq).2 htail
          subst q
          rfl

end Walk

namespace FinitePath

/-- A finite directed path is determined by its two endpoints and its
directed-edge set. -/
theorem eq_of_start_finish_edgeSet_eq {V : Type u} {D : Digraph V}
    (p q : FinitePath D) (hstart : p.start = q.start)
    (hfinish : p.finish = q.finish) (hedge : p.edgeSet = q.edgeSet) :
    p = q := by
  rcases p with ⟨a, b, p, hp⟩
  rcases q with ⟨c, d, q, hq⟩
  dsimp only at hstart hfinish hedge
  subst c
  subst d
  have hpq : p = q := Walk.eq_of_edgeSet_eq p q hp hq hedge
  subst q
  rfl

/-- Selecting the suffix at the initial vertex of a finite path returns
the whole path. -/
theorem suffixFromAux_initial_eq {V : Type u} {D : Digraph V}
    (q : FinitePath D) (hx : q.start ∈ q.support) :
    q.suffixFromAux q.start hx = q := by
  have hsupport : (q.suffixData q.start hx).walk.support = q.walk.support := by
    apply List.Nodup.eq_of_head_mem_of_suffix
      (hne := q.walk.support_ne_nil)
      (q.suffixData_support_suffix q.start hx)
    · simpa only [q.walk.head_support] using
        (q.suffixData q.start hx).walk.start_mem_support
    · exact q.isPath
  have hwalk : (q.suffixData q.start hx).walk = q.walk :=
    Walk.eq_of_support_eq _ _ hsupport
  apply eq_of_start_finish_edgeSet_eq
  · rfl
  · rfl
  · exact congrArg Walk.edgeSet hwalk

end FinitePath

namespace Ray

/-- Selecting the suffix at the initial vertex of a ray returns the ray. -/
theorem suffixFrom_initial_eq {V : Type u} {D : Digraph V}
    (r : Ray D) (hx : r.initial ∈ r.support) :
    r.suffixFrom r.initial hx = r := by
  unfold suffixFrom
  have hzero : Classical.choose hx = 0 := by
    apply r.injective
    simpa only [initial] using Classical.choose_spec hx
  rw [hzero, tail_zero]

/-- A directed ray is determined by its initial vertex and directed-edge
set. -/
theorem eq_of_initial_edgeSet_eq {V : Type u} {D : Digraph V}
    (r s : Ray D) (hinitial : r.initial = s.initial)
    (hedge : r.edgeSet = s.edgeSet) : r = s := by
  apply Ray.ext
  funext n
  induction n with
  | zero => exact hinitial
  | succ n ih =>
      have he : (r n, r (n + 1)) ∈ s.edgeSet := by
        rw [← hedge]
        exact ⟨n, rfl⟩
      obtain ⟨m, hm⟩ := he
      have hmn : m = n := by
        apply s.injective
        calc
          s m = r n := (congrArg Prod.fst hm).symm
          _ = s n := ih
      subst m
      exact congrArg Prod.snd hm

/-- Prepending one vertex contributes exactly its new first edge. -/
theorem edgeSet_prependVertex {V : Type u} {D : Digraph V}
    {u : V} (r : Ray D) (h : D.Adj u r.initial)
    (hu : u ∉ r.support) :
    (r.prependVertex h hu).edgeSet =
      ({(u, r.initial)} : Set (V × V)) ∪ r.edgeSet := by
  ext e
  constructor
  · rintro ⟨n, rfl⟩
    cases n with
    | zero => exact Or.inl (Set.mem_singleton _)
    | succ n =>
        exact Or.inr ⟨n, by
          simp only [prependVertex_apply_succ]⟩
  · rintro (he | he)
    · have heq : e = (u, r.initial) := by simpa using he
      subst e
      exact ⟨0, rfl⟩
    · obtain ⟨n, rfl⟩ := he
      exact ⟨n + 1, by
        simp only [prependVertex_apply_succ]⟩

end Ray

namespace Walk

/-- Directed edges of an appended walk are the union of the two edge
sets. -/
theorem edgeSet_append' {V : Type u} {D : Digraph V}
    {a b c : V} (p : Walk D a b) (q : Walk D b c) :
    (p.append q).edgeSet = p.edgeSet ∪ q.edgeSet := by
  induction p with
  | nil => simp [Walk.edgeSet]
  | cons e p ih =>
      ext z
      simp only [Walk.append, Walk.edgeSet_cons, ih, Set.mem_union,
        Set.mem_singleton_iff]
      tauto

/-- Prepending a finite simple walk to a ray contributes exactly the
finite-walk edges before the ray edges. -/
theorem edgeSet_prependRayAux {V : Type u} {D : Digraph V}
    {a b : V} (p : Walk D a b) (r : Ray D)
    (hp : p.IsPath) (hinit : r.initial = b)
    (hdis : Disjoint p.front r.support) :
    (p.prependRayAux r hp hinit hdis).ray.edgeSet =
      p.edgeSet ∪ r.edgeSet := by
  induction p with
  | nil =>
      simp [prependRayAux]
  | @cons a x b e p ih =>
      rw [prependRayAux]
      rw [Ray.edgeSet_prependVertex]
      rw [(p.prependRayAux r (List.nodup_cons.mp hp).2 hinit
        (hdis.mono (by simp) Set.Subset.rfl)).initial_eq]
      rw [ih (List.nodup_cons.mp hp).2 hinit
        (hdis.mono (by simp) Set.Subset.rfl)]
      rw [Walk.edgeSet_cons]
      exact (Set.union_assoc _ _ _).symm

end Walk

namespace Path

/-- Selecting the suffix of a finite path or ray at its initial vertex
returns the whole path. -/
theorem suffixFrom_initial_eq {V : Type u} {D : Digraph V}
    (q : Path D) (hx : q.initial ∈ q.support) :
    q.suffixFrom q.initial hx = q := by
  rcases q with q | r
  · change Sum.inl (q.suffixFromAux q.start hx) = Sum.inl q
    rw [q.suffixFromAux_initial_eq hx]
  · change Sum.inr (r.suffixFrom r.initial hx) = Sum.inr r
    rw [r.suffixFrom_initial_eq hx]

/-- A finite path or ray is determined by its initial vertex, terminal
option, and directed-edge set. -/
theorem eq_of_initial_terminal_edgeSet_eq {V : Type u} {D : Digraph V}
    (p q : Path D) (hinitial : p.initial = q.initial)
    (hterminal : p.terminal? = q.terminal?)
    (hedge : p.edgeSet = q.edgeSet) : p = q := by
  rcases p with p | r <;> rcases q with q | s
  · apply congrArg Sum.inl
    exact p.eq_of_start_finish_edgeSet_eq q hinitial
      (Option.some.inj hterminal) hedge
  · simp at hterminal
  · simp at hterminal
  · apply congrArg Sum.inr
    exact r.eq_of_initial_edgeSet_eq s hinitial hedge

/-- The directed edges of a splice are the union of the old prefix edges
and the selected suffix edges. -/
theorem edgeSet_appendAt {V : Type u} {D : Digraph V}
    (p : FinitePath D) (q : Path D)
    (hx : p.finish ∈ q.support) (h : Appendable p q hx) :
    (appendAt p q hx h).edgeSet =
      p.edgeSet ∪ (q.suffixFrom p.finish hx).edgeSet := by
  rcases q with q | r
  · change
      (p.walk.append (q.suffixData p.finish hx).walk).edgeSet =
        p.walk.edgeSet ∪ (q.suffixData p.finish hx).walk.edgeSet
    exact p.walk.edgeSet_append' (q.suffixData p.finish hx).walk
  · change
      (p.walk.prependRayAux (r.suffixFrom p.finish hx) p.isPath
        (r.initial_suffixFrom p.finish hx)
        (p.disjoint_front_of_appendableRay r hx h)).ray.edgeSet = _
    exact p.walk.edgeSet_prependRayAux (r.suffixFrom p.finish hx)
      p.isPath (r.initial_suffixFrom p.finish hx)
      (p.disjoint_front_of_appendableRay r hx h)

end Path

end DirectedPath

namespace DWeb
namespace KappaLadder

variable {V : Type u} {G : DWeb V} {kappa : Cardinal.{u}}

/-- The rung at `a`, lifted through the essential quotient stage into the
ambient web. -/
def liftedRung (L : G.KappaLadder kappa) (a : Ladder.Stage kappa) :
    Set G.DPath :=
  L.liftStagePath a '' L.rung a

@[simp]
theorem mem_liftedRung_iff (L : G.KappaLadder kappa)
    (a : Ladder.Stage kappa) (q : G.DPath) :
    q ∈ L.liftedRung a ↔
      ∃ r ∈ L.rung a, L.liftStagePath a r = q :=
  Iff.rfl

@[simp]
theorem support_liftStagePath (L : G.KappaLadder kappa)
    (a : Ladder.Stage kappa) (p : (L.stageWeb a).DPath) :
    (L.liftStagePath a p).support = p.support := by
  unfold liftStagePath
  rw [G.support_liftQuotientPath]
  exact (G.quotient
    (G.terminalFrontier (L.warpAt a))).support_liftEssentialPartPath p

@[simp]
theorem initial_liftStagePath (L : G.KappaLadder kappa)
    (a : Ladder.Stage kappa) (p : (L.stageWeb a).DPath) :
    (L.liftStagePath a p).initial = p.initial := by
  unfold liftStagePath
  rw [G.initial_liftQuotientPath]
  exact (G.quotient
    (G.terminalFrontier (L.warpAt a))).initial_liftEssentialPartPath p

@[simp]
theorem terminal?_liftStagePath (L : G.KappaLadder kappa)
    (a : Ladder.Stage kappa) (p : (L.stageWeb a).DPath) :
    G.terminal? (L.liftStagePath a p) =
      (L.stageWeb a).terminal? p := by
  rcases p with p | p <;> rfl

/-- Lifting a rung changes neither the vertices of its paths nor the
vertex set of the family. -/
theorem vertexSet_liftedRung (L : G.KappaLadder kappa)
    (a : Ladder.Stage kappa) :
    G.vertexSet (L.liftedRung a) =
      (L.stageWeb a).vertexSet (L.rung a) := by
  ext x
  constructor
  · rintro ⟨q, ⟨r, hr, rfl⟩, hxr⟩
    refine ⟨r, hr, ?_⟩
    rwa [L.support_liftStagePath a r] at hxr
  · rintro ⟨r, hr, hxr⟩
    refine ⟨L.liftStagePath a r, ⟨r, hr, rfl⟩, ?_⟩
    rwa [L.support_liftStagePath a r]

/-- A lifted rung path can meet the old terminal frontier only at its
initial vertex. -/
theorem eq_initial_of_mem_liftStagePath_of_mem_terminalFrontier
    (L : G.KappaLadder kappa) (a : Ladder.Stage kappa)
    (r : (L.stageWeb a).DPath) {x : V}
    (hxr : x ∈ (L.liftStagePath a r).support)
    (hxT : x ∈ G.terminalFrontier (L.warpAt a)) :
    x = r.initial := by
  by_contra hne
  let Q := G.quotient (G.terminalFrontier (L.warpAt a))
  let r' : Q.essentialPart.DPath := r
  let q : Q.DPath := Q.liftEssentialPartPath r'
  have hxr' : x ∈ r.support := by
    rwa [L.support_liftStagePath a r] at hxr
  have hxq : x ∈ q.support := by
    dsimp only [q]
    rw [Q.support_liftEssentialPartPath]
    exact hxr'
  have hneq : x ≠ q.initial := by
    dsimp only [q]
    rw [Q.initial_liftEssentialPartPath]
    exact hne
  exact (G.quotientPath_avoids_after_initial
    (G.terminalFrontier (L.warpAt a)) q hxq hneq).2 hxT

/-- Self-roofing of the old family makes every rung path starting at an
old finite terminal a clean candidate for the concrete arrow. -/
theorem clean_liftStagePath_of_selfRoof
    (L : G.KappaLadder kappa) (a : Ladder.Stage kappa)
    (hself : G.vertexSet (L.warpAt a) ⊆
      G.roof (G.terminalFrontier (L.warpAt a)))
    (f : FinitePath G.graph) (hf : (Sum.inl f : G.DPath) ∈ L.warpAt a)
    (r : (L.stageWeb a).DPath) (hstart : r.initial = f.finish) :
    let hfinish : f.finish ∈ (L.liftStagePath a r).support := by
      rw [← hstart, ← L.initial_liftStagePath a r]
      exact Path.initial_mem_support _
    ((L.liftStagePath a r).suffixFrom f.finish hfinish).support ∩
        G.vertexSet (L.warpAt a) = {f.finish} := by
  dsimp only
  let hfinish : f.finish ∈ (L.liftStagePath a r).support := by
    rw [← hstart, ← L.initial_liftStagePath a r]
    exact Path.initial_mem_support _
  have hinitial : (L.liftStagePath a r).initial = f.finish := by
    rw [L.initial_liftStagePath, hstart]
  rw [show (L.liftStagePath a r).suffixFrom f.finish hfinish =
      L.liftStagePath a r by
    simpa only [hinitial] using
      (Path.suffixFrom_initial_eq (L.liftStagePath a r)
        (Path.initial_mem_support _))]
  ext x
  constructor
  · rintro ⟨hxr, hxOld⟩
    have hxRoof := hself hxOld
    by_cases hxi : x = f.finish
    · simpa [hxi]
    · have hxne : x ≠ r.initial := by simpa [hstart] using hxi
      let Q := G.quotient (G.terminalFrontier (L.warpAt a))
      let r' : Q.essentialPart.DPath := r
      let q : Q.DPath := Q.liftEssentialPartPath r'
      have hxr' : x ∈ r.support := by
        rwa [L.support_liftStagePath a r] at hxr
      have hxq : x ∈ q.support := by
        dsimp only [q]
        rw [Q.support_liftEssentialPartPath]
        exact hxr'
      have hxqne : x ≠ q.initial := by
        dsimp only [q]
        rw [Q.initial_liftEssentialPartPath]
        exact hxne
      have hav := G.quotientPath_avoids_after_initial
        (G.terminalFrontier (L.warpAt a)) q hxq hxqne
      have hxEssential : x ∈
          G.essential (G.terminalFrontier (L.warpAt a)) := by
        by_contra hxNotEssential
        exact hav.1 ⟨hxRoof, hxNotEssential⟩
      exact (hav.2 (G.essential_subset _ hxEssential)).elim
  · intro hx
    have hxeq : x = f.finish := by simpa using hx
    subst x
    exact ⟨hfinish, ⟨Sum.inl f, hf, f.finish_mem_support⟩⟩

/-- A matching rung path supplies an arrow candidate. -/
noncomputable def arrowCandidate_of_rung
    (L : G.KappaLadder kappa) (a : Ladder.Stage kappa)
    (hself : G.vertexSet (L.warpAt a) ⊆
      G.roof (G.terminalFrontier (L.warpAt a)))
    (f : FinitePath G.graph) (hf : (Sum.inl f : G.DPath) ∈ L.warpAt a)
    (r : (L.stageWeb a).DPath) (hr : r ∈ L.rung a)
    (hstart : r.initial = f.finish) :
    G.ArrowCandidate (L.warpAt a) (L.liftedRung a) f := by
  let hfinish : f.finish ∈ (L.liftStagePath a r).support := by
    rw [← hstart, ← L.initial_liftStagePath a r]
    exact Path.initial_mem_support _
  exact
    { path := L.liftStagePath a r
      mem_path := ⟨r, hr, rfl⟩
      finish_mem := hfinish
      clean := L.clean_liftStagePath_of_selfRoof a hself f hf r hstart }

/-- Every concrete arrow candidate through the lifted rung meets its
selected rung path at that path's initial vertex. -/
theorem arrowCandidate_rung_data
    (L : G.KappaLadder kappa) (a : Ladder.Stage kappa)
    (f : FinitePath G.graph) (hf : (Sum.inl f : G.DPath) ∈ L.warpAt a)
    (c : G.ArrowCandidate (L.warpAt a) (L.liftedRung a) f) :
    ∃ r ∈ L.rung a,
      c.path = L.liftStagePath a r ∧ f.finish = r.initial := by
  rcases c.mem_path with ⟨r, hr, hrc⟩
  refine ⟨r, hr, hrc.symm, ?_⟩
  apply L.eq_initial_of_mem_liftStagePath_of_mem_terminalFrontier a r
  · simpa only [hrc] using c.finish_mem
  · exact ⟨Sum.inl f, hf, rfl⟩

/-- Under the canonical self-roofing invariant, the concrete functional
arrow sends every old path to a rung-arrow successor. -/
theorem isRungArrowPair_arrowPath_of_isWarp_selfRoof
    (L : G.KappaLadder kappa) (a : Ladder.Stage kappa)
    (_hwarp : G.IsWarp (L.warpAt a))
    (hself : G.vertexSet (L.warpAt a) ⊆
      G.roof (G.terminalFrontier (L.warpAt a)))
    (p : G.DPath) (hp : p ∈ L.warpAt a) :
    L.IsRungArrowPair a p
      (G.arrowPath (L.warpAt a) (L.liftedRung a) ⟨p, hp⟩) := by
  classical
  rcases p with f | ray
  · refine Or.inr ⟨f.finish, rfl, ?_⟩
    by_cases hc : Nonempty
        (G.ArrowCandidate (L.warpAt a) (L.liftedRung a) f)
    · let c : G.ArrowCandidate (L.warpAt a) (L.liftedRung a) f :=
        Classical.choice hc
      have harrow :
          G.arrowPath (L.warpAt a) (L.liftedRung a) ⟨Sum.inl f, hp⟩ =
            Path.appendAt f c.path c.finish_mem (c.appendable hp) := by
        change G.arrowFinite (L.warpAt a) (L.liftedRung a) f hp = _
        rw [arrowFinite, dif_pos hc]
      rcases L.arrowCandidate_rung_data a f hp c with
        ⟨r, hr, hcpath, hfinish⟩
      let r' : (L.stageWeb a).DPath := r
      have hr' : r' ∈ L.rung a := hr
      have hcpath' : c.path = L.liftStagePath a r' := hcpath
      have hfinish' : f.finish = r'.initial := hfinish
      have hinitial : (L.liftStagePath a r').initial = f.finish := by
        exact (L.initial_liftStagePath a r').trans hfinish'.symm
      have hsuffix : c.path.suffixFrom f.finish c.finish_mem =
          L.liftStagePath a r' := by
        have hcinitial : c.path.initial = f.finish := hcpath' ▸ hinitial
        have hwhole : c.path.suffixFrom f.finish c.finish_mem = c.path := by
          simpa only [hcinitial] using
            (Path.suffixFrom_initial_eq c.path (Path.initial_mem_support _))
        exact hwhole.trans hcpath'
      refine Or.inl ⟨r', hfinish'.symm, ?_⟩
      refine ⟨hr', ?_, ?_, ?_, ?_, ?_⟩
      · exact congrArg some hfinish'
      · rw [harrow]
        exact Path.extends_appendAt f c.path c.finish_mem (c.appendable hp)
      · rw [harrow, Path.support_appendAt, hsuffix]
        rfl
      · rw [harrow, pathEdgeSet, Path.edgeSet_appendAt, hsuffix]
        rfl
      · rw [harrow]
        exact (Path.terminal?_appendAt f c.path c.finish_mem
          (c.appendable hp)).trans (congrArg G.terminal? hcpath')
    · refine Or.inr ⟨?_, ?_⟩
      · rintro ⟨r, hr, hstart⟩
        apply hc
        exact ⟨L.arrowCandidate_of_rung a hself f hp r hr hstart⟩
      · change G.arrowFinite (L.warpAt a) (L.liftedRung a) f hp = _
        rw [arrowFinite, dif_neg hc]
  · exact Or.inl ⟨rfl, G.arrowPath_ray
      (L.warpAt a) (L.liftedRung a) ray hp⟩

/-- Rung-arrow successors are functional when the rung is a warp. -/
theorem isRungArrowPair_unique_of_rungWarp
    (L : G.KappaLadder kappa) (a : Ladder.Stage kappa)
    (hrungWarp : (L.stageWeb a).IsWarp (L.rung a))
    (p q₁ q₂ : G.DPath)
    (h₁ : L.IsRungArrowPair a p q₁)
    (h₂ : L.IsRungArrowPair a p q₂) : q₁ = q₂ := by
  rcases h₁ with ⟨hpNone, rfl⟩ |
      ⟨x₁, hpSome₁, hcase₁⟩
  · rcases h₂ with ⟨_hpNone₂, rfl⟩ |
      ⟨x₂, hpSome₂, _hcase₂⟩
    · rfl
    · rw [hpNone] at hpSome₂
      cases hpSome₂
  · rcases h₂ with ⟨hpNone₂, rfl⟩ |
      ⟨x₂, hpSome₂, hcase₂⟩
    · rw [hpNone₂] at hpSome₁
      cases hpSome₁
    · have hx : x₁ = x₂ := Option.some.inj (hpSome₁.symm.trans hpSome₂)
      subst x₂
      rcases hcase₁ with ⟨r₁, hr₁Initial, hc₁⟩ |
          ⟨hno₁, rfl⟩
      · rcases hcase₂ with ⟨r₂, hr₂Initial, hc₂⟩ |
            ⟨hno₂, rfl⟩
        · have hrEq : r₁ = r₂ := by
            by_contra hne
            have hdis := hrungWarp hc₁.1 hc₂.1 hne
            exact Set.disjoint_left.1 hdis
              (Path.initial_mem_support r₁)
              (by rw [hr₁Initial, ← hr₂Initial]
                  exact Path.initial_mem_support r₂)
          have hinitial : q₁.initial = q₂.initial :=
            (G.extends_initial hc₁.2.2.1).symm.trans
              (G.extends_initial hc₂.2.2.1)
          have hterminal : G.terminal? q₁ = G.terminal? q₂ := by
            rw [hc₁.2.2.2.2.2, hc₂.2.2.2.2.2, hrEq]
          have hedge : q₁.edgeSet = q₂.edgeSet := by
            change pathEdgeSet q₁ = pathEdgeSet q₂
            rw [hc₁.2.2.2.2.1, hc₂.2.2.2.2.1, hrEq]
          exact Path.eq_of_initial_terminal_edgeSet_eq
            q₁ q₂ hinitial hterminal hedge
        · exact (hno₂ ⟨r₁, hc₁.1, hr₁Initial⟩).elim
      · rcases hcase₂ with ⟨r₂, hr₂Initial, hc₂⟩ |
            ⟨_hno₂, rfl⟩
        · exact (hno₁ ⟨r₂, hc₂.1, hr₂Initial⟩).elim
        · rfl

/-- Pointwise statement that the functional source-arrow operation realizes
exactly the ladder's relational rung-arrow specification.  The reverse
implication includes the functionality needed by `IsRungArrowResult`; it is
not merely a membership assertion. -/
def ArrowRealizesRung (L : G.KappaLadder kappa)
    (a : Ladder.Stage kappa) : Prop :=
  ∀ (p : G.DPath) (hp : p ∈ L.warpAt a) (q : G.DPath),
    L.IsRungArrowPair a p q ↔
      q = G.arrowPath (L.warpAt a) (L.liftedRung a) ⟨p, hp⟩

/-- If the rung is the trivial wave, every relational rung-arrow successor
is the original path. -/
theorem eq_self_of_isRungArrowPair_of_rung_eq_trivialWave
    (L : G.KappaLadder kappa) (a : Ladder.Stage kappa)
    (hrung : L.rung a = (L.stageWeb a).trivialWave)
    {p q : G.DPath} (hpq : L.IsRungArrowPair a p q) : q = p := by
  rcases hpq with ⟨_hpNone, rfl⟩ |
      ⟨x, hpSome, hcase⟩
  · rfl
  · rcases hcase with ⟨r, _hrInitial, hc⟩ | ⟨_hno, rfl⟩
    · have hr : r ∈ (L.stageWeb a).trivialWave := hrung ▸ hc.1
      rcases hr with ⟨y, hy, rfl⟩
      have hlift : L.liftStagePath a ((L.stageWeb a).trivialPath y) =
          G.trivialPath y := by
        rfl
      have hinitial : q.initial = p.initial :=
        (G.extends_initial hc.2.2.1).symm
      have hterminal : G.terminal? q = G.terminal? p := by
        rw [hc.2.2.2.2.2, hlift, G.terminal?_trivialPath]
        exact hc.2.1.symm
      have hedge : q.edgeSet = p.edgeSet := by
        change pathEdgeSet q = pathEdgeSet p
        rw [hc.2.2.2.2.1, hlift]
        change p.edgeSet ∪ (∅ : Set (V × V)) = p.edgeSet
        exact Set.union_empty _
      exact Path.eq_of_initial_terminal_edgeSet_eq
        q p hinitial hterminal hedge
    · rfl

/-- Consequently the concrete arrow through a trivial rung is literally
the old family. -/
theorem arrow_eq_of_rung_eq_trivialWave
    (L : G.KappaLadder kappa) (a : Ladder.Stage kappa)
    (hrealize : L.ArrowRealizesRung a)
    (hrung : L.rung a = (L.stageWeb a).trivialWave) :
    G.arrow (L.warpAt a) (L.liftedRung a) = L.warpAt a := by
  ext q
  constructor
  · rintro ⟨p, rfl⟩
    have hpair := (hrealize p.1 p.2 _).2 rfl
    exact (L.eq_self_of_isRungArrowPair_of_rung_eq_trivialWave
      a hrung hpair) ▸ p.2
  · intro hq
    refine ⟨⟨q, hq⟩, ?_⟩
    have hpair := (hrealize q hq _).2 rfl
    exact (L.eq_self_of_isRungArrowPair_of_rung_eq_trivialWave
      a hrung hpair)

/-- The concrete arrow is an exact rung-arrow result as soon as its
pointwise graph agrees with `IsRungArrowPair`. -/
theorem isRungArrowResult_arrow (L : G.KappaLadder kappa)
    (a : Ladder.Stage kappa) (hrealize : L.ArrowRealizesRung a) :
    L.IsRungArrowResult a
      (G.arrow (L.warpAt a) (L.liftedRung a)) := by
  constructor
  · intro p hp
    let q := G.arrowPath (L.warpAt a) (L.liftedRung a) ⟨p, hp⟩
    refine ⟨q, ⟨⟨⟨p, hp⟩, rfl⟩, (hrealize p hp q).2 rfl⟩, ?_⟩
    intro r hr
    exact (hrealize p hp r).1 hr.2
  · rintro q ⟨p, rfl⟩
    exact ⟨p.1, p.2, (hrealize p.1 p.2 _).2 rfl⟩

/-- A singleton marker path is disjoint, as a family of paths, from any
family whose vertex set does not contain the marker. -/
theorem disjoint_singleton_trivialPath_of_not_mem_vertexSet
    (G : DWeb V) (U : Set G.DPath) (y : V)
    (hy : y ∉ G.vertexSet U) :
    Disjoint U ({G.trivialPath y} : Set G.DPath) := by
  rw [Set.disjoint_left]
  intro p hpU hpMarker
  have hp : p = G.trivialPath y := by simpa using hpMarker
  apply hy
  refine ⟨p, hpU, ?_⟩
  rw [hp, G.support_trivialPath]
  exact Set.mem_singleton y

/-- If the chosen marker is outside the concrete arrow's vertex set, its
optional marker family is disjoint from the arrow family.  The no-marker
case is automatic. -/
theorem disjoint_arrow_markerPathSet
    (L : G.KappaLadder kappa) (a : Ladder.Stage kappa)
    (houtside : ∀ y : V, L.marker a = some y →
      y ∉ G.vertexSet (G.arrow (L.warpAt a) (L.liftedRung a))) :
    Disjoint (G.arrow (L.warpAt a) (L.liftedRung a))
      (L.markerPathSet a) := by
  cases hmarker : L.marker a with
  | none => simp [markerPathSet, hmarker]
  | some y =>
      simpa only [markerPathSet, hmarker] using
        disjoint_singleton_trivialPath_of_not_mem_vertexSet G
          (G.arrow (L.warpAt a) (L.liftedRung a)) y
          (houtside y hmarker)

/-- Removing a disjoint optional marker from an arrow-plus-marker successor
recovers the concrete arrow exactly. -/
theorem arrowPart_eq_arrow_of_successor_eq
    (L : G.KappaLadder kappa) (a : Ladder.Stage kappa)
    (hsucc : L.successorWarp a =
      G.arrow (L.warpAt a) (L.liftedRung a) ∪ L.markerPathSet a)
    (hdis : Disjoint (G.arrow (L.warpAt a) (L.liftedRung a))
      (L.markerPathSet a)) :
    L.arrowPart a = G.arrow (L.warpAt a) (L.liftedRung a) := by
  ext p
  rw [arrowPart, hsucc]
  constructor
  · rintro ⟨hpArrow | hpMarker, hpNotMarker⟩
    · exact hpArrow
    · exact (hpNotMarker hpMarker).elim
  · intro hpArrow
    exact ⟨Or.inl hpArrow, fun hpMarker ↦
      Set.disjoint_left.1 hdis hpArrow hpMarker⟩

/-- Stagewise constructor for the exact successor-arrow clause. -/
theorem exactSuccessorArrowAt_of_arrow
    (L : G.KappaLadder kappa) (a : Ladder.Stage kappa)
    (hrealize : L.ArrowRealizesRung a)
    (hsucc : L.successorWarp a =
      G.arrow (L.warpAt a) (L.liftedRung a) ∪ L.markerPathSet a)
    (hdis : Disjoint (G.arrow (L.warpAt a) (L.liftedRung a))
      (L.markerPathSet a)) :
    L.IsRungArrowResult a (L.arrowPart a) ∧
      L.successorWarp a = L.arrowPart a ∪ L.markerPathSet a := by
  have hpart := L.arrowPart_eq_arrow_of_successor_eq a hsucc hdis
  constructor
  · rw [hpart]
    exact L.isRungArrowResult_arrow a hrealize
  · rw [hpart]
    exact hsucc

/-- Family-level constructor for `HasExactSuccessorArrows`. -/
theorem hasExactSuccessorArrows_of_arrow
    (L : G.KappaLadder kappa)
    (hrealize : ∀ a : Ladder.Stage kappa, L.ArrowRealizesRung a)
    (hsucc : ∀ a : Ladder.Stage kappa, L.successorWarp a =
      G.arrow (L.warpAt a) (L.liftedRung a) ∪ L.markerPathSet a)
    (hdis : ∀ a : Ladder.Stage kappa,
      Disjoint (G.arrow (L.warpAt a) (L.liftedRung a))
        (L.markerPathSet a)) :
    L.HasExactSuccessorArrows := by
  intro a
  exact L.exactSuccessorArrowAt_of_arrow a (hrealize a) (hsucc a) (hdis a)

/-- The functional arrow is pointwise a rung-arrow pair, together with
functionality of the relational specification, is enough to establish the
bidirectional realization condition. -/
theorem arrowRealizesRung_of_pair_unique
    (L : G.KappaLadder kappa) (a : Ladder.Stage kappa)
    (hpair : ∀ (p : G.DPath) (hp : p ∈ L.warpAt a),
      L.IsRungArrowPair a p
        (G.arrowPath (L.warpAt a) (L.liftedRung a) ⟨p, hp⟩))
    (hunique : ∀ (p : G.DPath) (hp : p ∈ L.warpAt a)
      (q r : G.DPath), L.IsRungArrowPair a p q →
        L.IsRungArrowPair a p r → q = r) :
    L.ArrowRealizesRung a := by
  intro p hp q
  constructor
  · intro hq
    exact hunique p hp q _ hq (hpair p hp)
  · rintro rfl
    exact hpair p hp

/-- The canonical warp and self-roof invariants make the concrete arrow
exactly realize the rung relation. -/
theorem arrowRealizesRung_of_isWarp_selfRoof
    (L : G.KappaLadder kappa) (a : Ladder.Stage kappa)
    (hwarp : G.IsWarp (L.warpAt a))
    (hself : G.vertexSet (L.warpAt a) ⊆
      G.roof (G.terminalFrontier (L.warpAt a)))
    (hrungWarp : (L.stageWeb a).IsWarp (L.rung a)) :
    L.ArrowRealizesRung a := by
  apply L.arrowRealizesRung_of_pair_unique a
  · exact L.isRungArrowPair_arrowPath_of_isWarp_selfRoof a hwarp hself
  · intro p _hp q r hq hr
    exact L.isRungArrowPair_unique_of_rungWarp a hrungWarp p q r hq hr

/-- A successor presented as an arrow-plus-marker satisfies the exact
successor clause when the pointwise arrow is a rung pair, rung pairs are
functional, and the selected marker lies outside the arrow. -/
theorem exactSuccessorArrowAt_of_pair_unique
    (L : G.KappaLadder kappa) (a : Ladder.Stage kappa)
    (hpair : ∀ (p : G.DPath) (hp : p ∈ L.warpAt a),
      L.IsRungArrowPair a p
        (G.arrowPath (L.warpAt a) (L.liftedRung a) ⟨p, hp⟩))
    (hunique : ∀ (p : G.DPath) (hp : p ∈ L.warpAt a)
      (q r : G.DPath), L.IsRungArrowPair a p q →
        L.IsRungArrowPair a p r → q = r)
    (hsucc : L.successorWarp a =
      G.arrow (L.warpAt a) (L.liftedRung a) ∪ L.markerPathSet a)
    (houtside : ∀ y : V, L.marker a = some y →
      y ∉ G.vertexSet (G.arrow (L.warpAt a) (L.liftedRung a))) :
    L.IsRungArrowResult a (L.arrowPart a) ∧
      L.successorWarp a = L.arrowPart a ∪ L.markerPathSet a := by
  apply L.exactSuccessorArrowAt_of_arrow a
      (L.arrowRealizesRung_of_pair_unique a hpair hunique) hsucc
  exact L.disjoint_arrow_markerPathSet a houtside

/-- The canonical ladder has the exact source-arrow successor geometry at
every stage, including the frozen stages after marker exhaustion. -/
theorem canonicalLadder_hasExactSuccessorArrows
    (preferred : Ladder.Stage kappa → Option V)
    (hNoEnter : G.NoEdgeEnters G.source) :
    (canonicalLadder G kappa preferred).HasExactSuccessorArrows := by
  classical
  let L := canonicalLadder G kappa preferred
  intro a
  let s := G.canonicalLadderState kappa preferred
    (Ladder.Stage.toExtended a)
  have hwarpState : L.warpAt a = s.1 := rfl
  have hliftedState : L.liftedRung a =
      G.liftedLadderRungOfState s := rfl
  have hmarkerState : L.markerPathSet a =
      G.ladderMarkerPathSetOfState (preferred a) s := rfl
  have hinv : CanonicalRecursionInvariant (G := G)
      (G.ladderSuccessorState
        (extendLadderPreference kappa preferred)) a.1 :=
    canonicalRecursionInvariant_all hNoEnter
      (extendLadderPreference kappa preferred) a.1
  have hwarp : G.IsWarp (L.warpAt a) := by
    change G.IsWarp s.1
    exact hinv.warp
  have hself : G.vertexSet (L.warpAt a) ⊆
      G.roof (G.terminalFrontier (L.warpAt a)) := by
    change G.vertexSet s.1 ⊆ G.roof (G.terminalFrontier s.1)
    exact hinv.selfRoof
  have hrungWarp : (L.stageWeb a).IsWarp (L.rung a) := by
    exact ((G.canonicalLadderCore kappa preferred).stageWeb a)
      |>.chosenMaximalWave.property.1
  have hrealize : L.ArrowRealizesRung a :=
    L.arrowRealizesRung_of_isWarp_selfRoof a hwarp hself hrungWarp
  have hcontact : G.LadderStateContactsStageSource s :=
    G.ladderStateContactsStageSource_of_roofs s
      hinv.sourceRoof hinv.selfRoof
  have hdis : Disjoint
      (G.arrow (L.warpAt a) (L.liftedRung a))
      (L.markerPathSet a) := by
    change Disjoint
      (G.arrow s.1 (G.liftedLadderRungOfState s))
      (G.ladderMarkerPathSetOfState (preferred a) s)
    exact G.disjoint_arrow_ladderMarkerPathSetOfState
      (preferred a) s hinv.warp hcontact
  have hsuccState : L.successorWarp a =
      (G.ladderSuccessorState
        (extendLadderPreference kappa preferred) a.1 s).1 := by
    exact congrArg Prod.fst
      (G.canonicalLadderState_succ kappa preferred a)
  have hsucc : L.successorWarp a =
      G.arrow (L.warpAt a) (L.liftedRung a) ∪
        L.markerPathSet a := by
    by_cases hactive : s.2 = true
    · rw [hsuccState, ladderSuccessorState, dif_pos hactive]
      simp only [Prod.fst]
      rw [extendLadderPreference_stage, hwarpState,
        hliftedState, hmarkerState]
      rfl
    · have hfrozen := G.ladderAccumulatedStateAux_inactive_frozen
          hNoEnter (extendLadderPreference kappa preferred) a.1
          (by exact hactive)
      have hloose : (L.stageWeb a).IsLoose := by
        exact hfrozen.2
      have hrung : L.rung a = (L.stageWeb a).trivialWave := by
        exact (L.stageWeb a).chosenMaximalWave_eq_trivialWave hloose
      have harrow :
          G.arrow (L.warpAt a) (L.liftedRung a) = L.warpAt a :=
        L.arrow_eq_of_rung_eq_trivialWave a hrealize hrung
      have hmarker : L.marker a = none := by
        change G.ladderMarkerOfState (preferred a) s = none
        exact G.ladderMarkerOfState_eq_none_of_inactive
          (preferred a) s hactive
      rw [hsuccState, ladderSuccessorState, dif_neg hactive,
        harrow]
      simpa [markerPathSet, hmarker] using hwarpState.symm
  exact L.exactSuccessorArrowAt_of_arrow a hrealize hsucc hdis

/-- All construction laws for the canonical ladder except the genuinely
source-sensitive hanging-record provenance are automatic.  Keeping this
wrapper after the successor and frozen-stage developments avoids the import
cycle which would arise if `LadderExistence` imported those developments
directly. -/
theorem canonicalLadderWithBookkeeping_isLegal_of_hangingProvenance
    (preferred : Ladder.Stage kappa → Option V)
    (hkappa : kappa.IsRegular)
    (hkappaUncountable : Cardinal.aleph0 < kappa)
    (hNoEnter : G.NoEdgeEnters G.source)
    (hhanging :
      (canonicalLadder G kappa preferred).HasHangingProvenance) :
    (canonicalLadder G kappa preferred).IsLegal := by
  apply canonicalLadderWithBookkeeping_isLegal preferred
    hkappa hkappaUncountable hNoEnter
  · exact canonicalLadder_hasExactSuccessorArrows preferred hNoEnter
  · exact canonicalLadderWithBookkeeping_marker_none_iff_candidates_empty
      preferred hNoEnter
  · exact canonicalLadderWithBookkeeping_marksTimeAfterExhaustion
      preferred hNoEnter
  · exact hhanging

/-- Existential packaging of the canonical construction after all local
successor, limit, marker, and maximal-rung obligations have been discharged.
Only hanging-record provenance remains an explicit input. -/
theorem exists_legalLadder_with_maximalRungs_of_hangingProvenance
    (preferred : Ladder.Stage kappa → Option V)
    (hkappa : kappa.IsRegular)
    (hkappaUncountable : Cardinal.aleph0 < kappa)
    (hNoEnter : G.NoEdgeEnters G.source)
    (hhanging :
      (canonicalLadder G kappa preferred).HasHangingProvenance) :
    ∃ L : G.KappaLadder kappa, L.IsLegal ∧ L.HasRoofMaximalRungs := by
  let L := canonicalLadder G kappa preferred
  have hlegal : L.IsLegal :=
    canonicalLadderWithBookkeeping_isLegal_of_hangingProvenance
      preferred hkappa hkappaUncountable hNoEnter hhanging
  exact ⟨L, hlegal, hlegal.roofMaximalRungs⟩

end KappaLadder
end DWeb
end Erdos599
