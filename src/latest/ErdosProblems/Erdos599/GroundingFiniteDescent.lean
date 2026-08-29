/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingCutDecoder
import ErdosProblems.Erdos599.SafeSwitching

/-!
# The well-founded core of Assertion 8.18

The descent in Aharoni--Berger, Assertion 8.18, repeatedly replaces the
current last encounter of the finite original path by an earlier encounter.
The graph-theoretic work at one step is substantial: it constructs the
surviving ladder fragment, traverses it backwards, and splices the resulting
route to an escaping auxiliary path.  Termination, however, uses only the
strict decrease of the encounter position on the finite path.

This file records that termination argument without hiding any of the
graph-theoretic content.  A `PathCompiler` must provide an initial decoded
record and, for every record, either the requested cut-avoiding auxiliary
source--target path or another record at a strictly earlier position.  The
last theorem turns compilers for all original paths into the literal
`GroundingCut.FiniteDescentDecoder` consumed by Assertion 8.18.
-/

noncomputable section

namespace Erdos599
namespace GroundingFiniteDescent

open Set DirectedPath

universe u v

variable {V : Type u} {I : Type v} {Gamma : DWeb V}

abbrev Input (Gamma : DWeb V) (I : Type v) : Type (max u v) :=
  PopularAuxiliary.Input Gamma I

abbrev LV (L : Input Gamma I) : Type (max u v) :=
  PopularAuxiliary.Input.LambdaVertex V I

/-! ## Surviving components of one ladder path -/

open Alternating
open Alternating.RelationDecomposition

private theorem Ray.edgeSet_not_containsDirectedCycle
    {D : Digraph V} (r : Ray D) :
    ¬ ContainsDirectedCycle r.edgeSet := by
  rintro ⟨K, hK⟩
  let i0 : Fin K.length := ⟨0, K.positive⟩
  obtain ⟨n0, hn0⟩ := hK ⟨i0, rfl⟩
  have hzero : K.vertex i0 = r n0 := congrArg Prod.fst hn0
  have hvertex : ∀ n : ℕ, ∀ hn : n < K.length,
      K.vertex ⟨n, hn⟩ = r (n0 + n) := by
    intro n
    induction n with
    | zero =>
        intro hn
        simpa [i0] using hzero
    | succ n ih =>
        intro hn
        have hn' : n < K.length := Nat.lt_trans (Nat.lt_succ_self n) hn
        let i : Fin K.length := ⟨n, hn'⟩
        have hnext : K.next i = ⟨n + 1, hn⟩ := by
          apply Fin.ext
          exact Nat.mod_eq_of_lt hn
        obtain ⟨m, hm⟩ := hK ⟨i, rfl⟩
        have hsource : K.vertex i = r m := congrArg Prod.fst hm
        have htarget : K.vertex (K.next i) = r (m + 1) :=
          congrArg Prod.snd hm
        have hm_eq : m = n0 + n := by
          apply r.injective
          exact hsource.symm.trans (ih hn')
        rw [hnext, hm_eq] at htarget
        simpa [Nat.add_assoc] using htarget
  let last := K.length - 1
  have hlast : last < K.length := Nat.sub_lt K.positive (by omega)
  let iLast : Fin K.length := ⟨last, hlast⟩
  have hnextLast : K.next iLast = i0 := by
    apply Fin.ext
    have hs : last + 1 = K.length := Nat.sub_add_cancel K.positive
    simp [DirectedCycle.next, iLast, i0, hs]
  obtain ⟨m, hm⟩ := hK ⟨iLast, rfl⟩
  have hsource : K.vertex iLast = r m := congrArg Prod.fst hm
  have htarget : K.vertex (K.next iLast) = r (m + 1) :=
    congrArg Prod.snd hm
  have hm_eq : m = n0 + last := by
    apply r.injective
    exact hsource.symm.trans (hvertex last hlast)
  have hreturn : r n0 = r (n0 + K.length) := by
    rw [hnextLast, hm_eq] at htarget
    rw [Nat.add_assoc, Nat.sub_add_cancel K.positive] at htarget
    exact hzero.symm.trans htarget
  have := r.injective hreturn
  omega

private theorem FinitePath.edgeSet_not_containsReverseDirectedRay
    {D : Digraph V} (p : FinitePath D) :
    ¬ ContainsReverseDirectedRay p.edgeSet := by
  rintro ⟨R, hR⟩
  have hall : ∀ n : ℕ, R.vertex n ∈ p.support := by
    intro n
    cases n with
    | zero => exact (p.edgeSet_subset_support_prod (hR 0)).2
    | succ n => exact (p.edgeSet_subset_support_prod (hR n)).1
  exact p.support_finite.not_infinite
    (Set.infinite_of_injective_forall_mem R.injective hall)

private theorem Ray.edgeSet_not_containsReverseDirectedRay
    {D : Digraph V} (r : Ray D) :
    ¬ ContainsReverseDirectedRay r.edgeSet := by
  rintro ⟨R, hR⟩
  let f : ℕ → ℕ := fun n ↦ Classical.choose (hR n)
  have hf (n : ℕ) :
      (R.vertex (n + 1), R.vertex n) = (r (f n), r (f n + 1)) :=
    Classical.choose_spec (hR n)
  have hstep (n : ℕ) : f (n + 1) + 1 = f n := by
    apply r.injective
    exact (congrArg Prod.snd (hf (n + 1))).symm.trans
      (congrArg Prod.fst (hf n))
  have hsum : ∀ n : ℕ, f n + n = f 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        calc
          f (n + 1) + (n + 1) = (f (n + 1) + 1) + n := by omega
          _ = f n + n := by rw [hstep]
          _ = f 0 := ih
  have := hsum (f 0 + 1)
  omega

private theorem Path.edgeSet_not_containsDirectedCycle
    {D : Digraph V} (p : Path D) :
    ¬ ContainsDirectedCycle p.edgeSet := by
  rcases p with p | r
  · exact Alternating.FinitePath.edgeSet_not_containsDirectedCycle p
  · exact Ray.edgeSet_not_containsDirectedCycle r

private theorem Path.edgeSet_not_containsReverseDirectedRay
    {D : Digraph V} (p : Path D) :
    ¬ ContainsReverseDirectedRay p.edgeSet := by
  rcases p with p | r
  · exact FinitePath.edgeSet_not_containsReverseDirectedRay p
  · exact Ray.edgeSet_not_containsReverseDirectedRay r

private theorem ForwardOrientation.vertexSet_rootPaths
    (G : DWeb V) (O : ForwardOrientation G.graph) :
    G.vertexSet O.rootPaths = O.carrier := by
  ext x
  constructor
  · rintro ⟨p, ⟨r, rfl⟩, hxp⟩
    simp only [ForwardOrientation.rootPath] at hxp
    split at hxp <;> rename_i hstop
    · obtain ⟨n, rfl⟩ := hxp
      cases n with
      | zero => exact r.2.1
      | succ n =>
          exact (O.endpoints_mem _
            (O.orbit_edge (fun k _ ↦ hstop k))).2
    · change x ∈ (O.orbitWalk r.1 (O.stoppingIndex hstop)
        (O.alive_stoppingIndex hstop)).support at hxp
      rw [O.orbitWalk_support] at hxp
      simp only [List.mem_ofFn] at hxp
      obtain ⟨i, rfl⟩ := hxp
      have hi_le : i.1 ≤ O.stoppingIndex hstop :=
        Nat.lt_succ_iff.mp i.2
      by_cases hi0 : i.1 = 0
      · simpa [hi0] using r.2.1
      · obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hi0
        rw [hn] at hi_le ⊢
        exact (O.endpoints_mem _
          (O.orbit_edge (O.alive_mono
            (O.alive_stoppingIndex hstop) hi_le))).2
  · intro hx
    obtain ⟨hroot, halive, horbit⟩ := O.reachable_from_component x hx
    let r : O.Root := ⟨O.component x, hroot⟩
    refine ⟨O.rootPath r, ⟨r, rfl⟩, ?_⟩
    simp only [ForwardOrientation.rootPath]
    split <;> rename_i hstop
    · exact ⟨O.depth x, horbit⟩
    · have hle : O.depth x ≤ O.stoppingIndex hstop := by
        by_contra hnot
        have hlt : O.stoppingIndex hstop < O.depth x := Nat.lt_of_not_ge hnot
        exact O.not_hasNext_stoppingIndex hstop (halive _ hlt)
      change x ∈ (O.orbitWalk r.1 (O.stoppingIndex hstop)
        (O.alive_stoppingIndex hstop)).support
      rw [O.orbitWalk_support]
      simp only [List.mem_ofFn]
      exact ⟨⟨O.depth x, Nat.lt_succ_iff.mpr hle⟩, horbit⟩

private theorem exists_forwardOrientation_exact
    {D : Digraph V} (E : Set (V × V)) (carrier : Set V)
    (hgraph : E ⊆ {e | D.Adj e.1 e.2})
    (hendpoints : ∀ e ∈ E, e.1 ∈ carrier ∧ e.2 ∈ carrier)
    (hunique : Relator.BiUnique (fun x y ↦ (x, y) ∈ E))
    (hcycle : ¬ ContainsDirectedCycle E)
    (hreverse : ¬ ContainsReverseDirectedRay E) :
    ∃ O : ForwardOrientation D, O.edge = E ∧ O.carrier = carrier := by
  let hwf : WellFounded (fun x y ↦ (x, y) ∈ E) :=
    ForwardOrientation.predecessor_wellFounded E hcycle hreverse
  let O : ForwardOrientation D :=
    { edge := E
      carrier := carrier
      depth := ForwardOrientation.wellFoundedDepth E hwf
      component := ForwardOrientation.wellFoundedRoot E hwf
      edge_in_graph := hgraph
      endpoints_mem := hendpoints
      out_unique := fun hxy hxz ↦ hunique.2 hxy hxz
      in_unique := fun hxz hyz ↦ hunique.1 hxz hyz
      depth_step := fun hxy ↦
        ForwardOrientation.wellFoundedDepth_step E hunique hwf hxy
      component_step := fun hxy ↦
        ForwardOrientation.wellFoundedRoot_step E hunique hwf hxy
      root_label := fun _hx hdepth ↦
        ForwardOrientation.wellFoundedRoot_eq_self_of_depth_eq_zero
          E hwf hdepth
      predecessor := by
        intro x _hx hpos
        have hne : ForwardOrientation.wellFoundedDepth E hwf x ≠ 0 :=
          Nat.ne_of_gt hpos
        exact Classical.byContradiction fun hnot ↦
          hne ((ForwardOrientation.wellFoundedDepth_eq_zero_iff
            E hwf x).mpr hnot) }
  exact ⟨O, rfl, rfl⟩

/-- Every ladder path splits, after deleting `CE`, into a disjoint warp of
finite paths and rays.  The decomposition covers exactly the old path and
uses exactly its surviving edges. -/
theorem exists_surviving_decomposition
    (L : Input Gamma I) (C : Set (LV L)) (p : Gamma.DPath) :
    ∃ Q : Set Gamma.DPath,
      Gamma.IsWarp Q ∧ Gamma.vertexSet Q = p.support ∧
      Alternating.familyEdges Q =
        p.edgeSet \ GroundingCut.CE L C := by
  let E := p.edgeSet \ GroundingCut.CE L C
  have hgraph : E ⊆ {e | Gamma.graph.Adj e.1 e.2} :=
    fun _ he ↦ p.edgeSet_subset_adj he.1
  have hendpoints : ∀ e ∈ E, e.1 ∈ p.support ∧ e.2 ∈ p.support :=
    fun e he ↦ p.edgeSet_subset_support_prod he.1
  have hunique : Relator.BiUnique (fun x y ↦ (x, y) ∈ E) := by
    refine ⟨?_, ?_⟩
    · intro x y z hxz hyz
      exact (Path.edgeSet_biUnique p).1 hxz.1 hyz.1
    · intro x y z hxy hxz
      exact (Path.edgeSet_biUnique p).2 hxy.1 hxz.1
  have hcycle : ¬ ContainsDirectedCycle E := by
    rintro ⟨K, hK⟩
    exact Path.edgeSet_not_containsDirectedCycle p
      ⟨K, hK.trans fun _ he ↦ he.1⟩
  have hreverse : ¬ ContainsReverseDirectedRay E := by
    rintro ⟨R, hR⟩
    exact Path.edgeSet_not_containsReverseDirectedRay p
      ⟨R, fun n ↦ (hR n).1⟩
  obtain ⟨O, hOE, hOC⟩ := exists_forwardOrientation_exact
    E p.support hgraph hendpoints hunique hcycle hreverse
  refine ⟨O.rootPaths, O.rootPaths_pairwiseDisjoint, ?_, ?_⟩
  · simpa [hOC] using ForwardOrientation.vertexSet_rootPaths Gamma O
  · change O.rootPathEdges = _
    exact O.rootPathEdges_eq.trans hOE

/-- Every vertex of a directed path is joined to its initial vertex by a
finite initial segment using no new vertices or edges. -/
private theorem exists_initial_segment
    (p : Gamma.DPath) {x : V} (hx : x ∈ p.support) :
    ∃ q : FinitePath Gamma.graph,
      q.start = p.initial ∧ q.finish = x ∧
        q.support ⊆ p.support ∧ q.edgeSet ⊆ p.edgeSet := by
  rcases p with p | r
  · have hmeet : p.walk.Meets ({x} : Set V) := ⟨x, hx, rfl⟩
    let F := p.walk.firstHit ({x} : Set V) hmeet
    let q : FinitePath Gamma.graph :=
      { start := p.start
        finish := F.endpoint
        walk := F.walk
        isPath := F.isPath p.isPath }
    have hfinish : F.endpoint = x := by
      simpa using F.endpoint_mem
    refine ⟨q, rfl, hfinish, ?_, ?_⟩
    · exact F.support_subset
    · exact Walk.edgeSet_subset_of_support_prefix F.walk p.walk
        F.support_prefix
  · obtain ⟨n, rfl⟩ := hx
    let q := GroundingCutDecoder.raySegmentPath (Gamma := Gamma) r 0 n
    refine ⟨q, ?_, ?_, ?_, ?_⟩
    · rfl
    · simp [q, GroundingCutDecoder.raySegmentPath]
    · intro z hz
      change z ∈
        (GroundingCutDecoder.raySegmentWalk (Gamma := Gamma) r 0 n).support at hz
      rw [GroundingCutDecoder.raySegmentWalk_support] at hz
      simp only [List.mem_ofFn] at hz
      obtain ⟨i, rfl⟩ := hz
      change ∃ m : ℕ, r m = r (0 + i.1)
      exact ⟨0 + i.1, rfl⟩
    · exact GroundingCutDecoder.raySegmentPath_edgeSet_subset r 0 n

/-- A finite walk whose edges lie in a warp's family cannot leave the warp
member containing its first vertex. -/
private theorem finish_mem_of_walk_edges_subset_family
    {Q : Set Gamma.DPath} (hQ : Gamma.IsWarp Q)
    {q : Gamma.DPath} (hqQ : q ∈ Q)
    {a b : V} (w : Walk Gamma.graph a b)
    (haq : a ∈ q.support)
    (hw : w.edgeSet ⊆ Alternating.familyEdges Q) :
    b ∈ q.support := by
  induction w with
  | nil => exact haq
  | @cons a c b hac tail ih =>
      have hacFamily : (a, c) ∈ Alternating.familyEdges Q :=
        hw (by simp [Walk.edgeSet_cons])
      simp only [Alternating.familyEdges, Set.mem_iUnion] at hacFamily
      obtain ⟨s, hsQ, hacs⟩ := hacFamily
      have has : a ∈ s.support :=
        (s.edgeSet_subset_support_prod hacs).1
      have hcs : c ∈ s.support :=
        (s.edgeSet_subset_support_prod hacs).2
      have hsq : s = q :=
        Alternating.DWeb.IsWarp.eq_of_mem_support hQ hsQ hqQ has haq
      apply ih (hsq ▸ hcs)
      intro e he
      exact hw (by simp only [Walk.edgeSet_cons, Set.mem_union,
        Set.mem_singleton_iff]; exact Or.inr he)

/-- Every vertex of a ladder member belongs to one of the maximal fragments
obtained by deleting the represented cut edges.  Maximality is literal:
the fragment support is exactly the surviving connected component inside
the parent ladder path. -/
theorem exists_deleted_fragment_containing
    (L : Input Gamma I) (C : Set (LV L))
    (parent : Gamma.DPath) (hparent : parent ∈ L.ladder.paths)
    {x : V} (hx : x ∈ parent.support) :
    ∃ P : L.Fragment,
      P ∈ GroundingCut.fragments L C ∧ x ∈ P.path.support := by
  obtain ⟨Q, hQ, hvertex, hedges⟩ :=
    exists_surviving_decomposition L C parent
  have hxQ : x ∈ Gamma.vertexSet Q := by
    rw [hvertex]
    exact hx
  obtain ⟨q, hqQ, hxq⟩ := hxQ
  have hqSupport : q.support ⊆ parent.support := by
    intro z hz
    rw [← hvertex]
    exact ⟨q, hqQ, hz⟩
  have hqEdges : q.edgeSet ⊆ parent.edgeSet := by
    intro e he
    have heFamily : e ∈ Alternating.familyEdges Q := by
      simp only [Alternating.familyEdges, Set.mem_iUnion]
      exact ⟨q, hqQ, he⟩
    rw [hedges] at heFamily
    exact heFamily.1
  let P : L.Fragment :=
    { path := q
      parent := parent
      parent_mem := hparent
      support_subset := hqSupport
      edges_subset := hqEdges }
  have hqDisjoint : Disjoint q.edgeSet (GroundingCut.CE L C) := by
    apply Set.disjoint_left.2
    intro e heq heC
    have heFamily : e ∈ Alternating.familyEdges Q := by
      simp only [Alternating.familyEdges, Set.mem_iUnion]
      exact ⟨q, hqQ, heq⟩
    rw [hedges] at heFamily
    exact heFamily.2 heC
  refine ⟨P, ⟨hqDisjoint, ?_⟩, hxq⟩
  ext z
  constructor
  · intro hz
    refine ⟨hqSupport hz, ?_⟩
    obtain ⟨r, hrstart, hrfinish, hrSupport, hrEdges⟩ :=
      exists_initial_segment q hz
    refine ⟨r, Or.inl ⟨hrstart, hrfinish⟩,
      hrSupport.trans hqSupport, hrEdges.trans hqEdges, ?_⟩
    exact hqDisjoint.mono hrEdges Subset.rfl
  · rintro ⟨_zparent, r, horient, _hrSupport, hrEdges, hrDisjoint⟩
    have hrFamily : r.edgeSet ⊆ Alternating.familyEdges Q := by
      intro e he
      rw [hedges]
      exact ⟨hrEdges he, Set.disjoint_left.1 hrDisjoint he⟩
    rcases horient with horient | horient
    · exact horient.2 ▸ finish_mem_of_walk_edges_subset_family
        hQ hqQ r.walk (horient.1 ▸ q.initial_mem_support) hrFamily
    · have hzQ : z ∈ Gamma.vertexSet Q := by
        rw [hvertex]
        exact _zparent
      obtain ⟨s, hsQ, hzs⟩ := hzQ
      have hinitials : q.initial ∈ s.support :=
        horient.2 ▸ finish_mem_of_walk_edges_subset_family
          hQ hsQ r.walk (horient.1 ▸ hzs) hrFamily
      have hsq : s = q :=
        Alternating.DWeb.IsWarp.eq_of_mem_support hQ hsQ hqQ
          hinitials q.initial_mem_support
      simpa [hsq] using hzs

/-- The output which the finite descent is required to construct. -/
structure Output (L : Input Gamma I) (C : Set (LV L)) : Type (max u v) where
  path : FinitePath L.lambda.graph
  starts : path.start ∈ L.lambda.source
  finishes : path.finish ∈ L.lambda.target
  avoids : L.lambda.Avoids path C

/-! ## Source-faithful last-fragment descent states -/

/-- A terminal-cut vertex belongs to a surviving fragment of an essential
ladder parent. -/
theorem terminalCut_has_fragment
    (L : Input Gamma I) (C : Set (LV L)) {t : V}
    (ht : t ∈ L.terminalCut) :
    ∃ P : L.Fragment,
      P ∈ GroundingCut.fragments L C ∧ t ∈ P.path.support ∧
        P.parent ∈ L.essentialLadder := by
  obtain ⟨parent, hparentEssential, hterminal⟩ := ht
  have htParent : t ∈ parent.support :=
    Gamma.terminal_mem_support hterminal
  obtain ⟨P, hP, htP⟩ :=
    exists_deleted_fragment_containing L C parent
      hparentEssential.1 htParent
  have htPParent : t ∈ P.parent.support := P.support_subset htP
  have hparentEq : P.parent = parent :=
    _root_.Erdos599.Alternating.DWeb.IsWarp.eq_of_mem_support
      L.ladder.disjoint P.parent_mem hparentEssential.1
        htPParent htParent
  exact ⟨P, hP, htP, hparentEq ▸ hparentEssential⟩

/-- A selected surviving fragment together with the already compiled
ordinary suffix beginning at its contact with the ambient finite path.

The source proof first forms a relaxed route at an earlier encounter and
then traverses the contacted fragment backwards.  This absorbs the virtual
first step, so the stored suffix legitimately starts at `old contact`; the
edge-gadget-aware open occurrence remains in `RelaxedEscape`, rather than
being incorrectly asserted here. -/
structure EscapeSuffixState
    (L : Input Gamma I) (C : Set (LV L))
    (R : FinitePath Gamma.graph) : Type (max u v) where
  position : Fin R.walk.support.length
  fragment : L.Fragment
  fragment_mem : fragment ∈ GroundingCut.G0 L C
  fragment_escape :
    PopularAuxiliary.Input.Fragment.MeetsEscape L C fragment
  contact_mem : R.walk.support[position] ∈ fragment.path.support
  suffix : FinitePath L.lambda.graph
  suffix_start : suffix.start = .old R.walk.support[position]
  suffix_target : suffix.finish ∈ L.lambda.target
  suffix_avoids : L.lambda.Avoids suffix C

/-- A completely compiled auxiliary source--target route. -/
abbrev ResolvedRoute (L : Input Gamma I) (C : Set (LV L)) :=
  Output L C

/-- The optional successful branch of a contact state.  Keeping the
compiled route itself in this proposition avoids imposing any false claim
that the open escape at the contact already begins at `old contact`. -/
def EscapeSuffixState.HasSourcePrefix
    {L : Input Gamma I} {C : Set (LV L)}
    {R : FinitePath Gamma.graph} (_S : EscapeSuffixState L C R) : Prop :=
  Nonempty (ResolvedRoute L C)

theorem EscapeSuffixState.resolvedRoute_of_hasSourcePrefix
    {L : Input Gamma I} {C : Set (LV L)}
    {R : FinitePath Gamma.graph} (S : EscapeSuffixState L C R)
    (h : S.HasSourcePrefix) : Nonempty (ResolvedRoute L C) := h

/-- A prefix route ending at a displayed fragment contact.  This is the
input form of Assertion 8.21. -/
structure ContactRoute
    (L : Input Gamma I) (C : Set (LV L))
    (R : FinitePath Gamma.graph) : Type (max u v) where
  position : Fin R.walk.support.length
  fragment : L.Fragment
  fragment_mem : fragment ∈ GroundingCut.G0 L C
  contact_mem : R.walk.support[position] ∈ fragment.path.support
  sourceRoute : FinitePath L.lambda.graph
  sourceRoute_start : sourceRoute.start ∈ L.lambda.source
  sourceRoute_finish : sourceRoute.finish = .old R.walk.support[position]
  sourceRoute_avoids : L.lambda.Avoids sourceRoute C

theorem ContactRoute.beforeEq_blockingPoint
    {L : Input Gamma I} {C : Set (LV L)}
    {R : FinitePath Gamma.graph} (S : ContactRoute L C R)
    (hC : Popular.IsSeparator L.lambda C) :
    GroundingCut.BeforeEq S.fragment.path R.walk.support[S.position]
      (GroundingCut.blockingPoint L C S.fragment) :=
  GroundingCutDecoder.assertion8_21 L C hC S.fragment S.fragment_mem
    S.sourceRoute S.sourceRoute_start S.sourceRoute_avoids
      S.sourceRoute_finish S.contact_mem

/-- The exact well-founded transition system used in Assertion 8.18. -/
structure LastFragmentDescentSystem
    (L : Input Gamma I) (C : Set (LV L))
    (R : FinitePath Gamma.graph) : Type (max u v) where
  seed : EscapeSuffixState L C R
  resolve : ∀ current : EscapeSuffixState L C R,
    Nonempty (ResolvedRoute L C) ∨
      ∃ earlier : EscapeSuffixState L C R,
        earlier.position.1 < current.position.1

/-- Strict decrease of ambient contact positions terminates in a compiled
auxiliary source--target route. -/
theorem LastFragmentDescentSystem.exists_avoiding_source_target_path
    {L : Input Gamma I} {C : Set (LV L)}
    {R : FinitePath Gamma.graph}
    (D : LastFragmentDescentSystem L C R) :
    ∃ q : FinitePath L.lambda.graph,
      q.start ∈ L.lambda.source ∧ q.finish ∈ L.lambda.target ∧
        L.lambda.Avoids q C := by
  have solve : ∀ n : Nat, ∀ current : EscapeSuffixState L C R,
      current.position.1 = n → Nonempty (ResolvedRoute L C) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro current hposition
        rcases D.resolve current with hdone | ⟨earlier, hearlier⟩
        · exact hdone
        · apply ih earlier.position.1
          · simpa only [hposition] using hearlier
          · rfl
  obtain ⟨O⟩ := solve D.seed.position.1 D.seed rfl
  exact ⟨O.path, O.starts, O.finishes, O.avoids⟩

/-- A last-fragment descent system for every avoiding original path. -/
def FiniteContactDescentGeometry
    (L : Input Gamma I) (C : Set (LV L)) : Prop :=
  ∀ (R : FinitePath Gamma.graph),
    R.start ∈ Gamma.source → R.finish ∈ L.terminalCut →
      Gamma.Avoids R (GroundingCut.BB L C) →
        Nonempty (LastFragmentDescentSystem L C R)

/-- Project the checked finite contact descent to the literal pathwise
decoder stored by the grounding certificate. -/
theorem finiteDescentDecoder_of_contactGeometry
    (L : Input Gamma I) (C : Set (LV L))
    (H : FiniteContactDescentGeometry L C) :
    GroundingCut.FiniteDescentDecoder L C := by
  intro R hsource hterminal havoid
  obtain ⟨D⟩ := H R hsource hterminal havoid
  exact D.exists_avoiding_source_target_path

/-- The first Lambda occurrence of a route which semantically starts at an
original vertex `x`.

The first two constructors are literal: the route starts at `old x`, or one
Lambda arc after it.  The last two are the open forward cases from the source
proof.  They omit the unretained old ladder vertex `x` and begin at the old or
edge gadget whose entry is the head of the first original edge.

This extra representation is essential.  If `x` is an unretained ladder
vertex, `(u,t)` is a ladder edge, and the source escape begins with an
original edge `x → t`, then `.old x → .edge u t` is not a Lambda arc:
`ArcVE` requires `x ∈ offLadder ∪ finiteSource`.  Nevertheless `.edge u t`
is exactly the first admissible occurrence of the alternating route. -/
inductive StartOccurrence (L : Input Gamma I) (x : V) : LV L → Prop
  | atOld : StartOccurrence L x (.old x)
  | afterLambdaArc {a : LV L} (h : L.lambda.graph.Adj (.old x) a) :
      StartOccurrence L x a
  | afterForwardOld {y : V}
      (hy : y ∈ L.offLadder ∪ L.targetMarkers)
      (hxy : Gamma.graph.Adj x y) :
      StartOccurrence L x (.old y)
  | afterForwardEdge {u y : V}
      (huy : (u, y) ∈ L.familyEdges)
      (hxy : Gamma.graph.Adj x y) :
      StartOccurrence L x (.edge u y)

/-- At a finite auxiliary source, every open occurrence closes to either
the source vertex itself or one genuine Lambda arc from it. -/
theorem StartOccurrence.eq_or_adj_of_mem_finiteSource
    {L : Input Gamma I} {x : V} {a : LV L}
    (h : StartOccurrence L x a) (hx : x ∈ L.finiteSource) :
    a = .old x ∨ L.lambda.graph.Adj (.old x) a := by
  cases h with
  | atOld => exact Or.inl rfl
  | afterLambdaArc h => exact Or.inr h
  | afterForwardOld hy hxy =>
      exact Or.inr ((L.lambda_adj_old_old x _).2
        ⟨Or.inr hx, hy, hxy⟩)
  | afterForwardEdge huy hxy =>
      exact Or.inr ((L.lambda_adj_old_edge x _ _).2
        ⟨huy, Or.inr ⟨Or.inr hx, hxy⟩⟩)

/-- A proxy can close either open forward occurrence when the encounter is
on its represented path. -/
theorem StartOccurrence.adj_proxy_of_mem_proxyPath
    {L : Input Gamma I} {x : V} {a : LV L} {i : I}
    (h : StartOccurrence L x a)
    (hx : x ∈ (L.proxyPath i).support) :
    (a = .old x ∨ L.lambda.graph.Adj (.old x) a) ∨
      L.lambda.graph.Adj (.proxy i) a := by
  cases h with
  | atOld => exact Or.inl (Or.inl rfl)
  | afterLambdaArc h => exact Or.inl (Or.inr h)
  | afterForwardOld hy hxy =>
      exact Or.inr ((L.lambda_adj_proxy_old i _).2
        ⟨hy, x, hx, hxy⟩)
  | afterForwardEdge huy hxy =>
      exact Or.inr ((L.lambda_adj_proxy_edge i _ _).2
        ⟨huy, x, hx, hxy⟩)

/-- A cut-avoiding open Lambda tail attached to an encounter of the original
finite path.  `position` is the measure decreased by the source proof. -/
structure Record (L : Input Gamma I) (C : Set (LV L))
    (R : FinitePath Gamma.graph) : Type (max u v) where
  position : Fin R.walk.support.length
  route : FinitePath L.lambda.graph
  startsAt : StartOccurrence L R.walk.support[position] route.start
  finishes : route.finish ∈ L.lambda.target
  avoids : L.lambda.Avoids route C

/-- Close an open record by prepending a cut-avoiding auxiliary source.
Loop erasure is needed because that source can already occur later in the
tail. -/
theorem Record.output_of_source_arc
    {L : Input Gamma I} {C : Set (LV L)}
    {R : FinitePath Gamma.graph} (current : Record L C R)
    {s : LV L} (hs : s ∈ L.lambda.source) (hsC : s ∉ C)
    (hstart : current.route.start = s ∨
      L.lambda.graph.Adj s current.route.start) :
    Nonempty (Output L C) := by
  rcases hstart with hstart | hstart
  · exact ⟨{
      path := current.route
      starts := hstart.symm ▸ hs
      finishes := current.finishes
      avoids := current.avoids }⟩
  · let w : Walk L.lambda.graph s current.route.finish :=
      .cons hstart current.route.walk
    obtain ⟨p, hpSupport⟩ :=
      RelationalRoof.exists_pathTo_support_subset
        (R := L.lambda.graph.Adj) w
    let q : FinitePath L.lambda.graph :=
      { start := s
        finish := current.route.finish
        walk := p.1
        isPath := p.2 }
    refine ⟨{
      path := q
      starts := hs
      finishes := current.finishes
      avoids := ?_ }⟩
    change Disjoint q.support C
    rw [Set.disjoint_left]
    intro z hzq hzC
    have hzw : z ∈ w.support := hpSupport hzq
    simp only [w, Walk.support_cons, List.mem_cons] at hzw
    rcases hzw with rfl | hzroute
    · exact hsC hzC
    · exact Set.disjoint_left.1 current.avoids hzroute hzC

/-- In the finite-record branch, avoiding the old encounter closes the open
tail at the corresponding ordinary Lambda source. -/
theorem Record.output_of_mem_finiteSource
    {L : Input Gamma I} {C : Set (LV L)}
    {R : FinitePath Gamma.graph} (current : Record L C R)
    (hx : R.walk.support[current.position] ∈ L.finiteSource)
    (hxC : (PopularAuxiliary.Input.LambdaVertex.old
      R.walk.support[current.position] : LV L) ∉ C) :
    Nonempty (Output L C) := by
  let s : LV L := .old R.walk.support[current.position]
  apply current.output_of_source_arc
    ((L.mem_lambda_source_old _).2 hx) hxC
  rcases current.startsAt.eq_or_adj_of_mem_finiteSource hx with h | h
  · exact Or.inl h
  · exact Or.inr h

/-- In the infinite-record branch the caller supplies the literal proxy arc
to the first occurrence.  This is the exact endpoint certificate carried by
an open forward step from the represented ray. -/
theorem Record.output_of_proxy_arc
    {L : Input Gamma I} {C : Set (LV L)}
    {R : FinitePath Gamma.graph} (current : Record L C R)
    (i : I) (hiC : (PopularAuxiliary.Input.LambdaVertex.proxy i : LV L) ∉ C)
    (hi : L.lambda.graph.Adj (.proxy i) current.route.start) :
    Nonempty (Output L C) :=
  current.output_of_source_arc (L.mem_lambda_source_proxy i) hiC (Or.inr hi)

/-- The honest one-path compiler for the descent.  `step` contains precisely
the local geometric obligation: either the current route can be extended
back to an auxiliary source, or the last-fragment construction produces a
strictly earlier record. -/
structure PathCompiler (L : Input Gamma I) (C : Set (LV L))
    (R : FinitePath Gamma.graph) : Type (max u v) where
  initial : Record L C R
  step : ∀ current : Record L C R,
    Nonempty (Output L C) ∨
      ∃ earlier : Record L C R,
        earlier.position.1 < current.position.1

/-- Strict decrease of encounter positions terminates and returns an
auxiliary source--target path. -/
theorem PathCompiler.exists_output
    {L : Input Gamma I} {C : Set (LV L)}
    {R : FinitePath Gamma.graph} (K : PathCompiler L C R) :
    Nonempty (Output L C) := by
  have solve : ∀ n : Nat, ∀ current : Record L C R,
      current.position.1 = n → Nonempty (Output L C) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro current hposition
        rcases K.step current with hdone | ⟨earlier, hearlier⟩
        · exact hdone
        · apply ih earlier.position.1
          · simpa only [hposition] using hearlier
          · rfl
  exact solve K.initial.position.1 K.initial rfl

/-- A compiler for each original source--terminal-cut path avoiding `BB` is
exactly enough to discharge the pathwise decoder premise of Assertion 8.18.
No separation conclusion is assumed here. -/
def Compiler
    (L : Input Gamma I) (C : Set (LV L)) : Prop :=
  ∀ (R : FinitePath Gamma.graph),
    R.start ∈ Gamma.source → R.finish ∈ L.terminalCut →
      Gamma.Avoids R (GroundingCut.BB L C) →
        Nonempty (PathCompiler L C R)

/-- Projection of the checked well-founded compiler to the exact
`FiniteDescentDecoder` stored in the selected switch/prune certificate. -/
theorem finiteDescentDecoder_of_compiler
    (L : Input Gamma I) (C : Set (LV L))
    (K : Compiler L C) :
    GroundingCut.FiniteDescentDecoder L C := by
  intro R hsource hterminal havoid
  obtain ⟨P⟩ := K R hsource hterminal havoid
  obtain ⟨O⟩ := P.exists_output
  exact ⟨O.path, O.starts, O.finishes, O.avoids⟩

end GroundingFiniteDescent
end Erdos599
