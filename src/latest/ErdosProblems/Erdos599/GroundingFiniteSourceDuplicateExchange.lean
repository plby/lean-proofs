/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingGroundedRecordMarkerDisjoint
import ErdosProblems.Erdos599.GroundingErasedRouteCore
import ErdosProblems.Erdos599.GroundingRelaxedEscape
import ErdosProblems.Erdos599.LadderLimitHitClosure

/-!
# The finite-source duplicate exchange path

The raw switched relation need not make the whole set `BB` an antichain: a
surviving piece of a grounded finite record can run from an earlier blocking
point to its terminal, which also belongs to `CV`.  In a legal ladder this
cannot be the degenerate example in which the escape marker itself lies on
the grounded parent (`groundedRecord_support_disjoint_targetMarkers`).  The
remaining case has a useful positive replacement.

Removing the old terminal vertex from the auxiliary cut does not change
`CE`, hence does not change the surviving fragments.  Assertion 8.18's
backwards-fragment compiler can therefore splice an escape at the earlier
blocking point into a genuine auxiliary path starting at the terminal.  The
result meets the original cut at exactly that terminal.  When the terminal is
in `finiteSource`, this is a private auxiliary source--target path, which is
the input needed for the finite-source duplicate exchange.
-/

noncomputable section

open Set

namespace Erdos599
namespace GroundingFiniteSourceDuplicateExchange

open DirectedPath

universe u v

variable {V : Type u} {I : Type v} {Gamma : DWeb V}

abbrev Input (Gamma : DWeb V) (I : Type v) : Type (max u v) :=
  PopularAuxiliary.Input Gamma I

abbrev LV (L : Input Gamma I) : Type (max u v) :=
  PopularAuxiliary.Input.LambdaVertex V I

@[simp]
theorem edgeSet_castStart {R : V → V → Prop} {a a' b : V}
    (h : a = a') (p : Walk (RelationalRoof.relationDigraph R) a b) :
    (RelationalRoof.castStart R h p).edgeSet = p.edgeSet := by
  subst a'
  rfl

/-- Loop erasure may be chosen without introducing chord edges.  The
standard support-only interface is enough for avoidance, but the stronger
ordered interface is needed when the first decoded direction must be
retained. -/
theorem exists_pathTo_support_edgeSet_subset {R : V → V → Prop} :
    ∀ {a b : V} (p : Walk (RelationalRoof.relationDigraph R) a b),
      ∃ q : Walk.PathTo (RelationalRoof.relationDigraph R) a b,
        q.1.support ⊆ p.support ∧ q.1.edgeSet ⊆ p.edgeSet
  | a, _, .nil => by
      exact ⟨⟨.nil, Walk.isPath_nil a⟩, by simp⟩
  | a, b, .cons (v := c) h p => by
      obtain ⟨q, hqSupport, hqEdges⟩ :=
        exists_pathTo_support_edgeSet_subset p
      by_cases ha : a ∈ q.1.support
      · let hm : q.1.Meets ({a} : Set V) :=
          ⟨a, ha, Set.mem_singleton a⟩
        let T := q.1.lastHit ({a} : Set V) hm
        have hTa : T.startpoint = a :=
          Set.mem_singleton_iff.1 T.startpoint_mem
        let r : Walk.PathTo (RelationalRoof.relationDigraph R) a b :=
          ⟨RelationalRoof.castStart R hTa T.walk, by
            simpa [Walk.IsPath] using T.isPath q.2⟩
        refine ⟨r, ?_, ?_⟩
        · intro x hx
          have hxT : x ∈ T.walk.support := by simpa [r] using hx
          exact List.mem_cons_of_mem a (hqSupport (T.support_subset hxT))
        · intro e he
          have heT : e ∈ T.walk.edgeSet := by
            change e ∈
              (RelationalRoof.castStart R hTa T.walk).edgeSet at he
            simpa only [edgeSet_castStart] using he
          have heQ : e ∈ q.1.edgeSet :=
            T.walk.edgeSet_subset_of_support_suffix q.1 T.support_suffix heT
          exact Set.mem_union_right _ (hqEdges heQ)
      · let r : Walk.PathTo (RelationalRoof.relationDigraph R) a b :=
          ⟨.cons h q.1, by simpa [Walk.IsPath, ha] using q.2⟩
        refine ⟨r, ?_, ?_⟩
        · intro x hx
          simp only [r, Walk.support_cons, List.mem_cons] at hx ⊢
          exact hx.elim Or.inl (fun hxq ↦ Or.inr (hqSupport hxq))
        · intro e he
          simp only [r, Walk.edgeSet_cons, Set.mem_union,
            Set.mem_singleton_iff] at he ⊢
          exact he.elim Or.inl (fun heq ↦ Or.inr (hqEdges heq))

/-- Removing an old vertex from the auxiliary cut does not delete any ladder
edge. -/
theorem CE_diff_singleton_old
    (L : Input Gamma I) (C : Set (LV L)) (x : V) :
    GroundingCut.CE L (C \ {(.old x : LV L)}) = GroundingCut.CE L C := by
  ext e
  simp

/-- Consequently the maximal surviving fragments are unchanged when one old
cut vertex is removed. -/
theorem fragments_diff_singleton_old
    (L : Input Gamma I) (C : Set (LV L)) (x : V) :
    GroundingCut.fragments L (C \ {(.old x : LV L)}) =
      GroundingCut.fragments L C := by
  have hCE := CE_diff_singleton_old L C x
  ext P
  simp only [GroundingCut.fragments, Set.mem_setOf_eq,
    GroundingCut.IsDeletedFragment, GroundingCut.SurvivingConnected, hCE]

/-- A relaxed escape remains a relaxed escape after shrinking the cut. -/
private def relaxedEscape_mono
    (L : Input Gamma I) {C D : Set (LV L)} {x : V}
    (hDC : D ⊆ C) (E : L.RelaxedEscape C x) :
    L.RelaxedEscape D x :=
  { route := E.route
    start_eq := E.start_eq
    target := E.target
    avoids := E.avoids.mono_right hDC
    old_not_mem := fun hxD => E.old_not_mem (hDC hxD) }

/-- Chronological erasure makes the final vertex genuinely final: no
retained forward edge of its maximal-run compression leaves that vertex. -/
theorem erasedCompression_terminal_not_forward_source
    {J : Type u} {L : Input Gamma J}
    {p : FinitePath L.lambda.graph} (T : L.MicroTrace p) {z : V} :
    (T.terminal, z) ∉
      T.erasedCompression.path.directionEdges .forward := by
  intro hz
  let E := T.runs.erasedSignedRoute
  have hvalid : ∀ {s : PopularAuxiliary.Input.SignedEdge V},
      s ∈ E.steps →
      PopularAuxiliary.Input.SignedEdge.Valid (Gamma := Gamma) s :=
    fun {_s} hs ↦ T.valid _ (E.steps_sublist.subset hs)
  obtain ⟨s, hs, hsForward, hsEdge⟩ :=
    E.compressionOfValid_directionEdges_subset_directedSignedEdgeSet
      hvalid .forward hz
  obtain ⟨n, rfl⟩ := List.get_of_mem hs
  have hnForward : (E.steps.get n).direction = .forward := hsForward
  have hnEdge : (E.steps.get n).edge = (T.terminal, z) := hsEdge
  have hsource : E.routeVertex n = T.terminal := by
    have hroute := E.step_edge_eq_routeVertices_forward n hnForward
    exact (congrArg Prod.fst (hnEdge.symm.trans hroute)).symm
  have hrouteEq : E.routeVertex n = E.routeVertex E.steps.length :=
    hsource.trans E.routeVertex_last.symm
  have hnChain : n.1 < E.vertexChain.length := by
    rw [E.vertexChain_length]
    omega
  have hlastChain : E.steps.length < E.vertexChain.length := by
    rw [E.vertexChain_length]
    omega
  have hget :
      E.vertexChain.get ⟨n.1, hnChain⟩ =
        E.vertexChain.get ⟨E.steps.length, hlastChain⟩ := by
    unfold PopularAuxiliary.Input.ErasedSignedRoute.routeVertex at hrouteEq
    rw [List.getD_eq_get E.vertexChain T.terminal ⟨n.1, hnChain⟩,
      List.getD_eq_get E.vertexChain T.terminal
        ⟨E.steps.length, hlastChain⟩] at hrouteEq
    exact hrouteEq
  have hindex :
      (⟨n.1, hnChain⟩ : Fin E.vertexChain.length) =
        ⟨E.steps.length, hlastChain⟩ :=
    E.vertexChain_nodup.get_inj_iff.mp hget
  have : n.1 = E.steps.length := congrArg Fin.val hindex
  omega

/-- Direction-sensitive provenance reduces forward/reference edge
disjointness of the erased compression to the corresponding pointwise fact
for the retained signed route. -/
theorem erasedCompression_forwardLinksOff_of_forward_not_mem
    {J : Type u} {L : Input Gamma J}
    {p : FinitePath L.lambda.graph} (T : L.MicroTrace p)
    (hforward : ∀ {s : PopularAuxiliary.Input.SignedEdge V},
      s ∈ T.runs.erasedSignedRoute.steps →
      s.direction = .forward →
      s.edge ∉ Alternating.familyEdges L.ladder.paths) :
    Alternating.ForwardLinksOff L.ladder.paths
      T.erasedCompression.path := by
  intro l hl hldir
  rw [Set.disjoint_left]
  intro e hel heFamily
  have heDirection : e ∈
      T.erasedCompression.path.directionEdges .forward := by
    simp only [Alternating.AltPath.directionEdges, Set.mem_iUnion]
    exact ⟨l, hl, hldir, hel⟩
  let E := T.runs.erasedSignedRoute
  have hvalid : ∀ {s : PopularAuxiliary.Input.SignedEdge V},
      s ∈ E.steps →
      PopularAuxiliary.Input.SignedEdge.Valid (Gamma := Gamma) s :=
    fun {_s} hs ↦ T.valid _ (E.steps_sublist.subset hs)
  obtain ⟨s, hs, hsForward, hsEdge⟩ :=
    E.compressionOfValid_directionEdges_subset_directedSignedEdgeSet
      hvalid .forward heDirection
  apply hforward hs hsForward
  simpa only [hsEdge] using heFamily

/-- A strict backwards fragment traversal followed by a relaxed escape gives
a path which is private for the original cut at its old starting vertex.

This is the reusable exchange form of the Assertion 8.18 splice: unlike the
ordinary avoidance version, the start is allowed to belong to the original
cut, and it is the only cut vertex on the compiled path. -/
theorem exists_private_reverse_to_relaxedEscape
    (L : Input Gamma I) (C : Set (LV L))
    (P : L.Fragment) (hP : P ∈ GroundingCut.fragments L C)
    {b x : V} (hbx : GroundingCut.Before P.path b x)
    (hxC : (PopularAuxiliary.Input.LambdaVertex.old x : LV L) ∈ C)
    (E : L.RelaxedEscape C b) :
    ∃ r : FinitePath L.lambda.graph,
      r.start = .old x ∧ r.finish ∈ L.lambda.target ∧
        L.lambda.Avoids r (C \ {(.old x : LV L)}) ∧
        r.support ∩ C = {(.old x : LV L)} := by
  let D : Set (LV L) := C \ {(.old x : LV L)}
  have hP' : P ∈ GroundingCut.fragments L D := by
    simpa only [D, fragments_diff_singleton_old L C x] using hP
  have hxNotD : (PopularAuxiliary.Input.LambdaVertex.old x : LV L) ∉ D := by
    intro hxD
    exact hxD.2 rfl
  let E' : L.RelaxedEscape D b :=
    relaxedEscape_mono L Set.diff_subset E
  obtain ⟨r, hrStart, hrTarget, hrAvoid⟩ :=
    GroundingRelaxedEscape.exists_avoiding_reverse_to_relaxedEscape
      L D P hP' hbx hxNotD E'
  refine ⟨r, hrStart, hrTarget, hrAvoid, Set.Subset.antisymm ?_ ?_⟩
  · intro z hz
    have hzEq : z = (.old x : LV L) := by
      by_contra hne
      exact Set.disjoint_left.1 hrAvoid hz.1 ⟨hz.2, hne⟩
    simpa only [Set.mem_singleton_iff] using hzEq
  · intro z hz
    have hzEq : z = (.old x : LV L) := by
      simpa only [Set.mem_singleton_iff] using hz
    subst z
    exact ⟨hrStart ▸ r.start_mem_support, hxC⟩

/-- If the terminal of a surviving fragment is also in the auxiliary cut and
its blocking point is genuinely earlier, then the blocking escape compiles to
a cut-private path starting at that terminal. -/
theorem exists_private_path_of_blockingPoint_ne_terminal
    (L : Input Gamma I) (C : Set (LV L))
    (P : L.Fragment) (hP : P ∈ GroundingCut.fragments L C)
    {c : V} (hcTerminal : P.path.terminal? = some c)
    (hescape : PopularAuxiliary.Input.Fragment.MeetsEscape L C P)
    (hcC : (PopularAuxiliary.Input.LambdaVertex.old c : LV L) ∈ C)
    (hne : GroundingCut.blockingPoint L C P ≠ c) :
    ∃ r : FinitePath L.lambda.graph,
      r.start = .old c ∧ r.finish ∈ L.lambda.target ∧
        L.lambda.Avoids r (C \ {(.old c : LV L)}) ∧
        r.support ∩ C = {(.old c : LV L)} := by
  let b := GroundingCut.blockingPoint L C P
  have hbSupport : b ∈ P.path.support :=
    GroundingCut.blockingPoint_mem_support L C P
  have hbcEq : GroundingCut.BeforeEq P.path b c :=
    GroundingCut.beforeEq_terminal hcTerminal hbSupport
  have hbc : GroundingCut.Before P.path b c := ⟨hbcEq, hne⟩
  have hbEscape : b ∈ L.escapeRegion C :=
    GroundingCut.blockingPoint_mem_escapeRegion_of_meetsEscape
      L C P hescape
  obtain ⟨E⟩ := hbEscape
  exact exists_private_reverse_to_relaxedEscape L C P hP hbc hcC E

/-- In the finite-source duplicate case the private path supplied above is a
literal auxiliary source--target path.  Thus the problematic `CV` terminal
comes with the canonical rerouting witness required by an exchange argument.
-/
theorem exists_private_source_target_path_of_finiteSource_duplicate
    (L : Input Gamma I) (C : Set (LV L))
    (P : L.Fragment) (hP : P ∈ GroundingCut.fragments L C)
    {c : V} (hcTerminal : P.path.terminal? = some c)
    (hescape : PopularAuxiliary.Input.Fragment.MeetsEscape L C P)
    (hcFinite : c ∈ L.finiteSource)
    (hcCV : c ∈ GroundingCut.CV L C)
    (hne : GroundingCut.blockingPoint L C P ≠ c) :
    ∃ r : FinitePath L.lambda.graph,
      r.start ∈ L.lambda.source ∧ r.finish ∈ L.lambda.target ∧
        L.lambda.Avoids r (C \ {(.old c : LV L)}) ∧
        r.support ∩ C = {(.old c : LV L)} := by
  obtain ⟨r, hrStart, hrTarget, hrAvoid, hrPrivate⟩ :=
    exists_private_path_of_blockingPoint_ne_terminal
      L C P hP hcTerminal hescape (GroundingCut.mem_CV.mp hcCV) hne
  refine ⟨r, ?_, hrTarget, hrAvoid, hrPrivate⟩
  rw [hrStart, L.mem_lambda_source_old]
  exact hcFinite

/-- The private auxiliary path has a canonical loop-erased alternating
decode.  It starts at the finite terminal, ends at a target marker, and all
of its backward links belong to the limiting ladder.  This is the
switch-ready form of the finite-source exchange witness. -/
theorem exists_private_decoded_exchange_of_finiteSource_duplicate
    {J : Type u} (L : Input Gamma J) (C : Set (LV L))
    (P : L.Fragment) (hP : P ∈ GroundingCut.fragments L C)
    {c : V} (hcTerminal : P.path.terminal? = some c)
    (hescape : PopularAuxiliary.Input.Fragment.MeetsEscape L C P)
    (hcFinite : c ∈ L.finiteSource)
    (hcCV : c ∈ GroundingCut.CV L C)
    (hne : GroundingCut.blockingPoint L C P ≠ c) :
    ∃ (q : FinitePath L.lambda.graph)
        (A : Alternating.AltPath Gamma.graph) (y : V),
      q.start = .old c ∧ q.finish ∈ L.lambda.target ∧
        L.lambda.Avoids q (C \ {(.old c : LV L)}) ∧
        q.support ∩ C = {(.old c : LV L)} ∧
        q.support ∩ L.lambda.target ⊆ {q.finish} ∧
        A.initial = c ∧ A.terminal? = some y ∧
        y ∈ L.targetMarkers ∧
        (∀ z, (y, z) ∉ A.directionEdges .forward) ∧
        Alternating.BackwardLinksOn L.ladder.paths A := by
  obtain ⟨q, hqStart, hqTarget, hqAvoid, hqPrivate⟩ :=
    exists_private_path_of_blockingPoint_ne_terminal
      L C P hP hcTerminal hescape (GroundingCut.mem_CV.mp hcCV) hne
  let hmeet : q.walk.Meets L.lambda.target :=
    ⟨q.finish, q.finish_mem_support, hqTarget⟩
  let q₀ := q.firstHit L.lambda.target hmeet
  have hq₀Start : q₀.start = .old c := by
    change q.start = .old c
    exact hqStart
  have hq₀Target : q₀.finish ∈ L.lambda.target :=
    q.firstHit_finish_mem L.lambda.target hmeet
  have hq₀Subset : q₀.support ⊆ q.support :=
    q.firstHit_support_subset L.lambda.target hmeet
  have hq₀Avoid : L.lambda.Avoids q₀
      (C \ {(.old c : LV L)}) :=
    hqAvoid.mono hq₀Subset Set.Subset.rfl
  have hq₀Private : q₀.support ∩ C = {(.old c : LV L)} := by
    apply Set.Subset.antisymm
    · intro z hz
      have hzq : z ∈ q.support ∩ C := ⟨hq₀Subset hz.1, hz.2⟩
      exact hqPrivate ▸ hzq
    · intro z hz
      have hzc : z = (.old c : LV L) := by
        simpa only [Set.mem_singleton_iff] using hz
      subst z
      exact ⟨hq₀Start ▸ q₀.start_mem_support,
        (GroundingCut.mem_CV.mp hcCV)⟩
  have hq₀Pure : q₀.support ∩ L.lambda.target ⊆ {q₀.finish} := by
    intro z hz
    apply Set.mem_singleton_iff.2
    by_contra hzf
    have hzlast : z ≠ q₀.walk.support.getLast
        q₀.walk.support_ne_nil := by
      intro h
      apply hzf
      exact h.trans q₀.walk.getLast_support
    have hzdrop : z ∈ q₀.walk.support.dropLast :=
      List.mem_dropLast_of_mem_of_ne_getLast hz.1 hzlast
    exact (q.firstHit_no_mem_before L.lambda.target hmeet hzdrop) hz.2
  have hqSource : q₀.start ∈ L.lambda.source := by
    rw [hq₀Start, L.mem_lambda_source_old]
    exact hcFinite
  let T := L.decodeFinitePath q₀ hqSource hq₀Target
  let A := T.erasedCompression.path
  have hTInitial : T.initial = c := by
    classical
    simp only [T]
    unfold PopularAuxiliary.Input.decodeFinitePath
    split
    · rename_i x hx
      exact PopularAuxiliary.Input.LambdaVertex.old.inj
        (x.2.2.symm.trans hq₀Start)
    · rename_i i hi
      exact False.elim (by
        have hproxy :
            (PopularAuxiliary.Input.LambdaVertex.proxy i.1 : LV L) =
              .old c := i.2.symm.trans hq₀Start
        cases hproxy)
  have hback : Alternating.BackwardLinksOn L.ladder.paths A := by
    apply T.runs.erasedSignedRoute.compressionOfValid_backwardLinksOn
      (fun {_s} hs ↦ T.valid _
        (T.runs.erasedSignedRoute.steps_sublist.subset hs))
      L.ladder.disjoint
    intro s hs hdir
    simpa [PopularAuxiliary.Input.familyEdges,
      Alternating.familyEdges] using
      T.backward_on_ladder s
        (T.runs.erasedSignedRoute.steps_sublist.subset hs) hdir
  refine ⟨q₀, A, T.terminal, hq₀Start, hq₀Target, hq₀Avoid, hq₀Private,
    hq₀Pure,
    ?_, ?_, T.target_endpoint, ?_, hback⟩
  · exact T.erasedCompression.initial_eq.trans hTInitial
  · exact T.erasedCompression.terminal_eq
  · intro z
    exact erasedCompression_terminal_not_forward_source T

/-- Decoder provenance can be recovered from any auxiliary path whose old
initial point is a finite source and whose endpoint is in the auxiliary
target.  This is deliberately stated independently of the private-path
compiler: downstream contact normalization needs the actual `MicroTrace`,
not merely its compressed alternating path. -/
theorem exists_microTrace_of_finiteSource_target_path
    {J : Type u} (L : Input Gamma J)
    (q : FinitePath L.lambda.graph) {c : V}
    (hqStart : q.start = .old c) (hcFinite : c ∈ L.finiteSource)
    (hqTarget : q.finish ∈ L.lambda.target) :
    ∃ T : L.MicroTrace q,
      T.initial = c ∧ T.terminal ∈ L.targetMarkers ∧
        T.erasedCompression.path.initial = c ∧
        T.erasedCompression.path.terminal? = some T.terminal ∧
        (∀ z, (T.terminal, z) ∉
          T.erasedCompression.path.directionEdges .forward) ∧
        Alternating.BackwardLinksOn L.ladder.paths
          T.erasedCompression.path := by
  have hqSource : q.start ∈ L.lambda.source := by
    rw [hqStart, L.mem_lambda_source_old]
    exact hcFinite
  let T := L.decodeFinitePath q hqSource hqTarget
  have hTInitial : T.initial = c := by
    classical
    simp only [T]
    unfold PopularAuxiliary.Input.decodeFinitePath
    split
    · rename_i x hx
      exact PopularAuxiliary.Input.LambdaVertex.old.inj
        (x.2.2.symm.trans hqStart)
    · rename_i i hi
      exact False.elim (by
        have hproxy :
            (PopularAuxiliary.Input.LambdaVertex.proxy i.1 : LV L) =
              .old c := i.2.symm.trans hqStart
        cases hproxy)
  have hback : Alternating.BackwardLinksOn L.ladder.paths
      T.erasedCompression.path := by
    apply T.runs.erasedSignedRoute.compressionOfValid_backwardLinksOn
      (fun {_s} hs ↦ T.valid _
        (T.runs.erasedSignedRoute.steps_sublist.subset hs))
      L.ladder.disjoint
    intro s hs hdir
    simpa [PopularAuxiliary.Input.familyEdges,
      Alternating.familyEdges] using
      T.backward_on_ladder s
        (T.runs.erasedSignedRoute.steps_sublist.subset hs) hdir
  refine ⟨T, hTInitial, T.target_endpoint,
    T.erasedCompression.initial_eq.trans hTInitial,
    T.erasedCompression.terminal_eq, ?_, hback⟩
  intro z
  exact erasedCompression_terminal_not_forward_source T

end GroundingFiniteSourceDuplicateExchange

namespace DWeb.KappaLadder

open _root_.Erdos599.DirectedPath

universe w

variable {W : Type w} {Delta : DWeb W} {kappa : Cardinal.{w}}

/-- In the canonical legal input, any limiting-ladder fragment containing a
finite auxiliary source belongs to that source's grounded recorded parent.
This upgrades the existential definition of `finiteSource` to the exact
parent ownership needed in the duplicate case. -/
theorem fragment_parent_mem_groundedRecords_of_finiteSource_mem_support
    (L : Delta.KappaLadder kappa) (hlegal : L.IsLegal)
    (P : (L.popularAuxiliaryInput hlegal).Fragment) {c : W}
    (hcFinite : c ∈ (L.popularAuxiliaryInput hlegal).finiteSource)
    (hcP : c ∈ P.path.support) :
    P.parent ∈ (L.popularAuxiliaryInput hlegal).groundedRecords := by
  change c ∈ L.groundedFiniteTerminalSet at hcFinite
  obtain ⟨a, ha, q, hchosen, hterminal⟩ := hcFinite
  have hqRecord :
      q ∈ (L.popularAuxiliaryInput hlegal).groundedRecords :=
    ⟨a, ha.1, hchosen⟩
  have hqLimit : q ∈ L.limitWarp :=
    (L.groundedRecord_mem_inessentialPaths_limitWarp hlegal hqRecord).1
  have hcQ : c ∈ q.support := by
    cases q with
    | inl q =>
        change (some q.finish : Option W) = some c at hterminal
        change c ∈ q.support
        rw [← Option.some.inj hterminal]
        exact q.finish_mem_support
    | inr q =>
        change (none : Option W) = some c at hterminal
        cases hterminal
  have hparentLimit : P.parent ∈ L.limitWarp := by
    exact P.parent_mem
  have hcParent : c ∈ P.parent.support := P.support_subset hcP
  have hparent : q = P.parent :=
    Alternating.DWeb.IsWarp.eq_of_mem_support
      (hlegal.warpStages (Ladder.finalStage kappa))
      hqLimit hparentLimit hcQ hcParent
  exact hparent ▸ hqRecord

/-- If a finite auxiliary source is the terminal of a surviving fragment,
then it is also the terminal of that fragment's limiting-ladder parent. -/
theorem fragment_parent_terminal_of_finiteSource_terminal
    (L : Delta.KappaLadder kappa) (hlegal : L.IsLegal)
    (P : (L.popularAuxiliaryInput hlegal).Fragment) {c : W}
    (hcFinite : c ∈ (L.popularAuxiliaryInput hlegal).finiteSource)
    (hcTerminal : P.path.terminal? = some c) :
    Delta.terminal? P.parent = some c := by
  change c ∈ L.groundedFiniteTerminalSet at hcFinite
  obtain ⟨a, ha, q, hchosen, hqTerminal⟩ := hcFinite
  have hqRecord :
      q ∈ (L.popularAuxiliaryInput hlegal).groundedRecords :=
    ⟨a, ha.1, hchosen⟩
  have hqLimit : q ∈ L.limitWarp :=
    (L.groundedRecord_mem_inessentialPaths_limitWarp
      hlegal hqRecord).1
  have hcQ : c ∈ q.support :=
    Delta.terminal_mem_support hqTerminal
  have hcParent : c ∈ P.parent.support :=
    P.support_subset (Delta.terminal_mem_support hcTerminal)
  have hqParent : q = P.parent :=
    Alternating.DWeb.IsWarp.eq_of_mem_support
      (hlegal.warpStages (Ladder.finalStage kappa))
      hqLimit P.parent_mem hcQ hcParent
  simpa only [hqParent] using hqTerminal

/-- A target marker of the concrete auxiliary input is the initial point of
its unique limiting-ladder component. -/
theorem targetMarker_mem_initialSet_popularAuxiliary_ladder
    (L : Delta.KappaLadder kappa) (hlegal : L.IsLegal) {y : W}
    (hy : y ∈ (L.popularAuxiliaryInput hlegal).targetMarkers) :
    y ∈ Delta.initialSet
      (L.popularAuxiliaryInput hlegal).ladder.paths := by
  obtain ⟨p, hpEssential, hyp⟩ := hy.2
  have hpLimit : p ∈ L.limitWarp := hpEssential.1
  obtain ⟨a, ha⟩ := hy.1
  have htrivialSuccessor : Delta.trivialPath y ∈ L.successorWarp a :=
    (hlegal.freshMarkers.2 a y ha).2
  have htrivialStage : Delta.trivialPath y ∈
      L.warpAt (L.successorStage hlegal a) := by
    simpa only [L.warpAt_successorStage hlegal] using htrivialSuccessor
  have hmeet : ((Delta.trivialPath y).support ∩ p.support).Nonempty :=
    ⟨y, by simp, hyp⟩
  have hext : Delta.Extends (Delta.trivialPath y) p :=
    hlegal.extends_limitWarp_of_stage_intersects
      htrivialStage hpLimit hmeet
  have hpInitial : p.initial = y := by
    simpa using (Delta.extends_initial hext).symm
  exact ⟨p, by
    simpa only [KappaLadder.popularAuxiliaryInput] using hpLimit,
    hpInitial⟩

/-- A concrete target marker is either an isolated limiting-ladder
component or has the old outgoing edge required by a terminal-contact
switch.  The isolated alternative is genuine: the ladder construction
inserts markers as singleton paths, and legality alone does not assert that
every such component is later extended. -/
theorem targetMarker_isolated_or_hasOutgoing_familyEdges
    (L : Delta.KappaLadder kappa) (hlegal : L.IsLegal) {y : W}
    (hy : y ∈ (L.popularAuxiliaryInput hlegal).targetMarkers) :
    y ∈ Alternating.isolatedVertices
        (L.popularAuxiliaryInput hlegal).ladder.paths ∨
      Alternating.HasOutgoing
        (Alternating.familyEdges
          (L.popularAuxiliaryInput hlegal).ladder.paths) y := by
  have hyInitial :=
    L.targetMarker_mem_initialSet_popularAuxiliary_ladder hlegal hy
  obtain ⟨p, hp, hpInitial⟩ := hyInitial
  rw [← hpInitial]
  rcases p with p | r
  · by_cases htrivial : p.start = p.finish
    · left
      change Delta.trivialPath p.start ∈
        (L.popularAuxiliaryInput hlegal).ladder.paths
      have hpEq : (Sum.inl p : Delta.DPath) =
          Delta.trivialPath p.start := by
        rcases p with ⟨start, finish, walk, isPath⟩
        dsimp at htrivial ⊢
        subst finish
        have hwalk : walk = .nil := by
          cases hw : walk with
          | nil => rfl
          | @cons _ z _ hadj tail =>
              exfalso
              rw [hw] at isPath
              change (start :: tail.support).Nodup at isPath
              exact (List.nodup_cons.mp isPath).1
                tail.end_mem_support
        subst walk
        rfl
      exact hpEq ▸ hp
    · right
      obtain ⟨z, hz⟩ :=
        _root_.Erdos599.Alternating.FinitePath.exists_outgoing_edge_of_mem_support_of_ne_finish
          p p.start_mem_support htrivial
      exact ⟨z, Set.mem_iUnion.2 ⟨(Sum.inl p : Delta.DPath),
        Set.mem_iUnion.2 ⟨hp, hz⟩⟩⟩
  · right
    exact ⟨r 1, Set.mem_iUnion.2 ⟨(Sum.inr r : Delta.DPath),
      Set.mem_iUnion.2 ⟨hp, ⟨0, rfl⟩⟩⟩⟩

/-- Hence the blocking point of a canonical finite-source fragment is not a
target marker.  This is the precise legal-ladder invariant which excludes
the degenerate two-vertex raw-`BB` counterexample: there the earlier blocker
was itself declared to be the target marker on its grounded parent. -/
theorem blockingPoint_not_mem_targetMarkers_of_finiteSource_terminal
    (L : Delta.KappaLadder kappa) (hlegal : L.IsLegal)
    (C : Set (PopularAuxiliary.Input.LambdaVertex
      W L.groundedInfiniteRecords))
    (P : (L.popularAuxiliaryInput hlegal).Fragment) {c : W}
    (hcFinite : c ∈ (L.popularAuxiliaryInput hlegal).finiteSource)
    (hcTerminal : P.path.terminal? = some c) :
    GroundingCut.blockingPoint (L.popularAuxiliaryInput hlegal) C P ∉
      (L.popularAuxiliaryInput hlegal).targetMarkers := by
  have hcP : c ∈ P.path.support :=
    Delta.terminal_mem_support hcTerminal
  have hparentGrounded :=
    L.fragment_parent_mem_groundedRecords_of_finiteSource_mem_support
      hlegal P hcFinite hcP
  have hdisjoint :=
    L.groundedRecord_support_disjoint_targetMarkers hlegal hparentGrounded
  intro hbMarker
  apply Set.disjoint_left.1 hdisjoint
    (P.support_subset
      (GroundingCut.blockingPoint_mem_support
        (L.popularAuxiliaryInput hlegal) C P))
    hbMarker

/-- Canonical switch-ready form of the duplicate exchange.  Marker
freshness makes the decoded endpoints distinct, so chronological erasure
cannot collapse the route to a trivial alternating path.  The result is an
honest finite alternating trace from the grounded finite terminal to a
target marker outside its parent. -/
theorem exists_private_finite_exchange_of_finiteSource_duplicate
    (L : Delta.KappaLadder kappa) (hlegal : L.IsLegal)
    (C : Set (PopularAuxiliary.Input.LambdaVertex
      W L.groundedInfiniteRecords))
    (P : (L.popularAuxiliaryInput hlegal).Fragment)
    (hP : P ∈ GroundingCut.fragments
      (L.popularAuxiliaryInput hlegal) C)
    {c : W} (hcTerminal : P.path.terminal? = some c)
    (hescape : PopularAuxiliary.Input.Fragment.MeetsEscape
      (L.popularAuxiliaryInput hlegal) C P)
    (hcFinite : c ∈ (L.popularAuxiliaryInput hlegal).finiteSource)
    (hcCV : c ∈ GroundingCut.CV
      (L.popularAuxiliaryInput hlegal) C)
    (hne : GroundingCut.blockingPoint
      (L.popularAuxiliaryInput hlegal) C P ≠ c) :
    ∃ (q : FinitePath (L.popularAuxiliaryInput hlegal).lambda.graph)
        (Q : Alternating.FiniteTrace Delta.graph) (y : W),
      q.start = .old c ∧
        q.finish ∈ (L.popularAuxiliaryInput hlegal).lambda.target ∧
        (L.popularAuxiliaryInput hlegal).lambda.Avoids q
          (C \ {(.old c : PopularAuxiliary.Input.LambdaVertex
            W L.groundedInfiniteRecords)}) ∧
        q.support ∩ C =
          {(.old c : PopularAuxiliary.Input.LambdaVertex
            W L.groundedInfiniteRecords)} ∧
        q.support ∩
          (L.popularAuxiliaryInput hlegal).lambda.target ⊆ {q.finish} ∧
        (Alternating.AltPath.finite Q).initial = c ∧
        (Alternating.AltPath.finite Q).terminal? = some y ∧
        y ∈ (L.popularAuxiliaryInput hlegal).targetMarkers ∧
        y ∉ P.parent.support ∧
        c ∈ Delta.terminalFrontier
          (L.popularAuxiliaryInput hlegal).ladder.paths ∧
        y ∈ Delta.initialSet
          (L.popularAuxiliaryInput hlegal).ladder.paths ∧
        (∀ z, (y, z) ∉
          (Alternating.AltPath.finite Q).directionEdges .forward) ∧
        Alternating.BackwardLinksOn
          (L.popularAuxiliaryInput hlegal).ladder.paths
          (.finite Q) := by
  obtain ⟨q, A, y, hqStart, hqTarget, hqAvoid, hqPrivate,
      hqPure, hAInitial, hATerminal, hyTarget, hyNoForward, hback⟩ :=
    _root_.Erdos599.GroundingFiniteSourceDuplicateExchange.exists_private_decoded_exchange_of_finiteSource_duplicate
        (L.popularAuxiliaryInput hlegal) C P hP hcTerminal
        hescape hcFinite hcCV hne
  have hcP : c ∈ P.path.support :=
    Delta.terminal_mem_support hcTerminal
  have hparentGrounded :=
    L.fragment_parent_mem_groundedRecords_of_finiteSource_mem_support
      hlegal P hcFinite hcP
  have hdisjoint :=
    L.groundedRecord_support_disjoint_targetMarkers
      hlegal hparentGrounded
  have hyParent : y ∉ P.parent.support := by
    intro hy
    exact Set.disjoint_left.1 hdisjoint hy hyTarget
  have hcy : c ≠ y := by
    intro h
    apply hyParent
    exact h ▸ P.support_subset hcP
  have hcFrontier : c ∈ Delta.terminalFrontier
      (L.popularAuxiliaryInput hlegal).ladder.paths := by
    refine ⟨P.parent, P.parent_mem, ?_⟩
    exact L.fragment_parent_terminal_of_finiteSource_terminal
      hlegal P hcFinite hcTerminal
  have hyInitial : y ∈ Delta.initialSet
      (L.popularAuxiliaryInput hlegal).ladder.paths :=
    L.targetMarker_mem_initialSet_popularAuxiliary_ladder
      hlegal hyTarget
  cases hA : A with
  | trivial a =>
      have hac : a = c := by
        simpa only [hA, Alternating.AltPath.initial_trivial] using hAInitial
      have hay : a = y := by
        simpa only [hA, Alternating.AltPath.terminal?_trivial,
          Option.some.injEq] using hATerminal
      exact False.elim (hcy (hac.symm.trans hay))
  | finite Q =>
      refine ⟨q, Q, y, hqStart, hqTarget, hqAvoid, hqPrivate,
        hqPure, ?_, ?_, hyTarget, hyParent, hcFrontier, hyInitial,
        ?_, ?_⟩
      · simpa only [hA] using hAInitial
      · simpa only [hA] using hATerminal
      · simpa only [hA] using hyNoForward
      · simpa only [hA] using hback
  | infinite r =>
      have : (none : Option W) = some y := by
        simpa only [hA, Alternating.AltPath.terminal?_infinite] using hATerminal
      cases this

end DWeb.KappaLadder
end Erdos599

#print axioms Erdos599.GroundingFiniteSourceDuplicateExchange.CE_diff_singleton_old
#print axioms Erdos599.GroundingFiniteSourceDuplicateExchange.exists_pathTo_support_edgeSet_subset
#print axioms Erdos599.GroundingFiniteSourceDuplicateExchange.fragments_diff_singleton_old
#print axioms Erdos599.GroundingFiniteSourceDuplicateExchange.exists_private_reverse_to_relaxedEscape
#print axioms Erdos599.GroundingFiniteSourceDuplicateExchange.exists_private_source_target_path_of_finiteSource_duplicate
#print axioms Erdos599.GroundingFiniteSourceDuplicateExchange.exists_private_decoded_exchange_of_finiteSource_duplicate
#print axioms Erdos599.GroundingFiniteSourceDuplicateExchange.exists_microTrace_of_finiteSource_target_path
#print axioms Erdos599.GroundingFiniteSourceDuplicateExchange.erasedCompression_terminal_not_forward_source
#print axioms Erdos599.GroundingFiniteSourceDuplicateExchange.erasedCompression_forwardLinksOff_of_forward_not_mem
#print axioms Erdos599.DWeb.KappaLadder.fragment_parent_mem_groundedRecords_of_finiteSource_mem_support
#print axioms Erdos599.DWeb.KappaLadder.fragment_parent_terminal_of_finiteSource_terminal
#print axioms Erdos599.DWeb.KappaLadder.targetMarker_mem_initialSet_popularAuxiliary_ladder
#print axioms Erdos599.DWeb.KappaLadder.targetMarker_isolated_or_hasOutgoing_familyEdges
#print axioms Erdos599.DWeb.KappaLadder.blockingPoint_not_mem_targetMarkers_of_finiteSource_terminal
#print axioms Erdos599.DWeb.KappaLadder.exists_private_finite_exchange_of_finiteSource_duplicate
