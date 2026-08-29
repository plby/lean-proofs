/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingCut
import ErdosProblems.Erdos599.RelationComponents
import ErdosProblems.Erdos599.LambdaDecoder
import ErdosProblems.Erdos599.AlternatingTraceOps

/-!
# Endpoint transport for the grounding-cut decoder

The reverse part of a `Lambda` route is carried by edge gadgets.  If the
route has arrived at the gadget for the ladder edge `x -> y`, then it leaves
that gadget at the old vertex `x`.  Consequently every nontrivial auxiliary
path beginning at `old x` can instead begin at `edge x y`.  The first theorem
below is the one-arc form of this observation; the second theorem performs
the replacement on a whole path and erases any loop it creates.

The final two lemmas record an important endpoint fact literally forced by
the six arc classes defining `Lambda`: entering the gadget for an edge
`u -> v` directly from `old v`, or leaving it directly for `old u`, requires
a loop in the original digraph.  Thus a backwards fragment cannot in general
be packaged as an `old x`--`old y` auxiliary path.  It has to be spliced to
the following escape while its endpoint is still an edge gadget.
-/

noncomputable section

open Set

namespace Erdos599
namespace GroundingCutDecoder

open DirectedPath

universe u v

variable {V : Type u} {I : Type v} {Gamma : DWeb V}

abbrev Input (Gamma : DWeb V) (I : Type v) : Type (max u v) :=
  PopularAuxiliary.Input Gamma I

abbrev LV (L : Input Gamma I) : Type (max u v) :=
  PopularAuxiliary.Input.LambdaVertex V I

/-! ## Replacing the old initial gadget of an escape -/

/-- An edge gadget with exit `x` has every successor that `old x` has,
provided the represented edge belongs to the ladder family. -/
theorem lambda_adj_edge_of_old
    (L : Input Gamma I) {x y : V} (hxy : (x, y) ∈ L.familyEdges)
    {b : LV L} (h : L.lambda.graph.Adj (.old x) b) :
    L.lambda.graph.Adj (.edge x y) b := by
  cases b with
  | old z =>
      have hz := (L.lambda_adj_old_old x z).1 h
      exact (L.lambda_adj_edge_old x y z).2 ⟨hxy, Or.inr hz.2⟩
  | edge z w =>
      have hzw := (L.lambda_adj_old_edge x z w).1 h
      refine (L.lambda_adj_edge_edge x y z w).2
        ⟨hxy, hzw.1, ?_⟩
      exact hzw.2.elim Or.inl (fun hforward ↦ Or.inr hforward.2)
  | proxy j =>
      exact False.elim (L.lambda_not_adj_to_proxy (.old x) j h)

/-- If a represented family edge was not deleted by `C`, its edge gadget
does not belong to `C`. -/
theorem edge_not_mem_cut_of_not_mem_CE
    (L : Input Gamma I) (C : Set (LV L)) {x y : V}
    (hxy : (x, y) ∈ L.familyEdges)
    (hnot : (x, y) ∉ GroundingCut.CE L C) :
    PopularAuxiliary.Input.LambdaVertex.edge x y ∉ C := by
  intro hedge
  exact hnot ⟨hedge, hxy⟩

/-! ## Literal reverse traversal of a finite original walk -/

/-- Reverse all the edge gadgets of a nonempty original walk, stopping at
the gadget for its first edge.  No old vertex is inserted between two
successive edge gadgets. -/
def reverseGadgetCore (L : Input Gamma I) :
    ∀ {a c b : V} (h : Gamma.graph.Adj a c)
      (q : Walk Gamma.graph c b),
      (a, c) ∈ L.familyEdges → q.edgeSet ⊆ L.familyEdges →
        Walk L.lambda.graph (.old b) (.edge a c)
  | a, c, _, h, .nil, hac, _ =>
      .cons ((L.lambda_adj_old_edge c a c).2 ⟨hac, Or.inl rfl⟩) .nil
  | a, c, _, h, @Walk.cons _ _ _ d _ hcd r, hac, hfamily => by
      have hcdFamily : (c, d) ∈ L.familyEdges := hfamily (by simp)
      have hrFamily : r.edgeSet ⊆ L.familyEdges := by
        intro e he
        exact hfamily (by simp [he])
      exact (reverseGadgetCore L hcd r hcdFamily hrFamily).concat <|
        (L.lambda_adj_edge_edge c d a c).2
          ⟨hcdFamily, hac, Or.inl rfl⟩

/-- The complete reverse gadget walk.  Its only old vertices are its two
endpoints; all internal vertices represent edges of the original walk. -/
def reverseGadgetWalk (L : Input Gamma I) :
    ∀ {a b : V} (p : Walk Gamma.graph a b),
      p.edgeSet ⊆ L.familyEdges →
        Walk L.lambda.graph (.old b) (.old a)
  | _, _, .nil, _ => .nil
  | a, _, @Walk.cons _ _ _ c _ h q, hfamily => by
      have hac : (a, c) ∈ L.familyEdges := hfamily (by simp)
      have hqFamily : q.edgeSet ⊆ L.familyEdges := by
        intro e he
        exact hfamily (by simp [he])
      exact (reverseGadgetCore L h q hac hqFamily).concat
        ((L.lambda_adj_edge_old a c a).2 ⟨hac, Or.inl rfl⟩)

/-- Every vertex of the core reverse walk is either its initial old vertex
or an edge gadget belonging to the original nonempty walk. -/
theorem mem_reverseGadgetCore_support
    (L : Input Gamma I) {a c b : V} (h : Gamma.graph.Adj a c)
    (q : Walk Gamma.graph c b)
    (hac : (a, c) ∈ L.familyEdges)
    (hfamily : q.edgeSet ⊆ L.familyEdges) {z : LV L}
    (hz : z ∈ (reverseGadgetCore L h q hac hfamily).support) :
    z = .old b ∨
      ∃ e ∈ (Walk.cons h q).edgeSet,
        z = PopularAuxiliary.Input.LambdaVertex.edge e.1 e.2 := by
  induction q generalizing a with
  | nil =>
      simp [reverseGadgetCore] at hz ⊢
      exact hz
  | @cons c d b hcd r ih =>
      have hcdFamily : (c, d) ∈ L.familyEdges := hfamily (by simp)
      have hrFamily : r.edgeSet ⊆ L.familyEdges := by
        intro e he
        exact hfamily (by simp [he])
      simp only [reverseGadgetCore, Walk.support_concat,
        Walk.support_cons, List.tail_cons, List.nil_append,
        List.mem_append, List.mem_cons, List.not_mem_nil] at hz
      rcases hz with hz | hz
      · rcases ih hcd hcdFamily hrFamily hz with hzold | ⟨e, he, hze⟩
        · exact Or.inl hzold
        · exact Or.inr ⟨e, by simp only [Walk.edgeSet_cons,
              Set.mem_union, Set.mem_singleton_iff]; exact Or.inr he,
            hze⟩
      · have hza : z = .edge a c := by simpa using hz
        exact Or.inr ⟨(a, c), by simp, by simpa using hza⟩

/-- Support accounting for the complete reverse gadget walk. -/
theorem mem_reverseGadgetWalk_support
    (L : Input Gamma I) {a b : V} (p : Walk Gamma.graph a b)
    (hfamily : p.edgeSet ⊆ L.familyEdges) {z : LV L}
    (hz : z ∈ (reverseGadgetWalk L p hfamily).support) :
    z = .old a ∨ z = .old b ∨
      ∃ e ∈ p.edgeSet,
        z = PopularAuxiliary.Input.LambdaVertex.edge e.1 e.2 := by
  cases p with
  | nil =>
      simpa [reverseGadgetWalk] using hz
  | @cons a c b h q =>
      have hac : (a, c) ∈ L.familyEdges := hfamily (by simp)
      have hqFamily : q.edgeSet ⊆ L.familyEdges := by
        intro e he
        exact hfamily (by simp [he])
      simp only [reverseGadgetWalk, Walk.support_concat,
        Walk.support_cons, List.tail_cons, List.nil_append,
        List.mem_append, List.mem_cons, List.not_mem_nil] at hz
      rcases hz with hz | hz
      · rcases mem_reverseGadgetCore_support L h q hac hqFamily hz with
          hzold | ⟨e, he, hze⟩
        · exact Or.inr (Or.inl hzold)
        · exact Or.inr (Or.inr ⟨e, he, hze⟩)
      · exact Or.inl (by simpa using hz)

/-- Loop-erasing the raw reverse traversal gives a simple auxiliary path.
Avoidance requires only that its two old endpoints avoid `C` and that none
of the represented original edges was deleted by `C`. -/
theorem exists_avoiding_reverseGadgetPath
    (L : Input Gamma I) (C : Set (LV L))
    {a b : V} (p : Walk Gamma.graph a b)
    (hfamily : p.edgeSet ⊆ L.familyEdges)
    (hdeleted : Disjoint p.edgeSet (GroundingCut.CE L C))
    (ha : (PopularAuxiliary.Input.LambdaVertex.old a : LV L) ∉ C)
    (hb : (PopularAuxiliary.Input.LambdaVertex.old b : LV L) ∉ C) :
    ∃ r : FinitePath L.lambda.graph,
      r.start = .old b ∧ r.finish = .old a ∧
        L.lambda.Avoids r C := by
  let w := reverseGadgetWalk L p hfamily
  obtain ⟨q, hqSupport⟩ :=
    RelationalRoof.exists_pathTo_support_subset
      (R := L.lambda.graph.Adj) w
  let r : FinitePath L.lambda.graph :=
    { start := .old b
      finish := .old a
      walk := q.1
      isPath := q.2 }
  refine ⟨r, rfl, rfl, ?_⟩
  change Disjoint r.support C
  rw [Set.disjoint_left]
  intro z hzr hzC
  have hzw : z ∈ w.support := hqSupport hzr
  rcases mem_reverseGadgetWalk_support L p hfamily hzw with
      hza | hzb | ⟨e, hep, hze⟩
  · exact ha (hza ▸ hzC)
  · exact hb (hzb ▸ hzC)
  · subst z
    have heFamily : e ∈ L.familyEdges := hfamily hep
    have heNotCE : e ∉ GroundingCut.CE L C :=
      Set.disjoint_left.1 hdeleted hep
    exact edge_not_mem_cut_of_not_mem_CE L C heFamily heNotCE hzC

/-! ## Extracting the forward segment named by `Before` -/

/-- The first `n` edges of a ray beginning at index `i`. -/
def raySegmentWalk (r : Ray Gamma.graph) (i : ℕ) :
    (n : ℕ) → Walk Gamma.graph (r i) (r (i + n))
  | 0 => .nil
  | n + 1 =>
      (raySegmentWalk r i n).concat (by
        simpa [Nat.add_assoc] using r.adj_succ (i + n))

@[simp] theorem raySegmentWalk_support
    (r : Ray Gamma.graph) (i n : ℕ) :
    (raySegmentWalk r i n).support =
      List.ofFn (fun k : Fin (n + 1) ↦ r (i + k)) := by
  induction n with
  | zero => simp [raySegmentWalk]
  | succ n ih =>
      rw [raySegmentWalk, Walk.support_concat, ih]
      rw [@List.ofFn_succ_last V (n + 1)
        (fun k : Fin ((n + 1) + 1) ↦ r (i + k))]
      congr 1 <;> simp [Nat.add_assoc]

theorem raySegmentWalk_isPath
    (r : Ray Gamma.graph) (i n : ℕ) :
    (raySegmentWalk r i n).IsPath := by
  rw [Walk.isPath_iff, raySegmentWalk_support]
  exact List.nodup_ofFn.mpr fun j k hjk ↦ by
    apply Fin.ext
    exact Nat.add_left_cancel (r.injective hjk)

/-- The corresponding finite ray segment. -/
def raySegmentPath (r : Ray Gamma.graph) (i n : ℕ) :
    FinitePath Gamma.graph where
  start := r i
  finish := r (i + n)
  walk := raySegmentWalk r i n
  isPath := raySegmentWalk_isPath r i n

theorem raySegmentPath_edgeSet_subset
    (r : Ray Gamma.graph) (i n : ℕ) :
    (raySegmentPath r i n).edgeSet ⊆ r.edgeSet := by
  intro e he
  change e ∈ (raySegmentWalk r i n).edgeSet at he
  induction n with
  | zero => simpa [raySegmentWalk, Walk.edgeSet] using he
  | succ n ih =>
      rw [raySegmentWalk,
        Alternating.RelationComponents.walkEdgeSetConcatRC] at he
      rcases he with he | he
      · exact ih he
      · have hi : i + (n + 1) = i + n + 1 := by omega
        rw [hi] at he
        exact ⟨i + n, he⟩

/-- Strict order on a finite path or ray supplies its literal forward
finite segment, with no new directed edges. -/
theorem exists_forward_segment_of_before
    {P : Gamma.DPath} {a b : V}
    (hab : GroundingCut.Before P a b) :
    ∃ p : FinitePath Gamma.graph,
      p.start = a ∧ p.finish = b ∧ p.edgeSet ⊆ P.edgeSet := by
  rcases hab with ⟨⟨m, n, hma, hnb, hmn⟩, habne⟩
  cases P with
  | inl P =>
      rcases hma with ⟨hmLen, hma⟩
      rcases hnb with ⟨hnLen, hnb⟩
      have hmnlt : m < n := by
        apply lt_of_le_of_ne hmn
        intro hmnEq
        subst n
        exact habne (hma.symm.trans hnb)
      have hsuffix :
          P.walk.support = P.walk.support.take m ++
            a :: P.walk.support.drop (m + 1) := by
        calc
          P.walk.support = P.walk.support.take m ++ P.walk.support.drop m :=
            (List.take_append_drop m P.walk.support).symm
          _ = P.walk.support.take m ++
              P.walk.support[m] :: P.walk.support.drop (m + 1) := by
            rw [List.drop_eq_getElem_cons hmLen]
          _ = P.walk.support.take m ++
              a :: P.walk.support.drop (m + 1) := by rw [hma]
      have hindex : n - (m + 1) <
          (P.walk.support.drop (m + 1)).length := by
        simp only [List.length_drop]
        omega
      have hget :
          (P.walk.support.drop (m + 1))[n - (m + 1)] = b := by
        rw [List.getElem_drop]
        simpa [Nat.add_sub_of_le (Nat.succ_le_iff.2 hmnlt)] using hnb
      have hbSuffix : b ∈ P.walk.support.drop (m + 1) := by
        rw [← hget]
        exact List.getElem_mem hindex
      obtain ⟨hocc⟩ :=
        FinitePath.OrderedOccurrence.nonempty_of_mem_suffix
          (p := P) (x := a) (y := b)
          (P.walk.support.take m) (P.walk.support.drop (m + 1))
          hsuffix hbSuffix
      exact ⟨P.between hocc, rfl, rfl,
        P.between_edgeSet_subset hocc⟩
  | inr r =>
      change r m = a at hma
      change r n = b at hnb
      have hmnlt : m < n := by
        apply lt_of_le_of_ne hmn
        intro hmnEq
        subst n
        exact habne (hma.symm.trans hnb)
      let p := raySegmentPath (Gamma := Gamma) r m (n - m)
      refine ⟨p, ?_, ?_, ?_⟩
      · exact hma
      · change r (m + (n - m)) = b
        simpa [Nat.add_sub_of_le hmn] using hnb
      · exact raySegmentPath_edgeSet_subset r m (n - m)

/-! ## The concrete backwards decoder and Assertion 8.21 -/

/-- A surviving fragment segment decodes backwards to a cut-avoiding
auxiliary path as soon as its two displayed old endpoints avoid the cut.
All internal auxiliary vertices are edge gadgets, so no unrecorded old
vertex avoidance premise is needed. -/
theorem backwardDecode
    (L : Input Gamma I) (C : Set (LV L))
    (P : L.Fragment) (hfragment : P ∈ GroundingCut.fragments L C)
    {a b : V}
    (ha : (PopularAuxiliary.Input.LambdaVertex.old a : LV L) ∉ C)
    (hb : (PopularAuxiliary.Input.LambdaVertex.old b : LV L) ∉ C)
    (hab : GroundingCut.Before P.path a b) :
    ∃ r : FinitePath L.lambda.graph,
      r.start = .old b ∧ r.finish = .old a ∧
        L.lambda.Avoids r C := by
  obtain ⟨p, hpstart, hpfinish, hpEdges⟩ :=
    exists_forward_segment_of_before hab
  have hpFamily : p.walk.edgeSet ⊆ L.familyEdges := by
    intro e he
    exact ⟨P.parent, P.parent_mem,
      P.edges_subset (hpEdges he)⟩
  have hpDeleted : Disjoint p.walk.edgeSet (GroundingCut.CE L C) :=
    hfragment.1.mono hpEdges Subset.rfl
  have ha' :
      (PopularAuxiliary.Input.LambdaVertex.old p.start : LV L) ∉ C := by
    simpa only [hpstart] using ha
  have hb' :
      (PopularAuxiliary.Input.LambdaVertex.old p.finish : LV L) ∉ C := by
    simpa only [hpfinish] using hb
  obtain ⟨r, hrstart, hrfinish, hravoid⟩ :=
    exists_avoiding_reverseGadgetPath L C p.walk hpFamily hpDeleted ha' hb'
  exact ⟨r, by simpa [hpfinish] using hrstart,
    by simpa [hpstart] using hrfinish, hravoid⟩

/-! ## Absorbing a source-faithful open escape -/

/-- A represented ladder-edge gadget has the virtual forward successor
specified by a relaxed first occurrence at its tail. -/
theorem lambda_adj_edge_of_relaxedForwardStep
    (L : Input Gamma I) {x z : V} {a : LV L}
    (hxz : (x, z) ∈ L.familyEdges)
    (ha : L.RelaxedForwardStep x a) :
    L.lambda.graph.Adj (.edge x z) a := by
  cases a with
  | old y =>
      exact (L.lambda_adj_edge_old x z y).2
        ⟨hxz, Or.inr ha⟩
  | edge u y =>
      exact (L.lambda_adj_edge_edge x z u y).2
        ⟨hxz, ha.1, Or.inr ha.2⟩
  | proxy i => exact False.elim ha

private theorem reverseCore_avoids
    (L : Input Gamma I) (C : Set (LV L))
    {P : L.Fragment} (hP : P ∈ GroundingCut.fragments L C)
    {a c b : V} (hac : Gamma.graph.Adj a c)
    (q : Walk Gamma.graph c b)
    (hsegment : (Walk.cons hac q).edgeSet ⊆ P.path.edgeSet)
    (hacFamily : (a, c) ∈ L.familyEdges)
    (hqFamily : q.edgeSet ⊆ L.familyEdges)
    (hb : (PopularAuxiliary.Input.LambdaVertex.old b : LV L) ∉ C) :
    Disjoint
      ({w | w ∈
        (reverseGadgetCore L hac q hacFamily hqFamily).support} :
        Set (LV L)) C := by
  rw [Set.disjoint_left]
  intro w hw hCw
  rcases mem_reverseGadgetCore_support
      L hac q hacFamily hqFamily hw with rfl | ⟨e, he, rfl⟩
  · exact hb hCw
  · have heFragment : e ∈ P.path.edgeSet := hsegment he
    have heNotCE : e ∉ GroundingCut.CE L C :=
      Set.disjoint_left.1 hP.1 heFragment
    have heFamily : e ∈ L.familyEdges :=
      ⟨P.parent, P.parent_mem, P.edges_subset heFragment⟩
    exact edge_not_mem_cut_of_not_mem_CE
      L C heFamily heNotCE hCw

/-- Traversing a nonempty surviving fragment backwards absorbs the virtual
first connector of a relaxed escape.  The result starts at the old
occurrence of the later fragment point and ends at the auxiliary target. -/
theorem exists_avoiding_reverse_to_relaxedEscape
    (L : Input Gamma I) (C : Set (LV L))
    (P : L.Fragment) (hP : P ∈ GroundingCut.fragments L C)
    {b x : V} (hbx : GroundingCut.Before P.path b x)
    (hxNotC : (PopularAuxiliary.Input.LambdaVertex.old x : LV L) ∉ C)
    (E : L.RelaxedEscape C b) :
    ∃ r : FinitePath L.lambda.graph,
      r.start = .old x ∧ r.finish ∈ L.lambda.target ∧
        L.lambda.Avoids r C := by
  rcases E.start_eq with hordinary | hrelaxed
  · obtain ⟨p, hpStart, hpFinish, hpAvoid⟩ :=
      backwardDecode L C P hP E.old_not_mem hxNotC hbx
    obtain ⟨r, hrStart, hrFinish, hrAvoid⟩ :=
      PopularSwitching.exists_avoiding_path_of_avoiding_paths
        p E.route (hpFinish.trans hordinary.symm) hpAvoid E.avoids
    exact ⟨r, hrStart.trans hpStart, hrFinish ▸ E.target, hrAvoid⟩
  · obtain ⟨p, hpStart, hpFinish, hpEdges⟩ :=
      exists_forward_segment_of_before hbx
    have hpNe : p.start ≠ p.finish := by
      intro h
      exact hbx.2 (hpStart.symm.trans (h.trans hpFinish))
    obtain ⟨c, hac, tail, hpWalk⟩ :=
      RelationalRoof.exists_cons_of_start_ne_finish
        Gamma.graph.Adj p.walk hpNe
    have hacEdge : (p.start, c) ∈ p.edgeSet := by
      change (p.start, c) ∈ p.walk.edgeSet
      rw [hpWalk]
      simp
    have hacFragment : (p.start, c) ∈ P.path.edgeSet := hpEdges hacEdge
    have hacFamily : (p.start, c) ∈ L.familyEdges :=
      ⟨P.parent, P.parent_mem, P.edges_subset hacFragment⟩
    have htailFamily : tail.edgeSet ⊆ L.familyEdges := by
      intro e he
      have hep : e ∈ p.edgeSet := by
        change e ∈ p.walk.edgeSet
        rw [hpWalk]
        exact Set.mem_union_right _ he
      have heFragment := hpEdges hep
      exact ⟨P.parent, P.parent_mem, P.edges_subset heFragment⟩
    have hwholeFragment :
        (Walk.cons hac tail).edgeSet ⊆ P.path.edgeSet := by
      intro e he
      apply hpEdges
      change e ∈ p.walk.edgeSet
      simpa only [hpWalk] using he
    let core : Walk L.lambda.graph
        (.old p.finish) (.edge p.start c) :=
      reverseGadgetCore L hac tail hacFamily htailFamily
    have hcoreAvoid : Disjoint
        ({w | w ∈ core.support} : Set (LV L)) C := by
      apply reverseCore_avoids L C hP hac tail hwholeFragment
        hacFamily htailFamily
      simpa only [hpFinish] using hxNotC
    have hjoin : L.lambda.graph.Adj (.edge p.start c) E.route.start := by
      apply lambda_adj_edge_of_relaxedForwardStep L hacFamily
      simpa only [hpStart] using hrelaxed
    let suffix : Walk L.lambda.graph (.edge p.start c) E.route.finish :=
      .cons hjoin E.route.walk
    let raw : Walk L.lambda.graph (.old p.finish) E.route.finish :=
      core.append suffix
    obtain ⟨q, hqSupport⟩ :=
      RelationalRoof.exists_pathTo_support_subset
        (R := L.lambda.graph.Adj) raw
    let r : FinitePath L.lambda.graph :=
      { start := .old p.finish
        finish := E.route.finish
        walk := q.1
        isPath := q.2 }
    refine ⟨r, by simpa only [r, hpFinish], E.target, ?_⟩
    change Disjoint r.support C
    rw [Set.disjoint_left]
    intro w hwr hwC
    have hwRaw : w ∈ raw.support := hqSupport hwr
    have hwAppend : w ∈ core.support ++ suffix.support.tail := by
      simpa only [raw, Walk.support_append] using hwRaw
    rcases List.mem_append.mp hwAppend with hwCore | hwSuffix
    · exact Set.disjoint_left.1 hcoreAvoid hwCore hwC
    · have hwRoute : w ∈ E.route.support := by
        change w ∈ E.route.walk.support
        simpa only [suffix, Walk.support_cons, List.tail_cons] using hwSuffix
      exact Set.disjoint_left.1 E.avoids hwRoute hwC

theorem occursAt_index_injective
    {P : Gamma.DPath} {m n : ℕ} {x : V}
    (hm : GroundingCut.OccursAt P m x)
    (hn : GroundingCut.OccursAt P n x) : m = n := by
  cases P with
  | inl p =>
      rcases hm with ⟨hmLen, hm⟩
      rcases hn with ⟨hnLen, hn⟩
      have hfin : (⟨m, hmLen⟩ : Fin p.walk.support.length) =
          ⟨n, hnLen⟩ :=
        p.isPath.get_inj_iff.mp (hm.trans hn.symm)
      exact congrArg Fin.val hfin
  | inr r =>
      exact r.injective (hm.trans hn.symm)

theorem beforeEq_antisymm
    {P : Gamma.DPath} {a b : V}
    (hab : GroundingCut.BeforeEq P a b)
    (hba : GroundingCut.BeforeEq P b a) : a = b := by
  rcases hab with ⟨m, n, hma, hnb, hmn⟩
  rcases hba with ⟨p, q, hpb, hqa, hpq⟩
  have hqm : q = m := (occursAt_index_injective hma hqa).symm
  subst q
  have hpn : p = n := (occursAt_index_injective hnb hpb).symm
  subst p
  have hmnEq : m = n := le_antisymm hmn hpq
  subst n
  cases P with
  | inl P =>
      rcases hma with ⟨hmLen, hma⟩
      rcases hnb with ⟨hnLen, hnb⟩
      exact hma.symm.trans hnb
  | inr r =>
      change r m = a at hma
      change r m = b at hnb
      exact hma.symm.trans hnb

/-- Assertion 8.21 with its backwards decoder discharged by the literal
edge-gadget traversal. -/
theorem assertion8_21
    (L : Input Gamma I) (C : Set (LV L))
    (hC : Popular.IsSeparator L.lambda C)
    (P : L.Fragment) (hP : P ∈ GroundingCut.G0 L C)
    (q : FinitePath L.lambda.graph)
    (hqstart : q.start ∈ L.lambda.source)
    (hqavoid : L.lambda.Avoids q C) {x : V}
    (hqfinish : q.finish = .old x)
    (hxP : x ∈ P.path.support) :
    GroundingCut.BeforeEq P.path x
      (GroundingCut.blockingPoint L C P) := by
  apply GroundingCut.assertion8_21 L C hC P hP q hqstart hqavoid
    hqfinish hxP
  intro hbefore E
  have hxNotC :
      (PopularAuxiliary.Input.LambdaVertex.old x : LV L) ∉ C := by
    intro hxC
    exact Set.disjoint_left.1 hqavoid q.finish_mem_support
      (hqfinish ▸ hxC)
  exact exists_avoiding_reverse_to_relaxedEscape
    L C P hP.1 hbefore hxNotC E

/-- Replace the first `old x` vertex of a nontrivial escaping path by the
gadget for a surviving edge `x -> y`.  Loop erasure makes the construction
valid even when the new edge gadget occurred later on the original path.

This is the endpoint-splicing operation needed after a backwards traversal
of a surviving ladder fragment: one must splice *before* trying to turn that
traversal into an old-to-old auxiliary path. -/
theorem exists_avoiding_path_from_edge_of_old_start
    (L : Input Gamma I) (C : Set (LV L)) {x y : V}
    (hxy : (x, y) ∈ L.familyEdges)
    (hnotCE : (x, y) ∉ GroundingCut.CE L C)
    (q : FinitePath L.lambda.graph)
    (hqstart : q.start = .old x)
    (hxnotTarget :
      (PopularAuxiliary.Input.LambdaVertex.old x : LV L) ∉ L.lambda.target)
    (hqfinish : q.finish ∈ L.lambda.target)
    (hqavoid : L.lambda.Avoids q C) :
    ∃ r : FinitePath L.lambda.graph,
      r.start = .edge x y ∧ r.finish = q.finish ∧
        L.lambda.Avoids r C := by
  have hxNotFinish : (PopularAuxiliary.Input.LambdaVertex.old x : LV L) ≠
      q.finish := by
    intro hx
    exact hxnotTarget (hx ▸ hqfinish)
  have hstartFinish : q.start ≠ q.finish := by
    intro heq
    exact hxNotFinish (hqstart ▸ heq)
  obtain ⟨b, hab, tail, hwalk⟩ :=
    RelationalRoof.exists_cons_of_start_ne_finish
      L.lambda.graph.Adj q.walk hstartFinish
  have holdb : L.lambda.graph.Adj
      (PopularAuxiliary.Input.LambdaVertex.old x) b := by
    simpa only [hqstart] using hab
  have hedgeB : L.lambda.graph.Adj
      (PopularAuxiliary.Input.LambdaVertex.edge x y) b :=
    lambda_adj_edge_of_old L hxy holdb
  let w : Walk L.lambda.graph
      (PopularAuxiliary.Input.LambdaVertex.edge x y) q.finish :=
    .cons hedgeB tail
  obtain ⟨p, hpSupport⟩ :=
    RelationalRoof.exists_pathTo_support_subset
      (R := L.lambda.graph.Adj) w
  let r : FinitePath L.lambda.graph :=
    { start := .edge x y
      finish := q.finish
      walk := p.1
      isPath := p.2 }
  refine ⟨r, rfl, rfl, ?_⟩
  change Disjoint r.support C
  rw [Set.disjoint_left]
  intro z hzr hzC
  have hzw : z ∈ w.support := hpSupport hzr
  simp only [w, Walk.support_cons, List.mem_cons] at hzw
  rcases hzw with hze | hztail
  · subst z
    exact edge_not_mem_cut_of_not_mem_CE L C hxy hnotCE hzC
  · have hzq : z ∈ q.support := by
      change z ∈ q.walk.support
      rw [hwalk]
      simp only [Walk.support_cons, List.mem_cons]
      exact Or.inr hztail
    exact Set.disjoint_left.1 hqavoid hzq hzC

/-! ## The literal endpoint obstruction in the six arc classes -/

/-- Directly entering the backwards gadget for `u -> v` from its head `v`
is always possible for a represented ladder edge.  The zero-length equality
join deliberately bypasses the old-vertex retention side condition. -/
theorem lambda_adj_old_head_to_edge_iff
    (L : Input Gamma I) (u v : V) :
    L.lambda.graph.Adj (.old v) (.edge u v) ↔
      (u, v) ∈ L.familyEdges := by
  rw [L.lambda_adj_old_edge]
  simp

/-- Directly leaving the backwards gadget for `u -> v` at its tail `u`
is always possible for a represented ladder edge.  This is the terminal
zero-length equality join of a reverse segment. -/
theorem lambda_adj_edge_to_old_tail_iff
    (L : Input Gamma I) (u v : V) :
    L.lambda.graph.Adj (.edge u v) (.old u) ↔
      (u, v) ∈ L.familyEdges := by
  rw [L.lambda_adj_edge_old]
  simp

theorem lambda_adj_old_head_to_edge
    (L : Input Gamma I) {u v : V} (h : (u, v) ∈ L.familyEdges) :
    L.lambda.graph.Adj (.old v) (.edge u v) :=
  (lambda_adj_old_head_to_edge_iff L u v).2 h

theorem lambda_adj_edge_to_old_tail
    (L : Input Gamma I) {u v : V} (h : (u, v) ∈ L.familyEdges) :
    L.lambda.graph.Adj (.edge u v) (.old u) :=
  (lambda_adj_edge_to_old_tail_iff L u v).2 h

end GroundingCutDecoder
end Erdos599
