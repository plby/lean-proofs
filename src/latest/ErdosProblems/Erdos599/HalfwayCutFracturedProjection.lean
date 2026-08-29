/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayCutConstruction

/-!
# Projecting the literal split cut family

`OutsideSplitWarp` is the genuine family of components obtained after every
retained edge incident with the closing set has been given an incoming or an
outgoing endpoint copy.  This file projects those components back to the
original web.  The rank retained by `OutsideSplitWarp` proves that projection
is injective on each component.  Distinct projected components can meet only
when one ends and the other starts at the same cut vertex, which is exactly
the permitted intersection in `FracturedWarp`.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace Blueprint
namespace LinkageBlueprint

open DirectedPath Alternating
open FracturedDuplication

universe u

variable {V : Type u}
variable {Gamma : DWeb V}

namespace OutsideSplitWarp

variable {W : Set Gamma.DPath} {X : Set V}

/-- The finite representative of one member of the split family. -/
noncomputable def finitePath (S : OutsideSplitWarp W X)
    (p : {p // p ∈ S.paths}) :
    FinitePath (CutSplit.web Gamma).graph :=
  (S.finiteCharacter p.property).choose

@[simp] theorem finitePath_eq (S : OutsideSplitWarp W X)
    (p : {p // p ∈ S.paths}) :
    (Sum.inl (S.finitePath p) : (CutSplit.web Gamma).DPath) = p.1 :=
  (S.finiteCharacter p.property).choose_spec.symm

private theorem project_adj {a b : Vertex V}
    (h : (CutSplit.web Gamma).graph.Adj a b) :
    Gamma.graph.Adj (project a) (project b) :=
  h

private theorem walk_start_depth_le
    {D : Digraph (Vertex V)} (d : Vertex V → Nat)
    {a b : Vertex V} (q : Walk D a b)
    (hstep : ∀ {x y}, (x, y) ∈ q.edgeSet → d y = d x + 1)
    {z : Vertex V} (hz : z ∈ q.support) : d a ≤ d z := by
  induction q with
  | nil =>
      simp only [Walk.support_nil, List.mem_singleton] at hz
      subst z
      exact le_rfl
  | @cons a b c hab q ih =>
      simp only [Walk.support_cons, List.mem_cons] at hz
      rcases hz with rfl | hz
      · exact le_rfl
      · have habStep : d b = d a + 1 := hstep (by simp [Walk.edgeSet])
        have htail : ∀ {x y}, (x, y) ∈ q.edgeSet →
            d y = d x + 1 := by
          intro x y hxy
          exact hstep (by simp [Walk.edgeSet, hxy])
        exact (by omega : d a < d b).le.trans (ih htail hz)

private theorem walk_depth_pairwise
    {D : Digraph (Vertex V)} (d : Vertex V → Nat)
    {a b : Vertex V} (q : Walk D a b)
    (hstep : ∀ {x y}, (x, y) ∈ q.edgeSet → d y = d x + 1) :
    (q.support.map d).Pairwise (· < ·) := by
  induction q with
  | nil => simp
  | @cons a b c hab q ih =>
      have habStep : d b = d a + 1 := hstep (by simp [Walk.edgeSet])
      have htail : ∀ {x y}, (x, y) ∈ q.edgeSet →
          d y = d x + 1 := by
        intro x y hxy
        exact hstep (by simp [Walk.edgeSet, hxy])
      rw [Walk.support_cons, List.map_cons, List.pairwise_cons]
      refine ⟨?_, ih htail⟩
      intro n hn
      obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hn
      have hbz : d b ≤ d z := walk_start_depth_le d q htail hz
      omega

/-- The split-family rank increases along every edge of one selected split
component. -/
theorem projectDepth_step_of_mem_edge (S : OutsideSplitWarp W X)
    (p : {p // p ∈ S.paths}) {a b : Vertex V}
    (hab : (a, b) ∈ (S.finitePath p).edgeSet) :
    S.projectDepth (project b) = S.projectDepth (project a) + 1 := by
  have hp : (Sum.inl (S.finitePath p) : (CutSplit.web Gamma).DPath) ∈
      S.paths := by
    rw [S.finitePath_eq p]
    exact p.property
  have habFamily : (a, b) ∈ familyEdges S.paths := by
    exact Set.mem_iUnion.2 ⟨Sum.inl (S.finitePath p),
      Set.mem_iUnion.2 ⟨hp, hab⟩⟩
  rw [S.familyEdges_eq] at habFamily
  exact S.projectDepth_step (CutSplit.mem_edge_iff.1 habFamily).1

/-- Project a finite split component.  Injectivity is local to this path and
follows from strict growth of `projectDepth`; no global injectivity of the
three-copy projection is asserted. -/
noncomputable def projectedFinitePath (S : OutsideSplitWarp W X)
    (p : {p // p ∈ S.paths}) : FinitePath Gamma.graph where
  start := project (S.finitePath p).start
  finish := project (S.finitePath p).finish
  walk := mapWalk project project_adj (S.finitePath p).walk
  isPath := by
    rw [Walk.isPath_iff, support_mapWalk]
    let d : Vertex V → Nat := fun z => S.projectDepth (project z)
    have hpair :
        ((S.finitePath p).walk.support.map d).Pairwise (· < ·) := by
      apply walk_depth_pairwise d (S.finitePath p).walk
      intro a b hab
      exact S.projectDepth_step_of_mem_edge p hab
    have hdNodup : ((S.finitePath p).walk.support.map d).Nodup :=
      hpair.nodup
    have hdInj : ∀ a ∈ (S.finitePath p).walk.support,
        ∀ b ∈ (S.finitePath p).walk.support, d a = d b → a = b :=
      (List.nodup_map_iff_inj_on (S.finitePath p).isPath).mp hdNodup
    apply List.Nodup.map_on _ (S.finitePath p).isPath
    intro a ha b hb hab
    exact hdInj a ha b hb (by simp only [d, hab])

/-- One projected split member, as a finite directed path. -/
noncomputable def projectedPath (S : OutsideSplitWarp W X)
    (p : {p // p ∈ S.paths}) : Gamma.DPath :=
  Sum.inl (S.projectedFinitePath p)

/-- The literal family of projected split components. -/
def projectedPaths (S : OutsideSplitWarp W X) : Set Gamma.DPath :=
  Set.range S.projectedPath

@[simp] theorem initial_projectedPath (S : OutsideSplitWarp W X)
    (p : {p // p ∈ S.paths}) :
    (S.projectedPath p).initial = project p.1.initial := by
  rw [projectedPath, Path.initial]
  change project (S.finitePath p).start = project p.1.initial
  rw [← finitePath_eq S p]
  rfl

@[simp] theorem terminal_projectedPath (S : OutsideSplitWarp W X)
    (p : {p // p ∈ S.paths}) :
    Gamma.terminal? (S.projectedPath p) =
      Option.map project ((CutSplit.web Gamma).terminal? p.1) := by
  rw [projectedPath]
  change some (project (S.finitePath p).finish) = _
  rw [← finitePath_eq S p]
  rfl

theorem mem_support_projectedPath (S : OutsideSplitWarp W X)
    (p : {p // p ∈ S.paths}) {x : V} :
    x ∈ (S.projectedPath p).support ↔
      ∃ z ∈ p.1.support, project z = x := by
  rw [projectedPath]
  change x ∈ (mapWalk project project_adj
      (S.finitePath p).walk).support ↔ _
  rw [support_mapWalk]
  constructor
  · intro hx
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hx
    exact ⟨z, by
      rw [← finitePath_eq S p]
      exact hz, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    apply List.mem_map.mpr
    refine ⟨z, ?_, rfl⟩
    change z ∈ DirectedPath.Path.support
      (Sum.inl (S.finitePath p) : (CutSplit.web Gamma).DPath)
    rw [finitePath_eq S p]
    exact hz

private theorem edgeSet_mapWalk
    {A B : Type u} {D : Digraph A} {E : Digraph B}
    (f : A → B) (hf : ∀ {x y}, D.Adj x y → E.Adj (f x) (f y))
    {a b : A} (q : Walk D a b) :
    (mapWalk f hf q).edgeSet =
      (fun e : A × A => (f e.1, f e.2)) '' q.edgeSet := by
  induction q with
  | nil => simp [mapWalk]
  | @cons a b c h q ih =>
      simp [mapWalk, ih, Set.image_insert_eq]

theorem edgeSet_projectedPath (S : OutsideSplitWarp W X)
    (p : {p // p ∈ S.paths}) :
    (S.projectedPath p).edgeSet =
      (fun e : Vertex V × Vertex V => (project e.1, project e.2)) ''
        p.1.edgeSet := by
  rw [projectedPath]
  change (mapWalk project project_adj
      (S.finitePath p).walk).edgeSet = _
  rw [edgeSet_mapWalk]
  congr 1
  ext e
  change e ∈ (S.finitePath p).walk.edgeSet ↔ e ∈ p.1.edgeSet
  rw [← finitePath_eq S p]
  rfl

theorem familyEdges_projectedPaths (S : OutsideSplitWarp W X) :
    familyEdges S.projectedPaths =
      (fun e : Vertex V × Vertex V => (project e.1, project e.2)) ''
        familyEdges S.paths := by
  ext e
  constructor
  · intro he
    simp only [familyEdges, Set.mem_iUnion] at he
    obtain ⟨q, hqProjected, heq⟩ := he
    rcases hqProjected with ⟨p, rfl⟩
    rw [S.edgeSet_projectedPath p] at heq
    obtain ⟨f, hf, rfl⟩ := heq
    refine ⟨f, ?_, rfl⟩
    exact Set.mem_iUnion.2 ⟨p.1,
      Set.mem_iUnion.2 ⟨p.property, hf⟩⟩
  · rintro ⟨f, hf, rfl⟩
    simp only [familyEdges, Set.mem_iUnion] at hf ⊢
    obtain ⟨q, hqS, hfq⟩ := hf
    let p : {p // p ∈ S.paths} := ⟨q, hqS⟩
    refine ⟨S.projectedPath p, ⟨p, rfl⟩, ?_⟩
    rw [S.edgeSet_projectedPath p]
    exact ⟨f, hfq, rfl⟩

theorem familyEdges_projectedPaths_eq (S : OutsideSplitWarp W X) :
    familyEdges S.projectedPaths = outsideFamilyEdges W X := by
  rw [S.familyEdges_projectedPaths, S.familyEdges_eq,
    CutSplit.project_edge_image]

theorem vertexSet_projectedPaths (S : OutsideSplitWarp W X) :
    Gamma.vertexSet S.projectedPaths =
      project '' (CutSplit.web Gamma).vertexSet S.paths := by
  ext x
  constructor
  · rintro ⟨q, ⟨p, rfl⟩, hx⟩
    rw [S.mem_support_projectedPath p] at hx
    obtain ⟨z, hz, rfl⟩ := hx
    exact ⟨z, ⟨p.1, p.property, hz⟩, rfl⟩
  · rintro ⟨z, ⟨q, hqS, hzq⟩, rfl⟩
    let p : {p // p ∈ S.paths} := ⟨q, hqS⟩
    refine ⟨S.projectedPath p, ⟨p, rfl⟩, ?_⟩
    rw [S.mem_support_projectedPath p]
    exact ⟨z, hzq, rfl⟩

private theorem project_outsideCarrier :
    project '' CutSplit.carrier (outsideCarrier W X)
      (outsideFamilyEdges W X) X = outsideCarrier W X := by
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [CutSplit.mem_carrier_iff] at hz
    rcases hz with hz | hz | hz
    · exact hz.2.1
    · obtain ⟨y, hxy⟩ := hz.2.2
      exact (outsideFamilyEdges_endpoints W X hxy).1
    · obtain ⟨y, hyx⟩ := hz.2.2
      exact (outsideFamilyEdges_endpoints W X hyx).2
  · intro hx
    by_cases hxX : x ∈ X
    · by_cases hout : ∃ y, (x, y) ∈ outsideFamilyEdges W X
      · exact ⟨outgoing x, by
          rw [CutSplit.mem_carrier_iff]
          exact Or.inr (Or.inl ⟨rfl, hxX, hout⟩), rfl⟩
      · by_cases hin : ∃ y, (y, x) ∈ outsideFamilyEdges W X
        · exact ⟨incoming x, by
            rw [CutSplit.mem_carrier_iff]
            exact Or.inr (Or.inr ⟨rfl, hxX, hin⟩), rfl⟩
        · exfalso
          -- A cut vertex of the outside carrier is retained only as an
          -- endpoint of an outside edge.
          change x ∈ (Gamma.vertexSet W \ X) ∪
            {x | ∃ y, (x, y) ∈ outsideFamilyEdges W X ∨
              (y, x) ∈ outsideFamilyEdges W X} at hx
          rcases hx with hxOutside | hxEndpoint
          · exact hxOutside.2 hxX
          · rcases hxEndpoint with ⟨y, hxy | hyx⟩
            · exact hout ⟨y, hxy⟩
            · exact hin ⟨y, hyx⟩
    · exact ⟨plain x, by
        rw [CutSplit.mem_carrier_iff]
        exact Or.inl ⟨rfl, hx, hxX⟩, rfl⟩

theorem vertexSet_projectedPaths_eq (S : OutsideSplitWarp W X) :
    Gamma.vertexSet S.projectedPaths = outsideCarrier W X := by
  rw [S.vertexSet_projectedPaths, S.vertexSet_eq]
  exact project_outsideCarrier

theorem initialSet_projectedPaths (S : OutsideSplitWarp W X) :
    Gamma.initialSet S.projectedPaths =
      project '' (CutSplit.web Gamma).initialSet S.paths := by
  ext x
  constructor
  · rintro ⟨q, ⟨p, rfl⟩, hqx⟩
    refine ⟨p.1.initial, ⟨p.1, p.property, rfl⟩, ?_⟩
    simpa only [S.initial_projectedPath p] using hqx
  · rintro ⟨z, ⟨q, hqS, hqz⟩, rfl⟩
    let p : {p // p ∈ S.paths} := ⟨q, hqS⟩
    refine ⟨S.projectedPath p, ⟨p, rfl⟩, ?_⟩
    rw [S.initial_projectedPath p, hqz]

theorem initialSet_projectedPaths_eq (S : OutsideSplitWarp W X) :
    Gamma.initialSet S.projectedPaths =
      CutSplit.initialVertices (outsideCarrier W X)
        (outsideFamilyEdges W X) X := by
  rw [S.initialSet_projectedPaths, S.project_initialSet]

theorem terminalFrontier_projectedPaths (S : OutsideSplitWarp W X) :
    Gamma.terminalFrontier S.projectedPaths =
      project '' (CutSplit.web Gamma).terminalFrontier S.paths := by
  ext x
  constructor
  · rintro ⟨q, ⟨p, rfl⟩, hqx⟩
    have hpterm : (CutSplit.web Gamma).terminal? p.1 =
        some (S.finitePath p).finish := by
      rw [← S.finitePath_eq p]
      rfl
    refine ⟨(S.finitePath p).finish, ⟨p.1, p.property, hpterm⟩, ?_⟩
    change project (S.finitePath p).finish = x
    change some (project (S.finitePath p).finish) = some x at hqx
    exact Option.some.inj hqx
  · rintro ⟨z, ⟨q, hqS, hqz⟩, rfl⟩
    let p : {p // p ∈ S.paths} := ⟨q, hqS⟩
    refine ⟨S.projectedPath p, ⟨p, rfl⟩, ?_⟩
    rw [S.terminal_projectedPath p, hqz]
    rfl

theorem terminalFrontier_projectedPaths_eq (S : OutsideSplitWarp W X) :
    Gamma.terminalFrontier S.projectedPaths =
      CutSplit.terminalVertices (outsideCarrier W X)
        (outsideFamilyEdges W X) X := by
  rw [S.terminalFrontier_projectedPaths, S.project_terminalFrontier]

private theorem walk_finish_depth_eq
    {D : Digraph (Vertex V)} (d : Vertex V → Nat)
    {a b : Vertex V} (q : Walk D a b)
    (hstep : ∀ {x y}, (x, y) ∈ q.edgeSet → d y = d x + 1) :
    d b = d a + q.length := by
  induction q with
  | nil => simp
  | @cons a b c hab q ih =>
      have habStep : d b = d a + 1 := hstep (by simp [Walk.edgeSet])
      have htail : ∀ {x y}, (x, y) ∈ q.edgeSet →
          d y = d x + 1 := by
        intro x y hxy
        exact hstep (by simp [Walk.edgeSet, hxy])
      have hrest := ih htail
      simp only [Walk.length_cons]
      omega

private theorem walk_endpoints_eq_of_length_eq_zero
    {D : Digraph (Vertex V)} {a b : Vertex V} (q : Walk D a b)
    (h : q.length = 0) : a = b := by
  cases q with
  | nil => rfl
  | cons _ _ => simp at h

/-- Along a nontrivial split component, the retained original-vertex rank
strictly increases from the projected initial to the projected terminal. -/
theorem projectDepth_lt_of_initial_terminal (S : OutsideSplitWarp W X)
    (p : {p // p ∈ S.paths}) {a b : Vertex V}
    (ha : p.1.initial = a)
    (hb : (CutSplit.web Gamma).terminal? p.1 = some b)
    (hab : project a ≠ project b) :
    S.projectDepth (project a) < S.projectDepth (project b) := by
  have hstart : (S.finitePath p).start = a := by
    have h := congrArg Path.initial (S.finitePath_eq p)
    exact h.trans ha
  have hfinish : (S.finitePath p).finish = b := by
    have h := congrArg ((CutSplit.web Gamma).terminal?)
      (S.finitePath_eq p)
    change some (S.finitePath p).finish =
      (CutSplit.web Gamma).terminal? p.1 at h
    rw [hb] at h
    exact Option.some.inj h
  have hdepth := walk_finish_depth_eq
    (fun z : Vertex V => S.projectDepth (project z))
    (S.finitePath p).walk (by
      intro x y hxy
      exact S.projectDepth_step_of_mem_edge p hxy)
  have hdepth' :
      S.projectDepth (project b) = S.projectDepth (project a) +
        (S.finitePath p).walk.length := by
    simpa only [hstart, hfinish] using hdepth
  have hlength : 0 < (S.finitePath p).walk.length := by
    by_contra hzero
    have hnil : (S.finitePath p).walk.length = 0 :=
      Nat.eq_zero_of_not_pos hzero
    have heq : (S.finitePath p).start = (S.finitePath p).finish :=
      walk_endpoints_eq_of_length_eq_zero (S.finitePath p).walk hnil
    exact hab (by simpa [hstart, hfinish] using congrArg project heq)
  omega

/-- Two distinct split occurrences above one original vertex on two split
components must be the incoming/outgoing endpoint pair at a cut vertex. -/
theorem endpoint_cases_of_project_eq (S : OutsideSplitWarp W X)
    (p q : {p // p ∈ S.paths})
    {z w : Vertex V} (hz : z ∈ p.1.support) (hw : w ∈ q.1.support)
    (hproject : project z = project w) (hzw : z ≠ w) :
    project z ∈ X ∧
      ((z = p.1.initial ∧
          (CutSplit.web Gamma).terminal? q.1 = some w) ∨
        ((CutSplit.web Gamma).terminal? p.1 = some z ∧
          w = q.1.initial)) := by
  have hzCarrier := S.support_subset_carrier p.property hz
  have hwCarrier := S.support_subset_carrier q.property hw
  have hzX : project z ∈ X := by
    by_contra hzX
    exact hzw (CutSplit.eq_of_mem_carrier_of_project_eq_of_not_mem
      hzCarrier hwCarrier hproject hzX)
  rw [CutSplit.mem_carrier_iff] at hzCarrier hwCarrier
  rcases hzCarrier with hzPlain | hzOut | hzIn
  · exact False.elim (hzPlain.2.2 hzX)
  · rcases hwCarrier with hwPlain | hwOut | hwIn
    · exact False.elim (hwPlain.2.2 (hproject ▸ hzX))
    · exact False.elim <| hzw <| by
        rw [hzOut.1, hwOut.1, hproject]
    · refine ⟨hzX, Or.inl ⟨?_, ?_⟩⟩
      · exact S.eq_initial_of_eq_outgoing_of_mem_support p.property hz hzX
          hzOut.1
      · exact S.terminal_eq_some_of_eq_incoming_of_mem_support q.property
          hw (hproject ▸ hzX) hwIn.1
  · rcases hwCarrier with hwPlain | hwOut | hwIn
    · exact False.elim (hwPlain.2.2 (hproject ▸ hzX))
    · refine ⟨hzX, Or.inr ⟨?_, ?_⟩⟩
      · exact S.terminal_eq_some_of_eq_incoming_of_mem_support p.property
          hz hzX hzIn.1
      · exact S.eq_initial_of_eq_outgoing_of_mem_support q.property hw
          (hproject ▸ hzX) hwOut.1
    · exact False.elim <| hzw <| by
        rw [hzIn.1, hwIn.1, hproject]

/-- A projected component which contains a cut occurrence is nontrivial.
The corresponding occurrence has an incident retained edge, and warp
disjointness forces that edge to belong to the same split component. -/
theorem projectedPath_nontrivial_of_cut_occurrence
    (S : OutsideSplitWarp W X) (p : {p // p ∈ S.paths})
    {z : Vertex V} (hz : z ∈ p.1.support) (hzX : project z ∈ X) :
    PathNontrivial (S.projectedPath p) := by
  have hzCarrier := S.support_subset_carrier p.property hz
  rw [CutSplit.mem_carrier_iff] at hzCarrier
  rcases hzCarrier with hzPlain | hzOut | hzIn
  · exact False.elim (hzPlain.2.2 hzX)
  · obtain ⟨y, hxy⟩ := hzOut.2.2
    let b : Vertex V := CutSplit.headCopy X y
    have hzb : (z, b) ∈
        CutSplit.edge (outsideFamilyEdges W X) X := by
      rw [CutSplit.mem_edge_iff]
      refine ⟨?_, ?_, ?_⟩
      · simpa [b] using hxy
      · rw [hzOut.1]
        simp [CutSplit.tailCopy, hzX]
      · simp [b]
    have hzbFamily : (z, b) ∈ familyEdges S.paths := by
      rw [S.familyEdges_eq]
      exact hzb
    simp only [familyEdges, Set.mem_iUnion] at hzbFamily
    obtain ⟨r, hrS, hzbr⟩ := hzbFamily
    have hzR : z ∈ r.support := (r.edgeSet_subset_support_prod hzbr).1
    have hpr : p.1 = r :=
      DWeb.IsWarp.eq_of_mem_support S.isWarp p.property hrS hz hzR
    have hzbp : (z, b) ∈ p.1.edgeSet := by simpa [hpr] using hzbr
    have hprojected : (project z, project b) ∈
        (S.projectedPath p).edgeSet := by
      rw [S.edgeSet_projectedPath p]
      exact ⟨(z, b), hzbp, rfl⟩
    have hneq : project z ≠ project b := by
      intro heq
      have hstep := S.projectDepth_step
        (CutSplit.mem_edge_iff.1 hzb).1
      rw [heq] at hstep
      omega
    exact ⟨project z,
      ((S.projectedPath p).edgeSet_subset_support_prod hprojected).1,
      project b,
      ((S.projectedPath p).edgeSet_subset_support_prod hprojected).2,
      hneq⟩
  · obtain ⟨y, hyz⟩ := hzIn.2.2
    let a : Vertex V := CutSplit.tailCopy X y
    have haz : (a, z) ∈
        CutSplit.edge (outsideFamilyEdges W X) X := by
      rw [CutSplit.mem_edge_iff]
      refine ⟨?_, ?_, ?_⟩
      · simpa [a] using hyz
      · simp [a]
      · rw [hzIn.1]
        simp [CutSplit.headCopy, hzX]
    have hazFamily : (a, z) ∈ familyEdges S.paths := by
      rw [S.familyEdges_eq]
      exact haz
    simp only [familyEdges, Set.mem_iUnion] at hazFamily
    obtain ⟨r, hrS, hazr⟩ := hazFamily
    have hzR : z ∈ r.support := (r.edgeSet_subset_support_prod hazr).2
    have hpr : p.1 = r :=
      DWeb.IsWarp.eq_of_mem_support S.isWarp p.property hrS hz hzR
    have hazp : (a, z) ∈ p.1.edgeSet := by simpa [hpr] using hazr
    have hprojected : (project a, project z) ∈
        (S.projectedPath p).edgeSet := by
      rw [S.edgeSet_projectedPath p]
      exact ⟨(a, z), hazp, rfl⟩
    have hneq : project a ≠ project z := by
      intro heq
      have hstep := S.projectDepth_step
        (CutSplit.mem_edge_iff.1 haz).1
      rw [heq] at hstep
      omega
    exact ⟨project a,
      ((S.projectedPath p).edgeSet_subset_support_prod hprojected).1,
      project z,
      ((S.projectedPath p).edgeSet_subset_support_prod hprojected).2,
      hneq⟩

/-- Distinct projected split components have at most one common original
vertex. -/
theorem support_inter_projectedPath_eq_singleton
    (S : OutsideSplitWarp W X)
    (p q : {p // p ∈ S.paths})
    (hpq : S.projectedPath p ≠ S.projectedPath q)
    {x : V} (hxp : x ∈ (S.projectedPath p).support)
    (hxq : x ∈ (S.projectedPath q).support) :
    (S.projectedPath p).support ∩ (S.projectedPath q).support = {x} := by
  rw [S.mem_support_projectedPath p] at hxp
  rw [S.mem_support_projectedPath q] at hxq
  obtain ⟨zp, hzp, hzpProject⟩ := hxp
  obtain ⟨zq, hzq, hzqProject⟩ := hxq
  have hprojectX : project zp = project zq :=
    hzpProject.trans hzqProject.symm
  have hzpzq : zp ≠ zq := by
    intro heq
    subst zq
    have hpqSplit : p.1 = q.1 :=
      DWeb.IsWarp.eq_of_mem_support S.isWarp p.property q.property
        hzp hzq
    have hpqSubtype : p = q := Subtype.ext hpqSplit
    exact hpq (congrArg S.projectedPath hpqSubtype)
  have hxCases := S.endpoint_cases_of_project_eq p q hzp hzq
    hprojectX hzpzq
  apply Set.Subset.antisymm
  · rintro y ⟨hyp, hyq⟩
    rw [S.mem_support_projectedPath p] at hyp
    rw [S.mem_support_projectedPath q] at hyq
    obtain ⟨yp, hyp, hypProject⟩ := hyp
    obtain ⟨yq, hyq, hyqProject⟩ := hyq
    have hprojectY : project yp = project yq :=
      hypProject.trans hyqProject.symm
    have hypyq : yp ≠ yq := by
      intro heq
      subst yq
      have hpqSplit : p.1 = q.1 :=
        DWeb.IsWarp.eq_of_mem_support S.isWarp p.property q.property
          hyp hyq
      have hpqSubtype : p = q := Subtype.ext hpqSplit
      exact hpq (congrArg S.projectedPath hpqSubtype)
    have hyCases := S.endpoint_cases_of_project_eq p q hyp hyq
      hprojectY hypyq
    have hyx : y = x := by
      rcases hxCases.2 with hxForward | hxBackward
      · rcases hyCases.2 with hyForward | hyBackward
        · calc
            y = project yp := hypProject.symm
            _ = project p.1.initial := congrArg project hyForward.1
            _ = project zp := congrArg project hxForward.1.symm
            _ = x := hzpProject
        · by_contra hyx
          have hxyProject : project zp ≠ project yp := by
            simpa [hzpProject, hypProject] using Ne.symm hyx
          have hpLt := S.projectDepth_lt_of_initial_terminal p
            hxForward.1.symm hyBackward.1 hxyProject
          have hqLt := S.projectDepth_lt_of_initial_terminal q
            hyBackward.2.symm hxForward.2 (by
              simpa [hzqProject, hyqProject] using hyx)
          rw [hprojectX, hprojectY] at hpLt
          omega
      · rcases hyCases.2 with hyForward | hyBackward
        · by_contra hyx
          have hxyProject : project zq ≠ project yq := by
            simpa [hzqProject, hyqProject] using Ne.symm hyx
          have hqLt := S.projectDepth_lt_of_initial_terminal q
            hxBackward.2.symm hyForward.2 hxyProject
          have hpLt := S.projectDepth_lt_of_initial_terminal p
            hyForward.1.symm hxBackward.1 (by
              simpa [hzpProject, hypProject] using hyx)
          rw [hprojectX, hprojectY] at hpLt
          omega
        · calc
            y = project yq := hyqProject.symm
            _ = project q.1.initial := congrArg project hyBackward.2
            _ = project zq := congrArg project hxBackward.2.symm
            _ = x := hzqProject
    simpa [hyx]
  · intro y hy
    have hyx : y = x := Set.mem_singleton_iff.1 hy
    subst y
    exact ⟨by
      rw [S.mem_support_projectedPath p]
      exact ⟨zp, hzp, hzpProject⟩, by
      rw [S.mem_support_projectedPath q]
      exact ⟨zq, hzq, hzqProject⟩⟩

theorem projectedPaths_hasFiniteCharacter (S : OutsideSplitWarp W X) :
    Gamma.HasFiniteCharacter S.projectedPaths := by
  rintro q ⟨p, rfl⟩
  exact ⟨S.projectedFinitePath p, rfl⟩

/-- Every visit of one literal projected component to the cut is an endpoint
visit.  This is the path-level fact lost by the honest recombination: two
consecutive components may share a cut vertex, but no individual component
passes internally through it. -/
theorem projectedPath_cut_vertex_is_endpoint
    (S : OutsideSplitWarp W X) (p : {p // p ∈ S.paths})
    {x : V} (hx : x ∈ (S.projectedPath p).support) (hxX : x ∈ X) :
    (S.projectedPath p).initial = x ∨
      Gamma.terminal? (S.projectedPath p) = some x := by
  rw [S.mem_support_projectedPath p] at hx
  obtain ⟨z, hz, hzx⟩ := hx
  have hzCarrier := S.support_subset_carrier p.property hz
  rw [CutSplit.mem_carrier_iff] at hzCarrier
  rcases hzCarrier with hzPlain | hzOut | hzIn
  · exact False.elim (hzPlain.2.2 (hzx ▸ hxX))
  · left
    rw [S.initial_projectedPath p]
    have hzinitial := S.eq_initial_of_eq_outgoing_of_mem_support
      p.property hz (hzx ▸ hxX) hzOut.1
    exact (congrArg project hzinitial.symm).trans hzx
  · right
    have hzterm := S.terminal_eq_some_of_eq_incoming_of_mem_support
      p.property hz (hzx ▸ hxX) hzIn.1
    rw [S.terminal_projectedPath p, hzterm]
    simpa only [Option.map_some] using congrArg some hzx

/-- The projected split components, recombined by the honest outside warp,
form the literal fractured warp of the cut. -/
noncomputable def fractured (S : OutsideSplitWarp W X)
    (C : OutsideEdgeWarp W X) : FracturedWarp Gamma where
  paths := S.projectedPaths
  edgeWarp := C.paths
  edgeWarp_isWarp := C.isWarp
  same_edges := S.familyEdges_projectedPaths_eq.trans C.familyEdges_eq.symm
  allowed_intersection := by
    intro p hp q hq hpq hmeet
    rcases hp with ⟨P, rfl⟩
    rcases hq with ⟨Q, rfl⟩
    rw [Set.not_disjoint_iff] at hmeet
    obtain ⟨x, hxP, hxQ⟩ := hmeet
    rw [S.mem_support_projectedPath P] at hxP
    rw [S.mem_support_projectedPath Q] at hxQ
    obtain ⟨zP, hzP, hzPproject⟩ := hxP
    obtain ⟨zQ, hzQ, hzQproject⟩ := hxQ
    have hproject : project zP = project zQ :=
      hzPproject.trans hzQproject.symm
    have hzNe : zP ≠ zQ := by
      intro heq
      subst zQ
      have hPQ : P.1 = Q.1 :=
        DWeb.IsWarp.eq_of_mem_support S.isWarp P.property Q.property
          hzP hzQ
      have hPQ' : P = Q := Subtype.ext hPQ
      exact hpq (congrArg S.projectedPath hPQ')
    have hcases := S.endpoint_cases_of_project_eq P Q hzP hzQ
      hproject hzNe
    have hPnontrivial :=
      S.projectedPath_nontrivial_of_cut_occurrence P hzP hcases.1
    have hQnontrivial :=
      S.projectedPath_nontrivial_of_cut_occurrence Q hzQ
        (hproject ▸ hcases.1)
    have hinter := S.support_inter_projectedPath_eq_singleton P Q hpq
      (by rw [S.mem_support_projectedPath P]; exact ⟨zP, hzP, hzPproject⟩)
      (by rw [S.mem_support_projectedPath Q]; exact ⟨zQ, hzQ, hzQproject⟩)
    refine ⟨hPnontrivial, hQnontrivial, ?_⟩
    rcases hcases.2 with hforward | hbackward
    · left
      refine ⟨x, ?_, ?_, hinter⟩
      · rw [S.terminal_projectedPath Q, hforward.2]
        simpa only [Option.map_some] using congrArg some hzQproject
      · rw [S.initial_projectedPath P, ← hforward.1]
        exact hzPproject
    · right
      refine ⟨x, ?_, ?_, hinter⟩
      · rw [S.terminal_projectedPath P, hbackward.1]
        simpa only [Option.map_some] using congrArg some hzPproject
      · rw [S.initial_projectedPath Q, ← hbackward.2]
        exact hzQproject

@[simp] theorem fractured_paths (S : OutsideSplitWarp W X)
    (C : OutsideEdgeWarp W X) : (S.fractured C).paths = S.projectedPaths :=
  rfl

@[simp] theorem fractured_edgeWarp (S : OutsideSplitWarp W X)
    (C : OutsideEdgeWarp W X) : (S.fractured C).edgeWarp = C.paths :=
  rfl

/-- Package the projected split family with its exact cut geometry. -/
noncomputable def toOutsideFracturedWarp (S : OutsideSplitWarp W X)
    (C : OutsideEdgeWarp W X) : OutsideFracturedWarp W X where
  holes := S.fractured C
  finiteCharacter := by
    change Gamma.HasFiniteCharacter S.projectedPaths
    exact S.projectedPaths_hasFiniteCharacter
  edgeWarpFiniteCharacter := by
    change Gamma.HasFiniteCharacter C.paths
    exact C.finiteCharacter
  familyEdges_eq := by
    change familyEdges S.projectedPaths = outsideFamilyEdges W X
    exact S.familyEdges_projectedPaths_eq
  vertexSet_eq := by
    change Gamma.vertexSet S.projectedPaths = outsideCarrier W X
    exact S.vertexSet_projectedPaths_eq
  initialSet_eq := by
    change Gamma.initialSet S.projectedPaths =
      CutSplit.initialVertices (outsideCarrier W X)
        (outsideFamilyEdges W X) X
    exact S.initialSet_projectedPaths_eq
  terminalFrontier_eq := by
    change Gamma.terminalFrontier S.projectedPaths =
      CutSplit.terminalVertices (outsideCarrier W X)
        (outsideFamilyEdges W X) X
    exact S.terminalFrontier_projectedPaths_eq

/-- The concrete split projection together with the endpoint-at-cut fact
needed by later assignment/closure arguments.  Keeping this certificate
separate from `OutsideFracturedWarp` avoids pretending it follows from the
bare edge-recombination interface. -/
structure SplitProjectedOutsideFracturedWarp
    (W : Set Gamma.DPath) (X : Set V) where
  outside : OutsideFracturedWarp W X
  /-- The honest recombination is the canonical outside-edge decomposition,
  so it retains no extra isolated vertices beyond the exact outside carrier.
  This fact is deliberately stored on the concrete split projection rather
  than on the abstract `FracturedWarp` interface. -/
  edgeWarp_vertexSet_eq :
    Gamma.vertexSet outside.holes.edgeWarp = outsideCarrier W X
  cut_vertex_is_endpoint : ∀ p ∈ outside.holes.paths,
    ∀ {x : V}, x ∈ p.support → x ∈ X →
      p.initial = x ∨ Gamma.terminal? p = some x

/-- Package a literal split family without forgetting its cut-intersection
certificate. -/
noncomputable def toSplitProjectedOutsideFracturedWarp
    (S : OutsideSplitWarp W X) (C : OutsideEdgeWarp W X) :
    SplitProjectedOutsideFracturedWarp W X where
  outside := S.toOutsideFracturedWarp C
  edgeWarp_vertexSet_eq := by
    change Gamma.vertexSet C.paths = outsideCarrier W X
    exact C.vertexSet_eq
  cut_vertex_is_endpoint := by
    intro q hq x hx hxX
    change q ∈ S.projectedPaths at hq
    obtain ⟨p, rfl⟩ := hq
    exact S.projectedPath_cut_vertex_is_endpoint p hx hxX

end OutsideSplitWarp

/-- The literal fractured outside family exists unconditionally from an
honest finite-character warp and a cut set. -/
theorem exists_outsideFracturedWarp_of_splitProjection
    (W : Set Gamma.DPath) (X : Set V)
    (hW : Gamma.IsWarp W) (hfinite : Gamma.HasFiniteCharacter W) :
    Nonempty (OutsideFracturedWarp W X) := by
  obtain ⟨S, C, _hmatching⟩ :=
    exists_outsideSplitAndEdgeWarp W X hW hfinite
  exact ⟨S.toOutsideFracturedWarp C⟩

/-- Strengthened literal cut constructor retaining the fact that each
projected component meets the closing set only at its endpoints. -/
theorem exists_splitProjectedOutsideFracturedWarp
    (W : Set Gamma.DPath) (X : Set V)
    (hW : Gamma.IsWarp W) (hfinite : Gamma.HasFiniteCharacter W) :
    Nonempty (OutsideSplitWarp.SplitProjectedOutsideFracturedWarp W X) := by
  obtain ⟨S, C, _hmatching⟩ :=
    exists_outsideSplitAndEdgeWarp W X hW hfinite
  exact ⟨S.toSplitProjectedOutsideFracturedWarp C⟩

end LinkageBlueprint
end Blueprint
end Erdos599
