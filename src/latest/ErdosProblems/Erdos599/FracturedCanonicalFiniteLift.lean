/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.FracturedDuplication
import ErdosProblems.Erdos599.AlternatingSourceAssertions

/-!
# The canonical proper-edge lift of a finite fractured path

The reference expansion in `FracturedDuplication` uses blocks
`outgoing -> plain -> incoming` and proper edges
`incoming x -> outgoing y`.  For an original forward path we need the
dual convention.  We swap the incoming/outgoing roles in the full expansion
and take the literal interval from `outgoing(start)` to `incoming(finish)`.
Consequently every genuine original edge has its unique canonical lift
`outgoing x -> incoming y`, while internal vertices are traversed through
`incoming -> plain -> outgoing`.

Only nontrivial finite paths are treated here.  Singleton members are meant
to be peeled before this construction.
-/

noncomputable section

namespace Erdos599.Alternating.FracturedCanonicalFiniteLift

open Set DirectedPath
open FracturedDuplication

universe u

variable {V : Type u} {Gamma : DWeb V}

/-- Exchange the two boundary roles and fix the plain role. -/
def swapRole : Role → Role
  | .plain => .plain
  | .incoming => .outgoing
  | .outgoing => .incoming

/-- The induced involution on duplicated vertices. -/
def swapVertex (z : Vertex V) : Vertex V := (z.1, swapRole z.2)

@[simp] theorem swapRole_swapRole (r : Role) : swapRole (swapRole r) = r := by
  cases r <;> rfl

@[simp] theorem swapVertex_swapVertex (z : Vertex V) :
    swapVertex (swapVertex z) = z := by
  rcases z with ⟨x, r⟩
  simp [swapVertex]

theorem swapVertex_injective : Function.Injective (swapVertex : Vertex V → Vertex V) :=
  fun _ _ h ↦ by simpa using congrArg swapVertex h

@[simp] theorem project_swapVertex (z : Vertex V) :
    project (swapVertex z) = project z := rfl

@[simp] theorem swapVertex_plain (x : V) : swapVertex (plain x) = plain x := rfl
@[simp] theorem swapVertex_incoming (x : V) :
    swapVertex (incoming x) = outgoing x := rfl
@[simp] theorem swapVertex_outgoing (x : V) :
    swapVertex (outgoing x) = incoming x := rfl

/-- Role swap is an automorphism of the duplicated graph. -/
theorem graph_adj_swapVertex (Z : FracturedWarp Gamma)
    {a b : Vertex V} (h : (web Gamma Z).graph.Adj a b) :
    (web Gamma Z).graph.Adj (swapVertex a) (swapVertex b) := by
  rcases h with h | ⟨hproj, hrole⟩
  · exact Or.inl (by simpa using h)
  · right
    refine ⟨by simpa using hproj, ?_⟩
    intro hswap
    apply hrole
    have := congrArg swapRole hswap
    simpa [swapVertex] using this

/-- The block order for an original forward member. -/
def canonicalBlock (x : V) : List (Vertex V) :=
  [incoming x, plain x, outgoing x]

theorem canonicalBlock_nodup (x : V) : (canonicalBlock x).Nodup := by
  simp [canonicalBlock, incoming, plain, outgoing]

theorem mem_canonicalBlock_project {x : V} {z : Vertex V}
    (hz : z ∈ canonicalBlock x) : project z = x := by
  simp only [canonicalBlock, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl <;> rfl

/-- Swap every role in the full reference-style expansion. -/
def swappedExpansion (Z : FracturedWarp Gamma)
    (p : FinitePath Gamma.graph) : FinitePath (web Gamma Z).graph :=
  mapFinitePath swapVertex swapVertex_injective
    (graph_adj_swapVertex Z) (expandFinitePath Z p)

@[simp] theorem swappedExpansion_start (Z : FracturedWarp Gamma)
    (p : FinitePath Gamma.graph) :
    (swappedExpansion Z p).start = incoming p.start := by
  rfl

@[simp] theorem swappedExpansion_finish (Z : FracturedWarp Gamma)
    (p : FinitePath Gamma.graph) :
    (swappedExpansion Z p).finish = outgoing p.finish := by
  rfl

/-- Its ordered support is the concatenation of the canonical blocks. -/
theorem swappedExpansion_support (Z : FracturedWarp Gamma)
    (p : FinitePath Gamma.graph) :
    (swappedExpansion Z p).walk.support =
      p.walk.support.flatMap canonicalBlock := by
  change (mapWalk swapVertex (graph_adj_swapVertex Z)
    (expandWalk Z p.walk)).support = _
  rw [support_mapWalk, support_expandWalk]
  induction p.walk.support with
  | nil => rfl
  | cons x xs ih =>
      simp [vertexBlock, canonicalBlock, ih]

theorem swappedExpansion_support_set (Z : FracturedWarp Gamma)
    (p : FinitePath Gamma.graph) {z : Vertex V} :
    z ∈ (swappedExpansion Z p).support ↔
      ∃ x ∈ p.support, z ∈ canonicalBlock x := by
  change z ∈ (swappedExpansion Z p).walk.support ↔ _
  rw [swappedExpansion_support]
  simp [FinitePath.support]

/-- In the swapped expansion, `outgoing(start)` occurs before
`incoming(finish)`.  The record also retains the exact discarded endpoint
blocks, which is used to prove exact projected support after cutting. -/
structure CanonicalOccurrenceData (Z : FracturedWarp Gamma)
    (p : FinitePath Gamma.graph) where
  occurrence : FinitePath.OrderedOccurrence (swappedExpansion Z p)
    (outgoing p.start) (incoming p.finish)
  before_eq : occurrence.before = [incoming p.start, plain p.start]
  after_eq : occurrence.after = [plain p.finish, outgoing p.finish]

/-- Construct the endpoint occurrence data from the literal full expansion. -/
theorem exists_canonicalOccurrenceData (Z : FracturedWarp Gamma)
    (p : FinitePath Gamma.graph) (hne : p.start ≠ p.finish) :
    Nonempty (CanonicalOccurrenceData Z p) := by
  obtain ⟨y, hxy, q, hpwalk⟩ :=
    RelationalRoof.exists_cons_of_start_ne_finish Gamma.graph.Adj p.walk hne
  have hsupport : p.walk.support = p.start :: q.support := by
    rw [hpwalk]
    rfl
  have hlast : q.support.getLast q.support_ne_nil = p.finish := by
    exact q.getLast_support
  have htail : q.support = q.support.dropLast ++ [p.finish] := by
    calc
      q.support = q.support.dropLast ++
          [q.support.getLast q.support_ne_nil] :=
        (List.dropLast_append_getLast q.support_ne_nil).symm
      _ = q.support.dropLast ++ [p.finish] := by
        exact congrArg (fun z ↦ q.support.dropLast ++ [z]) hlast
  let middle := q.support.dropLast.flatMap canonicalBlock
  let H : FinitePath.OrderedOccurrence (swappedExpansion Z p)
      (outgoing p.start) (incoming p.finish) := {
    before := [incoming p.start, plain p.start]
    middle := middle
    after := [plain p.finish, outgoing p.finish]
    support_eq := by
      rw [swappedExpansion_support, hsupport, List.flatMap_cons, htail,
        List.flatMap_append]
      simp [canonicalBlock, middle, List.append_assoc] }
  exact ⟨⟨H, rfl, rfl⟩⟩

/-- A canonical choice of the endpoint occurrence. -/
def canonicalOccurrenceData (Z : FracturedWarp Gamma)
    (p : FinitePath Gamma.graph) (hne : p.start ≠ p.finish) :
    CanonicalOccurrenceData Z p :=
  Classical.choice (exists_canonicalOccurrenceData Z p hne)

/-- The canonical proper-edge lift, obtained as a literal subpath of the
swapped full expansion. -/
def lift (Z : FracturedWarp Gamma) (p : FinitePath Gamma.graph)
    (hne : p.start ≠ p.finish) : FinitePath (web Gamma Z).graph :=
  (swappedExpansion Z p).between (canonicalOccurrenceData Z p hne).occurrence

@[simp] theorem lift_start (Z : FracturedWarp Gamma)
    (p : FinitePath Gamma.graph) (hne : p.start ≠ p.finish) :
    (lift Z p hne).start = outgoing p.start := rfl

@[simp] theorem lift_finish (Z : FracturedWarp Gamma)
    (p : FinitePath Gamma.graph) (hne : p.start ≠ p.finish) :
    (lift Z p hne).finish = incoming p.finish := rfl

theorem lift_isSubpathOf_swappedExpansion (Z : FracturedWarp Gamma)
    (p : FinitePath Gamma.graph) (hne : p.start ≠ p.finish) :
    (lift Z p hne).IsSubpathOf (.inl (swappedExpansion Z p)) :=
  (swappedExpansion Z p).between_isSubpathOf
    (canonicalOccurrenceData Z p hne).occurrence

private theorem edgeSet_mapWalk
    {A B : Type u} {D : Digraph A} {E : Digraph B}
    (f : A → B) (hf : ∀ {x y}, D.Adj x y → E.Adj (f x) (f y))
    {a b : A} (q : Walk D a b) :
    (mapWalk f hf q).edgeSet =
      (fun e : A × A ↦ (f e.1, f e.2)) '' q.edgeSet := by
  induction q with
  | nil => simp [mapWalk]
  | @cons a b c h q ih =>
      simp [mapWalk, ih, Set.image_insert_eq]

private theorem vertexWalk_edge_projects_eq
    (Z : FracturedWarp Gamma) (x : V) {e : Vertex V × Vertex V}
    (he : e ∈ (vertexWalk Z x).edgeSet) :
    project e.1 = project e.2 := by
  have hs := (vertexWalk Z x).edgeSet_subset_support_prod he
  rw [support_vertexWalk] at hs
  exact (mem_vertexBlock_project Z hs.1).trans
    (mem_vertexBlock_project Z hs.2).symm

private theorem walk_edgeSet_append
    {A : Type u} {D : Digraph A} {a b c : A}
    (q : Walk D a b) (r : Walk D b c) :
    (q.append r).edgeSet = q.edgeSet ∪ r.edgeSet := by
  induction q with
  | nil => simp
  | @cons a b d hab q ih =>
      ext e
      simp only [Walk.append, Walk.edgeSet_cons, ih, Set.mem_insert_iff,
        Set.mem_union]
      tauto

/-- Every nonconnector edge of a full expansion has the old reference-style
roles and projects to a literal original edge. -/
private theorem expandWalk_nonconnector_roles
    (Z : FracturedWarp Gamma) {a b : V} (q : Walk Gamma.graph a b)
    {e : Vertex V × Vertex V} (he : e ∈ (expandWalk Z q).edgeSet)
    (hne : project e.1 ≠ project e.2) :
    e.1 = incoming (project e.1) ∧
      e.2 = outgoing (project e.2) ∧
      (project e.1, project e.2) ∈ q.edgeSet := by
  induction q with
  | nil => exact False.elim (hne (vertexWalk_edge_projects_eq Z _ he))
  | @cons a b c hab q ih =>
      rw [expandWalk, walk_edgeSet_append] at he
      rcases he with hblock | hrest
      · exact False.elim (hne (vertexWalk_edge_projects_eq Z _ hblock))
      · simp only [Walk.edgeSet_cons, Set.mem_union,
          Set.mem_singleton_iff] at hrest ⊢
        rcases hrest with hproper | htail
        · subst e
          exact ⟨rfl, rfl, Or.inl rfl⟩
        · obtain ⟨h₁, h₂, h₃⟩ := ih htail
          exact ⟨h₁, h₂, Or.inr h₃⟩

/-- Every nonconnector edge of the canonical lift has the unique forward
roles `outgoing -> incoming` and projects to an actual edge of the original
finite path. -/
theorem lift_edge_roles_of_project_ne (Z : FracturedWarp Gamma)
    (p : FinitePath Gamma.graph) (hne : p.start ≠ p.finish)
    {e : Vertex V × Vertex V} (he : e ∈ (lift Z p hne).edgeSet)
    (hproject : project e.1 ≠ project e.2) :
    e.1 = outgoing (project e.1) ∧
      e.2 = incoming (project e.2) ∧
      (project e.1, project e.2) ∈ p.edgeSet := by
  have heFull := (lift_isSubpathOf_swappedExpansion Z p hne).2 he
  change e ∈ (mapWalk swapVertex (graph_adj_swapVertex Z)
    (expandWalk Z p.walk)).edgeSet at heFull
  rw [edgeSet_mapWalk] at heFull
  rcases heFull with ⟨e₀, he₀, rfl⟩
  have hproj₀ : project e₀.1 ≠ project e₀.2 := by
    simpa using hproject
  obtain ⟨h₁, h₂, h₃⟩ :=
    expandWalk_nonconnector_roles Z p.walk he₀ hproj₀
  constructor
  · change swapVertex e₀.1 = outgoing (project (swapVertex e₀.1))
    rw [h₁]
    rfl
  constructor
  · change swapVertex e₀.2 = incoming (project (swapVertex e₀.2))
    rw [h₂]
    rfl
  · change (project e₀.1, project e₀.2) ∈ p.walk.edgeSet
    exact h₃

@[simp] theorem project_lift_start (Z : FracturedWarp Gamma)
    (p : FinitePath Gamma.graph) (hne : p.start ≠ p.finish) :
    project (lift Z p hne).start = p.start := by
  rw [lift_start]
  rfl

@[simp] theorem project_lift_finish (Z : FracturedWarp Gamma)
    (p : FinitePath Gamma.graph) (hne : p.start ≠ p.finish) :
    project (lift Z p hne).finish = p.finish := by
  rw [lift_finish]
  rfl

/-- Over the original initial vertex, the cut lift retains only the outgoing
copy.  The incoming and plain copies lie in the discarded initial block. -/
theorem eq_outgoing_start_of_mem_lift_support_of_project_eq
    (Z : FracturedWarp Gamma) (p : FinitePath Gamma.graph)
    (hne : p.start ≠ p.finish) {z : Vertex V}
    (hz : z ∈ (lift Z p hne).support) (hproject : project z = p.start) :
    z = outgoing p.start := by
  let D := canonicalOccurrenceData Z p hne
  have hzFull := (lift_isSubpathOf_swappedExpansion Z p hne).1 hz
  change z ∈ (swappedExpansion Z p).support at hzFull
  rcases (swappedExpansion_support_set Z p).1 hzFull with
    ⟨x, hx, hzx⟩
  have hxstart : x = p.start := by
    exact (mem_canonicalBlock_project hzx).symm.trans hproject
  subst x
  let core := outgoing p.start :: D.occurrence.middle ++ [incoming p.finish]
  let rest := core ++ D.occurrence.after
  have hzCore : z ∈ core := by
    change z ∈ (lift Z p hne).walk.support at hz
    simpa only [lift, D, core,
      (swappedExpansion Z p).between_support_eq D.occurrence] using hz
  have hzRest : z ∈ rest := List.mem_append_left _ hzCore
  have hn : (D.occurrence.before ++ rest).Nodup := by
    have hnFull := (swappedExpansion Z p).isPath
    rw [Walk.IsPath] at hnFull
    rw [D.occurrence.support_eq] at hnFull
    simpa only [rest, core, List.append_assoc, List.singleton_append] using hnFull
  have hdis := (List.nodup_append.mp hn).2.2
  simp only [canonicalBlock, List.mem_cons, List.not_mem_nil, or_false] at hzx
  rcases hzx with rfl | rfl | rfl
  · exact False.elim <| hdis _ (by simp [D.before_eq]) _ hzRest rfl
  · exact False.elim <| hdis _ (by simp [D.before_eq]) _ hzRest rfl
  · rfl

/-- Over the original terminal vertex, the cut lift retains only the incoming
copy.  The plain and outgoing copies lie in the discarded terminal block. -/
theorem eq_incoming_finish_of_mem_lift_support_of_project_eq
    (Z : FracturedWarp Gamma) (p : FinitePath Gamma.graph)
    (hne : p.start ≠ p.finish) {z : Vertex V}
    (hz : z ∈ (lift Z p hne).support) (hproject : project z = p.finish) :
    z = incoming p.finish := by
  let D := canonicalOccurrenceData Z p hne
  have hzFull := (lift_isSubpathOf_swappedExpansion Z p hne).1 hz
  change z ∈ (swappedExpansion Z p).support at hzFull
  rcases (swappedExpansion_support_set Z p).1 hzFull with
    ⟨x, hx, hzx⟩
  have hxfinish : x = p.finish := by
    exact (mem_canonicalBlock_project hzx).symm.trans hproject
  subst x
  let core := outgoing p.start :: D.occurrence.middle ++ [incoming p.finish]
  let pre := D.occurrence.before ++ core
  have hzCore : z ∈ core := by
    change z ∈ (lift Z p hne).walk.support at hz
    simpa only [lift, D, core,
      (swappedExpansion Z p).between_support_eq D.occurrence] using hz
  have hzPrefix : z ∈ pre := List.mem_append_right _ hzCore
  have hn : (pre ++ D.occurrence.after).Nodup := by
    have hnFull := (swappedExpansion Z p).isPath
    rw [Walk.IsPath] at hnFull
    rw [D.occurrence.support_eq] at hnFull
    simpa only [pre, core, List.append_assoc, List.singleton_append] using hnFull
  have hdis := (List.nodup_append.mp hn).2.2
  simp only [canonicalBlock, List.mem_cons, List.not_mem_nil, or_false] at hzx
  rcases hzx with rfl | rfl | rfl
  · rfl
  · exact False.elim <| hdis _ hzPrefix _ (by simp [D.after_eq]) rfl
  · exact False.elim <| hdis _ hzPrefix _ (by simp [D.after_eq]) rfl

/-- The canonical lift loses no original vertex under projection. -/
theorem project_image_lift_support (Z : FracturedWarp Gamma)
    (p : FinitePath Gamma.graph) (hne : p.start ≠ p.finish) :
    project '' (lift Z p hne).support = p.support := by
  let D := canonicalOccurrenceData Z p hne
  apply Set.Subset.antisymm
  · rintro x ⟨z, hz, rfl⟩
    have hzFull := (lift_isSubpathOf_swappedExpansion Z p hne).1 hz
    change z ∈ (swappedExpansion Z p).support at hzFull
    rw [swappedExpansion_support_set] at hzFull
    rcases hzFull with ⟨x, hx, hzx⟩
    simpa only [mem_canonicalBlock_project hzx] using hx
  · intro x hx
    by_cases hxs : x = p.start
    · subst x
      refine ⟨outgoing p.start, ?_, rfl⟩
      simpa only [lift_start] using (lift Z p hne).start_mem_support
    by_cases hxf : x = p.finish
    · subst x
      refine ⟨incoming p.finish, ?_, rfl⟩
      simpa only [lift_finish] using (lift Z p hne).finish_mem_support
    · have hzFull : plain x ∈ (swappedExpansion Z p).support :=
        (swappedExpansion_support_set Z p).2
          ⟨x, hx, by simp [canonicalBlock]⟩
      change plain x ∈ (swappedExpansion Z p).walk.support at hzFull
      rw [D.occurrence.support_eq, D.before_eq, D.after_eq] at hzFull
      have hzMiddle : plain x ∈ D.occurrence.middle := by
        have hcases : x = p.start ∨ plain x ∈ D.occurrence.middle ∨
            x = p.finish := by
          simpa [incoming, plain, outgoing] using hzFull
        rcases hcases with hxStart | hmiddle | hxFinish
        · exact False.elim (hxs hxStart)
        · exact hmiddle
        · exact False.elim (hxf hxFinish)
      refine ⟨plain x, ?_, rfl⟩
      have hmem : plain x ∈
          (outgoing p.start :: D.occurrence.middle ++ [incoming p.finish]) := by
        simp [hzMiddle]
      have hsupp := (swappedExpansion Z p).between_support_eq D.occurrence
      change plain x ∈ (lift Z p hne).walk.support
      simpa only [lift, D, hsupp] using hmem

/-- The canonical lifts of the active (non-singleton) finite fractured
members.  Singleton members are deliberately absent from this family. -/
def liftedActiveFinitePaths (Z : FracturedWarp Gamma) :
    Set (web Gamma Z).DPath :=
  {P | ∃ (p : FinitePath Gamma.graph)
      (hp : (.inl p : Gamma.DPath) ∈ Z.paths)
      (hne : p.start ≠ p.finish),
      P = .inl (lift Z p hne)}

theorem lift_mem_liftedActiveFinitePaths (Z : FracturedWarp Gamma)
    {p : FinitePath Gamma.graph} (hp : (.inl p : Gamma.DPath) ∈ Z.paths)
    (hne : p.start ≠ p.finish) :
    (.inl (lift Z p hne) : (web Gamma Z).DPath) ∈
      liftedActiveFinitePaths Z :=
  ⟨p, hp, hne, rfl⟩

theorem liftedActiveFinitePaths_hasFiniteCharacter (Z : FracturedWarp Gamma) :
    (web Gamma Z).HasFiniteCharacter (liftedActiveFinitePaths Z) := by
  rintro P ⟨p, hp, hne, rfl⟩
  exact ⟨lift Z p hne, rfl⟩

/-- Initial vertices of the active finite members downstairs. -/
def activeFiniteInitials (Z : FracturedWarp Gamma) : Set V :=
  {x | ∃ (p : FinitePath Gamma.graph)
      (_hp : (.inl p : Gamma.DPath) ∈ Z.paths)
      (_hne : p.start ≠ p.finish), p.start = x}

/-- Finite terminals of the active finite members downstairs. -/
def activeFiniteTerminals (Z : FracturedWarp Gamma) : Set V :=
  {x | ∃ (p : FinitePath Gamma.graph)
      (_hp : (.inl p : Gamma.DPath) ∈ Z.paths)
      (_hne : p.start ≠ p.finish), p.finish = x}

/-- The lifted family starts at precisely the outgoing copies of the active
downstairs initials. -/
theorem initialSet_liftedActiveFinitePaths (Z : FracturedWarp Gamma) :
    (web Gamma Z).initialSet (liftedActiveFinitePaths Z) =
      outgoing '' activeFiniteInitials Z := by
  ext z
  constructor
  · rintro ⟨P, ⟨p, hp, hpne, rfl⟩, rfl⟩
    exact ⟨p.start, ⟨p, hp, hpne, rfl⟩, rfl⟩
  · rintro ⟨x, ⟨p, hp, hpne, rfl⟩, rfl⟩
    exact ⟨.inl (lift Z p hpne), ⟨p, hp, hpne, rfl⟩, rfl⟩

/-- The lifted family ends at precisely the incoming copies of the active
downstairs finite terminals. -/
theorem terminalFrontier_liftedActiveFinitePaths (Z : FracturedWarp Gamma) :
    (web Gamma Z).terminalFrontier (liftedActiveFinitePaths Z) =
      incoming '' activeFiniteTerminals Z := by
  ext z
  constructor
  · rintro ⟨P, ⟨p, hp, hpne, rfl⟩, hterm⟩
    have hz : incoming p.finish = z := by
      change some (incoming p.finish) = some z at hterm
      exact Option.some.inj hterm
    exact ⟨p.finish, ⟨p, hp, hpne, rfl⟩, hz⟩
  · rintro ⟨x, ⟨p, hp, hpne, rfl⟩, rfl⟩
    exact ⟨.inl (lift Z p hpne), ⟨p, hp, hpne, rfl⟩, by simp⟩

/-- The fixed-role canonical lifts of active finite fractured members form an
honest warp.  At an allowed fractured junction the earlier member ends at an
incoming copy and the later member starts at the distinct outgoing copy. -/
theorem liftedActiveFinitePaths_isWarp (Z : FracturedWarp Gamma) :
    (web Gamma Z).IsWarp (liftedActiveFinitePaths Z) := by
  rintro P ⟨p, hp, hpne, rfl⟩ Q ⟨q, hq, hqne, rfl⟩ hPQ
  have hpq : (.inl p : Gamma.DPath) ≠ .inl q := by
    intro hpq'
    have hpq'' : p = q := Sum.inl.inj hpq'
    subst q
    exact hPQ rfl
  change Disjoint (lift Z p hpne).support (lift Z q hqne).support
  rw [Set.disjoint_left]
  intro z hzp hzq
  have hxp : project z ∈ p.support := by
    rw [← project_image_lift_support Z p hpne]
    exact ⟨z, hzp, rfl⟩
  have hxq : project z ∈ q.support := by
    rw [← project_image_lift_support Z q hqne]
    exact ⟨z, hzq, rfl⟩
  have hnotdisj : ¬ Disjoint p.support q.support := by
    rw [Set.not_disjoint_iff]
    exact ⟨project z, hxp, hxq⟩
  rcases Z.allowed_intersection hp hq hpq hnotdisj with
    ⟨_, _, hmeet | hmeet⟩
  · rcases hmeet with ⟨t, hqt, hpi, hinter⟩
    have hqfinish : q.finish = t := by
      change some q.finish = some t at hqt
      exact Option.some.inj hqt
    have hpstart : p.start = t := hpi
    have hxt : project z = t := by
      have : project z ∈ ({t} : Set V) := by
        rw [← hinter]
        exact ⟨hxp, hxq⟩
      simpa using this
    have hzp' : z = outgoing p.start :=
      eq_outgoing_start_of_mem_lift_support_of_project_eq Z p hpne hzp
        (hxt.trans hpstart.symm)
    have hzq' : z = incoming q.finish :=
      eq_incoming_finish_of_mem_lift_support_of_project_eq Z q hqne hzq
        (hxt.trans hqfinish.symm)
    have hroles : outgoing p.start = incoming q.finish :=
      hzp'.symm.trans hzq'
    simpa [outgoing, incoming] using hroles
  · rcases hmeet with ⟨t, hpt, hqi, hinter⟩
    have hpfinish : p.finish = t := by
      change some p.finish = some t at hpt
      exact Option.some.inj hpt
    have hqstart : q.start = t := hqi
    have hxt : project z = t := by
      have : project z ∈ ({t} : Set V) := by
        rw [← hinter]
        exact ⟨hxp, hxq⟩
      simpa using this
    have hzp' : z = incoming p.finish :=
      eq_incoming_finish_of_mem_lift_support_of_project_eq Z p hpne hzp
        (hxt.trans hpfinish.symm)
    have hzq' : z = outgoing q.start :=
      eq_outgoing_start_of_mem_lift_support_of_project_eq Z q hqne hzq
        (hxt.trans hqstart.symm)
    have hroles : incoming p.finish = outgoing q.start :=
      hzp'.symm.trans hzq'
    simpa [outgoing, incoming] using hroles

/-- Every proper edge of the active lifted warp projects to a literal edge of
the original fractured family. -/
theorem project_edge_mem_familyEdges_of_mem_liftedActiveFinitePaths
    (Z : FracturedWarp Gamma) {e : Vertex V × Vertex V}
    (he : e ∈ familyEdges (liftedActiveFinitePaths Z))
    (hproper : project e.1 ≠ project e.2) :
    (project e.1, project e.2) ∈ familyEdges Z.paths := by
  simp only [familyEdges, Set.mem_iUnion] at he ⊢
  rcases he with ⟨P, ⟨p, hp, hpne, rfl⟩, he⟩
  change e ∈ (lift Z p hpne).edgeSet at he
  have hclass := lift_edge_roles_of_project_ne Z p hpne he hproper
  exact ⟨.inl p, hp, hclass.2.2⟩

/-- Projection is injective on the proper edges of the canonical active
lift.  Thus a downstairs genuine edge has at most one upstairs occurrence,
and that occurrence has the forced roles `outgoing -> incoming`. -/
theorem projectEdge_injOn_proper_liftedActiveFinitePaths
    (Z : FracturedWarp Gamma) :
    Set.InjOn (fun e : Vertex V × Vertex V ↦
      (project e.1, project e.2))
      {e | e ∈ familyEdges (liftedActiveFinitePaths Z) ∧
        project e.1 ≠ project e.2} := by
  intro e he f hf hproject
  have he₁ := he.1
  simp only [familyEdges, Set.mem_iUnion] at he₁
  rcases he₁ with ⟨P, ⟨p, hp, hpne, rfl⟩, hep⟩
  change e ∈ (lift Z p hpne).edgeSet at hep
  have heClass := lift_edge_roles_of_project_ne Z p hpne hep he.2
  have hf₁ := hf.1
  simp only [familyEdges, Set.mem_iUnion] at hf₁
  rcases hf₁ with ⟨Q, ⟨q, hq, hqne, rfl⟩, hfq⟩
  change f ∈ (lift Z q hqne).edgeSet at hfq
  have hfClass := lift_edge_roles_of_project_ne Z q hqne hfq hf.2
  change (project e.1, project e.2) =
    (project f.1, project f.2) at hproject
  have hfirst : project e.1 = project f.1 :=
    congrArg (fun z : V × V ↦ z.1) hproject
  have hsecond : project e.2 = project f.2 :=
    congrArg (fun z : V × V ↦ z.2) hproject
  apply Prod.ext
  · rw [heClass.1, hfClass.1, hfirst]
  · rw [heClass.2.1, hfClass.2.1, hsecond]

#print axioms exists_canonicalOccurrenceData
#print axioms project_image_lift_support
#print axioms liftedActiveFinitePaths_isWarp
#print axioms projectEdge_injOn_proper_liftedActiveFinitePaths

end Erdos599.Alternating.FracturedCanonicalFiniteLift
