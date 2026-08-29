/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.Alternating

/-!
# Duplicating the junctions of a fractured warp

This file isolates the vertex-splitting construction in Remark 4.20 of
Aharoni--Berger.  A vertex which is simultaneously the initial vertex of one
member of a fractured warp and the finite terminal of another member gets an
incoming and an outgoing copy.  On a member of the fractured warp, an initial
junction is sent to the outgoing copy and a terminal junction to the incoming
copy.  All other occurrences use the plain copy.

The split graph contains every lift of an original edge, together with the
two directed connector edges between the copies of a junction.  Thus its
projection to the original graph contracts only connector edges.
-/

namespace Erdos599
namespace Alternating

open Set
open DirectedPath

universe u

variable {V : Type u} {Γ : DWeb V}

namespace FracturedDuplication

/-- The three roles of a vertex in the duplicated graph. -/
inductive Role
  | plain
  | incoming
  | outgoing
  deriving DecidableEq, Repr

/-- A vertex together with its role in the duplicated graph. -/
abbrev Vertex (V : Type u) := V × Role

/-- Forget the role of a duplicated vertex. -/
def project : Vertex V → V := Prod.fst

/-- A junction of a fractured warp is both a fragment source and a finite
fragment terminal. -/
def IsJunction (Z : FracturedWarp Γ) (x : V) : Prop :=
  x ∈ Γ.initialSet Z.paths ∩ Γ.terminalFrontier Z.paths

/-- The plain copy of a vertex. -/
def plain (x : V) : Vertex V := (x, .plain)

/-- The copy on the incoming side of a fractured-warp junction. -/
def incoming (x : V) : Vertex V := (x, .incoming)

/-- The copy on the outgoing side of a fractured-warp junction. -/
def outgoing (x : V) : Vertex V := (x, .outgoing)

/-- The canonical copy of a source occurrence.  We duplicate all vertices,
not merely junctions; the surplus copies are harmless and make expansion of
the reference warp uniform. -/
def sourceCopy (_Z : FracturedWarp Γ) (x : V) : Vertex V := outgoing x

/-- The canonical copy at which an expanded finite path leaves a vertex
block. -/
def terminalCopy (_Z : FracturedWarp Γ) (x : V) : Vertex V := incoming x

@[simp] theorem project_plain (x : V) : project (plain x) = x := rfl
@[simp] theorem project_incoming (x : V) : project (incoming x) = x := rfl
@[simp] theorem project_outgoing (x : V) : project (outgoing x) = x := rfl

@[simp] theorem project_sourceCopy (Z : FracturedWarp Γ) (x : V) :
    project (sourceCopy Z x) = x := rfl

theorem sourceCopy_injective (Z : FracturedWarp Γ) :
    Function.Injective (sourceCopy Z) := by
  intro x y h
  simpa only [project_sourceCopy] using congrArg project h

@[simp] theorem project_terminalCopy (Z : FracturedWarp Γ) (x : V) :
    project (terminalCopy Z x) = x := rfl

theorem terminalCopy_injective (Z : FracturedWarp Γ) :
    Function.Injective (terminalCopy Z) := by
  intro x y h
  simpa only [project_terminalCopy] using congrArg project h

/-- The occurrence of `x` on a particular fractured-warp path.  Initial
vertices use the outgoing copy, finite terminal vertices use the incoming
copy, and every other occurrence uses the plain copy. -/
noncomputable def occurrence (_Z : FracturedWarp Γ) (p : Γ.DPath) (x : V) :
    Vertex V := by
  classical
  exact
    if x = p.initial then outgoing x
    else if Γ.terminal? p = some x then incoming x
    else plain x

@[simp] theorem project_occurrence (Z : FracturedWarp Γ) (p : Γ.DPath) (x : V) :
    project (occurrence Z p x) = x := by
  classical
  rw [occurrence]
  split
  · rfl
  · split <;> rfl

theorem occurrence_injective (Z : FracturedWarp Γ) (p : Γ.DPath) :
    Function.Injective (occurrence Z p) := by
  intro x y h
  simpa only [project_occurrence] using congrArg project h

/-- The duplicated graph.  Every original edge may be lifted between any
two roles.  The only extra edges are connectors between distinct copies of
the same original vertex.  This deliberately makes the projection relation
explicit: an edge either projects to an original edge or is contracted.
-/
def graph (Γ : DWeb V) (_Z : FracturedWarp Γ) : Digraph (Vertex V) where
  Adj a b :=
    Γ.graph.Adj (project a) (project b) ∨
      (project a = project b ∧ a.2 ≠ b.2)

/-- The duplicated web.  Its distinguished sides are the full inverse
images of the original sides; later reductions may use smaller, lifted side
sets without changing the graph. -/
def web (Γ : DWeb V) (Z : FracturedWarp Γ) : DWeb (Vertex V) where
  graph := graph Γ Z
  source := project ⁻¹' Γ.source
  target := project ⁻¹' Γ.target

theorem graph_adj_of_adj (Z : FracturedWarp Γ) {a b : Vertex V}
    (h : Γ.graph.Adj (project a) (project b)) : (graph Γ Z).Adj a b :=
  Or.inl h

theorem graph_adj_projects_or_contracts (Z : FracturedWarp Γ)
    {a b : Vertex V} (h : (graph Γ Z).Adj a b) :
    Γ.graph.Adj (project a) (project b) ∨
      project a = project b := by
  rcases h with h | ⟨hab, _⟩
  · exact Or.inl h
  · exact Or.inr hab

theorem web_adj_occurrence (Z : FracturedWarp Γ) (p : Γ.DPath)
    {x y : V} (h : Γ.graph.Adj x y) :
    (web Γ Z).graph.Adj (occurrence Z p x) (occurrence Z p y) := by
  apply graph_adj_of_adj Z
  simpa using h

/-! ## Mapping paths into a graph on another vertex type -/

section Map

variable {W : Type u} {D : Digraph V} {E : Digraph W}

/-- Map a directed walk along a vertex map which sends edges to edges. -/
def mapWalk (f : V → W) (h : ∀ {x y}, D.Adj x y → E.Adj (f x) (f y)) :
    {x y : V} → Walk D x y → Walk E (f x) (f y)
  | _, _, .nil => .nil
  | _, _, .cons e p => .cons (h e) (mapWalk f h p)

@[simp] theorem support_mapWalk (f : V → W)
    (h : ∀ {x y}, D.Adj x y → E.Adj (f x) (f y))
    {x y : V} (p : Walk D x y) :
    (mapWalk f h p).support = p.support.map f := by
  induction p with
  | nil => rfl
  | cons e p ih => simp only [mapWalk, Walk.support_cons, List.map_cons, ih]

theorem isPath_mapWalk (f : V → W) (hf : Function.Injective f)
    (h : ∀ {x y}, D.Adj x y → E.Adj (f x) (f y))
    {x y : V} {p : Walk D x y} (hp : p.IsPath) :
    (mapWalk f h p).IsPath := by
  rw [Walk.isPath_iff, support_mapWalk]
  exact hp.map hf

/-- Map a finite directed path along an injective edge map. -/
def mapFinitePath (f : V → W) (hf : Function.Injective f)
    (h : ∀ {x y}, D.Adj x y → E.Adj (f x) (f y))
    (p : FinitePath D) : FinitePath E where
  start := f p.start
  finish := f p.finish
  walk := mapWalk f h p.walk
  isPath := isPath_mapWalk f hf h p.isPath

@[simp] theorem start_mapFinitePath (f : V → W) (hf : Function.Injective f)
    (h : ∀ {x y}, D.Adj x y → E.Adj (f x) (f y))
    (p : FinitePath D) :
    (mapFinitePath f hf h p).start = f p.start := rfl

@[simp] theorem finish_mapFinitePath (f : V → W) (hf : Function.Injective f)
    (h : ∀ {x y}, D.Adj x y → E.Adj (f x) (f y))
    (p : FinitePath D) :
    (mapFinitePath f hf h p).finish = f p.finish := rfl

@[simp] theorem mem_support_mapFinitePath (f : V → W) (hf : Function.Injective f)
    (h : ∀ {x y}, D.Adj x y → E.Adj (f x) (f y))
    (p : FinitePath D) (z : W) :
    z ∈ (mapFinitePath f hf h p).support ↔ ∃ x ∈ p.support, f x = z := by
  change z ∈ (mapWalk f h p.walk).support ↔ _
  rw [support_mapWalk]
  simp [FinitePath.support]

/-- Map a ray along an injective edge map. -/
def mapRay (f : V → W) (hf : Function.Injective f)
    (h : ∀ {x y}, D.Adj x y → E.Adj (f x) (f y))
    (r : Ray D) : Ray E where
  toFun n := f (r n)
  adj_succ n := h (r.adj_succ n)
  injective := hf.comp r.injective

@[simp] theorem apply_mapRay (f : V → W) (hf : Function.Injective f)
    (h : ∀ {x y}, D.Adj x y → E.Adj (f x) (f y))
    (r : Ray D) (n : ℕ) : mapRay f hf h r n = f (r n) := rfl

@[simp] theorem mem_support_mapRay (f : V → W) (hf : Function.Injective f)
    (h : ∀ {x y}, D.Adj x y → E.Adj (f x) (f y))
    (r : Ray D) (z : W) :
    z ∈ (mapRay f hf h r).support ↔ ∃ x ∈ r.support, f x = z := by
  constructor
  · rintro ⟨n, rfl⟩
    exact ⟨r n, ⟨n, rfl⟩, rfl⟩
  · rintro ⟨x, ⟨n, rfl⟩, rfl⟩
    exact ⟨n, rfl⟩

/-- Map a finite path or ray along an injective edge map. -/
def mapPath (f : V → W) (hf : Function.Injective f)
    (h : ∀ {x y}, D.Adj x y → E.Adj (f x) (f y)) :
    Path D → Path E
  | .inl p => .inl (mapFinitePath f hf h p)
  | .inr r => .inr (mapRay f hf h r)

@[simp] theorem initial_mapPath (f : V → W) (hf : Function.Injective f)
    (h : ∀ {x y}, D.Adj x y → E.Adj (f x) (f y))
    (p : Path D) : (mapPath f hf h p).initial = f p.initial := by
  rcases p with p | r <;> rfl

@[simp] theorem mem_support_mapPath (f : V → W) (hf : Function.Injective f)
    (h : ∀ {x y}, D.Adj x y → E.Adj (f x) (f y))
    (p : Path D) (z : W) :
    z ∈ (mapPath f hf h p).support ↔ ∃ x ∈ p.support, f x = z := by
  rcases p with p | r
  · exact mem_support_mapFinitePath f hf h p z
  · exact mem_support_mapRay f hf h r z

@[simp] theorem terminal_mapPath (f : V → W) (hf : Function.Injective f)
    (h : ∀ {x y}, D.Adj x y → E.Adj (f x) (f y))
    (p : Path D) :
    (mapPath f hf h p).terminal? = p.terminal?.map f := by
  rcases p with p | r <;> rfl

end Map

/-! ## The lifted fractured family -/

/-- Lift one member of a fractured warp to the duplicated graph. -/
noncomputable def liftPath (Z : FracturedWarp Γ) (p : Γ.DPath) :
    (web Γ Z).DPath :=
  mapPath (occurrence Z p) (occurrence_injective Z p)
    (web_adj_occurrence Z p) p

@[simp] theorem initial_liftPath (Z : FracturedWarp Γ) (p : Γ.DPath) :
    (liftPath Z p).initial = occurrence Z p p.initial :=
  by
    unfold liftPath
    apply initial_mapPath

@[simp] theorem mem_support_liftPath (Z : FracturedWarp Γ)
    (p : Γ.DPath) (z : Vertex V) :
    z ∈ (liftPath Z p).support ↔
      ∃ x ∈ p.support, occurrence Z p x = z :=
  by
    unfold liftPath
    apply mem_support_mapPath

@[simp] theorem terminal_liftPath (Z : FracturedWarp Γ) (p : Γ.DPath) :
    (liftPath Z p).terminal? = p.terminal?.map (occurrence Z p) :=
  by
    unfold liftPath
    apply terminal_mapPath

@[simp] theorem project_initial_liftPath (Z : FracturedWarp Γ) (p : Γ.DPath) :
    project (liftPath Z p).initial = p.initial := by
  rw [initial_liftPath, project_occurrence]

theorem project_image_support_liftPath (Z : FracturedWarp Γ) (p : Γ.DPath) :
    project '' (liftPath Z p).support = p.support := by
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    rcases (mem_support_liftPath Z p z).1 hz with ⟨y, hy, hyz⟩
    have : y = project z := by
      simpa only [project_occurrence] using congrArg project hyz
    exact this ▸ hy
  · intro hx
    refine ⟨occurrence Z p x, ?_, project_occurrence Z p x⟩
    exact (mem_support_liftPath Z p (occurrence Z p x)).2 ⟨x, hx, rfl⟩

@[simp] theorem terminal_liftPath_projected (Z : FracturedWarp Γ) (p : Γ.DPath) :
    (liftPath Z p).terminal?.map project = p.terminal? := by
  rw [terminal_liftPath]
  rcases h : p.terminal? with _ | x
  · rfl
  · simp

/-- The lifted family of fractured-warp members. -/
noncomputable def liftedPaths (Z : FracturedWarp Γ) :
    Set (web Γ Z).DPath := liftPath Z '' Z.paths

theorem liftPath_mem_liftedPaths (Z : FracturedWarp Γ) {p : Γ.DPath}
    (hp : p ∈ Z.paths) : liftPath Z p ∈ liftedPaths Z :=
  ⟨p, hp, rfl⟩

/-- A nontrivial finite path cannot have equal endpoints. -/
theorem walk_support_eq_singleton_of_isPath_of_endpoints_eq
    {D : Digraph V} {u v : V} (w : Walk D u v)
    (hw : w.IsPath) (h : u = v) : w.support = [u] := by
  induction w with
  | nil => rfl
  | @cons u v w e q ih =>
      have hn : u ∉ q.support := (List.nodup_cons.1 hw).1
      exact (hn (h ▸ q.end_mem_support)).elim

theorem finite_start_ne_finish_of_nontrivial
    (p : FinitePath Γ.graph) (hp : PathNontrivial (Sum.inl p)) :
    p.start ≠ p.finish := by
  intro hsf
  rcases hp with ⟨x, hx, y, hy, hxy⟩
  have hsingleton : p.walk.support = [p.start] :=
    walk_support_eq_singleton_of_isPath_of_endpoints_eq p.walk p.isPath hsf
  have hx' : x = p.start := by
    change x ∈ p.walk.support at hx
    rw [hsingleton] at hx
    simpa using hx
  have hy' : y = p.start := by
    change y ∈ p.walk.support at hy
    rw [hsingleton] at hy
    simpa using hy
  exact hxy (hx'.trans hy'.symm)

theorem initial_ne_terminal_of_nontrivial {p : Γ.DPath} {t : V}
    (hp : PathNontrivial p) (ht : Γ.terminal? p = some t) :
    p.initial ≠ t := by
  rcases p with p | r
  · have hfinish : p.finish = t := Option.some.inj ht
    change p.start ≠ t
    exact fun hstart ↦ finite_start_ne_finish_of_nontrivial p hp
      (hstart.trans hfinish.symm)
  · simp at ht

theorem junction_of_initial_terminal (Z : FracturedWarp Γ)
    {p q : Γ.DPath} (hp : p ∈ Z.paths) (hq : q ∈ Z.paths)
    {x : V} (hpi : p.initial = x) (hqt : Γ.terminal? q = some x) :
    IsJunction Z x := by
  constructor
  · exact ⟨p, hp, hpi⟩
  · exact ⟨q, hq, hqt⟩

theorem occurrence_initial_at_junction (Z : FracturedWarp Γ)
    (p : Γ.DPath) {x : V} (_hj : IsJunction Z x) (hpi : p.initial = x) :
    occurrence Z p x = outgoing x := by
  simp [occurrence, hpi]

theorem occurrence_initial (Z : FracturedWarp Γ) (p : Γ.DPath) :
    occurrence Z p p.initial = sourceCopy Z p.initial := by
  simp [occurrence, sourceCopy]

theorem occurrence_terminal_at_junction (Z : FracturedWarp Γ)
    {p : Γ.DPath} {x : V} (hpnt : PathNontrivial p)
    (_hj : IsJunction Z x) (hpt : Γ.terminal? p = some x) :
    occurrence Z p x = incoming x := by
  have hne : x ≠ p.initial := (initial_ne_terminal_of_nontrivial hpnt hpt).symm
  simp [occurrence, hpt, hne]

theorem outgoing_ne_incoming (x : V) : outgoing x ≠ incoming x := by
  intro h
  exact Role.noConfusion (congrArg Prod.snd h)

/-- The two occurrences at every permitted fracture are separated by the
duplication: the initial occurrence is outgoing and the terminal occurrence
is incoming. -/
theorem occurrences_ne_of_allowed_intersection (Z : FracturedWarp Γ)
    {p q : Γ.DPath} (hp : p ∈ Z.paths) (hq : q ∈ Z.paths) (hpq : p ≠ q)
    {x : V} (hxp : x ∈ p.support) (hxq : x ∈ q.support) :
    occurrence Z p x ≠ occurrence Z q x := by
  have hnotdisj : ¬ Disjoint p.support q.support := by
    rw [Set.not_disjoint_iff]
    exact ⟨x, hxp, hxq⟩
  rcases Z.allowed_intersection hp hq hpq hnotdisj with
    ⟨hpnt, hqnt, hcase | hcase⟩
  · rcases hcase with ⟨t, hqt, hpi, hinter⟩
    have hxt : x = t := by
      have hxinter : x ∈ p.support ∩ q.support := ⟨hxp, hxq⟩
      rw [hinter] at hxinter
      simpa using hxinter
    subst x
    have hj := junction_of_initial_terminal Z hp hq hpi hqt
    rw [occurrence_initial_at_junction Z p hj hpi,
      occurrence_terminal_at_junction Z hqnt hj hqt]
    exact outgoing_ne_incoming t
  · rcases hcase with ⟨t, hpt, hqi, hinter⟩
    have hxt : x = t := by
      have hxinter : x ∈ p.support ∩ q.support := ⟨hxp, hxq⟩
      rw [hinter] at hxinter
      simpa using hxinter
    subst x
    have hj := junction_of_initial_terminal Z hq hp hqi hpt
    rw [occurrence_terminal_at_junction Z hpnt hj hpt,
      occurrence_initial_at_junction Z q hj hqi]
    exact (outgoing_ne_incoming t).symm

/-- The lifted fractured family is an honest warp.  This is the central
set-theoretic assertion in Remark 4.20. -/
theorem liftedPaths_isWarp (Z : FracturedWarp Γ) :
    (web Γ Z).IsWarp (liftedPaths Z) := by
  intro P hP Q hQ hPQ
  rcases hP with ⟨p, hp, rfl⟩
  rcases hQ with ⟨q, hq, rfl⟩
  have hpq : p ≠ q := by
    intro hpq
    subst q
    exact hPQ rfl
  change Disjoint (liftPath Z p).support (liftPath Z q).support
  rw [Set.disjoint_left]
  intro z hzp hzq
  rcases (mem_support_liftPath Z p z).1 hzp with ⟨x, hxp, hxz⟩
  rcases (mem_support_liftPath Z q z).1 hzq with ⟨y, hyq, hyz⟩
  have hxy : x = y := by
    simpa only [project_occurrence] using
      congrArg project (hxz.trans hyz.symm)
  subst y
  exact occurrences_ne_of_allowed_intersection Z hp hq hpq hxp hyq
    (hxz.trans hyz.symm)

/-- Finite character is unchanged by duplicating vertices. -/
theorem liftedPaths_hasFiniteCharacter (Z : FracturedWarp Γ)
    (hfin : Γ.HasFiniteCharacter Z.paths) :
    (web Γ Z).HasFiniteCharacter (liftedPaths Z) := by
  intro P hP
  rcases hP with ⟨p, hp, rfl⟩
  rcases hfin hp with ⟨q, rfl⟩
  exact ⟨mapFinitePath (occurrence Z (Sum.inl q))
    (occurrence_injective Z (Sum.inl q))
    (web_adj_occurrence Z (Sum.inl q)) q, rfl⟩

/-- The source set of the lifted proper warp is exactly the image, under
the outgoing/plain source-copy map, of the source set of the fractured
warp. -/
theorem initialSet_liftedPaths (Z : FracturedWarp Γ) :
    (web Γ Z).initialSet (liftedPaths Z) =
      sourceCopy Z '' Γ.initialSet Z.paths := by
  ext z
  constructor
  · rintro ⟨P, ⟨p, hp, rfl⟩, hP⟩
    rw [initial_liftPath, occurrence_initial] at hP
    refine ⟨p.initial, ⟨p, hp, rfl⟩, ?_⟩
    exact hP
  · rintro ⟨x, ⟨p, hp, hpx⟩, rfl⟩
    refine ⟨liftPath Z p, liftPath_mem_liftedPaths Z hp, ?_⟩
    rw [initial_liftPath, occurrence_initial, hpx]

theorem sourceCopy_mem_initialSet_liftedPaths (Z : FracturedWarp Γ)
    {x : V} (hx : x ∈ Γ.initialSet Z.paths) :
    sourceCopy Z x ∈ (web Γ Z).initialSet (liftedPaths Z) := by
  rw [initialSet_liftedPaths]
  exact ⟨x, hx, rfl⟩

/-! ## Expanding the finite reference warp through every junction copy -/

/-- The list of split vertices representing one original vertex on an
expanded reference path. -/
noncomputable def vertexBlock (_Z : FracturedWarp Γ) (x : V) :
    List (Vertex V) := [outgoing x, plain x, incoming x]

theorem vertexBlock_nodup (Z : FracturedWarp Γ) (x : V) :
    (vertexBlock Z x).Nodup := by
  simp [vertexBlock, outgoing, plain, incoming]

theorem mem_vertexBlock_project (Z : FracturedWarp Γ) {x : V} {z : Vertex V}
    (hz : z ∈ vertexBlock Z x) : project z = x := by
  have hz' : z = outgoing x ∨ z = plain x ∨ z = incoming x := by
    simpa only [vertexBlock, List.mem_cons, List.not_mem_nil, or_false] using hz
  rcases hz' with rfl | rfl | rfl <;> rfl

theorem sourceCopy_mem_vertexBlock (Z : FracturedWarp Γ) (x : V) :
    sourceCopy Z x ∈ vertexBlock Z x := by
  simp [sourceCopy, vertexBlock]

theorem terminalCopy_mem_vertexBlock (Z : FracturedWarp Γ) (x : V) :
    terminalCopy Z x ∈ vertexBlock Z x := by
  simp [terminalCopy, vertexBlock]

/-- The connector walk through all copies of a single vertex. -/
noncomputable def vertexWalk (Z : FracturedWarp Γ) (x : V) :
    Walk (web Γ Z).graph (sourceCopy Z x) (terminalCopy Z x) := by
  let h₁ : (web Γ Z).graph.Adj (outgoing x) (plain x) :=
    Or.inr ⟨rfl, by simp [outgoing, plain]⟩
  let h₂ : (web Γ Z).graph.Adj (plain x) (incoming x) :=
    Or.inr ⟨rfl, by simp [plain, incoming]⟩
  exact Walk.cons h₁ (Walk.cons h₂ Walk.nil)

@[simp] theorem support_vertexWalk (Z : FracturedWarp Γ) (x : V) :
    (vertexWalk Z x).support = vertexBlock Z x := by
  change [outgoing x, plain x, incoming x] = vertexBlock Z x
  rfl

theorem vertexWalk_isPath (Z : FracturedWarp Γ) (x : V) :
    (vertexWalk Z x).IsPath := by
  rw [Walk.isPath_iff, support_vertexWalk]
  exact vertexBlock_nodup Z x

theorem adj_terminal_source_of_adj (Z : FracturedWarp Γ) {x y : V}
    (h : Γ.graph.Adj x y) :
    (web Γ Z).graph.Adj (terminalCopy Z x) (sourceCopy Z y) := by
  apply graph_adj_of_adj Z
  simpa using h

/-- Expand every vertex of an original walk to its full split-vertex block. -/
noncomputable def expandWalk (Z : FracturedWarp Γ) :
    {x y : V} → Walk Γ.graph x y →
      Walk (web Γ Z).graph (sourceCopy Z x) (terminalCopy Z y)
  | _, _, .nil => vertexWalk Z _
  | _, _, .cons e p =>
      (vertexWalk Z _).append
        (.cons (adj_terminal_source_of_adj Z e) (expandWalk Z p))

@[simp] theorem support_expandWalk (Z : FracturedWarp Γ) :
    {x y : V} → (p : Walk Γ.graph x y) →
      (expandWalk Z p).support = p.support.flatMap (vertexBlock Z)
  | _, _, .nil => by simp [expandWalk]
  | _, _, .cons e p => by
      rw [expandWalk, Walk.support_append, support_vertexWalk]
      simp [support_expandWalk Z p]

theorem isPath_expandWalk (Z : FracturedWarp Γ) {x y : V}
    (p : Walk Γ.graph x y) (hp : p.IsPath) :
    (expandWalk Z p).IsPath := by
  rw [Walk.isPath_iff, support_expandWalk]
  induction p with
  | nil => simp [vertexBlock_nodup]
  | @cons x y z e p ih =>
      rw [Walk.isPath_iff] at hp
      have hx : x ∉ p.support := (List.nodup_cons.1 hp).1
      have hp' : p.IsPath := (List.nodup_cons.1 hp).2
      simp only [Walk.support_cons, List.flatMap_cons]
      rw [List.nodup_append]
      refine ⟨vertexBlock_nodup Z x, ih hp', ?_⟩
      intro a ha b hb hab
      have hpa : project a = x := mem_vertexBlock_project Z ha
      simp only [List.mem_flatMap] at hb
      rcases hb with ⟨y, hy, hby⟩
      have hpb : project b = y := mem_vertexBlock_project Z hby
      have hxy : x = y := hpa.symm.trans ((congrArg project hab).trans hpb)
      exact hx (hxy ▸ hy)

/-- Expand a finite reference path through all split copies over its support. -/
noncomputable def expandFinitePath (Z : FracturedWarp Γ)
    (p : FinitePath Γ.graph) : FinitePath (web Γ Z).graph where
  start := sourceCopy Z p.start
  finish := terminalCopy Z p.finish
  walk := expandWalk Z p.walk
  isPath := isPath_expandWalk Z p.walk p.isPath

@[simp] theorem start_expandFinitePath (Z : FracturedWarp Γ)
    (p : FinitePath Γ.graph) :
    (expandFinitePath Z p).start = sourceCopy Z p.start := rfl

@[simp] theorem finish_expandFinitePath (Z : FracturedWarp Γ)
    (p : FinitePath Γ.graph) :
    (expandFinitePath Z p).finish = terminalCopy Z p.finish := rfl

@[simp] theorem support_expandFinitePath (Z : FracturedWarp Γ)
    (p : FinitePath Γ.graph) :
    (expandFinitePath Z p).support =
      {z | ∃ x ∈ p.support, z ∈ vertexBlock Z x} := by
  ext z
  change z ∈ (expandWalk Z p.walk).support ↔ _
  rw [support_expandWalk]
  simp [FinitePath.support]

/-- Lift a finite-character reference warp, expanding every member through
all copies of every junction on that member. -/
noncomputable def liftedReference (Z : FracturedWarp Γ)
    (Y : Set Γ.DPath) : Set (web Γ Z).DPath :=
  {P | ∃ p : FinitePath Γ.graph, (Sum.inl p : Γ.DPath) ∈ Y ∧
      P = Sum.inl (expandFinitePath Z p)}

theorem mem_liftedReference_iff (Z : FracturedWarp Γ)
    {Y : Set Γ.DPath} {P : (web Γ Z).DPath} :
    P ∈ liftedReference Z Y ↔
      ∃ p : FinitePath Γ.graph, (Sum.inl p : Γ.DPath) ∈ Y ∧
        P = Sum.inl (expandFinitePath Z p) :=
  Iff.rfl

theorem liftedReference_hasFiniteCharacter (Z : FracturedWarp Γ)
    (Y : Set Γ.DPath) :
    (web Γ Z).HasFiniteCharacter (liftedReference Z Y) := by
  rintro P ⟨p, hp, rfl⟩
  exact ⟨expandFinitePath Z p, rfl⟩

theorem liftedReference_isWarp (Z : FracturedWarp Γ) {Y : Set Γ.DPath}
    (hY : Γ.IsWarp Y) :
    (web Γ Z).IsWarp (liftedReference Z Y) := by
  rintro P ⟨p, hp, rfl⟩ Q ⟨q, hq, rfl⟩ hPQ
  have hpq : (Sum.inl p : Γ.DPath) ≠ Sum.inl q := by
    intro h
    have : p = q := Sum.inl.inj h
    subst q
    exact hPQ rfl
  have hd := hY hp hq hpq
  change Disjoint p.support q.support at hd
  change Disjoint (expandFinitePath Z p).support
    (expandFinitePath Z q).support
  rw [Set.disjoint_left] at hd ⊢
  intro z hzp hzq
  rw [support_expandFinitePath] at hzp hzq
  rcases hzp with ⟨x, hxp, hzx⟩
  rcases hzq with ⟨y, hyq, hzy⟩
  have hxy : x = y := by
    rw [← mem_vertexBlock_project Z hzx, ← mem_vertexBlock_project Z hzy]
  exact hd hxp (hxy ▸ hyq)

theorem vertexSet_liftedReference (Z : FracturedWarp Γ) {Y : Set Γ.DPath}
    (hfin : Γ.HasFiniteCharacter Y) :
    (web Γ Z).vertexSet (liftedReference Z Y) =
      {z | ∃ x ∈ Γ.vertexSet Y, z ∈ vertexBlock Z x} := by
  ext z
  constructor
  · rintro ⟨P, ⟨p, hp, rfl⟩, hz⟩
    change z ∈ (expandFinitePath Z p).support at hz
    rw [support_expandFinitePath] at hz
    rcases hz with ⟨x, hxp, hzx⟩
    exact ⟨x, ⟨Sum.inl p, hp, hxp⟩, hzx⟩
  · rintro ⟨x, ⟨P, hP, hxP⟩, hzx⟩
    rcases hfin hP with ⟨p, rfl⟩
    refine ⟨Sum.inl (expandFinitePath Z p), ⟨p, hP, rfl⟩, ?_⟩
    change z ∈ (expandFinitePath Z p).support
    change x ∈ p.support at hxP
    rw [support_expandFinitePath]
    exact ⟨x, hxP, hzx⟩

theorem fiber_subset_vertexSet_liftedReference
    (Z : FracturedWarp Γ) {Y : Set Γ.DPath}
    (hfin : Γ.HasFiniteCharacter Y) {x : V}
    (hxY : x ∈ Γ.vertexSet Y) :
    project ⁻¹' {x} ⊆ (web Γ Z).vertexSet (liftedReference Z Y) := by
  rw [vertexSet_liftedReference Z hfin]
  rintro ⟨y, r⟩ hy
  simp only [Set.mem_preimage, Set.mem_singleton_iff, project] at hy
  subst y
  refine ⟨x, hxY, ?_⟩
  rcases r <;> simp [vertexBlock, plain, incoming, outgoing]

theorem initialSet_liftedReference (Z : FracturedWarp Γ) {Y : Set Γ.DPath}
    (hfin : Γ.HasFiniteCharacter Y) :
    (web Γ Z).initialSet (liftedReference Z Y) =
      sourceCopy Z '' Γ.initialSet Y := by
  ext z
  constructor
  · rintro ⟨P, ⟨p, hp, rfl⟩, hz⟩
    change (expandFinitePath Z p).start = z at hz
    exact ⟨p.start, ⟨Sum.inl p, hp, rfl⟩, hz⟩
  · rintro ⟨x, ⟨P, hP, hxP⟩, rfl⟩
    rcases hfin hP with ⟨p, rfl⟩
    refine ⟨Sum.inl (expandFinitePath Z p), ⟨p, hP, rfl⟩, ?_⟩
    change p.start = x at hxP
    change sourceCopy Z p.start = sourceCopy Z x
    rw [hxP]

/-! ## Endpoint-regular lifts

The occurrence lift above sends a singleton fractured member to its outgoing
copy.  For normalization it is more convenient to remember both sides of a
singleton occurrence: it is replaced by the connector path through its three
role copies.  Non-singleton members retain the occurrence lift.  Thus every
finite member starts at an outgoing copy and ends at an incoming copy.
-/

/-- A finite fractured member with singleton support is expanded across its
whole role fibre; every other member uses the ordinary occurrence lift. -/
noncomputable def endpointLiftFinitePath (Z : FracturedWarp Γ)
    (p : FinitePath Γ.graph) : FinitePath (web Γ Z).graph := by
  classical
  exact if p.start = p.finish then expandFinitePath Z p else
    mapFinitePath (occurrence Z (.inl p))
      (occurrence_injective Z (.inl p))
      (web_adj_occurrence Z (.inl p)) p

@[simp] theorem start_endpointLiftFinitePath (Z : FracturedWarp Γ)
    (p : FinitePath Γ.graph) :
    (endpointLiftFinitePath Z p).start = sourceCopy Z p.start := by
  classical
  by_cases h : p.start = p.finish
  · rw [endpointLiftFinitePath, if_pos h,
      start_expandFinitePath]
  · rw [endpointLiftFinitePath, if_neg h]
    change occurrence Z (.inl p) p.start = sourceCopy Z p.start
    exact occurrence_initial Z (.inl p)

@[simp] theorem finish_endpointLiftFinitePath (Z : FracturedWarp Γ)
    (p : FinitePath Γ.graph) :
    (endpointLiftFinitePath Z p).finish = terminalCopy Z p.finish := by
  classical
  by_cases h : p.start = p.finish
  · rw [endpointLiftFinitePath, if_pos h,
      finish_expandFinitePath]
  · rw [endpointLiftFinitePath, if_neg h]
    change occurrence Z (.inl p) p.finish = terminalCopy Z p.finish
    rw [occurrence]
    change (if p.finish = p.start then outgoing p.finish
      else if some p.finish = some p.finish then incoming p.finish
      else plain p.finish) = incoming p.finish
    rw [if_neg (Ne.symm h), if_pos rfl]

theorem project_image_support_endpointLiftFinitePath
    (Z : FracturedWarp Γ) (p : FinitePath Γ.graph) :
    project '' (endpointLiftFinitePath Z p).support = p.support := by
  classical
  by_cases h : p.start = p.finish
  · rw [endpointLiftFinitePath, if_pos h]
    · ext x
      simp only [support_expandFinitePath, Set.mem_image, Set.mem_setOf_eq]
      constructor
      · rintro ⟨z, ⟨y, hy, hzy⟩, rfl⟩
        simpa only [mem_vertexBlock_project Z hzy] using hy
      · intro hx
        refine ⟨sourceCopy Z x, ⟨x, hx, sourceCopy_mem_vertexBlock Z x⟩, rfl⟩
  · rw [endpointLiftFinitePath, if_neg h]
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      rcases (mem_support_mapFinitePath
          (occurrence Z (.inl p)) (occurrence_injective Z (.inl p))
          (web_adj_occurrence Z (.inl p)) p z).1 hz with ⟨y, hy, hyz⟩
      have : y = project z := by
        simpa only [project_occurrence] using congrArg project hyz
      exact this.symm ▸ hy
    · intro hx
      refine ⟨occurrence Z (.inl p) x, ?_, project_occurrence Z (.inl p) x⟩
      exact (mem_support_mapFinitePath
        (occurrence Z (.inl p)) (occurrence_injective Z (.inl p))
        (web_adj_occurrence Z (.inl p)) p _).2 ⟨x, hx, rfl⟩

/-- The endpoint-regular finite lift of the fractured family. -/
noncomputable def endpointLiftedPaths (Z : FracturedWarp Γ) :
    Set (web Γ Z).DPath :=
  {P | ∃ p : FinitePath Γ.graph, (.inl p : Γ.DPath) ∈ Z.paths ∧
      P = .inl (endpointLiftFinitePath Z p)}

theorem endpointLiftFinitePath_mem_endpointLiftedPaths
    (Z : FracturedWarp Γ) {p : FinitePath Γ.graph}
    (hp : (.inl p : Γ.DPath) ∈ Z.paths) :
    (.inl (endpointLiftFinitePath Z p) : (web Γ Z).DPath) ∈
      endpointLiftedPaths Z :=
  ⟨p, hp, rfl⟩

theorem endpointLiftedPaths_hasFiniteCharacter (Z : FracturedWarp Γ) :
    (web Γ Z).HasFiniteCharacter (endpointLiftedPaths Z) := by
  rintro P ⟨p, hp, rfl⟩
  exact ⟨endpointLiftFinitePath Z p, rfl⟩

/-- Endpoint-regularization preserves disjointness: an intersection between
two distinct original members is permitted only when both are nontrivial,
where the construction agrees with the already separated occurrence lift. -/
theorem endpointLiftedPaths_isWarp (Z : FracturedWarp Γ) :
    (web Γ Z).IsWarp (endpointLiftedPaths Z) := by
  rintro P ⟨p, hp, rfl⟩ Q ⟨q, hq, rfl⟩ hPQ
  have hpq : (.inl p : Γ.DPath) ≠ .inl q := by
    intro hpq'
    have : p = q := Sum.inl.inj hpq'
    subst q
    exact hPQ rfl
  change Disjoint (endpointLiftFinitePath Z p).support
    (endpointLiftFinitePath Z q).support
  rw [Set.disjoint_left]
  intro z hzp hzq
  have hxp : project z ∈ p.support := by
    rw [← project_image_support_endpointLiftFinitePath Z p]
    exact ⟨z, hzp, rfl⟩
  have hxq : project z ∈ q.support := by
    rw [← project_image_support_endpointLiftFinitePath Z q]
    exact ⟨z, hzq, rfl⟩
  have hnotdisj : ¬ Disjoint p.support q.support := by
    rw [Set.not_disjoint_iff]
    exact ⟨project z, hxp, hxq⟩
  rcases Z.allowed_intersection hp hq hpq hnotdisj with
    ⟨hpnt, hqnt, _hmeeting⟩
  have hpne : p.start ≠ p.finish :=
    finite_start_ne_finish_of_nontrivial p hpnt
  have hqne : q.start ≠ q.finish :=
    finite_start_ne_finish_of_nontrivial q hqnt
  rw [endpointLiftFinitePath, if_neg hpne] at hzp
  rw [endpointLiftFinitePath, if_neg hqne] at hzq
  rcases (mem_support_mapFinitePath
      (occurrence Z (.inl p)) (occurrence_injective Z (.inl p))
      (web_adj_occurrence Z (.inl p)) p z).1 hzp with
    ⟨x, hxp', hxz⟩
  rcases (mem_support_mapFinitePath
      (occurrence Z (.inl q)) (occurrence_injective Z (.inl q))
      (web_adj_occurrence Z (.inl q)) q z).1 hzq with
    ⟨y, hyq', hyz⟩
  have hxy : x = y := by
    simpa only [project_occurrence] using
      congrArg project (hxz.trans hyz.symm)
  subst y
  exact occurrences_ne_of_allowed_intersection Z hp hq hpq hxp' hyq'
    (hxz.trans hyz.symm)

theorem initialSet_endpointLiftedPaths (Z : FracturedWarp Γ)
    (hfinite : Γ.HasFiniteCharacter Z.paths) :
    (web Γ Z).initialSet (endpointLiftedPaths Z) =
      sourceCopy Z '' Γ.initialSet Z.paths := by
  ext z
  constructor
  · rintro ⟨P, ⟨p, hp, rfl⟩, hP⟩
    refine ⟨p.start, ⟨(.inl p : Γ.DPath), hp, rfl⟩, ?_⟩
    exact (start_endpointLiftFinitePath Z p).symm.trans hP
  · rintro ⟨x, ⟨p, hp, hpx⟩, rfl⟩
    rcases hfinite hp with ⟨q, rfl⟩
    refine ⟨(.inl (endpointLiftFinitePath Z q) : (web Γ Z).DPath),
      endpointLiftFinitePath_mem_endpointLiftedPaths Z hp, ?_⟩
    change q.start = x at hpx
    exact (start_endpointLiftFinitePath Z q).trans
      (congrArg (sourceCopy Z) hpx)

theorem terminalFrontier_endpointLiftedPaths (Z : FracturedWarp Γ)
    (hfinite : Γ.HasFiniteCharacter Z.paths) :
    (web Γ Z).terminalFrontier (endpointLiftedPaths Z) =
      terminalCopy Z '' Γ.terminalFrontier Z.paths := by
  ext z
  constructor
  · rintro ⟨P, ⟨p, hp, rfl⟩, hP⟩
    refine ⟨p.finish, ⟨(.inl p : Γ.DPath), hp, rfl⟩, ?_⟩
    change some (endpointLiftFinitePath Z p).finish = some z at hP
    exact (finish_endpointLiftFinitePath Z p).symm.trans
      (Option.some.inj hP)
  · rintro ⟨x, ⟨p, hp, hpx⟩, rfl⟩
    rcases hfinite hp with ⟨q, rfl⟩
    refine ⟨(.inl (endpointLiftFinitePath Z q) : (web Γ Z).DPath),
      endpointLiftFinitePath_mem_endpointLiftedPaths Z hp, ?_⟩
    change some (endpointLiftFinitePath Z q).finish =
      some (terminalCopy Z x)
    change some q.finish = some x at hpx
    rw [finish_endpointLiftFinitePath, Option.some.inj hpx]

/-! ## Exact normalization of the endpoint-regular split family -/

/-- The auxiliary split web has precisely the endpoint-regular fractured
sources and terminals as its distinguished sides. -/
def endpointWeb (Γ : DWeb V) (Z : FracturedWarp Γ) : DWeb (Vertex V) where
  graph := (web Γ Z).graph
  source := (web Γ Z).initialSet (endpointLiftedPaths Z)
  target := (web Γ Z).terminalFrontier (endpointLiftedPaths Z)

/-- A finite member of a warp meets the warp's initial set only at its own
initial vertex. -/
theorem finite_support_inter_initialSet_of_isWarp
    {W : Set Γ.DPath} (hW : Γ.IsWarp W)
    {p : FinitePath Γ.graph} (hp : (.inl p : Γ.DPath) ∈ W) :
    p.support ∩ Γ.initialSet W ⊆ {p.start} := by
  intro x hx
  rcases hx.2 with ⟨q, hq, hqx⟩
  have hxq : x ∈ q.support := hqx ▸ q.initial_mem_support
  have hpq : (.inl p : Γ.DPath) = q := by
    by_contra hpq
    exact Set.disjoint_left.1 (hW hp hq hpq) hx.1 hxq
  subst q
  change p.start = x at hqx
  exact hqx.symm

/-- Regard a finite path as a path in the normalized graph when it has no
later source and no earlier target contact.  Its vertex list is unchanged. -/
noncomputable def normalizeExactFinitePath (Delta : DWeb V)
    (p : FinitePath Delta.graph)
    (hsource : ∀ {z}, z ∈ p.walk.support.tail → z ∉ Delta.source)
    (htarget : ∀ {z}, z ∈ p.walk.support.dropLast → z ∉ Delta.target) :
    FinitePath Delta.normalized.graph where
  start := p.start
  finish := p.finish
  walk := Delta.normalizeWalk p.walk hsource htarget
  isPath := by
    change (Delta.normalizeWalk p.walk hsource htarget).support.Nodup
    rw [Delta.support_normalizeWalk]
    exact p.isPath

@[simp] theorem support_normalizeExactFinitePath (Delta : DWeb V)
    (p : FinitePath Delta.graph)
    (hsource : ∀ {z}, z ∈ p.walk.support.tail → z ∉ Delta.source)
    (htarget : ∀ {z}, z ∈ p.walk.support.dropLast → z ∉ Delta.target) :
    (normalizeExactFinitePath Delta p hsource htarget).support = p.support := by
  unfold normalizeExactFinitePath
  ext x
  simp only [FinitePath.support, Set.mem_setOf_eq]
  rw [Delta.support_normalizeWalk p.walk hsource htarget]

theorem normalizeExactFinitePath_congr (Delta : DWeb V)
    {p q : FinitePath Delta.graph} (hpq : p = q)
    (hsourceP : ∀ {z}, z ∈ p.walk.support.tail → z ∉ Delta.source)
    (htargetP : ∀ {z}, z ∈ p.walk.support.dropLast → z ∉ Delta.target)
    (hsourceQ : ∀ {z}, z ∈ q.walk.support.tail → z ∉ Delta.source)
    (htargetQ : ∀ {z}, z ∈ q.walk.support.dropLast → z ∉ Delta.target) :
    normalizeExactFinitePath Delta p hsourceP htargetP =
      normalizeExactFinitePath Delta q hsourceQ htargetQ := by
  subst q
  rfl

/-- The endpoint-regular fractured member, now in the normalized auxiliary
split web. -/
noncomputable def normalizedEndpointLiftFinitePath
    (Z : FracturedWarp Γ) (p : FinitePath Γ.graph)
    (hp : (.inl p : Γ.DPath) ∈ Z.paths) :
    FinitePath (endpointWeb Γ Z).normalized.graph := by
  let q := endpointLiftFinitePath Z p
  have hqW : (.inl q : (web Γ Z).DPath) ∈ endpointLiftedPaths Z :=
    endpointLiftFinitePath_mem_endpointLiftedPaths Z hp
  let hs : ∀ {z}, z ∈ q.walk.support.tail →
      z ∉ (endpointWeb Γ Z).source := by
    intro z hz hzsource
    have hzq : z ∈ q.support := List.mem_of_mem_tail hz
    have hzi : z = q.start := by
      simpa [endpointWeb] using
        finite_support_inter_initialSet_of_isWarp
          (endpointLiftedPaths_isWarp Z) hqW ⟨hzq, hzsource⟩
    exact DWeb.walk_start_not_mem_tail2 q.walk q.isPath
      (hzi ▸ hz)
  let ht : ∀ {z}, z ∈ q.walk.support.dropLast →
      z ∉ (endpointWeb Γ Z).target := by
    intro z hz hztarget
    have hzq : z ∈ q.support := List.mem_of_mem_dropLast hz
    have hzt : z = q.finish := by
      simpa [endpointWeb] using
        DWeb.IsWarp.finite_support_inter_terminalFrontier
          (web Γ Z) (endpointLiftedPaths_isWarp Z) hqW
          ⟨hzq, hztarget⟩
    exact DWeb.walk_finish_not_mem_dropLast2 q.walk q.isPath
      (hzt ▸ hz)
  exact normalizeExactFinitePath (endpointWeb Γ Z) q hs ht

@[simp] theorem support_normalizedEndpointLiftFinitePath
    (Z : FracturedWarp Γ) (p : FinitePath Γ.graph)
    (hp : (.inl p : Γ.DPath) ∈ Z.paths) :
    (normalizedEndpointLiftFinitePath Z p hp).support =
      (endpointLiftFinitePath Z p).support := by
  unfold normalizedEndpointLiftFinitePath
  apply support_normalizeExactFinitePath

@[simp] theorem start_normalizedEndpointLiftFinitePath
    (Z : FracturedWarp Γ) (p : FinitePath Γ.graph)
    (hp : (.inl p : Γ.DPath) ∈ Z.paths) :
    (normalizedEndpointLiftFinitePath Z p hp).start = sourceCopy Z p.start := by
  change (endpointLiftFinitePath Z p).start = sourceCopy Z p.start
  exact start_endpointLiftFinitePath Z p

@[simp] theorem finish_normalizedEndpointLiftFinitePath
    (Z : FracturedWarp Γ) (p : FinitePath Γ.graph)
    (hp : (.inl p : Γ.DPath) ∈ Z.paths) :
    (normalizedEndpointLiftFinitePath Z p hp).finish = terminalCopy Z p.finish := by
  change (endpointLiftFinitePath Z p).finish = terminalCopy Z p.finish
  exact finish_endpointLiftFinitePath Z p

/-- The endpoint-regular fractured family in the normalized split web. -/
noncomputable def normalizedEndpointLiftedPaths (Z : FracturedWarp Γ) :
    Set (endpointWeb Γ Z).normalized.DPath :=
  {P | ∃ (p : FinitePath Γ.graph) (hp : (.inl p : Γ.DPath) ∈ Z.paths),
      P = .inl (normalizedEndpointLiftFinitePath Z p hp)}

theorem normalizedEndpointLiftedPaths_hasFiniteCharacter
    (Z : FracturedWarp Γ) :
    (endpointWeb Γ Z).normalized.HasFiniteCharacter
      (normalizedEndpointLiftedPaths Z) := by
  rintro P ⟨p, hp, rfl⟩
  exact ⟨normalizedEndpointLiftFinitePath Z p hp, rfl⟩

theorem normalizedEndpointLiftedPaths_isWarp (Z : FracturedWarp Γ) :
    (endpointWeb Γ Z).normalized.IsWarp
      (normalizedEndpointLiftedPaths Z) := by
  rintro P ⟨p, hp, rfl⟩ Q ⟨q, hq, rfl⟩ hPQ
  change Disjoint (normalizedEndpointLiftFinitePath Z p hp).support
    (normalizedEndpointLiftFinitePath Z q hq).support
  rw [support_normalizedEndpointLiftFinitePath,
    support_normalizedEndpointLiftFinitePath]
  apply endpointLiftedPaths_isWarp Z
    (endpointLiftFinitePath_mem_endpointLiftedPaths Z hp)
    (endpointLiftFinitePath_mem_endpointLiftedPaths Z hq)
  intro heq
  have heq' : endpointLiftFinitePath Z p = endpointLiftFinitePath Z q :=
    Sum.inl.inj heq
  apply hPQ
  congr 1
  unfold normalizedEndpointLiftFinitePath
  apply normalizeExactFinitePath_congr
  exact heq'

/-! ## The occurrence-aware simultaneous assignment

Projecting a split alternating path does not, in general, give a literal
alternating path in the original graph: a backward connector can contract to
a point.  In particular, an infinite split alternating path can project to a
forward ray.  We therefore retain the split path and project only its two
exposed endpoints.  This is the exact information used after Remark 4.20 in
the simultaneous construction.
-/

/-- The original (unsplit) sources which have not already been used by the
reference warp. -/
abbrev AssignmentSource (Z : FracturedWarp Γ) (Y : Set Γ.DPath) :=
  {x : V // x ∈ Γ.initialSet Z.paths \ Γ.initialSet Y}

/-- The canonical outgoing copy of an uncovered source is an uncovered
source of the two lifted families. -/
def liftedAssignmentSource (Z : FracturedWarp Γ) {Y : Set Γ.DPath}
    (hYfinite : Γ.HasFiniteCharacter Y)
    (s : AssignmentSource Z Y) :
    {z : Vertex V // z ∈
      (web Γ Z).initialSet (liftedPaths Z) \
        (web Γ Z).initialSet (liftedReference Z Y)} := by
  refine ⟨sourceCopy Z s.1, sourceCopy_mem_initialSet_liftedPaths Z s.2.1, ?_⟩
  rw [initialSet_liftedReference Z hYfinite]
  rintro ⟨x, hxY, hxs⟩
  apply s.2.2
  have : x = s.1 := sourceCopy_injective Z hxs
  simpa [this] using hxY

@[simp] theorem project_liftedAssignmentSource
    (Z : FracturedWarp Γ) {Y : Set Γ.DPath}
    (hYfinite : Γ.HasFiniteCharacter Y) (s : AssignmentSource Z Y) :
    project (liftedAssignmentSource Z hYfinite s).1 = s.1 :=
  rfl

/-- A terminal of a lifted fractured member projects to a terminal of the
corresponding original member. -/
theorem project_mem_terminalFrontier_of_mem_terminalFrontier_liftedPaths
    (Z : FracturedWarp Γ) {z : Vertex V}
    (hz : z ∈ (web Γ Z).terminalFrontier (liftedPaths Z)) :
    project z ∈ Γ.terminalFrontier Z.paths := by
  rcases hz with ⟨P, ⟨p, hpZ, rfl⟩, hterm⟩
  refine ⟨p, hpZ, ?_⟩
  have hproject := congrArg (Option.map project) hterm
  simpa only [terminal_liftPath_projected, Option.map_some] using hproject

/-- If a role-copy over `x` is outside the expanded reference warp, then
`x` itself is outside the original reference warp. -/
theorem project_not_mem_vertexSet_liftedReference
    (Z : FracturedWarp Γ) {Y : Set Γ.DPath}
    (hYfinite : Γ.HasFiniteCharacter Y) {z : Vertex V}
    (hz : z ∉ (web Γ Z).vertexSet (liftedReference Z Y)) :
    project z ∉ Γ.vertexSet Y := by
  intro hxY
  exact hz (fiber_subset_vertexSet_liftedReference Z hYfinite hxY rfl)

/-- Distinct members of a fractured warp cannot have the same finite
terminal.  A permitted meeting at that terminal would force one of the two
nontrivial members to have equal initial and terminal vertices. -/
theorem eq_of_mem_of_terminal_eq (Z : FracturedWarp Γ)
    {p q : Γ.DPath} (hp : p ∈ Z.paths) (hq : q ∈ Z.paths)
    {x : V} (hpt : Γ.terminal? p = some x)
    (hqt : Γ.terminal? q = some x) : p = q := by
  by_contra hpq
  have hxP : x ∈ p.support := Γ.terminal_mem_support hpt
  have hxQ : x ∈ q.support := Γ.terminal_mem_support hqt
  have hnotdisj : ¬ Disjoint p.support q.support := by
    rw [Set.not_disjoint_iff]
    exact ⟨x, hxP, hxQ⟩
  rcases Z.allowed_intersection hp hq hpq hnotdisj with
    ⟨hpnt, hqnt, hcase | hcase⟩
  · rcases hcase with ⟨t, hqt', hpi, _⟩
    have htx : t = x := Option.some.inj (hqt'.symm.trans hqt)
    exact (initial_ne_terminal_of_nontrivial hpnt hpt)
      (hpi.trans htx)
  · rcases hcase with ⟨t, hpt', hqi, _⟩
    have htx : t = x := Option.some.inj (hpt'.symm.trans hpt)
    exact (initial_ne_terminal_of_nontrivial hqnt hqt)
      (hqi.trans htx)

/-- Projection is injective on the finite terminal frontier of the lifted
fractured warp. -/
theorem eq_of_mem_terminalFrontier_liftedPaths_of_project_eq
    (Z : FracturedWarp Γ) {z w : Vertex V}
    (hz : z ∈ (web Γ Z).terminalFrontier (liftedPaths Z))
    (hw : w ∈ (web Γ Z).terminalFrontier (liftedPaths Z))
    (hproject : project z = project w) : z = w := by
  rcases hz with ⟨P, ⟨p, hpZ, hP⟩, hPterm⟩
  rcases hw with ⟨Q, ⟨q, hqZ, hQ⟩, hQterm⟩
  subst P
  subst Q
  have hpterm : Γ.terminal? p = some (project z) := by
    have h := congrArg (Option.map project) hPterm
    simpa only [terminal_liftPath_projected, Option.map_some] using h
  have hqterm : Γ.terminal? q = some (project z) := by
    have h := congrArg (Option.map project) hQterm
    rw [terminal_liftPath_projected, Option.map_some] at h
    simpa [hproject] using h
  have hpq : p = q := eq_of_mem_of_terminal_eq Z hpZ hqZ hpterm hqterm
  subst q
  change (liftPath Z p).terminal? = some z at hPterm
  change (liftPath Z p).terminal? = some w at hQterm
  rw [terminal_liftPath] at hPterm hQterm
  rcases hptermOpt : p.terminal? with _ | x
  · simp [hptermOpt] at hPterm
  · rw [hptermOpt] at hPterm hQterm
    simp only [Option.map_some, Option.some.injEq] at hPterm hQterm
    exact hPterm.symm.trans hQterm

/-- Remark 4.20 represented without the invalid contraction step.  The
assigned paths stay in the duplicated occurrence web; only their exposed
endpoints are projected to the original vertex type. -/
structure DuplicatedFracturedAssignment
    (Z : FracturedWarp Γ) (Y : Set Γ.DPath) where
  splitPath : AssignmentSource Z Y → AltPath (web Γ Z).graph
  projected_start : ∀ s, project (splitPath s).initial = s.1
  projected_finite_terminal : ∀ s z, (splitPath s).terminal? = some z →
    project z ∈ Γ.terminalFrontier Z.paths \ Γ.vertexSet Y
  projected_finite_terminals_injective : ∀ s₁ s₂ z₁ z₂,
    (splitPath s₁).terminal? = some z₁ →
    (splitPath s₂).terminal? = some z₂ →
    project z₁ = project z₂ → s₁ = s₂

namespace DuplicatedFracturedAssignment

variable {Z : FracturedWarp Γ} {Y : Set Γ.DPath}

/-- The split alternating path assigned to an original uncovered source. -/
noncomputable def assigned
    (A : DuplicatedFracturedAssignment Z Y)
    (_hYfinite : Γ.HasFiniteCharacter Y)
    (s : AssignmentSource Z Y) : AltPath (web Γ Z).graph :=
  A.splitPath s

/-- The projected finite endpoint, with `none` denoting an infinite split
alternating path. -/
noncomputable def endAt
    (A : DuplicatedFracturedAssignment Z Y)
    (hYfinite : Γ.HasFiniteCharacter Y)
    (s : AssignmentSource Z Y) : Option V :=
  (A.assigned hYfinite s).terminal?.map project

theorem project_initial_assigned
    (A : DuplicatedFracturedAssignment Z Y)
    (hYfinite : Γ.HasFiniteCharacter Y)
    (s : AssignmentSource Z Y) :
    project (A.assigned hYfinite s).initial = s.1 := by
  exact A.projected_start s

theorem infinite_iff_endAt_eq_none
    (A : DuplicatedFracturedAssignment Z Y)
    (hYfinite : Γ.HasFiniteCharacter Y)
    (s : AssignmentSource Z Y) :
    (A.assigned hYfinite s).IsInfinite ↔ A.endAt hYfinite s = none := by
  rw [AltPath.isInfinite_iff_terminal?_eq_none]
  simp [endAt]

theorem finite_exit_mem
    (A : DuplicatedFracturedAssignment Z Y)
    (hYfinite : Γ.HasFiniteCharacter Y)
    {s : AssignmentSource Z Y} {v : V}
    (h : A.endAt hYfinite s = some v) :
    v ∈ Γ.terminalFrontier Z.paths \ Γ.vertexSet Y := by
  simp only [endAt, Option.map_eq_some_iff] at h
  rcases h with ⟨z, hterm, rfl⟩
  exact A.projected_finite_terminal s z hterm

theorem finite_exits_injective
    (A : DuplicatedFracturedAssignment Z Y)
    (hYfinite : Γ.HasFiniteCharacter Y)
    {s₁ s₂ : AssignmentSource Z Y} {v : V}
    (h₁ : A.endAt hYfinite s₁ = some v)
    (h₂ : A.endAt hYfinite s₂ = some v) :
    s₁ = s₂ := by
  simp only [endAt, Option.map_eq_some_iff] at h₁ h₂
  rcases h₁ with ⟨z₁, hz₁, hp₁⟩
  rcases h₂ with ⟨z₂, hz₂, hp₂⟩
  exact A.projected_finite_terminals_injective s₁ s₂ z₁ z₂ hz₁ hz₂
    (hp₁.trans hp₂.symm)

end DuplicatedFracturedAssignment

/-- The source-level ordinary theorem on the duplicated occurrence web gives
the occurrence-aware fractured assignment.  No ambient source or target side
is mentioned. -/
theorem exists_duplicatedFracturedAssignment
    (Z : FracturedWarp Γ) (Y : Set Γ.DPath)
    (hordinary : SourceSimultaneousAssignmentStatement (web Γ Z))
    (hY : Γ.IsWarp Y)
    (hZfinite : Γ.HasFiniteCharacter Z.paths)
    (hYfinite : Γ.HasFiniteCharacter Y)
    (hinitial : Γ.initialSet Y ⊆ Γ.initialSet Z.paths) :
    Nonempty (DuplicatedFracturedAssignment Z Y) := by
  have hinitial' :
      (web Γ Z).initialSet (liftedReference Z Y) ⊆
        (web Γ Z).initialSet (liftedPaths Z) := by
    rw [initialSet_liftedReference Z hYfinite, initialSet_liftedPaths]
    exact Set.image_mono hinitial
  exact (hordinary (liftedPaths Z) (liftedReference Z Y)
    (liftedPaths_isWarp Z) (liftedReference_isWarp Z hY)
    (liftedPaths_hasFiniteCharacter Z hZfinite)
    (liftedReference_hasFiniteCharacter Z Y) hinitial').map
      (fun A ↦ {
        splitPath := fun s ↦
          A.assigned (liftedAssignmentSource Z hYfinite s)
        projected_start := by
          intro s
          rw [A.starts_at]
          rfl
        projected_finite_terminal := by
          intro s z hterm
          have hz := A.finite_terminal_mem
            (liftedAssignmentSource Z hYfinite s) hterm
          exact
            ⟨project_mem_terminalFrontier_of_mem_terminalFrontier_liftedPaths Z hz.1,
              project_not_mem_vertexSet_liftedReference Z hYfinite hz.2⟩
        projected_finite_terminals_injective := by
          intro s₁ s₂ z₁ z₂ hz₁ hz₂ hproject
          have hm₁ := A.finite_terminal_mem
            (liftedAssignmentSource Z hYfinite s₁) hz₁
          have hm₂ := A.finite_terminal_mem
            (liftedAssignmentSource Z hYfinite s₂) hz₂
          have hz : z₁ = z₂ :=
            eq_of_mem_terminalFrontier_liftedPaths_of_project_eq Z hm₁.1 hm₂.1
              hproject
          subst z₂
          exact congrArg Subtype.val (A.finite_terminals_injective hz₁ hz₂)
            |> fun hs ↦ Subtype.ext (sourceCopy_injective Z hs) })

/-- Endpoint purity for the source side of Remark 4.20: every source which
still needs an assignment is genuinely outside the reference warp. -/
def UncoveredSourcesOutsideReference
    (Z : FracturedWarp Γ) (Y : Set Γ.DPath) : Prop :=
  Γ.initialSet Z.paths \ Γ.initialSet Y ⊆ (Γ.vertexSet Y)ᶜ

/-- Endpoint purity for the terminal side of Remark 4.20: a fractured
terminal which touches the reference warp is already a reference terminal. -/
def TerminalContactPure
    (Z : FracturedWarp Γ) (Y : Set Γ.DPath) : Prop :=
  Γ.terminalFrontier Z.paths ∩ Γ.vertexSet Y ⊆
    Γ.terminalFrontier Y

/-- The truthful, source/target-independent fractured assignment statement.

The output deliberately stays in the occurrence-split web.  The two
endpoint-purity assumptions are the hypotheses available in Remark 4.20 and
in Assertion 9.31; they are not ambient-web side conditions. -/
def DuplicatedFracturedAssignmentStatement (Γ : DWeb V) : Prop :=
  ∀ (Z : FracturedWarp Γ) (Y : Set Γ.DPath),
    Γ.IsWarp Y →
    Γ.HasFiniteCharacter Z.paths → Γ.HasFiniteCharacter Y →
    Γ.initialSet Y ⊆ Γ.initialSet Z.paths →
    UncoveredSourcesOutsideReference Z Y →
    TerminalContactPure Z Y →
    Nonempty (DuplicatedFracturedAssignment Z Y)

/-- The ordinary source theorem, instantiated in every occurrence-split
web, proves the source/target-independent fractured statement. -/
theorem duplicatedFracturedAssignmentStatement_of_source
    (hordinary : ∀ Z : FracturedWarp Γ,
      SourceSimultaneousAssignmentStatement (web Γ Z)) :
    DuplicatedFracturedAssignmentStatement Γ := by
  intro Z Y hY hZfinite hYfinite hinitial _huncovered _hterminal
  exact exists_duplicatedFracturedAssignment Z Y (hordinary Z) hY
    hZfinite hYfinite hinitial

/-! ## The normalized-web reduction

For the exact theorem interface used in this development, normalization
makes the projection step unnecessary.  Indeed, a permitted fracture vertex
would be both the terminal of one nontrivial member and the initial vertex of
another.  The latter lies in the source side.  In a normalized web a source
vertex occurring on the former path must be its initial vertex as well,
contradicting nontriviality.
-/

/-- Under the standing normalized-web and source-side hypotheses, a
fractured warp is already an honest warp. -/
theorem paths_isWarp_of_normalized (Z : FracturedWarp Γ)
    (hΓ : Γ.IsNormalized)
    (hsource : Γ.initialSet Z.paths ⊆ Γ.source) :
    Γ.IsWarp Z.paths := by
  intro p hp q hq hpq
  change Disjoint p.support q.support
  rw [Set.disjoint_left]
  intro x hxp hxq
  exfalso
  have hnotdisj : ¬ Disjoint p.support q.support := by
    rw [Set.not_disjoint_iff]
    exact ⟨x, hxp, hxq⟩
  rcases Z.allowed_intersection hp hq hpq hnotdisj with
    ⟨hpnt, hqnt, hcase | hcase⟩
  · rcases hcase with ⟨t, hqt, hpi, _⟩
    have htA : t ∈ Γ.source := hsource ⟨p, hp, hpi⟩
    have htq : t ∈ q.support := Γ.terminal_mem_support hqt
    have htinit : t = q.initial := hΓ.eq_initial_of_mem_path q htq htA
    exact (initial_ne_terminal_of_nontrivial hqnt hqt) htinit.symm
  · rcases hcase with ⟨t, hpt, hqi, _⟩
    have htA : t ∈ Γ.source := hsource ⟨q, hq, hqi⟩
    have htp : t ∈ p.support := Γ.terminal_mem_support hpt
    have htinit : t = p.initial := hΓ.eq_initial_of_mem_path p htp htA
    exact (initial_ne_terminal_of_nontrivial hpnt hpt) htinit.symm

/-- Remark 4.20 for the exact normalized-web theorem interface.  The
ordinary simultaneous-assignment theorem applies directly, because the
preceding lemma shows that its allegedly fractured first family is already
a warp. -/
theorem fracturedSimultaneousAssignment_of_ordinary
    (hordinary : SimultaneousAssignmentStatement Γ) :
    FracturedSimultaneousAssignmentStatement Γ := by
  intro hΓ Z Y hsource htarget hY hfinZ hfinY hinitial
  exact hordinary hΓ Z.paths Y hsource htarget
    (paths_isWarp_of_normalized Z hΓ hsource) hY hfinZ hfinY hinitial

end FracturedDuplication
end Alternating
end Erdos599
