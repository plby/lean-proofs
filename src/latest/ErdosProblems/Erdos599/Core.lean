/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.PathTools

/-!
# Erdős Problem 599: concrete web calculus

This is the canonical concrete foundation for the Aharoni--Berger
development.  It uses the finite paths and rays from `DirectedPath.lean`;
no second path representation is introduced here.

A `DWeb V` contains a Mathlib digraph and distinguished source and target
sets.  Warps are genuinely pairwise vertex-disjoint families of finite paths
and rays.  Roofs quantify over concrete finite directed paths to the target.
The normalized deletion, quotient, and essential-part operations all retain
the original vertex type but restrict the edge relation, which makes the
path lifting maps explicit and checkable.
-/

namespace Erdos599

open Set

universe u

namespace DirectedPath

variable {V : Type u} {D E : Digraph V} {a b : V}

/-- Restrict a walk to another graph when every traversed edge is certified
using its endpoints in this walk's support.  Unlike `Path.lift`, the edge
implication need not hold globally. -/
def Walk.restrictGraphOnSupport : {a b : V} → (p : Walk D a b) →
    (∀ {x y : V}, D.Adj x y → x ∈ p.support → y ∈ p.support → E.Adj x y) →
    Walk E a b
  | _, _, .nil, _ => .nil
  | _, _, .cons e p, h =>
      .cons (h e (by simp) (by simp))
        (p.restrictGraphOnSupport fun e' hx hy ↦
          h e' (by simp [hx]) (by simp [hy]))

@[simp]
theorem Walk.support_restrictGraphOnSupport {a b : V} (p : Walk D a b)
    (h : ∀ {x y : V}, D.Adj x y →
      x ∈ p.support → y ∈ p.support → E.Adj x y) :
    (p.restrictGraphOnSupport h).support = p.support := by
  induction p with
  | nil => rfl
  | cons e p ih =>
      simp only [Walk.restrictGraphOnSupport, Walk.support_cons]
      let htail : ∀ {x y : V}, D.Adj x y →
          x ∈ p.support → y ∈ p.support → E.Adj x y :=
        fun e' hx hy ↦ h e' (by simp [hx]) (by simp [hy])
      exact congrArg (List.cons _) (ih htail)

/-- Restrict a finite path to another graph using only its own support. -/
def FinitePath.restrictGraphOnSupport (p : FinitePath D)
    (h : ∀ {x y : V}, D.Adj x y →
      x ∈ p.support → y ∈ p.support → E.Adj x y) : FinitePath E where
  start := p.start
  finish := p.finish
  walk := p.walk.restrictGraphOnSupport (fun e hx hy ↦ h e hx hy)
  isPath := by
    change (p.walk.restrictGraphOnSupport (fun e hx hy ↦ h e hx hy)).support.Nodup
    rw [Walk.support_restrictGraphOnSupport]
    exact p.isPath

@[simp]
theorem FinitePath.support_restrictGraphOnSupport (p : FinitePath D)
    (h : ∀ {x y : V}, D.Adj x y →
      x ∈ p.support → y ∈ p.support → E.Adj x y) :
    (p.restrictGraphOnSupport h).support = p.support := by
  ext x
  change x ∈ (p.walk.restrictGraphOnSupport (fun e hx hy ↦ h e hx hy)).support ↔
    x ∈ p.walk.support
  rw [Walk.support_restrictGraphOnSupport]

/-- Restrict a ray to another graph using only its own support. -/
def Ray.restrictGraphOnSupport (r : Ray D)
    (h : ∀ {x y : V}, D.Adj x y →
      x ∈ r.support → y ∈ r.support → E.Adj x y) : Ray E where
  toFun := r.toFun
  adj_succ n := h (r.adj_succ n) (r.apply_mem_support n) (r.apply_mem_support (n + 1))
  injective := r.injective

@[simp]
theorem Ray.support_restrictGraphOnSupport (r : Ray D)
    (h : ∀ {x y : V}, D.Adj x y →
      x ∈ r.support → y ∈ r.support → E.Adj x y) :
    (r.restrictGraphOnSupport h).support = r.support :=
  rfl

/-- Restrict a finite-or-infinite path to another graph using its support. -/
def Path.restrictGraphOnSupport (p : Path D)
    (h : ∀ {x y : V}, D.Adj x y →
      x ∈ p.support → y ∈ p.support → E.Adj x y) : Path E := by
  rcases p with p | r
  · exact .inl (p.restrictGraphOnSupport h)
  · exact .inr (r.restrictGraphOnSupport h)

@[simp]
theorem Path.support_restrictGraphOnSupport (p : Path D)
    (h : ∀ {x y : V}, D.Adj x y →
      x ∈ p.support → y ∈ p.support → E.Adj x y) :
    (p.restrictGraphOnSupport h).support = p.support := by
  rcases p with p | r
  · exact p.support_restrictGraphOnSupport h
  · exact r.support_restrictGraphOnSupport h

@[simp]
theorem Path.initial_restrictGraphOnSupport (p : Path D)
    (h : ∀ {x y : V}, D.Adj x y →
      x ∈ p.support → y ∈ p.support → E.Adj x y) :
    (p.restrictGraphOnSupport h).initial = p.initial := by
  rcases p with p | r <;> rfl

end DirectedPath

open DirectedPath

/-! ## Concrete webs and warps -/

/-- A directed web: a digraph together with its source and target sets. -/
structure DWeb (V : Type u) where
  graph : Digraph V
  source : Set V
  target : Set V

namespace DWeb

variable {V : Type u} (Γ : DWeb V)

/-- The concrete finite-or-infinite paths in a web. -/
abbrev DPath := DirectedPath.Path Γ.graph

/-- The support union of a family of web paths. -/
def vertexSet (W : Set Γ.DPath) : Set V :=
  {x | ∃ p ∈ W, x ∈ p.support}

/-- The initial vertices of a family of web paths. -/
def initialSet (W : Set Γ.DPath) : Set V :=
  DirectedPath.Path.initial '' W

/-- The terminal of a path, absent precisely for rays. -/
abbrev terminal? : Γ.DPath → Option V :=
  DirectedPath.Path.terminal?

/-- The terminal frontier of a family: terminals of its finite members. -/
def terminalFrontier (W : Set Γ.DPath) : Set V :=
  {x | ∃ p ∈ W, Γ.terminal? p = some x}

/-- A warp is a pairwise vertex-disjoint family of concrete paths and rays. -/
def IsWarp (W : Set Γ.DPath) : Prop :=
  W.PairwiseDisjoint DirectedPath.Path.support

/-- A warp all of whose paths are finite. -/
def HasFiniteCharacter (W : Set Γ.DPath) : Prop :=
  ∀ {p : Γ.DPath}, p ∈ W →
    ∃ q : DirectedPath.FinitePath Γ.graph, p = .inl q

/-- A bundled concrete warp. -/
structure Warp where
  paths : Set Γ.DPath
  disjoint : Γ.IsWarp paths

@[simp]
theorem mem_vertexSet {W : Set Γ.DPath} {x : V} :
    x ∈ Γ.vertexSet W ↔ ∃ p ∈ W, x ∈ p.support :=
  Iff.rfl

@[simp]
theorem mem_initialSet {W : Set Γ.DPath} {x : V} :
    x ∈ Γ.initialSet W ↔ ∃ p ∈ W, p.initial = x :=
  Set.mem_image _ _ _

@[simp]
theorem mem_terminalFrontier {W : Set Γ.DPath} {x : V} :
    x ∈ Γ.terminalFrontier W ↔
      ∃ p ∈ W, Γ.terminal? p = some x :=
  Iff.rfl

@[simp]
theorem terminal?_finite (p : DirectedPath.FinitePath Γ.graph) :
    Γ.terminal? (.inl p) = some p.finish :=
  rfl

@[simp]
theorem terminal?_ray (r : DirectedPath.Ray Γ.graph) :
    Γ.terminal? (.inr r) = none :=
  rfl

theorem terminal_mem_support {p : Γ.DPath} {x : V}
    (h : Γ.terminal? p = some x) : x ∈ p.support :=
  DirectedPath.Path.terminal_mem_support p x h

theorem IsWarp.disjoint {W : Set Γ.DPath} (hW : Γ.IsWarp W)
    {p q : Γ.DPath} (hp : p ∈ W) (hq : q ∈ W) (hpq : p ≠ q) :
    Disjoint p.support q.support :=
  hW hp hq hpq

/-- The length-zero finite path based at `x`. -/
def trivialPath (x : V) : Γ.DPath :=
  DirectedPath.Path.trivial Γ.graph x

@[simp]
theorem support_trivialPath (x : V) :
    (Γ.trivialPath x).support = ({x} : Set V) :=
  DirectedPath.Path.support_trivial Γ.graph x

@[simp]
theorem initial_trivialPath (x : V) : (Γ.trivialPath x).initial = x :=
  DirectedPath.Path.initial_trivial Γ.graph x

@[simp]
theorem terminal?_trivialPath (x : V) : Γ.terminal? (Γ.trivialPath x) = some x :=
  DirectedPath.Path.terminal?_trivial Γ.graph x

/-! ### Honest forward extension, inherited from `PathTools` -/

abbrev Extends (p q : Γ.DPath) : Prop :=
  DirectedPath.Path.Extends p q

theorem extends_refl (p : Γ.DPath) : Γ.Extends p p :=
  DirectedPath.Path.extends_refl p

theorem extends_trans {p q r : Γ.DPath}
    (hpq : Γ.Extends p q) (hqr : Γ.Extends q r) : Γ.Extends p r :=
  DirectedPath.Path.extends_trans hpq hqr

theorem extends_initial {p q : Γ.DPath} (h : Γ.Extends p q) :
    p.initial = q.initial :=
  DirectedPath.Path.extends_initial h

theorem support_mono_of_extends {p q : Γ.DPath} (h : Γ.Extends p q) :
    p.support ⊆ q.support :=
  DirectedPath.Path.support_mono_of_extends h

/-! ## Target reachability and roofs -/

/-- A finite path begins at `v` and ends in the target. -/
def IsTargetPathFrom (v : V) (p : DirectedPath.FinitePath Γ.graph) : Prop :=
  p.start = v ∧ p.finish ∈ Γ.target

/-- A finite path avoids a vertex set. -/
def Avoids (p : DirectedPath.FinitePath Γ.graph) (S : Set V) : Prop :=
  Disjoint p.support S

/-- A finite path meets a vertex set. -/
def Meets (p : DirectedPath.FinitePath Γ.graph) (S : Set V) : Prop :=
  (p.support ∩ S).Nonempty

/-- A vertex can reach the target by a finite path avoiding `S`. -/
def CanReachTargetAvoiding (S : Set V) (v : V) : Prop :=
  ∃ p : DirectedPath.FinitePath Γ.graph,
    Γ.IsTargetPathFrom v p ∧ Γ.Avoids p S

/-- Vertices from which some finite path reaches the target. -/
def reachableToTarget : Set V :=
  {v | ∃ p : DirectedPath.FinitePath Γ.graph, Γ.IsTargetPathFrom v p}

/-- The roof of `S`: every concrete finite path from the vertex to the
target meets `S`. -/
def roof (S : Set V) : Set V :=
  {v | ∀ p : DirectedPath.FinitePath Γ.graph,
    Γ.IsTargetPathFrom v p → Γ.Meets p S}

/-- The essential points of `S`. -/
def essential (S : Set V) : Set V :=
  {s | s ∈ S ∧ s ∉ Γ.roof (S \ {s})}

/-- The inessential points of `S`. -/
def inessential (S : Set V) : Set V :=
  S \ Γ.essential S

/-- The strict roof, with the essential boundary removed. -/
def strictRoof (S : Set V) : Set V :=
  Γ.roof S \ Γ.essential S

@[simp]
theorem mem_reachableToTarget_iff (v : V) :
    v ∈ Γ.reachableToTarget ↔
      ∃ p : DirectedPath.FinitePath Γ.graph, Γ.IsTargetPathFrom v p :=
  Iff.rfl

@[simp]
theorem mem_roof_iff (S : Set V) (v : V) :
    v ∈ Γ.roof S ↔
      ∀ p : DirectedPath.FinitePath Γ.graph,
        Γ.IsTargetPathFrom v p → Γ.Meets p S :=
  Iff.rfl

@[simp]
theorem mem_essential_iff (S : Set V) (s : V) :
    s ∈ Γ.essential S ↔ s ∈ S ∧ s ∉ Γ.roof (S \ {s}) :=
  Iff.rfl

@[simp]
theorem mem_strictRoof_iff (S : Set V) (v : V) :
    v ∈ Γ.strictRoof S ↔
      v ∈ Γ.roof S ∧ v ∉ Γ.essential S :=
  Iff.rfl

theorem avoids_iff_not_meets (p : DirectedPath.FinitePath Γ.graph) (S : Set V) :
    Γ.Avoids p S ↔ ¬ Γ.Meets p S := by
  simp only [Avoids, Meets, Set.not_nonempty_iff_eq_empty]
  exact Set.disjoint_iff_inter_eq_empty

theorem not_mem_roof_iff (S : Set V) (v : V) :
    v ∉ Γ.roof S ↔ Γ.CanReachTargetAvoiding S v := by
  constructor
  · intro hv
    change ¬ ∀ p : DirectedPath.FinitePath Γ.graph,
      Γ.IsTargetPathFrom v p → Γ.Meets p S at hv
    simp only [not_forall] at hv
    obtain ⟨p, hp, hmeet⟩ := hv
    exact ⟨p, hp, (Γ.avoids_iff_not_meets p S).2 hmeet⟩
  · rintro ⟨p, hp, hav⟩ hv
    exact (Γ.avoids_iff_not_meets p S).1 hav (hv p hp)

theorem target_subset_reachableToTarget : Γ.target ⊆ Γ.reachableToTarget := by
  intro b hb
  let p : DirectedPath.FinitePath Γ.graph :=
    { start := b
      finish := b
      walk := .nil
      isPath := DirectedPath.Walk.isPath_nil b }
  exact ⟨p, rfl, hb⟩

theorem subset_roof (S : Set V) : S ⊆ Γ.roof S := by
  intro v hv p hp
  exact ⟨p.start, p.start_mem_support, hp.1 ▸ hv⟩

theorem roof_mono : Monotone Γ.roof := by
  intro S T hST v hv p hp
  obtain ⟨x, hxp, hxS⟩ := hv p hp
  exact ⟨x, hxp, hST hxS⟩

theorem essential_subset (S : Set V) : Γ.essential S ⊆ S :=
  fun _ hs ↦ hs.1

theorem essential_subset_roof (S : Set V) : Γ.essential S ⊆ Γ.roof S :=
  (Γ.essential_subset S).trans (Γ.subset_roof S)

theorem strictRoof_subset_roof (S : Set V) : Γ.strictRoof S ⊆ Γ.roof S :=
  Set.sdiff_subset

theorem disjoint_strictRoof_essential (S : Set V) :
    Disjoint (Γ.strictRoof S) (Γ.essential S) :=
  Set.disjoint_sdiff_left

/-! ## Last-hit trimming and the essential roof -/

private theorem mem_walk_support_iff_start_or_mem_tail
    {a b x : V} (p : DirectedPath.Walk Γ.graph a b) :
    x ∈ p.support ↔ x = a ∨ x ∈ p.support.tail := by
  cases p <;> simp

/-- A last hit of `S` on a target path is essential. -/
theorem lastHit_mem_essential {v : V} (S : Set V)
    (p : DirectedPath.FinitePath Γ.graph) (hp : Γ.IsTargetPathFrom v p)
    (hmeet : Γ.Meets p S) :
    let L := DirectedPath.Walk.lastHit p.walk S
      ⟨hmeet.choose, hmeet.choose_spec.1, hmeet.choose_spec.2⟩
    L.startpoint ∈ Γ.essential S := by
  let hwMeet : p.walk.Meets S :=
    ⟨hmeet.choose, hmeet.choose_spec.1, hmeet.choose_spec.2⟩
  let L := DirectedPath.Walk.lastHit p.walk S hwMeet
  change L.startpoint ∈ S ∧ L.startpoint ∉ Γ.roof (S \ {L.startpoint})
  refine ⟨L.startpoint_mem, (Γ.not_mem_roof_iff _ _).2 ?_⟩
  let q : DirectedPath.FinitePath Γ.graph :=
    { start := L.startpoint
      finish := p.finish
      walk := L.walk
      isPath := L.isPath p.isPath }
  refine ⟨q, ⟨rfl, hp.2⟩, ?_⟩
  rw [Γ.avoids_iff_not_meets]
  rintro ⟨x, hxq, hxS, hxs⟩
  have hxwalk : x ∈ L.walk.support := hxq
  rcases (Γ.mem_walk_support_iff_start_or_mem_tail L.walk).1 hxwalk with rfl | hxtail
  · exact hxs rfl
  · exact L.no_mem_after hxtail hxS

/-- Trimming to the last `S`-vertex shows that the essential subset has the
same roof as `S` (Aharoni--Berger Lemma 2.14). -/
theorem roof_essential (S : Set V) :
    Γ.roof (Γ.essential S) = Γ.roof S := by
  apply Set.Subset.antisymm
  · exact Γ.roof_mono (Γ.essential_subset S)
  · intro v hv p hp
    have hmeetS := hv p hp
    let hwMeet : p.walk.Meets S :=
      ⟨hmeetS.choose, hmeetS.choose_spec.1, hmeetS.choose_spec.2⟩
    let L := DirectedPath.Walk.lastHit p.walk S hwMeet
    refine ⟨L.startpoint, ?_, Γ.lastHit_mem_essential S p hp hmeetS⟩
    exact L.support_subset L.walk.start_mem_support

/-- Roofing by a roofed set is idempotent in the needed cut sense. -/
theorem roof_cut {X S : Set V} (hXS : X ⊆ Γ.roof S) :
    Γ.roof X ⊆ Γ.roof S := by
  intro v hv p hp
  have hmeetX := hv p hp
  let hwMeet : p.walk.Meets X :=
    ⟨hmeetX.choose, hmeetX.choose_spec.1, hmeetX.choose_spec.2⟩
  let L := DirectedPath.Walk.lastHit p.walk X hwMeet
  let q : DirectedPath.FinitePath Γ.graph :=
    { start := L.startpoint
      finish := p.finish
      walk := L.walk
      isPath := L.isPath p.isPath }
  have hq : Γ.IsTargetPathFrom L.startpoint q := ⟨rfl, hp.2⟩
  obtain ⟨s, hsq, hsS⟩ := hXS L.startpoint_mem q hq
  exact ⟨s, L.support_subset hsq, hsS⟩

/-! ## Essential trimming of a warp -/

/-- Keep the finite members whose terminals lie in the essential terminal
frontier.  Rays are necessarily discarded. -/
def essentialWarpPart (W : Set Γ.DPath) : Set Γ.DPath :=
  {p | p ∈ W ∧ ∃ t,
    Γ.terminal? p = some t ∧ t ∈ Γ.essential (Γ.terminalFrontier W)}

theorem terminalFrontier_essentialWarpPart (W : Set Γ.DPath) :
    Γ.terminalFrontier (Γ.essentialWarpPart W) =
      Γ.essential (Γ.terminalFrontier W) := by
  ext x
  constructor
  · rintro ⟨p, ⟨hp, t, hpt, ht⟩, hpx⟩
    have htx : t = x := Option.some.inj (hpt.symm.trans hpx)
    exact htx ▸ ht
  · intro hx
    obtain ⟨p, hp, hpx⟩ := hx.1
    exact ⟨p, ⟨hp, x, hpx, hx⟩, hpx⟩

theorem IsWarp.essentialWarpPart {W : Set Γ.DPath} (hW : Γ.IsWarp W) :
    Γ.IsWarp (Γ.essentialWarpPart W) := by
  intro p hp q hq hpq
  exact hW hp.1 hq.1 hpq

/-! ## Graph restriction, deletion, quotient, and essential part -/

/-- The induced digraph on `R`, kept on the original vertex type. -/
def inducedGraph (D : Digraph V) (R : Set V) : Digraph V where
  Adj u v := D.Adj u v ∧ u ∈ R ∧ v ∈ R

/-- Delete a set of vertices. -/
def delete (X : Set V) : DWeb V where
  graph := inducedGraph Γ.graph Xᶜ
  source := Γ.source \ X
  target := Γ.target \ X

/-- The quotient graph deletes the strict roof and every arc entering the
commitment set `X`. -/
def quotientGraph (X : Set V) : Digraph V where
  Adj u v := Γ.graph.Adj u v ∧
    u ∉ Γ.strictRoof X ∧ v ∉ Γ.strictRoof X ∧ v ∉ X

/-- The normalized quotient by `X`.  Its new source is the essential part
of the old source together with `X`; its target remains the old target. -/
def quotient (X : Set V) : DWeb V where
  graph := Γ.quotientGraph X
  source := Γ.essential (Γ.source ∪ X)
  target := Γ.target

/-- The essential part deletes every vertex from which the target is
unreachable, not merely unreachable sources. -/
def essentialPart : DWeb V where
  graph := inducedGraph Γ.graph Γ.reachableToTarget
  source := Γ.source ∩ Γ.reachableToTarget
  target := Γ.target

@[simp] theorem delete_source (X : Set V) : (Γ.delete X).source = Γ.source \ X := rfl
@[simp] theorem delete_target (X : Set V) : (Γ.delete X).target = Γ.target \ X := rfl
@[simp] theorem quotient_source (X : Set V) :
    (Γ.quotient X).source = Γ.essential (Γ.source ∪ X) := rfl
@[simp] theorem quotient_target (X : Set V) : (Γ.quotient X).target = Γ.target := rfl
@[simp] theorem essentialPart_source :
    Γ.essentialPart.source = Γ.source ∩ Γ.reachableToTarget := rfl
@[simp] theorem essentialPart_target : Γ.essentialPart.target = Γ.target := rfl

theorem delete_adj_imp {X : Set V} {u v : V} :
    (Γ.delete X).graph.Adj u v → Γ.graph.Adj u v :=
  fun h ↦ h.1

theorem quotient_adj_imp {X : Set V} {u v : V} :
    (Γ.quotient X).graph.Adj u v → Γ.graph.Adj u v :=
  fun h ↦ h.1

theorem essentialPart_adj_imp {u v : V} :
    Γ.essentialPart.graph.Adj u v → Γ.graph.Adj u v :=
  fun h ↦ h.1

/-- Lift a path in a deleted web back to the original web. -/
def liftDeletePath (X : Set V) (p : (Γ.delete X).DPath) : Γ.DPath :=
  DirectedPath.Path.lift (D := (Γ.delete X).graph) (E := Γ.graph)
    (fun {u v} h ↦ Γ.delete_adj_imp (X := X) (u := u) (v := v) h) p

/-- Lift a quotient path back to the original web. -/
def liftQuotientPath (X : Set V) (p : (Γ.quotient X).DPath) : Γ.DPath :=
  DirectedPath.Path.lift (D := (Γ.quotient X).graph) (E := Γ.graph)
    (fun {u v} h ↦ Γ.quotient_adj_imp (X := X) (u := u) (v := v) h) p

/-- Lift a path in the essential part back to the original web. -/
def liftEssentialPartPath (p : Γ.essentialPart.DPath) : Γ.DPath :=
  DirectedPath.Path.lift (D := Γ.essentialPart.graph) (E := Γ.graph)
    (fun {u v} h ↦ Γ.essentialPart_adj_imp (u := u) (v := v) h) p

@[simp] theorem support_liftDeletePath (X : Set V) (p : (Γ.delete X).DPath) :
    (Γ.liftDeletePath X p).support = p.support := by
  exact DirectedPath.Path.support_lift _ p

@[simp] theorem support_liftQuotientPath (X : Set V) (p : (Γ.quotient X).DPath) :
    (Γ.liftQuotientPath X p).support = p.support := by
  exact DirectedPath.Path.support_lift _ p

@[simp] theorem support_liftEssentialPartPath (p : Γ.essentialPart.DPath) :
    (Γ.liftEssentialPartPath p).support = p.support := by
  exact DirectedPath.Path.support_lift _ p

@[simp] theorem initial_liftDeletePath (X : Set V) (p : (Γ.delete X).DPath) :
    (Γ.liftDeletePath X p).initial = p.initial := by
  rcases p with p | r <;> rfl

@[simp] theorem initial_liftQuotientPath (X : Set V) (p : (Γ.quotient X).DPath) :
    (Γ.liftQuotientPath X p).initial = p.initial := by
  rcases p with p | r <;> rfl

private theorem deleteWalk_avoids {X : Set V} {a b : V}
    (p : DirectedPath.Walk (Γ.delete X).graph a b) (ha : a ∉ X) :
    ∀ {x : V}, x ∈ p.support → x ∉ X := by
  induction p with
  | nil => simpa using ha
  | @cons u v w e p ih =>
      intro x hx
      simp only [DirectedPath.Walk.support_cons, List.mem_cons] at hx
      exact hx.elim (fun h ↦ h ▸ e.2.1) (ih e.2.2)

/-- A path in a deleted web whose initial vertex is retained avoids every
deleted vertex.  The initial-vertex hypothesis is necessary because the
same-type representation still admits a formal length-zero path at a
deleted vertex. -/
theorem liftDeletePath_avoids (X : Set V) (p : (Γ.delete X).DPath)
    (hinitial : p.initial ∉ X) :
    Disjoint (Γ.liftDeletePath X p).support X := by
  rw [Γ.support_liftDeletePath]
  apply Set.disjoint_left.2
  intro x hxp hxX
  rcases p with p | r
  · exact Γ.deleteWalk_avoids p.walk hinitial hxp hxX
  · obtain ⟨n, rfl⟩ := hxp
    exact (r.adj_succ n).2.1 hxX

/-! ### Restricting original paths to the transformed webs -/

/-- Restrict an original path to a vertex-deleted web when every support
vertex is retained. -/
def restrictDeletePath (X : Set V) (p : Γ.DPath)
    (hretain : p.support ⊆ Xᶜ) : (Γ.delete X).DPath :=
  p.restrictGraphOnSupport fun e hu hv ↦ ⟨e, hretain hu, hretain hv⟩

@[simp]
theorem support_restrictDeletePath (X : Set V) (p : Γ.DPath)
    (hretain : p.support ⊆ Xᶜ) :
    (Γ.restrictDeletePath X p hretain).support = p.support := by
  unfold restrictDeletePath
  exact DirectedPath.Path.support_restrictGraphOnSupport
    (D := Γ.graph) (E := (Γ.delete X).graph) p
    (fun e hu hv ↦ ⟨e, hretain hu, hretain hv⟩)

@[simp]
theorem initial_restrictDeletePath (X : Set V) (p : Γ.DPath)
    (hretain : p.support ⊆ Xᶜ) :
    (Γ.restrictDeletePath X p hretain).initial = p.initial := by
  unfold restrictDeletePath
  exact DirectedPath.Path.initial_restrictGraphOnSupport
    (D := Γ.graph) (E := (Γ.delete X).graph) p
    (fun e hu hv ↦ ⟨e, hretain hu, hretain hv⟩)

/-- Restrict a path to the essential part when every support vertex can
still reach the target. -/
def restrictEssentialPartPath (p : Γ.DPath)
    (hreach : p.support ⊆ Γ.reachableToTarget) : Γ.essentialPart.DPath :=
  p.restrictGraphOnSupport fun e hu hv ↦ ⟨e, hreach hu, hreach hv⟩

@[simp]
theorem support_restrictEssentialPartPath (p : Γ.DPath)
    (hreach : p.support ⊆ Γ.reachableToTarget) :
    (Γ.restrictEssentialPartPath p hreach).support = p.support := by
  unfold restrictEssentialPartPath
  exact DirectedPath.Path.support_restrictGraphOnSupport
    (D := Γ.graph) (E := Γ.essentialPart.graph) p
    (fun e hu hv ↦ ⟨e, hreach hu, hreach hv⟩)

/-- A sufficient, entirely concrete condition for a path to survive the
quotient by `X`: its support avoids the strict roof, and every original arc
between support vertices has its head outside `X`.  The latter is stronger
than necessary but makes restriction independent of the path constructor. -/
def QuotientAdmissible (X : Set V) (p : Γ.DPath) : Prop :=
  Disjoint p.support (Γ.strictRoof X) ∧
    ∀ {u v : V}, Γ.graph.Adj u v → u ∈ p.support → v ∈ p.support → v ∉ X

/-- Restrict a quotient-admissible original path to the quotient graph. -/
def restrictQuotientPath (X : Set V) (p : Γ.DPath)
    (h : Γ.QuotientAdmissible X p) : (Γ.quotient X).DPath :=
  p.restrictGraphOnSupport fun e hu hv ↦
    ⟨e, Set.disjoint_left.1 h.1 hu, Set.disjoint_left.1 h.1 hv, h.2 e hu hv⟩

@[simp]
theorem support_restrictQuotientPath (X : Set V) (p : Γ.DPath)
    (h : Γ.QuotientAdmissible X p) :
    (Γ.restrictQuotientPath X p h).support = p.support := by
  unfold restrictQuotientPath
  exact DirectedPath.Path.support_restrictGraphOnSupport
    (D := Γ.graph) (E := (Γ.quotient X).graph) p
    (fun e hu hv ↦
      ⟨e, Set.disjoint_left.1 h.1 hu, Set.disjoint_left.1 h.1 hv, h.2 e hu hv⟩)

@[simp]
theorem initial_restrictQuotientPath (X : Set V) (p : Γ.DPath)
    (h : Γ.QuotientAdmissible X p) :
    (Γ.restrictQuotientPath X p h).initial = p.initial := by
  unfold restrictQuotientPath
  exact DirectedPath.Path.initial_restrictGraphOnSupport
    (D := Γ.graph) (E := (Γ.quotient X).graph) p
    (fun e hu hv ↦
      ⟨e, Set.disjoint_left.1 h.1 hu, Set.disjoint_left.1 h.1 hv, h.2 e hu hv⟩)

end DWeb

end Erdos599
