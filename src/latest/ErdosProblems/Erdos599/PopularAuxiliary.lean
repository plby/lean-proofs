/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.Alternating
import ErdosProblems.Erdos599.Popular

/-!
# The auxiliary webs in Section 8 of Aharoni--Berger

This file gives the concrete `Core`-based versions of the two auxiliary
digraphs used to turn a stationary ladder obstruction into an ordinary
hindrance.

* `theta` is the roof-restricted original web, augmented by a fresh proxy
  for every selected infinite troublesome path;
* `lambda` replaces every edge of the ladder warp by a vertex.  Its
  adjacency relation is the union of the six arc classes in Section 8.

The tags in `ThetaVertex` and `LambdaVertex` are important.  A proxy is
fresh even if the original vertex type happens to contain an equal-looking
index, and a represented ladder edge is distinct from every old vertex.
This makes the conversion literal rather than relying on disjointness side
conditions on untagged unions.
-/

noncomputable section

namespace Erdos599
namespace PopularAuxiliary

open Set
open DirectedPath

universe u v

variable {V : Type u}

/-! ## Grounded and hanging paths -/

/-- A ladder path is grounded when its genuine initial vertex lies in the
original source set. -/
def IsGroundedPath (Γ : DWeb V) (p : Γ.DPath) : Prop :=
  p.initial ∈ Γ.source

/-- A ladder path is hanging when its genuine initial vertex does not lie
in the original source set. -/
def IsHangingPath (Γ : DWeb V) (p : Γ.DPath) : Prop :=
  p.initial ∉ Γ.source

@[simp]
theorem isHangingPath_iff_not_isGroundedPath (Γ : DWeb V) (p : Γ.DPath) :
    IsHangingPath Γ p ↔ ¬ IsGroundedPath Γ p :=
  Iff.rfl

theorem grounded_or_hanging (Γ : DWeb V) (p : Γ.DPath) :
    IsGroundedPath Γ p ∨ IsHangingPath Γ p :=
  Classical.em _

theorem not_grounded_and_hanging (Γ : DWeb V) (p : Γ.DPath) :
    ¬ (IsGroundedPath Γ p ∧ IsHangingPath Γ p) :=
  fun h ↦ h.2 h.1

/-- The grounded members of a path family. -/
def groundedPaths (Γ : DWeb V) (W : Set Γ.DPath) : Set Γ.DPath :=
  {p | p ∈ W ∧ IsGroundedPath Γ p}

/-- The hanging members of a path family. -/
def hangingPaths (Γ : DWeb V) (W : Set Γ.DPath) : Set Γ.DPath :=
  {p | p ∈ W ∧ IsHangingPath Γ p}

theorem grounded_union_hanging (Γ : DWeb V) (W : Set Γ.DPath) :
    groundedPaths Γ W ∪ hangingPaths Γ W = W := by
  ext p
  constructor
  · rintro (hp | hp) <;> exact hp.1
  · intro hpW
    by_cases hp : IsGroundedPath Γ p
    · exact Or.inl ⟨hpW, hp⟩
    · exact Or.inr ⟨hpW, hp⟩

theorem disjoint_grounded_hanging (Γ : DWeb V) (W : Set Γ.DPath) :
    Disjoint (groundedPaths Γ W) (hangingPaths Γ W) := by
  rw [Set.disjoint_left]
  exact fun _ hp hq ↦ hq.2 hp.2

/-! ## Input and the web Theta -/

/-- Vertices of `Theta`: old vertices and genuinely fresh proxy vertices. -/
abbrev ThetaVertex (V : Type u) (I : Type v) := Sum V I

/-- The data needed to form the Section 8 auxiliary web.

`finiteSource` is the set of terminals of the finite troublesome paths.
`proxyPath i` is the infinite troublesome path represented by the fresh
proxy `i`.  Rayhood and the bookkeeping indices are recorded in the ladder
layer; the graph construction itself only needs the represented support.
-/
structure Input (Γ : DWeb V) (I : Type v) where
  ladder : Γ.Warp
  finiteSource : Set V
  markerSet : Set V
  proxyPath : I → Γ.DPath
  proxy_isRay : ∀ i, ∃ r : Ray Γ.graph, proxyPath i = .inr r

namespace Input

variable {Γ : DWeb V} {I : Type v} (L : Input Γ I)

/-- The essential subwarp of the limiting ladder warp. -/
def essentialLadder : Set Γ.DPath :=
  Γ.essentialWarpPart L.ladder.paths

/-- `T = ter[Ess(Y)]`. -/
def terminalCut : Set V :=
  Γ.terminalFrontier L.essentialLadder

/-- `R = RF(T)`, the roof on which the old part of `Theta` is induced. -/
def roofRegion : Set V :=
  Γ.roof L.terminalCut

/-- The target marker set retained by the essential ladder warp. -/
def targetMarkers : Set V :=
  L.markerSet ∩ Γ.vertexSet L.essentialLadder

/-- Old vertices of the roof not lying on the complete limiting ladder
warp.  These, rather than vertices merely outside the essential subwarp,
are the ordinary vertices retained by the alternating conversion. -/
def offLadder : Set V :=
  L.roofRegion \ Γ.vertexSet L.ladder.paths

/-- Edges occurring on members of the limiting ladder warp. -/
def familyEdges : Set (V × V) :=
  {e | ∃ p ∈ L.ladder.paths, e ∈ p.edgeSet}

/-- The adjacency relation of `Theta`.

There are old-to-old arcs induced by the roof, and proxy-to-old arcs
representing an outgoing original edge from any vertex of the represented
infinite path.  There are no arcs entering a proxy. -/
def ThetaAdj : ThetaVertex V I → ThetaVertex V I → Prop
  | .inl u, .inl v =>
      Γ.graph.Adj u v ∧ u ∈ L.roofRegion ∧ v ∈ L.roofRegion
  | .inr i, .inl v =>
      v ∈ L.roofRegion ∧ ∃ u ∈ (L.proxyPath i).support, Γ.graph.Adj u v
  | _, .inr _ => False

/-- The Section 8 web `Theta = (F,X,Y)`. -/
def theta : DWeb (ThetaVertex V I) where
  graph := ⟨L.ThetaAdj⟩
  source := Sum.inl '' L.finiteSource ∪ Sum.inr '' Set.univ
  target := Sum.inl '' L.targetMarkers

@[simp]
theorem theta_adj_old_old (u v : V) :
    L.theta.graph.Adj (.inl u) (.inl v) ↔
      Γ.graph.Adj u v ∧ u ∈ L.roofRegion ∧ v ∈ L.roofRegion :=
  Iff.rfl

@[simp]
theorem theta_adj_proxy_old (i : I) (v : V) :
    L.theta.graph.Adj (.inr i) (.inl v) ↔
      v ∈ L.roofRegion ∧
        ∃ u ∈ (L.proxyPath i).support, Γ.graph.Adj u v :=
  Iff.rfl

@[simp]
theorem theta_not_adj_to_proxy (z : ThetaVertex V I) (i : I) :
    ¬ L.theta.graph.Adj z (.inr i) := by
  rcases z with u | j <;> simp [theta, ThetaAdj]

@[simp]
theorem mem_theta_source_old (v : V) :
    Sum.inl v ∈ L.theta.source ↔ v ∈ L.finiteSource := by
  simp [theta]

@[simp]
theorem mem_theta_source_proxy (i : I) :
    Sum.inr i ∈ L.theta.source := by
  simp [theta]

@[simp]
theorem mem_theta_target_old (v : V) :
    Sum.inl v ∈ L.theta.target ↔ v ∈ L.targetMarkers := by
  simp [theta]

@[simp]
theorem not_mem_theta_target_proxy (i : I) :
    Sum.inr i ∉ L.theta.target := by
  simp [theta]

/-! ## The six arc classes of Lambda -/

/-- Vertices of `Lambda`: old vertices, represented ladder edges, and the
fresh proxies for selected infinite troublesome paths. -/
inductive LambdaVertex (V : Type u) (I : Type v)
  | old : V → LambdaVertex V I
  | edge : V → V → LambdaVertex V I
  | proxy : I → LambdaVertex V I
  deriving DecidableEq

/-- `E_VV`: an original edge between retained ordinary vertices. -/
def ArcVV (a b : LambdaVertex V I) : Prop :=
  ∃ u v, a = .old u ∧ b = .old v ∧
    u ∈ L.offLadder ∪ L.finiteSource ∧
    v ∈ L.offLadder ∪ L.targetMarkers ∧ Γ.graph.Adj u v

/-- `E_EV`: from the vertex representing `(u,v)` to an ordinary `q`,
using the original edge `uq`, or the zero-length join `u=q` at a change
from backward to forward travel. -/
def ArcEV (a b : LambdaVertex V I) : Prop :=
  ∃ u v q, a = .edge u v ∧ b = .old q ∧
    (u, v) ∈ L.familyEdges ∧
    (u = q ∨
      (q ∈ L.offLadder ∪ L.targetMarkers ∧ Γ.graph.Adj u q))

/-- `E_VE`: from an ordinary `q` to the vertex representing `(u,v)`,
using the original edge `qv`, or the zero-length join `q=v` at a change
from forward to backward travel. -/
def ArcVE (a b : LambdaVertex V I) : Prop :=
  ∃ q u v, a = .old q ∧ b = .edge u v ∧
    (u, v) ∈ L.familyEdges ∧
    (q = v ∨
      (q ∈ L.offLadder ∪ L.finiteSource ∧ Γ.graph.Adj q v))

/-- `E_EE`: between two represented ladder edges.

The second disjunct is `D u z`.  The occurrence of `D v w` in Remark 8.11
of version 4 of the paper is a typo; Section 4.2's inverse matching gives
`m(e)=u` and `w(f)=z`. -/
def ArcEE (a b : LambdaVertex V I) : Prop :=
  ∃ u v w z, a = .edge u v ∧ b = .edge w z ∧
    (u, v) ∈ L.familyEdges ∧ (w, z) ∈ L.familyEdges ∧
    (u = z ∨ Γ.graph.Adj u z)

/-- `E_infty,V`: a proxy uses an outgoing original edge from any vertex
of the represented infinite path. -/
def ArcInfinityV (a b : LambdaVertex V I) : Prop :=
  ∃ i v, a = .proxy i ∧ b = .old v ∧
    v ∈ L.offLadder ∪ L.targetMarkers ∧
    ∃ u ∈ (L.proxyPath i).support, Γ.graph.Adj u v

/-- `E_infty,E`: a proxy enters a represented ladder edge `(w,v)` using
an original edge from the represented path to `v`. -/
def ArcInfinityE (a b : LambdaVertex V I) : Prop :=
  ∃ i w v, a = .proxy i ∧ b = .edge w v ∧
    (w, v) ∈ L.familyEdges ∧
    ∃ u ∈ (L.proxyPath i).support, Γ.graph.Adj u v

/-- The adjacency relation of the alternating conversion is exactly the
union of the six source arc classes. -/
def LambdaAdj (a b : LambdaVertex V I) : Prop :=
  L.ArcVV a b ∨ L.ArcEV a b ∨ L.ArcVE a b ∨
    L.ArcEE a b ∨ L.ArcInfinityV a b ∨ L.ArcInfinityE a b

/-- The alternating-path conversion `Lambda_Theta(Y)`. -/
def lambda : DWeb (LambdaVertex V I) where
  graph := ⟨L.LambdaAdj⟩
  source := LambdaVertex.old '' L.finiteSource ∪
    LambdaVertex.proxy '' Set.univ
  target := LambdaVertex.old '' L.targetMarkers

theorem lambda_adj_iff (a b : LambdaVertex V I) :
    L.lambda.graph.Adj a b ↔
      L.ArcVV a b ∨ L.ArcEV a b ∨ L.ArcVE a b ∨
        L.ArcEE a b ∨ L.ArcInfinityV a b ∨ L.ArcInfinityE a b :=
  Iff.rfl

@[simp]
theorem lambda_adj_old_old (u v : V) :
    L.lambda.graph.Adj (.old u) (.old v) ↔
      u ∈ L.offLadder ∪ L.finiteSource ∧
      v ∈ L.offLadder ∪ L.targetMarkers ∧ Γ.graph.Adj u v := by
  simp only [lambda, LambdaAdj, ArcVV, ArcEV, ArcVE, ArcEE,
    ArcInfinityV, ArcInfinityE]
  aesop

@[simp]
theorem lambda_adj_edge_old (u v q : V) :
    L.lambda.graph.Adj (.edge u v) (.old q) ↔
      (u, v) ∈ L.familyEdges ∧
      (u = q ∨
        (q ∈ L.offLadder ∪ L.targetMarkers ∧ Γ.graph.Adj u q)) := by
  simp only [lambda, LambdaAdj, ArcVV, ArcEV, ArcVE, ArcEE,
    ArcInfinityV, ArcInfinityE]
  aesop

@[simp]
theorem lambda_adj_old_edge (q u v : V) :
    L.lambda.graph.Adj (.old q) (.edge u v) ↔
      (u, v) ∈ L.familyEdges ∧
      (q = v ∨
        (q ∈ L.offLadder ∪ L.finiteSource ∧ Γ.graph.Adj q v)) := by
  simp only [lambda, LambdaAdj, ArcVV, ArcEV, ArcVE, ArcEE,
    ArcInfinityV, ArcInfinityE]
  aesop

@[simp]
theorem lambda_adj_edge_edge (u v w z : V) :
    L.lambda.graph.Adj (.edge u v) (.edge w z) ↔
      (u, v) ∈ L.familyEdges ∧ (w, z) ∈ L.familyEdges ∧
        (u = z ∨ Γ.graph.Adj u z) := by
  simp only [lambda, LambdaAdj, ArcVV, ArcEV, ArcVE, ArcEE,
    ArcInfinityV, ArcInfinityE]
  aesop

@[simp]
theorem lambda_adj_proxy_old (i : I) (v : V) :
    L.lambda.graph.Adj (.proxy i) (.old v) ↔
      v ∈ L.offLadder ∪ L.targetMarkers ∧
        ∃ u ∈ (L.proxyPath i).support, Γ.graph.Adj u v := by
  simp only [lambda, LambdaAdj, ArcVV, ArcEV, ArcVE, ArcEE,
    ArcInfinityV, ArcInfinityE]
  aesop

@[simp]
theorem lambda_adj_proxy_edge (i : I) (w v : V) :
    L.lambda.graph.Adj (.proxy i) (.edge w v) ↔
      (w, v) ∈ L.familyEdges ∧
        ∃ u ∈ (L.proxyPath i).support, Γ.graph.Adj u v := by
  simp only [lambda, LambdaAdj, ArcVV, ArcEV, ArcVE, ArcEE,
    ArcInfinityV, ArcInfinityE]
  aesop

@[simp]
theorem lambda_not_adj_to_proxy (a : LambdaVertex V I) (i : I) :
    ¬ L.lambda.graph.Adj a (.proxy i) := by
  change ¬ L.LambdaAdj a (.proxy i)
  cases a <;>
    simp [LambdaAdj, ArcVV, ArcEV, ArcVE, ArcEE, ArcInfinityV, ArcInfinityE]

@[simp]
theorem mem_lambda_source_old (v : V) :
    LambdaVertex.old v ∈ L.lambda.source ↔ v ∈ L.finiteSource := by
  simp [lambda]

@[simp]
theorem mem_lambda_source_proxy (i : I) :
    LambdaVertex.proxy i ∈ L.lambda.source := by
  simp [lambda]

@[simp]
theorem not_mem_lambda_source_edge (u v : V) :
    LambdaVertex.edge u v ∉ L.lambda.source := by
  simp [lambda]

@[simp]
theorem mem_lambda_target_old (v : V) :
    LambdaVertex.old v ∈ L.lambda.target ↔ v ∈ L.targetMarkers := by
  simp [lambda]

@[simp]
theorem not_mem_lambda_target_edge (u v : V) :
    LambdaVertex.edge u v ∉ L.lambda.target := by
  simp [lambda]

@[simp]
theorem not_mem_lambda_target_proxy (i : I) :
    LambdaVertex.proxy i ∉ L.lambda.target := by
  simp [lambda]

/-! ## The ordinal indexing of Lambda (Assertion 8.12) -/

/-- The source-index map obtained from separate indices for finite
troublesome terminals and infinite-path proxies. -/
def sourceIndex {κ : Cardinal.{max u v}}
    (finiteIndex : L.finiteSource → Stationary.Below κ)
    (proxyIndex : I → Stationary.Below κ) :
    L.lambda.source → Stationary.Below κ :=
  fun x ↦ match h : x.1 with
    | .old a => finiteIndex ⟨a, by
        have hx : LambdaVertex.old a ∈ L.lambda.source := h ▸ x.2
        exact (L.mem_lambda_source_old a).1 hx⟩
    | .edge a b => False.elim <| by
        have hx : LambdaVertex.edge a b ∈ L.lambda.source := h ▸ x.2
        exact L.not_mem_lambda_source_edge a b hx
    | .proxy i => proxyIndex i

/-- The target-index embedding induced by the injective marker chronology. -/
def targetIndex {κ : Cardinal.{max u v}}
    (markerIndex : L.targetMarkers ↪ Stationary.Below κ) :
    L.lambda.target ↪ Stationary.Below κ where
  toFun y := match h : y.1 with
    | .old b => markerIndex ⟨b, by
        have hy : LambdaVertex.old b ∈ L.lambda.target := h ▸ y.2
        exact (L.mem_lambda_target_old b).1 hy⟩
    | .edge a b => False.elim <| by
        have hy : LambdaVertex.edge a b ∈ L.lambda.target := h ▸ y.2
        exact L.not_mem_lambda_target_edge a b hy
    | .proxy i => False.elim <| by
        have hy : LambdaVertex.proxy i ∈ L.lambda.target := h ▸ y.2
        exact L.not_mem_lambda_target_proxy i hy
  inj' := by
    rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
    apply Subtype.ext
    cases x with
    | old a =>
        cases y with
        | old b =>
            have hxy' :
                markerIndex ⟨a, (L.mem_lambda_target_old a).1 hx⟩ =
                  markerIndex ⟨b, (L.mem_lambda_target_old b).1 hy⟩ := hxy
            exact congrArg LambdaVertex.old
              (congrArg Subtype.val (markerIndex.injective hxy'))
        | edge c d => exact False.elim (L.not_mem_lambda_target_edge c d hy)
        | proxy j => exact False.elim (L.not_mem_lambda_target_proxy j hy)
    | edge a b => exact False.elim (L.not_mem_lambda_target_edge a b hx)
    | proxy i => exact False.elim (L.not_mem_lambda_target_proxy i hx)

/-- The two non-definitional facts supplied by ladder chronology in source
Assertions 8.12 and 7.17--7.18.  The maps themselves are fixed by the
finite-stage, proxy-stage, and marker-stage indices rather than hidden in
this structure. -/
structure IndexData (κ : Cardinal.{max u v}) where
  regular : κ.IsRegular
  uncountable : Cardinal.aleph0 < κ
  finiteIndex : L.finiteSource → Stationary.Below κ
  proxyIndex : I → Stationary.Below κ
  markerIndex : L.targetMarkers ↪ Stationary.Below κ
  sourceRange_stationary : Stationary.IsStationaryBelow κ
    (Set.range (L.sourceIndex finiteIndex proxyIndex))
  descends : ∀ (p : FinitePath L.lambda.graph)
    (hstart : p.start ∈ L.lambda.source)
    (hfinish : p.finish ∈ L.lambda.target),
    L.targetIndex markerIndex ⟨p.finish, hfinish⟩ <
      L.sourceIndex finiteIndex proxyIndex ⟨p.start, hstart⟩

/-- Assertion 8.12: the explicit Section 8 chronology data makes `Lambda`
a `κ`-unbalanced web in the sense used by the popular-separator theorem. -/
def IndexData.toKappaUnbalanced {κ : Cardinal.{max u v}}
    (J : L.IndexData κ) : Popular.KappaUnbalanced L.lambda κ where
  toKappaIndexed :=
    { regular := J.regular
      uncountable := J.uncountable
      f := L.sourceIndex J.finiteIndex J.proxyIndex
      g := L.targetIndex J.markerIndex
      f_range_stationary := J.sourceRange_stationary }
  descends := J.descends

/-! ## Fragments, escaping vertices, and elementary control assertions -/

/-- A fragment of a ladder path.  The two subset fields are the exact
representation-independent facts about a component left after deleting
some represented ladder edges. -/
structure Fragment where
  path : Γ.DPath
  parent : Γ.DPath
  parent_mem : parent ∈ L.ladder.paths
  support_subset : path.support ⊆ parent.support
  edges_subset : path.edgeSet ⊆ parent.edgeSet

namespace Fragment

/-- A fragment is grounded or hanging according to its parent ladder
path, as in the source's `Y_G/G_G` and `Y_H/G_H` notation. -/
def IsGrounded (P : L.Fragment) : Prop :=
  IsGroundedPath Γ P.parent

def IsHanging (P : L.Fragment) : Prop :=
  IsHangingPath Γ P.parent

theorem grounded_or_hanging (P : L.Fragment) :
    P.IsGrounded ∨ P.IsHanging :=
  PopularAuxiliary.grounded_or_hanging Γ P.parent

end Fragment

/-- The first represented occurrence of a forward alternating route which
semantically starts at the original vertex `x`.

An old ladder vertex is not itself a vertex of the Section 8 auxiliary web.
Consequently the first represented occurrence can be either an ordinary old
vertex outside the ladder, or the gadget for the ladder edge whose head is
reached by the first forward edge.  The index `x` is the projection back to
the unrepresented encounter on the original path. -/
def RelaxedForwardStep (x : V) : LambdaVertex V I → Prop
  | .old y =>
      y ∈ L.offLadder ∪ L.targetMarkers ∧ Γ.graph.Adj x y
  | .edge u y =>
      (u, y) ∈ L.familyEdges ∧ Γ.graph.Adj x y
  | .proxy _ => False

/-- A source-faithful escape beginning at an original vertex `x`.

The route either starts literally at `old x`, when that occurrence is
available, or at the first old/edge occurrence after one virtual forward
step out of `x`.  The latter is the situation in the source proof's path
`t₁ R t ←P q Q`: `t₁` lies on the ladder and is therefore not an
ordinary Lambda vertex. -/
structure RelaxedEscape (C : Set (LambdaVertex V I)) (x : V) where
  route : FinitePath L.lambda.graph
  start_eq : route.start = .old x ∨ L.RelaxedForwardStep x route.start
  target : route.finish ∈ L.lambda.target
  avoids : L.lambda.Avoids route C
  old_not_mem : (LambdaVertex.old x : LambdaVertex V I) ∉ C

/-- The original vertices from which a `C`-avoiding, start-relaxed
alternating path escapes to the auxiliary target.  This is `RR` in the
source proof. -/
def escapeRegion (C : Set (LambdaVertex V I)) : Set V :=
  {v | Nonempty (L.RelaxedEscape C v)}

/-- Assertion 8.13 in its literal graph form: separation rules out a
`C`-avoiding finite path from `X` to `Y`. -/
theorem no_avoiding_source_target_path {W : Type*} (web : DWeb W) (C : Set W)
    (hC : Popular.IsSeparator web C) (p : FinitePath web.graph)
    (hstart : p.start ∈ web.source) (hfinish : p.finish ∈ web.target) :
    ¬ web.Avoids p C := by
  intro hav
  have hmeet : web.Meets p C := hC p hstart hfinish
  exact (web.avoids_iff_not_meets p C).1 hav hmeet

/-- The pointwise form of Assertion 8.13. -/
theorem not_canReachTargetAvoiding_of_source
    (C : Set (LambdaVertex V I)) (hC : Popular.IsSeparator L.lambda C)
    {x : LambdaVertex V I} (hx : x ∈ L.lambda.source) :
    ¬ L.lambda.CanReachTargetAvoiding C x := by
  rintro ⟨p, hp, hav⟩
  have hstart : p.start ∈ L.lambda.source := by simpa [hp.1] using hx
  exact no_avoiding_source_target_path L.lambda C hC p hstart hp.2 hav

/-- Assertion 8.15's immediate separator consequence: a finite
troublesome terminal retained in `X \ C` cannot itself start a
`C`-avoiding escape in `Lambda`. -/
theorem finiteSource_has_no_escape
    (C : Set (LambdaVertex V I)) (hC : Popular.IsSeparator L.lambda C)
    {x : V} (hx : x ∈ L.finiteSource) :
    ¬ L.lambda.CanReachTargetAvoiding C (.old x) :=
  L.not_canReachTargetAvoiding_of_source C hC
    ((L.mem_lambda_source_old x).2 hx)

/-! ## The countable collision bound behind Assertion 8.19 -/

/-- An `S`-joined family all of whose members meet a countable set disjoint
from `S` is countable.  This is the correction needed in Assertion 8.19:
the fixed hanging ladder path can be a ray, so its support is countable,
not necessarily finite. -/
theorem joinedFamily_paths_countable_of_meets_countable
    {W : Type*} {web : DWeb W} {S R : Set W}
    (F : Popular.JoinedFamily web S) (hR : R.Countable)
    (hRS : Disjoint R S)
    (hmeet : ∀ p ∈ F.paths, ∃ x ∈ R, x ∈ p.support) :
    F.paths.Countable := by
  have hdisjoint : F.paths.PairwiseDisjoint
      (fun p : FinitePath web.graph ↦ p.support \ S) := by
    intro p hp q hq hpq
    change Disjoint (p.support \ S) (q.support \ S)
    rw [Set.disjoint_left]
    intro x hxp hxq
    have hxS : x ∈ S := F.joined hp hq hpq ⟨hxp.1, hxq.1⟩
    exact hxp.2 hxS
  have hmeetOutside : ∀ p ∈ F.paths,
      ∃ x ∈ R, x ∈ p.support \ S := by
    intro p hp
    obtain ⟨x, hxR, hxp⟩ := hmeet p hp
    refine ⟨x, hxR, hxp, ?_⟩
    exact fun hxS ↦ Set.disjoint_left.1 hRS hxR hxS
  exact FamilyTools.countable_of_pairwiseDisjoint_of_meets
    hdisjoint hR hmeetOutside

/-- Consequently the initial-index set of such a joined family is
nonstationary below a regular uncountable `κ`. -/
theorem joinedFamily_initialIndices_nonstationary_of_meets_countable
    {W : Type*} {web : DWeb W} {κ : Cardinal}
    (U : Popular.KappaIndexed web κ) {S R : Set W}
    (F : Popular.JoinedFamily web S) (hR : R.Countable)
    (hRS : Disjoint R S)
    (hmeet : ∀ p ∈ F.paths, ∃ x ∈ R, x ∈ p.support) :
    ¬ Stationary.IsStationaryBelow κ
      (Popular.initialIndicesOf U F.paths F.starts_in_source) := by
  have hpaths : F.paths.Countable :=
    joinedFamily_paths_countable_of_meets_countable F hR hRS hmeet
  let indexOf : F.paths → Stationary.Below κ := fun p ↦
    U.f ⟨p.1.start, F.starts_in_source p.2⟩
  have hindices :
      (Popular.initialIndicesOf U F.paths F.starts_in_source).Countable := by
    let _ : Countable F.paths := hpaths.to_subtype
    refine (Set.countable_range indexOf).mono ?_
    rintro a ⟨p, hp, hpa⟩
    exact ⟨⟨p, hp⟩, hpa⟩
  exact Stationary.not_isStationaryBelow_of_countable
    U.regular U.uncountable hindices

/-- Path-specialized form used after pressing down in Assertions 8.19 and
8.20.  Every finite path and every ray has countable support. -/
theorem joinedFamily_initialIndices_nonstationary_of_meets_path
    {W : Type*} {web : DWeb W} {κ : Cardinal}
    (U : Popular.KappaIndexed web κ) {S : Set W}
    (F : Popular.JoinedFamily web S) (r : DirectedPath.Path web.graph)
    (hrS : Disjoint r.support S)
    (hmeet : ∀ p ∈ F.paths, ∃ x ∈ r.support, x ∈ p.support) :
    ¬ Stationary.IsStationaryBelow κ
      (Popular.initialIndicesOf U F.paths F.starts_in_source) :=
  joinedFamily_initialIndices_nonstationary_of_meets_countable
    U F r.support_countable hrS hmeet

/-- A fragment meets the escape region when one of its old vertices can
start a `C`-avoiding escape. -/
def Fragment.MeetsEscape (C : Set (LambdaVertex V I)) (P : L.Fragment) : Prop :=
  (P.path.support ∩ L.escapeRegion C).Nonempty

/-- The discarded family `H_empty` is characterized, for the structural
part of Assertion 8.17, by having no escaping vertex.  Additional source
conditions (groundedness and the finite/infinite case split) select which
such fragments are actually discarded. -/
def Fragment.IsEscapeFree (C : Set (LambdaVertex V I)) (P : L.Fragment) : Prop :=
  ¬ Fragment.MeetsEscape L C P

/-- Assertion 8.17, in the exact form used subsequently: every fragment
meeting `RR` survives removal of the escape-free fragments. -/
theorem fragment_meeting_escape_not_escapeFree
    (C : Set (LambdaVertex V I)) (P : L.Fragment)
    (hP : Fragment.MeetsEscape L C P) :
    ¬ Fragment.IsEscapeFree L C P :=
  fun h ↦ h hP

/-! The remaining Assertions 8.18--8.22 require the popular-separator
selection lemmas, the alternating-path/path-switching correspondence, and
the recursively chosen stationary in-fans.  Their graph objects are now
typed by `Fragment`, `escapeRegion`, and the six exact arc predicates above;
they are proved in the assembly module rather than represented here by
assumption-bearing declarations. -/

end Input
end PopularAuxiliary
end Erdos599
