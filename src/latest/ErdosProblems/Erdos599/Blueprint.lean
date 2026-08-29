/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.Alternating
import ErdosProblems.Erdos599.WarpLimits
import Mathlib.Order.Zorn
import Mathlib.SetTheory.Cardinal.Regular

/-!
# Hammocks and linkage blueprints

This file formalizes the definitions in Section 9 of Aharoni--Berger's
proof of the infinite Menger theorem.  In particular, the graph obtained by
adjoining imaginary edges is an actual `Digraph`, and a linkage blueprint is
an actual warp in that graph.  The six conditions imposed on a blueprint are
kept in the separate predicate `IsLinkageBlueprint`; they are not assumptions
hidden in the data type.

The deep existence assertions 9.22--9.34 are represented below by their exact
conclusion predicates.  This file proves the structural facts about those
predicates which follow from the definitions.  Existence of the witnesses is
left to the later cardinal-induction argument rather than being postulated as
a field or primitive declaration.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace Blueprint

open DirectedPath
open Alternating

universe u v

variable {V : Type u}

/-! ## Hammocks -/

/-- The endpoints which may be shared by members of a hammock.  For a
`(u, infinity)` hammock only the initial vertex is shared. -/
def hammockEndpoints (u : V) : AltEnd V → Set V
  | .vertex v => {u, v}
  | .infinity => {u}

/-- The internal vertices of an alternating path relative to its prescribed
hammock endpoints. -/
def hammockInterior {D : Digraph V} (u : V) (e : AltEnd V)
    (Q : AltPath D) : Set V :=
  Q.vertexSet \ hammockEndpoints u e

/-- Aharoni--Berger Definition 9.20.  A hammock is a family of safe
alternating paths with common prescribed endpoints and pairwise disjoint
interiors.  Its eligibility with respect to a ladder slice is recorded by
`HammockEligible` below, rather than mixed into this intrinsic definition. -/
def Hammock (Γ : DWeb V) (Y : Set Γ.DPath) (u : V) (e : AltEnd V)
    (H : Set (AltPath Γ.graph)) : Prop :=
  (∀ Q ∈ H, IsSafe Y Q ∧ Q.initial = u ∧ HasEnd Q e) ∧
    H.PairwiseDisjoint (hammockInterior u e)

theorem hammock_empty (Γ : DWeb V) (Y : Set Γ.DPath) (u : V)
    (e : AltEnd V) : Hammock Γ Y u e ∅ := by
  constructor <;> simp

theorem Hammock.subset {Γ : DWeb V} {Y : Set Γ.DPath} {u : V}
    {e : AltEnd V} {H K : Set (AltPath Γ.graph)}
    (hH : Hammock Γ Y u e H) (hKH : K ⊆ H) :
    Hammock Γ Y u e K := by
  refine ⟨fun Q hQ ↦ hH.1 Q (hKH hQ), hH.2.subset hKH⟩

/-- The source/endpoint location requirements in Definition 9.20.
`innerRoof` is `RF°(T_α)` and `roof` is `RF(T_α)`. -/
def HammockEligible (ZBefore innerRoof roof : Set V) (u : V)
    (e : AltEnd V) : Prop :=
  u ∈ ZBefore ∩ innerRoof ∧
    match e with
    | .vertex v => v ∈ ZBefore ∩ roof
    | .infinity => True

/-- A hammock of exactly the specified cardinality. -/
def HasHammockCard (Γ : DWeb V) (Y : Set Γ.DPath) (u : V)
    (e : AltEnd V) (κ : Cardinal.{u}) : Prop :=
  ∃ H : Set (AltPath Γ.graph), Hammock Γ Y u e H ∧ #H = κ

/-- A hammock all of whose members are nondegenerate in the sense of
Definition 4.10. -/
def NondegenerateHammock (Γ : DWeb V) (Y : Set Γ.DPath) (u : V)
    (e : AltEnd V) (H : Set (AltPath Γ.graph)) : Prop :=
  Hammock Γ Y u e H ∧ ∀ Q ∈ H, ¬IsDegenerate Y Q e

/-- A nondegenerate hammock of exactly the specified cardinality. -/
def HasNondegenerateHammockCard (Γ : DWeb V) (Y : Set Γ.DPath)
    (u : V) (e : AltEnd V) (κ : Cardinal.{u}) : Prop :=
  ∃ H : Set (AltPath Γ.graph),
    NondegenerateHammock Γ Y u e H ∧ #H = κ

/-- The vertices used by a hammock. -/
def hammockVertexSet {D : Digraph V} (H : Set (AltPath D)) : Set V :=
  ⋃ Q ∈ H, Q.vertexSet

/-- A hammock is contained in a closing-up set. -/
def HammockContained {D : Digraph V} (H : Set (AltPath D))
    (Z : Set V) : Prop :=
  hammockVertexSet H ⊆ Z

theorem HammockContained.mono {D : Digraph V} {H : Set (AltPath D)}
    {Z Z' : Set V} (hHZ : HammockContained H Z) (hZZ' : Z ⊆ Z') :
    HammockContained H Z' :=
  hHZ.trans hZZ'

/-! ### Maximal up to a cardinal -/

/-- Definition 9.21.  The second branch deliberately mentions a possibly
different hammock of size `ρ⁺`; it does not assert that `H` has that size. -/
def MaximalUpTo {X : Type v} (Good : Set (Set X)) (ρ : Cardinal.{v})
    (H : Set X) : Prop :=
  (H ∈ Good ∧ Maximal (fun K ↦ K ∈ Good) H ∧ #H ≤ ρ) ∨
    (H ∈ Good ∧ #H = ρ ∧ ∃ K ∈ Good, #K = succ ρ)

theorem MaximalUpTo.mem {X : Type v} {Good : Set (Set X)}
    {ρ : Cardinal.{v}} {H : Set X} (hH : MaximalUpTo Good ρ H) :
    H ∈ Good := by
  rcases hH with hH | hH <;> exact hH.1

theorem MaximalUpTo.card_le {X : Type v} {Good : Set (Set X)}
    {ρ : Cardinal.{v}} {H : Set X} (hH : MaximalUpTo Good ρ H) :
    #H ≤ ρ := by
  rcases hH with hH | hH
  · exact hH.2.2
  · exact hH.2.1.le

theorem maximalUpTo_of_maximal {X : Type v} {Good : Set (Set X)}
    {ρ : Cardinal.{v}} {H : Set X} (hgood : H ∈ Good)
    (hmax : Maximal (fun K ↦ K ∈ Good) H) (hcard : #H ≤ ρ) :
    MaximalUpTo Good ρ H :=
  Or.inl ⟨hgood, hmax, hcard⟩

theorem maximalUpTo_of_large {X : Type v} {Good : Set (Set X)}
    {ρ : Cardinal.{v}} {H K : Set X} (hgood : H ∈ Good)
    (hcard : #H = ρ) (hKgood : K ∈ Good) (hKcard : #K = succ ρ) :
    MaximalUpTo Good ρ H :=
  Or.inr ⟨hgood, hcard, K, hKgood, hKcard⟩

theorem MaximalUpTo.maximal_of_no_large {X : Type v}
    {Good : Set (Set X)} {ρ : Cardinal.{v}} {H : Set X}
    (hH : MaximalUpTo Good ρ H)
    (hlarge : ∀ K ∈ Good, #K ≠ succ ρ) :
    Maximal (fun K ↦ K ∈ Good) H := by
  rcases hH with hH | hH
  · exact hH.2.1
  · exact (hlarge hH.2.2.choose hH.2.2.choose_spec.1
      hH.2.2.choose_spec.2).elim

theorem MaximalUpTo.maximal_of_card_lt {X : Type v}
    {Good : Set (Set X)} {ρ : Cardinal.{v}} {H : Set X}
    (hH : MaximalUpTo Good ρ H) (hcard : #H < ρ) :
    Maximal (fun K ↦ K ∈ Good) H := by
  rcases hH with hH | hH
  · exact hH.2.1
  · exact (hcard.ne hH.2.1).elim

/-- The collection to which Definition 9.21 is applied for hammocks. -/
def hammockFamilies (Γ : DWeb V) (Y : Set Γ.DPath) (u : V)
    (e : AltEnd V) : Set (Set (AltPath Γ.graph)) :=
  {H | Hammock Γ Y u e H}

/-- Unions of inclusion-chains of hammocks are hammocks. -/
theorem hammock_sUnion_of_chain {Γ : DWeb V} {Y : Set Γ.DPath}
    {u : V} {e : AltEnd V} {c : Set (Set (AltPath Γ.graph))}
    (hcsub : c ⊆ hammockFamilies Γ Y u e)
    (hc : IsChain (· ⊆ ·) c) :
    Hammock Γ Y u e (⋃₀ c) := by
  constructor
  · intro Q hQ
    obtain ⟨H, hHc, hQH⟩ := Set.mem_sUnion.1 hQ
    exact (hcsub hHc).1 Q hQH
  · intro Q hQ R hR hQR
    obtain ⟨HQ, hHQc, hQHQ⟩ := Set.mem_sUnion.1 hQ
    obtain ⟨HR, hHRc, hRHR⟩ := Set.mem_sUnion.1 hR
    by_cases hsame : HQ = HR
    · subst HR
      exact (hcsub hHQc).2 hQHQ hRHR hQR
    · rcases hc hHQc hHRc hsame with hHQHR | hHRHQ
      · exact (hcsub hHRc).2 (hHQHR hQHQ) hRHR hQR
      · exact (hcsub hHQc).2 hQHQ (hHRHQ hRHR) hQR

/-- Every endpoint pair has an inclusion-maximal hammock.  This is the Zorn
part of the closing-up assertion; the cardinal truncation in Definition 9.21
is handled separately. -/
theorem exists_maximal_hammock (Γ : DWeb V) (Y : Set Γ.DPath)
    (u : V) (e : AltEnd V) :
    ∃ H : Set (AltPath Γ.graph),
      Maximal (fun K ↦ Hammock Γ Y u e K) H := by
  apply zorn_subset
  intro c hcsub hc
  by_cases hcne : c.Nonempty
  · exact ⟨⋃₀ c, hammock_sUnion_of_chain hcsub hc,
      fun H hHc ↦ Set.subset_sUnion_of_mem hHc⟩
  · have hcempty : c = ∅ := Set.not_nonempty_iff_eq_empty.mp hcne
    exact ⟨∅, hammock_empty Γ Y u e, by simp [hcempty]⟩

/-- A hammock maximal up to `ρ`. -/
def HammockMaximalUpTo (Γ : DWeb V) (Y : Set Γ.DPath) (u : V)
    (e : AltEnd V) (ρ : Cardinal.{u}) (H : Set (AltPath Γ.graph)) : Prop :=
  MaximalUpTo (hammockFamilies Γ Y u e) ρ H

theorem HammockMaximalUpTo.isHammock {Γ : DWeb V} {Y : Set Γ.DPath}
    {u : V} {e : AltEnd V} {ρ : Cardinal.{u}}
    {H : Set (AltPath Γ.graph)} (hH : HammockMaximalUpTo Γ Y u e ρ H) :
    Hammock Γ Y u e H :=
  MaximalUpTo.mem hH

theorem HammockMaximalUpTo.card_le {Γ : DWeb V} {Y : Set Γ.DPath}
    {u : V} {e : AltEnd V} {ρ : Cardinal.{u}}
    {H : Set (AltPath Γ.graph)} (hH : HammockMaximalUpTo Γ Y u e ρ H) :
    #H ≤ ρ :=
  MaximalUpTo.card_le hH

/-! ## Imaginary edges and popularity -/

/-- An imaginary edge is witnessed by a hammock of size `κ⁺`. -/
def IsImaginaryEdge (Γ : DWeb V) (Y : Set Γ.DPath) (κ : Cardinal.{u})
    (u v : V) : Prop :=
  HasHammockCard Γ Y u (.vertex v) (succ κ)

/-- A strong imaginary edge has a size-`κ⁺` hammock consisting entirely
of nondegenerate safe alternating paths. -/
def IsStrongImaginaryEdge (Γ : DWeb V) (Y : Set Γ.DPath)
    (κ : Cardinal.{u}) (u v : V) : Prop :=
  HasNondegenerateHammockCard Γ Y u (.vertex v) (succ κ)

/-- A weak imaginary edge is imaginary but not strong. -/
def IsWeakImaginaryEdge (Γ : DWeb V) (Y : Set Γ.DPath)
    (κ : Cardinal.{u}) (u v : V) : Prop :=
  IsImaginaryEdge Γ Y κ u v ∧ ¬IsStrongImaginaryEdge Γ Y κ u v

theorem IsStrongImaginaryEdge.isImaginary {Γ : DWeb V} {Y : Set Γ.DPath}
    {κ : Cardinal.{u}} {u v : V}
    (h : IsStrongImaginaryEdge Γ Y κ u v) :
    IsImaginaryEdge Γ Y κ u v := by
  rcases h with ⟨H, ⟨hH, _hnondeg⟩, hcard⟩
  exact ⟨H, hH, hcard⟩

/-- Popularity in Definition 9.26.  The distinguished set is
`T_{κ⁺}`. -/
def IsPopular (Γ : DWeb V) (Y : Set Γ.DPath) (persistent : Set V)
    (κ : Cardinal.{u}) (u : V) : Prop :=
  u ∈ persistent ∨ HasHammockCard Γ Y u .infinity (succ κ)

/-- The graph `D' = D ∪ IE`. -/
def imaginaryGraph (Γ : DWeb V) (Y : Set Γ.DPath)
    (κ : Cardinal.{u}) : Digraph V where
  Adj u v := Γ.graph.Adj u v ∨ IsImaginaryEdge Γ Y κ u v

/-- Type-style alias used by the cardinal-induction layer. -/
abbrev ImaginaryGraph (Γ : DWeb V) (Y : Set Γ.DPath)
    (κ : Cardinal.{u}) : Digraph V :=
  imaginaryGraph Γ Y κ

/-- The web carried by the imaginary-edge augmentation. -/
def imaginaryWeb (Γ : DWeb V) (Y : Set Γ.DPath)
    (κ : Cardinal.{u}) : DWeb V where
  graph := imaginaryGraph Γ Y κ
  source := Γ.source
  target := Γ.target

theorem original_adj_imaginaryGraph {Γ : DWeb V} {Y : Set Γ.DPath}
    {κ : Cardinal.{u}} {u v : V} (h : Γ.graph.Adj u v) :
    (imaginaryGraph Γ Y κ).Adj u v :=
  Or.inl h

/-! ## Blueprint data and its six defining conditions -/

/-- Actual blueprint data: a pairwise vertex-disjoint path family in the
imaginary-edge augmentation. -/
structure LinkageBlueprint (Γ : DWeb V) (Y : Set Γ.DPath)
    (κ : Cardinal.{u}) where
  paths : Set (DirectedPath.Path (imaginaryGraph Γ Y κ))
  isWarp : (imaginaryWeb Γ Y κ).IsWarp paths

namespace LinkageBlueprint

variable {Γ : DWeb V} {Y : Set Γ.DPath} {κ : Cardinal.{u}}

private theorem walk_exists_outgoing_of_mem_support_of_ne_finish
    {D : Digraph V} : ∀ {a b x : V} (p : DirectedPath.Walk D a b),
      x ∈ p.support → x ≠ b → ∃ y, (x, y) ∈ p.edgeSet
  | a, _, x, .nil, hx, hne => by
      have : x = a := by simpa using hx
      exact (hne this).elim
  | a, b, x, .cons (v := c) edge p, hx, hne => by
      simp only [DirectedPath.Walk.support_cons, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact ⟨c, by simp⟩
      · obtain ⟨y, hy⟩ :=
          walk_exists_outgoing_of_mem_support_of_ne_finish p hx hne
        exact ⟨y, by simp [hy]⟩

private theorem path_exists_outgoing_of_mem_support_of_not_terminal
    {D : Digraph V} (p : DirectedPath.Path D) {x : V}
    (hx : x ∈ p.support)
    (hterm : p.terminal? ≠ some x) :
    ∃ y, (x, y) ∈ p.edgeSet := by
  rcases p with p | r
  · have hne : x ≠ p.finish := by
      intro h
      exact hterm (by simp [h])
    exact walk_exists_outgoing_of_mem_support_of_ne_finish p.walk hx hne
  · obtain ⟨n, hn⟩ := hx
    refine ⟨r (n + 1), ?_⟩
    exact ⟨n, congrArg (fun z ↦ (z, r (n + 1))) hn.symm⟩

def vertexSet (W : LinkageBlueprint Γ Y κ) : Set V :=
  (imaginaryWeb Γ Y κ).vertexSet W.paths

def initialSet (W : LinkageBlueprint Γ Y κ) : Set V :=
  (imaginaryWeb Γ Y κ).initialSet W.paths

def terminalSet (W : LinkageBlueprint Γ Y κ) : Set V :=
  (imaginaryWeb Γ Y κ).terminalFrontier W.paths

def edgeSet (W : LinkageBlueprint Γ Y κ) : Set (V × V) :=
  ⋃ p ∈ W.paths, p.edgeSet

@[simp] theorem mem_vertexSet {W : LinkageBlueprint Γ Y κ} {x : V} :
    x ∈ W.vertexSet ↔ ∃ p ∈ W.paths, x ∈ p.support :=
  Iff.rfl

@[simp] theorem mem_initialSet {W : LinkageBlueprint Γ Y κ} {x : V} :
    x ∈ W.initialSet ↔ ∃ p ∈ W.paths, p.initial = x :=
  Set.mem_image _ _ _

@[simp] theorem mem_terminalSet {W : LinkageBlueprint Γ Y κ} {x : V} :
    x ∈ W.terminalSet ↔
      ∃ p ∈ W.paths, (imaginaryWeb Γ Y κ).terminal? p = some x :=
  Iff.rfl

/-- The warp condition makes the member through a given vertex unique. -/
theorem path_eq_of_mem_support
    (W : LinkageBlueprint Γ Y κ)
    {p q : DirectedPath.Path (imaginaryGraph Γ Y κ)} {u : V}
    (hp : p ∈ W.paths) (hq : q ∈ W.paths)
    (hup : u ∈ p.support) (huq : u ∈ q.support) : p = q := by
  by_contra hpq
  have hd := W.isWarp hp hq hpq
  exact (Set.disjoint_left.1 hd hup huq).elim

/-- Members of a blueprint which start in `X`. -/
def restrictInitial (W : LinkageBlueprint Γ Y κ) (X : Set V) :
    Set (DirectedPath.Path (imaginaryGraph Γ Y κ)) :=
  {p | p ∈ W.paths ∧ p.initial ∈ X}

/-- Members of the reference warp which meet `X`.  This is the paper's
restriction notation `Y⟨X⟩`; it is not restriction by initial vertex. -/
def referencePathsMeeting (Y : Set Γ.DPath) (X : Set V) : Set Γ.DPath :=
  {p | p ∈ Y ∧ (p.support ∩ X).Nonempty}

/-- The initial vertices retained from the ladder warp in blueprint
condition (2). -/
def retainedReferenceInitials (W : LinkageBlueprint Γ Y κ)
    (T : Set V) : Set V :=
  Γ.initialSet
    (referencePathsMeeting Y T \ referencePathsMeeting Y W.vertexSet)

/-- The set of indices of strong imaginary edges along a ray. -/
def strongEdgeIndices (r : DirectedPath.Ray (imaginaryGraph Γ Y κ)) : Set ℕ :=
  {n | IsStrongImaginaryEdge Γ Y κ (r n) (r (n + 1))}

/-- Blueprint condition (5). -/
def InfinitelyManyStrongEdges (W : LinkageBlueprint Γ Y κ) : Prop :=
  ∀ r : DirectedPath.Ray (imaginaryGraph Γ Y κ),
    (Sum.inr r : DirectedPath.Path (imaginaryGraph Γ Y κ)) ∈ W.paths →
      (strongEdgeIndices r).Infinite

/-- The six conditions in Definition 9.27.  Here `T` is `T_α`, `Z` is
the closing-up set, and `persistent` is `T_{κ⁺}`. -/
structure IsLinkageBlueprint (W : LinkageBlueprint Γ Y κ)
    (T Z persistent : Set V) : Prop where
  vertices_roofed : W.vertexSet ⊆ Γ.roof T
  covers_source : Γ.source ⊆ W.initialSet ∪ W.retainedReferenceInitials T
  vertices_closed : W.vertexSet ⊆ Z
  card_paths : #W.paths ≤ κ
  infinitely_many_strong : W.InfinitelyManyStrongEdges
  terminals_popular : W.terminalSet ⊆
    {u | IsPopular Γ Y persistent κ u} ∪ T

/-- Definition 9.29: a blueprint is stable if each of its `T_α`
terminals already belongs to `T_{κ⁺}`. -/
def Stable (W : LinkageBlueprint Γ Y κ) (T persistent : Set V) : Prop :=
  W.terminalSet ∩ T ⊆ persistent

theorem Stable.terminal_mem_persistent {W : LinkageBlueprint Γ Y κ}
    {T persistent : Set V} (hW : W.Stable T persistent)
    {x : V} (hxW : x ∈ W.terminalSet) (hxT : x ∈ T) :
    x ∈ persistent :=
  hW ⟨hxW, hxT⟩

end LinkageBlueprint

/-! ## The real part -/

/-- The spanning directed subgraph carried by a path family.  Isolated
vertices are retained explicitly; this matters for the real part of a
blueprint. -/
structure FamilyGraph (V : Type u) where
  vertices : Set V
  edges : Set (V × V)

namespace FamilyGraph

variable {X : Type u}

/-- Tails of edges in a family graph. -/
def tails (R : FamilyGraph X) : Set X :=
  {x | ∃ y, (x, y) ∈ R.edges}

/-- Terminals of the path components represented by a family graph. -/
def terminals (R : FamilyGraph X) : Set X :=
  R.vertices \ R.tails

/-- Graph inclusion, the set-level forward-extension relation used for real
parts. -/
def Extends (R S : FamilyGraph X) : Prop :=
  R.vertices ⊆ S.vertices ∧ R.edges ⊆ S.edges

@[refl] theorem extends_refl (R : FamilyGraph X) : R.Extends R :=
  ⟨Set.Subset.rfl, Set.Subset.rfl⟩

@[trans] theorem extends_trans {R S T : FamilyGraph X}
    (hRS : R.Extends S) (hST : S.Extends T) : R.Extends T :=
  ⟨hRS.1.trans hST.1, hRS.2.trans hST.2⟩

theorem vertices_subset_terminals_union_tails (R : FamilyGraph X) :
    R.vertices ⊆ R.terminals ∪ R.tails := by
  intro x hx
  by_cases htail : x ∈ R.tails
  · exact Or.inr htail
  · exact Or.inl ⟨hx, htail⟩

end FamilyGraph

namespace LinkageBlueprint

variable {Γ : DWeb V} {Y : Set Γ.DPath} {κ : Cardinal.{u}}

/-- The path-family graph of a blueprint. -/
def familyGraph (W : LinkageBlueprint Γ Y κ) : FamilyGraph V where
  vertices := W.vertexSet
  edges := W.edgeSet

/-- Source Definition 2.3 (ordinary extension), specialized to blueprint
family graphs.  It is plain inclusion of the old vertices and edges; unlike
`ForwardExtends`, it does not assert a path-by-path prefix correspondence. -/
def OrdinaryExtends (W U : LinkageBlueprint Γ Y κ) : Prop :=
  W.familyGraph.Extends U.familyGraph

@[refl] theorem ordinaryExtends_refl (W : LinkageBlueprint Γ Y κ) :
    W.OrdinaryExtends W :=
  FamilyGraph.extends_refl _

@[trans] theorem ordinaryExtends_trans {W U R : LinkageBlueprint Γ Y κ}
    (hWU : W.OrdinaryExtends U) (hUR : U.OrdinaryExtends R) :
    W.OrdinaryExtends R :=
  FamilyGraph.extends_trans hWU hUR

theorem vertexSet_mono_of_paths_subset {W U : LinkageBlueprint Γ Y κ}
    (h : W.paths ⊆ U.paths) : W.vertexSet ⊆ U.vertexSet := by
  rintro x ⟨p, hpW, hxp⟩
  exact ⟨p, h hpW, hxp⟩

theorem edgeSet_mono_of_paths_subset {W U : LinkageBlueprint Γ Y κ}
    (h : W.paths ⊆ U.paths) : W.edgeSet ⊆ U.edgeSet := by
  intro e he
  rcases Set.mem_iUnion.1 he with ⟨p, he⟩
  rcases Set.mem_iUnion.1 he with ⟨hpW, hep⟩
  exact Set.mem_iUnion.2 ⟨p, Set.mem_iUnion.2 ⟨h hpW, hep⟩⟩

/-- Inclusion of the underlying path sets is a concrete sufficient
condition for ordinary extension. -/
theorem ordinaryExtends_of_paths_subset {W U : LinkageBlueprint Γ Y κ}
    (h : W.paths ⊆ U.paths) : W.OrdinaryExtends U :=
  ⟨vertexSet_mono_of_paths_subset h, edgeSet_mono_of_paths_subset h⟩

/-- `cut` is obtained from `W` by deleting exactly the single outgoing
imaginary edge `(u,v)`.  Deleting the edge splits its warp member but keeps
all vertices; the resulting path decomposition is carried by the blueprint
data `cut`. -/
def IsImaginaryEdgeDeletionAt (W cut : LinkageBlueprint Γ Y κ)
    (u v : V) : Prop :=
  (u, v) ∈ W.edgeSet ∧ IsImaginaryEdge Γ Y κ u v ∧
    cut.vertexSet = W.vertexSet ∧
      cut.edgeSet = W.edgeSet \ {(u, v)}

theorem IsImaginaryEdgeDeletionAt.edge_mem
    {W cut : LinkageBlueprint Γ Y κ} {u v : V}
    (h : W.IsImaginaryEdgeDeletionAt cut u v) : (u, v) ∈ W.edgeSet :=
  h.1

theorem IsImaginaryEdgeDeletionAt.imaginary
    {W cut : LinkageBlueprint Γ Y κ} {u v : V}
    (h : W.IsImaginaryEdgeDeletionAt cut u v) :
    IsImaginaryEdge Γ Y κ u v :=
  h.2.1

theorem IsImaginaryEdgeDeletionAt.vertices_eq
    {W cut : LinkageBlueprint Γ Y κ} {u v : V}
    (h : W.IsImaginaryEdgeDeletionAt cut u v) :
    cut.vertexSet = W.vertexSet :=
  h.2.2.1

theorem IsImaginaryEdgeDeletionAt.edges_eq
    {W cut : LinkageBlueprint Γ Y κ} {u v : V}
    (h : W.IsImaginaryEdgeDeletionAt cut u v) :
    cut.edgeSet = W.edgeSet \ {(u, v)} :=
  h.2.2.2

/-- Source notation `W^u`: at a blueprint terminal nothing is changed;
otherwise the specified outgoing imaginary edge with tail `u` is deleted.
The existential edge branch records its head and certifies exact deletion. -/
def IsCutAt (W cut : LinkageBlueprint Γ Y κ) (u : V) : Prop :=
  (u ∈ W.terminalSet ∧ cut = W) ∨
    ∃ v, W.IsImaginaryEdgeDeletionAt cut u v

theorem isCutAt_self_of_mem_terminalSet
    (W : LinkageBlueprint Γ Y κ) {u : V} (hu : u ∈ W.terminalSet) :
    W.IsCutAt W u :=
  Or.inl ⟨hu, rfl⟩

theorem IsImaginaryEdgeDeletionAt.isCutAt
    {W cut : LinkageBlueprint Γ Y κ} {u v : V}
    (h : W.IsImaginaryEdgeDeletionAt cut u v) : W.IsCutAt cut u :=
  Or.inr ⟨v, h⟩

/-- A one-edge deletion is an ordinary sub-blueprint of the original. -/
theorem IsImaginaryEdgeDeletionAt.ordinaryExtends_original
    {W cut : LinkageBlueprint Γ Y κ} {u v : V}
    (h : W.IsImaginaryEdgeDeletionAt cut u v) : cut.OrdinaryExtends W := by
  constructor
  · intro x hx
    change x ∈ cut.vertexSet at hx
    change x ∈ W.vertexSet
    rw [h.vertices_eq] at hx
    exact hx
  · intro e he
    change e ∈ cut.edgeSet at he
    change e ∈ W.edgeSet
    rw [h.edges_eq] at he
    exact he.1

theorem IsCutAt.ordinaryExtends_original
    {W cut : LinkageBlueprint Γ Y κ} {u : V}
    (h : W.IsCutAt cut u) : cut.OrdinaryExtends W := by
  rcases h with ⟨_, rfl⟩ | ⟨v, hv⟩
  · exact ordinaryExtends_refl _
  · exact hv.ordinaryExtends_original

theorem IsCutAt.exists_imaginaryEdgeDeletion_of_ne
    {W cut : LinkageBlueprint Γ Y κ} {u : V}
    (h : W.IsCutAt cut u) (hne : cut ≠ W) :
    ∃ v, W.IsImaginaryEdgeDeletionAt cut u v := by
  rcases h with ⟨_, hcut⟩ | hedge
  · exact (hne hcut).elim
  · exact hedge

/-- Definition 9.28: the real part is spanning on the same vertex set and
retains exactly the blueprint edges which are also edges of `D`. -/
def realPart (W : LinkageBlueprint Γ Y κ) : FamilyGraph V where
  vertices := W.vertexSet
  edges := W.edgeSet ∩ {e | Γ.graph.Adj e.1 e.2}

@[simp] theorem realPart_vertices (W : LinkageBlueprint Γ Y κ) :
    W.realPart.vertices = W.vertexSet :=
  rfl

@[simp] theorem realPart_edges (W : LinkageBlueprint Γ Y κ) :
    W.realPart.edges = W.edgeSet ∩ {e | Γ.graph.Adj e.1 e.2} :=
  rfl

theorem realPart_edges_subset (W : LinkageBlueprint Γ Y κ) :
    W.realPart.edges ⊆ W.edgeSet :=
  Set.inter_subset_left

theorem realPart_edges_are_original (W : LinkageBlueprint Γ Y κ) :
    W.realPart.edges ⊆ {e | Γ.graph.Adj e.1 e.2} :=
  Set.inter_subset_right

/-- Ordinary extension also includes the spanning real parts, because both
real edge sets are obtained by intersecting with the same original graph. -/
theorem OrdinaryExtends.realPart_extends {W U : LinkageBlueprint Γ Y κ}
    (h : W.OrdinaryExtends U) : W.realPart.Extends U.realPart := by
  refine ⟨h.1, ?_⟩
  rintro e ⟨heW, heD⟩
  exact ⟨h.2 heW, heD⟩

theorem OrdinaryExtends.vertices_mono {W U : LinkageBlueprint Γ Y κ}
    (h : W.OrdinaryExtends U) : W.vertexSet ⊆ U.vertexSet :=
  h.1

theorem OrdinaryExtends.edges_mono {W U : LinkageBlueprint Γ Y κ}
    (h : W.OrdinaryExtends U) : W.edgeSet ⊆ U.edgeSet :=
  h.2

/-- An edge adjoined as imaginary but already present in `D` belongs to the
real part, as required by Definition 9.28. -/
theorem mem_realPart_of_mem_edgeSet_of_original
    (W : LinkageBlueprint Γ Y κ) {e : V × V}
    (heW : e ∈ W.edgeSet) (heD : Γ.graph.Adj e.1 e.2) :
    e ∈ W.realPart.edges :=
  ⟨heW, heD⟩

/-- Every nonterminal blueprint vertex is the tail of a blueprint edge. -/
theorem exists_outgoing_of_mem_vertexSet_of_not_mem_terminalSet
    (W : LinkageBlueprint Γ Y κ) {x : V} (hx : x ∈ W.vertexSet)
    (hterm : x ∉ W.terminalSet) :
    ∃ y, (x, y) ∈ W.edgeSet := by
  obtain ⟨p, hpW, hxp⟩ := hx
  have hpterm : (imaginaryWeb Γ Y κ).terminal? p ≠ some x := by
    intro hp
    exact hterm ⟨p, hpW, hp⟩
  have hpterm' : p.terminal? ≠ some x := by
    simpa [DWeb.terminal?, DirectedPath.Path.terminal?] using hpterm
  obtain ⟨y, hy⟩ :=
    path_exists_outgoing_of_mem_support_of_not_terminal p hxp hpterm'
  exact ⟨y, Set.mem_iUnion.2 ⟨p, Set.mem_iUnion.2 ⟨hpW, hy⟩⟩⟩

/-- Vertices lying on a real path of `W` which has already reached `B`.
This is `V[Re(W)⟨B⟩]` in (9.32). -/
def completedRealVertices (W : LinkageBlueprint Γ Y κ) (B : Set V) : Set V :=
  {x | ∃ p : DirectedPath.FinitePath Γ.graph,
    p.finish ∈ B ∧ p.support ⊆ W.realPart.vertices ∧
      p.edgeSet ⊆ W.realPart.edges ∧ x ∈ p.support}

/-- The real part links `u` to `B`. -/
def RealLinksTo (W : LinkageBlueprint Γ Y κ) (u : V) (B : Set V) : Prop :=
  ∃ p : DirectedPath.FinitePath Γ.graph,
    p.start = u ∧ p.finish ∈ B ∧ p.support ⊆ W.realPart.vertices ∧
      p.edgeSet ⊆ W.realPart.edges

theorem RealLinksTo.start_mem_completedRealVertices
    {W : LinkageBlueprint Γ Y κ} {u : V} {B : Set V}
    (h : W.RealLinksTo u B) : u ∈ W.completedRealVertices B := by
  rcases h with ⟨p, hpstart, hpB, hpsupport, hpedge⟩
  exact ⟨p, hpB, hpsupport, hpedge, hpstart ▸ p.start_mem_support⟩

/-- Forward extension of actual blueprint paths. -/
def ForwardExtends (W U : LinkageBlueprint Γ Y κ) : Prop :=
  (∀ p ∈ W.paths, ∃ q ∈ U.paths, (imaginaryWeb Γ Y κ).Extends p q) ∧
    (∀ q ∈ U.paths, ∃ p ∈ W.paths, (imaginaryWeb Γ Y κ).Extends p q)

@[refl] theorem forwardExtends_refl (W : LinkageBlueprint Γ Y κ) :
    W.ForwardExtends W := by
  constructor <;> intro p hp <;>
    exact ⟨p, hp, (imaginaryWeb Γ Y κ).extends_refl p⟩

@[trans] theorem forwardExtends_trans {W U R : LinkageBlueprint Γ Y κ}
    (hWU : W.ForwardExtends U) (hUR : U.ForwardExtends R) :
    W.ForwardExtends R := by
  constructor
  · intro p hp
    obtain ⟨q, hq, hpq⟩ := hWU.1 p hp
    obtain ⟨r, hr, hqr⟩ := hUR.1 q hq
    exact ⟨r, hr, (imaginaryWeb Γ Y κ).extends_trans hpq hqr⟩
  · intro r hr
    obtain ⟨q, hq, hqr⟩ := hUR.2 r hr
    obtain ⟨p, hp, hpq⟩ := hWU.2 q hq
    exact ⟨p, hp, (imaginaryWeb Γ Y κ).extends_trans hpq hqr⟩

/-- Definition (9.32).  The first conjunct is ordinary extension of the real
parts (vertex and edge inclusion).  The second is the exact persistence
condition from the paper; the
edge intersection is the intersection of all blueprint edges, not merely
of imaginary edges. -/
def RealExtends (W U : LinkageBlueprint Γ Y κ) (B : Set V) : Prop :=
  W.realPart.Extends U.realPart ∧
    W.vertexSet ⊆
      (U.terminalSet ∩ W.terminalSet) ∪
        {x | ∃ y, (x, y) ∈ W.familyGraph.edges ∩ U.familyGraph.edges} ∪
          U.completedRealVertices B

theorem realExtends_refl (W : LinkageBlueprint Γ Y κ) (B : Set V) :
    W.RealExtends W B := by
  refine ⟨FamilyGraph.extends_refl _, ?_⟩
  intro x hx
  by_cases hxterm : x ∈ W.terminalSet
  · exact Or.inl (Or.inl ⟨hxterm, hxterm⟩)
  · obtain ⟨y, hy⟩ :=
      W.exists_outgoing_of_mem_vertexSet_of_not_mem_terminalSet hx hxterm
    exact Or.inl (Or.inr ⟨y, hy, hy⟩)

theorem RealExtends.realPart_extends {W U : LinkageBlueprint Γ Y κ}
    {B : Set V} (h : W.RealExtends U B) :
    W.realPart.Extends U.realPart :=
  h.1

theorem RealExtends.vertices_mono {W U : LinkageBlueprint Γ Y κ}
    {B : Set V} (h : W.RealExtends U B) : W.vertexSet ⊆ U.vertexSet := by
  simpa only [realPart_vertices] using h.1.1

theorem RealExtends.realEdges_mono {W U : LinkageBlueprint Γ Y κ}
    {B : Set V} (h : W.RealExtends U B) :
    W.realPart.edges ⊆ U.realPart.edges :=
  h.1.2

/-! ## Exact conclusion predicates for Assertions 9.30--9.34 -/

/-- Preservation of the real terminals of `W`, apart from a scheduled set
of exceptions.  This small interface is used when composing 9.30 and 9.31. -/
def PreservesRealTerminalsExcept (W U : LinkageBlueprint Γ Y κ)
    (except : Set V) : Prop :=
  W.realPart.terminals \ except ⊆ U.realPart.terminals

/-- Preservation by `U` of terminals inherited simultaneously from an
ancestor `A` and the current blueprint `W`, apart from scheduled exceptions.
The ancestor parameter makes the terminal transport in the proof of 9.34
explicit rather than silently strengthening 9.31. -/
def PreservesInheritedTerminalsExcept
    (A W U : LinkageBlueprint Γ Y κ) (except : Set V) : Prop :=
  (A.terminalSet ∩ W.terminalSet) \ except ⊆ U.terminalSet

theorem PreservesInheritedTerminalsExcept.apply
    {A W U : LinkageBlueprint Γ Y κ} {except : Set V}
    (h : PreservesInheritedTerminalsExcept A W U except)
    {x : V} (hxA : x ∈ A.terminalSet) (hxW : x ∈ W.terminalSet)
    (hx : x ∉ except) : x ∈ U.terminalSet :=
  h ⟨⟨hxA, hxW⟩, hx⟩

/-- The literal structural output of source Assertion 9.30.  `cut = W^u`
is `W` itself when `u` is a blueprint terminal; otherwise it is obtained by
deleting the single outgoing imaginary edge of `W` with tail `u`.  The
resulting blueprint ordinarily extends this cut, links `u` to the current
ladder slice, and loses no other real terminal.  In particular, this
assertion does not claim the later real-extension relation (9.32). -/
def ContinuationConclusion (W cut U : LinkageBlueprint Γ Y κ)
    (u : V) (T : Set V) : Prop :=
  W.IsCutAt cut u ∧ cut.OrdinaryExtends U ∧
    U.RealLinksTo u T ∧
    W.PreservesRealTerminalsExcept U {u}

/-- The exact three output clauses of Assertion 9.31, together with
ordinary extension in the sense of Definition 2.3. -/
def AdvanceConclusion (W U : LinkageBlueprint Γ Y κ)
    (z : V) (T persistent B : Set V) : Prop :=
  W.OrdinaryExtends U ∧ U.RealLinksTo z B ∧
    W.realPart.terminals ⊆ U.realPart.terminals ∪ T ∧
    W.terminalSet ∩ persistent ⊆ U.terminalSet ∪ {z}

/-- Assertion 9.33 as a property of a proposed limit blueprint.  The
construction of the limit is kept separate from this specification. -/
def StableLimitConclusion {I : Type v}
    (stage : I → LinkageBlueprint Γ Y κ)
    (limit : LinkageBlueprint Γ Y κ) (T Z persistent B : Set V) : Prop :=
  limit.IsLinkageBlueprint T Z persistent ∧ limit.Stable T persistent ∧
    ∀ i, (stage i).RealExtends limit B

/-- The exact output of Assertion 9.34. -/
def StableExtensionConclusion (W U : LinkageBlueprint Γ Y κ)
    (u : V) (T Z persistent B : Set V) : Prop :=
  U.IsLinkageBlueprint T Z persistent ∧ U.Stable T persistent ∧
    W.RealExtends U B ∧ U.RealLinksTo u B ∧
      W.realPart.terminals \ {u} ⊆ U.realPart.terminals

theorem ContinuationConclusion.isCutAt
    {W cut U : LinkageBlueprint Γ Y κ} {u : V} {T : Set V}
    (h : ContinuationConclusion W cut U u T) :
    W.IsCutAt cut u :=
  h.1

theorem ContinuationConclusion.ordinaryExtends
    {W cut U : LinkageBlueprint Γ Y κ} {u : V} {T : Set V}
    (h : ContinuationConclusion W cut U u T) : cut.OrdinaryExtends U :=
  h.2.1

theorem ContinuationConclusion.links
    {W cut U : LinkageBlueprint Γ Y κ} {u : V} {T : Set V}
    (h : ContinuationConclusion W cut U u T) : U.RealLinksTo u T :=
  h.2.2.1

theorem ContinuationConclusion.preserves_other_terminals
    {W cut U : LinkageBlueprint Γ Y κ} {u : V} {T : Set V}
    (h : ContinuationConclusion W cut U u T) :
    W.realPart.terminals \ {u} ⊆ U.realPart.terminals :=
  h.2.2.2

theorem AdvanceConclusion.ordinaryExtends
    {W U : LinkageBlueprint Γ Y κ} {z : V} {T persistent B : Set V}
    (h : AdvanceConclusion W U z T persistent B) : W.OrdinaryExtends U :=
  h.1

theorem AdvanceConclusion.links
    {W U : LinkageBlueprint Γ Y κ} {z : V} {T persistent B : Set V}
    (h : AdvanceConclusion W U z T persistent B) : U.RealLinksTo z B :=
  h.2.1

theorem StableExtensionConclusion.preserves_other_terminals
    {W U : LinkageBlueprint Γ Y κ} {u : V} {T Z persistent B : Set V}
    (h : StableExtensionConclusion W U u T Z persistent B) :
    W.realPart.terminals \ {u} ⊆ U.realPart.terminals :=
  h.2.2.2.2

theorem StableExtensionConclusion.isLinkageBlueprint
    {W U : LinkageBlueprint Γ Y κ} {u : V} {T Z persistent B : Set V}
    (h : StableExtensionConclusion W U u T Z persistent B) :
    U.IsLinkageBlueprint T Z persistent :=
  h.1

theorem StableExtensionConclusion.stable
    {W U : LinkageBlueprint Γ Y κ} {u : V} {T Z persistent B : Set V}
    (h : StableExtensionConclusion W U u T Z persistent B) :
    U.Stable T persistent :=
  h.2.1

theorem StableExtensionConclusion.realExtends
    {W U : LinkageBlueprint Γ Y κ} {u : V} {T Z persistent B : Set V}
    (h : StableExtensionConclusion W U u T Z persistent B) :
    W.RealExtends U B :=
  h.2.2.1

theorem StableExtensionConclusion.links
    {W U : LinkageBlueprint Γ Y κ} {u : V} {T Z persistent B : Set V}
    (h : StableExtensionConclusion W U u T Z persistent B) :
    U.RealLinksTo u B :=
  h.2.2.2.1

/-! ## Liminf of blueprint path families -/

/-- The eventual path set of a family of blueprints. -/
def limitPaths {I : Type v} [Preorder I] [Nonempty I]
    (stage : I → LinkageBlueprint Γ Y κ) :
    Set (DirectedPath.Path (imaginaryGraph Γ Y κ)) :=
  WarpLimits.setLiminf fun i ↦ (stage i).paths

/-- Pairwise disjointness is preserved by directed liminf.  This is the
purely structural warp part of Assertion 9.33. -/
theorem limitPaths_isWarp {I : Type v} [Preorder I] [Nonempty I]
    [IsDirectedOrder I] (stage : I → LinkageBlueprint Γ Y κ) :
    (imaginaryWeb Γ Y κ).IsWarp (limitPaths stage) := by
  intro p hp q hq hpq
  obtain ⟨ip, hip⟩ := (WarpLimits.mem_setLiminf _ _).1 hp
  obtain ⟨iq, hiq⟩ := (WarpLimits.mem_setLiminf _ _).1 hq
  obtain ⟨k, hik, hjk⟩ := exists_ge_ge ip iq
  exact (stage k).isWarp (hip k hik) (hiq k hjk) hpq

/-- The liminf path set, bundled as actual blueprint data. -/
def limit {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]
    (stage : I → LinkageBlueprint Γ Y κ) : LinkageBlueprint Γ Y κ where
  paths := limitPaths stage
  isWarp := limitPaths_isWarp stage

@[simp] theorem limit_paths {I : Type v} [Preorder I] [Nonempty I]
    [IsDirectedOrder I] (stage : I → LinkageBlueprint Γ Y κ) :
    (limit stage).paths = limitPaths stage :=
  rfl

end LinkageBlueprint

/-! ## Closing-up predicates used in Assertions 9.22--9.25 -/

/-- Every reference path which meets `Z` is wholly contained in `Z`
(Assertion 9.24). -/
def ClosedUnderPaths (Γ : DWeb V) (Y : Set Γ.DPath) (Z : Set V) : Prop :=
  ∀ p ∈ Y, (p.support ∩ Z).Nonempty → p.support ⊆ Z

/-- The path-closing conclusion of Assertion 9.23.  `Preserves p` is
instantiated later by the statement that deleting the chosen `v`--`B` path
leaves the relevant quotient web unhindered. -/
def HasPreservingTargetPaths (Γ : DWeb V) (T Z B : Set V)
    (Preserves : DirectedPath.FinitePath Γ.graph → Prop) : Prop :=
  ∀ v ∈ T ∩ Z, ∃ p : DirectedPath.FinitePath Γ.graph,
    p.start = v ∧ p.finish ∈ B ∧ p.support ⊆ Z ∧ Preserves p

theorem closedUnderPaths_iUnion {Γ : DWeb V} {Y : Set Γ.DPath}
    {I : Type v} [Nonempty I] {Z : I → Set V}
    (hZ : ∀ i, ClosedUnderPaths Γ Y (Z i)) :
    ClosedUnderPaths Γ Y (⋃ i, Z i) := by
  intro p hp hmeet
  obtain ⟨x, hxp, hxZ⟩ := hmeet
  obtain ⟨i, hxi⟩ := Set.mem_iUnion.1 hxZ
  intro y hyp
  exact Set.mem_iUnion.2 ⟨i, hZ i p hp ⟨x, hxp, hxi⟩ hyp⟩

/-- The hammock closure demanded by Assertion 9.22, stated without claiming
its transfinite construction. -/
def HammockClosedUpTo (Γ : DWeb V) (Y : Set Γ.DPath)
    (Z ZBefore innerRoof roof : Set V) (ρ : Cardinal.{u}) : Prop :=
  ∀ u e, HammockEligible ZBefore innerRoof roof u e →
    ∃ H : Set (AltPath Γ.graph),
      HammockMaximalUpTo Γ Y u e ρ H ∧ HammockContained H Z

/-- The closure conclusion of Assertion 9.25. -/
def ContainedInRoof (Z roof : Set V) : Prop :=
  Z ⊆ roof

theorem ContainedInRoof.mono_left {Z Z' roof : Set V}
    (hZ : ContainedInRoof Z roof) (hZ' : Z' ⊆ Z) :
    ContainedInRoof Z' roof :=
  hZ'.trans hZ

end Blueprint
end Erdos599
