/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos63.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions

/-!
# Expansion notions for the Liu--Montgomery argument

This file records the definitions used in the Komlós--Szemerédi extraction
and Liu--Montgomery path argument.  In particular, `expansionEpsilon` is the
piecewise expansion profile from Liu--Montgomery, and `IsLMExpander` uses an
external neighborhood (so the set being expanded is not counted as part of
its own neighborhood).

A `Bipartition` remembers finite sides which cover the vertex type.  This is
slightly stronger than `SimpleGraph.IsBipartiteWith`, whose two sets need only
cover the support of the graph, and is the useful form once isolated vertices
have been removed.  Its principal consequence here is the parity rule for
walks.

Finally, `BoundedVertexExpansion G root D m` is the induced-vertex-set form of
a `(D,m)`-expansion: it is a set of exactly `D` vertices, containing `root`,
and every vertex can be joined to `root` by a path of length at most `m`
which remains in that set.  Passing to the graph induced by the recorded set
makes this equivalent to the subgraph formulation in the paper.
-/

open Finset Set SimpleGraph
open scoped BigOperators SimpleGraph

namespace Erdos63

attribute [local instance] Classical.propDecidable Classical.decEq

universe u

variable {V : Type u}
variable {G G' G'' : SimpleGraph V}

/-! ## The Liu--Montgomery expansion profile -/

/-- The expansion function

`epsilon(x, epsilon₁, k) = 0` for `x < k / 5`, and
`epsilon₁ / log(15x/k)^2` otherwise.

The cardinal argument is a natural number because it will always be the
cardinality of a finite vertex set. -/
noncomputable def expansionEpsilon (epsilon₁ k : ℝ) (x : ℕ) : ℝ :=
  if (x : ℝ) < k / 5 then 0
  else epsilon₁ / (Real.log (15 * (x : ℝ) / k)) ^ 2

@[simp] theorem expansionEpsilon_of_lt {epsilon₁ k : ℝ} {x : ℕ}
    (hx : (x : ℝ) < k / 5) : expansionEpsilon epsilon₁ k x = 0 := by
  simp [expansionEpsilon, hx]

theorem expansionEpsilon_of_le {epsilon₁ k : ℝ} {x : ℕ}
    (hx : k / 5 ≤ (x : ℝ)) :
    expansionEpsilon epsilon₁ k x =
      epsilon₁ / (Real.log (15 * (x : ℝ) / k)) ^ 2 := by
  simp [expansionEpsilon, not_lt.mpr hx]

@[simp] theorem expansionEpsilon_zero_left (k : ℝ) (x : ℕ) :
    expansionEpsilon 0 k x = 0 := by
  by_cases hx : (x : ℝ) < k / 5 <;>
    simp [expansionEpsilon, hx]

theorem expansionEpsilon_nonneg {epsilon₁ k : ℝ} (hepsilon : 0 ≤ epsilon₁)
    (x : ℕ) : 0 ≤ expansionEpsilon epsilon₁ k x := by
  by_cases hx : (x : ℝ) < k / 5
  · simp [expansionEpsilon, hx]
  · rw [expansionEpsilon_of_le (not_lt.mp hx)]
    exact div_nonneg hepsilon (sq_nonneg _)

theorem expansionEpsilon_mono_epsilon {epsilon₁ epsilon₁' k : ℝ}
    (h : epsilon₁ ≤ epsilon₁') (x : ℕ) :
    expansionEpsilon epsilon₁ k x ≤ expansionEpsilon epsilon₁' k x := by
  by_cases hx : (x : ℝ) < k / 5
  · simp [expansionEpsilon, hx]
  · rw [expansionEpsilon_of_le (not_lt.mp hx), expansionEpsilon_of_le (not_lt.mp hx)]
    exact div_le_div_of_nonneg_right h (sq_nonneg _)

/-- A set expands at a specified real rate when its external neighborhood is
at least that rate times its cardinality. -/
def ExpandsAt [Fintype V] (G : SimpleGraph V) (rate : ℝ) (S : Finset V) : Prop :=
  rate * (S.card : ℝ) ≤ (externalNeighborhood G S).card

theorem ExpandsAt.mono_graph [Fintype V] {rate : ℝ} {S : Finset V}
    (h : ExpandsAt G rate S) (hGG' : G ≤ G') : ExpandsAt G' rate S := by
  refine h.trans ?_
  exact_mod_cast Finset.card_le_card (externalNeighborhood_mono_graph hGG' S)

theorem ExpandsAt.anti_rate [Fintype V] {rate rate' : ℝ} {S : Finset V}
    (h : ExpandsAt G rate S) (hrate : rate' ≤ rate) : ExpandsAt G rate' S := by
  exact (mul_le_mul_of_nonneg_right hrate (Nat.cast_nonneg _)).trans h

theorem card_externalNeighborhood_le_card_compl [Fintype V]
    (G : SimpleGraph V) (S : Finset V) :
    (externalNeighborhood G S).card ≤ Fintype.card V - S.card := by
  have hsum : (externalNeighborhood G S).card + S.card ≤ Fintype.card V := by
    rw [← Finset.card_union_of_disjoint (externalNeighborhood_disjoint G S)]
    exact Finset.card_le_univ _
  omega

theorem card_externalNeighborhood_le_card [Fintype V]
    (G : SimpleGraph V) (S : Finset V) :
    (externalNeighborhood G S).card ≤ Fintype.card V := by
  exact (card_externalNeighborhood_le_card_compl G S).trans (Nat.sub_le _ _)

/-- The exact expansion condition used in the Liu--Montgomery paper.  Only
sets of real cardinality between `k/2` and half the order of the graph are
required to expand. -/
def IsLMExpander [Fintype V] (G : SimpleGraph V) (epsilon₁ k : ℝ) : Prop :=
  ∀ S : Finset V,
    k / 2 ≤ (S.card : ℝ) →
    (S.card : ℝ) ≤ (Fintype.card V : ℝ) / 2 →
    ExpandsAt G (expansionEpsilon epsilon₁ k S.card) S

theorem IsLMExpander.expands [Fintype V] {epsilon₁ k : ℝ}
    (h : IsLMExpander G epsilon₁ k) {S : Finset V}
    (hlower : k / 2 ≤ (S.card : ℝ))
    (hupper : (S.card : ℝ) ≤ (Fintype.card V : ℝ) / 2) :
    ExpandsAt G (expansionEpsilon epsilon₁ k S.card) S :=
  h S hlower hupper

theorem IsLMExpander.mono_graph [Fintype V] {epsilon₁ k : ℝ}
    (h : IsLMExpander G epsilon₁ k) (hGG' : G ≤ G') :
    IsLMExpander G' epsilon₁ k := by
  intro S hlower hupper
  exact (h S hlower hupper).mono_graph hGG'

theorem IsLMExpander.anti_profile [Fintype V] {epsilon₁ epsilon₁' k : ℝ}
    (h : IsLMExpander G epsilon₁ k)
    (hprofile : ∀ x : ℕ,
      expansionEpsilon epsilon₁' k x ≤ expansionEpsilon epsilon₁ k x) :
    IsLMExpander G epsilon₁' k := by
  intro S hlower hupper
  exact (h S hlower hupper).anti_rate (hprofile S.card)

theorem IsLMExpander.anti_epsilon [Fintype V] {epsilon₁ epsilon₁' k : ℝ}
    (h : IsLMExpander G epsilon₁ k) (hepsilon : epsilon₁' ≤ epsilon₁) :
    IsLMExpander G epsilon₁' k := by
  exact h.anti_profile fun x ↦ expansionEpsilon_mono_epsilon hepsilon x

theorem IsLMExpander.vacuous [Fintype V] {epsilon₁ k : ℝ}
    (hk : (Fintype.card V : ℝ) < k) : IsLMExpander G epsilon₁ k := by
  intro S hlower hupper
  exfalso
  have htwo : (0 : ℝ) < 2 := by norm_num
  have hkn : k ≤ (Fintype.card V : ℝ) :=
    (div_le_div_iff_of_pos_right htwo).mp (hlower.trans hupper)
  exact (not_le_of_gt hk) hkn

/-! ## Bipartition sides and path parity -/

/-- Two vertices lie on the same one of the recorded sides. -/
def SameSide (left right : Finset V) (x y : V) : Prop :=
  (x ∈ left ∧ y ∈ left) ∨ (x ∈ right ∧ y ∈ right)

/-- Two vertices lie on opposite recorded sides. -/
def OppositeSides (left right : Finset V) (x y : V) : Prop :=
  (x ∈ left ∧ y ∈ right) ∨ (x ∈ right ∧ y ∈ left)

theorem SameSide.symm {left right : Finset V} {x y : V}
    (h : SameSide left right x y) : SameSide left right y x := by
  rcases h with h | h
  · exact Or.inl ⟨h.2, h.1⟩
  · exact Or.inr ⟨h.2, h.1⟩

theorem OppositeSides.symm {left right : Finset V} {x y : V}
    (h : OppositeSides left right x y) : OppositeSides left right y x := by
  rcases h with h | h
  · exact Or.inr ⟨h.2, h.1⟩
  · exact Or.inl ⟨h.2, h.1⟩

/-- A finite bipartition whose sides cover the whole current vertex type. -/
structure Bipartition [Fintype V] (G : SimpleGraph V) where
  /-- The left side. -/
  left : Finset V
  /-- The right side. -/
  right : Finset V
  /-- No vertex belongs to both sides.  This pointwise form avoids putting a
  computational `DecidableEq V` parameter on the certificate type. -/
  disjoint : ∀ x : V, x ∈ left → x ∈ right → False
  /-- Every vertex belongs to one of the two sides. -/
  cover : ∀ x : V, x ∈ left ∨ x ∈ right
  isBipartiteWith : G.IsBipartiteWith (left : Set V) (right : Set V)

namespace Bipartition

variable [Fintype V]

/-- A Boolean proper coloring determines a bipartition of the entire vertex
type, including isolated vertices. -/
noncomputable def ofColoring (c : G.Coloring Bool) : Bipartition G where
  left := Finset.univ.filter fun x ↦ c x = true
  right := Finset.univ.filter fun x ↦ c x = false
  disjoint := by
    intro x hxleft hxright
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hxleft hxright
    simp [hxleft] at hxright
  cover := by
    intro x
    cases hx : c x <;> simp [hx]
  isBipartiteWith := by
    refine ⟨?_, ?_⟩
    · rw [Set.disjoint_left]
      intro x hxleft hxright
      simp only [Finset.coe_filter, Finset.coe_univ, Set.mem_setOf_eq,
        Set.mem_univ, true_and] at hxleft hxright
      simp [hxleft] at hxright
    · intro x y hxy
      have hne := c.valid hxy
      cases hx : c x <;> cases hy : c y <;>
        simp [hx, hy] at hne ⊢

/-- Every bipartite graph on a finite vertex type admits a bipartition which
covers that type. -/
noncomputable def ofIsBipartite (h : G.IsBipartite) : Bipartition G :=
  ofColoring (G.recolorOfEquiv finTwoEquiv h.some)

@[simp] theorem ofColoring_mem_left (c : G.Coloring Bool) (x : V) :
    x ∈ (ofColoring c).left ↔ c x = true := by
  simp [ofColoring]

@[simp] theorem ofColoring_mem_right (c : G.Coloring Bool) (x : V) :
    x ∈ (ofColoring c).right ↔ c x = false := by
  simp [ofColoring]

theorem mem_left_or_right (B : Bipartition G) (x : V) :
    x ∈ B.left ∨ x ∈ B.right :=
  B.cover x

theorem not_mem_right_of_mem_left (B : Bipartition G) {x : V}
    (hx : x ∈ B.left) : x ∉ B.right :=
  B.disjoint x hx

theorem not_mem_left_of_mem_right (B : Bipartition G) {x : V}
    (hx : x ∈ B.right) : x ∉ B.left := fun hxleft ↦
  B.disjoint x hxleft hx

theorem mem_right_iff_not_mem_left (B : Bipartition G) (x : V) :
    x ∈ B.right ↔ x ∉ B.left := by
  constructor
  · exact B.not_mem_left_of_mem_right
  · intro hx
    exact (B.mem_left_or_right x).resolve_left hx

theorem mem_left_iff_not_mem_right (B : Bipartition G) (x : V) :
    x ∈ B.left ↔ x ∉ B.right := by
  constructor
  · exact B.not_mem_right_of_mem_left
  · intro hx
    exact (B.mem_left_or_right x).resolve_right hx

theorem sameSide_refl (B : Bipartition G) (x : V) :
    SameSide B.left B.right x x := by
  rcases B.mem_left_or_right x with hx | hx
  · exact Or.inl ⟨hx, hx⟩
  · exact Or.inr ⟨hx, hx⟩

theorem sameSide_iff_left_membership (B : Bipartition G) (x y : V) :
    SameSide B.left B.right x y ↔ (x ∈ B.left ↔ y ∈ B.left) := by
  constructor
  · rintro (⟨hx, hy⟩ | ⟨hx, hy⟩)
    · simp [hx, hy]
    · simp [B.not_mem_left_of_mem_right hx,
        B.not_mem_left_of_mem_right hy]
  · intro h
    by_cases hx : x ∈ B.left
    · exact Or.inl ⟨hx, h.mp hx⟩
    · exact Or.inr ⟨(B.mem_right_iff_not_mem_left x).2 hx,
        (B.mem_right_iff_not_mem_left y).2 (fun hy ↦ hx (h.mpr hy))⟩

theorem oppositeSides_iff_not_sameSide (B : Bipartition G) (x y : V) :
    OppositeSides B.left B.right x y ↔ ¬ SameSide B.left B.right x y := by
  rw [B.sameSide_iff_left_membership]
  by_cases hx : x ∈ B.left <;> by_cases hy : y ∈ B.left
  <;> simp_all [OppositeSides, B.mem_right_iff_not_mem_left]

theorem sameSide_or_oppositeSides (B : Bipartition G) (x y : V) :
    SameSide B.left B.right x y ∨ OppositeSides B.left B.right x y := by
  by_cases h : SameSide B.left B.right x y
  · exact Or.inl h
  · exact Or.inr ((B.oppositeSides_iff_not_sameSide x y).2 h)

theorem card_left_add_card_right (B : Bipartition G) :
    B.left.card + B.right.card = Fintype.card V := by
  have hdisjoint : Disjoint B.left B.right :=
    Finset.disjoint_left.2 fun x hxleft hxright ↦ B.disjoint x hxleft hxright
  have hcover : B.left ∪ B.right = (Finset.univ : Finset V) := by
    ext x
    simp only [Finset.mem_union, Finset.mem_univ, iff_true]
    exact B.cover x
  rw [← Finset.card_union_of_disjoint hdisjoint, hcover]
  simp

theorem oppositeSides_of_adj (B : Bipartition G) {x y : V}
    (hxy : G.Adj x y) : OppositeSides B.left B.right x y := by
  exact B.isBipartiteWith.mem_of_adj hxy

/-- Restrict a bipartition to a subgraph on the same vertex type. -/
def of_le (B : Bipartition G') (hGG' : G ≤ G') : Bipartition G where
  left := B.left
  right := B.right
  disjoint := B.disjoint
  cover := B.cover
  isBipartiteWith := {
    disjoint := B.isBipartiteWith.disjoint
    mem_of_adj := fun {_ _} h ↦ B.isBipartiteWith.mem_of_adj (hGG' h) }

@[simp] theorem of_le_left (B : Bipartition G') (hGG' : G ≤ G') :
    (B.of_le hGG').left = B.left := rfl

@[simp] theorem of_le_right (B : Bipartition G') (hGG' : G ≤ G') :
    (B.of_le hGG').right = B.right := rfl

/-- The Boolean coloring associated to a bipartition. -/
noncomputable def coloring (B : Bipartition G) : G.Coloring Bool := by
  classical
  refine SimpleGraph.Coloring.mk (fun x ↦ decide (x ∈ B.left)) ?_
  intro x y hxy
  rcases B.oppositeSides_of_adj hxy with ⟨hx, hy⟩ | ⟨hx, hy⟩
  · have hy' : y ∉ B.left := B.not_mem_left_of_mem_right hy
    simp [hx, hy']
  · have hx' : x ∉ B.left := B.not_mem_left_of_mem_right hx
    simp [hx', hy]

@[simp] theorem coloring_apply (B : Bipartition G) (x : V) :
    B.coloring x = decide (x ∈ B.left) := rfl

theorem even_length_iff_sameSide (B : Bipartition G) {x y : V}
    (p : G.Walk x y) :
    Even p.length ↔ SameSide B.left B.right x y := by
  rw [B.coloring.even_length_iff_congr p, B.sameSide_iff_left_membership]
  simp

theorem odd_length_iff_oppositeSides (B : Bipartition G) {x y : V}
    (p : G.Walk x y) :
    Odd p.length ↔ OppositeSides B.left B.right x y := by
  rw [← Nat.not_even_iff_odd, B.even_length_iff_sameSide,
    B.oppositeSides_iff_not_sameSide]

end Bipartition

/-- A length has the parity forced by two endpoints in a bipartition. -/
def ParityCompatible [Fintype V] (B : Bipartition G) (x y : V) (n : ℕ) : Prop :=
  Even n ↔ SameSide B.left B.right x y

@[simp] theorem parityCompatible_iff [Fintype V] (B : Bipartition G)
    (x y : V) (n : ℕ) :
    ParityCompatible B x y n ↔ (Even n ↔ SameSide B.left B.right x y) :=
  Iff.rfl

theorem _root_.SimpleGraph.Walk.parityCompatible [Fintype V] (B : Bipartition G)
    {x y : V} (p : G.Walk x y) : ParityCompatible B x y p.length :=
  B.even_length_iff_sameSide p

/-! ## Paths supported on a fixed finite vertex set -/

end Erdos63

namespace SimpleGraph.Walk

open Erdos63

universe u

variable {V : Type u}
variable {G G' : SimpleGraph V}

/-- Every vertex visited by a walk belongs to `S`. -/
def SupportsIn (p : G.Walk x y) (S : Finset V) : Prop :=
  ∀ z : V, z ∈ p.support → z ∈ S

theorem SupportsIn.start_mem {p : G.Walk x y} {S : Finset V}
    (h : p.SupportsIn S) : x ∈ S :=
  h x p.start_mem_support

theorem SupportsIn.end_mem {p : G.Walk x y} {S : Finset V}
    (h : p.SupportsIn S) : y ∈ S :=
  h y p.end_mem_support

theorem SupportsIn.mono {p : G.Walk x y} {S T : Finset V}
    (h : p.SupportsIn S) (hST : S ⊆ T) : p.SupportsIn T :=
  fun z hz ↦ hST (h z hz)

theorem SupportsIn.of_support_subset {p : G.Walk x y} {q : G.Walk x' y'}
    {S : Finset V} (h : p.SupportsIn S) (hqp : q.support ⊆ p.support) :
    q.SupportsIn S :=
  fun z hz ↦ h z (hqp hz)

@[simp] theorem supportsIn_nil_iff (x : V) (S : Finset V) :
    (Walk.nil : G.Walk x x).SupportsIn S ↔ x ∈ S := by
  simp [SupportsIn]

theorem SupportsIn.reverse {p : G.Walk x y} {S : Finset V}
    (h : p.SupportsIn S) : p.reverse.SupportsIn S := by
  intro z hz
  apply h z
  simpa [p.support_reverse] using hz

theorem SupportsIn.append {p : G.Walk x y} {q : G.Walk y z}
    {S : Finset V} (hp : p.SupportsIn S) (hq : q.SupportsIn S) :
    (p.append q).SupportsIn S := by
  intro w hw
  rcases (p.mem_support_append_iff q).1 hw with hw | hw
  · exact hp w hw
  · exact hq w hw

theorem SupportsIn.mapLe {G G' : SimpleGraph V} (hGG' : G ≤ G')
    {p : G.Walk x y} {S : Finset V} (h : p.SupportsIn S) :
    (p.mapLe hGG').SupportsIn S := by
  rw [SupportsIn, p.support_mapLe_eq_support]
  exact h

theorem supportsIn_iff_toFinset_subset [DecidableEq V]
    {p : G.Walk x y} {S : Finset V} :
    p.SupportsIn S ↔ p.support.toFinset ⊆ S := by
  constructor
  · intro h z hz
    exact h z (List.mem_toFinset.mp hz)
  · intro h z hz
    exact h (List.mem_toFinset.mpr hz)

end SimpleGraph.Walk

namespace Erdos63

attribute [local instance] Classical.propDecidable Classical.decEq

universe u

variable {V : Type u}
variable {G G' : SimpleGraph V}

/-! ## Bounded vertex expansions -/

/-- The induced-vertex-set form of a `(D,m)`-expansion about `root`. -/
structure BoundedVertexExpansion (G : SimpleGraph V) (root : V) (D m : ℕ) where
  /-- The vertices of the expansion. -/
  vertices : Finset V
  root_mem : root ∈ vertices
  card_vertices : vertices.card = D
  path_to : ∀ y : V, y ∈ vertices →
    ∃ p : G.Walk root y,
      p.IsPath ∧ p.length ≤ m ∧ p.SupportsIn vertices

namespace BoundedVertexExpansion

variable {root : V} {D m m' : ℕ}

theorem vertices_nonempty (E : BoundedVertexExpansion G root D m) :
    E.vertices.Nonempty := ⟨root, E.root_mem⟩

theorem one_le_size (E : BoundedVertexExpansion G root D m) : 1 ≤ D := by
  rw [← E.card_vertices]
  exact Finset.one_le_card.2 E.vertices_nonempty

theorem size_pos (E : BoundedVertexExpansion G root D m) : 0 < D :=
  E.one_le_size

theorem size_le_card [Fintype V] (E : BoundedVertexExpansion G root D m) :
    D ≤ Fintype.card V := by
  rw [← E.card_vertices]
  exact Finset.card_le_univ E.vertices

theorem exists_path_to (E : BoundedVertexExpansion G root D m)
    {y : V} (hy : y ∈ E.vertices) :
    ∃ p : G.Walk root y,
      p.IsPath ∧ p.length ≤ m ∧ p.SupportsIn E.vertices :=
  E.path_to y hy

theorem reachable (E : BoundedVertexExpansion G root D m)
    {y : V} (hy : y ∈ E.vertices) : G.Reachable root y := by
  obtain ⟨p, -, -, -⟩ := E.path_to y hy
  exact p.reachable

/-- The recorded paths also witness reachability in the graph induced by the
recorded vertex set.  This is the formal link with the induced-subgraph
formulation of a `(D,m)`-expansion. -/
theorem reachable_induce (E : BoundedVertexExpansion G root D m)
    {y : V} (hy : y ∈ E.vertices) :
    (G.induce (E.vertices : Set V)).Reachable
      ⟨root, E.root_mem⟩ ⟨y, hy⟩ := by
  obtain ⟨p, -, -, hsupp⟩ := E.path_to y hy
  exact (p.induce (E.vertices : Set V) hsupp).reachable

theorem connected_to_root (E : BoundedVertexExpansion G root D m)
    {y : V} (hy : y ∈ E.vertices) : G.Reachable y root :=
  (E.reachable hy).symm

/-- Any two vertices of an expansion are connected inside its vertex set by
a walk of length at most `2m`.  The concatenated walk need not itself be a
path, which is exactly the form needed for diameter estimates. -/
theorem exists_walk_between (E : BoundedVertexExpansion G root D m)
    {x y : V} (hx : x ∈ E.vertices) (hy : y ∈ E.vertices) :
    ∃ p : G.Walk x y, p.length ≤ 2 * m ∧ p.SupportsIn E.vertices := by
  obtain ⟨px, -, hpxlen, hpxsupport⟩ := E.path_to x hx
  obtain ⟨py, -, hpylen, hpysupport⟩ := E.path_to y hy
  refine ⟨px.reverse.append py, ?_, hpxsupport.reverse.append hpysupport⟩
  simp only [Walk.length_append, Walk.length_reverse]
  simpa [two_mul] using Nat.add_le_add hpxlen hpylen

theorem reachable_between (E : BoundedVertexExpansion G root D m)
    {x y : V} (hx : x ∈ E.vertices) (hy : y ∈ E.vertices) :
    G.Reachable x y := by
  obtain ⟨p, -, -⟩ := E.exists_walk_between hx hy
  exact p.reachable

/-- Increasing the allowed radius preserves a bounded expansion. -/
def radiusMono (E : BoundedVertexExpansion G root D m) (hmm' : m ≤ m') :
    BoundedVertexExpansion G root D m' where
  vertices := E.vertices
  root_mem := E.root_mem
  card_vertices := E.card_vertices
  path_to y hy := by
    obtain ⟨p, hp, hlen, hsupp⟩ := E.path_to y hy
    exact ⟨p, hp, hlen.trans hmm', hsupp⟩

@[simp] theorem radiusMono_vertices (E : BoundedVertexExpansion G root D m)
    (hmm' : m ≤ m') : (E.radiusMono hmm').vertices = E.vertices := rfl

/-- Passing to a supergraph preserves a bounded expansion. -/
def monoGraph (E : BoundedVertexExpansion G root D m) (hGG' : G ≤ G') :
    BoundedVertexExpansion G' root D m where
  vertices := E.vertices
  root_mem := E.root_mem
  card_vertices := E.card_vertices
  path_to y hy := by
    obtain ⟨p, hp, hlen, hsupp⟩ := E.path_to y hy
    exact ⟨p.mapLe hGG', hp.mapLe hGG', by simpa using hlen, hsupp.mapLe hGG'⟩

@[simp] theorem monoGraph_vertices (E : BoundedVertexExpansion G root D m)
    (hGG' : G ≤ G') : (E.monoGraph hGG').vertices = E.vertices := rfl

/-- Restrict the recorded vertex set when paths to all retained vertices are
known to remain in the retained set. -/
def restrictVertices (E : BoundedVertexExpansion G root D m) (T : Finset V)
    (hroot : root ∈ T) (D' : ℕ) (hcard : T.card = D')
    (hpaths : ∀ y : V, y ∈ T →
      ∃ p : G.Walk root y,
        p.IsPath ∧ p.length ≤ m ∧ p.SupportsIn T) :
    BoundedVertexExpansion G root D' m where
  vertices := T
  root_mem := hroot
  card_vertices := hcard
  path_to := hpaths

end BoundedVertexExpansion

end Erdos63
