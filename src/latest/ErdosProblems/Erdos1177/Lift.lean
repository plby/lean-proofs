-- Modified for this repository: Lean 4.33.0 port and Erdos1177 namespace.
import Mathlib

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# The complete-rank one-apex lift and its chromatic number

This file formalizes the central self-contained construction of

  Eric Li, *A Resolution of Erdős Problems 593 and 1177: Obligatory Triple
  Systems and Exact Spectra*, arXiv:2606.24882,

namely the *complete-rank one-apex lift* `Lift(A, κ)` of a graph `A`
(Section 3) and the theorem that `χ(Lift(A,κ)) = κ` whenever `χ(A) = κ`
(Theorem `thm:lift-chromatic`).  This is a ZFC theorem and is proved here
in full, with no appeal to any of the paper's imported external results.

## Design notes

* A *hypergraph* is a set of edges (each a set of vertices).  A colouring
  `c : V → C` is *proper* if no edge is monochromatic.  `ColorableBy H θ`
  means there is a proper colouring into a set of cardinality `θ`, and
  `HasChromatic H κ` means `χ(H) = κ`.

* Transfinite sequences of edges of `A` of ordinal length `< κ` are encoded,
  staying inside a single universe, by using `κ.ord.ToType` (a `Type u`
  carrying the well-order of the ordinal `κ.ord`).  A `Node` is a position
  `p : κ.ord.ToType` together with a choice of edge at every earlier index.
-/

open Cardinal Ordinal

namespace Erdos1177

universe u

/-- A hypergraph on vertex type `V` is a set of edges, each edge a set of
vertices. -/
structure Hypergraph (V : Type u) where
  edges : Set (Set V)

/-- A colouring `c : V → C` is *proper* for `H` if no edge of `H` is
monochromatic, i.e. every edge has two vertices of different colour. -/
def Hypergraph.ProperColoring {V : Type u} {C : Type*} (H : Hypergraph V)
    (c : V → C) : Prop :=
  ∀ e ∈ H.edges, ∃ u ∈ e, ∃ v ∈ e, c u ≠ c v

/-- `H` is colourable with `θ` colours if it has a proper colouring into a
type of cardinality `θ`. -/
def Hypergraph.ColorableBy {V : Type u} (H : Hypergraph V) (θ : Cardinal.{u}) :
    Prop :=
  ∃ c : V → θ.out, H.ProperColoring c

/-- `H` has (weak) chromatic number `κ`: it is colourable with `κ` colours,
but not with any smaller number of colours. -/
def Hypergraph.HasChromatic {V : Type u} (H : Hypergraph V) (κ : Cardinal.{u}) :
    Prop :=
  H.ColorableBy κ ∧ ∀ θ, θ < κ → ¬ H.ColorableBy θ

/-- The hypergraph associated to a simple graph: its edges are the
two-element sets `{x, y}` with `x` adjacent to `y`. -/
def SimpleGraph.toHG {α : Type u} (A : SimpleGraph α) : Hypergraph α :=
  ⟨{ e | ∃ x y, A.Adj x y ∧ e = ({x, y} : Set α) }⟩

section Lift

variable {α : Type u} (A : SimpleGraph α) (κ : Cardinal.{u})

/-- Index type for transfinite positions: elements of the order type of the
ordinal `κ.ord`.  It is a `Type u` carrying a well-order. -/
abbrev Idx := κ.ord.ToType

/-- A node of the lift's coordinate tree: a position `pos` and a choice of an
edge of `A` at every strictly smaller position. -/
structure Node where
  pos : Idx κ
  seq : {q : Idx κ // q < pos} → A.edgeSet

/-- The edge `{x, y}` of `A`, as an element of `A.edgeSet`, from adjacency. -/
def edgeOf {x y : α} (h : A.Adj x y) : A.edgeSet := ⟨s(x, y), by simpa using! h⟩

/-- `σ` is a proper prefix of `τ`: `σ.pos < τ.pos` and they agree at every
index below `σ.pos`. -/
def Node.pre (σ τ : Node A κ) : Prop :=
  ∃ h : σ.pos < τ.pos, ∀ (q : Idx κ) (hq : q < σ.pos),
     τ.seq ⟨q, lt_trans hq h⟩ = σ.seq ⟨q, hq⟩

/-- The complete-rank one-apex lift `Lift(A, κ)`.  Its vertices are pairs
`(node, vertex of A)`.  Its edges are the triples
`{(σ,x), (σ,y), (τ,z)}` where `σ` is a proper prefix of `τ`, the edge of `τ`
at coordinate `σ.pos` is `{x, y}`, and `z` is any vertex of `A`. -/
def liftHG : Hypergraph (Node A κ × α) :=
  ⟨ { s | ∃ (σ τ : Node A κ) (x y z : α) (hpre : Node.pre A κ σ τ),
        (τ.seq ⟨σ.pos, hpre.1⟩ : Sym2 α) = s(x, y) ∧
        s = ({(σ, x), (σ, y), (τ, z)} : Set (Node A κ × α)) } ⟩

/-
Every edge of `Lift(A, κ)` consists of exactly three distinct vertices, so
`Lift(A, κ)` is genuinely a triple system.
-/
theorem liftHG_isTripleSystem :
    ∀ e ∈ (liftHG A κ).edges, ∃ a b c : Node A κ × α,
      a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ e = {a, b, c} := by
  intro e he
  obtain ⟨σ, τ, x, y, z, hpre, h_edge⟩ := (Set.mem_setOf.mp he);
  refine' ⟨ ( σ, x ), ( σ, y ), ( τ, z ), _, _, _, h_edge.2 ⟩ <;> simp_all +decide only [ne_eq, Prod.mk.injEq, not_and, true_and] ;
  · intro h; simp_all +decide ;
    exact absurd h_edge.1 ( by exact fun h => by have := τ.seq ⟨ σ.pos, hpre.1 ⟩ |>.2; aesop );
  · rintro rfl; exact absurd hpre.1 (lt_irrefl _)
  · rintro rfl; exact absurd hpre.1 ( lt_irrefl _ ) ;

end Lift

/-
A colouring of the graph `A` (via `toHG`) is proper iff adjacent vertices
get different colours.
-/
theorem toHG_proper_iff {α : Type u} (A : SimpleGraph α) {C : Type*}
    (c : α → C) :
    (SimpleGraph.toHG A).ProperColoring c ↔ ∀ x y, A.Adj x y → c x ≠ c y := by
  simp [SimpleGraph.toHG, Hypergraph.ProperColoring];
  grind

/-
If `A` is not `θ`-colourable then every colouring of its vertices by `θ`
colours has a monochromatic edge.
-/
theorem exists_mono_edge {α : Type u} {A : SimpleGraph α} {θ : Cardinal.{u}}
    (hA : ¬ (SimpleGraph.toHG A).ColorableBy θ) (g : α → θ.out) :
    ∃ x y, A.Adj x y ∧ g x = g y := by
  contrapose! hA;
  exact ⟨ g, fun e he => by rcases he with ⟨ x, y, hxy, rfl ⟩ ; exact ⟨ x, by simp, y, by simp, hA x y hxy ⟩ ⟩

/-
**Upper bound** for the lift's chromatic number: a proper `κ`-colouring
of `A` induces a proper `κ`-colouring of `Lift(A,κ)` (colour a lift vertex by
the `A`-colour of its second coordinate).
-/
theorem lift_colorableBy {α : Type u} (A : SimpleGraph α) (κ : Cardinal.{u})
    (hA : (SimpleGraph.toHG A).ColorableBy κ) :
    (liftHG A κ).ColorableBy κ := by
  obtain ⟨c, hc⟩ := hA;
  refine' ⟨ fun ⟨ σ, x ⟩ => c x, _ ⟩;
  intro e he
  obtain ⟨σ, τ, x, y, z, hpre, hseq, rfl⟩ := he;
  have := hc ( τ.seq ⟨ σ.pos, hpre.1 ⟩ : Set α ) ?_ <;> simp_all +decide [ SimpleGraph.toHG ];
  · tauto;
  · cases h : τ.seq ⟨ σ.pos, hpre.1 ⟩ ; aesop

section LowerBound

variable {α : Type u} (A : SimpleGraph α) (κ : Cardinal.{u})
  {θ : Cardinal.{u}} (c : Node A κ × α → θ.out)
  (hA : ¬ (SimpleGraph.toHG A).ColorableBy θ)

/-- One step of the branch recursion: given the branch below position `a`,
build the node at `a` and choose a monochromatic edge of `A` for the induced
colouring `x ↦ c(node, x)`. -/
noncomputable def stepEdge (a : Idx κ)
    (g : (q : Idx κ) → q < a → {p : α × α // A.Adj p.1 p.2}) :
    {p : α × α // A.Adj p.1 p.2} :=
  let node : Node A κ := ⟨a, fun q => edgeOf A (g q.1 q.2).2⟩
  let h := exists_mono_edge hA (fun x => c (node, x))
  ⟨(Classical.choose h, Classical.choose (Classical.choose_spec h)),
   (Classical.choose_spec (Classical.choose_spec h)).1⟩

/-- The branch: for every position `a`, the monochromatic edge chosen at `a`,
built by well-founded recursion on the position order. -/
noncomputable def branch : Idx κ → {p : α × α // A.Adj p.1 p.2} :=
  WellFounded.fix wellFounded_lt (stepEdge A κ c hA)

theorem branch_eq (a : Idx κ) :
    branch A κ c hA a = stepEdge A κ c hA a (fun q _ => branch A κ c hA q) :=
  WellFounded.fix_eq _ _ _

/-- The node at position `a` determined by the global branch. -/
noncomputable def branchNode (a : Idx κ) : Node A κ :=
  ⟨a, fun q => edgeOf A (branch A κ c hA q.1).2⟩

/-
The edge chosen at `a` is monochromatic for the colouring `x ↦ c(node_a, x)`:
the two endpoints get the same colour.
-/
theorem branch_mono (a : Idx κ) :
    c (branchNode A κ c hA a, (branch A κ c hA a).1.1)
      = c (branchNode A κ c hA a, (branch A κ c hA a).1.2) := by
  rw [ branch_eq ];
  convert! Classical.choose_spec ( Classical.choose_spec ( exists_mono_edge hA ( fun x => c ( branchNode A κ c hA a, x ) ) ) ) |>.2

/-
The edge of `branchNode b` at coordinate `a`, for `a < b`, is exactly the
edge chosen by the branch at `a`.
-/
theorem branchNode_seq (a b : Idx κ) (hab : a < b) :
    ((branchNode A κ c hA b).seq ⟨a, hab⟩ : Sym2 α)
      = s((branch A κ c hA a).1.1, (branch A κ c hA a).1.2) := by
  rfl

/-
**Lower bound** for the lift's chromatic number: if `A` is not
`θ`-colourable and `θ < κ`, then `Lift(A,κ)` is not `θ`-colourable.
-/
theorem lift_not_colorableBy (hA : ¬ (SimpleGraph.toHG A).ColorableBy θ)
    (hθ : θ < κ) :
    ¬ (liftHG A κ).ColorableBy θ := by
  intro hLift;
  -- Define the "stage colour" `d : Idx κ → θ.out` by `d a := c (branchNode A κ c hA a, (branch A κ c hA a).1.1)`.
  obtain ⟨c, hc⟩ := hLift
  set d : Idx κ → θ.out := fun a => c (branchNode A κ c hA a, (branch A κ c hA a).1.1);
  -- By `lt_trichotomy a b`, and by symmetry of the roles of `a,b` (since `d a = d b`), assume `a < b` (the case `b < a` is identical with `a,b` swapped; `a = b` is excluded).
  obtain ⟨a, b, hab, hd⟩ : ∃ a b : Idx κ, a < b ∧ d a = d b := by
    by_contra! h;
    have h_card : Cardinal.mk (Idx κ) ≤ Cardinal.mk (Quotient.out θ) := by
      exact Cardinal.mk_le_of_injective ( show Function.Injective d from fun a b hab => le_antisymm ( le_of_not_gt fun h' => h _ _ h' hab.symm ) ( le_of_not_gt fun h' => h _ _ h' hab ) );
    simp_all +decide [ Cardinal.mk_toType ];
    exact not_lt_of_ge h_card hθ;
  obtain ⟨ u, hu, v, hv, huv ⟩ := hc { ( branchNode A κ c hA a, ( branch A κ c hA a ).1.1 ), ( branchNode A κ c hA a, ( branch A κ c hA a ).1.2 ), ( branchNode A κ c hA b, ( branch A κ c hA b ).1.1 ) } ⟨ branchNode A κ c hA a, branchNode A κ c hA b, ( branch A κ c hA a ).1.1, ( branch A κ c hA a ).1.2, ( branch A κ c hA b ).1.1, ⟨ hab, fun q hq => rfl ⟩, by
    convert! branchNode_seq A κ c hA a b hab, rfl ⟩ ; simp_all +decide [ Set.mem_insert_iff, Set.mem_singleton_iff ];
  rcases hu with ( rfl | rfl | rfl ) <;> rcases hv with ( rfl | rfl | rfl ) <;> simp_all +decide [ branch_mono ]; all_goals have := branch_mono A κ c hA a; have := branch_mono A κ c hA b; aesop;

end LowerBound

/--
**Theorem (`thm:lift-chromatic`).** If `χ(A) = κ`, then `χ(Lift(A,κ)) = κ`.
(The paper states this for infinite `κ`; the argument here needs no such
assumption, matching the paper's remark that no regularity or cofinality of
`κ` is used.)
-/
theorem lift_hasChromatic {α : Type u} (A : SimpleGraph α) (κ : Cardinal.{u})
    (hA : (SimpleGraph.toHG A).HasChromatic κ) :
    (liftHG A κ).HasChromatic κ := by
  refine' ⟨ lift_colorableBy A κ hA.1, fun θ hθ => _ ⟩;
  apply lift_not_colorableBy A κ;
  · exact hA.2 θ hθ;
  · exact hθ

end Erdos1177
