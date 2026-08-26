import ErdosProblems.Erdos593.Graph.CountableColoring
import ErdosProblems.Erdos593.TripleSystem.Obligatory
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Data.Nat.Pairing

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Predicate-local colourings of triple systems

This module separates colouring a selected family of host edges from colouring
the whole triple system.  The selected family is represented by a predicate on
edge indices, so it remains compatible with the project's edge-indexed model
and does not require constructing a restricted triple system first.

The graph bridge records the elementary but frequently used observation that a
proper colouring of a graph colours every hyperedge which contains an edge of
that graph.
-/

namespace Erdos593

universe u v w x

namespace TripleSystem

variable {W : Type u} {D : Type v} (H : TripleSystem W D)

/-- A colouring is proper on the edge indices satisfying `P` when each such
hyperedge contains two vertices of different colours. -/
def IsProperColoringOn {C : Type w} (P : D → Prop) (c : W → C) : Prop :=
  ∀ e : D, P e → ∃ x : W, H.Inc x e ∧ ∃ y : W, H.Inc y e ∧ c x ≠ c y

/-- A selected family of edges is countably colourable when it has a proper
colouring by natural numbers. -/
def CountablyColorableOn (P : D → Prop) : Prop :=
  ∃ c : W → ℕ, H.IsProperColoringOn P c

/-- An indexed hyperedge contains an edge of `G`. -/
def EdgeContainsGraphEdge (G : _root_.SimpleGraph W) : D → Prop := fun e =>
  ∃ x y : W, H.Inc x e ∧ H.Inc y e ∧ G.Adj x y

theorem IsProperColoringOn.mono {P Q : D → Prop} {C : Type w} {c : W → C}
    (hc : H.IsProperColoringOn Q c) (hPQ : ∀ e, P e → Q e) :
    H.IsProperColoringOn P c := by
  intro e he
  exact hc e (hPQ e he)

/-- The empty edge family is properly coloured by every colouring. -/
theorem isProperColoringOn_empty {C : Type w} (c : W → C) :
    H.IsProperColoringOn (fun _ => False) c := by
  intro e he
  exact False.elim he

/-- Combine colourings of two edge families by pairing their colour values. -/
theorem IsProperColoringOn.union
    {P Q : D → Prop} {C₁ : Type w} {C₂ : Type x}
    {c₁ : W → C₁} {c₂ : W → C₂}
    (hc₁ : H.IsProperColoringOn P c₁)
    (hc₂ : H.IsProperColoringOn Q c₂) :
    H.IsProperColoringOn (fun e => P e ∨ Q e) (fun z => (c₁ z, c₂ z)) := by
  intro e he
  rcases he with he | he
  · rcases hc₁ e he with ⟨a, hae, b, hbe, hab⟩
    refine ⟨a, hae, b, hbe, ?_⟩
    intro hEq
    exact hab (congrArg Prod.fst hEq)
  · rcases hc₂ e he with ⟨a, hae, b, hbe, hab⟩
    refine ⟨a, hae, b, hbe, ?_⟩
    intro hEq
    exact hab (congrArg Prod.snd hEq)

theorem CountablyColorableOn.mono {P Q : D → Prop}
    (hQ : H.CountablyColorableOn Q) (hPQ : ∀ e, P e → Q e) :
    H.CountablyColorableOn P := by
  rcases hQ with ⟨c, hc⟩
  exact ⟨c, IsProperColoringOn.mono H hc hPQ⟩

/-- Two countably colourable edge families have countably colourable union.
The natural-number pairing is injective in each coordinate. -/
theorem CountablyColorableOn.union {P Q : D → Prop}
    (hP : H.CountablyColorableOn P) (hQ : H.CountablyColorableOn Q) :
    H.CountablyColorableOn (fun e => P e ∨ Q e) := by
  rcases hP with ⟨cP, hcP⟩
  rcases hQ with ⟨cQ, hcQ⟩
  refine ⟨fun z => Nat.pair (cP z) (cQ z), ?_⟩
  intro e he
  rcases he with he | he
  · rcases hcP e he with ⟨a, hae, b, hbe, hab⟩
    refine ⟨a, hae, b, hbe, ?_⟩
    intro hEq
    exact hab (Nat.pair_eq_pair.mp hEq).1
  · rcases hcQ e he with ⟨a, hae, b, hbe, hab⟩
    refine ⟨a, hae, b, hbe, ?_⟩
    intro hEq
    exact hab (Nat.pair_eq_pair.mp hEq).2

/-- A proper graph colouring is proper on every host edge containing an edge
of that graph. -/
theorem isProperColoringOn_edgeContainsGraphEdge
    {G : _root_.SimpleGraph W} {C : Type w} (c : G.Coloring C) :
    H.IsProperColoringOn (H.EdgeContainsGraphEdge G) (fun z => c z) := by
  intro e he
  rcases he with ⟨a, b, hae, hbe, hab⟩
  exact ⟨a, hae, b, hbe, c.valid hab⟩

/-- A countable graph colouring colours the hyperedges containing graph
edges.  Instantiate this with `highPairGraph H t` for the high-pair part of a
host. -/
theorem countablyColorableOn_edgeContainsGraphEdge
    {G : _root_.SimpleGraph W} (hG : Erdos593.SimpleGraph.CountablyColorable G) :
    H.CountablyColorableOn (H.EdgeContainsGraphEdge G) := by
  rcases hG with ⟨c⟩
  exact ⟨fun z => c z, H.isProperColoringOn_edgeContainsGraphEdge c⟩

end TripleSystem

end Erdos593
