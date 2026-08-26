/-
Copyright (c) 2026 Samuil Petkov. Licensed under CC BY 4.0.
Definitions adapted for independent statement checking.
-/
import Mathlib

open scoped Cardinal

namespace Erdos593

universe u v w x

namespace SimpleGraph

/-- A bridge must be an actual edge as well as disconnecting its endpoints upon deletion. -/
def bridgeEdges {V : Type u} (G : _root_.SimpleGraph V) : Set (Sym2 V) :=
  {e | e ∈ G.edgeSet ∧ G.IsBridge e}

end SimpleGraph

/-- A simple hypergraph in which each indexed edge contains exactly three vertices. -/
structure TripleSystem (V : Type u) (E : Type v) where
  Inc : V → E → Prop
  edge_ncard : ∀ e, Set.ncard {x | Inc x e} = 3
  simple : Function.Injective (fun e => {x | Inc x e})

namespace TripleSystem

variable {V : Type u} {E : Type v} (F : TripleSystem V E)

def IsIsolated (x : V) : Prop :=
  ∀ e, ¬F.Inc x e

def Linear : Prop :=
  ∀ ⦃e f : E⦄ ⦃x y : V⦄, e ≠ f →
    F.Inc x e → F.Inc x f → F.Inc y e → F.Inc y f → x = y

def edgeSet (e : E) : Set V :=
  {x | F.Inc x e}

/-- Vertex injections preserve source edges; extra host edges are allowed. -/
structure Embedding {V : Type u} {E : Type v} {W : Type w} {D : Type x}
    (F : TripleSystem V E) (H : TripleSystem W D) where
  vertex : V ↪ W
  edge : E → D
  map_edge : ∀ e, vertex '' F.edgeSet e = H.edgeSet (edge e)

def IsProperColoring {C : Type w} (c : V → C) : Prop :=
  ∀ e : E, ∃ x : V, F.Inc x e ∧ ∃ y : V, F.Inc y e ∧ c x ≠ c y

noncomputable def chromaticCardinal : Cardinal.{u} :=
  sInf {k : Cardinal.{u} | ∃ C : Type u, #C = k ∧
    ∃ c : V → C, F.IsProperColoring c}

def Appears {W : Type u} {D : Type v}
    (F : TripleSystem V E) (H : TripleSystem W D) : Prop :=
  Nonempty (F.Embedding H)

/-- Host hypergraphs are unrestricted in size. -/
def IsObligatory : Prop :=
  ∀ (W : Type u) (D : Type v) [DecidableEq W]
    (H : TripleSystem W D), ℵ₀ < H.chromaticCardinal → F.Appears H

theorem not_isolated_of_inc {x : V} {e : E} (hxe : F.Inc x e) :
    ¬F.IsIsolated x := by
  intro hx
  exact hx e hxe

abbrev NonIsolatedPoint :=
  {x : V // ¬F.IsIsolated x}

/-- Delete isolated points without changing the edges. -/
def isolatedReduction : TripleSystem F.NonIsolatedPoint E where
  Inc x e := F.Inc x.1 e
  edge_ncard := by
    intro e
    change Set.ncard {x : F.NonIsolatedPoint |
      (x : V) ∈ {y : V | F.Inc y e}} = 3
    rw [Set.ncard_subtype]
    have hsubset : {x : V | F.Inc x e} ⊆ {x : V | ¬F.IsIsolated x} := by
      intro x hx
      exact F.not_isolated_of_inc hx
    rw [Set.inter_eq_left.mpr hsubset]
    exact F.edge_ncard e
  simple := by
    intro e f hef
    apply F.simple
    ext x
    constructor
    · intro hxe
      let x' : F.NonIsolatedPoint := ⟨x, F.not_isolated_of_inc hxe⟩
      have hiff := Set.ext_iff.mp hef x'
      exact hiff.mp hxe
    · intro hxf
      let x' : F.NonIsolatedPoint := ⟨x, F.not_isolated_of_inc hxf⟩
      have hiff := Set.ext_iff.mp hef x'
      exact hiff.mpr hxf

def incidenceRel : V ⊕ E → V ⊕ E → Prop
  | .inl x, .inr e => F.Inc x e
  | _, _ => False

/-- The bipartite incidence graph, with vertices on one side and hyperedges on the other. -/
def levi : _root_.SimpleGraph (V ⊕ E) :=
  _root_.SimpleGraph.fromRel F.incidenceRel

def BridgeAtEveryEdge : Prop :=
  ∀ e : E, ∃ x : V,
    s(Sum.inl x, Sum.inr e) ∈ SimpleGraph.bridgeEdges F.levi

/-- Berge-cycle lengths are half the corresponding incidence-graph cycle lengths. -/
def EvenBergeCycles : Prop :=
  ∀ ⦃z : V ⊕ E⦄ (c : F.levi.Walk z z), c.IsCycle → 4 ∣ c.length

end TripleSystem

theorem erdos_593 {V E : Type u} (F : TripleSystem V E) [Fintype V] [Fintype E] :
    F.IsObligatory ↔
      F.isolatedReduction.Linear ∧
      F.isolatedReduction.BridgeAtEveryEdge ∧
      F.isolatedReduction.EvenBergeCycles := by
  sorry

end Erdos593
