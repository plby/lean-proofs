/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos79.Core

/-!
# Recoding an arbitrary finite graph on `Fin`

`GraphCode` uses a canonical finite ordinal as vertex type.  This file
packages Mathlib's `overFin` construction so later graph transformations can
be carried out on convenient subtype vertex sets and recoded only at their
boundary.
-/

open scoped SimpleGraph

noncomputable section

namespace Erdos570

open Erdos79

/-- Canonical `GraphCode` associated with a graph on an arbitrary finite
vertex type. -/
def recodeGraph {V : Type*} [Fintype V] (G : SimpleGraph V) : GraphCode :=
  ⟨Fintype.card V, G.overFin rfl⟩

@[simp] theorem recodeGraph_vertexCount {V : Type*} [Fintype V]
    (G : SimpleGraph V) :
    (recodeGraph G).vertexCount = Fintype.card V := rfl

/-- The canonical graph isomorphism into the recoded graph. -/
def recodeGraphIso {V : Type*} [Fintype V] (G : SimpleGraph V) :
    G ≃g (recodeGraph G).graph := by
  change G ≃g G.overFin (by rfl)
  exact SimpleGraph.overFinIso (G := G) rfl

theorem recodeGraph_isomorphic {V : Type*} [Fintype V]
    (G : SimpleGraph V) :
    Nonempty (G ≃g (recodeGraph G).graph) :=
  ⟨recodeGraphIso G⟩

@[simp] theorem recodeGraph_edgeCount {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (recodeGraph G).edgeCount = G.edgeFinset.card := by
  classical
  letI : DecidableRel (recodeGraph G).graph.Adj := Classical.decRel _
  rw [GraphCode.edgeCount_eq_card_edgeFinset]
  exact (recodeGraphIso G).card_edgeFinset_eq.symm

theorem recodeGraph_noIsolated_iff {V : Type*} [Fintype V]
    (G : SimpleGraph V) :
    NoIsolated (recodeGraph G) ↔ ∀ v : V, ¬ G.IsIsolated v := by
  constructor
  · intro h v
    rw [← G.exists_adj_iff_not_isIsolated]
    obtain ⟨w, hw⟩ :=
      (recodeGraph G).graph.exists_adj_iff_not_isIsolated.mpr
        (h (recodeGraphIso G v))
    refine ⟨(recodeGraphIso G).symm w, ?_⟩
    have hm := (recodeGraphIso G).symm.toHom.map_adj hw
    change G.Adj ((recodeGraphIso G).symm (recodeGraphIso G v))
      ((recodeGraphIso G).symm w) at hm
    have hev : (recodeGraphIso G).symm (recodeGraphIso G v) = v :=
      (recodeGraphIso G).symm_apply_apply v
    rw [hev] at hm
    exact hm
  · intro h v
    rw [← (recodeGraph G).graph.exists_adj_iff_not_isIsolated]
    let x := (recodeGraphIso G).symm v
    obtain ⟨y, hxy⟩ := G.exists_adj_iff_not_isIsolated.mpr (h x)
    refine ⟨recodeGraphIso G y, ?_⟩
    have hm := (recodeGraphIso G).toHom.map_adj hxy
    change (recodeGraph G).graph.Adj (recodeGraphIso G x)
      (recodeGraphIso G y) at hm
    have hex : recodeGraphIso G x = v := by
      dsimp only [x]
      exact (recodeGraphIso G).apply_symm_apply v
    rw [hex] at hm
    exact hm

theorem recodeGraph_connected_iff {V : Type*} [Fintype V]
    (G : SimpleGraph V) :
    (recodeGraph G).graph.Connected ↔ G.Connected := by
  exact (recodeGraphIso G).connected_iff.symm

/-- A recoded graph is contained in a host exactly when its original
finite-type presentation is. -/
theorem recodeGraph_isContained_iff {V W : Type*} [Fintype V]
    (G : SimpleGraph V) (C : SimpleGraph W) :
    (recodeGraph G).graph ⊑ C ↔ G ⊑ C := by
  constructor
  · intro h
    exact (recodeGraphIso G).isContained.trans h
  · intro h
    exact (recodeGraphIso G).symm.isContained.trans h

end Erdos570
