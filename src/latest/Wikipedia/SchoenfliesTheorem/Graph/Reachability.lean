import Wikipedia.SchoenfliesTheorem.Graph.Walk
import Mathlib.Logic.Relation

/-!
# Adjacency-based reachability and explicit walks

`Graph.Reachable` is the reflexive-transitive closure of adjacency. Unlike
`Graph.Reaches`, it permits a stationary chain outside the vertex set. On actual
vertices the two notions agree, so both presentations use the same
`Graph.Connected` definition from `Graph.Walk`.
-/

namespace Graph

variable {α β : Type*} {G : Graph α β} {u v : α} {W : List β}

/-- Reachability by a finite chain of adjacent vertices. -/
def Reachable (G : Graph α β) (u v : α) : Prop :=
  Relation.ReflTransGen G.Adj u v

theorem IsWalk.reachable (h : G.IsWalk u W v) : G.Reachable u v := by
  induction h with
  | nil => exact Relation.ReflTransGen.refl
  | cons hl _ ih => exact (Relation.ReflTransGen.single ⟨_, hl⟩).trans ih

theorem Reaches.reachable (h : G.Reaches u v) : G.Reachable u v :=
  h.choose_spec.reachable

theorem Reachable.reaches (h : G.Reachable u v) (hu : u ∈ G.vertexSet) :
    G.Reaches u v := by
  induction h with
  | refl => exact Reaches.refl hu
  | tail _ hab ih => exact ih.trans (Reaches.of_adj hab)

/-- The vertex-membership condition accounts for stationary adjacency chains. -/
theorem reaches_iff_mem_and_reachable :
    G.Reaches u v ↔ u ∈ G.vertexSet ∧ G.Reachable u v :=
  ⟨fun h ↦ ⟨h.left_mem, h.reachable⟩, fun ⟨hu, h⟩ ↦ h.reaches hu⟩

theorem reaches_iff_reachable (hu : u ∈ G.vertexSet) :
    G.Reaches u v ↔ G.Reachable u v :=
  ⟨Reaches.reachable, fun h ↦ h.reaches hu⟩

/-- Connectedness can equivalently be stated using adjacency chains. -/
theorem connected_iff_pairwise_reachable :
    G.Connected ↔ G.vertexSet.Nonempty ∧
      ∀ ⦃u v : α⦄, u ∈ G.vertexSet → v ∈ G.vertexSet → G.Reachable u v := by
  constructor
  · intro h
    exact ⟨h.nonempty, fun {_ _} hu hv ↦ (h.reaches hu hv).reachable⟩
  · rintro ⟨hne, h⟩
    exact ⟨hne, fun {_} hu {_} hv ↦ (h hu hv).reaches hu⟩

end Graph
