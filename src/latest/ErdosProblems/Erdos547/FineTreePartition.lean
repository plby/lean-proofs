import ErdosProblems.Erdos547.FineSeparator
import ErdosProblems.Erdos547.ComponentPartition

/-!
# A finite fine partition of a rooted tree

The shrubs are actual disjoint induced subtrees.  Every edge leaving a shrub
goes to a cut vertex, and its one or two cut neighbours have a common colour.
-/

namespace Erdos547

open Finset SimpleGraph

variable {U : Type*} [Fintype U] [DecidableEq U]

structure FineTreePartition (T : SimpleGraph U) [DecidableRel T.Adj]
    (r : U) (ℓ : ℕ) (col : T.Coloring (Fin 2)) where
  seeds : Finset U
  shrubs : Finset (Finset U)
  root_mem : r ∈ seeds
  seeds_bound : ℓ * seeds.card ≤ 180 * Fintype.card U
  cover : seeds ∪ shrubs.biUnion id = Finset.univ
  disjoint_seeds : ∀ C ∈ shrubs, Disjoint C seeds
  disjoint_shrubs : ∀ C ∈ shrubs, ∀ D ∈ shrubs, C ≠ D → Disjoint C D
  shrub_tree : ∀ C ∈ shrubs, (T.induce (C : Set U)).IsTree
  shrub_size : ∀ C ∈ shrubs, C.card ≤ ℓ
  edge_exit : ∀ C ∈ shrubs, ∀ u ∈ C, ∀ v, T.Adj u v → v ∈ C ∨ v ∈ seeds
  has_attachment : ∀ C ∈ shrubs, ∃ z ∈ seeds, 0 < degreeIn T C z
  attachment_count : ∀ C ∈ shrubs, (seeds.filter (fun z ↦ 0 < degreeIn T C z)).card ≤ 2
  attachment_colour : ∀ C ∈ shrubs, ∀ u ∈ seeds, ∀ v ∈ seeds,
    0 < degreeIn T C u → 0 < degreeIn T C v → col u = col v
  attachment_distance : ∀ C ∈ shrubs, ∀ u ∈ seeds, ∀ v ∈ seeds,
    0 < degreeIn T C u → 0 < degreeIn T C v → u ≠ v → 6 ≤ T.dist u v

theorem nonempty_fine_tree_partition (T : SimpleGraph U) [DecidableRel T.Adj]
    (hT : T.IsTree) (r : U) (ℓ : ℕ) (hℓ : 2 ≤ ℓ) (hℓn : ℓ ≤ Fintype.card U)
    (col : T.Coloring (Fin 2)) : Nonempty (FineTreePartition T r ℓ col) := by
  classical
  obtain ⟨Z, hr, hcount, hfine⟩ := exists_fine_separator T hT r ℓ hℓ hℓn col
  obtain ⟨F, hcover, hpairwise, hpieces⟩ := exists_component_partition T Zᶜ
  have hdis (C : Finset U) (hC : C ∈ F) : Disjoint C Z := by
    apply Finset.disjoint_left.mpr
    intro u hu hz
    exact (Finset.mem_compl.mp ((hpieces C hC).1 hu)) hz
  have hconn (C : Finset U) (hC : C ∈ F) := (hpieces C hC).2.1
  have hexit (C : Finset U) (hC : C ∈ F) (u : U) (hu : u ∈ C) (v : U)
      (huv : T.Adj u v) : v ∈ C ∨ v ∈ Z := by
    by_cases hv : v ∈ Z
    · exact Or.inr hv
    · exact Or.inl ((hpieces C hC).2.2 u hu v (Finset.mem_compl.mpr hv) huv)
  have hattach (C : Finset U) (hC : C ∈ F) : ∃ z ∈ Z, 0 < degreeIn T C z := by
    have hne : (C : Set U).Nonempty := by
      obtain ⟨u⟩ := (hconn C hC).nonempty
      exact ⟨u.val, u.property⟩
    have hproper : (C : Set U) ≠ Set.univ := by
      intro he
      have hrC : r ∈ (C : Set U) := by rw [he]; exact Set.mem_univ _
      exact Finset.disjoint_left.mp (hdis C hC) hrC hr
    obtain ⟨u, hu, v, hv, huv⟩ := exists_boundary_edge hT.connected.preconnected
      (C : Set U) hne hproper
    have hvZ : v ∈ Z := (hexit C hC u hu v huv).resolve_left hv
    exact ⟨v, hvZ, Finset.card_pos.mpr ⟨u, Finset.mem_filter.mpr ⟨hu, huv.symm⟩⟩⟩
  refine ⟨{
    seeds := Z
    shrubs := F
    root_mem := hr
    seeds_bound := hcount
    cover := ?_
    disjoint_seeds := hdis
    disjoint_shrubs := hpairwise
    shrub_tree := fun C hC ↦ ⟨hconn C hC, hT.isAcyclic.induce _⟩
    shrub_size := fun C hC ↦ (hfine C (hdis C hC) (hconn C hC)).1
    edge_exit := hexit
    has_attachment := hattach
    attachment_count := fun C hC ↦ (hfine C (hdis C hC) (hconn C hC)).2.1
    attachment_colour := ?_
    attachment_distance := ?_
  }⟩
  · rw [hcover]
    simp
  · intro C hC u hu v hv hdu hdv
    exact ((hfine C (hdis C hC) (hconn C hC)).2.2 u hu v hv hdu hdv).1
  · intro C hC u hu v hv hdu hdv huv
    exact ((hfine C (hdis C hC) (hconn C hC)).2.2 u hu v hv hdu hdv).2 huv

end Erdos547

#print axioms Erdos547.nonempty_fine_tree_partition
