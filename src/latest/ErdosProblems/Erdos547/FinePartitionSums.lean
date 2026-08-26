import ErdosProblems.Erdos547.FineTreePartition
import ErdosProblems.Erdos547.HighDegreeCore

/-!
# Summing vertices and degrees across a fine tree partition
-/

namespace Erdos547

open Finset SimpleGraph
open scoped BigOperators

variable {U I : Type*} [Fintype U] [DecidableEq U]
variable (T : SimpleGraph U) [DecidableRel T.Adj]

theorem degreeIn_biUnion_of_disjoint (J : Finset I) (C : I → Finset U)
    (hdis : ∀ i ∈ J, ∀ j ∈ J, i ≠ j → Disjoint (C i) (C j)) (v : U) :
    degreeIn T (J.biUnion C) v = ∑ i ∈ J, degreeIn T (C i) v := by
  unfold degreeIn
  rw [Finset.filter_biUnion, Finset.card_biUnion]
  exact fun i hi j hj hij ↦ (hdis i hi j hj hij).mono
    (Finset.filter_subset _ _) (Finset.filter_subset _ _)

theorem degree_eq_degreeIn_of_neighbours {S : Finset U} (v : U)
    (hS : ∀ u, T.Adj v u → u ∈ S) : T.degree v = degreeIn T S v := by
  rw [← degreeIn_univ]
  unfold degreeIn
  congr 1
  ext u
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun h ↦ ⟨hS u h, h⟩, And.right⟩

namespace FineTreePartition

variable {T} {r : U} {ℓ : ℕ} {col : T.Coloring (Fin 2)}
variable (P : FineTreePartition T r ℓ col)

theorem seeds_disjoint_shrub_union : Disjoint P.seeds (P.shrubs.biUnion id) := by
  apply Finset.disjoint_left.mpr
  intro u hu hs
  obtain ⟨S, hS, huS⟩ := Finset.mem_biUnion.mp hs
  exact Finset.disjoint_left.mp (P.disjoint_seeds S hS) huS hu

theorem sum_over_partition {M : Type*} [AddCommMonoid M] (f : U → M) :
    (∑ v, f v) = (∑ v ∈ P.seeds, f v) + ∑ S ∈ P.shrubs, ∑ v ∈ S, f v := by
  rw [← P.cover, Finset.sum_union P.seeds_disjoint_shrub_union]
  rw [Finset.sum_biUnion (show (P.shrubs : Set (Finset U)).PairwiseDisjoint id from
    fun S hS Q hQ hne ↦ P.disjoint_shrubs S hS Q hQ hne)]
  rfl

theorem card_partition : P.seeds.card + (∑ S ∈ P.shrubs, S.card) = Fintype.card U := by
  simpa using (P.sum_over_partition (fun _ ↦ (1 : ℕ))).symm

theorem degree_from_partition (v : U) : T.degree v =
    degreeIn T P.seeds v + ∑ S ∈ P.shrubs, degreeIn T S v := by
  rw [← degreeIn_univ, ← P.cover, degreeIn_union T P.seeds_disjoint_shrub_union,
    degreeIn_biUnion_of_disjoint T P.shrubs id P.disjoint_shrubs]
  rfl

theorem degree_of_shrub_vertex (S : Finset U) (hS : S ∈ P.shrubs) (v : U) (hv : v ∈ S) :
    T.degree v = degreeIn T S v + degreeIn T P.seeds v := by
  rw [degree_eq_degreeIn_of_neighbours T v (S := S ∪ P.seeds)
    (fun u h ↦ Finset.mem_union.mpr (P.edge_exit S hS v hv u h)),
    degreeIn_union T (P.disjoint_seeds S hS)]

theorem sum_degrees_partition : (∑ v, T.degree v) =
    (∑ v ∈ P.seeds, degreeIn T P.seeds v) +
      2 * (∑ S ∈ P.shrubs, ∑ v ∈ P.seeds, degreeIn T S v) +
        ∑ S ∈ P.shrubs, ∑ v ∈ S, degreeIn T S v := by
  have hseeds : (∑ v ∈ P.seeds, T.degree v) =
      (∑ v ∈ P.seeds, degreeIn T P.seeds v) +
        ∑ S ∈ P.shrubs, ∑ v ∈ P.seeds, degreeIn T S v := by
    simp_rw [P.degree_from_partition]
    rw [Finset.sum_add_distrib, Finset.sum_comm]
  have hshrubs : (∑ S ∈ P.shrubs, ∑ v ∈ S, T.degree v) =
      (∑ S ∈ P.shrubs, ∑ v ∈ S, degreeIn T S v) +
        ∑ S ∈ P.shrubs, ∑ v ∈ P.seeds, degreeIn T S v := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro S hS
    rw [sum_degreeIn_comm T P.seeds S, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun v hv ↦ P.degree_of_shrub_vertex S hS v hv)
  rw [P.sum_over_partition, hseeds, hshrubs]
  omega

end FineTreePartition

end Erdos547

#print axioms Erdos547.FineTreePartition.sum_degrees_partition
