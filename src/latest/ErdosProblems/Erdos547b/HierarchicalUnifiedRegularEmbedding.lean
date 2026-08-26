/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.HierarchicalUnifiedPools
import ErdosProblems.Erdos547b.HierarchicalRegularEmbedding

/-! Regular-pair degree certificates for unified physical-pool occupancy. -/

open scoped SimpleGraph BigOperators

noncomputable section

namespace Erdos547b.ZhaoLemma59HierarchicalUnifiedRegular

open Finset Fintype SimpleGraph
open Erdos547b.ZhaoLemma59Hierarchical
open Erdos547b.ZhaoLemma59HierarchicalOnline
open Erdos547b.ZhaoLemma59HierarchicalRegular
open Erdos547b.ZhaoLemma59HierarchicalUnified
open Erdos547b.ZhaoLemma59HierarchicalOnline.HierarchicalSegmentForest
open Erdos547b.ZhaoLemma59HierarchicalRegular.HierarchicalSegmentForest
open Erdos547b.ZhaoLemma59HierarchicalUnified.HierarchicalSegmentForest

universe u

namespace HierarchicalSegmentForest

variable {r s : ℕ} {B : Type u} {Pool : Type*} [DecidableEq Pool]

/-- Concrete degree/separation certificate for the unified-pool online
realizer.  The graph-side constructor proves these fields from actual whole
regular pairs, target-relative cleaning, and aggregate capacities. -/
structure UnifiedCleanedRegularSystem [Fintype B] [DecidableEq B]
    (F : HierarchicalSegmentForest r s)
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (originalImage : Fin r → B)
    (rootPool interiorPool : Fin s → Pool)
    (rootCandidate : Fin s → Finset B)
    (interiorCandidate : (i : Fin s) → Fin (F.segments.size i) → Finset B)
    where
  rootRaw : Fin s → Finset B
  interiorRaw : (i : Fin s) → Fin (F.segments.size i) → Finset B
  rootRemoved : Fin s → Finset B
  interiorRemoved : (i : Fin s) → Fin (F.segments.size i) → Finset B
  rootCandidate_eq : ∀ i, rootCandidate i = rootRaw i \ rootRemoved i
  interiorCandidate_eq : ∀ i a,
    interiorCandidate i a = interiorRaw i a \ interiorRemoved i a
  attach_original_capacity : ∀ i q, F.parent i = Sum.inl q →
    (poolLoad F rootPool interiorPool (rootPool i) + 1 : ℝ) +
        #(rootRemoved i) ≤
      (#((rootRaw i).filter (G.Adj (originalImage q))) : ℝ)
  attach_source_degree : ∀ i j a, F.parent i = Sum.inr ⟨j, a⟩ →
    ∀ z ∈ sourceCandidate F rootCandidate interiorCandidate j a,
    (poolLoad F rootPool interiorPool (rootPool i) + 1 : ℝ) +
        #(rootRemoved i) ≤
      (#((rootRaw i).filter (G.Adj z)) : ℝ)
  internal_source_degree : ∀ i a b, (F.segments.tree i).Adj a b →
    b ≠ F.segments.root i →
    ∀ z ∈ sourceCandidate F rootCandidate interiorCandidate i a,
    (poolLoad F rootPool interiorPool (interiorPool i) + 1 : ℝ) +
        #(interiorRemoved i b) ≤
      (#((interiorRaw i b).filter (G.Adj z)) : ℝ)
  original_injective : Function.Injective originalImage
  original_outside_root : ∀ q i, originalImage q ∉ rootCandidate i
  original_outside_interior : ∀ q i a,
    originalImage q ∉ interiorCandidate i a
  root_disjoint : ∀ i j, rootPool i ≠ rootPool j →
    Disjoint (rootCandidate i) (rootCandidate j)
  interior_disjoint : ∀ i a j b, interiorPool i ≠ interiorPool j →
    Disjoint (interiorCandidate i a) (interiorCandidate j b)
  root_interior_disjoint : ∀ i j a, rootPool i ≠ interiorPool j →
    Disjoint (rootCandidate i) (interiorCandidate j a)

/-- Public no-pointwise-oracle realization from a unified cleaned regular
system. -/
theorem exists_hierarchicalUnifiedRegularEmbedding
    [Fintype B] [DecidableEq B]
    (F : HierarchicalSegmentForest r s)
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (originalImage : Fin r → B)
    (rootPool interiorPool : Fin s → Pool)
    (rootCandidate : Fin s → Finset B)
    (interiorCandidate : (i : Fin s) → Fin (F.segments.size i) → Finset B)
    (S : UnifiedCleanedRegularSystem F G originalImage rootPool interiorPool
      rootCandidate interiorCandidate) :
    Nonempty (HierarchicalCandidateEmbedding F G originalImage
      rootCandidate interiorCandidate) := by
  classical
  apply exists_hierarchicalCandidateEmbedding_unifiedPools F G originalImage
    rootPool interiorPool rootCandidate interiorCandidate S.original_injective
    S.original_outside_root S.original_outside_interior S.root_disjoint
    S.interior_disjoint S.root_interior_disjoint
  · intro i q hp
    rw [S.rootCandidate_eq i]
    exact card_neighbors_sdiff_ge_of_real G (S.rootRaw i) (S.rootRemoved i)
      (originalImage q) (poolLoad F rootPool interiorPool (rootPool i) + 1)
      (by simpa only [Nat.cast_add, Nat.cast_one] using
        S.attach_original_capacity i q hp)
  · intro i j a hp z hz
    rw [S.rootCandidate_eq i]
    exact card_neighbors_sdiff_ge_of_real G (S.rootRaw i) (S.rootRemoved i)
      z (poolLoad F rootPool interiorPool (rootPool i) + 1)
      (by simpa only [Nat.cast_add, Nat.cast_one] using
        S.attach_source_degree i j a hp z hz)
  · intro i a b hab hb z hz
    rw [S.interiorCandidate_eq i b]
    exact card_neighbors_sdiff_ge_of_real G (S.interiorRaw i b)
      (S.interiorRemoved i b) z
      (poolLoad F rootPool interiorPool (interiorPool i) + 1)
      (by simpa only [Nat.cast_add, Nat.cast_one] using
        S.internal_source_degree i a b hab hb z hz)

end HierarchicalSegmentForest

end Erdos547b.ZhaoLemma59HierarchicalUnifiedRegular

#print axioms Erdos547b.ZhaoLemma59HierarchicalUnifiedRegular.HierarchicalSegmentForest.exists_hierarchicalUnifiedRegularEmbedding
