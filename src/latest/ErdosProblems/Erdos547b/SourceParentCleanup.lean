/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceOnlineMatchingRoot

/-!
# Permanent cleanup for future cut parents

Each endpoint is cleaned toward only the two actual large root reservoirs.
The deletion budget is independent of the number of future roots and of
the number of matching edges. Every retained vertex has the required
root-reservoir degree whenever the corresponding reduced edge exists.
-/

open scoped SimpleGraph Classical
noncomputable section

namespace Erdos547b.ZhaoSourceParentCleanup

open Finset SimpleGraph
open Erdos547b.ZhaoStability Erdos547b.ZhaoDegreeForm Erdos547b.ZhaoEvenReducedPadding
open Erdos547b.ZhaoLemma611Full Erdos547b.ZhaoSection6RichHierarchy
open Erdos547b.ZhaoSourceParameterSchedule Erdos547b.ZhaoSourceDegreeFormRootRows
open Erdos547b.ZhaoSourceEmbeddingHost Erdos547b.ZhaoSourceActualChunkEmbedding
open Erdos547b.ZhaoSourceFreshChunkBounds
open Erdos547b.ZhaoLemma59HierarchicalCanonical.HierarchicalSegmentForest

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G) (Q : Certificate W)

abbrev rootCluster (s : Fin 2) : Index W := if s = 0 then Q.A else Q.B
abbrev reservoir (s : Fin 2) : Finset (Fin hostN) := if s = 0 then Q.A₀ else Q.B₀

theorem reservoir_card (s : Fin 2) : (reservoir W Q s).card = sourceQuota W := by
  fin_cases s <;> simp [reservoir, Q.A₀_card, Q.B₀_card]

theorem reservoir_subset (s : Fin 2) :
    reservoir W Q s ⊆ clusterVertices (assignment W) (rootCluster W Q s) := by
  fin_cases s
  · exact Q.A₀_subset
  · exact Q.B₀_subset

private theorem epsilon_le_one (hα : 0 < α) (hα1 : α ≤ 1 / 4) : (epsilon α : ℝ) ≤ 1 := by
  obtain ⟨_, _, _, _, he, hd⟩ := reservoir_cleanup_bounds hα hα1
  have h : epsilon α ≤ 1 := by linarith only [he, hd]
  exact_mod_cast h

/-- The actual high-vertex reservoir is a large target for regularity. -/
theorem reservoir_large (hα : 0 < α) (hα1 : α ≤ 1 / 4) (s : Fin 2) :
    (epsilon α : ℝ) * (clusterVertices (assignment W) (rootCluster W Q s)).card ≤
      (reservoir W Q s).card := by
  have hcard : (clusterVertices (assignment W) (rootCluster W Q s)).card = W.clusterSize := by
    rw [clusterVertices_partitionAssignment]
    exact W.equal_clusters _ (rootCluster W Q s).2
  obtain ⟨hσ, _, _, hd, he, _⟩ := reservoir_cleanup_bounds hα hα1
  have hεσQ : epsilon α ≤ 2 * fourthRoot α ^ 2 := by linarith only [hd, he, hσ]
  have hεσ : (epsilon α : ℝ) ≤ 2 * (fourthRoot α : ℝ) ^ 2 := by exact_mod_cast hεσQ
  rw [hcard, reservoir_card]
  exact (mul_le_mul_of_nonneg_right hεσ (Nat.cast_nonneg W.clusterSize)).trans (Nat.le_ceil _)

def badToward (x : EvenPadding (Index W)) (s : Fin 2) : Finset (Fin hostN) :=
  if (padGraph (reduced W)).Adj x (Sum.inl (rootCluster W Q s)) then
    targetLowDegreeVertices (embeddingHost W) (epsilon α : ℝ)
      (padCluster (clusterVertices (assignment W)) x)
      (clusterVertices (assignment W) (rootCluster W Q s))
      (padCluster (clusterVertices (assignment W)) x) (reservoir W Q s)
  else ∅

theorem badToward_subset (x : EvenPadding (Index W)) (s : Fin 2) :
    badToward W Q x s ⊆ padCluster (clusterVertices (assignment W)) x := by
  unfold badToward
  split_ifs
  · exact Finset.filter_subset _ _
  · exact Finset.empty_subset _

theorem card_badToward_le (hα : 0 < α) (hα1 : α ≤ 1 / 4)
    (x : EvenPadding (Index W)) (s : Fin 2) :
    ((badToward W Q x s).card : ℝ) ≤
      (epsilon α : ℝ) * (padCluster (clusterVertices (assignment W)) x).card := by
  unfold badToward
  split_ifs with hadj
  · have hp := (embedding_pair_realization W).pair_of_adj _ _ hadj
    apply card_targetLowDegreeVertices_le (embeddingHost W) hp.1 (Finset.Subset.refl _)
      (reservoir_subset W Q s) _ (reservoir_large W Q hα hα1 s)
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (epsilon_le_one hα hα1)
      (Nat.cast_nonneg (padCluster (clusterVertices (assignment W)) x).card)
  · have he : (0 : ℝ) < epsilon α := by exact_mod_cast (parameter_pos hα).2.2.2.2.2.2.2
    simp only [Finset.card_empty, Nat.cast_zero]
    positivity

def deleted (e : MatchingEdge Q.claim67.M) (c : Fin 2) : Finset (Fin hostN) :=
  badToward W Q (edgeVertex W Q e c) 0 ∪ badToward W Q (edgeVertex W Q e c) 1

theorem deleted_subset (e : MatchingEdge Q.claim67.M) (c : Fin 2) :
    deleted W Q e c ⊆ edgeWhole W Q e c :=
  Finset.union_subset (badToward_subset W Q _ 0) (badToward_subset W Q _ 1)

theorem card_deleted_le (hα : 0 < α) (hα1 : α ≤ 1 / 4)
    (e : MatchingEdge Q.claim67.M) (c : Fin 2) :
    (deleted W Q e c).card ≤ freshDeletionBudget α W.clusterSize := by
  have hA := card_badToward_le W Q hα hα1 (edgeVertex W Q e c) 0
  have hB := card_badToward_le W Q hα hα1 (edgeVertex W Q e c) 1
  change ((badToward W Q (edgeVertex W Q e c) 0).card : ℝ) ≤
    (epsilon α : ℝ) * (edgeWhole W Q e c).card at hA
  change ((badToward W Q (edgeVertex W Q e c) 1).card : ℝ) ≤
    (epsilon α : ℝ) * (edgeWhole W Q e c).card at hB
  rw [edgeWhole_card] at hA hB
  have hsum : ((deleted W Q e c).card : ℝ) ≤
      ((badToward W Q (edgeVertex W Q e c) 0).card : ℝ) +
        (badToward W Q (edgeVertex W Q e c) 1).card := by
    exact_mod_cast Finset.card_union_le (badToward W Q (edgeVertex W Q e c) 0)
      (badToward W Q (edgeVertex W Q e c) 1)
  have hbound : ((deleted W Q e c).card : ℝ) ≤ 2 * (epsilon α : ℝ) * W.clusterSize := by
    linarith only [hA, hB, hsum]
  have hceil : 2 * (epsilon α : ℝ) * W.clusterSize ≤
      (freshDeletionBudget α W.clusterSize : ℝ) := Nat.le_ceil _
  exact Nat.cast_le.mp (hbound.trans hceil)

/-- Avoiding the one actual reservoir's low-degree set supplies its
degree bound, whether the vertex is a cut parent or another root. -/
theorem degree_into_reservoir_of_not_mem_badToward
    (x : EvenPadding (Index W)) (s : Fin 2) (v : Fin hostN)
    (hv : v ∈ padCluster (clusterVertices (assignment W)) x)
    (hnot : v ∉ badToward W Q x s)
    (hadj : (padGraph (reduced W)).Adj x (Sum.inl (rootCluster W Q s))) :
    ((densityCutoff α : ℝ) - (epsilon α : ℝ)) * (sourceQuota W : ℝ) ≤
      (#((reservoir W Q s).filter ((embeddingHost W).Adj v)) : ℝ) := by
  rw [badToward, if_pos hadj] at hnot
  have hlower := target_degree_ge_of_not_mem_lowDegree (embeddingHost W) (epsilon α : ℝ)
    (padCluster (clusterVertices (assignment W)) x)
    (clusterVertices (assignment W) (rootCluster W Q s))
    (padCluster (clusterVertices (assignment W)) x) (reservoir W Q s) v hv hnot
  rw [reservoir_card] at hlower
  have hd := ((embedding_pair_realization W).pair_of_adj _ _ hadj).2
  exact (mul_le_mul_of_nonneg_right (sub_le_sub_right hd _)
    (Nat.cast_nonneg (sourceQuota W))).trans hlower

/-- A future parent in the cleaned endpoint has many neighbors in each
root reservoir required by reduced adjacency. -/
theorem parent_degree_into_reservoir
    (e : MatchingEdge Q.claim67.M) (c s : Fin 2) (v : Fin hostN)
    (hv : v ∈ edgeWhole W Q e c \ deleted W Q e c)
    (hadj : (padGraph (reduced W)).Adj (edgeVertex W Q e c) (Sum.inl (rootCluster W Q s))) :
    ((densityCutoff α : ℝ) - (epsilon α : ℝ)) * (sourceQuota W : ℝ) ≤
      (#((reservoir W Q s).filter ((embeddingHost W).Adj v)) : ℝ) := by
  have hnot : v ∉ badToward W Q (edgeVertex W Q e c) s := by
    intro hbad
    apply (Finset.mem_sdiff.mp hv).2
    rcases Erdos547b.RegularPair.OrderedRootedForest.fin_two_eq_zero_or_one s with rfl | rfl
    · exact Finset.mem_union_left _ hbad
    · exact Finset.mem_union_right _ hbad
  exact degree_into_reservoir_of_not_mem_badToward W Q _ s v
    (Finset.mem_sdiff.mp hv).1 hnot hadj

end Erdos547b.ZhaoSourceParentCleanup

#print axioms Erdos547b.ZhaoSourceParentCleanup.reservoir_large
#print axioms Erdos547b.ZhaoSourceParentCleanup.badToward_subset
#print axioms Erdos547b.ZhaoSourceParentCleanup.card_badToward_le
#print axioms Erdos547b.ZhaoSourceParentCleanup.deleted_subset
#print axioms Erdos547b.ZhaoSourceParentCleanup.card_deleted_le
#print axioms Erdos547b.ZhaoSourceParentCleanup.degree_into_reservoir_of_not_mem_badToward
#print axioms Erdos547b.ZhaoSourceParentCleanup.parent_degree_into_reservoir
