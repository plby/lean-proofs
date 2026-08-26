/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceMatchingGeometry
import ErdosProblems.Erdos547b.SourceParentCleanup

/-!
# Parent-reservoir cleanup on an arbitrary reduced matching

Only the two original root reservoirs are used. The physical endpoints
may belong to a switched matching and need no new coverage certificate.
-/

open scoped SimpleGraph Classical
noncomputable section

namespace Erdos547b.ZhaoSourceMatchingParentCleanup

open Finset SimpleGraph Erdos547b.ZhaoStability Erdos547b.ZhaoDegreeForm
open Erdos547b.ZhaoSourceDegreeFormRootRows Erdos547b.ZhaoSourceParameterSchedule
open Erdos547b.ZhaoSourceMatchingGeometry Erdos547b.ZhaoSourceEmbeddingHost
open Erdos547b.ZhaoEvenReducedPadding Erdos547b.ZhaoLemma611Full
open Erdos547b.ZhaoSourceParentCleanup Erdos547b.ZhaoSourceFreshChunkBounds

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G) (Q : Certificate W)
variable (P : (padGraph (reduced W)).Subgraph)

def deleted (e : MatchingEdge P) (c : Fin 2) : Finset (Fin hostN) :=
  badToward W Q (pairVertex W P e c) 0 ∪ badToward W Q (pairVertex W P e c) 1

theorem deleted_subset (e : MatchingEdge P) (c : Fin 2) :
    deleted W Q P e c ⊆ pairWhole W P e c :=
  Finset.union_subset (badToward_subset W Q _ 0) (badToward_subset W Q _ 1)

theorem card_deleted_le (hα : 0 < α) (hα1 : α ≤ 1 / 4)
    (e : MatchingEdge P) (c : Fin 2) :
    (deleted W Q P e c).card ≤ freshDeletionBudget α W.clusterSize := by
  have hA := card_badToward_le W Q hα hα1 (pairVertex W P e c) 0
  have hB := card_badToward_le W Q hα hα1 (pairVertex W P e c) 1
  change ((badToward W Q (pairVertex W P e c) 0).card : ℝ) ≤
    (epsilon α : ℝ) * (pairWhole W P e c).card at hA
  change ((badToward W Q (pairVertex W P e c) 1).card : ℝ) ≤
    (epsilon α : ℝ) * (pairWhole W P e c).card at hB
  rw [pairWhole_card] at hA hB
  have hsum : ((deleted W Q P e c).card : ℝ) ≤
      ((badToward W Q (pairVertex W P e c) 0).card : ℝ) +
        (badToward W Q (pairVertex W P e c) 1).card := by
    exact_mod_cast Finset.card_union_le (badToward W Q (pairVertex W P e c) 0)
      (badToward W Q (pairVertex W P e c) 1)
  have hbound : ((deleted W Q P e c).card : ℝ) ≤ 2 * (epsilon α : ℝ) * W.clusterSize := by
    linarith only [hA, hB, hsum]
  have hceil : 2 * (epsilon α : ℝ) * W.clusterSize ≤
      (freshDeletionBudget α W.clusterSize : ℝ) := Nat.le_ceil _
  exact Nat.cast_le.mp (hbound.trans hceil)

theorem parent_degree_into_reservoir (e : MatchingEdge P) (c s : Fin 2) (v : Fin hostN)
    (hv : v ∈ pairWhole W P e c \ deleted W Q P e c)
    (hadj : (padGraph (reduced W)).Adj (pairVertex W P e c) (Sum.inl (rootCluster W Q s))) :
    ((densityCutoff α : ℝ) - (epsilon α : ℝ)) * (sourceQuota W : ℝ) ≤
      (#((reservoir W Q s).filter ((embeddingHost W).Adj v)) : ℝ) := by
  have hnot : v ∉ badToward W Q (pairVertex W P e c) s := by
    intro hbad
    apply (Finset.mem_sdiff.mp hv).2
    rcases Erdos547b.RegularPair.OrderedRootedForest.fin_two_eq_zero_or_one s with rfl | rfl
    · exact Finset.mem_union_left _ hbad
    · exact Finset.mem_union_right _ hbad
  exact degree_into_reservoir_of_not_mem_badToward W Q _ s v
    (Finset.mem_sdiff.mp hv).1 hnot hadj

end Erdos547b.ZhaoSourceMatchingParentCleanup

#print axioms Erdos547b.ZhaoSourceMatchingParentCleanup.card_deleted_le
#print axioms Erdos547b.ZhaoSourceMatchingParentCleanup.parent_degree_into_reservoir
