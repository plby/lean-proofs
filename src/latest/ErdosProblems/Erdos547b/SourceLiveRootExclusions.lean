/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceActualPartThreeStep
import ErdosProblems.Erdos547b.SourceRootExclusions

/-!
# Small current-root exclusions for a live Part-3 pending edge

Regularity is applied to the actual unused endpoint subsets. Their size
gate is supplied by the residual source budget before root selection.
Each endpoint still costs at most epsilon times the whole cluster order.
-/

open scoped SimpleGraph Classical
noncomputable section

namespace Erdos547b.ZhaoSourceLiveRootExclusions

open Finset SimpleGraph
open Erdos547b.ZhaoStability Erdos547b.ZhaoDegreeForm Erdos547b.ZhaoEvenReducedPadding
open Erdos547b.ZhaoLemma611Full Erdos547b.ZhaoRichClaim61Lemma611
open Erdos547b.ZhaoSourceParameterSchedule Erdos547b.ZhaoSourceDegreeFormRootRows
open Erdos547b.ZhaoSourceEmbeddingHost Erdos547b.ZhaoSourceActualChunkEmbedding
open Erdos547b.ZhaoSourceActualPartThreeStep
open Erdos547b.ZhaoLemma59HierarchicalCanonical.HierarchicalSegmentForest

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G) (Q : Certificate W)

def badForLiveEntry (C : Index W) (e : MatchingEdge Q.claim67.M)
    (live : Fin 2 → Finset (Fin hostN)) (c : Fin 2) : Finset (Fin hostN) :=
  targetLowDegreeVertices (embeddingHost W) (epsilon α : ℝ)
    (clusterVertices (assignment W) C) (edgeWhole W Q e c)
    (clusterVertices (assignment W) C) (live c)

def badForLiveEdge (C : Index W) (e : MatchingEdge Q.claim67.M)
    (live : Fin 2 → Finset (Fin hostN)) : Finset (Fin hostN) :=
  badForLiveEntry W Q C e live 0 ∪ badForLiveEntry W Q C e live 1

private theorem source_entry_pair (S : CleanSourceWitness W Q) (C : Index W)
    (hC : C = Q.A ∨ C = Q.B) (e : MatchingEdge Q.claim67.M)
    (he : e ∈ edgesAwayFromDistinguished Q.claim67.M (padFinset (large W))
      (Sum.inl Q.A) (Sum.inl Q.B)) (c : Fin 2)
    (hpos : 0 < rootDensity W S (Sum.inl C) (edgeVertex W Q e c)) :
    (embeddingHost W).IsUniform (epsilon α : ℝ)
        (clusterVertices (assignment W) C) (edgeWhole W Q e c) ∧
      rootDensity W S (Sum.inl C) (edgeVertex W Q e c) ≤
        (embeddingHost W).edgeDensity (clusterVertices (assignment W) C) (edgeWhole W Q e c) +
          (epsilon α : ℝ) := by
  have hn := endpoint_ne_distinguished_of_mem_away Q.claim67.M (padFinset (large W))
    (Sum.inl Q.A) (Sum.inl Q.B) he c
  rcases hC with rfl | rfl
  · have hp := source_pair_A W S hn.1 hn.2 hpos
    exact ⟨hp.1, hp.2.2⟩
  · have hp := source_pair_B W S hn.1 hn.2 hpos
    exact ⟨hp.1, hp.2.2⟩

/-- The actual live target has the same epsilon-sized root exceptional set. -/
theorem card_badForLiveEntry_le (hα : 0 < α) (hα1 : α ≤ 1 / 4)
    (S : CleanSourceWitness W Q) (C : Index W) (hC : C = Q.A ∨ C = Q.B)
    (e : MatchingEdge Q.claim67.M)
    (he : e ∈ edgesAwayFromDistinguished Q.claim67.M (padFinset (large W))
      (Sum.inl Q.A) (Sum.inl Q.B))
    (live : Fin 2 → Finset (Fin hostN)) (c : Fin 2)
    (hpos : 0 < rootDensity W S (Sum.inl C) (edgeVertex W Q e c))
    (hlive : live c ⊆ edgeWhole W Q e c)
    (hlarge : (epsilon α : ℝ) * W.clusterSize ≤ (live c).card) :
    ((badForLiveEntry W Q C e live c).card : ℝ) ≤ (epsilon α : ℝ) * W.clusterSize := by
  have hpair := source_entry_pair W Q S C hC e he c hpos
  obtain ⟨_, _, _, _, hεd, hd1⟩ := reservoir_cleanup_bounds hα hα1
  have hεQ : epsilon α ≤ 1 := by linarith only [hεd, hd1]
  have hε : (epsilon α : ℝ) ≤ 1 := by exact_mod_cast hεQ
  have hc : (clusterVertices (assignment W) C).card = W.clusterSize := by
    rw [clusterVertices_partitionAssignment]
    exact W.equal_clusters C.1 C.2
  have hA : (epsilon α : ℝ) * (clusterVertices (assignment W) C).card ≤
      ((clusterVertices (assignment W) C).card : ℝ) := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hε
      (Nat.cast_nonneg (clusterVertices (assignment W) C).card : (0 : ℝ) ≤ _)
  simpa only [badForLiveEntry, hc] using card_targetLowDegreeVertices_le (embeddingHost W) hpair.1
    (Finset.Subset.refl _) hlive hA (by simpa only [edgeWhole_card] using hlarge)

theorem card_badForLiveEdge_le (hα : 0 < α) (hα1 : α ≤ 1 / 4)
    (S : CleanSourceWitness W Q) (C : Index W) (hC : C = Q.A ∨ C = Q.B)
    (e : MatchingEdge Q.claim67.M)
    (he : e ∈ edgesAwayFromDistinguished Q.claim67.M (padFinset (large W))
      (Sum.inl Q.A) (Sum.inl Q.B))
    (live : Fin 2 → Finset (Fin hostN))
    (hpos : ∀ c, 0 < rootDensity W S (Sum.inl C) (edgeVertex W Q e c))
    (hlive : ∀ c, live c ⊆ edgeWhole W Q e c)
    (hlarge : ∀ c, (epsilon α : ℝ) * W.clusterSize ≤ (live c).card) :
    ((badForLiveEdge W Q C e live).card : ℝ) ≤ 2 * (epsilon α : ℝ) * W.clusterSize := by
  have h0 := card_badForLiveEntry_le W Q hα hα1 S C hC e he live 0 (hpos 0) (hlive 0) (hlarge 0)
  have h1 := card_badForLiveEntry_le W Q hα hα1 S C hC e he live 1 (hpos 1) (hlive 1) (hlarge 1)
  have hu : ((badForLiveEdge W Q C e live).card : ℝ) ≤
      ((badForLiveEntry W Q C e live 0).card : ℝ) + (badForLiveEntry W Q C e live 1).card := by
    exact_mod_cast Finset.card_union_le (badForLiveEntry W Q C e live 0) (badForLiveEntry W Q C e live 1)
  linarith only [h0, h1, hu]

/-- Outside the two actual live exceptional sets, the selected root
satisfies exactly the Part-3 live predicate used by the graph step. -/
theorem eligibleLiveRoot_of_not_mem_bad
    (S : CleanSourceWitness W Q) (C : Index W) (hC : C = Q.A ∨ C = Q.B)
    (e : MatchingEdge Q.claim67.M)
    (he : e ∈ edgesAwayFromDistinguished Q.claim67.M (padFinset (large W))
      (Sum.inl Q.A) (Sum.inl Q.B)) (live : Fin 2 → Finset (Fin hostN))
    (hpos : ∀ c, 0 < rootDensity W S (Sum.inl C) (edgeVertex W Q e c))
    (z : Fin hostN) (hz : z ∈ clusterVertices (assignment W) C)
    (hgood : z ∉ badForLiveEdge W Q C e live) :
    EligibleLiveRoot W Q S C e live z := by
  intro c
  have hnot : z ∉ badForLiveEntry W Q C e live c := by
    intro hbad
    apply hgood
    rcases Erdos547b.RegularPair.OrderedRootedForest.fin_two_eq_zero_or_one c with rfl | rfl
    · exact Finset.mem_union_left _ hbad
    · exact Finset.mem_union_right _ hbad
  have hdegree := target_degree_ge_of_not_mem_lowDegree (embeddingHost W) (epsilon α : ℝ)
    (clusterVertices (assignment W) C) (edgeWhole W Q e c)
    (clusterVertices (assignment W) C) (live c) z hz hnot
  have hsource := (source_entry_pair W Q S C hC e he c (hpos c)).2
  have hcoeff : rootDensity W S (Sum.inl C) (edgeVertex W Q e c) - 2 * (epsilon α : ℝ) ≤
      (embeddingHost W).edgeDensity (clusterVertices (assignment W) C) (edgeWhole W Q e c) -
        (epsilon α : ℝ) := by linarith only [hsource]
  exact (mul_le_mul_of_nonneg_right hcoeff (Nat.cast_nonneg (live c).card)).trans hdegree

end Erdos547b.ZhaoSourceLiveRootExclusions

#print axioms Erdos547b.ZhaoSourceLiveRootExclusions.card_badForLiveEntry_le
#print axioms Erdos547b.ZhaoSourceLiveRootExclusions.card_badForLiveEdge_le
#print axioms Erdos547b.ZhaoSourceLiveRootExclusions.eligibleLiveRoot_of_not_mem_bad
