/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceMatchingRootSelection
import ErdosProblems.Erdos547b.SourcePendingRootSelection

/-!
# Pending-edge exclusions for an arbitrary reduced matching

Two whole-target lower-atypical sets pay for one fixed matching edge.
One further set pays for the opposite raw root reservoir. These exclusions
and the already used roots fit the proved cut-parent reconnection margin.
-/

open scoped SimpleGraph Classical
noncomputable section

namespace Erdos547b.ZhaoSourceMatchingRootExclusions

open Finset SimpleGraph
open Erdos547b.ZhaoStability Erdos547b.ZhaoDegreeForm Erdos547b.ZhaoEvenReducedPadding
open Erdos547b.ZhaoLemma611Full Erdos547b.ZhaoRichClaim61Lemma611
open Erdos547b.ZhaoSourceParameterSchedule Erdos547b.ZhaoSourceDegreeFormRootRows
open Erdos547b.ZhaoSourceEmbeddingHost Erdos547b.ZhaoSourceActualChunkEmbedding
open Erdos547b.ZhaoSourceMatchingRootSelection Erdos547b.ZhaoSourceParentCleanup
open Erdos547b.ZhaoSourceMatchingGeometry Erdos547b.ZhaoSourcePendingRootSelection
open Erdos547b.ZhaoSourceRootReconnection Erdos547b.ZhaoSourceDegreeFormBounds
open Erdos547b.ZhaoLemma59HierarchicalCanonical.HierarchicalSegmentForest

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G) (Q : Certificate W)
variable (P : (padGraph (reduced W)).Subgraph)

theorem rootCluster_cases (s : Fin 2) : rootCluster W Q s = Q.A ∨ rootCluster W Q s = Q.B := by
  unfold rootCluster
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr rfl

def badForEntry (S : CleanSourceWitness W Q) (C : Index W)
    (e : MatchingEdge P) (c : Fin 2) : Finset (Fin hostN) :=
  if 0 < rootDensity W S (Sum.inl C) (pairVertex W P e c) then
    targetLowDegreeVertices (embeddingHost W) (epsilon α : ℝ)
      (clusterVertices (assignment W) C) (pairWhole W P e c)
      (clusterVertices (assignment W) C) (pairWhole W P e c)
  else ∅

private theorem entry_pair (S : CleanSourceWitness W Q) (C : Index W)
    (hC : C = Q.A ∨ C = Q.B) (e : MatchingEdge P)
    (he : e ∈ edgesAwayFromDistinguished P (padFinset (large W))
      (Sum.inl Q.A) (Sum.inl Q.B)) (c : Fin 2)
    (hpos : 0 < rootDensity W S (Sum.inl C) (pairVertex W P e c)) :
    (embeddingHost W).IsUniform (epsilon α : ℝ)
        (clusterVertices (assignment W) C) (pairWhole W P e c) ∧
      rootDensity W S (Sum.inl C) (pairVertex W P e c) ≤
        (embeddingHost W).edgeDensity (clusterVertices (assignment W) C) (pairWhole W P e c) +
          (epsilon α : ℝ) := by
  have hn := endpoint_ne_distinguished_of_mem_away P (padFinset (large W))
    (Sum.inl Q.A) (Sum.inl Q.B) he c
  rcases hC with rfl | rfl
  · have hp := source_pair_A W S hn.1 hn.2 hpos
    exact ⟨hp.1, hp.2.2⟩
  · have hp := source_pair_B W S hn.1 hn.2 hpos
    exact ⟨hp.1, hp.2.2⟩

theorem card_badForEntry_le (hα : 0 < α) (hα1 : α ≤ 1 / 4)
    (S : CleanSourceWitness W Q) (C : Index W) (hC : C = Q.A ∨ C = Q.B)
    (e : MatchingEdge P)
    (he : e ∈ edgesAwayFromDistinguished P (padFinset (large W))
      (Sum.inl Q.A) (Sum.inl Q.B)) (c : Fin 2) :
    ((badForEntry W Q P S C e c).card : ℝ) ≤ (epsilon α : ℝ) * W.clusterSize := by
  unfold badForEntry
  split_ifs with hp
  · have hpair := entry_pair W Q P S C hC e he c hp
    obtain ⟨_, _, _, _, hεd, hd1⟩ := reservoir_cleanup_bounds hα hα1
    have hεQ : epsilon α ≤ 1 := by linarith only [hεd, hd1]
    have hε : (epsilon α : ℝ) ≤ 1 := by exact_mod_cast hεQ
    have hlarge (X : Finset (Fin hostN)) : (epsilon α : ℝ) * X.card ≤ (X.card : ℝ) := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hε (Nat.cast_nonneg X.card)
    have hc : (clusterVertices (assignment W) C).card = W.clusterSize := by
      rw [clusterVertices_partitionAssignment]
      exact W.equal_clusters C.1 C.2
    simpa only [hc] using card_targetLowDegreeVertices_le (embeddingHost W) hpair.1
      (Finset.Subset.refl _) (Finset.Subset.refl _) (hlarge _) (hlarge _)
  · have hε : (0 : ℝ) < epsilon α := by exact_mod_cast (parameter_pos hα).2.2.2.2.2.2.2
    simp only [Finset.card_empty, Nat.cast_zero]
    positivity

def badForEdge (S : CleanSourceWitness W Q) (C : Index W)
    (e : MatchingEdge P) : Finset (Fin hostN) :=
  badForEntry W Q P S C e 0 ∪ badForEntry W Q P S C e 1

theorem card_badForEdge_le (hα : 0 < α) (hα1 : α ≤ 1 / 4)
    (S : CleanSourceWitness W Q) (C : Index W) (hC : C = Q.A ∨ C = Q.B)
    (e : MatchingEdge P)
    (he : e ∈ edgesAwayFromDistinguished P (padFinset (large W))
      (Sum.inl Q.A) (Sum.inl Q.B)) :
    ((badForEdge W Q P S C e).card : ℝ) ≤ 2 * (epsilon α : ℝ) * W.clusterSize := by
  have h0 := card_badForEntry_le W Q P hα hα1 S C hC e he 0
  have h1 := card_badForEntry_le W Q P hα hα1 S C hC e he 1
  have hu : ((badForEdge W Q P S C e).card : ℝ) ≤
      ((badForEntry W Q P S C e 0).card : ℝ) + (badForEntry W Q P S C e 1).card := by
    exact_mod_cast Finset.card_union_le (badForEntry W Q P S C e 0) (badForEntry W Q P S C e 1)
  linarith only [h0, h1, hu]

theorem eligibleRoot_of_not_mem_badForEdge
    (S : CleanSourceWitness W Q) (C : Index W) (hC : C = Q.A ∨ C = Q.B)
    (e : MatchingEdge P)
    (he : e ∈ edgesAwayFromDistinguished P (padFinset (large W))
      (Sum.inl Q.A) (Sum.inl Q.B)) (z : Fin hostN)
    (hz : z ∈ clusterVertices (assignment W) C) (hgood : z ∉ badForEdge W Q P S C e) :
    EligibleRoot W Q S P C e z := by
  intro c hpos
  have hnot : z ∉ badForEntry W Q P S C e c := by
    intro hbad
    apply hgood
    rcases Erdos547b.RegularPair.OrderedRootedForest.fin_two_eq_zero_or_one c with rfl | rfl
    · exact Finset.mem_union_left _ hbad
    · exact Finset.mem_union_right _ hbad
  rw [badForEntry, if_pos hpos] at hnot
  have hdegree := target_degree_ge_of_not_mem_lowDegree (embeddingHost W) (epsilon α : ℝ)
    (clusterVertices (assignment W) C) (pairWhole W P e c)
    (clusterVertices (assignment W) C) (pairWhole W P e c) z hz hnot
  have hsource := (entry_pair W Q P S C hC e he c hpos).2
  have hcoeff : rootDensity W S (Sum.inl C) (pairVertex W P e c) - 2 * (epsilon α : ℝ) ≤
      (embeddingHost W).edgeDensity (clusterVertices (assignment W) C) (pairWhole W P e c) -
        (epsilon α : ℝ) := by linarith only [hsource]
  rw [pairWhole_card] at hdegree
  exact (mul_le_mul_of_nonneg_right hcoeff (Nat.cast_nonneg W.clusterSize)).trans hdegree

def forbidden (S : CleanSourceWitness W Q) (s t : Fin 2)
    (fixed : MatchingEdge P) (used : Finset (Fin hostN)) : Finset (Fin hostN) :=
  used ∪ badForEdge W Q P S (rootCluster W Q s) fixed ∪
    badToward W Q (Sum.inl (rootCluster W Q s)) t

theorem card_forbidden_le (hα : 0 < α) (hα1 : α ≤ 1 / 4)
    (S : CleanSourceWitness W Q) (s t : Fin 2)
    (fixed : MatchingEdge P)
    (hfixed : fixed ∈ edgesAwayFromDistinguished P (padFinset (large W))
      (Sum.inl Q.A) (Sum.inl Q.B))
    (used : Finset (Fin hostN)) (hused : (used.card : ℝ) ≤ (epsilon α : ℝ) * W.clusterSize) :
    ((forbidden W Q P S s t fixed used).card : ℝ) ≤
      (3 * (rootTypicality α : ℝ) + 6 * (epsilon α : ℝ)) * W.clusterSize := by
  have he := card_badForEdge_le W Q P hα hα1 S _ (rootCluster_cases W Q s) fixed hfixed
  have hr := card_badToward_le W Q hα hα1 (Sum.inl (rootCluster W Q s)) t
  have hc : (padCluster (clusterVertices (assignment W)) (Sum.inl (rootCluster W Q s))).card =
      W.clusterSize := by
    change (clusterVertices (assignment W) (rootCluster W Q s)).card = _
    rw [clusterVertices_partitionAssignment]
    exact W.equal_clusters _ (rootCluster W Q s).2
  rw [hc] at hr
  have hu : ((forbidden W Q P S s t fixed used).card : ℝ) ≤
      (used.card : ℝ) + ((badForEdge W Q P S (rootCluster W Q s) fixed).card : ℝ) +
        (badToward W Q (Sum.inl (rootCluster W Q s)) t).card := by
    have h := Finset.card_union_le (used ∪ badForEdge W Q P S (rootCluster W Q s) fixed)
      (badToward W Q (Sum.inl (rootCluster W Q s)) t)
    exact_mod_cast h.trans (Nat.add_le_add_right (Finset.card_union_le _ _) _)
  have hε : (0 : ℝ) ≤ epsilon α := by exact_mod_cast (parameter_pos hα).2.2.2.2.2.2.2.le
  have hδ : (0 : ℝ) ≤ rootTypicality α := by
    exact_mod_cast (rootTypicality_margin hα hα1).1.le
  have hεN := mul_nonneg hε (Nat.cast_nonneg W.clusterSize)
  have hδN := mul_nonneg hδ (Nat.cast_nonneg W.clusterSize)
  nlinarith only [hused, he, hr, hu, hεN, hδN]


/-- An arbitrary already-paid exclusion set may include pending-edge and
midpoint conditions. The parent pool itself is proved large here. -/
theorem exists_root_after_parent_exclusions
    (hα : 0 < α) (hα1 : α ≤ 1 / 4)
    (S : CleanSourceWitness W Q) (s : Fin 2) (v : Fin hostN)
    (hdegree : ((densityCutoff α : ℝ) - (epsilon α : ℝ)) * (sourceQuota W : ℝ) ≤
      (#((reservoir W Q s).filter ((embeddingHost W).Adj v)) : ℝ))
    (excluded : Finset (Fin hostN))
    (hexcluded : (excluded.card : ℝ) ≤
      (3 * (rootTypicality α : ℝ) + 6 * (epsilon α : ℝ)) * W.clusterSize)
    (remaining : Finset (MatchingEdge P))
    (hremaining : remaining ⊆ edgesAwayFromDistinguished P
      (padFinset (large W)) (Sum.inl Q.A) (Sum.inl Q.B)) :
    ∃ z ∈ reservoir W Q s, (embeddingHost W).Adj v z ∧ z ∉ excluded ∧
      ∃ bad ⊆ remaining,
        (bad.card : ℝ) ≤ 2 * (rootTypicality α : ℝ) * remaining.card ∧
        ∀ e ∈ remaining \ bad, EligibleRoot W Q S P (rootCluster W Q s) e z := by
  have hpool := parentPool_large_of_degree W Q hα hα1 s v hdegree excluded hexcluded
  obtain ⟨z, hz, bad, hb, hcount, hgood⟩ :=
    Erdos547b.ZhaoSourceMatchingRootSelection.exists_eligible_root_most_edges
      W Q S P hα hα1 (rootCluster W Q s) (rootCluster_cases W Q s) remaining
      (fun e he c => endpoint_ne_distinguished_of_mem_away P (padFinset (large W))
        (Sum.inl Q.A) (Sum.inl Q.B) (hremaining he) c)
      (parentPool W Q s v excluded) (parentPool_subset W Q s v excluded) hpool
  obtain ⟨hzR, hzAdj, hzFresh⟩ := (mem_parentPool W Q).mp hz
  exact ⟨z, hzR, hzAdj, hzFresh, bad, hb, hcount, hgood⟩

end Erdos547b.ZhaoSourceMatchingRootExclusions

#print axioms Erdos547b.ZhaoSourceMatchingRootExclusions.card_badForEdge_le
#print axioms Erdos547b.ZhaoSourceMatchingRootExclusions.eligibleRoot_of_not_mem_badForEdge
#print axioms Erdos547b.ZhaoSourceMatchingRootExclusions.card_forbidden_le
#print axioms Erdos547b.ZhaoSourceMatchingRootExclusions.exists_root_after_parent_exclusions
