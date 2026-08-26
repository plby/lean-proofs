/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceEmbeddingHost

/-!
# Physical pairs for any matching of the actual reduced graph

In particular these definitions apply to a switched matching without
asserting a new Claim-6.7 coverage certificate.
-/

open scoped SimpleGraph Classical
noncomputable section

namespace Erdos547b.ZhaoSourceMatchingGeometry

open Finset SimpleGraph Erdos547b.ZhaoStability Erdos547b.ZhaoDegreeForm
open Erdos547b.ZhaoSourceDegreeFormRootRows Erdos547b.ZhaoSourceEmbeddingHost
open Erdos547b.ZhaoSourceParameterSchedule Erdos547b.ZhaoEvenReducedPadding
open Erdos547b.ZhaoLemma611Full
open Erdos547b.ZhaoSection6Dichotomy

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G) (P : (padGraph (reduced W)).Subgraph)

def pairVertex (e : MatchingEdge P) (c : Fin 2) : EvenPadding (Index W) :=
  orientedEndpoint P (padFinset (large W)) e c

def pairWhole (e : MatchingEdge P) (c : Fin 2) : Finset (Fin hostN) :=
  padCluster (clusterVertices (assignment W)) (pairVertex W P e c)

theorem pair_adj (e : MatchingEdge P) :
    (padGraph (reduced W)).Adj (pairVertex W P e 0) (pairVertex W P e 1) :=
  P.adj_sub (orientedEndpoint_adj P (padFinset (large W)) e)

theorem pairVertex_real (e : MatchingEdge P) (c : Fin 2) :
    ∃ i : Index W, pairVertex W P e c = Sum.inl i := by
  have hreal {x y : EvenPadding (Index W)} (hxy : (padGraph (reduced W)).Adj x y) :
      ∃ i : Index W, x = Sum.inl i := by
    cases x with
    | inl i => exact ⟨i, rfl⟩
    | inr d => exact (padGraph_not_adj_inr_left (reduced W) d y hxy).elim
  fin_cases c
  · exact hreal (pair_adj W P e)
  · exact hreal (pair_adj W P e).symm

theorem pairWhole_card (e : MatchingEdge P) (c : Fin 2) :
    (pairWhole W P e c).card = W.clusterSize := by
  obtain ⟨i, hi⟩ := pairVertex_real W P e c
  rw [pairWhole, hi]
  change (clusterVertices (assignment W) i).card = _
  rw [clusterVertices_partitionAssignment]
  exact W.equal_clusters i.1 i.2

theorem pairWhole_disjoint (e : MatchingEdge P) :
    Disjoint (pairWhole W P e 0) (pairWhole W P e 1) := by
  have h := clusterVertices_disjoint (padAssignment (assignment W)) (pair_adj W P e).ne
  simpa only [clusterVertices_padAssignment, pairWhole] using h

theorem pair_regular (e : MatchingEdge P) :
    (embeddingHost W).IsUniform (epsilon α : ℝ) (pairWhole W P e 0) (pairWhole W P e 1) ∧
      (densityCutoff α : ℝ) ≤ (embeddingHost W).edgeDensity (pairWhole W P e 0) (pairWhole W P e 1) :=
  (embedding_pair_realization W).pair_of_adj _ _ (pair_adj W P e)

theorem pairWhole_cross_disjoint (hP : P.IsMatching) (e f : MatchingEdge P) (hef : e ≠ f)
    (c d : Fin 2) : Disjoint (pairWhole W P e c) (pairWhole W P f d) := by
  have hne : pairVertex W P e c ≠ pairVertex W P f d := by
    intro h
    have hpair : (e, c) = (f, d) := orientedEndpoint_injective P hP (padFinset (large W)) h
    exact hef (congrArg Prod.fst hpair)
  have h := clusterVertices_disjoint (padAssignment (assignment W)) hne
  simpa only [clusterVertices_padAssignment, pairWhole] using h

theorem matchingVolume_bound (hP : P.IsMatching) (hhost : hostN = 2 * q)
    (E : Finset (MatchingEdge P)) : (W.clusterSize : ℝ) * E.card ≤ q := by
  let pair := fun e => pairWhole W P e 0 ∪ pairWhole W P e 1
  have hcard (e : MatchingEdge P) : (pair e).card = 2 * W.clusterSize := by
    rw [Finset.card_union_of_disjoint (pairWhole_disjoint W P e), pairWhole_card, pairWhole_card]
    omega
  have hd : ∀ e ∈ E, ∀ f ∈ E, e ≠ f → Disjoint (pair e) (pair f) := by
    intro e _ f _ hef
    rw [Finset.disjoint_union_left, Finset.disjoint_union_right, Finset.disjoint_union_right]
    exact ⟨⟨pairWhole_cross_disjoint W P hP e f hef 0 0, pairWhole_cross_disjoint W P hP e f hef 0 1⟩,
      ⟨pairWhole_cross_disjoint W P hP e f hef 1 0, pairWhole_cross_disjoint W P hP e f hef 1 1⟩⟩
  have hc : (E.biUnion pair).card = E.card * (2 * W.clusterSize) := by
    rw [Finset.card_biUnion hd]
    simp only [hcard, Finset.sum_const, nsmul_eq_mul, Nat.cast_id]
  have hbound : E.card * (2 * W.clusterSize) ≤ 2 * q := by
    rw [← hc, ← hhost]
    simpa only [Finset.card_univ, Fintype.card_fin] using Finset.card_le_univ (E.biUnion pair)
  have hR : (E.card : ℝ) * (2 * W.clusterSize) ≤ 2 * q := by exact_mod_cast hbound
  nlinarith only [hR]

end Erdos547b.ZhaoSourceMatchingGeometry

#print axioms Erdos547b.ZhaoSourceMatchingGeometry.pair_regular
#print axioms Erdos547b.ZhaoSourceMatchingGeometry.matchingVolume_bound
