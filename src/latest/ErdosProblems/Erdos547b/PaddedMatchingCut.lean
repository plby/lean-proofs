/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.EvenReducedPadding
import ErdosProblems.Erdos547b.DegreeFormQuantitative
import ErdosProblems.Erdos547b.Claim61Numerics
import ErdosProblems.Erdos547b.Lemma611Claim618Adapter

open scoped SimpleGraph

noncomputable section

namespace Erdos547b.ZhaoPaddedMatchingCut

open Finset SimpleGraph
open Erdos547b.ZhaoStability
open Erdos547b.ZhaoSection6Dichotomy
open Erdos547b.ZhaoEvenReducedPadding
open Erdos547b.ZhaoLemma611Full
open Erdos547b.ZhaoDegreeForm
open Erdos547b.ZhaoDegreeFormQuantitative
open Erdos547b.ZhaoClaim61Numerics

universe u

/-- The original indices represented by a finset of padded indices. -/
def unpadFinset {ι : Type u} [Fintype ι] [DecidableEq ι]
    (I : Finset (EvenPadding ι)) : Finset ι :=
  Finset.univ.filter fun i => (Sum.inl i : EvenPadding ι) ∈ I

@[simp] theorem mem_unpadFinset
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    {I : Finset (EvenPadding ι)} {i : ι} :
    i ∈ unpadFinset I ↔ (Sum.inl i : EvenPadding ι) ∈ I := by
  simp [unpadFinset]

/-- A finset containing no dummy index is recovered exactly by padding its
unpadding. -/
theorem padFinset_unpadFinset
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (I : Finset (EvenPadding ι))
    (hI : I ⊆ padFinset (Finset.univ : Finset ι)) :
    padFinset (unpadFinset I) = I := by
  ext x
  cases x with
  | inl i => simp
  | inr d =>
      simp only [not_mem_padFinset_inr, false_iff]
      intro hd
      exact not_mem_padFinset_inr d (hI hd)

theorem card_unpadFinset
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (I : Finset (EvenPadding ι))
    (hI : I ⊆ padFinset (Finset.univ : Finset ι)) :
    (unpadFinset I).card = I.card := by
  rw [← card_padFinset (unpadFinset I), padFinset_unpadFinset I hI]

/-- Dummy-free padded index sets carry exactly the original cluster union. -/
theorem clusterUnion_padAssignment_eq_unpad
    {V ι : Type*} [Fintype V] [Fintype ι]
    [DecidableEq V] [DecidableEq ι]
    (P : ClusterAssignment V ι) (I : Finset (EvenPadding ι))
    (hI : I ⊆ padFinset (Finset.univ : Finset ι)) :
    clusterUnion (padAssignment P) I = clusterUnion P (unpadFinset I) := by
  calc
    clusterUnion (padAssignment P) I =
        clusterUnion (padAssignment P) (padFinset (unpadFinset I)) := by
      rw [padFinset_unpadFinset I hI]
    _ = clusterUnion P (unpadFinset I) :=
      clusterUnion_padFinset P (unpadFinset I)

theorem card_clusterUnion_padAssignment_eq
    {V ι : Type*} [Fintype V] [Fintype ι]
    [DecidableEq V] [DecidableEq ι]
    (P : ClusterAssignment V ι) (I : Finset (EvenPadding ι))
    (hI : I ⊆ padFinset (Finset.univ : Finset ι)) (m : ℕ)
    (hcluster : ∀ i, (clusterVertices P i).card = m) :
    (clusterUnion (padAssignment P) I).card = I.card * m := by
  calc
    (clusterUnion (padAssignment P) I).card =
        (clusterUnion P (unpadFinset I)).card := by
      rw [clusterUnion_padAssignment_eq_unpad P I hI]
    _ = (unpadFinset I).card * m :=
      card_clusterUnion_eq_of_equal P (unpadFinset I) m
        (fun i _ => hcluster i)
    _ = I.card * m := by rw [card_unpadFinset I hI]

/-- A genuine finite matching in an isolated padding cannot support a dummy
vertex. -/
theorem matchingSupport_subset_padFinset_univ
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (R : SimpleGraph ι) [DecidableRel R.Adj]
    (M : (padGraph R).Subgraph) (hM : M.IsMatching) :
    matchingSupport M ⊆ padFinset (Finset.univ : Finset ι) := by
  intro x hx
  cases x with
  | inl i => simp
  | inr d =>
      have hverts : (Sum.inr d : EvenPadding ι) ∈ M.verts :=
        (mem_matchingSupport M _).mp hx
      obtain ⟨y, hdy, _⟩ := hM hverts
      exact False.elim
        (padGraph_not_adj_inr_left R d y (M.adj_sub hdy))

/-- The `V1` cut side produced by Lemma 6.11 is dummy-free. -/
theorem decomposition_V1_subset_padFinset_univ
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    {R : SimpleGraph ι} [DecidableRel R.Adj]
    {L O : Finset (EvenPadding ι)}
    {miss lowerV1 upperV1 upperV2 mbBound : ℕ}
    {C67 : Claim67Certificate (padGraph R) L miss}
    {degreeA : Finset (MatchingEdge C67.M) → ℝ}
    (D : MatchingDecomposition L O miss C67 lowerV1 upperV1 upperV2 mbBound
      degreeA) :
    D.V1 ⊆ padFinset (Finset.univ : Finset ι) := by
  intro x hx
  apply matchingSupport_subset_padFinset_univ R C67.M C67.isMatching
  rw [D.support_union]
  exact Finset.mem_union_left _ hx

/-- Exact host size of the `V1` cluster union, despite the possible one
dummy index in the ambient reduced graph. -/
theorem card_decomposition_V1_clusterUnion
    {V ι : Type*} [Fintype V] [Fintype ι]
    [DecidableEq V] [DecidableEq ι]
    {R : SimpleGraph ι} [DecidableRel R.Adj]
    (P : ClusterAssignment V ι)
    {L O : Finset (EvenPadding ι)}
    {miss lowerV1 upperV1 upperV2 mbBound : ℕ}
    {C67 : Claim67Certificate (padGraph R) L miss}
    {degreeA : Finset (MatchingEdge C67.M) → ℝ}
    (D : MatchingDecomposition L O miss C67 lowerV1 upperV1 upperV2 mbBound
      degreeA)
    (m : ℕ) (hcluster : ∀ i, (clusterVertices P i).card = m) :
    (clusterUnion (padAssignment P) D.V1).card = D.V1.card * m :=
  card_clusterUnion_padAssignment_eq P D.V1
    (decomposition_V1_subset_padFinset_univ D) m hcluster

/-- Padding is monotone in the underlying graph. -/
theorem padGraph_mono
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    {R' R : SimpleGraph ι} (h : R' ≤ R) :
    padGraph R' ≤ padGraph R := by
  intro x y hxy
  cases x with
  | inl i =>
      cases y with
      | inl j =>
          rw [padGraph_adj_inl] at hxy ⊢
          exact h hxy
      | inr d => exact False.elim (padGraph_not_adj_inr_right R' _ d hxy)
  | inr d => exact False.elim (padGraph_not_adj_inr_left R' d _ hxy)

/-- Exact Section-6 EC2 endpoint for a padded Lemma-6.11 cut and the cleaned
degree-form reduced graph.  The only remaining premises are transparent
cardinality and numeric inequalities. -/
theorem zhaoExtremalCaseTwo_of_padded_cleanedDegreeForm
    {n m₀ M miss lowerV1 upperV1 upperV2 mbBound b cross : ℕ}
    {ε d δ α : ℚ}
    (G : SimpleGraph (Fin (2 * n - 2))) [DecidableRel G.Adj]
    (W : DegreeFormWitness G ε d m₀ M)
    [DecidableRel (cleanedReducedGraph W δ).Adj]
    (Rsource : SimpleGraph {Q // Q ∈ W.partition.parts})
    [DecidableRel Rsource.Adj]
    {L O : Finset (EvenPadding {Q // Q ∈ W.partition.parts})}
    (C67 : Claim67Certificate (padGraph Rsource) L miss)
    {degreeA : Finset (MatchingEdge C67.M) → ℝ}
    (D : MatchingDecomposition L O miss C67 lowerV1 upperV1 upperV2 mbBound
      degreeA)
    (hn : 2 ≤ n) (hδd : δ ≤ d)
    (hXupper : D.V1.card * W.clusterSize ≤ n - 1 + b)
    (hXlower : n - 1 ≤ D.V1.card * W.clusterSize + b)
    (hcross :
      ((padGraph (cleanedReducedGraph W δ)).interedges D.V1 D.V2).card ≤
        cross)
    (hnumeric :
      ((cross * (W.clusterSize * W.clusterSize) +
          (D.V1.card * W.clusterSize) *
            (W.exceptional.card + W.loss) +
          2 * (n - 1) * b : ℕ) : ℚ) ≤
        α * ((n - 1 : ℕ) : ℚ) * ((n - 1 : ℕ) : ℚ)) :
    ZhaoExtremalCaseTwo α G := by
  classical
  let P : ClusterAssignment (Fin (2 * n - 2))
      {Q // Q ∈ W.partition.parts} :=
    partitionAssignment W.exceptional W.partition
  let : DecidableRel W.graph.Adj := W.graph_decidable
  have hrespect0 :
      EdgesRespectReducedGraph P W.graph (cleanedReducedGraph W δ) := by
    simpa [P] using cleanedGraph_respects_cleanedReducedGraph W hδd
  have hrespect :
      EdgesRespectReducedGraph (padAssignment P) W.graph
        (padGraph (cleanedReducedGraph W δ)) :=
    edgesRespect_pad P W.graph (cleanedReducedGraph W δ) hrespect0
  have hcluster0 : ∀ i : {Q // Q ∈ W.partition.parts},
      (clusterVertices P i).card = W.clusterSize := by
    intro i
    simpa [P] using W.equal_clusters i.1 i.2
  have hcluster : ∀ i,
      (clusterVertices (padAssignment P) i).card ≤ W.clusterSize := by
    intro i
    cases i with
    | inl i => simp [hcluster0 i]
    | inr e => simp
  have hXcard : (clusterUnion (padAssignment P) D.V1).card =
      D.V1.card * W.clusterSize := by
    exact card_decomposition_V1_clusterUnion P D W.clusterSize hcluster0
  obtain ⟨hdisj, hcover, _⟩ :=
    Erdos547b.ZhaoLemma611Claim618Adapter.reducedCut_of_decomposition D
  refine zhaoExtremalCaseTwo_of_degreeForm_reducedCut
    (P := padAssignment P) (G := G) (H := W.graph)
    (R := padGraph (cleanedReducedGraph W δ))
    (α := α) (hn := hn) (hHG := W.graph_le) (loss := W.loss)
    (hloss := W.degree_loss) (hrespect := hrespect)
    (I := D.V1) (J := D.V2) (m := W.clusterSize) (b := b)
    (cross := cross) (hindices := hdisj) (hindices_cover := hcover)
    (hcluster := hcluster) ?_ ?_ ?_ ?_
  · rw [hXcard]
    exact hXupper
  · rw [hXcard]
    exact hXlower
  · change
      ((padGraph (cleanedReducedGraph W δ)).interedges D.V1 D.V2).card ≤ cross
    exact hcross
  · change
      ((cross * (W.clusterSize * W.clusterSize) +
          (clusterUnion (padAssignment P) D.V1).card *
            ((exceptionalVertices (padAssignment P)).card + W.loss) +
          2 * (n - 1) * b : ℕ) : ℚ) ≤
        α * ((n - 1 : ℕ) : ℚ) * ((n - 1 : ℕ) : ℚ)
    rw [hXcard, exceptionalVertices_padAssignment]
    simpa only [P, exceptionalVertices_partitionAssignment] using hnumeric

/-- Real-bound spelling matching the outputs of Claims 6.17 and 6.18.  The
integer `cross` parameter of the endpoint is chosen to be the actual reduced
crossing-edge count. -/
theorem zhaoExtremalCaseTwo_of_padded_cleanedDegreeForm_realBound
    {n m₀ M miss lowerV1 upperV1 upperV2 mbBound b : ℕ}
    {ε d δ α : ℚ}
    (G : SimpleGraph (Fin (2 * n - 2))) [DecidableRel G.Adj]
    (W : DegreeFormWitness G ε d m₀ M)
    [DecidableRel (cleanedReducedGraph W δ).Adj]
    (Rsource : SimpleGraph {Q // Q ∈ W.partition.parts})
    [DecidableRel Rsource.Adj]
    {L O : Finset (EvenPadding {Q // Q ∈ W.partition.parts})}
    (C67 : Claim67Certificate (padGraph Rsource) L miss)
    {degreeA : Finset (MatchingEdge C67.M) → ℝ}
    (D : MatchingDecomposition L O miss C67 lowerV1 upperV1 upperV2 mbBound
      degreeA)
    (hn : 2 ≤ n) (hδd : δ ≤ d)
    (hXupper : D.V1.card * W.clusterSize ≤ n - 1 + b)
    (hXlower : n - 1 ≤ D.V1.card * W.clusterSize + b)
    (bound : ℝ)
    (hcross :
      (((padGraph (cleanedReducedGraph W δ)).interedges
        D.V1 D.V2).card : ℝ) < bound)
    (hnumeric :
      bound * (W.clusterSize : ℝ) ^ 2 +
          (((D.V1.card * W.clusterSize) *
            (W.exceptional.card + W.loss) : ℕ) : ℝ) +
          ((2 * (n - 1) * b : ℕ) : ℝ) ≤
        (α : ℝ) * ((n - 1 : ℕ) : ℝ) ^ 2) :
    ZhaoExtremalCaseTwo α G := by
  let cross := ((padGraph (cleanedReducedGraph W δ)).interedges
    D.V1 D.V2).card
  have hendpointNumeric :
      ((cross * (W.clusterSize * W.clusterSize) +
          (D.V1.card * W.clusterSize) *
            (W.exceptional.card + W.loss) +
          2 * (n - 1) * b : ℕ) : ℚ) ≤
        α * ((n - 1 : ℕ) : ℚ) * ((n - 1 : ℕ) : ℚ) := by
    apply endpoint_numeric_of_reducedCross_lt cross W.clusterSize
      (D.V1.card * W.clusterSize) (W.exceptional.card + W.loss)
      (n - 1) b bound α
    · exact hcross
    · norm_num only [Nat.cast_mul, Nat.cast_add] at hnumeric ⊢
      exact hnumeric
  apply zhaoExtremalCaseTwo_of_padded_cleanedDegreeForm G W Rsource C67 D
    hn hδd hXupper hXlower (cross := cross)
  · exact le_rfl
  · exact hendpointNumeric

#print axioms padFinset_unpadFinset
#print axioms matchingSupport_subset_padFinset_univ
#print axioms card_decomposition_V1_clusterUnion
#print axioms padGraph_mono
#print axioms zhaoExtremalCaseTwo_of_padded_cleanedDegreeForm
#print axioms zhaoExtremalCaseTwo_of_padded_cleanedDegreeForm_realBound

end Erdos547b.ZhaoPaddedMatchingCut
