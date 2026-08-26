/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Claim61RichFull
import ErdosProblems.Erdos547b.ClusterPairPruning

/-!
# Rich Claim 6.1 after whole-pair pruning

This is the degree-form constructor with Zhao's separate deletion of pairs
between nonlarge clusters. It reuses the existing rich certificate and dense
cut argument. Unlike the older constructor, it needs no inequality forcing
the regularity cutoff above the high-degree reservoir fraction.
-/

open scoped BigOperators SimpleGraph
noncomputable section

namespace Erdos547b.ZhaoClaim61PairPrunedFull

open Finset SimpleGraph
open Erdos547b.ZhaoStability Erdos547b.ZhaoDegreeForm
open Erdos547b.ZhaoSection6Dichotomy Erdos547b.ZhaoEvenReducedPadding
open Erdos547b.ZhaoClaim61Full Erdos547b.ZhaoQuantitativeLargeClusters
open Erdos547b.ZhaoPrunedReducedLargeEdges Erdos547b.ZhaoLemma611Full
open Erdos547b.ZhaoClaim61RichFull Erdos547b.ZhaoClusterPairPruning

/-- Rich Claim 6.1 with independently chosen reservoir quota and density
cutoff. Whole-pair deletion preserves every degree used in the proof. -/
theorem claim6_1_rich_pairPruned_full
    {n m₀ M : ℕ} {ε d α : ℚ}
    (G : SimpleGraph (Fin (2 * n - 2))) [DecidableRel G.Adj]
    (W : DegreeFormWitness
      (pruneSmallEdges G {v | n - 1 ≤ G.degree v}) ε d m₀ M)
    (hn : 2 ≤ n)
    (hlarge : n - 1 ≤ (highDegreeVertices G (n - 1)).card)
    (quota c : ℕ) (hquota : 0 < quota) (hm : 0 < W.clusterSize)
    (hRichPositive :
      W.exceptional.card +
        (Fintype.card {Q // Q ∈ W.partition.parts} -
          (largeClustersAtLeast
            (partitionAssignment W.exceptional W.partition) G (n - 1) quota).card) *
            (quota - 1) < n - 1)
    (hdegreeScale :
      (paddedHalf {Q // Q ∈ W.partition.parts} - c) * W.clusterSize ≤
        (n - 1 - W.loss) - W.exceptional.card)
    (hcardScale :
      (paddedHalf {Q // Q ∈ W.partition.parts} - c) * W.clusterSize ≤
        n - 1 - W.exceptional.card -
          (Fintype.card {Q // Q ∈ W.partition.parts} -
            (largeClustersAtLeast
              (partitionAssignment W.exceptional W.partition) G
                (n - 1) quota).card) * (quota - 1))
    (hEC1numeric :
      let largeError :=
        (Fintype.card {Q // Q ∈ W.partition.parts} -
          (largeClustersAtLeast
            (partitionAssignment W.exceptional W.partition) G
              (n - 1) quota).card) * (quota - 1)
      let b := W.exceptional.card + W.loss + largeError
      let lower :=
        (n - 1 - W.exceptional.card - largeError) * (n - 1 - W.loss)
      (1 - α) * ((n - 1 : ℕ) : ℚ) * ((n - 1 : ℕ) : ℚ) ≤
        ((lower - 2 * (n - 1) * b : ℕ) : ℚ)) :
    let ι := {Q // Q ∈ W.partition.parts}
    let P : ClusterAssignment (Fin (2 * n - 2)) ι :=
      partitionAssignment W.exceptional W.partition
    let L := largeClustersAtLeast P G (n - 1) quota
    let R : SimpleGraph ι := pruneSmallEdges
      (regularityReducedGraph (pruneSmallEdges G {v | n - 1 ≤ G.degree v})
        (fun i : ι => i.1) ε d) (L : Set ι)
    ZhaoExtremalCaseOne α G ∨
      Nonempty (RichClaim61Certificate P G (n - 1) quota R L
        (2 * c + 1)) := by
  classical
  let : DecidableRel W.graph.Adj := W.graph_decidable
  dsimp only
  let ι := {Q // Q ∈ W.partition.parts}
  let P : ClusterAssignment (Fin (2 * n - 2)) ι :=
    partitionAssignment W.exceptional W.partition
  let H₀ := pruneSmallEdges G {v | n - 1 ≤ G.degree v}
  let R₀ : SimpleGraph ι := regularityReducedGraph H₀ (fun i : ι => i.1) ε d
  let L := largeClustersAtLeast P G (n - 1) quota
  let R : SimpleGraph ι := pruneSmallEdges R₀ (L : Set ι)
  let H := pairPrunedGraph P W.graph L
  let : Std.Symm H.Adj := H.symm
  have hrespect : EdgesRespectReducedGraph P H R :=
    respects_pruned_reduced_graph P W.graph R₀ L W.respects_reduced
  let X := clusterUnion P L
  let Y := Finset.univ \ X
  let B := highDegreeVerticesInLargeClusters P G (n - 1) quota
  let q := n - 1
  let largeError := (Fintype.card ι - L.card) * (quota - 1)
  let b := W.exceptional.card + W.loss + largeError
  let lower := (q - W.exceptional.card - largeError) * (q - W.loss)
  have hE : exceptionalVertices P = W.exceptional := by
    exact exceptionalVertices_partitionAssignment W.exceptional W.partition
  have hcluster : ∀ i : ι, (clusterVertices P i).card = W.clusterSize := by
    intro i
    rw [show clusterVertices P i = i.1 by
      exact clusterVertices_partitionAssignment W.exceptional W.partition i]
    exact W.equal_clusters i.1 i.2
  have hLmeeting : ∀ i ∈ L,
      i ∈ clustersMeeting P (highDegreeVertices H₀ q) := by
    intro i hi
    have hrescard := largeVertexReservoir_card P G q quota hi
    have hresnonempty : (largeVertexReservoir P G q i).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hempty
      have : (largeVertexReservoir P G q i).card = 0 := by simp [hempty]
      omega
    obtain ⟨v, hv⟩ := hresnonempty
    rw [mem_clustersMeeting]
    refine ⟨v, ?_, ?_⟩
    · rw [mem_highDegreeVertices]
      apply (highDegree_iff_pruneSmallEdges_highDegree G q v).mpr
      exact degree_of_mem_largeVertexReservoir P G q i hv
    · exact (mem_clusterVertices P i v).mp
        (largeVertexReservoir_subset_cluster P G q i hv)
  have hdegreeCapacity : ∀ i ∈ L,
      (q - W.loss) - W.exceptional.card ≤ R.degree i * W.clusterSize := by
    intro i hi
    have hmeeting := hLmeeting i hi
    rw [mem_clustersMeeting] at hmeeting
    obtain ⟨v, hvHigh, hvP⟩ := hmeeting
    have hvDegree : q ≤ H₀.degree v := (mem_highDegreeVertices H₀ q v).1 hvHigh
    have hretained : q - W.loss ≤ H.degree v := by
      change q - W.loss ≤ (pairPrunedGraph P W.graph L).degree v
      rw [degree_eq_of_large_cluster P W.graph L hi hvP]
      exact cleaned_degree_ge_threshold_sub_loss
        H₀ W.graph W.loss q W.degree_loss hvDegree
    have hi' := threshold_sub_exceptional_le_reduced_degree_mul
      P H R hrespect W.clusterSize (q - W.loss)
      (fun j => (hcluster j).le) hvP hretained
    simpa only [hE] using hi'
  have hcardCapacity :
      q - W.exceptional.card - largeError ≤ L.card * W.clusterSize := by
    have hupper := highDegree_card_le_exceptional_add_large_small
      P G q quota W.clusterSize hquota (fun j => (hcluster j).le)
    change q ≤ (highDegreeVertices G q).card at hlarge
    rw [hE] at hupper
    dsimp only [largeError, L]
    dsimp only [q] at hlarge hupper ⊢
    have htotal := hlarge.trans hupper
    rw [Nat.sub_le_iff_le_add, Nat.sub_le_iff_le_add]
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htotal
  have hLdegree : ∀ i ∈ L, paddedHalf ι - c ≤ R.degree i := by
    intro i hi
    apply Nat.le_of_mul_le_mul_right (c := W.clusterSize) ?_ hm
    exact hdegreeScale.trans (hdegreeCapacity i hi)
  have hLcard : paddedHalf ι - c ≤ L.card := by
    apply Nat.le_of_mul_le_mul_right (c := W.clusterSize) ?_ hm
    exact hcardScale.trans hcardCapacity
  by_cases hLindep : R.IsIndepSet (L : Set ι)
  · left
    have hretained : ∀ v ∈ B, q - W.loss ≤ H.degree v := by
      intro v hvB
      have hvG : q ≤ G.degree v :=
        degree_of_mem_highDegreeVerticesInLargeClusters P G q quota hvB
      have hvH₀ : q ≤ H₀.degree v := by
        exact (highDegree_iff_pruneSmallEdges_highDegree G q v).mpr hvG
      have hvX := highDegreeVerticesInLargeClusters_subset_clusterUnion
        P G q quota hvB
      obtain ⟨i, hi, hvP⟩ := (mem_clusterUnion P L v).1 hvX
      change q - W.loss ≤ (pairPrunedGraph P W.graph L).degree v
      rw [degree_eq_of_large_cluster P W.graph L hi hvP]
      exact cleaned_degree_ge_threshold_sub_loss
        H₀ W.graph W.loss q W.degree_loss hvH₀
    have hdenseRaw :=
      cleaned_denseCut_of_independent_quantitativeLargeClusters
        P G H R q quota W.loss hrespect hretained hLindep
    have hdense : B ⊆ X ∧
        q - W.exceptional.card - largeError ≤ B.card ∧
        (∀ v ∈ B, q - W.loss ≤
          Erdos547EC2.degreeInto H v Y) ∧
        B.card * (q - W.loss) ≤ (H.interedges X Y).card := by
      rcases hdenseRaw with ⟨hBX, hBcardRaw, hdegreeRaw, hcrossRaw⟩
      refine ⟨hBX, ?_, hdegreeRaw, hcrossRaw⟩
      have hlargeQ : q ≤ (highDegreeVertices G q).card := by
        simpa only [q] using hlarge
      have hmono :
          q - W.exceptional.card - largeError ≤
            (highDegreeVertices G q).card - W.exceptional.card - largeError :=
        Nat.sub_le_sub_right
          (Nat.sub_le_sub_right hlargeQ W.exceptional.card) largeError
      apply hmono.trans
      simpa only [L, B, q, largeError, hE] using hBcardRaw
    have hBnonempty : B.Nonempty := by
      apply Finset.nonempty_iff_ne_empty.mpr
      intro hB
      have hzero : B.card = 0 := by simp [hB]
      have hpos : 0 < q - W.exceptional.card - largeError := by
        dsimp only [q, largeError, L, P, ι]
        omega
      omega
    have hYlower : q - W.loss ≤ Y.card := by
      obtain ⟨v, hvB⟩ := hBnonempty
      exact (hdense.2.2.1 v hvB).trans
        (Erdos547EC2.degreeInto_le_card H v Y)
    have hXlower : q - W.exceptional.card - largeError ≤ X.card :=
      hdense.2.1.trans (Finset.card_le_card hdense.1)
    have hunivcard :
        (Finset.univ : Finset (Fin (2 * n - 2))).card = 2 * q := by
      simp [q]
      omega
    have hXYcard : X.card + Y.card = 2 * q := by
      dsimp only [Y]
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ X), hunivcard]
      have hXle : X.card ≤ 2 * q := by
        rw [← hunivcard]
        exact Finset.card_le_card (Finset.subset_univ X)
      omega
    have hhighXY : lower ≤ (H.interedges X Y).card := by
      exact calc
        lower = (q - W.exceptional.card - largeError) * (q - W.loss) := rfl
        _ ≤ B.card * (q - W.loss) :=
          Nat.mul_le_mul_right (q - W.loss) hdense.2.1
        _ ≤ (H.interedges X Y).card := hdense.2.2.2
    have hgraphle : H ≤ G :=
      (pairPrunedGraph_le P W.graph L).trans
        (W.graph_le.trans (pruneSmallEdges_le G {v | q ≤ G.degree v}))
    by_cases hXsmall : X.card ≤ q
    · apply zhaoExtremalCaseOne_of_cleaned_denseCut
        G H α hn hgraphle X Y b lower
      · exact Finset.disjoint_sdiff
      · exact Finset.union_sdiff_of_subset (Finset.subset_univ X)
      · exact hXsmall
      · dsimp only [b]
        omega
      · exact hhighXY
      · simpa only [q, b, lower] using hEC1numeric
    · have hYsmall : Y.card ≤ q := by omega
      have hcoverYX : Y ∪ X = Finset.univ := by
        rw [Finset.union_comm]
        exact Finset.union_sdiff_of_subset (Finset.subset_univ X)
      apply zhaoExtremalCaseOne_of_cleaned_denseCut
        G H α hn hgraphle Y X b lower
      · exact Finset.disjoint_sdiff.symm
      · exact hcoverYX
      · exact hYsmall
      · dsimp only [b]
        omega
      · rw [show (H.interedges Y X).card =
            (H.interedges X Y).card by
          exact Rel.card_interedges_comm Y X]
        exact hhighXY
      · simpa only [q, b, lower] using hEC1numeric
  · right
    obtain ⟨C67⟩ :=
      exists_claim67Certificate_of_padding R L c hLcard hLdegree hLindep
    obtain ⟨x, hx, y, hy, hxy⟩ := C67.adjacentLarge
    have hxL : x ∈ padFinset L := (Finset.mem_inter.mp hx).1
    have hxO : x ∈ C67.O := (Finset.mem_inter.mp hx).2
    have hyL : y ∈ padFinset L := (Finset.mem_inter.mp hy).1
    have hyO : y ∈ C67.O := (Finset.mem_inter.mp hy).2
    cases x with
    | inr e =>
        exact False.elim (padGraph_not_adj_inr_left R e y hxy)
    | inl A =>
        cases y with
        | inr e =>
            exact False.elim
              (padGraph_not_adj_inr_right R (Sum.inl A) e hxy)
        | inl B =>
            have hA : A ∈ L := by simpa using hxL
            have hB : B ∈ L := by simpa using hyL
            have hAB : R.Adj A B := (padGraph_adj_inl R A B).mp hxy
            obtain ⟨A₀, hA₀sub, hA₀card, hA₀high⟩ :=
              exists_reservoir_card_eq P G q quota hA
            obtain ⟨B₀, hB₀sub, hB₀card, hB₀high⟩ :=
              exists_reservoir_card_eq P G q quota hB
            have hReducedEdgeMeets : ∀ {i j : ι},
                R.Adj i j → i ∈ L ∨ j ∈ L := by
              intro i j hij
              exact hij.2
            have hMatchingEdgeMeets : ∀ e : MatchingEdge C67.M,
                e.1.out.1 ∈ padFinset L ∨ e.1.out.2 ∈ padFinset L :=
              every_claim67_matching_edge_meets_large
                R L (2 * c + 1) C67 (@hReducedEdgeMeets)
            exact ⟨
              { A := A
                B := B
                adj := hAB
                A_mem := hA
                B_mem := hB
                A₀ := A₀
                B₀ := B₀
                A₀_subset := hA₀sub
                B₀_subset := hB₀sub
                A₀_card := hA₀card
                B₀_card := hB₀card
                A₀_high := hA₀high
                B₀_high := hB₀high
                claim67 := C67
                A_in_claim67O := hxO
                B_in_claim67O := hyO
                matching_edge_meets_large := hMatchingEdgeMeets }⟩

end Erdos547b.ZhaoClaim61PairPrunedFull

#print axioms Erdos547b.ZhaoClaim61PairPrunedFull.claim6_1_rich_pairPruned_full
