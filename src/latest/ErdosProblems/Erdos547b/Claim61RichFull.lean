/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Claim61Full
import ErdosProblems.Erdos547b.LargeClusterReservoir
import ErdosProblems.Erdos547b.PrunedReducedLargeEdges

open scoped BigOperators SimpleGraph

noncomputable section

namespace Erdos547b.ZhaoClaim61RichFull

open Finset SimpleGraph
open ZhaoStability ZhaoDegreeForm ZhaoSection6Dichotomy
open ZhaoEvenReducedPadding ZhaoClaim61Full
open ZhaoQuantitativeLargeClusters ZhaoPrunedReducedLargeEdges
open ZhaoLemma611Full

/-- The complete nonindependent output of quantitative Claim 6.1.  In
addition to the padded Claim-6.7 certificate it retains the actual reduced
edge which witnessed nonindependence and exact high-degree reservoirs in its
two endpoint clusters. -/
structure RichClaim61Certificate
    {V ι : Type*} [Fintype V] [Fintype ι]
    [DecidableEq V] [DecidableEq ι]
    (P : ClusterAssignment V ι)
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (threshold quota : ℕ) (R : SimpleGraph ι) [DecidableRel R.Adj]
    (L : Finset ι) (miss : ℕ) where
  A : ι
  B : ι
  adj : R.Adj A B
  A_mem : A ∈ L
  B_mem : B ∈ L
  A₀ : Finset V
  B₀ : Finset V
  A₀_subset : A₀ ⊆ clusterVertices P A
  B₀_subset : B₀ ⊆ clusterVertices P B
  A₀_card : A₀.card = quota
  B₀_card : B₀.card = quota
  A₀_high : ∀ v ∈ A₀, threshold ≤ G.degree v
  B₀_high : ∀ v ∈ B₀, threshold ≤ G.degree v
  claim67 : Claim67Certificate (padGraph R) (padFinset L) miss
  A_in_claim67O : (Sum.inl A : EvenPadding ι) ∈ claim67.O
  B_in_claim67O : (Sum.inl B : EvenPadding ι) ∈ claim67.O
  matching_edge_meets_large : ∀ e : MatchingEdge claim67.M,
    e.1.out.1 ∈ padFinset L ∨ e.1.out.2 ∈ padFinset L

/-! ## Independent quantitative-large-cluster branch -/

/-- Host-level crossing estimate for a quantitatively large independent
cluster family.  The selected high vertices are only those lying in the
large cluster union; the explicit non-large-cluster error is accounted for
by `highDegreeVerticesInLargeClusters_card_lower`. -/
theorem cleaned_denseCut_of_independent_quantitativeLargeClusters
    {V ι : Type*} [Fintype V] [Fintype ι]
    [DecidableEq V] [DecidableEq ι]
    (P : ClusterAssignment V ι)
    (G H : SimpleGraph V) (R : SimpleGraph ι)
    [DecidableRel G.Adj] [DecidableRel H.Adj] [DecidableRel R.Adj]
    (threshold quota loss : ℕ)
    (hrespect : EdgesRespectReducedGraph P H R)
    (hretained : ∀ v ∈ highDegreeVerticesInLargeClusters P G threshold quota,
      threshold - loss ≤ H.degree v)
    (hLindep : R.IsIndepSet
      (largeClustersAtLeast P G threshold quota : Set ι)) :
    let L := largeClustersAtLeast P G threshold quota
    let X := clusterUnion P L
    let Y := Finset.univ \ X
    let B := highDegreeVerticesInLargeClusters P G threshold quota
    B ⊆ X ∧
      (highDegreeVertices G threshold).card -
          (exceptionalVertices P).card -
          (Fintype.card ι - L.card) * (quota - 1) ≤ B.card ∧
      (∀ v ∈ B, threshold - loss ≤
        Erdos547EC2.degreeInto H v Y) ∧
      B.card * (threshold - loss) ≤ (H.interedges X Y).card := by
  classical
  dsimp only
  let L := largeClustersAtLeast P G threshold quota
  let X := clusterUnion P L
  let Y := Finset.univ \ X
  let B := highDegreeVerticesInLargeClusters P G threshold quota
  have hBX : B ⊆ X := by
    exact highDegreeVerticesInLargeClusters_subset_clusterUnion
      P G threshold quota
  have hBcard :
      (highDegreeVertices G threshold).card -
          (exceptionalVertices P).card -
          (Fintype.card ι - L.card) * (quota - 1) ≤ B.card := by
    exact highDegreeVerticesInLargeClusters_card_lower
      P G threshold quota
  have hcrossDegree : ∀ v ∈ B, threshold - loss ≤
      Erdos547EC2.degreeInto H v Y := by
    intro v hvB
    have hvH : threshold - loss ≤ H.degree v := hretained v hvB
    have hneighbor : H.neighborFinset v ⊆ Y := by
      intro w hw
      apply Finset.mem_sdiff.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      intro hwX
      rw [mem_clusterUnion] at hwX
      obtain ⟨j, hjL, hPwj⟩ := hwX
      have hvX := hBX hvB
      rw [mem_clusterUnion] at hvX
      obtain ⟨i, hiL, hPvi⟩ := hvX
      have hHij : H.Adj v w := by simpa using hw
      have hRij : R.Adj i j := hrespect hPvi hPwj hHij
      exact hLindep hiL hjL hRij.ne hRij
    have hdegInto : H.degree v ≤ Erdos547EC2.degreeInto H v Y := by
      rw [← card_neighborFinset_eq_degree]
      unfold Erdos547EC2.degreeInto
      apply Finset.card_le_card
      intro w hw
      exact Finset.mem_filter.mpr ⟨hneighbor hw, by simpa using hw⟩
    exact hvH.trans hdegInto
  refine ⟨hBX, hBcard, hcrossDegree, ?_⟩
  exact Erdos547EC2.card_mul_le_card_interedges_of_subset_of_degreeInto
    H hBX hcrossDegree

/-! ## Corrected quantitative Claim 6.1 -/

/-- Claim 6.1 with Zhao's quantitative large-cluster family.

The degree-form witness is applied to the host after deleting low--low
edges.  `largeError` is the exact maximum number of high vertices lying in
non-large ordinary clusters.  Thus the independent branch gives a genuine
host EC1 cut, while the nonindependent branch gives the canonical padded
Claim-6.7 certificate on the same quantitative large set. -/
theorem claim6_1_rich_full
    {n m₀ M : ℕ} {ε d α : ℚ}
    (G : SimpleGraph (Fin (2 * n - 2))) [DecidableRel G.Adj]
    (W : DegreeFormWitness
      (pruneSmallEdges G {v | n - 1 ≤ G.degree v}) ε d m₀ M)
    (hn : 2 ≤ n)
    (hlarge : n - 1 ≤ (highDegreeVertices G (n - 1)).card)
    (quota c : ℕ) (hquota : 0 < quota) (hm : 0 < W.clusterSize)
    (hdensitySlots :
      (((2 * (quota - 1) * W.clusterSize : ℕ) : ℚ)) <
        d * (W.clusterSize : ℚ) * (W.clusterSize : ℚ))
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
    let R : SimpleGraph ι := regularityReducedGraph
      (pruneSmallEdges G {v | n - 1 ≤ G.degree v})
      (fun i : ι => i.1) ε d
    let L := largeClustersAtLeast P G (n - 1) quota
    ZhaoExtremalCaseOne α G ∨
      Nonempty (RichClaim61Certificate P G (n - 1) quota R L
        (2 * c + 1)) := by
  classical
  let : DecidableRel W.graph.Adj := W.graph_decidable
  let : Std.Symm W.graph.Adj := W.graph.symm
  dsimp only
  let ι := {Q // Q ∈ W.partition.parts}
  let P : ClusterAssignment (Fin (2 * n - 2)) ι :=
    partitionAssignment W.exceptional W.partition
  let H₀ := pruneSmallEdges G {v | n - 1 ≤ G.degree v}
  let R : SimpleGraph ι := regularityReducedGraph H₀ (fun i : ι => i.1) ε d
  let L := largeClustersAtLeast P G (n - 1) quota
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
    have hi' := reduced_degree_capacity_of_degreeForm P H₀ W.graph R
      W.respects_reduced W.clusterSize q W.loss
      (fun j => (hcluster j).le) W.degree_loss (hLmeeting i hi)
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
    have hretained : ∀ v ∈ B, q - W.loss ≤ W.graph.degree v := by
      intro v hvB
      have hvG : q ≤ G.degree v :=
        degree_of_mem_highDegreeVerticesInLargeClusters P G q quota hvB
      have hvH₀ : q ≤ H₀.degree v := by
        exact (highDegree_iff_pruneSmallEdges_highDegree G q v).mpr hvG
      exact cleaned_degree_ge_threshold_sub_loss
        H₀ W.graph W.loss q W.degree_loss hvH₀
    have hdenseRaw :=
      cleaned_denseCut_of_independent_quantitativeLargeClusters
        P G W.graph R q quota W.loss W.respects_reduced hretained hLindep
    have hdense : B ⊆ X ∧
        q - W.exceptional.card - largeError ≤ B.card ∧
        (∀ v ∈ B, q - W.loss ≤
          Erdos547EC2.degreeInto W.graph v Y) ∧
        B.card * (q - W.loss) ≤ (W.graph.interedges X Y).card := by
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
        (Erdos547EC2.degreeInto_le_card W.graph v Y)
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
    have hhighXY : lower ≤ (W.graph.interedges X Y).card := by
      exact calc
        lower = (q - W.exceptional.card - largeError) * (q - W.loss) := rfl
        _ ≤ B.card * (q - W.loss) :=
          Nat.mul_le_mul_right (q - W.loss) hdense.2.1
        _ ≤ (W.graph.interedges X Y).card := hdense.2.2.2
    have hgraphle : W.graph ≤ G :=
      W.graph_le.trans (pruneSmallEdges_le G {v | q ≤ G.degree v})
    by_cases hXsmall : X.card ≤ q
    · apply zhaoExtremalCaseOne_of_cleaned_denseCut
        G W.graph α hn hgraphle X Y b lower
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
        G W.graph α hn hgraphle Y X b lower
      · exact Finset.disjoint_sdiff.symm
      · exact hcoverYX
      · exact hYsmall
      · dsimp only [b]
        omega
      · rw [show (W.graph.interedges Y X).card =
            (W.graph.interedges X Y).card by
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
              exact (every_degreeForm_reduced_edge_meets_quantitativelyLarge
                G (n - 1) quota W hm hdensitySlots) hij
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

end Erdos547b.ZhaoClaim61RichFull
