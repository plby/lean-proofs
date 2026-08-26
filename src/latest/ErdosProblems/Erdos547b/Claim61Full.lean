/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.DegreeForm
import ErdosProblems.Erdos547b.Section6Dichotomy
import ErdosProblems.Erdos547b.EvenReducedPadding

open scoped BigOperators SimpleGraph

noncomputable section

namespace Erdos547b.ZhaoClaim61Full

open Finset SimpleGraph
open ZhaoStability ZhaoDegreeForm ZhaoSection6Dichotomy
open ZhaoEvenReducedPadding

/-- The concrete reduced graph has a classical adjacency decision procedure.
This local instance lets the canonical `padGraph` decision procedure appear
already in the statement of `claim6_1_full`. -/
noncomputable instance regularityReducedGraph.instDecidableRelClaim61
    {V ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (C : ι → Finset V) (epsilon d : ℚ) :
    DecidableRel (regularityReducedGraph G C epsilon d).Adj :=
  Classical.decRel _

/-! ## Exact independent-large-cluster cut -/

/-- If the reduced large-cluster set is independent, every cleaned neighbor
of a high-degree nonexceptional vertex crosses from the union of large
clusters to its complement.  This is the missing host-level counting step
in the independent branch of Claim 6.1. -/
theorem cleaned_denseCut_of_independent_largeClusters
    {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : ClusterAssignment (Fin (2 * n - 2)) ι)
    (G H : SimpleGraph (Fin (2 * n - 2))) (R : SimpleGraph ι)
    [DecidableRel G.Adj] [DecidableRel H.Adj] [DecidableRel R.Adj]
    (hrespect : EdgesRespectReducedGraph P H R)
    (loss : ℕ) (hloss : DegreeLossAtMost G H loss)
    (hlarge : n - 1 ≤
      (Finset.univ.filter fun v => n - 1 ≤ G.degree v).card)
    (hLindep : R.IsIndepSet
      (clustersMeeting P
        (Finset.univ.filter fun v => n - 1 ≤ G.degree v) : Set ι)) :
    let S := Finset.univ.filter fun v => n - 1 ≤ G.degree v
    let L := clustersMeeting P S
    let X := clusterUnion P L
    let Y := Finset.univ \ X
    let B := S \ exceptionalVertices P
    B ⊆ X ∧
      n - 1 - (exceptionalVertices P).card ≤ B.card ∧
      (∀ v ∈ B, n - 1 - loss ≤ Erdos547EC2.degreeInto H v Y) ∧
      B.card * (n - 1 - loss) ≤ (H.interedges X Y).card := by
  classical
  dsimp only
  let S := Finset.univ.filter fun v => n - 1 ≤ G.degree v
  let L := clustersMeeting P S
  let X := clusterUnion P L
  let Y := Finset.univ \ X
  let B := S \ exceptionalVertices P
  have hBX : B ⊆ X := by
    intro v hv
    have hvS : v ∈ S := (Finset.mem_sdiff.mp hv).1
    have hvNotE : v ∉ exceptionalVertices P := (Finset.mem_sdiff.mp hv).2
    cases hPv : P v with
    | none =>
        exact False.elim (hvNotE ((mem_exceptionalVertices P v).mpr hPv))
    | some i =>
        rw [mem_clusterUnion]
        refine ⟨i, ?_, hPv⟩
        rw [mem_clustersMeeting]
        exact ⟨v, hvS, hPv⟩
  have hBcard : n - 1 - (exceptionalVertices P).card ≤ B.card := by
    have hpartition := Finset.card_sdiff_add_card_inter S (exceptionalVertices P)
    have hinter : (S ∩ exceptionalVertices P).card ≤
        (exceptionalVertices P).card :=
      Finset.card_le_card (Finset.inter_subset_right)
    change n - 1 ≤ S.card at hlarge
    change B.card + (S ∩ exceptionalVertices P).card = S.card at hpartition
    omega
  have hcrossDegree : ∀ v ∈ B,
      n - 1 - loss ≤ Erdos547EC2.degreeInto H v Y := by
    intro v hvB
    have hvS : v ∈ S := (Finset.mem_sdiff.mp hvB).1
    have hvG : n - 1 ≤ G.degree v := by
      simpa [S] using hvS
    have hvH : n - 1 - loss ≤ H.degree v :=
      cleaned_degree_ge_threshold_sub_loss G H loss (n - 1) hloss hvG
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

/-! ## The unconditional Claim 6.1 split -/

/-- Full Claim 6.1 adapter from a concrete degree-form witness.

The only additional hypotheses are the explicit integer consequences of the
constant hierarchy.  `hclaim67Scale` converts vertex capacity to reduced
degree/cardinality, and `hEC1numeric` is exactly the density inequality used
by the balanced-cut endpoint.  No dichotomy or embedding conclusion is
assumed.

In the nonindependent branch the reduced graph is even-padded by at most one
isolated vertex and the concrete Gallai--Edmonds constructor supplies the
`Claim67Certificate`. -/
theorem claim6_1_full
    {n m₀ M : ℕ} {ε d α : ℚ}
    (G : SimpleGraph (Fin (2 * n - 2))) [DecidableRel G.Adj]
    (W : DegreeFormWitness G ε d m₀ M)
    (hn : 2 ≤ n)
    (hlarge : n - 1 ≤
      (Finset.univ.filter fun v => n - 1 ≤ G.degree v).card)
    (c : ℕ) (hm : 0 < W.clusterSize)
    (hEsmall : W.exceptional.card < n - 1)
    (hclaim67Scale :
      (paddedHalf {Q // Q ∈ W.partition.parts} - c) * W.clusterSize ≤
        (n - 1 - W.loss) - W.exceptional.card)
    (hEC1numeric :
      (1 - α) * ((n - 1 : ℕ) : ℚ) * ((n - 1 : ℕ) : ℚ) ≤
        ((((n - 1 - W.exceptional.card) * (n - 1 - W.loss)) -
          2 * (n - 1) * (W.exceptional.card + W.loss) : ℕ) : ℚ)) :
    let ι := {Q // Q ∈ W.partition.parts}
    let P : ClusterAssignment (Fin (2 * n - 2)) ι :=
      partitionAssignment W.exceptional W.partition
    let R : SimpleGraph ι := regularityReducedGraph G (fun i : ι => i.1) ε d
    let S := Finset.univ.filter fun v => n - 1 ≤ G.degree v
    let L := clustersMeeting P S
    ZhaoExtremalCaseOne α G ∨
      Nonempty (Claim67Certificate (padGraph R) (padFinset L)
        (2 * c + 1)) := by
  classical
  letI : DecidableRel W.graph.Adj := W.graph_decidable
  letI : Std.Symm W.graph.Adj := W.graph.symm
  dsimp only
  let ι := {Q // Q ∈ W.partition.parts}
  let P : ClusterAssignment (Fin (2 * n - 2)) ι :=
    partitionAssignment W.exceptional W.partition
  let R : SimpleGraph ι := regularityReducedGraph G (fun i : ι => i.1) ε d
  let S := Finset.univ.filter fun v => n - 1 ≤ G.degree v
  let L := clustersMeeting P S
  let X := clusterUnion P L
  let Y := Finset.univ \ X
  let B := S \ exceptionalVertices P
  let q := n - 1
  let b := W.exceptional.card + W.loss
  let lower := (q - W.exceptional.card) * (q - W.loss)
  have hE : exceptionalVertices P = W.exceptional := by
    exact exceptionalVertices_partitionAssignment W.exceptional W.partition
  have hcluster : ∀ i : ι, (clusterVertices P i).card = W.clusterSize := by
    intro i
    rw [show clusterVertices P i = i.1 by
      exact clusterVertices_partitionAssignment W.exceptional W.partition i]
    exact W.equal_clusters i.1 i.2
  have hdegreeCapacity : ∀ i ∈ L,
      (q - W.loss) - W.exceptional.card ≤ R.degree i * W.clusterSize := by
    intro i hi
    have hi' := reduced_degree_capacity_of_degreeForm P G W.graph R
      W.respects_reduced W.clusterSize q W.loss
      (fun j => (hcluster j).le) W.degree_loss hi
    simpa only [hE] using hi'
  have hcardCapacity : q - W.exceptional.card ≤ L.card * W.clusterSize := by
    have hupper := card_le_exceptional_add_clustersMeeting_mul P S
      W.clusterSize (fun j => (hcluster j).le)
    change q ≤ S.card at hlarge
    change S.card ≤ (exceptionalVertices P).card + L.card * W.clusterSize at hupper
    rw [hE] at hupper
    omega
  have hLdegree : ∀ i ∈ L,
      paddedHalf ι - c ≤ R.degree i := by
    intro i hi
    apply Nat.le_of_mul_le_mul_right (c := W.clusterSize) ?_ hm
    exact hclaim67Scale.trans (hdegreeCapacity i hi)
  have hLcard : paddedHalf ι - c ≤ L.card := by
    apply Nat.le_of_mul_le_mul_right (c := W.clusterSize) ?_ hm
    exact hclaim67Scale.trans <| by
      apply hcardCapacity.trans'
      omega
  by_cases hLindep : R.IsIndepSet (L : Set ι)
  · left
    have hdenseRaw := cleaned_denseCut_of_independent_largeClusters
      P G W.graph R W.respects_reduced W.loss W.degree_loss hlarge
        hLindep
    have hdense : B ⊆ X ∧ q - W.exceptional.card ≤ B.card ∧
      (∀ v ∈ B, q - W.loss ≤ Erdos547EC2.degreeInto W.graph v Y) ∧
      B.card * (q - W.loss) ≤ (W.graph.interedges X Y).card := by
      simpa only [S, L, X, Y, B, q, hE] using hdenseRaw
    have hBnonempty : B.Nonempty := by
      apply Finset.nonempty_iff_ne_empty.mpr
      intro hB
      have : B.card = 0 := by simp [hB]
      have hpos : 0 < q - W.exceptional.card := by
        simp only [q]
        omega
      omega
    have hYlower : q - W.loss ≤ Y.card := by
      obtain ⟨v, hvB⟩ := hBnonempty
      exact (hdense.2.2.1 v hvB).trans
        (Erdos547EC2.degreeInto_le_card W.graph v Y)
    have hXlower : q - W.exceptional.card ≤ X.card :=
      hdense.2.1.trans (Finset.card_le_card hdense.1)
    have hunivcard : (Finset.univ : Finset (Fin (2 * n - 2))).card = 2 * q := by
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
        lower = (q - W.exceptional.card) * (q - W.loss) := rfl
        _ ≤ B.card * (q - W.loss) :=
          Nat.mul_le_mul_right (q - W.loss) hdense.2.1
        _ ≤ (W.graph.interedges X Y).card := hdense.2.2.2
    by_cases hXsmall : X.card ≤ q
    · apply zhaoExtremalCaseOne_of_cleaned_denseCut
        G W.graph α hn W.graph_le X Y b lower
      · exact Finset.disjoint_sdiff
      · exact Finset.union_sdiff_of_subset (Finset.subset_univ X)
      · exact hXsmall
      · dsimp only [b]
        omega
      · exact hhighXY
      · simpa [q, b, lower] using hEC1numeric
    · have hYsmall : Y.card ≤ q := by omega
      have hcoverYX : Y ∪ X = Finset.univ := by
        rw [Finset.union_comm]
        exact Finset.union_sdiff_of_subset (Finset.subset_univ X)
      apply zhaoExtremalCaseOne_of_cleaned_denseCut
        G W.graph α hn W.graph_le Y X b lower
      · exact Finset.disjoint_sdiff.symm
      · exact hcoverYX
      · exact hYsmall
      · dsimp only [b]
        omega
      · rw [show (W.graph.interedges Y X).card =
            (W.graph.interedges X Y).card by
          exact Rel.card_interedges_comm Y X]
        exact hhighXY
      · simpa [q, b, lower] using hEC1numeric
  · right
    exact exists_claim67Certificate_of_padding R L c hLcard hLdegree hLindep

#print axioms Erdos547b.ZhaoClaim61Full.cleaned_denseCut_of_independent_largeClusters
#print axioms Erdos547b.ZhaoClaim61Full.claim6_1_full

end Erdos547b.ZhaoClaim61Full
