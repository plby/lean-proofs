/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Claim61Full
import ErdosProblems.Erdos547b.Claim61Numerics
import ErdosProblems.Erdos547b.DegreeFormQuantitative
import ErdosProblems.Erdos547b.Lemma611Claim618Adapter
import ErdosProblems.Erdos547b.Lemma611RootAccess
import ErdosProblems.Erdos547b.PaddedMatchingCut
import ErdosProblems.Erdos547b.PrunedReducedLargeEdges
import ErdosProblems.Erdos547b.RoundedScales
import ErdosProblems.Erdos547b.SparseProperty

open scoped SimpleGraph

noncomputable section

namespace Erdos547b.ZhaoStabilityPropertyFull

open Finset SimpleGraph
open Erdos547b.ZhaoStability
open Erdos547b.ZhaoDegreeForm
open Erdos547b.ZhaoDegreeFormQuantitative
open Erdos547b.ZhaoClaim61Full
open Erdos547b.ZhaoClaim61Numerics
open Erdos547b.ZhaoEvenReducedPadding
open Erdos547b.ZhaoPrunedReducedLargeEdges
open Erdos547b.ZhaoSparseAssembly

/-- The structural parameter is chosen below the requested error, the
unconditional sparse-embedding cap, and `1/2`. -/
def sourceAlpha (α : ℚ) : ℚ := min α (min sparseCap (1 / 4))

theorem sourceAlpha_spec {α : ℚ} (hα : 0 < α) :
    0 < sourceAlpha α ∧ sourceAlpha α ≤ α ∧
      sourceAlpha α ≤ sparseCap ∧ sourceAlpha α < 1 / 2 := by
  have hcap : 0 < sparseCap := sparseCap_pos
  have hquarter : (0 : ℚ) < 1 / 4 := by norm_num
  refine ⟨lt_min hα (lt_min hcap hquarter), min_le_left _ _,
    (min_le_right α _).trans (min_le_left _ _), ?_⟩
  exact (min_le_right α _).trans (min_le_right _ _) |>.trans_lt (by norm_num)

/-! ## The pointwise large-error branch -/

/-- Every Ramsey host has a literal equal bipartition. -/
theorem exists_ramseyBalancedCut (n : ℕ) (hn : 1 ≤ n) :
    ∃ V₁ V₂ : Finset (Fin (2 * n - 2)), IsRamseyBalancedCut V₁ V₂ := by
  classical
  let q := n - 1
  have hcard : (Finset.univ : Finset (Fin (2 * n - 2))).card = 2 * q := by
    simp only [Finset.card_univ, Fintype.card_fin]
    dsimp only [q]
    omega
  have hq : q ≤ (Finset.univ : Finset (Fin (2 * n - 2))).card := by
    rw [hcard]
    omega
  obtain ⟨V₁, hV₁sub, hV₁card⟩ :=
    Finset.exists_subset_card_eq hq
  let V₂ := Finset.univ \ V₁
  have hV₂card : V₂.card = q := by
    dsimp only [V₂]
    rw [Finset.card_sdiff_of_subset hV₁sub, hcard, hV₁card]
    omega
  refine ⟨V₁, V₂, Finset.disjoint_sdiff,
    Finset.union_sdiff_of_subset hV₁sub, ?_, ?_⟩
  · simpa [q] using hV₁card
  · simpa [q] using hV₂card

/-- If `α ≥ 1/2`, every graph already lies in one of the two exact extremal
cases.  This removes the large-`α` branch before regularity is invoked. -/
theorem extremalCaseOne_or_two_of_half_le
    {n : ℕ} (G : SimpleGraph (Fin (2 * n - 2)))
    [hGdec : DecidableRel G.Adj]
    (α : ℚ) (hn : 1 ≤ n) (hα : (1 : ℚ) / 2 ≤ α) :
    ZhaoExtremalCaseOne α G ∨ ZhaoExtremalCaseTwo α G := by
  have hdec : hGdec = Classical.decRel G.Adj := Subsingleton.elim _ _
  cases hdec
  classical
  unfold ZhaoExtremalCaseOne ZhaoExtremalCaseTwo
  obtain ⟨V₁, V₂, hcut⟩ := exists_ramseyBalancedCut n hn
  by_cases hsparse : G.edgeDensity V₁ V₂ ≤ α
  · exact Or.inr ⟨V₁, V₂, hcut, hsparse⟩
  · left
    refine ⟨V₁, V₂, hcut, ?_⟩
    have hdense : α < G.edgeDensity V₁ V₂ := lt_of_not_ge hsparse
    have hthreshold : 1 - α ≤ α := by linarith
    exact hthreshold.trans hdense.le

/-- Dense extremality is monotone when edges are added. -/
theorem extremalCaseOne_mono_graph
    {n : ℕ} {H G : SimpleGraph (Fin (2 * n - 2))}
    [hHdec : DecidableRel H.Adj] [hGdec : DecidableRel G.Adj]
    (hHG : H ≤ G) {α : ℚ} (hH : ZhaoExtremalCaseOne α H) :
    ZhaoExtremalCaseOne α G := by
  have hdecH : hHdec = Classical.decRel H.Adj := Subsingleton.elim _ _
  have hdecG : hGdec = Classical.decRel G.Adj := Subsingleton.elim _ _
  cases hdecH
  cases hdecG
  classical
  unfold ZhaoExtremalCaseOne at hH ⊢
  obtain ⟨V₁, V₂, hcut, hdense⟩ := hH
  refine ⟨V₁, V₂, hcut, hdense.trans ?_⟩
  rw [H.edgeDensity_def, G.edgeDensity_def]
  gcongr
  intro p hp
  have hp' := (SimpleGraph.mem_interedges_iff H).mp hp
  exact (SimpleGraph.mem_interedges_iff G).mpr
    ⟨hp'.1, hp'.2.1, hHG hp'.2.2⟩

/-- Increasing the error parameter weakens the dense extremal condition. -/
theorem extremalCaseOne_mono_parameter
    {n : ℕ} {G : SimpleGraph (Fin (2 * n - 2))}
    {β α : ℚ} (hβα : β ≤ α) (hβ : ZhaoExtremalCaseOne β G) :
    ZhaoExtremalCaseOne α G := by
  obtain ⟨V₁, V₂, hcut, hdense⟩ := hβ
  refine ⟨V₁, V₂, hcut, ?_⟩
  exact (by linarith : 1 - α ≤ 1 - β).trans hdense

/-- Containment of all allowed trees is likewise monotone when edges are
added. -/
theorem containsAllTrees_mono_graph
    {n : ℕ} {H G : SimpleGraph (Fin (2 * n - 2))}
    (hHG : H ≤ G) (hH : ZhaoContainsAllTrees H) :
    ZhaoContainsAllTrees G := by
  intro t T hT ht
  exact (hH t T hT ht).trans_le hHG

/-- The sparse endpoint on the pruned host is not falsely lifted as an EC2
statement about `G`.  Instead the already unconditional sparse embedding
theorem turns it into containment in the pruned host, which then lifts to
`G`. -/
theorem containsAllTrees_of_pruned_extremalCaseTwo
    {n : ℕ} (G : SimpleGraph (Fin (2 * n - 2))) [DecidableRel G.Adj]
    (β : ℚ) (hβ : 0 < β) (hβcap : β ≤ sparseCap)
    (hn : largeThreshold + 1 ≤ n)
    (hlarge : n - 1 ≤
      (Finset.univ.filter fun v => n - 1 ≤ G.degree v).card)
    (hEC2 : ZhaoExtremalCaseTwo β
      (pruneSmallEdges G {v | n - 1 ≤ G.degree v})) :
    ZhaoContainsAllTrees G := by
  let H := pruneSmallEdges G {v | n - 1 ≤ G.degree v}
  have hlargeH : n - 1 ≤
      (Finset.univ.filter fun v => n - 1 ≤ H.degree v).card := by
    dsimp only [H]
    rw [highDegree_card_pruneSmallEdges]
    exact hlarge
  have hcontainH : ZhaoContainsAllTrees H :=
    zhaoSparseCutEmbeddingAtCap β hβ hβcap n hn H hlargeH hEC2
  exact containsAllTrees_mono_graph (pruneSmallEdges_le G _) hcontainH

/-! ## Degree form on the Ramsey host -/

/-- Direct degree-form existence on the host of order `2n-2`. -/
theorem exists_ramseyHostDegreeFormWitness
    {ε d : ℚ} (hε : 0 < ε) (hd : 0 < d) (m₀ n : ℕ)
    (hn : degreeFormThreshold ε m₀ ≤ 2 * n - 2)
    (G : SimpleGraph (Fin (2 * n - 2))) [DecidableRel G.Adj] :
    Nonempty (DegreeFormWitness G ε d m₀ (degreeFormBound ε m₀)) :=
  exists_degreeFormWitness hε hd m₀ (2 * n - 2) hn G

/-- Claim 6.1 exposed with the canonical padded reduced graph. -/
theorem degreeForm_ec1_or_claim67
    {n m₀ M : ℕ} {ε d α : ℚ}
    (G : SimpleGraph (Fin (2 * n - 2))) [DecidableRel G.Adj]
    (W : DegreeFormWitness G ε d m₀ M)
    (hn : 2 ≤ n)
    (hlarge : n - 1 ≤
      (Finset.univ.filter fun v => n - 1 ≤ G.degree v).card)
    (c : ℕ)
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
    let R : SimpleGraph ι :=
      regularityReducedGraph G (fun i : ι => i.1) ε d
    let S := Finset.univ.filter fun v => n - 1 ≤ G.degree v
    let L := clustersMeeting P S
    ZhaoExtremalCaseOne α G ∨
      Nonempty (Claim67Certificate (padGraph R) (padFinset L)
        (2 * c + 1)) := by
  exact claim6_1_full G W hn hlarge c W.clusterSize_pos hEsmall
    hclaim67Scale hEC1numeric

/-- A usable numeric entry to Claim 6.1.  Its premises are only the explicit
integer capacity/error inequalities produced by the chosen hierarchy.  In
particular, no extremal or embedding conclusion is assumed. -/
theorem degreeForm_ec1_or_claim67_of_error_capacities
    {n m₀ M : ℕ} {ε d α : ℚ}
    (G : SimpleGraph (Fin (2 * n - 2))) [DecidableRel G.Adj]
    (W : DegreeFormWitness G ε d m₀ M)
    (hn : 2 ≤ n)
    (hlarge : n - 1 ≤
      (Finset.univ.filter fun v => n - 1 ≤ G.degree v).card)
    (c : ℕ)
    (hc : c ≤ paddedHalf {Q // Q ∈ W.partition.parts})
    (hcapacity :
      W.clusterSize + 2 * W.loss + W.exceptional.card ≤
        2 * c * W.clusterSize)
    (hthree : 3 * (W.exceptional.card + W.loss) ≤ n - 1)
    (herror :
      (((3 * (n - 1) * (W.exceptional.card + W.loss) : ℕ) : ℕ) : ℚ) ≤
        α * ((n - 1 : ℕ) : ℚ) * ((n - 1 : ℕ) : ℚ)) :
    let ι := {Q // Q ∈ W.partition.parts}
    let P : ClusterAssignment (Fin (2 * n - 2)) ι :=
      partitionAssignment W.exceptional W.partition
    let R : SimpleGraph ι :=
      regularityReducedGraph G (fun i : ι => i.1) ε d
    let S := Finset.univ.filter fun v => n - 1 ≤ G.degree v
    let L := clustersMeeting P S
    ZhaoExtremalCaseOne α G ∨
      Nonempty (Claim67Certificate (padGraph R) (padFinset L)
        (2 * c + 1)) := by
  have hhost := exceptional_add_clusters_eq_host W
  have hhost' : W.exceptional.card +
      Fintype.card {Q // Q ∈ W.partition.parts} * W.clusterSize =
        2 * (n - 1) := by
    have hhost'' : W.exceptional.card +
        Fintype.card {Q // Q ∈ W.partition.parts} * W.clusterSize =
          2 * n - 2 := by
      simpa using hhost
    omega
  have hsmall : W.exceptional.card + W.loss ≤ n - 1 := by omega
  have hEsmall : W.exceptional.card < n - 1 := by omega
  have hclaim67Scale :
      (paddedHalf {Q // Q ∈ W.partition.parts} - c) * W.clusterSize ≤
        (n - 1 - W.loss) - W.exceptional.card :=
    claim67_scale_of_capacity {Q // Q ∈ W.partition.parts}
      (n - 1) W.exceptional.card W.loss W.clusterSize c
      hhost' hsmall hc hcapacity
  have hEC1numeric :
      (1 - α) * ((n - 1 : ℕ) : ℚ) * ((n - 1 : ℕ) : ℚ) ≤
        ((((n - 1 - W.exceptional.card) * (n - 1 - W.loss)) -
          2 * (n - 1) * (W.exceptional.card + W.loss) : ℕ) : ℚ) :=
    ec1_numeric_of_total_error α (n - 1) W.exceptional.card W.loss
      hthree herror
  exact degreeForm_ec1_or_claim67 G W hn hlarge c hEsmall
    hclaim67Scale hEC1numeric

/-! ## Source-faithful small--small preprocessing -/

/-- Claim 6.1 after the literal vertex pruning used by Zhao.  The dense
alternative is lifted back to the original host, while the Claim-6.7
certificate remains tied to the actual reduced graph of the pruned host.
The companion theorem
`every_pruned_degreeForm_claim67_edge_meets_large` supplies its matching-edge
orientation premise. -/
theorem pruned_degreeForm_ec1_or_claim67_of_error_capacities
    {n m₀ M : ℕ} {ε d α : ℚ}
    (G : SimpleGraph (Fin (2 * n - 2))) [DecidableRel G.Adj]
    (W : DegreeFormWitness
      (pruneSmallEdges G {v | n - 1 ≤ G.degree v}) ε d m₀ M)
    (hn : 2 ≤ n)
    (hlarge : n - 1 ≤
      (Finset.univ.filter fun v => n - 1 ≤ G.degree v).card)
    (c : ℕ)
    (hc : c ≤ paddedHalf {Q // Q ∈ W.partition.parts})
    (hcapacity :
      W.clusterSize + 2 * W.loss + W.exceptional.card ≤
        2 * c * W.clusterSize)
    (hthree : 3 * (W.exceptional.card + W.loss) ≤ n - 1)
    (herror :
      (((3 * (n - 1) * (W.exceptional.card + W.loss) : ℕ) : ℕ) : ℚ) ≤
        α * ((n - 1 : ℕ) : ℚ) * ((n - 1 : ℕ) : ℚ)) :
    let ι := {Q // Q ∈ W.partition.parts}
    let P : ClusterAssignment (Fin (2 * n - 2)) ι :=
      partitionAssignment W.exceptional W.partition
    let H := pruneSmallEdges G {v | n - 1 ≤ G.degree v}
    let R : SimpleGraph ι :=
      regularityReducedGraph H (fun i : ι => i.1) ε d
    let S := Finset.univ.filter fun v => n - 1 ≤ G.degree v
    let L := clustersMeeting P S
    ZhaoExtremalCaseOne α G ∨
      Nonempty (Claim67Certificate (padGraph R) (padFinset L)
        (2 * c + 1)) := by
  classical
  let H := pruneSmallEdges G {v | n - 1 ≤ G.degree v}
  have hlargeH : n - 1 ≤
      (Finset.univ.filter fun v => n - 1 ≤ H.degree v).card := by
    dsimp only [H]
    rw [highDegree_card_pruneSmallEdges]
    exact hlarge
  have hresult := degreeForm_ec1_or_claim67_of_error_capacities
    H W hn hlargeH c hc hcapacity hthree herror
  rcases hresult with hEC1 | hC67
  · exact Or.inl (extremalCaseOne_mono_graph (pruneSmallEdges_le G _) hEC1)
  · right
    have hS := highDegree_vertices_pruneSmallEdges G (n - 1)
    simpa only [H, hS] using hC67

/-- The padded graph returned by Claim 6.1 is definitionally tied to the
actual host: it is the regularity reduced graph of the empty-extended cluster
family. -/
theorem padded_reducedGraph_eq_actual
    {V ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (C : ι → Finset V) (ε d : ℚ) (hd : 0 < d) :
    padGraph (regularityReducedGraph G C ε d) =
      regularityReducedGraph G (padCluster C) ε d :=
  padGraph_regularityReducedGraph G C ε d hd

#print axioms exists_ramseyBalancedCut
#print axioms extremalCaseOne_or_two_of_half_le
#print axioms containsAllTrees_of_pruned_extremalCaseTwo
#print axioms exists_ramseyHostDegreeFormWitness
#print axioms degreeForm_ec1_or_claim67_of_error_capacities
#print axioms pruned_degreeForm_ec1_or_claim67_of_error_capacities
#print axioms padded_reducedGraph_eq_actual

end Erdos547b.ZhaoStabilityPropertyFull
