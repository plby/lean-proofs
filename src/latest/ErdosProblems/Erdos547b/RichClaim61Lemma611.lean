/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Section6EventualParameters
import ErdosProblems.Erdos547b.Lemma611CapacitySplit
import ErdosProblems.Erdos547b.Lemma611RootAccess

/-!
# The quantitative Claim 6.1 entry specialized to Lemma 6.11

There is a small but important source-level cleanup between Claim 6.7 and
Lemma 6.15.  The adjacent distinguished clusters `A,B` need not be outside
the support of the Claim-6.7 matching.  Lemma 6.15, on the other hand, is
applied to matching edges whose endpoints avoid both distinguished clusters.
Because the ambient subgraph is a matching, deleting the edges incident with
`{A,B}` removes at most two edges and hence at most `4*N` matching capacity.

This file implements that cleanup and then gives one concrete specialization
of the literal Lemma-6.11 constructor to `RichClaim61Certificate`.  No copy,
embedding continuation, or extremal conclusion is an input.  The only
containment hypothesis is the genuine omitted-tree premise used to
contrapose the copy-valued Lemma 6.15.
-/

open scoped BigOperators SimpleGraph

noncomputable section

namespace Erdos547b.ZhaoRichClaim61Lemma611

open Finset SimpleGraph
open Erdos547b.ZhaoStability
open Erdos547b.ZhaoLemma615
open Erdos547b.ZhaoLemma611Full
open Erdos547b.ZhaoClaim616
open Erdos547b.ZhaoClaim61RichFull
open Erdos547b.ZhaoEvenReducedPadding
open Erdos547b.ZhaoSection6EventualParameters

universe u v w

variable {K : Type u} [Fintype K] [DecidableEq K]
variable {R : SimpleGraph K} [DecidableRel R.Adj]

/-- The at-most-two matching edges incident with one of the distinguished
clusters. -/
def distinguishedIncidentEdges
    (M : R.Subgraph) (L : Finset K) (A B : K) :
    Finset (MatchingEdge M) :=
  incidentCoverEdges M L {A, B}

/-- The matching family to which Lemma 6.15 is literally applicable. -/
def edgesAwayFromDistinguished
    (M : R.Subgraph) (L : Finset K) (A B : K) :
    Finset (MatchingEdge M) :=
  allMatchingEdges M \ distinguishedIncidentEdges M L A B

theorem distinguishedIncidentEdges_card_le_two
    (M : R.Subgraph) (hM : M.IsMatching) (L : Finset K) (A B : K) :
    (distinguishedIncidentEdges M L A B).card ≤ 2 := by
  have h := incidentCoverEdges_card_le M hM L ({A, B} : Finset K)
  have hcard : ({A, B} : Finset K).card ≤ 2 := by
    have hinsert := Finset.card_insert_le A ({B} : Finset K)
    simpa only [Finset.card_singleton] using hinsert
  exact h.trans hcard

theorem edgesAwayFromDistinguished_subset
    (M : R.Subgraph) (L : Finset K) (A B : K) :
    edgesAwayFromDistinguished M L A B ⊆ allMatchingEdges M :=
  Finset.sdiff_subset

/-- Every endpoint of an edge in the cleaned family avoids both `A` and
`B`; this is the exact endpoint premise of the source-shaped Lemma 6.15. -/
theorem endpoint_ne_distinguished_of_mem_away
    (M : R.Subgraph) (L : Finset K) (A B : K)
    {e : MatchingEdge M}
    (he : e ∈ edgesAwayFromDistinguished M L A B) (c : Fin 2) :
    orientedEndpoint M L e c ≠ A ∧ orientedEndpoint M L e c ≠ B := by
  have heAll : e ∈ allMatchingEdges M := (Finset.mem_sdiff.mp he).1
  have heNot : e ∉ distinguishedIncidentEdges M L A B :=
    (Finset.mem_sdiff.mp he).2
  constructor
  · intro hA
    apply heNot
    change e ∈ incidentCoverEdges M L ({A, B} : Finset K)
    apply Finset.mem_filter.mpr
    refine ⟨heAll, ?_⟩
    rcases Erdos547b.RegularPair.OrderedRootedForest.fin_two_eq_zero_or_one c with
      rfl | rfl
    · exact Or.inl (Finset.mem_insert.mpr (Or.inl hA))
    · exact Or.inr (Finset.mem_insert.mpr (Or.inl hA))
  · intro hB
    apply heNot
    change e ∈ incidentCoverEdges M L ({A, B} : Finset K)
    apply Finset.mem_filter.mpr
    refine ⟨heAll, ?_⟩
    rcases Erdos547b.RegularPair.OrderedRootedForest.fin_two_eq_zero_or_one c with
      rfl | rfl
    · exact Or.inl
        (Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr hB)))
    · exact Or.inr
        (Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr hB)))

/-- Removing the distinguished incident edges costs at most `4*N` in either
source degree.  The statement is deliberately about the literal
`sourceDegree`, so it composes definitionally with Lemma 6.11. -/
theorem sourceDegree_away_add_four_mul_le
    (M : R.Subgraph) (hM : M.IsMatching) (L : Finset K)
    (density : K → K → ℝ) (N : ℝ) (C A B : K)
    (hN : 0 ≤ N)
    (hnonneg : ∀ e : MatchingEdge M,
      0 ≤ N * (density C (orientedEndpoint M L e 0) +
        density C (orientedEndpoint M L e 1)))
    (hcap : ∀ e : MatchingEdge M,
      N * (density C (orientedEndpoint M L e 0) +
        density C (orientedEndpoint M L e 1)) ≤ 2 * N) :
    sourceDegree M L density N C (allMatchingEdges M) ≤
      sourceDegree M L density N C
          (edgesAwayFromDistinguished M L A B) + 4 * N := by
  let I := distinguishedIncidentEdges M L A B
  let Away := edgesAwayFromDistinguished M L A B
  let contribution := fun e : MatchingEdge M ↦
    N * (density C (orientedEndpoint M L e 0) +
      density C (orientedEndpoint M L e 1))
  have hI : I ⊆ allMatchingEdges M := by
    intro e he
    exact (Finset.mem_filter.mp he).1
  have hsplit :
      (∑ e ∈ allMatchingEdges M, contribution e) =
        (∑ e ∈ Away, contribution e) + ∑ e ∈ I, contribution e := by
    have hs := Finset.sum_sdiff hI (f := contribution)
    simpa [Away, edgesAwayFromDistinguished] using hs.symm
  have hIcard : I.card ≤ 2 := by
    exact distinguishedIncidentEdges_card_le_two M hM L A B
  have hIsum : (∑ e ∈ I, contribution e) ≤ 4 * N := by
    calc
      (∑ e ∈ I, contribution e) ≤ ∑ _e ∈ I, 2 * N := by
        exact Finset.sum_le_sum fun e _he ↦ hcap e
      _ = (I.card : ℝ) * (2 * N) := by
        rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 2 * (2 * N) := by
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hIcard)
          (mul_nonneg (by norm_num) hN)
      _ = 4 * N := by ring
  rw [sourceDegree_eq_sum, sourceDegree_eq_sum, hsplit]
  linarith

/-- Convenient subtraction form of `sourceDegree_away_add_four_mul_le`. -/
theorem sourceDegree_away_lower
    (M : R.Subgraph) (hM : M.IsMatching) (L : Finset K)
    (density : K → K → ℝ) (N lower : ℝ) (C A B : K)
    (hN : 0 ≤ N)
    (hnonneg : ∀ e : MatchingEdge M,
      0 ≤ N * (density C (orientedEndpoint M L e 0) +
        density C (orientedEndpoint M L e 1)))
    (hcap : ∀ e : MatchingEdge M,
      N * (density C (orientedEndpoint M L e 0) +
        density C (orientedEndpoint M L e 1)) ≤ 2 * N)
    (htotal : lower + 4 * N ≤
      sourceDegree M L density N C (allMatchingEdges M)) :
    lower ≤ sourceDegree M L density N C
      (edgesAwayFromDistinguished M L A B) := by
  have hupper := sourceDegree_away_add_four_mul_le
    M hM L density N C A B hN hnonneg hcap
  linarith

/-! ## Actual high-root source degrees -/

/-- The endpoints of a finite matching, with their two occurrences, are
equivalent to its support. -/
noncomputable def matchingEndpointEquiv
    (M : R.Subgraph) (hM : M.IsMatching) (L : Finset K) :
    MatchingEdge M × Fin 2 ≃ {x : K // x ∈ matchingSupport M} := by
  let f : MatchingEdge M × Fin 2 → {x : K // x ∈ matchingSupport M} :=
    fun ⟨e, c⟩ ↦ ⟨orientedEndpoint M L e c, by
      apply (mem_matchingSupport M _).mpr
      rcases Erdos547b.RegularPair.OrderedRootedForest.fin_two_eq_zero_or_one c with
        rfl | rfl
      · exact (orientedEndpoint_adj M L e).fst_mem
      · exact (orientedEndpoint_adj M L e).snd_mem⟩
  apply Equiv.ofBijective f
  constructor
  · intro ec fd h
    exact orientedEndpoint_injective M hM L (congrArg Subtype.val h)
  · intro x
    have hxM : x.1 ∈ M.verts := (mem_matchingSupport M x.1).mp x.2
    obtain ⟨y, hxy, _⟩ := hM hxM
    let e : MatchingEdge M := ⟨s(x.1, y), hxy⟩
    have hxEnds : x.1 = orientedEndpoint M L e 0 ∨
        x.1 = orientedEndpoint M L e 1 := by
      have hxmem : x.1 ∈ (e.1 : Sym2 K) := Sym2.mem_mk_left x.1 y
      rw [← orientedEndpoint_pair_eq M L e] at hxmem
      simpa using hxmem
    rcases hxEnds with hx0 | hx1
    · refine ⟨(e, 0), Subtype.ext ?_⟩
      exact hx0.symm
    · refine ⟨(e, 1), Subtype.ext ?_⟩
      exact hx1.symm

theorem sum_matchingEndpoints_eq_sum_support
    (M : R.Subgraph) (hM : M.IsMatching) (L : Finset K)
    (f : K → ℝ) :
    (∑ e ∈ allMatchingEdges M,
      (f (orientedEndpoint M L e 0) + f (orientedEndpoint M L e 1))) =
      ∑ x ∈ matchingSupport M, f x := by
  classical
  calc
    (∑ e ∈ allMatchingEdges M,
        (f (orientedEndpoint M L e 0) + f (orientedEndpoint M L e 1))) =
        ∑ ec : MatchingEdge M × Fin 2,
          f (orientedEndpoint M L ec.1 ec.2) := by
      have hall : allMatchingEdges M = (Finset.univ : Finset (MatchingEdge M)) := by
        ext e
        simp only [mem_allMatchingEdges, Finset.mem_univ]
      rw [hall]
      rw [Fintype.sum_prod_type]
      simp only [Fin.sum_univ_two]
    _ = ∑ x : {x : K // x ∈ matchingSupport M}, f x :=
      (matchingEndpointEquiv M hM L).sum_comp fun x ↦ f x
    _ = ∑ x ∈ matchingSupport M, f x := by
      exact Finset.sum_attach (matchingSupport M) f

/-- The literal source-density row associated with one selected host root. -/
def rootedSourceDensity
    {V : Type*} [Fintype V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (cluster : K → Finset V) (N : ℝ) (z : V) (j : K) : ℝ :=
  (Erdos547EC2.degreeInto H z (cluster j) : ℝ) / N

/-- A single table carrying the independently selected `A`- and `B`-root
rows.  Rows not used in Section 6 are set to zero. -/
def twoRootSourceDensity
    {V : Type*} [Fintype V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (cluster : K → Finset V) (N : ℝ)
    (A B : K) (zA zB : V) (C j : K) : ℝ :=
  if C = A then rootedSourceDensity H cluster N zA j
  else if C = B then rootedSourceDensity H cluster N zB j
  else 0

theorem twoRootSourceDensity_row_A
    {V : Type*} [Fintype V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (cluster : K → Finset V) (N : ℝ)
    (A B : K) (zA zB : V) (j : K) :
    twoRootSourceDensity H cluster N A B zA zB A j =
      rootedSourceDensity H cluster N zA j := by
  simp [twoRootSourceDensity]

theorem twoRootSourceDensity_row_B
    {V : Type*} [Fintype V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (cluster : K → Finset V) (N : ℝ)
    (A B : K) (zA zB : V) (hAB : A ≠ B) (j : K) :
    twoRootSourceDensity H cluster N A B zA zB B j =
      rootedSourceDensity H cluster N zB j := by
  simp [twoRootSourceDensity, hAB, hAB.symm]

theorem sourceDegree_rooted_eq_sum_support_degreeInto
    {V : Type*} [Fintype V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (cluster : K → Finset V) (M : R.Subgraph) (hM : M.IsMatching)
    (L : Finset K) (N : ℝ) (hN : N ≠ 0) (C : K) (z : V) :
    sourceDegree M L
        (fun _ j ↦ rootedSourceDensity H cluster N z j) N C
        (allMatchingEdges M) =
      ∑ j ∈ matchingSupport M,
        (Erdos547EC2.degreeInto H z (cluster j) : ℝ) := by
  rw [sourceDegree_eq_sum]
  calc
    (∑ e ∈ allMatchingEdges M,
      N * (rootedSourceDensity H cluster N z (orientedEndpoint M L e 0) +
        rootedSourceDensity H cluster N z (orientedEndpoint M L e 1))) =
        ∑ e ∈ allMatchingEdges M,
          ((Erdos547EC2.degreeInto H z
              (cluster (orientedEndpoint M L e 0)) : ℝ) +
            (Erdos547EC2.degreeInto H z
              (cluster (orientedEndpoint M L e 1)) : ℝ)) := by
      apply Finset.sum_congr rfl
      intro e _
      simp only [rootedSourceDensity]
      field_simp [hN]
    _ = ∑ j ∈ matchingSupport M,
        (Erdos547EC2.degreeInto H z (cluster j) : ℝ) :=
      sum_matchingEndpoints_eq_sum_support M hM L
        (fun j ↦ (Erdos547EC2.degreeInto H z (cluster j) : ℝ))

/-- A cleaned host degree is accounted for by exceptional vertices and the
actual degrees into reduced-neighbor clusters. -/
theorem degree_le_exceptional_add_sum_degreeInto_reduced
    {V : Type*} [Fintype V] [DecidableEq V]
    (P : ClusterAssignment V K)
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (R : SimpleGraph K) [DecidableRel R.Adj]
    (hrespect : EdgesRespectReducedGraph P H R)
    (cluster : K → Finset V)
    (hcluster : ∀ i, cluster i = clusterVertices P i)
    {z : V} {A : K} (hz : P z = some A) :
    H.degree z ≤ (exceptionalVertices P).card +
      ∑ j ∈ R.neighborFinset A, Erdos547EC2.degreeInto H z (cluster j) := by
  classical
  let pieces := fun j : K ↦ H.neighborFinset z ∩ cluster j
  have hsubset : H.neighborFinset z ⊆
      exceptionalVertices P ∪ (R.neighborFinset A).biUnion pieces := by
    intro y hy
    have hyCover := neighborFinset_subset_exceptional_union_reduced
      P H R hrespect hz hy
    rcases Finset.mem_union.mp hyCover with hyE | hyR
    · exact Finset.mem_union_left _ hyE
    · obtain ⟨j, hj, hyj⟩ := Finset.mem_biUnion.mp hyR
      apply Finset.mem_union_right
      apply Finset.mem_biUnion.mpr
      refine ⟨j, hj, ?_⟩
      exact Finset.mem_inter.mpr ⟨hy, by simpa [hcluster j] using hyj⟩
  calc
    H.degree z = (H.neighborFinset z).card := rfl
    _ ≤ (exceptionalVertices P ∪
        (R.neighborFinset A).biUnion pieces).card :=
      Finset.card_le_card hsubset
    _ ≤ (exceptionalVertices P).card +
        ((R.neighborFinset A).biUnion pieces).card :=
      Finset.card_union_le _ _
    _ ≤ (exceptionalVertices P).card +
        ∑ j ∈ R.neighborFinset A, (pieces j).card := by
      exact Nat.add_le_add_left Finset.card_biUnion_le _
    _ = (exceptionalVertices P).card +
        ∑ j ∈ R.neighborFinset A,
          Erdos547EC2.degreeInto H z (cluster j) := by
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      apply congrArg Finset.card
      ext y
      simp only [pieces, Erdos547EC2.degreeInto, Finset.mem_inter,
        Finset.mem_filter, SimpleGraph.mem_neighborFinset]
      tauto

/-- Claim 6.7's missed-neighbor bound transfers a retained root degree
to matching-supported host degree, with only the exceptional class and
`miss*N` charged. -/
theorem matchingSupport_degree_lower_of_retainedRoot
    {V : Type*} [Fintype V] [DecidableEq V]
    (P : ClusterAssignment V K)
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (R : SimpleGraph K) [DecidableRel R.Adj]
    (hrespect : EdgesRespectReducedGraph P H R)
    (cluster : K → Finset V)
    (hcluster : ∀ i, cluster i = clusterVertices P i)
    (clusterSize threshold loss miss : ℕ)
    (hclusterCard : ∀ i, (cluster i).card ≤ clusterSize)
    {L : Finset K} (C67 : Claim67Certificate R L miss)
    {z : V} {A : K} (hzA : P z = some A)
    (hdegreeH : threshold - loss ≤ H.degree z) (hAO : A ∈ C67.O) :
    threshold - loss - (exceptionalVertices P).card - miss * clusterSize ≤
      ∑ j ∈ matchingSupport C67.M,
        Erdos547EC2.degreeInto H z (cluster j) := by
  classical
  have hdegreeReduced := degree_le_exceptional_add_sum_degreeInto_reduced
    P H R hrespect cluster hcluster hzA
  let Nbr := R.neighborFinset A
  let Covered := Nbr ∩ matchingSupport C67.M
  let Missed := Nbr \ matchingSupport C67.M
  have hsplit :
      (∑ j ∈ Nbr, Erdos547EC2.degreeInto H z (cluster j)) =
        (∑ j ∈ Covered, Erdos547EC2.degreeInto H z (cluster j)) +
          ∑ j ∈ Missed, Erdos547EC2.degreeInto H z (cluster j) := by
    simpa [Covered, Missed] using
      (Finset.sum_inter_add_sum_sdiff Nbr (matchingSupport C67.M)
        (fun j ↦ Erdos547EC2.degreeInto H z (cluster j))).symm
  have hmissCard : Missed.card ≤ miss := by
    simpa [Nbr, Missed] using C67.neighbors_missed A hAO
  have hmissSum :
      (∑ j ∈ Missed, Erdos547EC2.degreeInto H z (cluster j)) ≤
        miss * clusterSize := by
    calc
      (∑ j ∈ Missed, Erdos547EC2.degreeInto H z (cluster j)) ≤
          ∑ _j ∈ Missed, clusterSize := by
        apply Finset.sum_le_sum
        intro j _
        exact (Finset.card_filter_le (cluster j) _).trans (hclusterCard j)
      _ = Missed.card * clusterSize := by simp
      _ ≤ miss * clusterSize := Nat.mul_le_mul_right clusterSize hmissCard
  have hcovered :
      (∑ j ∈ Covered, Erdos547EC2.degreeInto H z (cluster j)) ≤
        ∑ j ∈ matchingSupport C67.M,
          Erdos547EC2.degreeInto H z (cluster j) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · exact Finset.inter_subset_right
    · intro _ _ _
      omega
  have htotal : threshold - loss ≤
      (exceptionalVertices P).card +
        (∑ j ∈ Covered, Erdos547EC2.degreeInto H z (cluster j)) +
          ∑ j ∈ Missed, Erdos547EC2.degreeInto H z (cluster j) := by
    calc
      threshold - loss ≤ (exceptionalVertices P).card +
          ∑ j ∈ Nbr, Erdos547EC2.degreeInto H z (cluster j) :=
        hdegreeH.trans hdegreeReduced
      _ = (exceptionalVertices P).card +
          (∑ j ∈ Covered, Erdos547EC2.degreeInto H z (cluster j)) +
            ∑ j ∈ Missed, Erdos547EC2.degreeInto H z (cluster j) := by
        rw [hsplit]
        omega
  omega

/-- Claim 6.7's missed-neighbor bound transfers an actual high root degree
to matching-supported host degree, with only the exceptional class and
`miss*N` charged. -/
theorem matchingSupport_degree_lower_of_highRoot
    {V : Type*} [Fintype V] [DecidableEq V]
    (P : ClusterAssignment V K)
    (G H : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    (R : SimpleGraph K) [DecidableRel R.Adj]
    (hrespect : EdgesRespectReducedGraph P H R)
    (cluster : K → Finset V)
    (hcluster : ∀ i, cluster i = clusterVertices P i)
    (clusterSize threshold loss miss : ℕ)
    (hclusterCard : ∀ i, (cluster i).card ≤ clusterSize)
    (hloss : DegreeLossAtMost G H loss)
    {L : Finset K} (C67 : Claim67Certificate R L miss)
    {z : V} {A : K} (hzA : P z = some A)
    (hzHigh : threshold ≤ G.degree z) (hAO : A ∈ C67.O) :
    threshold - loss - (exceptionalVertices P).card - miss * clusterSize ≤
      ∑ j ∈ matchingSupport C67.M,
        Erdos547EC2.degreeInto H z (cluster j) := by
  exact matchingSupport_degree_lower_of_retainedRoot P H R hrespect cluster
    hcluster clusterSize threshold loss miss hclusterCard C67 hzA
    (cleaned_degree_ge_threshold_sub_loss G H loss threshold hloss hzHigh) hAO

/-- The root-row construction only needs retained degrees on the two
reservoirs. This version applies after whole-pair pruning, which can have
large degree loss at vertices outside the large clusters. -/
theorem exists_twoRootSourceDensity_of_richClaim61_localDegree
    {V I : Type*} [Fintype V] [Fintype I]
    [DecidableEq V] [DecidableEq I]
    (Pcluster : ClusterAssignment V I)
    (Gdegree H : SimpleGraph V)
    [DecidableRel Gdegree.Adj] [DecidableRel H.Adj]
    (R0 : SimpleGraph I) [DecidableRel R0.Adj]
    (cluster : I → Finset V)
    (hcluster : ∀ i, cluster i = clusterVertices Pcluster i)
    (threshold quota miss clusterSize loss : ℕ)
    (hquota : 0 < quota) (hclusterSize : 0 < clusterSize)
    (hclusterCard : ∀ i, (cluster i).card ≤ clusterSize)
    (hrespect : EdgesRespectReducedGraph (padAssignment Pcluster) H
      (padGraph R0))
    (badA badB : Finset V)
    (hbadA : badA.card < quota) (hbadB : badB.card < quota)
    (Q : RichClaim61Certificate Pcluster Gdegree threshold quota R0
      (Erdos547b.ZhaoQuantitativeLargeClusters.largeClustersAtLeast
        Pcluster Gdegree threshold quota) miss)
    (hretainedA : ∀ z ∈ Q.A₀, threshold - loss ≤ H.degree z)
    (hretainedB : ∀ z ∈ Q.B₀, threshold - loss ≤ H.degree z) :
    ∃ zA ∈ Q.A₀, zA ∉ badA ∧ ∃ zB ∈ Q.B₀, zB ∉ badB ∧
      let Lp := padFinset
        (Erdos547b.ZhaoQuantitativeLargeClusters.largeClustersAtLeast
          Pcluster Gdegree threshold quota)
      let A : EvenPadding I := Sum.inl Q.A
      let B : EvenPadding I := Sum.inl Q.B
      let density := twoRootSourceDensity H (padCluster cluster)
        (clusterSize : ℝ) A B zA zB
      (((threshold - loss - (exceptionalVertices (padAssignment Pcluster)).card -
          miss * clusterSize : ℕ) : ℝ) ≤
        sourceDegree Q.claim67.M Lp density (clusterSize : ℝ) A
          (allMatchingEdges Q.claim67.M)) ∧
      (((threshold - loss - (exceptionalVertices (padAssignment Pcluster)).card -
          miss * clusterSize : ℕ) : ℝ) ≤
        sourceDegree Q.claim67.M Lp density (clusterSize : ℝ) B
          (allMatchingEdges Q.claim67.M)) ∧
      (∀ x, 0 ≤ density A x) ∧
      (∀ e : MatchingEdge Q.claim67.M,
        0 ≤ (clusterSize : ℝ) *
          (density A (orientedEndpoint Q.claim67.M Lp e 0) +
            density A (orientedEndpoint Q.claim67.M Lp e 1))) ∧
      (∀ e : MatchingEdge Q.claim67.M,
        0 ≤ (clusterSize : ℝ) *
          (density B (orientedEndpoint Q.claim67.M Lp e 0) +
            density B (orientedEndpoint Q.claim67.M Lp e 1))) ∧
      (∀ e : MatchingEdge Q.claim67.M,
        (clusterSize : ℝ) *
          (density A (orientedEndpoint Q.claim67.M Lp e 0) +
            density A (orientedEndpoint Q.claim67.M Lp e 1)) ≤
              2 * clusterSize) ∧
      (∀ e : MatchingEdge Q.claim67.M,
        (clusterSize : ℝ) *
          (density B (orientedEndpoint Q.claim67.M Lp e 0) +
            density B (orientedEndpoint Q.claim67.M Lp e 1)) ≤
              2 * clusterSize) ∧
      (∀ x, 0 < density A x → (padGraph R0).Adj A x) ∧
      (∀ x, 0 < density B x → (padGraph R0).Adj B x) := by
  classical
  have hA0pos : 0 < (Q.A₀ \ badA).card := by
    by_contra hzero
    have hsub : Q.A₀ ⊆ badA := by
      intro z hz
      by_contra hzbad
      have hzDiff : z ∈ Q.A₀ \ badA := Finset.mem_sdiff.mpr ⟨hz, hzbad⟩
      have : 0 < (Q.A₀ \ badA).card :=
        Finset.card_pos.mpr ⟨z, hzDiff⟩
      exact hzero this
    have hcard := Finset.card_le_card hsub
    rw [Q.A₀_card] at hcard
    omega
  have hB0pos : 0 < (Q.B₀ \ badB).card := by
    by_contra hzero
    have hsub : Q.B₀ ⊆ badB := by
      intro z hz
      by_contra hzbad
      have hzDiff : z ∈ Q.B₀ \ badB := Finset.mem_sdiff.mpr ⟨hz, hzbad⟩
      have : 0 < (Q.B₀ \ badB).card :=
        Finset.card_pos.mpr ⟨z, hzDiff⟩
      exact hzero this
    have hcard := Finset.card_le_card hsub
    rw [Q.B₀_card] at hcard
    omega
  obtain ⟨zA, hzAclean⟩ := Finset.card_pos.mp hA0pos
  obtain ⟨zB, hzBclean⟩ := Finset.card_pos.mp hB0pos
  have hzA := (Finset.mem_sdiff.mp hzAclean).1
  have hzB := (Finset.mem_sdiff.mp hzBclean).1
  refine ⟨zA, hzA, (Finset.mem_sdiff.mp hzAclean).2,
    zB, hzB, (Finset.mem_sdiff.mp hzBclean).2, ?_⟩
  dsimp only
  let Lp := padFinset
    (Erdos547b.ZhaoQuantitativeLargeClusters.largeClustersAtLeast
      Pcluster Gdegree threshold quota)
  let A : EvenPadding I := Sum.inl Q.A
  let B : EvenPadding I := Sum.inl Q.B
  let density := twoRootSourceDensity H (padCluster cluster)
    (clusterSize : ℝ) A B zA zB
  have hclusterPad : ∀ i,
      padCluster cluster i = clusterVertices (padAssignment Pcluster) i := by
    intro i
    rw [clusterVertices_padAssignment]
    cases i <;> simp [padCluster, hcluster]
  have hclusterPadCard : ∀ i, (padCluster cluster i).card ≤ clusterSize := by
    intro i
    cases i with
    | inl i => simpa [padCluster] using hclusterCard i
    | inr i => simp [padCluster]
  have hzAassign : padAssignment Pcluster zA = some A := by
    have hz := Q.A₀_subset hzA
    have : Pcluster zA = some Q.A :=
      (mem_clusterVertices Pcluster Q.A zA).mp hz
    simpa [A, padAssignment, this]
  have hzBassign : padAssignment Pcluster zB = some B := by
    have hz := Q.B₀_subset hzB
    have : Pcluster zB = some Q.B :=
      (mem_clusterVertices Pcluster Q.B zB).mp hz
    simpa [B, padAssignment, this]
  have hSupportA := matchingSupport_degree_lower_of_retainedRoot
    (padAssignment Pcluster) H (padGraph R0) hrespect
      (padCluster cluster) hclusterPad clusterSize threshold loss miss
      hclusterPadCard Q.claim67 hzAassign (hretainedA zA hzA)
      Q.A_in_claim67O
  have hSupportB := matchingSupport_degree_lower_of_retainedRoot
    (padAssignment Pcluster) H (padGraph R0) hrespect
      (padCluster cluster) hclusterPad clusterSize threshold loss miss
      hclusterPadCard Q.claim67 hzBassign (hretainedB zB hzB)
      Q.B_in_claim67O
  have hABne : A ≠ B := by
    intro h
    have : Q.A = Q.B := Sum.inl_injective h
    exact Q.adj.ne this
  have hrowA (j : EvenPadding I) : density A j =
      rootedSourceDensity H (padCluster cluster) (clusterSize : ℝ) zA j := by
    exact twoRootSourceDensity_row_A H (padCluster cluster)
      (clusterSize : ℝ) A B zA zB j
  have hrowB (j : EvenPadding I) : density B j =
      rootedSourceDensity H (padCluster cluster) (clusterSize : ℝ) zB j := by
    exact twoRootSourceDensity_row_B H (padCluster cluster)
      (clusterSize : ℝ) A B zA zB hABne j
  have hSourceA : sourceDegree Q.claim67.M Lp density (clusterSize : ℝ) A
      (allMatchingEdges Q.claim67.M) =
      ∑ j ∈ matchingSupport Q.claim67.M,
        (Erdos547EC2.degreeInto H zA (padCluster cluster j) : ℝ) := by
    rw [sourceDegree_eq_sum]
    simp_rw [hrowA]
    have hrooted := sourceDegree_rooted_eq_sum_support_degreeInto H
      (padCluster cluster) Q.claim67.M Q.claim67.isMatching Lp
        (clusterSize : ℝ) (by exact_mod_cast hclusterSize.ne') A zA
    rw [sourceDegree_eq_sum] at hrooted
    exact hrooted
  have hSourceB : sourceDegree Q.claim67.M Lp density (clusterSize : ℝ) B
      (allMatchingEdges Q.claim67.M) =
      ∑ j ∈ matchingSupport Q.claim67.M,
        (Erdos547EC2.degreeInto H zB (padCluster cluster j) : ℝ) := by
    rw [sourceDegree_eq_sum]
    simp_rw [hrowB]
    have hrooted := sourceDegree_rooted_eq_sum_support_degreeInto H
      (padCluster cluster) Q.claim67.M Q.claim67.isMatching Lp
        (clusterSize : ℝ) (by exact_mod_cast hclusterSize.ne') B zB
    rw [sourceDegree_eq_sum] at hrooted
    exact hrooted
  have hdegreeA :
      (((threshold - loss - (exceptionalVertices (padAssignment Pcluster)).card -
          miss * clusterSize : ℕ) : ℝ) ≤
        sourceDegree Q.claim67.M Lp density (clusterSize : ℝ) A
          (allMatchingEdges Q.claim67.M)) := by
    rw [hSourceA]
    exact_mod_cast hSupportA
  have hdegreeB :
      (((threshold - loss - (exceptionalVertices (padAssignment Pcluster)).card -
          miss * clusterSize : ℕ) : ℝ) ≤
        sourceDegree Q.claim67.M Lp density (clusterSize : ℝ) B
          (allMatchingEdges Q.claim67.M)) := by
    rw [hSourceB]
    exact_mod_cast hSupportB
  have hrowNonneg (z : V) (j : EvenPadding I) :
      0 ≤ rootedSourceDensity H (padCluster cluster) (clusterSize : ℝ) z j := by
    exact div_nonneg (by positivity) (by positivity)
  have hrowLeOne (z : V) (j : EvenPadding I) :
      rootedSourceDensity H (padCluster cluster) (clusterSize : ℝ) z j ≤ 1 := by
    rw [rootedSourceDensity]
    apply (div_le_one (by positivity)).mpr
    exact_mod_cast (Finset.card_filter_le (padCluster cluster j) _).trans
      (hclusterPadCard j)
  have hAnonneg : ∀ e : MatchingEdge Q.claim67.M,
      0 ≤ (clusterSize : ℝ) *
        (density A (orientedEndpoint Q.claim67.M Lp e 0) +
          density A (orientedEndpoint Q.claim67.M Lp e 1)) := by
    intro e
    apply mul_nonneg (by positivity)
    simp only [density, twoRootSourceDensity_row_A]
    exact add_nonneg (hrowNonneg zA _) (hrowNonneg zA _)
  have hAdensityNonneg : ∀ x, 0 ≤ density A x := by
    intro x
    simp only [density, twoRootSourceDensity_row_A]
    exact hrowNonneg zA x
  have hBnonneg : ∀ e : MatchingEdge Q.claim67.M,
      0 ≤ (clusterSize : ℝ) *
        (density B (orientedEndpoint Q.claim67.M Lp e 0) +
          density B (orientedEndpoint Q.claim67.M Lp e 1)) := by
    intro e
    apply mul_nonneg (by positivity)
    rw [hrowB, hrowB]
    exact add_nonneg (hrowNonneg zB _) (hrowNonneg zB _)
  have hAcap : ∀ e : MatchingEdge Q.claim67.M,
      (clusterSize : ℝ) *
        (density A (orientedEndpoint Q.claim67.M Lp e 0) +
          density A (orientedEndpoint Q.claim67.M Lp e 1)) ≤
            2 * clusterSize := by
    intro e
    have hsum : density A (orientedEndpoint Q.claim67.M Lp e 0) +
        density A (orientedEndpoint Q.claim67.M Lp e 1) ≤ 2 := by
      simp only [density, twoRootSourceDensity_row_A]
      linarith [hrowLeOne zA (orientedEndpoint Q.claim67.M Lp e 0),
        hrowLeOne zA (orientedEndpoint Q.claim67.M Lp e 1)]
    nlinarith [show (0 : ℝ) ≤ clusterSize by positivity]
  have hBcap : ∀ e : MatchingEdge Q.claim67.M,
      (clusterSize : ℝ) *
        (density B (orientedEndpoint Q.claim67.M Lp e 0) +
          density B (orientedEndpoint Q.claim67.M Lp e 1)) ≤
            2 * clusterSize := by
    intro e
    have hsum : density B (orientedEndpoint Q.claim67.M Lp e 0) +
        density B (orientedEndpoint Q.claim67.M Lp e 1) ≤ 2 := by
      rw [hrowB, hrowB]
      linarith [hrowLeOne zB (orientedEndpoint Q.claim67.M Lp e 0),
        hrowLeOne zB (orientedEndpoint Q.claim67.M Lp e 1)]
    nlinarith [show (0 : ℝ) ≤ clusterSize by positivity]
  have hdensityAdj : ∀ x, 0 < density A x → (padGraph R0).Adj A x := by
    intro x hx
    have hx' : 0 < rootedSourceDensity H (padCluster cluster)
        (clusterSize : ℝ) zA x := by
      simpa [density, twoRootSourceDensity_row_A] using hx
    have hcountR : 0 <
        (Erdos547EC2.degreeInto H zA (padCluster cluster x) : ℝ) := by
      have hden : (0 : ℝ) < clusterSize := by exact_mod_cast hclusterSize
      rw [rootedSourceDensity] at hx'
      rcases (div_pos_iff.mp hx') with hpos | hneg
      · exact hpos.1
      · exact False.elim ((not_lt_of_ge hden.le) hneg.2)
    have hcount : 0 < Erdos547EC2.degreeInto H zA (padCluster cluster x) := by
      exact_mod_cast hcountR
    obtain ⟨y, hy⟩ := Finset.card_pos.mp hcount
    have hy' := Finset.mem_filter.mp hy
    exact hrespect hzAassign
      ((mem_clusterVertices (padAssignment Pcluster) x y).mp
        (by rw [← hclusterPad x]; exact hy'.1)) hy'.2
  have hdensityAdjB : ∀ x, 0 < density B x → (padGraph R0).Adj B x := by
    intro x hx
    have hx' : 0 < rootedSourceDensity H (padCluster cluster)
        (clusterSize : ℝ) zB x := by
      rw [← twoRootSourceDensity_row_B H (padCluster cluster)
        (clusterSize : ℝ) A B zA zB hABne x]
      exact hx
    have hcountR : 0 <
        (Erdos547EC2.degreeInto H zB (padCluster cluster x) : ℝ) := by
      have hden : (0 : ℝ) < clusterSize := by exact_mod_cast hclusterSize
      rw [rootedSourceDensity] at hx'
      rcases (div_pos_iff.mp hx') with hpos | hneg
      · exact hpos.1
      · exact False.elim ((not_lt_of_ge hden.le) hneg.2)
    have hcount : 0 < Erdos547EC2.degreeInto H zB (padCluster cluster x) := by
      exact_mod_cast hcountR
    obtain ⟨y, hy⟩ := Finset.card_pos.mp hcount
    have hy' := Finset.mem_filter.mp hy
    exact hrespect hzBassign
      ((mem_clusterVertices (padAssignment Pcluster) x y).mp
        (by rw [← hclusterPad x]; exact hy'.1)) hy'.2
  exact ⟨hdegreeA, hdegreeB, hAdensityNonneg, hAnonneg, hBnonneg,
    hAcap, hBcap, hdensityAdj, hdensityAdjB⟩

/-- The quantitative reservoirs in `RichClaim61Certificate`, together with
degree-form loss and Claim 6.7 coverage, construct the two literal
source-density rows used by Lemma 6.11.  In particular the degree lower
bounds are conclusions, not hypotheses. -/
theorem exists_twoRootSourceDensity_of_richClaim61
    {V I : Type*} [Fintype V] [Fintype I]
    [DecidableEq V] [DecidableEq I]
    (Pcluster : ClusterAssignment V I)
    (Gdegree H : SimpleGraph V)
    [DecidableRel Gdegree.Adj] [DecidableRel H.Adj]
    (R0 : SimpleGraph I) [DecidableRel R0.Adj]
    (cluster : I → Finset V)
    (hcluster : ∀ i, cluster i = clusterVertices Pcluster i)
    (threshold quota miss clusterSize loss : ℕ)
    (hquota : 0 < quota) (hclusterSize : 0 < clusterSize)
    (hclusterCard : ∀ i, (cluster i).card ≤ clusterSize)
    (hloss : DegreeLossAtMost Gdegree H loss)
    (hrespect : EdgesRespectReducedGraph (padAssignment Pcluster) H
      (padGraph R0))
    (badA badB : Finset V)
    (hbadA : badA.card < quota) (hbadB : badB.card < quota)
    (Q : RichClaim61Certificate Pcluster Gdegree threshold quota R0
      (Erdos547b.ZhaoQuantitativeLargeClusters.largeClustersAtLeast
        Pcluster Gdegree threshold quota) miss) :
    ∃ zA ∈ Q.A₀, zA ∉ badA ∧ ∃ zB ∈ Q.B₀, zB ∉ badB ∧
      let Lp := padFinset
        (Erdos547b.ZhaoQuantitativeLargeClusters.largeClustersAtLeast
          Pcluster Gdegree threshold quota)
      let A : EvenPadding I := Sum.inl Q.A
      let B : EvenPadding I := Sum.inl Q.B
      let density := twoRootSourceDensity H (padCluster cluster)
        (clusterSize : ℝ) A B zA zB
      (((threshold - loss - (exceptionalVertices (padAssignment Pcluster)).card -
          miss * clusterSize : ℕ) : ℝ) ≤
        sourceDegree Q.claim67.M Lp density (clusterSize : ℝ) A
          (allMatchingEdges Q.claim67.M)) ∧
      (((threshold - loss - (exceptionalVertices (padAssignment Pcluster)).card -
          miss * clusterSize : ℕ) : ℝ) ≤
        sourceDegree Q.claim67.M Lp density (clusterSize : ℝ) B
          (allMatchingEdges Q.claim67.M)) ∧
      (∀ x, 0 ≤ density A x) ∧
      (∀ e : MatchingEdge Q.claim67.M,
        0 ≤ (clusterSize : ℝ) *
          (density A (orientedEndpoint Q.claim67.M Lp e 0) +
            density A (orientedEndpoint Q.claim67.M Lp e 1))) ∧
      (∀ e : MatchingEdge Q.claim67.M,
        0 ≤ (clusterSize : ℝ) *
          (density B (orientedEndpoint Q.claim67.M Lp e 0) +
            density B (orientedEndpoint Q.claim67.M Lp e 1))) ∧
      (∀ e : MatchingEdge Q.claim67.M,
        (clusterSize : ℝ) *
          (density A (orientedEndpoint Q.claim67.M Lp e 0) +
            density A (orientedEndpoint Q.claim67.M Lp e 1)) ≤
              2 * clusterSize) ∧
      (∀ e : MatchingEdge Q.claim67.M,
        (clusterSize : ℝ) *
          (density B (orientedEndpoint Q.claim67.M Lp e 0) +
            density B (orientedEndpoint Q.claim67.M Lp e 1)) ≤
              2 * clusterSize) ∧
      (∀ x, 0 < density A x → (padGraph R0).Adj A x) ∧
      (∀ x, 0 < density B x → (padGraph R0).Adj B x) := by
  apply exists_twoRootSourceDensity_of_richClaim61_localDegree Pcluster Gdegree H
    R0 cluster hcluster threshold quota miss clusterSize loss hquota hclusterSize
    hclusterCard hrespect badA badB hbadA hbadB Q
  · intro z hz
    exact cleaned_degree_ge_threshold_sub_loss Gdegree H loss threshold hloss
      (Q.A₀_high z hz)
  · intro z hz
    exact cleaned_degree_ge_threshold_sub_loss Gdegree H loss threshold hloss
      (Q.B₀_high z hz)

variable {TreeVertex : Type v} [Fintype TreeVertex] [DecidableEq TreeVertex]
variable {HostVertex : Type w} [Fintype HostVertex] [DecidableEq HostVertex]

/-- The honest Lemma-6.15 contrapositive after deleting the at-most-two
matching edges incident with `A` or `B`. -/
theorem exceptional_families_away_lt_of_not_contained
    {L : Finset K} {miss : ℕ}
    (T : SimpleGraph TreeVertex) [DecidableRel T.Adj]
    (G : SimpleGraph HostVertex) [DecidableRel G.Adj]
    (C67 : Claim67Certificate R L miss)
    (A B : K) (density : K → K → ℝ) (eta k : ℝ)
    (hforce :
      eta * k ≤
          ((unbalancedEdges (edgesAwayFromDistinguished C67.M L A B)
            (fun e c ↦ density A
              (orientedEndpoint C67.M L e c)) eta).card : ℝ) ∨
        eta * k ≤
          ((nonextremeEdges (edgesAwayFromDistinguished C67.M L A B)
            (fun e c ↦ density A
              (orientedEndpoint C67.M L e c)) eta).card : ℝ) →
        T.IsContained G)
    (hnot : ¬ T.IsContained G) :
    (((unbalancedEdges (edgesAwayFromDistinguished C67.M L A B)
      (fun e c ↦ density A (orientedEndpoint C67.M L e c)) eta).card : ℕ) : ℝ) <
        eta * k ∧
    (((nonextremeEdges (edgesAwayFromDistinguished C67.M L A B)
      (fun e c ↦ density A (orientedEndpoint C67.M L e c)) eta).card : ℕ) : ℝ) <
        eta * k := by
  let S := edgesAwayFromDistinguished C67.M L A B
  constructor
  · by_contra h
    have hlarge : eta * k ≤
        ((unbalancedEdges S
          (fun e c ↦ density A (orientedEndpoint C67.M L e c)) eta).card : ℝ) :=
      le_of_not_gt h
    apply hnot
    exact hforce (Or.inl hlarge)
  · by_contra h
    have hlarge : eta * k ≤
        ((nonextremeEdges S
          (fun e c ↦ density A (orientedEndpoint C67.M L e c)) eta).card : ℝ) :=
      le_of_not_gt h
    apply hnot
    exact hforce (Or.inr hlarge)

/-! ## Literal source-filter deletion accounting -/

private theorem sum_union_le_add_of_nonneg
    {E : Type*} [DecidableEq E] (S T : Finset E) (f : E → ℝ)
    (hf : ∀ e, 0 ≤ f e) :
    (∑ e ∈ S ∪ T, f e) ≤ (∑ e ∈ S, f e) + ∑ e ∈ T, f e := by
  classical
  have hdisj : Disjoint S (T \ S) := by
    rw [Finset.disjoint_left]
    intro e heS heTS
    exact (Finset.mem_sdiff.mp heTS).2 heS
  have hunion : S ∪ (T \ S) = S ∪ T := by
    ext e
    simp only [Finset.mem_union, Finset.mem_sdiff]
    tauto
  rw [← hunion, Finset.sum_union hdisj]
  have htail : (∑ e ∈ T \ S, f e) ≤ ∑ e ∈ T, f e :=
    Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset
      (fun e _ _ ↦ hf e)
  simpa only [add_comm] using
    add_le_add_left htail (∑ e ∈ S, f e)

theorem unbalanced_all_card_le_away_add_two
    {L : Finset K} {miss : ℕ}
    (C67 : Claim67Certificate R L miss) (A B : K)
    (density : K → K → ℝ) (eta : ℝ) :
    (unbalancedEdges (allMatchingEdges C67.M)
      (fun e c ↦ density A (orientedEndpoint C67.M L e c)) eta).card ≤
      (unbalancedEdges (edgesAwayFromDistinguished C67.M L A B)
        (fun e c ↦ density A (orientedEndpoint C67.M L e c)) eta).card + 2 := by
  classical
  let AllBad := unbalancedEdges (allMatchingEdges C67.M)
    (fun e c ↦ density A (orientedEndpoint C67.M L e c)) eta
  let AwayBad := unbalancedEdges (edgesAwayFromDistinguished C67.M L A B)
    (fun e c ↦ density A (orientedEndpoint C67.M L e c)) eta
  let Incident := distinguishedIncidentEdges C67.M L A B
  have hsub : AllBad ⊆ AwayBad ∪ Incident := by
    intro e he
    have he' := (mem_unbalancedEdges.mp he)
    by_cases hI : e ∈ Incident
    · exact Finset.mem_union_right _ hI
    · apply Finset.mem_union_left
      apply mem_unbalancedEdges.mpr
      exact ⟨Finset.mem_sdiff.mpr ⟨he'.1, hI⟩, he'.2⟩
  calc
    AllBad.card ≤ (AwayBad ∪ Incident).card := Finset.card_le_card hsub
    _ ≤ AwayBad.card + Incident.card := Finset.card_union_le _ _
    _ ≤ AwayBad.card + 2 := Nat.add_le_add_left
      (distinguishedIncidentEdges_card_le_two
        C67.M C67.isMatching L A B) _

theorem nonextreme_all_card_le_away_add_two
    {L : Finset K} {miss : ℕ}
    (C67 : Claim67Certificate R L miss) (A B : K)
    (density : K → K → ℝ) (eta : ℝ) :
    (nonextremeEdges (allMatchingEdges C67.M)
      (fun e c ↦ density A (orientedEndpoint C67.M L e c)) eta).card ≤
      (nonextremeEdges (edgesAwayFromDistinguished C67.M L A B)
        (fun e c ↦ density A (orientedEndpoint C67.M L e c)) eta).card + 2 := by
  classical
  let AllBad := nonextremeEdges (allMatchingEdges C67.M)
    (fun e c ↦ density A (orientedEndpoint C67.M L e c)) eta
  let AwayBad := nonextremeEdges (edgesAwayFromDistinguished C67.M L A B)
    (fun e c ↦ density A (orientedEndpoint C67.M L e c)) eta
  let Incident := distinguishedIncidentEdges C67.M L A B
  have hsub : AllBad ⊆ AwayBad ∪ Incident := by
    intro e he
    have he' := (mem_nonextremeEdges.mp he)
    by_cases hI : e ∈ Incident
    · exact Finset.mem_union_right _ hI
    · apply Finset.mem_union_left
      apply mem_nonextremeEdges.mpr
      exact ⟨Finset.mem_sdiff.mpr ⟨he'.1, hI⟩, he'.2⟩
  calc
    AllBad.card ≤ (AwayBad ∪ Incident).card := Finset.card_le_card hsub
    _ ≤ AwayBad.card + Incident.card := Finset.card_union_le _ _
    _ ≤ AwayBad.card + 2 := Nat.add_le_add_left
      (distinguishedIncidentEdges_card_le_two
        C67.M C67.isMatching L A B) _

/-- Exact upper bound for the weight deleted by the literal Lemma-6.11
filters.  This is the source arithmetic formerly exposed as the large
`hdeletionBudget` premise. -/
theorem source_filter_deletion_sum_le
    {L : Finset K} {miss : ℕ}
    (C67 : Claim67Certificate R L miss) (A B : K) (hAO : A ∈ C67.O)
    (density : K → K → ℝ) (N eta : ℝ)
    (hN : 0 ≤ N) (heta : 0 < eta) (hetaHalf : eta < 1 / 2)
    (hnonnegDensity : ∀ e : MatchingEdge C67.M, ∀ c,
      0 ≤ density A (orientedEndpoint C67.M L e c))
    (hcap : ∀ e : MatchingEdge C67.M,
      N * (density A (orientedEndpoint C67.M L e 0) +
        density A (orientedEndpoint C67.M L e 1)) ≤ 2 * N)
    (hdensityAdj : ∀ x, 0 < density A x → R.Adj A x)
    (u x q : ℕ)
    (hu : (unbalancedEdges (allMatchingEdges C67.M)
      (fun e c ↦ density A (orientedEndpoint C67.M L e c)) eta).card ≤ u)
    (hx : (nonextremeEdges (allMatchingEdges C67.M)
      (fun e c ↦ density A (orientedEndpoint C67.M L e c)) eta).card ≤ x)
    (Mb : Finset (MatchingEdge C67.M))
    (hMb : Mb ⊆ allMatchingEdges C67.M) (hMbcard : Mb.card ≤ q) :
    (∑ e ∈ allMatchingEdges C67.M \
        sourceCleanEdges C67.M L C67.O density A eta Mb,
      N * (density A (orientedEndpoint C67.M L e 0) +
        density A (orientedEndpoint C67.M L e 1))) ≤
      2 * N * (u + x + q + 1) +
        3 * eta * N * (allMatchingEdges C67.M).card := by
  classical
  let contribution := fun e : MatchingEdge C67.M ↦
    N * (density A (orientedEndpoint C67.M L e 0) +
      density A (orientedEndpoint C67.M L e 1))
  let U := unbalancedEdges (allMatchingEdges C67.M)
    (fun e c ↦ density A (orientedEndpoint C67.M L e c)) eta
  let X := nonextremeEdges (allMatchingEdges C67.M)
    (fun e c ↦ density A (orientedEndpoint C67.M L e c)) eta
  let Small := sourceSmallEdges C67.M L density A eta
  let Outside := sourceOutsideEdges C67.M L C67.O density A eta Mb
  let Deleted := allMatchingEdges C67.M \
    sourceCleanEdges C67.M L C67.O density A eta Mb
  have hcontributionNonneg : ∀ e, 0 ≤ contribution e := by
    intro e
    apply mul_nonneg hN
    exact add_nonneg (hnonnegDensity e 0) (hnonnegDensity e 1)
  have hsmallContribution : ∀ e ∈ Small,
      contribution e ≤ 3 * eta * N := by
    intro e he
    have he' := Finset.mem_filter.mp he
    have hnotU := (Finset.mem_sdiff.mp he'.1).2
    have hbalanced : |density A (orientedEndpoint C67.M L e 0) -
        density A (orientedEndpoint C67.M L e 1)| < eta := by
      exact lt_of_not_ge (fun h ↦ hnotU (mem_unbalancedEdges.mpr
        ⟨mem_allMatchingEdges C67.M e, h⟩))
    have habs := abs_lt.mp hbalanced
    have hsum : density A (orientedEndpoint C67.M L e 0) +
        density A (orientedEndpoint C67.M L e 1) < 3 * eta := by
      rcases he'.2 with hzero | hone <;> linarith
    dsimp only [contribution]
    calc
      N * (density A (orientedEndpoint C67.M L e 0) +
          density A (orientedEndpoint C67.M L e 1)) ≤ N * (3 * eta) :=
        mul_le_mul_of_nonneg_left hsum.le hN
      _ = 3 * eta * N := by ring
  have hOutsideCard : Outside.card ≤ 1 := by
    dsimp only [Outside]
    exact sourceOutsideEdges_card_le_one C67 A hAO density eta heta
      (by linarith) Mb hdensityAdj
  have hDeletedSub : Deleted ⊆ U ∪ X ∪ Small ∪ Mb ∪ Outside := by
    intro e he
    have heAll : e ∈ allMatchingEdges C67.M := (Finset.mem_sdiff.mp he).1
    have heNotClean := (Finset.mem_sdiff.mp he).2
    by_cases heU : e ∈ U
    · simp only [Finset.mem_union]
      exact Or.inl (Or.inl (Or.inl (Or.inl heU)))
    by_cases heX : e ∈ X
    · simp only [Finset.mem_union]
      exact Or.inl (Or.inl (Or.inl (Or.inr heX)))
    by_cases heSmall : e ∈ Small
    · simp only [Finset.mem_union]
      exact Or.inl (Or.inl (Or.inr heSmall))
    by_cases heMb : e ∈ Mb
    · simp only [Finset.mem_union]
      exact Or.inl (Or.inr heMb)
    have hePre : e ∈ sourcePrecleanEdges C67.M L density A eta Mb := by
      simp only [sourcePrecleanEdges, Finset.mem_sdiff]
      exact ⟨⟨⟨⟨heAll, heU⟩, heX⟩, heSmall⟩, heMb⟩
    have heEnds : ¬(orientedEndpoint C67.M L e 0 ∈ C67.O ∧
        orientedEndpoint C67.M L e 1 ∈ C67.O) := by
      intro hends
      apply heNotClean
      exact Finset.mem_filter.mpr ⟨hePre, hends⟩
    simp only [Finset.mem_union]
    exact Or.inr (Finset.mem_filter.mpr ⟨hePre, heEnds⟩)
  have hDeletedSum : (∑ e ∈ Deleted, contribution e) ≤
      (∑ e ∈ U, contribution e) +
      (∑ e ∈ X, contribution e) +
      (∑ e ∈ Small, contribution e) +
      (∑ e ∈ Mb, contribution e) +
      ∑ e ∈ Outside, contribution e := by
    have hsubsum : (∑ e ∈ Deleted, contribution e) ≤
        ∑ e ∈ U ∪ X ∪ Small ∪ Mb ∪ Outside, contribution e :=
      Finset.sum_le_sum_of_subset_of_nonneg hDeletedSub
        (fun e _ _ ↦ hcontributionNonneg e)
    have h1 := sum_union_le_add_of_nonneg (U ∪ X ∪ Small ∪ Mb) Outside
      contribution hcontributionNonneg
    have h2 := sum_union_le_add_of_nonneg (U ∪ X ∪ Small) Mb
      contribution hcontributionNonneg
    have h3 := sum_union_le_add_of_nonneg (U ∪ X) Small
      contribution hcontributionNonneg
    have h4 := sum_union_le_add_of_nonneg U X contribution hcontributionNonneg
    linarith
  have hUSum : (∑ e ∈ U, contribution e) ≤ (u : ℝ) * (2 * N) := by
    calc
      (∑ e ∈ U, contribution e) ≤ ∑ _e ∈ U, 2 * N :=
        Finset.sum_le_sum fun e _ ↦ hcap e
      _ = (U.card : ℝ) * (2 * N) := by
        rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (u : ℝ) * (2 * N) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hu)
          (mul_nonneg (by norm_num) hN)
  have hXSum : (∑ e ∈ X, contribution e) ≤ (x : ℝ) * (2 * N) := by
    calc
      (∑ e ∈ X, contribution e) ≤ ∑ _e ∈ X, 2 * N :=
        Finset.sum_le_sum fun e _ ↦ hcap e
      _ = (X.card : ℝ) * (2 * N) := by
        rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (x : ℝ) * (2 * N) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hx)
          (mul_nonneg (by norm_num) hN)
  have hSmallSum : (∑ e ∈ Small, contribution e) ≤
      (allMatchingEdges C67.M).card * (3 * eta * N) := by
    calc
      (∑ e ∈ Small, contribution e) ≤ ∑ _e ∈ Small, 3 * eta * N :=
        Finset.sum_le_sum hsmallContribution
      _ = (Small.card : ℝ) * (3 * eta * N) := by
        rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ((allMatchingEdges C67.M).card : ℝ) * (3 * eta * N) := by
        apply mul_le_mul_of_nonneg_right
        · exact_mod_cast Finset.card_le_card
            (show Small ⊆ allMatchingEdges C67.M by
              intro e he
              exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp he).1).1)
        · positivity
  have hMbSum : (∑ e ∈ Mb, contribution e) ≤ (q : ℝ) * (2 * N) := by
    calc
      (∑ e ∈ Mb, contribution e) ≤ ∑ _e ∈ Mb, 2 * N :=
        Finset.sum_le_sum fun e _ ↦ hcap e
      _ = (Mb.card : ℝ) * (2 * N) := by
        rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (q : ℝ) * (2 * N) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hMbcard)
          (mul_nonneg (by norm_num) hN)
  have hOutsideSum : (∑ e ∈ Outside, contribution e) ≤ 2 * N := by
    calc
      (∑ e ∈ Outside, contribution e) ≤ ∑ _e ∈ Outside, 2 * N :=
        Finset.sum_le_sum fun e _ ↦ hcap e
      _ = (Outside.card : ℝ) * (2 * N) := by
        rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 1 * (2 * N) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hOutsideCard)
          (mul_nonneg (by norm_num) hN)
      _ = 2 * N := by ring
  change (∑ e ∈ Deleted, contribution e) ≤ _
  push_cast
  nlinarith

theorem allMatchingEdges_card_le_paddedHalf
    {I : Type*} [Fintype I] [DecidableEq I]
    {R0 : SimpleGraph I} [DecidableRel R0.Adj]
    (M : (padGraph R0).Subgraph) (hM : M.IsMatching)
    (L : Finset (EvenPadding I)) :
    (allMatchingEdges M).card ≤ paddedHalf I := by
  have hsupp := edgeFinsetSubgraph_support_card M hM L (allMatchingEdges M)
  have hcard : (matchingSupport
      (edgeFinsetSubgraph M L (allMatchingEdges M))).card ≤
      Fintype.card (EvenPadding I) := by
    simpa only [Finset.card_univ] using
      Finset.card_le_card (Finset.subset_univ
        (matchingSupport (edgeFinsetSubgraph M L (allMatchingEdges M))))
  rw [hsupp, card_evenPadding] at hcard
  omega

theorem away_exceptional_card_le_auxiliaryScale
    {beta : ℚ} {reducedK : ℕ} {E : Type*} [DecidableEq E]
    (S : Finset E)
    (hS : (S.card : ℝ) < (eta beta : ℝ) * reducedK) :
    S.card ≤ auxiliaryScale beta reducedK := by
  have hceil : (eta beta : ℝ) * reducedK ≤
      (auxiliaryScale beta reducedK : ℝ) :=
    Erdos547b.ZhaoRoundedScales.le_upperScale_cast _
  have hcast : (S.card : ℝ) < (auxiliaryScale beta reducedK : ℝ) :=
    hS.trans_le hceil
  exact_mod_cast hcast.le

/-- The away-family Lemma-6.15 bounds imply the raw deletion-budget premise
of the Lemma-6.11 constructor once the displayed scalar hierarchy inequality
is supplied.  No statement about a desired matching decomposition appears
among the hypotheses. -/
theorem source_filter_deletion_budget_of_away
    {I : Type*} [Fintype I] [DecidableEq I]
    {R0 : SimpleGraph I} [DecidableRel R0.Adj]
    {beta : ℚ} {reducedK : ℕ}
    {L : Finset (EvenPadding I)} {miss : ℕ}
    (C67 : Claim67Certificate (padGraph R0) L miss)
    (A B : EvenPadding I) (hAO : A ∈ C67.O)
    (density : EvenPadding I → EvenPadding I → ℝ)
    (N targetA sourceLower : ℝ)
    (hN : 0 ≤ N) (hbeta : 0 < beta) (hbetaOne : beta ≤ 1 / 4)
    (hnonnegDensity : ∀ e : MatchingEdge C67.M, ∀ c,
      0 ≤ density A (orientedEndpoint C67.M L e c))
    (hcap : ∀ e : MatchingEdge C67.M,
      N * (density A (orientedEndpoint C67.M L e 0) +
        density A (orientedEndpoint C67.M L e 1)) ≤ 2 * N)
    (hdensityAdj : ∀ x, 0 < density A x → (padGraph R0).Adj A x)
    (hunbalancedAway :
      (((unbalancedEdges (edgesAwayFromDistinguished C67.M L A B)
        (fun e c ↦ density A (orientedEndpoint C67.M L e c))
          (eta beta : ℝ)).card : ℕ) : ℝ) <
            (eta beta : ℝ) * reducedK)
    (hnonextremeAway :
      (((nonextremeEdges (edgesAwayFromDistinguished C67.M L A B)
        (fun e c ↦ density A (orientedEndpoint C67.M L e c))
          (eta beta : ℝ)).card : ℕ) : ℝ) <
            (eta beta : ℝ) * reducedK)
    (hAllCard : (allMatchingEdges C67.M).card ≤ reducedK)
    (hsourceLower : sourceLower ≤
      sourceDegree C67.M L density N A (allMatchingEdges C67.M))
    (hnumeric : targetA +
        2 * N * (2 * (auxiliaryScale beta reducedK + 2) +
          claim617Q beta reducedK + 1) +
        3 * (eta beta : ℝ) * N * reducedK < sourceLower) :
    ∀ Mb : Finset (MatchingEdge C67.M),
      Mb ⊆ allMatchingEdges C67.M →
      Mb.card ≤ claim617Q beta reducedK →
      (∑ e ∈ allMatchingEdges C67.M \
          sourceCleanEdges C67.M L C67.O density A
            (eta beta : ℝ) Mb,
        N * (density A (orientedEndpoint C67.M L e 0) +
          density A (orientedEndpoint C67.M L e 1))) <
        sourceDegree C67.M L density N A (allMatchingEdges C67.M) - targetA := by
  intro Mb hMb hMbcard
  have hUaway := away_exceptional_card_le_auxiliaryScale
    (unbalancedEdges (edgesAwayFromDistinguished C67.M L A B)
      (fun e c ↦ density A (orientedEndpoint C67.M L e c))
        (eta beta : ℝ)) hunbalancedAway
  have hXaway := away_exceptional_card_le_auxiliaryScale
    (nonextremeEdges (edgesAwayFromDistinguished C67.M L A B)
      (fun e c ↦ density A (orientedEndpoint C67.M L e c))
        (eta beta : ℝ)) hnonextremeAway
  have hUall := (unbalanced_all_card_le_away_add_two
    C67 A B density (eta beta : ℝ)).trans
      (Nat.add_le_add_right hUaway 2)
  have hXall := (nonextreme_all_card_le_away_add_two
    C67 A B density (eta beta : ℝ)).trans
      (Nat.add_le_add_right hXaway 2)
  have hdelete := source_filter_deletion_sum_le C67 A B hAO density N
    (eta beta : ℝ) hN (by exact_mod_cast eta_pos hbeta)
      (by
        have heta := eta_le_rho_div_1000 hbeta hbetaOne
        have hrho : (rho beta : ℝ) ≤ 1 := by
          exact_mod_cast rho_le_one hbeta hbetaOne
        linarith)
      hnonnegDensity hcap hdensityAdj
      (auxiliaryScale beta reducedK + 2)
      (auxiliaryScale beta reducedK + 2)
      (claim617Q beta reducedK) hUall hXall Mb hMb hMbcard
  have hdelete' :
      (∑ e ∈ allMatchingEdges C67.M \
          sourceCleanEdges C67.M L C67.O density A
            (eta beta : ℝ) Mb,
        N * (density A (orientedEndpoint C67.M L e 0) +
          density A (orientedEndpoint C67.M L e 1))) ≤
        2 * N * (2 * (auxiliaryScale beta reducedK + 2) +
          claim617Q beta reducedK + 1) +
          3 * (eta beta : ℝ) * N * reducedK := by
    have hcoef : (0 : ℝ) ≤ 3 * (eta beta : ℝ) * N := by
      have heta : (0 : ℝ) ≤ (eta beta : ℝ) := by
        exact_mod_cast (eta_pos hbeta).le
      exact mul_nonneg (mul_nonneg (by norm_num) heta) hN
    have hcardCast : ((allMatchingEdges C67.M).card : ℝ) ≤ reducedK := by
      exact_mod_cast hAllCard
    calc
      _ ≤ 2 * N * ((auxiliaryScale beta reducedK + 2) +
            (auxiliaryScale beta reducedK + 2) +
            claim617Q beta reducedK + 1) +
          3 * (eta beta : ℝ) * N *
            ((allMatchingEdges C67.M).card : ℝ) := by
        simpa only [Nat.cast_add, Nat.cast_ofNat] using hdelete
      _ = 2 * N * (2 * (auxiliaryScale beta reducedK + 2) +
            claim617Q beta reducedK + 1) +
          3 * (eta beta : ℝ) * N *
            ((allMatchingEdges C67.M).card : ℝ) := by
        push_cast
        ring
      _ ≤ 2 * N * (2 * (auxiliaryScale beta reducedK + 2) +
            claim617Q beta reducedK + 1) +
          3 * (eta beta : ℝ) * N * reducedK := by
        have hlast := mul_le_mul_of_nonneg_left hcardCast hcoef
        linarith
  linarith

/-! ## One explicit rich-entry specialization -/

/-- The output handed simultaneously to Claim 6.16 and Claim 6.18.  It
retains the literal source-degree lower bounds and the quantitative
matching-edge coverage from Claim 6.1, rather than hiding either behind a
new interface assumption. -/
structure RichLemma611Output
    {V : Type u} {I : Type v} [Fintype V] [Fintype I]
    [DecidableEq V] [DecidableEq I]
    (Pcluster : ClusterAssignment V I)
    (Gdegree : SimpleGraph V) [DecidableRel Gdegree.Adj]
    (threshold quota : ℕ) (R0 : SimpleGraph I) [DecidableRel R0.Adj]
    (miss : ℕ)
    (Q : RichClaim61Certificate Pcluster Gdegree threshold quota R0
      (Erdos547b.ZhaoQuantitativeLargeClusters.largeClustersAtLeast
        Pcluster Gdegree threshold quota) miss)
    (density : EvenPadding I → EvenPadding I → ℝ)
    (N eta targetA targetB fb cutoff : ℝ)
    (lowerV1 upperV1 upperV2 mbEdgesBound mbBound : ℕ)
    (lowerA lowerB : ℝ)
    (exceptionalBound : ℝ) : Type (max u v) where
  D : MatchingDecomposition
    (padFinset (Erdos547b.ZhaoQuantitativeLargeClusters.largeClustersAtLeast
      Pcluster Gdegree threshold quota)) Q.claim67.O
    miss Q.claim67 lowerV1 upperV1 upperV2 mbBound
    (sourceDegree Q.claim67.M
      (padFinset (Erdos547b.ZhaoQuantitativeLargeClusters.largeClustersAtLeast
        Pcluster Gdegree threshold quota)) density N (Sum.inl Q.A))
  min_subset_clean : D.minEdges ⊆
    sourceCleanEdges Q.claim67.M
      (padFinset (Erdos547b.ZhaoQuantitativeLargeClusters.largeClustersAtLeast
        Pcluster Gdegree threshold quota)) Q.claim67.O density (Sum.inl Q.A)
          eta D.mbEdges
  targetA_eq : D.targetA = targetA
  reservedCapacity : OptionalReservedCapacity D
    (sourceDegree Q.claim67.M
      (padFinset (Erdos547b.ZhaoQuantitativeLargeClusters.largeClustersAtLeast
        Pcluster Gdegree threshold quota)) density N (Sum.inl Q.B))
    targetB N fb cutoff mbEdgesBound
  degreeA_all : lowerA ≤ sourceDegree Q.claim67.M
    (padFinset (Erdos547b.ZhaoQuantitativeLargeClusters.largeClustersAtLeast
      Pcluster Gdegree threshold quota)) density N (Sum.inl Q.A)
      (allMatchingEdges Q.claim67.M)
  degreeB_all : lowerB ≤ sourceDegree Q.claim67.M
    (padFinset (Erdos547b.ZhaoQuantitativeLargeClusters.largeClustersAtLeast
      Pcluster Gdegree threshold quota)) density N (Sum.inl Q.B)
      (allMatchingEdges Q.claim67.M)
  degreeA_away : lowerA - 4 * N ≤ sourceDegree Q.claim67.M
    (padFinset (Erdos547b.ZhaoQuantitativeLargeClusters.largeClustersAtLeast
      Pcluster Gdegree threshold quota)) density N (Sum.inl Q.A)
      (edgesAwayFromDistinguished Q.claim67.M
        (padFinset (Erdos547b.ZhaoQuantitativeLargeClusters.largeClustersAtLeast
          Pcluster Gdegree threshold quota)) (Sum.inl Q.A) (Sum.inl Q.B))
  degreeB_away : lowerB - 4 * N ≤ sourceDegree Q.claim67.M
    (padFinset (Erdos547b.ZhaoQuantitativeLargeClusters.largeClustersAtLeast
      Pcluster Gdegree threshold quota)) density N (Sum.inl Q.B)
      (edgesAwayFromDistinguished Q.claim67.M
        (padFinset (Erdos547b.ZhaoQuantitativeLargeClusters.largeClustersAtLeast
          Pcluster Gdegree threshold quota)) (Sum.inl Q.A) (Sum.inl Q.B))
  unbalanced_away_lt :
    (((unbalancedEdges
      (edgesAwayFromDistinguished Q.claim67.M
        (padFinset (Erdos547b.ZhaoQuantitativeLargeClusters.largeClustersAtLeast
          Pcluster Gdegree threshold quota)) (Sum.inl Q.A) (Sum.inl Q.B))
      (fun e c ↦ density (Sum.inl Q.A)
        (orientedEndpoint Q.claim67.M
          (padFinset (Erdos547b.ZhaoQuantitativeLargeClusters.largeClustersAtLeast
            Pcluster Gdegree threshold quota)) e c)) eta).card : ℕ) : ℝ) <
      exceptionalBound
  nonextreme_away_lt :
    (((nonextremeEdges
      (edgesAwayFromDistinguished Q.claim67.M
        (padFinset (Erdos547b.ZhaoQuantitativeLargeClusters.largeClustersAtLeast
          Pcluster Gdegree threshold quota)) (Sum.inl Q.A) (Sum.inl Q.B))
      (fun e c ↦ density (Sum.inl Q.A)
        (orientedEndpoint Q.claim67.M
          (padFinset (Erdos547b.ZhaoQuantitativeLargeClusters.largeClustersAtLeast
            Pcluster Gdegree threshold quota)) e c)) eta).card : ℕ) : ℝ) <
      exceptionalBound
  sourceDensityAdjA : ∀ x,
    0 < density (Sum.inl Q.A) x →
      (padGraph R0).Adj (Sum.inl Q.A) x
  sourceDensityAdjB : ∀ x,
    0 < density (Sum.inl Q.B) x →
      (padGraph R0).Adj (Sum.inl Q.B) x
  matching_edge_meets_large : ∀ e : MatchingEdge Q.claim67.M,
    e.1.out.1 ∈ padFinset
      (Erdos547b.ZhaoQuantitativeLargeClusters.largeClustersAtLeast
        Pcluster Gdegree threshold quota) ∨
    e.1.out.2 ∈ padFinset
      (Erdos547b.ZhaoQuantitativeLargeClusters.largeClustersAtLeast
        Pcluster Gdegree threshold quota)

/-- Concrete rich-entry invocation of the literal Lemma-6.11 constructor.

All scalar choices from the eventual hierarchy are fixed here:
`d = lemma611D beta`, `eta = eta beta`,
`targetA = lemma611TargetA beta nTree`,
`miss = claim61Miss beta reducedK`, the capped `M_in` size is
`minEdgeCap reducedK = ⌊reducedK/2⌋`, and the optional `M_b` has at most
`claim617Q beta reducedK` edges (hence support at most twice that).  The
cluster-size and coverage hypotheses are the literal degree-form identities
used to discharge the deletion and capacity inequalities; neither scalar
inequality is left at the public boundary.
-/
noncomputable def explicitMatchingDecompositionOfRichClaim61OfExceptionalBounds
    {V I : Type*} [Fintype V] [Fintype I]
    [DecidableEq V] [DecidableEq I]
    {beta : ℚ} (hbeta : 0 < beta) (hbetaOne : beta ≤ 1 / 4)
    (Pcluster : ClusterAssignment V I)
    (Gdegree : SimpleGraph V) [DecidableRel Gdegree.Adj]
    (threshold quota reducedK : ℕ)
    (hreducedK : reducedK = paddedHalf I)
    (hreducedKLarge : section6K₀ beta ≤ reducedK)
    (R0 : SimpleGraph I) [DecidableRel R0.Adj]
    (Q : RichClaim61Certificate Pcluster Gdegree threshold quota R0
      (Erdos547b.ZhaoQuantitativeLargeClusters.largeClustersAtLeast
        Pcluster Gdegree threshold quota) (claim61Miss beta reducedK))
    (density : EvenPadding I → EvenPadding I → ℝ)
    (N nTree targetB fb cutoff error : ℝ)
    (lowerV1 upperV1 upperV2 : ℕ)
    (hN : 0 < N) (hnTree : 0 < nTree)
    (herror : 0 ≤ error) (htargetB : 0 ≤ targetB)
    (hAnonneg : ∀ e : MatchingEdge Q.claim67.M,
      0 ≤ N * (density (Sum.inl Q.A)
          (orientedEndpoint Q.claim67.M
            (padFinset (Erdos547b.ZhaoQuantitativeLargeClusters.largeClustersAtLeast
              Pcluster Gdegree threshold quota)) e 0) +
        density (Sum.inl Q.A)
          (orientedEndpoint Q.claim67.M
            (padFinset (Erdos547b.ZhaoQuantitativeLargeClusters.largeClustersAtLeast
              Pcluster Gdegree threshold quota)) e 1)))
    (hAdensityNonneg : ∀ x, 0 ≤ density (Sum.inl Q.A) x)
    (hBnonneg : ∀ e : MatchingEdge Q.claim67.M,
      0 ≤ N * (density (Sum.inl Q.B)
          (orientedEndpoint Q.claim67.M
            (padFinset (Erdos547b.ZhaoQuantitativeLargeClusters.largeClustersAtLeast
              Pcluster Gdegree threshold quota)) e 0) +
        density (Sum.inl Q.B)
          (orientedEndpoint Q.claim67.M
            (padFinset (Erdos547b.ZhaoQuantitativeLargeClusters.largeClustersAtLeast
              Pcluster Gdegree threshold quota)) e 1)))
    (hAcap : ∀ e : MatchingEdge Q.claim67.M,
      N * (density (Sum.inl Q.A)
          (orientedEndpoint Q.claim67.M
            (padFinset (Erdos547b.ZhaoQuantitativeLargeClusters.largeClustersAtLeast
              Pcluster Gdegree threshold quota)) e 0) +
        density (Sum.inl Q.A)
          (orientedEndpoint Q.claim67.M
            (padFinset (Erdos547b.ZhaoQuantitativeLargeClusters.largeClustersAtLeast
              Pcluster Gdegree threshold quota)) e 1)) ≤ 2 * N)
    (hBcap : ∀ e : MatchingEdge Q.claim67.M,
      N * (density (Sum.inl Q.B)
          (orientedEndpoint Q.claim67.M
            (padFinset (Erdos547b.ZhaoQuantitativeLargeClusters.largeClustersAtLeast
              Pcluster Gdegree threshold quota)) e 0) +
        density (Sum.inl Q.B)
          (orientedEndpoint Q.claim67.M
            (padFinset (Erdos547b.ZhaoQuantitativeLargeClusters.largeClustersAtLeast
              Pcluster Gdegree threshold quota)) e 1)) ≤ 2 * N)
    (hdegreeA : (1 - 10 * Real.sqrt (lemma611D beta)) * nTree + 4 * N ≤
      sourceDegree Q.claim67.M
        (padFinset (Erdos547b.ZhaoQuantitativeLargeClusters.largeClustersAtLeast
          Pcluster Gdegree threshold quota)) density N (Sum.inl Q.A)
        (allMatchingEdges Q.claim67.M))
    (hdegreeB : (1 - 10 * Real.sqrt (lemma611D beta)) * nTree + 4 * N ≤
      sourceDegree Q.claim67.M
        (padFinset (Erdos547b.ZhaoQuantitativeLargeClusters.largeClustersAtLeast
          Pcluster Gdegree threshold quota)) density N (Sum.inl Q.B)
        (allMatchingEdges Q.claim67.M))
    (hsourceDensityAdjA : ∀ x,
      0 < density (Sum.inl Q.A) x →
        (padGraph R0).Adj (Sum.inl Q.A) x)
    (hsourceDensityAdjB : ∀ x,
      0 < density (Sum.inl Q.B) x →
        (padGraph R0).Adj (Sum.inl Q.B) x)
    (hBtotal : targetB ≤ sourceDegree Q.claim67.M
      (padFinset (Erdos547b.ZhaoQuantitativeLargeClusters.largeClustersAtLeast
        Pcluster Gdegree threshold quota)) density N (Sum.inl Q.B)
      (allMatchingEdges Q.claim67.M))
    (hBtotalPos : 0 < sourceDegree Q.claim67.M
      (padFinset (Erdos547b.ZhaoQuantitativeLargeClusters.largeClustersAtLeast
        Pcluster Gdegree threshold quota)) density N (Sum.inl Q.B)
      (allMatchingEdges Q.claim67.M))
    (hBcard : ((allMatchingEdges Q.claim67.M).card : ℝ) *
        (targetB + 2 * N) ≤
      (claim617Q beta reducedK : ℝ) * sourceDegree Q.claim67.M
        (padFinset (Erdos547b.ZhaoQuantitativeLargeClusters.largeClustersAtLeast
          Pcluster Gdegree threshold quota)) density N (Sum.inl Q.B)
        (allMatchingEdges Q.claim67.M))
    (hnCovered : nTree ≤ (reducedK : ℝ) * N + error)
    (hcover : (reducedK : ℝ) * N ≤ nTree + N)
    (herrorSmall : error ≤ (sigma beta : ℝ) * nTree)
    (hcluster : N ≤ 3 * (sigma beta : ℝ) * nTree)
    (hlower : ∀ S : Finset (MatchingEdge Q.claim67.M),
      S ⊆ allMatchingEdges Q.claim67.M →
      lemma611TargetA beta nTree < sourceDegree Q.claim67.M
        (padFinset (Erdos547b.ZhaoQuantitativeLargeClusters.largeClustersAtLeast
          Pcluster Gdegree threshold quota)) density N (Sum.inl Q.A) S →
      lowerV1 ≤ 2 * S.card)
    (hupper : 2 * minEdgeCap reducedK ≤ upperV1)
    (htotalCard : Fintype.card (EvenPadding I) ≤ lowerV1 + upperV2)
    (hExceptionalUnbalanced :
      (((unbalancedEdges
          (edgesAwayFromDistinguished Q.claim67.M
            (padFinset (Erdos547b.ZhaoQuantitativeLargeClusters.largeClustersAtLeast
              Pcluster Gdegree threshold quota)) (Sum.inl Q.A) (Sum.inl Q.B))
          (fun e c ↦ density (Sum.inl Q.A)
            (orientedEndpoint Q.claim67.M
              (padFinset (Erdos547b.ZhaoQuantitativeLargeClusters.largeClustersAtLeast
                Pcluster Gdegree threshold quota)) e c)) (eta beta : ℝ)).card : ℕ) : ℝ) <
        (eta beta : ℝ) * reducedK)
    (hExceptionalNonextreme :
      (((nonextremeEdges
          (edgesAwayFromDistinguished Q.claim67.M
            (padFinset (Erdos547b.ZhaoQuantitativeLargeClusters.largeClustersAtLeast
              Pcluster Gdegree threshold quota)) (Sum.inl Q.A) (Sum.inl Q.B))
          (fun e c ↦ density (Sum.inl Q.A)
            (orientedEndpoint Q.claim67.M
              (padFinset (Erdos547b.ZhaoQuantitativeLargeClusters.largeClustersAtLeast
                Pcluster Gdegree threshold quota)) e c)) (eta beta : ℝ)).card : ℕ) : ℝ) <
        (eta beta : ℝ) * reducedK) :
    RichLemma611Output Pcluster Gdegree threshold quota R0
      (claim61Miss beta reducedK) Q density N (eta beta : ℝ)
      (lemma611TargetA beta nTree) targetB fb cutoff lowerV1 upperV1 upperV2
      (claim617Q beta reducedK) (2 * claim617Q beta reducedK)
      ((1 - 10 * Real.sqrt (lemma611D beta)) * nTree + 4 * N)
      ((1 - 10 * Real.sqrt (lemma611D beta)) * nTree + 4 * N)
      ((eta beta : ℝ) * reducedK) := by
  let Lp := padFinset
    (Erdos547b.ZhaoQuantitativeLargeClusters.largeClustersAtLeast
      Pcluster Gdegree threshold quota)
  let A : EvenPadding I := Sum.inl Q.A
  let B : EvenPadding I := Sum.inl Q.B
  have htargetA : 0 ≤ lemma611TargetA beta nTree :=
    lemma611TargetA_nonneg hbeta hbetaOne hnTree.le
  have hdeletionNumeric := lemma611_deletion_numeric hbeta hbetaOne hN
    hnTree.le hcluster hcover
  have hcap : 0 < minEdgeCap reducedK :=
    minEdgeCap_pos hbeta hbetaOne hreducedKLarge
  have hcapEnough := lemma611_minEdgeCap_capacity hbeta hbetaOne hN
    hnTree herror hnCovered hcover herrorSmall hcluster
  have hexceptional :
      (((unbalancedEdges
          (edgesAwayFromDistinguished Q.claim67.M Lp A B)
          (fun e c ↦ density A (orientedEndpoint Q.claim67.M Lp e c))
          (eta beta : ℝ)).card : ℕ) : ℝ) < (eta beta : ℝ) * reducedK ∧
      (((nonextremeEdges
          (edgesAwayFromDistinguished Q.claim67.M Lp A B)
          (fun e c ↦ density A (orientedEndpoint Q.claim67.M Lp e c))
          (eta beta : ℝ)).card : ℕ) : ℝ) < (eta beta : ℝ) * reducedK := by
    constructor
    · simpa [Lp, A, B] using hExceptionalUnbalanced
    · simpa [Lp, A, B] using hExceptionalNonextreme
  have hAwayA : (1 - 10 * Real.sqrt (lemma611D beta)) * nTree ≤
      sourceDegree Q.claim67.M Lp density N A
        (edgesAwayFromDistinguished Q.claim67.M Lp A B) := by
    apply sourceDegree_away_lower Q.claim67.M Q.claim67.isMatching Lp
      density N ((1 - 10 * Real.sqrt (lemma611D beta)) * nTree) A A B
        hN.le hAnonneg hAcap
    simpa [A, Lp] using hdegreeA
  have hAwayB : (1 - 10 * Real.sqrt (lemma611D beta)) * nTree ≤
      sourceDegree Q.claim67.M Lp density N B
        (edgesAwayFromDistinguished Q.claim67.M Lp A B) := by
    apply sourceDegree_away_lower Q.claim67.M Q.claim67.isMatching Lp
      density N ((1 - 10 * Real.sqrt (lemma611D beta)) * nTree) B A B
        hN.le hBnonneg hBcap
    simpa [B, Lp] using hdegreeB
  have hAllCard : (allMatchingEdges Q.claim67.M).card ≤ reducedK := by
    calc
      (allMatchingEdges Q.claim67.M).card ≤ paddedHalf I :=
        allMatchingEdges_card_le_paddedHalf Q.claim67.M
          Q.claim67.isMatching Lp
      _ = reducedK := hreducedK.symm
  have hdeletionBudget : ∀ Mb : Finset (MatchingEdge Q.claim67.M),
      Mb ⊆ allMatchingEdges Q.claim67.M →
      Mb.card ≤ claim617Q beta reducedK →
      (∑ e ∈ allMatchingEdges Q.claim67.M \
          sourceCleanEdges Q.claim67.M Lp Q.claim67.O density A
            (eta beta : ℝ) Mb,
        N * (density A (orientedEndpoint Q.claim67.M Lp e 0) +
          density A (orientedEndpoint Q.claim67.M Lp e 1))) <
        sourceDegree Q.claim67.M Lp density N A
          (allMatchingEdges Q.claim67.M) - lemma611TargetA beta nTree := by
    apply source_filter_deletion_budget_of_away Q.claim67 A B
      Q.A_in_claim67O density N (lemma611TargetA beta nTree)
      ((1 - 10 * Real.sqrt (lemma611D beta)) * nTree + 4 * N)
      hN.le hbeta hbetaOne
    · intro e c
      exact hAdensityNonneg _
    · exact hAcap
    · exact hsourceDensityAdjA
    · exact hexceptional.1
    · exact hexceptional.2
    · exact hAllCard
    · simpa [A, Lp] using hdegreeA
    · exact hdeletionNumeric
  let hexists := exists_matchingDecomposition_of_claim67 Q.claim67 A B density N
      (eta beta : ℝ) (lemma611TargetA beta nTree) targetB fb cutoff
      (minEdgeCap reducedK) lowerV1 upperV1 upperV2
      (claim617Q beta reducedK) (2 * claim617Q beta reducedK)
      hN (by exact_mod_cast eta_pos hbeta) htargetA htargetB
      hAnonneg hBnonneg hBcap hBtotal hBtotalPos hBcard (by omega)
      hdeletionBudget hcap hcapEnough hlower hupper htotalCard
  let D := Classical.choose hexists
  have hspec := Classical.choose_spec hexists
  rcases hspec with ⟨hclean, htarget, hreserved⟩
  refine
    { D := D
      min_subset_clean := ?_
      targetA_eq := htarget
      reservedCapacity := hreserved
      degreeA_all := ?_
      degreeB_all := ?_
      degreeA_away := ?_
      degreeB_away := ?_
      unbalanced_away_lt := ?_
      nonextreme_away_lt := ?_
      sourceDensityAdjA := hsourceDensityAdjA
      sourceDensityAdjB := hsourceDensityAdjB
      matching_edge_meets_large := Q.matching_edge_meets_large }
  · exact hclean
  · exact hdegreeA
  · exact hdegreeB
  · convert hAwayA using 1 <;> simp [A, B, Lp] <;> ring
  · convert hAwayB using 1 <;> simp [A, B, Lp] <;> ring
  · exact hexceptional.1
  · exact hexceptional.2

end Erdos547b.ZhaoRichClaim61Lemma611

#print axioms Erdos547b.ZhaoRichClaim61Lemma611.explicitMatchingDecompositionOfRichClaim61OfExceptionalBounds
#print axioms Erdos547b.ZhaoRichClaim61Lemma611.matchingSupport_degree_lower_of_retainedRoot
#print axioms Erdos547b.ZhaoRichClaim61Lemma611.exists_twoRootSourceDensity_of_richClaim61_localDegree
#print axioms Erdos547b.ZhaoRichClaim61Lemma611.exists_twoRootSourceDensity_of_richClaim61
