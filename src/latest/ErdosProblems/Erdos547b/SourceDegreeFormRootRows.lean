/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceClaim61Entry
import ErdosProblems.Erdos547b.SourceRootRowsPreparation
import ErdosProblems.Erdos547b.SourcePairPrunedRootRows

/-!
# Clean source roots from the actual degree-form witness

This instantiates the almost-all-target construction at the explicit source
parameters. The source graph is a further subgraph of the pair-pruned host;
the graph used for regular-pair embeddings remains unchanged.
-/

open scoped SimpleGraph Classical
noncomputable section

namespace Erdos547b.ZhaoSourceDegreeFormRootRows

open Finset SimpleGraph Erdos547EC2
open Erdos547b.ZhaoStability Erdos547b.ZhaoDegreeForm
open Erdos547b.ZhaoSection6Dichotomy Erdos547b.ZhaoQuantitativeLargeClusters
open Erdos547b.ZhaoEvenReducedPadding Erdos547b.ZhaoClaim61RichFull
open Erdos547b.ZhaoSection6RichHierarchy Erdos547b.ZhaoSourceClaim61Numerics
open Erdos547b.ZhaoSourceParameterSchedule Erdos547b.ZhaoSourceDegreeFormBounds
open Erdos547b.ZhaoSourceClaim61Entry Erdos547b.ZhaoClusterPairPruning
open Erdos547b.ZhaoSourceRootTruncation Erdos547b.ZhaoSourceRootRowsPreparation
open Erdos547b.ZhaoRichClaim61Lemma611 Erdos547b.ZhaoLemma611Full
open Erdos547b.ZhaoClaim616

abbrev Witness (α : ℚ) (q M : ℕ) {hostN : ℕ}
    (G : SimpleGraph (Fin hostN)) [DecidableRel G.Adj] :=
  DegreeFormWitness (pruneSmallEdges G {v | q ≤ G.degree v})
    (epsilon α) (densityCutoff α) (requestedClusters α) M

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G)

abbrev Index := {C // C ∈ W.partition.parts}
abbrev assignment := partitionAssignment W.exceptional W.partition
abbrev sourceQuota := richQuota ((fourthRoot α : ℝ) ^ 2) W.clusterSize
abbrev large := largeClustersAtLeast (assignment W) G q (sourceQuota W)
abbrev reduced : SimpleGraph (Index W) :=
  pruneSmallEdges
    (regularityReducedGraph (pruneSmallEdges G {v | q ≤ G.degree v})
      (fun i : Index W => i.1) (epsilon α) (densityCutoff α)) (large W : Set (Index W))
abbrev host : SimpleGraph (Fin hostN) := pairPrunedGraph (assignment W) W.graph (large W)
abbrev missed := 2 * matchingDefect ((fourthRoot α : ℝ) ^ 2) (paddedHalf (Index W)) + 1
abbrev Certificate :=
  RichClaim61Certificate (assignment W) G q (sourceQuota W) (reduced W) (large W) (missed W)

/-- The two chosen roots and their actual source graph, with all extra
cleanup charged to the unused square-root margin. -/
structure CleanSourceWitness (Q : Certificate W) where
  source : SimpleGraph (Fin hostN)
  zA : Fin hostN
  zB : Fin hostN
  zA_mem : zA ∈ Q.A₀
  zB_mem : zB ∈ Q.B₀
  distinct : zA ≠ zB
  extraLoss : ℕ
  source_le : source ≤ host W
  degree_loss : DegreeLossAtMost (host W) source extraLoss
  extraLoss_small : (extraLoss : ℝ) < (fourthRoot α : ℝ) ^ 2 * q
  upperA : ∀ j : Index W, j ≠ Q.A → j ≠ Q.B →
    0 < degreeInto source zA (clusterVertices (assignment W) j) →
    (degreeInto source zA (clusterVertices (assignment W) j) : ℝ) ≤
      ((host W).edgeDensity (clusterVertices (assignment W) Q.A)
          (clusterVertices (assignment W) j) + (epsilon α : ℝ)) *
        (clusterVertices (assignment W) j).card
  upperB : ∀ j : Index W, j ≠ Q.A → j ≠ Q.B →
    0 < degreeInto source zB (clusterVertices (assignment W) j) →
    (degreeInto source zB (clusterVertices (assignment W) j) : ℝ) ≤
      ((host W).edgeDensity (clusterVertices (assignment W) Q.B)
          (clusterVertices (assignment W) j) + (epsilon α : ℝ)) *
        (clusterVertices (assignment W) j).card

private theorem uniform_real_of_rat
    {V : Type*} (H : SimpleGraph V) [DecidableRel H.Adj]
    {ε : ℚ} {X Y : Finset V} (h : H.IsUniform ε X Y) :
    H.IsUniform (ε : ℝ) X Y := by
  intro X' hX' Y' hY' hXlarge hYlarge
  have hXQ : (X.card : ℚ) * ε ≤ (X'.card : ℚ) := by exact_mod_cast hXlarge
  have hYQ : (Y.card : ℚ) * ε ≤ (Y'.card : ℚ) := by exact_mod_cast hYlarge
  exact_mod_cast h hX' hY' hXQ hYQ

/-- Every input is now an actual degree-form witness or source parameter:
there is no assumed typicality-union budget or embedding continuation. -/
theorem exists_clean_source
    (hα : 0 < α) (hα1 : α ≤ 1 / 4) (Q : Certificate W)
    (hhost : hostN = 2 * q) (horder : orderThreshold α M ≤ q) :
    Nonempty (CleanSourceWitness W Q) := by
  subst hostN
  let _ : DecidableRel W.graph.Adj := W.graph_decidable
  let J : Finset (Index W) := Finset.univ \ {Q.A, Q.B}
  have hJ : ∀ j ∈ J, j ≠ Q.A ∧ j ≠ Q.B := by
    intro j hj
    simpa only [J, Finset.mem_sdiff, Finset.mem_univ, true_and,
      Finset.mem_insert, Finset.mem_singleton, not_or] using hj
  have hcluster (i : Index W) : clusterVertices (assignment W) i = i.1 :=
    clusterVertices_partitionAssignment W.exceptional W.partition i
  have hclusterCard (i : Index W) :
      (clusterVertices (assignment W) i).card = W.clusterSize := by
    rw [hcluster]
    exact W.equal_clusters i.1 i.2
  have huniform (i j : Index W) :
      (host W).IsUniform (epsilon α : ℝ)
        (clusterVertices (assignment W) i) (clusterVertices (assignment W) j) := by
    apply uniform_real_of_rat
    apply uniform_pair (assignment W) W.graph (large W)
    rw [hcluster, hcluster]
    exact W.pair_uniform i j
  obtain ⟨hδposQ, hδmargin⟩ := rootTypicality_margin hα hα1
  have hδpos : (0 : ℝ) < rootTypicality α := by exact_mod_cast hδposQ
  have hδsmallQ : rootTypicality α < 2 * fourthRoot α ^ 2 := by
    linarith only [hδmargin, sq_nonneg (fourthRoot α)]
  have hδsmall : (rootTypicality α : ℝ) < 2 * (fourthRoot α : ℝ) ^ 2 := by
    exact_mod_cast hδsmallQ
  have hNpos : (0 : ℝ) < W.clusterSize := by exact_mod_cast W.clusterSize_pos
  have hpool (i : Index W) (pool : Finset (Fin (2 * q)))
      (hpoolCard : pool.card = sourceQuota W) :
      (rootTypicality α : ℝ) * (clusterVertices (assignment W) i).card < pool.card := by
    rw [hclusterCard, hpoolCard]
    calc
      (rootTypicality α : ℝ) * W.clusterSize <
          (2 * (fourthRoot α : ℝ) ^ 2) * W.clusterSize :=
        mul_lt_mul_of_pos_right hδsmall hNpos
      _ ≤ (sourceQuota W : ℝ) := Nat.le_ceil _
  have hεsquare : (epsilon α : ℝ) ≤ (rootTypicality α : ℝ) ^ 2 := by
    exact_mod_cast (rootTypicality_sq α).symm.le
  obtain ⟨zA, hzA, zB, hzB, DA, hDA, DB, hDB, hroots, hmassA, hmassB,
      hsource, hdegreeLoss, hupperA, hupperB⟩ :=
    exists_two_clean_roots (assignment W) (host W) Q.A Q.B Q.adj.ne Q.A₀ Q.B₀
      Q.A₀_subset Q.B₀_subset J hJ W.clusterSize
      (fun i _ => (hclusterCard i).le) (epsilon α : ℝ) (rootTypicality α : ℝ)
      hδpos hεsquare (fun j _ => huniform Q.A j) (fun j _ => huniform Q.B j)
      (hpool Q.A Q.A₀ Q.A₀_card) (hpool Q.B Q.B₀ Q.B₀_card)
  let Hsource := truncateRoot (truncateRoot (host W) zA (clusterUnion (assignment W) DA))
    zB (clusterUnion (assignment W) DB)
  let extraLoss := max (clusterUnion (assignment W) DA).card
    (clusterUnion (assignment W) DB).card + 2
  have hJcard : J.card ≤ W.partition.parts.card := by
    have h := Finset.card_le_univ J
    simpa only [Index, Fintype.card_coe] using h
  have hJcardR : (J.card : ℝ) ≤ W.partition.parts.card := by exact_mod_cast hJcard
  have hJscale : (rootTypicality α : ℝ) * J.card * W.clusterSize ≤
      (rootTypicality α : ℝ) * W.partition.parts.card * W.clusterSize := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hJcardR hδpos.le) (by positivity)
  have hmax : (max (clusterUnion (assignment W) DA).card
      (clusterUnion (assignment W) DB).card : ℝ) ≤
        (rootTypicality α : ℝ) * J.card * W.clusterSize := by
    exact max_le hmassA hmassB
  have hlossSmall : (extraLoss : ℝ) < (fourthRoot α : ℝ) ^ 2 * q := by
    have hbudget := root_truncation_budget hα hα1 W horder
    dsimp only [extraLoss]
    push_cast
    linarith only [hmax, hJscale, hbudget]
  refine ⟨{ source := Hsource
            zA := zA
            zB := zB
            zA_mem := hzA
            zB_mem := hzB
            distinct := hroots
            extraLoss := extraLoss
            source_le := hsource
            degree_loss := by convert hdegreeLoss using 1
            extraLoss_small := hlossSmall
            upperA := ?_
            upperB := ?_ }⟩
  · intro j hjA hjB
    convert hupperA j (by simp [J, hjA, hjB]) using 1 <;> congr!
  · intro j hjA hjB
    convert hupperB j (by simp [J, hjA, hjB]) using 1 <;> congr!

/-- Source-edge truncation keeps every reduced-graph compatibility fact. -/
theorem CleanSourceWitness.respects {Q : Certificate W} (F : CleanSourceWitness W Q) :
    EdgesRespectReducedGraph (padAssignment (assignment W)) F.source (padGraph (reduced W)) := by
  apply edgesRespect_pad
  have h := respects_pruned_reduced_graph (assignment W) W.graph
    (regularityReducedGraph (pruneSmallEdges G {v | q ≤ G.degree v})
      (fun i : Index W => i.1) (epsilon α) (densityCutoff α)) (large W) W.respects_reduced
  intro u v i j hui hvj huv
  exact h hui hvj (F.source_le huv)

/-- At a high vertex in a large cluster, whole-pair pruning costs nothing;
only the degree-form and root-truncation losses are subtracted. -/
theorem CleanSourceWitness.retained_degree {Q : Certificate W} (F : CleanSourceWitness W Q)
    {i : Index W} (hi : i ∈ large W) {z : Fin hostN}
    (hz : z ∈ clusterVertices (assignment W) i) (hhigh : q ≤ G.degree z) :
    q - (W.loss + F.extraLoss) ≤ F.source.degree z := by
  have hloss : DegreeLossAtMost
      (pruneSmallEdges G {v | q ≤ G.degree v}) W.graph W.loss := by
    convert W.degree_loss using 1
  have hretained : q - W.loss ≤ (host W).degree z := by
    change q - W.loss ≤ (pairPrunedGraph (assignment W) W.graph (large W)).degree z
    rw [degree_eq_of_large_cluster (assignment W) W.graph (large W) hi
      ((mem_clusterVertices (assignment W) i z).mp hz)]
    exact cleaned_degree_ge_threshold_sub_loss _ _ W.loss q hloss
      ((highDegree_iff_pruneSmallEdges_highDegree G q z).mpr hhigh)
  have hextra := F.degree_loss z
  omega

/-- Integer lower bound for either source row on the complete matching. -/
abbrev rowFloor {Q : Certificate W} (F : CleanSourceWitness W Q) : ℕ :=
  q - (W.loss + F.extraLoss) - W.exceptional.card - missed W * W.clusterSize

/-- The total cleanup leaves the source's `10 * sqrt(d)` margin, including
the capacity needed to remove the two distinguished matching edges. -/
theorem CleanSourceWitness.rowFloor_lower
    (hα : 0 < α) (hα1 : α ≤ 1 / 4) {Q : Certificate W} (F : CleanSourceWitness W Q)
    (hhost : hostN = 2 * q) (horder : orderThreshold α M ≤ q) :
    (1 - 10 * (fourthRoot α : ℝ) ^ 2) * q + 4 * W.clusterSize < (rowFloor W F : ℝ) := by
  subst hostN
  have hcleanup := preExceptional_cleanup_bound_nine hα hα1 W horder
  have hextra := F.extraLoss_small
  have hsub : q ≤ rowFloor W F + (W.loss + F.extraLoss) +
      W.exceptional.card + missed W * W.clusterSize := by
    dsimp only [rowFloor]
    omega
  have hsubR : (q : ℝ) ≤ (rowFloor W F : ℝ) + (W.loss + F.extraLoss : ℕ) +
      W.exceptional.card + (missed W * W.clusterSize : ℕ) := by exact_mod_cast hsub
  change ((W.loss + W.exceptional.card + missed W * W.clusterSize +
    4 * W.clusterSize : ℕ) : ℝ) < 9 * (fourthRoot α : ℝ) ^ 2 * q at hcleanup
  push_cast at hcleanup hsubR
  linarith only [hcleanup, hextra, hsubR]

/-- Literal normalized neighbor rows of the two fixed, cleaned roots. -/
abbrev rootDensity {Q : Certificate W} (F : CleanSourceWitness W Q) :=
  twoRootSourceDensity F.source (padCluster (fun i : Index W => i.1))
    (W.clusterSize : ℝ) (Sum.inl Q.A) (Sum.inl Q.B) F.zA F.zB

/-- The contribution of one actual matching edge to a chosen source row. -/
abbrev rowWeight {Q : Certificate W} (F : CleanSourceWitness W Q)
    (C : EvenPadding (Index W)) (e : MatchingEdge Q.claim67.M) : ℝ :=
  (W.clusterSize : ℝ) *
    (rootDensity W F C (orientedEndpoint Q.claim67.M (padFinset (large W)) e 0) +
      rootDensity W F C (orientedEndpoint Q.claim67.M (padFinset (large W)) e 1))

/-- Matching-supported facts for these actual roots, with no new choice
of roots or independently supplied density matrix. -/
structure SourceRowFacts (Q : Certificate W) (F : CleanSourceWitness W Q) : Prop where
  totalA : (rowFloor W F : ℝ) ≤ sourceDegree Q.claim67.M (padFinset (large W))
    (rootDensity W F) W.clusterSize (Sum.inl Q.A) (allMatchingEdges Q.claim67.M)
  totalB : (rowFloor W F : ℝ) ≤ sourceDegree Q.claim67.M (padFinset (large W))
    (rootDensity W F) W.clusterSize (Sum.inl Q.B) (allMatchingEdges Q.claim67.M)
  density_nonneg : ∀ x, 0 ≤ rootDensity W F (Sum.inl Q.A) x
  weightA_nonneg : ∀ e, 0 ≤ rowWeight W F (Sum.inl Q.A) e
  weightB_nonneg : ∀ e, 0 ≤ rowWeight W F (Sum.inl Q.B) e
  weightA_le : ∀ e, rowWeight W F (Sum.inl Q.A) e ≤ 2 * W.clusterSize
  weightB_le : ∀ e, rowWeight W F (Sum.inl Q.B) e ≤ 2 * W.clusterSize
  supportA : ∀ x, 0 < rootDensity W F (Sum.inl Q.A) x →
    (padGraph (reduced W)).Adj (Sum.inl Q.A) x
  supportB : ∀ x, 0 < rootDensity W F (Sum.inl Q.B) x →
    (padGraph (reduced W)).Adj (Sum.inl Q.B) x

/-- Force the already constructed clean roots through the local-degree
selector by excluding every other vertex of each reservoir. -/
theorem CleanSourceWitness.source_rows {Q : Certificate W} (F : CleanSourceWitness W Q) :
    SourceRowFacts W Q F := by
  have hquota : 0 < sourceQuota W := by
    rw [← Q.A₀_card]
    exact Finset.card_pos.mpr ⟨F.zA, F.zA_mem⟩
  have hbadA : (Q.A₀.erase F.zA).card < sourceQuota W := by
    exact (Finset.card_erase_lt_of_mem F.zA_mem).trans_eq Q.A₀_card
  have hbadB : (Q.B₀.erase F.zB).card < sourceQuota W := by
    exact (Finset.card_erase_lt_of_mem F.zB_mem).trans_eq Q.B₀_card
  obtain ⟨zA, hzA, hnotA, zB, hzB, hnotB, hrows⟩ :=
    exists_twoRootSourceDensity_of_richClaim61_localDegree
      (assignment W) G F.source (reduced W) (fun i : Index W => i.1)
      (fun i => (clusterVertices_partitionAssignment W.exceptional W.partition i).symm)
      q (sourceQuota W) (missed W) W.clusterSize (W.loss + F.extraLoss)
      hquota W.clusterSize_pos (fun i => (W.equal_clusters i.1 i.2).le)
      (CleanSourceWitness.respects W F) (Q.A₀.erase F.zA) (Q.B₀.erase F.zB)
      hbadA hbadB Q
      (fun z hz => CleanSourceWitness.retained_degree W F Q.A_mem
        (Q.A₀_subset hz) (Q.A₀_high z hz))
      (fun z hz => CleanSourceWitness.retained_degree W F Q.B_mem
        (Q.B₀_subset hz) (Q.B₀_high z hz))
  have hzAeq : zA = F.zA := by
    by_contra hne
    exact hnotA (Finset.mem_erase.mpr ⟨hne, hzA⟩)
  have hzBeq : zB = F.zB := by
    by_contra hne
    exact hnotB (Finset.mem_erase.mpr ⟨hne, hzB⟩)
  subst zA
  subst zB
  obtain ⟨hA, hB, hnonneg, hwA, hwB, hcapA, hcapB, hsA, hsB⟩ := hrows
  refine ⟨?_, ?_, hnonneg, hwA, hwB, hcapA, hcapB, hsA, hsB⟩
  · simpa only [rowFloor, assignment, exceptionalVertices_padAssignment,
      exceptionalVertices_partitionAssignment] using hA
  · simpa only [rowFloor, assignment, exceptionalVertices_padAssignment,
      exceptionalVertices_partitionAssignment] using hB

/-- Removing matching edges incident with the distinguished clusters still
leaves the full source lower bound in both rows. -/
theorem CleanSourceWitness.away_degrees
    (hα : 0 < α) (hα1 : α ≤ 1 / 4) {Q : Certificate W} (F : CleanSourceWitness W Q)
    (hhost : hostN = 2 * q) (horder : orderThreshold α M ≤ q) :
    let E := edgesAwayFromDistinguished Q.claim67.M (padFinset (large W))
      (Sum.inl Q.A) (Sum.inl Q.B)
    (1 - 10 * (fourthRoot α : ℝ) ^ 2) * q ≤
      sourceDegree Q.claim67.M (padFinset (large W)) (rootDensity W F)
        W.clusterSize (Sum.inl Q.A) E ∧
    (1 - 10 * (fourthRoot α : ℝ) ^ 2) * q ≤
      sourceDegree Q.claim67.M (padFinset (large W)) (rootDensity W F)
        W.clusterSize (Sum.inl Q.B) E := by
  have rows := CleanSourceWitness.source_rows W F
  have hfloor := CleanSourceWitness.rowFloor_lower W hα hα1 F hhost horder
  constructor
  · apply sourceDegree_away_lower Q.claim67.M Q.claim67.isMatching
      (padFinset (large W)) (rootDensity W F) W.clusterSize
      ((1 - 10 * (fourthRoot α : ℝ) ^ 2) * q) (Sum.inl Q.A) (Sum.inl Q.A) (Sum.inl Q.B)
      (by positivity) rows.weightA_nonneg rows.weightA_le
    exact hfloor.le.trans rows.totalA
  · apply sourceDegree_away_lower Q.claim67.M Q.claim67.isMatching
      (padFinset (large W)) (rootDensity W F) W.clusterSize
      ((1 - 10 * (fourthRoot α : ℝ) ^ 2) * q) (Sum.inl Q.B) (Sum.inl Q.A) (Sum.inl Q.B)
      (by positivity) rows.weightB_nonneg rows.weightB_le
    exact hfloor.le.trans rows.totalB

end Erdos547b.ZhaoSourceDegreeFormRootRows

#print axioms Erdos547b.ZhaoSourceDegreeFormRootRows.exists_clean_source
#print axioms Erdos547b.ZhaoSourceDegreeFormRootRows.CleanSourceWitness.respects
#print axioms Erdos547b.ZhaoSourceDegreeFormRootRows.CleanSourceWitness.retained_degree
#print axioms Erdos547b.ZhaoSourceDegreeFormRootRows.CleanSourceWitness.rowFloor_lower
#print axioms Erdos547b.ZhaoSourceDegreeFormRootRows.CleanSourceWitness.source_rows
#print axioms Erdos547b.ZhaoSourceDegreeFormRootRows.CleanSourceWitness.away_degrees
