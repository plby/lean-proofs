/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceRootExclusions
import ErdosProblems.Erdos547b.SourceSaturatedPacking

/-!
# Actual closed chunks after one online root choice

The finite packing now uses the actual matching capacities and the same
chosen root as the graph embeddings. Closed chunks are realized in
permanently cleaned endpoints; one pending chunk keeps access at that root.
This is a residual transition, not yet the full ordered-forest induction.
-/

open scoped SimpleGraph BigOperators Classical
noncomputable section

namespace Erdos547b.ZhaoSourceResidualRootPacking

open Finset SimpleGraph
open Erdos547b.RegularPair
open Erdos547b.ZhaoStability Erdos547b.ZhaoDegreeForm Erdos547b.ZhaoEvenReducedPadding
open Erdos547b.ZhaoSection6Dichotomy
open Erdos547b.ZhaoLemma611Full Erdos547b.ZhaoRichClaim61Lemma611
open Erdos547b.ZhaoSourceParameterSchedule Erdos547b.ZhaoSourceDegreeFormRootRows
open Erdos547b.ZhaoSourceEmbeddingHost Erdos547b.ZhaoSourceActualChunkEmbedding
open Erdos547b.ZhaoSourceOnlineMatchingRoot Erdos547b.ZhaoSourceParentCleanup
open Erdos547b.ZhaoSourceRootReconnection Erdos547b.ZhaoSourceRootExclusions
open Erdos547b.ZhaoSourceDegreeFormBounds Erdos547b.ZhaoSourceFreshChunkBounds
open Erdos547b.ZhaoSourceSaturatedPacking Erdos547b.ZhaoLemma58GroupedSmallForest
open Erdos547b.ZhaoLemma58ThresholdResidualCapacity

/-- Edge-form interface for the square-root bad-target accounting. -/
theorem exists_residual_saturatedPacking_bad_edges
    {Bin Item : Type*} [DecidableEq Bin]
    (all used bad : Finset Bin) (items : List Item)
    (weight : Item → ℝ) (capacity : Bin → ℝ) (δ N slack consumed : ℝ)
    (hused : used ⊆ all) (hbad : bad ⊆ all \ used)
    (hcount : (bad.card : ℝ) ≤ 2 * δ * (all \ used).card)
    (hδ : 0 ≤ δ) (hN : 0 ≤ N) (hslack : 0 ≤ slack)
    (hcap : ∀ e ∈ all \ used, capacity e ≤ 2 * N)
    (hprocessed : (∑ e ∈ used, (capacity e - slack)) ≤ consumed)
    (hsmall : ∀ i ∈ items, 0 < weight i ∧ weight i ≤ slack)
    (hbudget : mass weight items + consumed ≤
      (∑ e ∈ all, capacity e) - (4 * δ * N + slack) * all.card) :
    Nonempty (SaturatedPacking
      (((all \ used) \ bad).filter (fun e => slack < capacity e)).toList
      items weight capacity slack) := by
  let D : Finset (Bin × Fin 2) := bad ×ˢ {0}
  have hD : D ⊆ (all \ used) ×ˢ Finset.univ := by
    intro p hp
    exact Finset.mem_product.mpr ⟨hbad (Finset.mem_product.mp hp).1, Finset.mem_univ _⟩
  have hDcount : (D.card : ℝ) ≤ δ * ((all \ used) ×ˢ (Finset.univ : Finset (Fin 2))).card := by
    simpa only [D, Finset.card_product, Finset.card_singleton, mul_one, Finset.card_univ,
      Fintype.card_fin, Nat.cast_mul, Nat.cast_ofNat, mul_assoc, mul_comm, mul_left_comm] using hcount
  have hproj : D.image Prod.fst = bad := Finset.product_image_fst (by simp)
  simpa only [hproj] using exists_residual_saturatedPacking all used D items weight capacity
    δ N slack consumed hused hD hDcount hδ hN hslack hcap hprocessed hsmall hbudget

/-- Literal original rooted branches, in the order of an allocated chunk. -/
def listForest {b : ℕ} (F : OrderedRootedForest b) (items : List (Fin b)) :
    OrderedRootedForest items.length where
  size i := F.size items[i.val]
  tree i := F.tree items[i.val]
  isTree i := F.isTree items[i.val]
  root i := F.root items[i.val]

theorem listForest_order {b : ℕ} (F : OrderedRootedForest b) (items : List (Fin b)) :
    ((listForest F items).order : ℝ) = mass (fun i => (F.size i : ℝ)) items := by
  unfold OrderedRootedForest.order listForest
  rw [← List.sum_ofFn, List.ofFn_getElem_eq_map]
  simp only [mass, Nat.cast_list_sum, List.map_map, Function.comp_def]

theorem SaturatedPacking.chunk_mem
    {Bin Item : Type*} {bins : List Bin} {items : List Item}
    {weight : Item → ℝ} {capacity : Bin → ℝ} {slack : ℝ}
    (P : SaturatedPacking bins items weight capacity slack)
    {p : Bin × List Item} (hp : p ∈ P.closed ++ P.pending.toList)
    {i : Item} (hi : i ∈ p.2) : i ∈ items := by
  have hflat : (P.closed ++ P.pending.toList).flatMap Prod.snd = items := by
    rw [List.flatMap_append]
    exact P.flatten
  rw [← hflat]
  exact List.mem_flatMap.mpr ⟨p, hp, hi⟩

theorem SaturatedPacking.chunks_nodup
    {Bin Item : Type*} {bins : List Bin} {items : List Item}
    {weight : Item → ℝ} {capacity : Bin → ℝ} {slack : ℝ}
    (P : SaturatedPacking bins items weight capacity slack) (hi : items.Nodup) :
    (∀ p ∈ P.closed ++ P.pending.toList, p.2.Nodup) ∧
      (P.closed ++ P.pending.toList).Pairwise (fun p p' => p.2.Disjoint p'.2) := by
  apply List.nodup_flatMap.mp
  rw [List.flatMap_append, P.flatten]
  exact hi

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G) (Q : Certificate W)

theorem partOneCapacity_le_twice_clusterSize
    (hα : 0 < α) (S : CleanSourceWitness W Q) (C : Index W)
    (hC : C = Q.A ∨ C = Q.B) (e : MatchingEdge Q.claim67.M) :
    partOneCapacity W Q S C e ≤ 2 * W.clusterSize := by
  have h0 := source_entry_le_one W Q S C hC (edgeVertex W Q e 0)
  have h1 := source_entry_le_one W Q S C hC (edgeVertex W Q e 1)
  have hg : (0 : ℝ) < gamma α := by exact_mod_cast (parameter_pos hα).2.2.2.2.2.2.1
  have he : (0 : ℝ) < epsilon α := by exact_mod_cast (parameter_pos hα).2.2.2.2.2.2.2
  apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg W.clusterSize)
  linarith only [h0, h1, hg, he]

/-- A closed packed chunk has an actual attached embedding in its
permanently cleaned matching pair. The prescribed outer root is unchanged. -/
theorem realize_closed_chunks
    (hα : 0 < α) (hα1 : α ≤ 1 / 4)
    (S : CleanSourceWitness W Q) (C : Index W) {b : ℕ} (F : OrderedRootedForest b)
    (items : List (Fin b)) (bins : List (MatchingEdge Q.claim67.M)) (slack : ℝ)
    (P : SaturatedPacking bins items (fun i => (F.size i : ℝ))
      (partOneCapacity W Q S C) slack)
    (z : Fin hostN) (haccess : ∀ e ∈ bins, PartOneAccess W Q S C e z)
    (hsmall : ∀ i ∈ items, F.size i ≤ freshBranchBound α W.clusterSize) :
    ∀ p ∈ P.closed, ∃ orient : Fin p.2.length → Fin 2 ≃ Fin 2,
      Nonempty (DynamicAttachedForestEmbedding (listForest F p.2) (embeddingHost W)
        (fun _ => z) orient (residualSide (edgeWhole W Q p.1) (deleted W Q p.1))) := by
  intro p hp
  have hpAll : p ∈ P.closed ++ P.pending.toList := List.mem_append_left _ hp
  apply haccess p.1 (P.bins_mem p hpAll) p.2.length (listForest F p.2) (deleted W Q p.1)
  · intro j
    exact hsmall _ (SaturatedPacking.chunk_mem P hpAll (List.getElem_mem j.isLt))
  · rw [listForest_order]
    exact P.fits p hpAll
  · exact deleted_subset W Q p.1
  · exact card_deleted_le W Q hα hα1 p.1

/-- Distinct actual matching pairs have disjoint whole endpoint supports. -/
theorem edgeWhole_cross_disjoint (e f : MatchingEdge Q.claim67.M) (hef : e ≠ f) (c d : Fin 2) :
    Disjoint (edgeWhole W Q e c) (edgeWhole W Q f d) := by
  have hne : edgeVertex W Q e c ≠ edgeVertex W Q f d := by
    intro h
    have hh : (e, c) = (f, d) :=
      orientedEndpoint_injective Q.claim67.M Q.claim67.isMatching (padFinset (large W)) h
    exact hef (congrArg Prod.fst hh)
  have h := clusterVertices_disjoint (padAssignment (assignment W)) hne
  simpa only [clusterVertices_padAssignment] using h

abbrev goodBins (S : CleanSourceWitness W Q) (C : Index W)
    (all used bad : Finset (MatchingEdge Q.claim67.M)) : List (MatchingEdge Q.claim67.M) :=
  (((all \ used) \ bad).filter fun e =>
    (freshBranchBound α W.clusterSize : ℝ) < partOneCapacity W Q S C e).toList

/-- The actual closed-chunk graph data, with the pending root kept fixed.
The pending chunk has access but is not part of the chosen embeddings. -/
structure RealizedPacking (S : CleanSourceWitness W Q) (C : Index W)
    {b : ℕ} (F : OrderedRootedForest b) (items : List (Fin b))
    (bins : List (MatchingEdge Q.claim67.M))
    (P : SaturatedPacking bins items (fun i => (F.size i : ℝ))
      (partOneCapacity W Q S C) (freshBranchBound α W.clusterSize))
    (z : Fin hostN) : Prop where
  closed : ∀ p ∈ P.closed, ∃ orient : Fin p.2.length → Fin 2 ≃ Fin 2,
    Nonempty (DynamicAttachedForestEmbedding (listForest F p.2) (embeddingHost W)
      (fun _ => z) orient (residualSide (edgeWhole W Q p.1) (deleted W Q p.1)))
  pending_access : ∀ p, P.pending = some p → PartOneAccess W Q S C p.1 z

/-- Allocate and realize the residual branches at an already chosen root.
The access premise is supplied by the concrete root-selection theorem in
the parent-reconnection corollary below. -/
theorem exists_realized_residual_of_access
    (hα : 0 < α) (hα1 : α ≤ 1 / 4)
    (S : CleanSourceWitness W Q) (C : Index W) (hC : C = Q.A ∨ C = Q.B)
    {b : ℕ} (F : OrderedRootedForest b) (items : List (Fin b))
    (all used bad : Finset (MatchingEdge Q.claim67.M)) (consumed : ℝ)
    (hused : used ⊆ all) (hbad : bad ⊆ all \ used)
    (hcount : (bad.card : ℝ) ≤ 2 * (rootTypicality α : ℝ) * (all \ used).card)
    (hprocessed : (∑ e ∈ used,
      (partOneCapacity W Q S C e - freshBranchBound α W.clusterSize)) ≤ consumed)
    (hsmall : ∀ i ∈ items, F.size i ≤ freshBranchBound α W.clusterSize)
    (hbudget : mass (fun i => (F.size i : ℝ)) items + consumed ≤
      (∑ e ∈ all, partOneCapacity W Q S C e) -
        (4 * (rootTypicality α : ℝ) * W.clusterSize + freshBranchBound α W.clusterSize) * all.card)
    (z : Fin hostN) (haccess : ∀ e ∈ (all \ used) \ bad, PartOneAccess W Q S C e z) :
    ∃ P : SaturatedPacking (goodBins W Q S C all used bad) items (fun i => (F.size i : ℝ))
        (partOneCapacity W Q S C) (freshBranchBound α W.clusterSize),
      RealizedPacking W Q S C F items (goodBins W Q S C all used bad) P z := by
  have hδ : (0 : ℝ) ≤ rootTypicality α := by
    exact_mod_cast (rootTypicality_margin hα hα1).1.le
  have hweights : ∀ i ∈ items, (0 : ℝ) < F.size i ∧
      (F.size i : ℝ) ≤ freshBranchBound α W.clusterSize := by
    intro i hi
    have hpos : 0 < F.size i := (F.root i).pos
    exact ⟨by exact_mod_cast hpos, by exact_mod_cast hsmall i hi⟩
  obtain ⟨P⟩ := exists_residual_saturatedPacking_bad_edges all used bad items
    (fun i => (F.size i : ℝ)) (partOneCapacity W Q S C) (rootTypicality α : ℝ)
    W.clusterSize (freshBranchBound α W.clusterSize) consumed hused hbad hcount hδ
    (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    (fun e _ => partOneCapacity_le_twice_clusterSize W Q hα S C hC e)
    hprocessed hweights hbudget
  have hbinAccess : ∀ e ∈ goodBins W Q S C all used bad, PartOneAccess W Q S C e z := by
    intro e he
    exact haccess e (Finset.mem_filter.mp (Finset.mem_toList.mp he)).1
  refine ⟨P, ⟨realize_closed_chunks W Q hα hα1 S C F items _ _ P z hbinAccess hsmall, ?_⟩⟩
  intro p hp
  exact hbinAccess p.1 (P.bins_mem p (List.mem_append_right _ (by simp [hp])))

/-- One source-faithful residual transition: choose the new root while
closing a fixed pending edge, then construct its actual saturated closed
chunks on distinct eligible unused edges. No graph-realization premise is
present; the scalar inputs are the live induction's consumed-mass budget. -/
theorem exists_realized_residual_after_parent
    (hα : 0 < α) (hα1 : α ≤ 1 / 4)
    (hhost : hostN = 2 * q) (horder : orderThreshold α M ≤ q)
    (S : CleanSourceWitness W Q)
    (parentEdge : MatchingEdge Q.claim67.M) (c s t : Fin 2) (v : Fin hostN)
    (hv : v ∈ edgeWhole W Q parentEdge c \ deleted W Q parentEdge c)
    (hadj : (padGraph (reduced W)).Adj (edgeVertex W Q parentEdge c)
      (Sum.inl (rootCluster W Q s)))
    (fixed : MatchingEdge Q.claim67.M)
    (hfixed : fixed ∈ edgesAwayFromDistinguished Q.claim67.M (padFinset (large W))
      (Sum.inl Q.A) (Sum.inl Q.B))
    (usedRoots : Finset (Fin hostN))
    (husedRoots : (usedRoots.card : ℝ) ≤ (epsilon α : ℝ) * W.clusterSize)
    {b : ℕ} (F : OrderedRootedForest b) (items : List (Fin b))
    (all used : Finset (MatchingEdge Q.claim67.M)) (consumed : ℝ)
    (hused : used ⊆ all)
    (hall : all ⊆ edgesAwayFromDistinguished Q.claim67.M
      (padFinset (large W)) (Sum.inl Q.A) (Sum.inl Q.B))
    (hprocessed : (∑ e ∈ used,
      (partOneCapacity W Q S (rootCluster W Q s) e - freshBranchBound α W.clusterSize)) ≤ consumed)
    (hsmall : ∀ i ∈ items, F.size i ≤ freshBranchBound α W.clusterSize)
    (hbudget : mass (fun i => (F.size i : ℝ)) items + consumed ≤
      (∑ e ∈ all, partOneCapacity W Q S (rootCluster W Q s) e) -
        (4 * (rootTypicality α : ℝ) * W.clusterSize + freshBranchBound α W.clusterSize) * all.card) :
    ∃ z ∈ reservoir W Q s, (embeddingHost W).Adj v z ∧ z ∉ usedRoots ∧
      PartOneAccess W Q S (rootCluster W Q s) fixed z ∧
      ((padGraph (reduced W)).Adj (Sum.inl (rootCluster W Q s)) (Sum.inl (rootCluster W Q t)) →
        ((densityCutoff α : ℝ) - (epsilon α : ℝ)) * (sourceQuota W : ℝ) ≤
          (#((reservoir W Q t).filter ((embeddingHost W).Adj z)) : ℝ)) ∧
      ∃ bad ⊆ all \ used,
        (bad.card : ℝ) ≤ 2 * (rootTypicality α : ℝ) * (all \ used).card ∧
        ∃ P : SaturatedPacking (goodBins W Q S (rootCluster W Q s) all used bad) items
            (fun i => (F.size i : ℝ)) (partOneCapacity W Q S (rootCluster W Q s))
            (freshBranchBound α W.clusterSize),
          RealizedPacking W Q S (rootCluster W Q s) F items
            (goodBins W Q S (rootCluster W Q s) all used bad) P z := by
  obtain ⟨z, hz, hzAdj, hzFresh, hfixedAccess, hrootDegree, bad, hb, hcount, hgood⟩ :=
    exists_root_with_fixed_edge_after_parent W Q hα hα1 hhost horder S parentEdge c s t v hv hadj
      fixed hfixed usedRoots husedRoots (all \ used) (Finset.sdiff_subset.trans hall)
  obtain ⟨P, hP⟩ := exists_realized_residual_of_access W Q hα hα1 S _ (rootCluster_cases W Q s)
    F items all used bad consumed hused hb hcount hprocessed hsmall hbudget z hgood
  exact ⟨z, hz, hzAdj, hzFresh, hfixedAccess, hrootDegree, bad, hb, hcount, P, hP⟩

end Erdos547b.ZhaoSourceResidualRootPacking

#print axioms Erdos547b.ZhaoSourceResidualRootPacking.exists_residual_saturatedPacking_bad_edges
#print axioms Erdos547b.ZhaoSourceResidualRootPacking.listForest_order
#print axioms Erdos547b.ZhaoSourceResidualRootPacking.SaturatedPacking.chunk_mem
#print axioms Erdos547b.ZhaoSourceResidualRootPacking.SaturatedPacking.chunks_nodup
#print axioms Erdos547b.ZhaoSourceResidualRootPacking.partOneCapacity_le_twice_clusterSize
#print axioms Erdos547b.ZhaoSourceResidualRootPacking.realize_closed_chunks
#print axioms Erdos547b.ZhaoSourceResidualRootPacking.edgeWhole_cross_disjoint
#print axioms Erdos547b.ZhaoSourceResidualRootPacking.exists_realized_residual_of_access
#print axioms Erdos547b.ZhaoSourceResidualRootPacking.exists_realized_residual_after_parent
