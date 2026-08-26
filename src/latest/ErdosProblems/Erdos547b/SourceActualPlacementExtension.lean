/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceBranchPlacementExtension

/-!
# Extending the actual source placement and its consumed-mass invariant

Only newly closed matching edges enter the used-edge set. The exact
original branch counts identify their saturation mass with actual host
vertices. The joined state preserves every earlier branch image.
-/

open scoped SimpleGraph BigOperators Classical
noncomputable section

namespace Erdos547b.ZhaoSourceActualPlacementExtension

open Finset SimpleGraph
open Erdos547b.RegularPair
open Erdos547b.ZhaoSourceSaturatedPacking Erdos547b.ZhaoSourceResidualRootPacking
open Erdos547b.ZhaoSourceOriginalBranchPlacement

private theorem sum_map_mono {I : Type*} (l : List I) (f g : I → ℝ)
    (h : ∀ i ∈ l, f i ≤ g i) : (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons i l ih =>
    simp only [List.map_cons, List.sum_cons]
    exact add_le_add (h i List.mem_cons_self) (ih (fun j hj => h j (List.mem_cons_of_mem _ hj)))

private theorem mass_flatMap {Bin Item : Type*} (chunks : List (Bin × List Item)) (w : Item → ℝ) :
    (chunks.map (fun p => mass w p.2)).sum = mass w (chunks.flatMap Prod.snd) := by
  induction chunks with
  | nil => simp [mass]
  | cons p chunks ih =>
    simpa only [mass, List.map_cons, List.sum_cons, List.flatMap_cons, List.map_append,
      List.sum_append] using congrArg (fun x => mass w p.2 + x) ih

/-- Closed saturation pays for precisely the closed edge set. -/
theorem closed_saturation_mass
    {Bin Item : Type*} [DecidableEq Bin] {bins : List Bin} {items : List Item}
    {w : Item → ℝ} {cap : Bin → ℝ} {slack : ℝ}
    (P : SaturatedPacking bins items w cap slack) :
    (∑ e ∈ (P.closed.map Prod.fst).toFinset, (cap e - slack)) ≤ mass w (P.closed.flatMap Prod.snd) := by
  have hnd : (P.closed.map Prod.fst).Nodup := by
    have h := P.bins_nodup
    rw [List.map_append] at h
    exact (List.nodup_append.mp h).1
  rw [List.sum_toFinset (fun e => cap e - slack) hnd, List.map_map]
  exact (sum_map_mono P.closed _ _ (fun p hp => (P.saturated p hp).le)).trans_eq (mass_flatMap P.closed w)

theorem closed_mass_eq_sum
    {Bin Item : Type*} [DecidableEq Item] {bins : List Bin} {items : List Item}
    {w : Item → ℝ} {cap : Bin → ℝ} {slack : ℝ}
    (P : SaturatedPacking bins items w cap slack) (hi : items.Nodup) :
    mass w (P.closed.flatMap Prod.snd) = ∑ i ∈ (P.closed.flatMap Prod.snd).toFinset, w i := by
  have hnd : (P.closed.flatMap Prod.snd).Nodup := by
    rw [← P.flatten] at hi
    exact (List.nodup_append.mp hi).1
  exact (List.sum_toFinset w hnd).symm

open Erdos547b.ZhaoStability Erdos547b.ZhaoDegreeForm Erdos547b.ZhaoEvenReducedPadding
open Erdos547b.ZhaoLemma611Full Erdos547b.ZhaoSourceParameterSchedule
open Erdos547b.ZhaoSourceDegreeFormRootRows Erdos547b.ZhaoSourceEmbeddingHost
open Erdos547b.ZhaoSourceActualChunkEmbedding Erdos547b.ZhaoSourceOnlineMatchingRoot
open Erdos547b.ZhaoSourceParentCleanup Erdos547b.ZhaoSourceFreshChunkBounds
open Erdos547b.ZhaoSourceClosedChunkAssembly Erdos547b.ZhaoLemma58ThresholdResidualCapacity

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G) (Q : Certificate W)
variable (S : CleanSourceWitness W Q) (C : Index W)
variable {b : ℕ} (F : OrderedRootedForest b) (items : List (Fin b))
variable (all used bad : Finset (MatchingEdge Q.claim67.M))
variable (P : SaturatedPacking (goodBins W Q S C all used bad) items (fun i => (F.size i : ℝ))
  (partOneCapacity W Q S C) (freshBranchBound α W.clusterSize))

abbrev newSelected := closedSelected W Q S C F items (goodBins W Q S C all used bad) P
abbrev newEdges : Finset (MatchingEdge Q.claim67.M) := (P.closed.map Prod.fst).toFinset
abbrev cleanEndpoint (e : MatchingEdge Q.claim67.M) := residualSide (edgeWhole W Q e) (deleted W Q e)

theorem newEdges_subset_unused : newEdges W Q S C F items all used bad P ⊆ all \ used := by
  intro e he
  obtain ⟨p, hp, hpe⟩ := List.mem_map.mp (List.mem_toFinset.mp he)
  have hbin := P.bins_mem p (List.mem_append_left _ hp)
  have hgood := (Finset.mem_filter.mp (Finset.mem_toList.mp hbin)).1
  rw [← hpe]
  exact (Finset.mem_sdiff.mp hgood).1

theorem newSelected_subset_items : newSelected W Q S C F items all used bad P ⊆ items.toFinset := by
  intro i hi
  obtain ⟨p, hp, hip⟩ := List.mem_flatMap.mp (List.mem_toFinset.mp hi)
  exact List.mem_toFinset.mpr (Erdos547b.ZhaoSourceResidualRootPacking.SaturatedPacking.chunk_mem
    P (List.mem_append_left _ hp) hip)

/-- Instantiate the image-preserving extension with actual unused
matching edges and update the saturated consumed-mass invariant. -/
theorem exists_extended_source_placement
    (parent : Fin b → Fin hostN) (oldSelected : Finset (Fin b))
    (old : BranchPlacement F (embeddingHost W) oldSelected parent (cleanEndpoint W Q))
    (holdEdges : ∀ i, old.edge i ∈ used)
    (hprocessed : (∑ e ∈ used, (partOneCapacity W Q S C e - freshBranchBound α W.clusterSize)) ≤
      (old.used.card : ℝ))
    (hitems : items.Nodup) (hfresh : ∀ i ∈ items, i ∉ oldSelected)
    (z : Fin hostN) (hparent : ∀ i ∈ newSelected W Q S C F items all used bad P, parent i = z)
    (R : RealizedPacking W Q S C F items (goodBins W Q S C all used bad) P z) :
    ∃ D : BranchPlacement F (embeddingHost W)
        (oldSelected ∪ newSelected W Q S C F items all used bad P) parent (cleanEndpoint W Q),
      (∀ i hi, D.forestCopy.componentCopy i (Finset.mem_union_left _ hi) = old.forestCopy.componentCopy i hi) ∧
      (∀ i, D.edge i ∈ used ∪ newEdges W Q S C F items all used bad P) ∧
      D.used.card = old.used.card + ∑ i ∈ newSelected W Q S C F items all used bad P, F.size i ∧
      (∑ e ∈ used ∪ newEdges W Q S C F items all used bad P,
        (partOneCapacity W Q S C e - freshBranchBound α W.clusterSize)) ≤ (D.used.card : ℝ) := by
  obtain ⟨A⟩ := exists_closedAssembly W Q S C F items _ P z R
  obtain ⟨fresh, hfreshEdges⟩ := exists_original_closed_placement_with_closed_edges W Q S C F items _ P z A
  let next := fresh.reparent parent hparent
  have hdisjoint : Disjoint oldSelected (newSelected W Q S C F items all used bad P) := by
    rw [Finset.disjoint_left]
    intro i hi hnew
    exact hfresh i (List.mem_toFinset.mp (newSelected_subset_items W Q S C F items all used bad P hnew)) hi
  have hsides : ∀ i : {i // i ∈ oldSelected},
      ∀ j : {j // j ∈ newSelected W Q S C F items all used bad P}, ∀ c d,
        Disjoint (cleanEndpoint W Q (old.edge i) c) (cleanEndpoint W Q (next.edge j) d) := by
    intro i j c d
    have hnew : next.edge j ∈ newEdges W Q S C F items all used bad P := hfreshEdges j
    have hnot := (Finset.mem_sdiff.mp (newEdges_subset_unused W Q S C F items all used bad P hnew)).2
    have hne : old.edge i ≠ next.edge j := fun h => hnot (h ▸ holdEdges i)
    exact (edgeWhole_cross_disjoint W Q _ _ hne c d).mono Finset.sdiff_subset Finset.sdiff_subset
  let D := old.append next hsides
  have hcard : D.used.card = old.used.card + ∑ i ∈ newSelected W Q S C F items all used bad P, F.size i := by
    rw [BranchPlacement.card_used, Finset.sum_union hdisjoint, BranchPlacement.card_used]
  refine ⟨D, ?_, ?_, hcard, ?_⟩
  · intro i hi
    exact old.append_copy_left next hsides i hi
  · intro i
    by_cases hi : i.1 ∈ oldSelected
    · rw [show D.edge i = old.edge ⟨i.1, hi⟩ from old.append_edge_left next hsides i.1 hi]
      exact Finset.mem_union_left _ (holdEdges _)
    · have hin := (Finset.mem_union.mp i.2).resolve_left hi
      rw [show D.edge i = next.edge ⟨i.1, hin⟩ from old.append_edge_right next hsides hdisjoint i.1 hin]
      exact Finset.mem_union_right _ (hfreshEdges _)
  · have hedgeDisj : Disjoint used (newEdges W Q S C F items all used bad P) := by
      rw [Finset.disjoint_left]
      intro e he hn
      exact (Finset.mem_sdiff.mp (newEdges_subset_unused W Q S C F items all used bad P hn)).2 he
    have hnewMass := closed_saturation_mass P
    rw [closed_mass_eq_sum P hitems] at hnewMass
    rw [Finset.sum_union hedgeDisj, hcard, Nat.cast_add, Nat.cast_sum]
    exact add_le_add hprocessed hnewMass

end Erdos547b.ZhaoSourceActualPlacementExtension

#print axioms Erdos547b.ZhaoSourceActualPlacementExtension.closed_saturation_mass
#print axioms Erdos547b.ZhaoSourceActualPlacementExtension.closed_mass_eq_sum
#print axioms Erdos547b.ZhaoSourceActualPlacementExtension.newEdges_subset_unused
#print axioms Erdos547b.ZhaoSourceActualPlacementExtension.newSelected_subset_items
#print axioms Erdos547b.ZhaoSourceActualPlacementExtension.exists_extended_source_placement
