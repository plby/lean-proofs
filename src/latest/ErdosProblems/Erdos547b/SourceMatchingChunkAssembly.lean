/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceMatchingChunkClosure

/-!
# Closed-chunk assembly retaining positive source support

Paste the actual original-index placements on distinct matching edges.
Both the assigned edge set and the positive root-endpoint source density
survive the assembly. The source-specialized constructor builds every
local placement from the checked fixed-plan embedding theorem.
-/

open scoped SimpleGraph Classical
noncomputable section

namespace Erdos547b.ZhaoSourceMatchingChunkAssembly

open Finset SimpleGraph Erdos547b.RegularPair
open Erdos547b.ZhaoSourceOriginalBranchPlacement Erdos547b.ZhaoSourceMatchingActiveChunk
open Erdos547b.ZhaoSourceMatchingFamilyState Erdos547b.ZhaoSourceSortedBranchOrder
open Erdos547b.ZhaoSourceSaturatedPacking Erdos547b.ZhaoSourceResidualRootPacking
open Erdos547b.ZhaoStability Erdos547b.ZhaoDegreeForm Erdos547b.ZhaoEvenReducedPadding
open Erdos547b.ZhaoLemma611Full Erdos547b.ZhaoRichClaim61Lemma611
open Erdos547b.ZhaoSourceDegreeFormRootRows Erdos547b.ZhaoSourceDegreeFormBounds
open Erdos547b.ZhaoSourceEmbeddingHost Erdos547b.ZhaoSourceMatchingRootSelection
open Erdos547b.ZhaoSourceMatchingParentCleanup Erdos547b.ZhaoSourceMatchingGeometry
open Erdos547b.ZhaoSourceMatchingPendingPlan
open Erdos547b.ZhaoSourceFreshChunkBounds Erdos547b.ZhaoLemma58ThresholdResidualCapacity

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G) (Q : Certificate W)
variable (S : CleanSourceWitness W Q) (P : (padGraph (reduced W)).Subgraph) (C : Index W)
variable {b r : ℕ} (F : OrderedRootedForest b) (owner : Fin b → Fin r)
variable (rootImage : Fin r → Fin hostN)

/-- Assemble independently constructed chunks; the support property is
inherited from the same actual copies, not supplied after choosing them. -/
theorem exists_supported_chunk_assembly (hP : P.IsMatching)
    (chunks : List (MatchingEdge P × List (Fin b)))
    (hnd : (chunks.map Prod.fst).Nodup)
    (hlocal : ∀ p ∈ chunks,
      ∃ E : BranchPlacement F (embeddingHost W) p.2.toFinset
          (fun i => rootImage (owner i))
          (fun e => residualSide (pairWhole W P e) (deleted W Q P e)),
        (∀ i, E.edge i = p.1) ∧
        ∀ i, 0 < rootDensity W S (Sum.inl C)
          (pairVertex W P (E.edge i) (E.orient i 0))) :
    ∃ D : BranchPlacement F (embeddingHost W) (chunks.flatMap Prod.snd).toFinset
        (fun i => rootImage (owner i))
        (fun e => residualSide (pairWhole W P e) (deleted W Q P e)),
      (∀ i, D.edge i ∈ (chunks.map Prod.fst).toFinset) ∧
      ∀ i, 0 < rootDensity W S (Sum.inl C)
        (pairVertex W P (D.edge i) (D.orient i 0)) := by
  induction chunks with
  | nil =>
    refine ⟨BranchPlacement.empty F (embeddingHost W) (fun i => rootImage (owner i)) _, ?_, ?_⟩
    · intro i
      exact (Finset.notMem_empty _ i.2).elim
    · intro i
      exact (Finset.notMem_empty _ i.2).elim
  | cons p chunks ih =>
    have hn := List.nodup_cons.mp hnd
    obtain ⟨head, hhead, hheadpos⟩ := hlocal p List.mem_cons_self
    obtain ⟨tail, htail, htailpos⟩ := ih hn.2
      (fun a ha => hlocal a (List.mem_cons_of_mem _ ha))
    have hsupport : ∀ i : {i // i ∈ p.2.toFinset},
        ∀ j : {j // j ∈ (chunks.flatMap Prod.snd).toFinset}, ∀ c d,
          Disjoint (residualSide (pairWhole W P (head.edge i)) (deleted W Q P (head.edge i)) c)
            (residualSide (pairWhole W P (tail.edge j)) (deleted W Q P (tail.edge j)) d) := by
      intro i j c d
      have hne : head.edge i ≠ tail.edge j := by
        rw [hhead i]
        intro heq
        exact hn.1 (heq.symm ▸ List.mem_toFinset.mp (htail j))
      exact (pairWhole_cross_disjoint W P hP _ _ hne c d).mono
        Finset.sdiff_subset Finset.sdiff_subset
    let joined := head.append tail hsupport
    have hdomain : p.2.toFinset ∪ (chunks.flatMap Prod.snd).toFinset =
        ((p :: chunks).flatMap Prod.snd).toFinset := by
      simp only [List.flatMap_cons, List.toFinset_append]
    let D := castPlacement W Q P F owner (rootImage := rootImage) hdomain joined
    refine ⟨D, ?_, ?_⟩
    · intro i
      have hi : i.1 ∈ p.2.toFinset ∪ (chunks.flatMap Prod.snd).toFinset :=
        hdomain.symm ▸ i.2
      by_cases hp : i.1 ∈ p.2.toFinset
      · have he : p.1 ∈ ((p :: chunks).map Prod.fst).toFinset := by simp
        simpa only [D, castPlacement, joined, BranchPlacement.append, dif_pos hp,
          hhead] using he
      · have ht := (Finset.mem_union.mp hi).resolve_left hp
        have he := htail ⟨i.1, ht⟩
        have he' : tail.edge ⟨i.1, ht⟩ ∈ ((p :: chunks).map Prod.fst).toFinset := by
          exact List.mem_toFinset.mpr (List.mem_cons_of_mem _ (List.mem_toFinset.mp he))
        simpa only [D, castPlacement, joined, BranchPlacement.append, dif_neg hp] using he'
    · intro i
      have hi : i.1 ∈ p.2.toFinset ∪ (chunks.flatMap Prod.snd).toFinset :=
        hdomain.symm ▸ i.2
      by_cases hp : i.1 ∈ p.2.toFinset
      · simpa only [D, castPlacement, joined, BranchPlacement.append, dif_pos hp] using
          hheadpos ⟨i.1, hp⟩
      · have ht := (Finset.mem_union.mp hi).resolve_left hp
        simpa only [D, castPlacement, joined, BranchPlacement.append, dif_neg hp] using
          htailpos ⟨i.1, ht⟩

/-- Realize every closed chunk of the source packing with its support
certificate, then paste them into one original-index placement. -/
theorem exists_supported_closed_packing (hP : P.IsMatching)
    (hα : 0 < α) (hα1 : α ≤ 1 / 4)
    (hhost : hostN = 2 * q) (horder : orderThreshold α M ≤ q)
    (hC : C = Q.A ∨ C = Q.B)
    (bins : List (MatchingEdge P)) (items : List (Fin b))
    (packing : SaturatedPacking bins items (fun i => (F.size i : ℝ))
      (capacity W Q P S C) (freshBranchBound α W.clusterSize))
    (hitems : items.Nodup) (howners : items.Pairwise (fun i j => owner i ≤ owner j))
    (hsmall : ∀ i, F.size i ≤ freshBranchBound α W.clusterSize)
    (haway : ∀ e ∈ bins, e ∈ edgesAwayFromDistinguished P
      (padFinset (large W)) (Sum.inl Q.A) (Sum.inl Q.B))
    (z : Fin hostN) (hz : ∀ e ∈ bins, EligibleRoot W Q S P C e z)
    (hparent : ∀ i ∈ items, rootImage (owner i) = z) :
    ∃ D : BranchPlacement F (embeddingHost W) (packing.closed.flatMap Prod.snd).toFinset
        (fun i => rootImage (owner i))
        (fun e => residualSide (pairWhole W P e) (deleted W Q P e)),
      (∀ i, D.edge i ∈ (packing.closed.map Prod.fst).toFinset) ∧
      ∀ i, 0 < rootDensity W S (Sum.inl C)
        (pairVertex W P (D.edge i) (D.orient i 0)) := by
  apply exists_supported_chunk_assembly W Q S P C F owner rootImage hP packing.closed
  · have hn := packing.bins_nodup
    rw [List.map_append] at hn
    exact (List.nodup_append.mp hn).1
  · intro p hp
    have hp' := List.mem_append_left packing.pending.toList hp
    have hsub := packing_chunk_sublist packing p hp'
    have hbin := packing.bins_mem p hp'
    exact exists_fresh_closed_placement W Q S P C F owner hα hα1 hhost horder hC
      p.1 (haway p.1 hbin) p.2 (hitems.sublist hsub)
      (monotone_packing_chunk_owner packing owner howners p hp') hsmall (packing.fits p hp')
      rootImage z (hz p.1 hbin) (fun i hi => hparent i (hsub.subset hi))

end Erdos547b.ZhaoSourceMatchingChunkAssembly

#print axioms Erdos547b.ZhaoSourceMatchingChunkAssembly.exists_supported_chunk_assembly
#print axioms Erdos547b.ZhaoSourceMatchingChunkAssembly.exists_supported_closed_packing
