/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceFreshCapacityChunk
import ErdosProblems.Erdos547b.SourceSupportedChunkAssembly

/-!
# Constructing all closed current-owner chunks at the larger capacity

Every local copy is constructed from the actual classified source chunk.
The existing disjoint-edge assembly then pastes those concrete copies and
retains positive source support at their attachment endpoints.
-/

open scoped SimpleGraph Classical
noncomputable section

namespace Erdos547b.ZhaoSourceCapacityClosedPacking

open Finset SimpleGraph Erdos547b.RegularPair
open Erdos547b.ZhaoStability Erdos547b.ZhaoDegreeForm Erdos547b.ZhaoEvenReducedPadding
open Erdos547b.ZhaoLemma611Full Erdos547b.ZhaoRichClaim61Lemma611
open Erdos547b.ZhaoSourceDegreeFormRootRows Erdos547b.ZhaoSourceDegreeFormBounds
open Erdos547b.ZhaoSourceParameterSchedule Erdos547b.ZhaoSourceFreshChunkBounds
open Erdos547b.ZhaoSourceFamilyCapacity Erdos547b.ZhaoSourceGeneralizedChunk
open Erdos547b.ZhaoSourceMixedRootRequirements Erdos547b.ZhaoSourceSaturatedPacking
open Erdos547b.ZhaoSourceResidualRootPacking Erdos547b.ZhaoSourceSortedBranchOrder
open Erdos547b.ZhaoSourceOriginalBranchPlacement Erdos547b.ZhaoSourceSupportedChunkAssembly
open Erdos547b.ZhaoSourceEmbeddingHost Erdos547b.ZhaoSourceActualChunkEmbedding
open Erdos547b.ZhaoSourceParentCleanup Erdos547b.ZhaoLemma58ThresholdResidualCapacity

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G) (Q : Certificate W)
variable (S : CleanSourceWitness W Q) (C : Index W)
variable {b r : ℕ} (F : OrderedRootedForest b) (owner : Fin b → Fin r) (kind : FamilyKind)

theorem exists_supported_closed_packing
    (hα : 0 < α) (hα1 : α ≤ 1 / 4) (hhost : hostN = 2 * q)
    (horder : orderThreshold α M ≤ q) (hC : C = Q.A ∨ C = Q.B) (hkind : kind.Valid α)
    (rootImage : Fin r → Fin hostN) (n : Fin r)
    (bins : List (MatchingEdge Q.claim67.M)) (items : List (Fin b))
    (P : SaturatedPacking bins items (fun i => (F.size i : ℝ))
      (capacity W Q S C kind) (freshBranchBound α W.clusterSize))
    (hitems : items.Nodup) (howners : items.Pairwise (fun i j => owner i ≤ owner j))
    (hcurrent : ∀ i ∈ items, owner i = n)
    (hbranch : ∀ i ∈ items, kind.BranchValid F i)
    (hsmall : ∀ i, F.size i ≤ freshBranchBound α W.clusterSize)
    (haway : ∀ e ∈ bins, e ∈ edgesAwayFromDistinguished Q.claim67.M
      (padFinset (large W)) (Sum.inl Q.A) (Sum.inl Q.B))
    (hedge : ∀ e ∈ bins, edgeValid W Q S C kind e)
    (hz : ∀ e ∈ bins, requirementGood W Q S C (initialRequirement W Q kind e) (rootImage n)) :
    ∃ D : BranchPlacement F (embeddingHost W) (P.closed.flatMap Prod.snd).toFinset
        (fun i => rootImage (owner i))
        (fun e => residualSide (edgeWhole W Q e) (deleted W Q e)),
      (∀ i, D.edge i ∈ (P.closed.map Prod.fst).toFinset) ∧
      ∀ i, 0 < rootDensity W S (Sum.inl C) (edgeVertex W Q (D.edge i) (D.orient i 0)) := by
  apply exists_supported_chunk_assembly W Q S C F owner rootImage P.closed
  · have hn := P.bins_nodup
    rw [List.map_append] at hn
    exact (List.nodup_append.mp hn).1
  · intro p hp
    have hp' := List.mem_append_left P.pending.toList hp
    have hsub := packing_chunk_sublist P p hp'
    have hbin := P.bins_mem p hp'
    let D : ChunkSource W Q S C F owner kind := {
      edge := p.1
      edge_away := haway p.1 hbin
      edge_valid := hedge p.1 hbin
      items := p.2
      nodup := hitems.sublist hsub
      owner_mono := monotone_packing_chunk_owner P owner howners p hp'
      fits := P.fits p hp'
      branch_valid := fun i hi => hbranch i (hsub.subset hi)
      small := fun i _ => hsmall i }
    have hclosed := D.exists_fresh_closed W Q S C F owner kind hα hα1 hhost horder hC hkind
      rootImage n (fun i hi => hcurrent i (hsub.subset hi)) (rootImage n) (hz p.1 hbin)
    rw [Function.update_eq_self n rootImage] at hclosed
    exact hclosed

end Erdos547b.ZhaoSourceCapacityClosedPacking

#print axioms Erdos547b.ZhaoSourceCapacityClosedPacking.exists_supported_closed_packing
