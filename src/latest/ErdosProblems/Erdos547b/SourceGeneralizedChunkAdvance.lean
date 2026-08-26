/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceGeneralizedChunkInitial
import ErdosProblems.Erdos547b.SourceChosenOwnerAdvance

/-!
# Actual mixed-kind chunk successor

A threshold chunk uses its fixed sequential plan. An Appendix chunk
derives the current batch budget from its reserved source mass, embeds that
batch in the literal live sets, and propagates the residual invariant.
Both preserve every earlier copy and already chosen orientation.
-/

open scoped SimpleGraph Classical
noncomputable section

namespace Erdos547b.ZhaoSourceGeneralizedChunk

open Finset SimpleGraph Erdos547b.RegularPair
open Erdos547b.ZhaoLemma611Full Erdos547b.ZhaoSourceDegreeFormRootRows
open Erdos547b.ZhaoSourceParameterSchedule Erdos547b.ZhaoSourceDegreeFormBounds
open Erdos547b.ZhaoSourceActualChunkEmbedding Erdos547b.ZhaoSourceEmbeddingHost
open Erdos547b.ZhaoSourceParentCleanup Erdos547b.ZhaoSourceFreshChunkBounds
open Erdos547b.ZhaoSourceFamilyCapacity Erdos547b.ZhaoSourceAppendixCapacityBounds
open Erdos547b.ZhaoSourceActualPendingPlan Erdos547b.ZhaoSourcePartThreeResidualNumerics
open Erdos547b.ZhaoSourcePendingPlacement Erdos547b.ZhaoSourceSortedBranchOrder
open Erdos547b.ZhaoSourcePendingOwnerInterval Erdos547b.ZhaoSourcePendingInterval
open Erdos547b.ZhaoSourceSaturatedPacking Erdos547b.ZhaoLemma58DynamicBatchAppend
open Erdos547b.ZhaoSourceResidualRootPacking
open Erdos547b.ZhaoLemma58ChosenOwnerBatches Erdos547b.ZhaoLemma58ThresholdResidualCapacity
open Erdos547b.ZhaoLemma58SelectedOrientationReindex Erdos547b.ZhaoSourceMixedRootRequirements
open Erdos547b.ZhaoSourceActualPartThreeStep Erdos547b.ZhaoClaim616SourceBridge.OrderedBranchForest

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G) (Q : Certificate W)
variable (S : CleanSourceWitness W Q) (C : Index W)
variable {b r : ℕ} (F : OrderedRootedForest b) (owner : Fin b → Fin r) (kind : FamilyKind)
variable (D : ChunkSource W Q S C F owner kind)

/-- Extend precisely the current owner after its concrete mixed-kind
root requirement has been met. No future-parent or embedding premise. -/
theorem ChunkSource.exists_advance
    (hα : 0 < α) (hα1 : α ≤ 1 / 4) (hhost : hostN = 2 * q)
    (horder : orderThreshold α M ≤ q) (hkind : kind.Valid α)
    {backend : D.Backend W Q S C F owner kind}
    (rootImage : Fin r → Fin hostN) (n : Fin r)
    (E : D.Prefix W Q S C F owner kind backend rootImage n.val)
    (z : Fin hostN) (hz : requirementGood W Q S C (D.requirement W Q S C F owner kind E) z) :
    ∃ E' : D.Prefix W Q S C F owner kind backend (Function.update rootImage n z) (n.val + 1),
      (∀ i (hi : i ∈ branchPrefix (ownerCutoff (listOwner owner D.items) n.val)),
        (D.chosen W Q S C F owner kind E').state.forestCopy.componentCopy i
            (branchPrefix_mono (ownerCutoff_mono (listOwner owner D.items) (Nat.le_succ n.val)) hi) =
          (D.chosen W Q S C F owner kind E).state.forestCopy.componentCopy i hi) ∧
      ∀ i ∈ branchPrefix (ownerCutoff (listOwner owner D.items) n.val),
        (D.chosen W Q S C F owner kind E').orient i =
          (D.chosen W Q S C F owner kind E).orient i := by
  cases kind with
  | threshold ratio =>
      obtain ⟨out, hcopy⟩ := exists_owner_extension (listForest F D.items) (embeddingHost W)
        (listOwner owner D.items) D.owner_mono backend.orient
        (residualSide (edgeWhole W Q D.edge) (deleted W Q D.edge)) n rootImage E z
        (fun i p P => backend.step i p P z hz)
      exact ⟨out, hcopy, fun _ _ => rfl⟩
  | appendix lambda =>
      let f := listForest F D.items
      let o := listOwner owner D.items
      let batch := ownerBatch Finset.univ o n
      let live := fun c => residualSide (edgeWhole W Q D.edge) (deleted W Q D.edge) c \ E.val.used c
      have hdisjoint : Disjoint (branchPrefix (ownerCutoff o n.val)) batch := by
        simpa only [branchPrefix_ownerCutoff o D.owner_mono] using
          ownerPrefix_disjoint_ownerBatch Finset.univ o n.val n.isLt
      have hfits : (f.order : ℝ) ≤ capacity W Q S C (.appendix lambda) D.edge := by
        rw [listForest_order]
        exact D.fits
      have hbudget := effective_batch_budget W Q hα hα1 hhost horder S C D.edge lambda f hfits
        (fun i => rootImage (o i)) E.val.orient (branchPrefix (ownerCutoff o n.val)) batch
        E.val.state hdisjoint
      have hlower (k : Fin batch.card) : 2 ≤ (selectedForest f batch).size k :=
        D.branch_valid _ (List.get_mem D.items (selectedEquiv batch k))
      have hsmall (k : Fin batch.card) : (selectedForest f batch).size k ≤
          freshBranchBound α W.clusterSize :=
        D.small _ (List.get_mem D.items (selectedEquiv batch k))
      obtain ⟨orient, Ebatch, hnew, _⟩ := exists_actual_partThree_step W Q hα hα1 hhost horder
        S C D.edge (selectedForest f batch) live lambda hkind.1 hkind.2 D.edge_valid
        (fun _ => Finset.sdiff_subset.trans Finset.sdiff_subset) E.property
        (by rw [selectedForest_order]; exact hbudget) hlower hsmall z hz
      obtain ⟨out, hused, hcopy, horient⟩ := exists_chosen_owner_advance f (embeddingHost W) o
        D.owner_mono (edgeWhole W Q D.edge)
        (residualSide (edgeWhole W Q D.edge) (deleted W Q D.edge))
        (fun _ => Finset.sdiff_subset) (edgeWhole_disjoint W Q D.edge)
        rootImage n E.val z orient Ebatch
      have hresidual (c : Fin 2) :
          residualSide (edgeWhole W Q D.edge) (deleted W Q D.edge) c \ out.used c =
            live c \ Ebatch.used c := by
        rw [hused c]
        exact (sdiff_sdiff _ _ _).symm
      have hout : D.LiveInvariant W Q S C F owner (.appendix lambda) out := by
        change ResidualInvariant _ _ _ _
          ((W.clusterSize : ℝ) - (residualSide (edgeWhole W Q D.edge) (deleted W Q D.edge) 0 \ out.used 0).card)
          ((W.clusterSize : ℝ) - (residualSide (edgeWhole W Q D.edge) (deleted W Q D.edge) 1 \ out.used 1).card)
        rw [hresidual 0, hresidual 1]
        exact hnew
      exact ⟨⟨out, hout⟩, hcopy, horient⟩

end Erdos547b.ZhaoSourceGeneralizedChunk

#print axioms Erdos547b.ZhaoSourceGeneralizedChunk.ChunkSource.exists_advance
