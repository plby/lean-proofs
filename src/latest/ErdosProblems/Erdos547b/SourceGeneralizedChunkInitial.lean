/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceGeneralizedChunk

/-!
# Initial actual prefixes and source support for both chunk kinds

The Appendix prefix starts with no graph images; its initial trichotomy
is paid by the permanent deletion bound. Every subsequently stored root
endpoint is supported by a positive source entry in either concrete kind.
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
open Erdos547b.ZhaoSourceResidualRootPacking Erdos547b.ZhaoSourceSaturatedPacking
open Erdos547b.ZhaoSourceOriginalBranchPlacement Erdos547b.ZhaoLemma58DynamicBatchAppend
open Erdos547b.ZhaoLemma58ChosenOwnerBatches Erdos547b.ZhaoLemma58ThresholdResidualCapacity

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G) (Q : Certificate W)
variable (S : CleanSourceWitness W Q) (C : Index W)
variable {b r : ℕ} (F : OrderedRootedForest b) (owner : Fin b → Fin r) (kind : FamilyKind)
variable (D : ChunkSource W Q S C F owner kind)

/-- No source branch has been copied at stage zero. The arbitrary values
of the root map are therefore not hypotheses about future chosen roots. -/
theorem ChunkSource.exists_initial_prefix
    (hα : 0 < α) (hα1 : α ≤ 1 / 4) (hhost : hostN = 2 * q)
    (horder : orderThreshold α M ≤ q)
    (backend : D.Backend W Q S C F owner kind) (rootImage : Fin r → Fin hostN) :
    Nonempty (D.Prefix W Q S C F owner kind backend rootImage 0) := by
  cases kind with
  | threshold ratio =>
      change Nonempty (PartialDynamicAttachedForestEmbedding (listForest F D.items) (embeddingHost W)
        (fun i => rootImage (listOwner owner D.items i)) backend.orient
        (residualSide (edgeWhole W Q D.edge) (deleted W Q D.edge))
        (branchPrefix (ownerCutoff (listOwner owner D.items) 0)))
      rw [ownerCutoff_zero, branchPrefix_zero]
      exact ⟨emptyPartial _ _ _ _ _⟩
  | appendix lambda =>
      let initial : D.ChosenPrefix W Q S C F owner (.appendix lambda) rootImage 0 := {
        orient := fun _ => Equiv.refl _
        state := by
          simpa only [ownerCutoff_zero, branchPrefix_zero] using
            emptyPartial (listForest F D.items) (embeddingHost W)
              (fun i => rootImage (listOwner owner D.items i)) (fun _ => Equiv.refl _)
              (residualSide (edgeWhole W Q D.edge) (deleted W Q D.edge))
      }
      refine ⟨⟨initial, ?_⟩⟩
      have hused (c : Fin 2) : initial.used c = ∅ := by
        apply Finset.card_eq_zero.mp
        change (initial.state.used c).card = 0
        rw [initial.state.card_used]
        simp only [ownerCutoff_zero, branchPrefix_zero, Finset.sum_empty]
      change ResidualInvariant _ _ _ _
        ((W.clusterSize : ℝ) - (residualSide (edgeWhole W Q D.edge) (deleted W Q D.edge) 0 \ initial.used 0).card)
        ((W.clusterSize : ℝ) - (residualSide (edgeWhole W Q D.edge) (deleted W Q D.edge) 1 \ initial.used 1).card)
      rw [hused 0, hused 1, Finset.sdiff_empty, Finset.sdiff_empty]
      have hcount (c : Fin 2) :
          ((W.clusterSize : ℝ) - (residualSide (edgeWhole W Q D.edge) (deleted W Q D.edge) c).card) =
            (deleted W Q D.edge c).card := by
        have hc : ((residualSide (edgeWhole W Q D.edge) (deleted W Q D.edge) c).card : ℝ) +
            (deleted W Q D.edge c).card = W.clusterSize := by
          exact_mod_cast (Finset.card_sdiff_add_card_eq_card (deleted_subset W Q D.edge c)).trans
            (edgeWhole_card W Q D.edge c)
        linarith only [hc]
      rw [hcount 0, hcount 1]
      exact ResidualInvariant.of_cleanup _ _ _ _ _ _ (Nat.cast_nonneg _) (Nat.cast_nonneg _)
        (card_deleted_le_three_error W Q hα hα1 hhost horder D.edge 0)
        (card_deleted_le_three_error W Q hα hα1 hhost horder D.edge 1)

theorem ChunkSource.chosen_root_positive (hα : 0 < α) (hkind : kind.Valid α)
    {backend : D.Backend W Q S C F owner kind} {rootImage : Fin r → Fin hostN} {n : ℕ}
    (E : D.Prefix W Q S C F owner kind backend rootImage n) (i : Fin D.items.length) :
    0 < rootDensity W S (Sum.inl C)
      (edgeVertex W Q D.edge ((D.chosen W Q S C F owner kind E).orient i 0)) := by
  cases kind with
  | threshold _ => exact backend.root_positive i
  | appendix lambda =>
      have hd : (0 : ℝ) < densityCutoff α := by exact_mod_cast (parameter_pos hα).2.2.2.2.2.1
      exact (hd.trans_le hkind.1).trans_le (D.edge_valid (E.val.orient i 0)).1

theorem ChunkSource.placement_edge
    {backend : D.Backend W Q S C F owner kind} {rootImage : Fin r → Fin hostN} {n : ℕ}
    (E : D.Prefix W Q S C F owner kind backend rootImage n)
    (i : {i // i ∈ prefixSelected D.items (ownerCutoff (listOwner owner D.items) n)}) :
    (D.placement W Q S C F owner kind E).edge i = D.edge := rfl

theorem ChunkSource.placement_root_positive (hα : 0 < α) (hkind : kind.Valid α)
    {backend : D.Backend W Q S C F owner kind} {rootImage : Fin r → Fin hostN} {n : ℕ}
    (E : D.Prefix W Q S C F owner kind backend rootImage n)
    (i : {i // i ∈ prefixSelected D.items (ownerCutoff (listOwner owner D.items) n)}) :
    0 < rootDensity W S (Sum.inl C)
      (edgeVertex W Q ((D.placement W Q S C F owner kind E).edge i)
        ((D.placement W Q S C F owner kind E).orient i 0)) :=
  D.chosen_root_positive W Q S C F owner kind hα hkind E
    (position D.items i.1 (prefixSelected_mem_items i.2))

end Erdos547b.ZhaoSourceGeneralizedChunk

#print axioms Erdos547b.ZhaoSourceGeneralizedChunk.ChunkSource.exists_initial_prefix
#print axioms Erdos547b.ZhaoSourceGeneralizedChunk.ChunkSource.chosen_root_positive
#print axioms Erdos547b.ZhaoSourceGeneralizedChunk.ChunkSource.placement_root_positive
