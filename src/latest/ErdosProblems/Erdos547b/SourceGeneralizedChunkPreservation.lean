/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceGeneralizedChunkAdvance

/-!
# Skipping absent owners and preserving original-index chunk images

An unrelated root needs no eligibility test toward this chunk. Advancing
its empty owner interval leaves the exact live sets unchanged. For either
kind, prefix-copy and orientation preservation descend to original indices.
-/

open scoped SimpleGraph Classical
noncomputable section

namespace Erdos547b.ZhaoSourceGeneralizedChunk

open Finset SimpleGraph Erdos547b.RegularPair
open Erdos547b.ZhaoLemma611Full Erdos547b.ZhaoSourceDegreeFormRootRows
open Erdos547b.ZhaoSourceEmbeddingHost Erdos547b.ZhaoSourceActualChunkEmbedding
open Erdos547b.ZhaoSourceParentCleanup Erdos547b.ZhaoSourceFamilyCapacity
open Erdos547b.ZhaoSourcePendingPlacement Erdos547b.ZhaoSourceSortedBranchOrder
open Erdos547b.ZhaoSourcePendingOwnerInterval Erdos547b.ZhaoSourcePendingInterval
open Erdos547b.ZhaoSourceResidualRootPacking Erdos547b.ZhaoSourceActiveChunk
open Erdos547b.ZhaoLemma58DynamicBatchAppend Erdos547b.ZhaoLemma58ChosenOwnerBatches
open Erdos547b.ZhaoLemma58ThresholdResidualCapacity Erdos547b.ZhaoLemma58OnlineOwnerReparent
open Erdos547b.ZhaoSourcePartThreeResidualNumerics

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G) (Q : Certificate W)
variable (S : CleanSourceWitness W Q) (C : Index W)
variable {b r : ℕ} (F : OrderedRootedForest b) (owner : Fin b → Fin r) (kind : FamilyKind)
variable (D : ChunkSource W Q S C F owner kind)

theorem ChunkSource.exists_skip
    {backend : D.Backend W Q S C F owner kind}
    (rootImage : Fin r → Fin hostN) (n : Fin r)
    (E : D.Prefix W Q S C F owner kind backend rootImage n.val) (z : Fin hostN)
    (habsent : ∀ i ∈ D.items, owner i ≠ n) :
    ∃ E' : D.Prefix W Q S C F owner kind backend (Function.update rootImage n z) (n.val + 1),
      (∀ i (hi : i ∈ branchPrefix (ownerCutoff (listOwner owner D.items) n.val)),
        (D.chosen W Q S C F owner kind E').state.forestCopy.componentCopy i
            (branchPrefix_mono (ownerCutoff_mono (listOwner owner D.items) (Nat.le_succ n.val)) hi) =
          (D.chosen W Q S C F owner kind E).state.forestCopy.componentCopy i hi) ∧
      ∀ i, (D.chosen W Q S C F owner kind E').orient i =
        (D.chosen W Q S C F owner kind E).orient i := by
  let p := fun i => rootImage (listOwner owner D.items i)
  let p' := fun i => Function.update rootImage n z (listOwner owner D.items i)
  let available := residualSide (edgeWhole W Q D.edge) (deleted W Q D.edge)
  let s : Finset (Fin D.items.length) := branchPrefix (ownerCutoff (listOwner owner D.items) n.val)
  have hagrees : ∀ i ∈ s, p' i = p i := by
    intro i _
    exact Function.update_of_ne (habsent _ (List.get_mem D.items i)) z rootImage
  have hcut := ownerCutoff_succ_eq_of_absent D.items owner n habsent
  have hselected : s = branchPrefix (ownerCutoff (listOwner owner D.items) (n.val + 1)) :=
    congrArg (@branchPrefix D.items.length) hcut.symm
  let old := chosenReparent (listForest F D.items) (embeddingHost W) p p' available s
    (D.chosen W Q S C F owner kind E) hagrees
  let out := castChosenSelected (listForest F D.items) (embeddingHost W) p' available hselected old
  have hused (c : Fin 2) : out.used c = (D.chosen W Q S C F owner kind E).used c := by
    rw [used_castChosenSelected]
    rfl
  cases kind with
  | threshold ratio => exact ⟨out.state, fun _ _ => rfl, fun _ => rfl⟩
  | appendix lambda =>
      have hout : D.LiveInvariant W Q S C F owner (.appendix lambda) out := by
        unfold ChunkSource.LiveInvariant
        rw [hused 0, hused 1]
        exact E.property
      exact ⟨⟨out, hout⟩, fun _ _ => rfl, fun _ => rfl⟩

theorem ChunkSource.placement_preserved
    {backend : D.Backend W Q S C F owner kind}
    (rootImage rootImage' : Fin r → Fin hostN) {n m : ℕ} (hnm : n ≤ m)
    (E : D.Prefix W Q S C F owner kind backend rootImage n)
    (E' : D.Prefix W Q S C F owner kind backend rootImage' m)
    (hcopy : ∀ i hi, (D.chosen W Q S C F owner kind E').state.forestCopy.componentCopy i
        (branchPrefix_mono (ownerCutoff_mono (listOwner owner D.items) hnm) hi) =
      (D.chosen W Q S C F owner kind E).state.forestCopy.componentCopy i hi)
    (j : Fin b) (hj : j ∈ prefixSelected D.items (ownerCutoff (listOwner owner D.items) n)) :
    (D.placement W Q S C F owner kind E').forestCopy.componentCopy j
        (prefixSelected_mono D.items (ownerCutoff_mono (listOwner owner D.items) hnm) hj) =
      (D.placement W Q S C F owner kind E).forestCopy.componentCopy j hj := by
  apply SimpleGraph.Copy.ext
  intro a
  change originalCopy F (embeddingHost W) D.items (fun i => rootImage' (owner i))
      (D.chosen W Q S C F owner kind E').orient
      (fun e => residualSide (edgeWhole W Q e) (deleted W Q e)) D.edge
      (D.chosen W Q S C F owner kind E').state j
      (prefixSelected_mono D.items (ownerCutoff_mono (listOwner owner D.items) hnm) hj) a =
    originalCopy F (embeddingHost W) D.items (fun i => rootImage (owner i))
      (D.chosen W Q S C F owner kind E).orient
      (fun e => residualSide (edgeWhole W Q e) (deleted W Q e)) D.edge
      (D.chosen W Q S C F owner kind E).state j hj a
  erw [originalCopy_apply, originalCopy_apply]
  exact congrArg (fun f => f (Fin.cast
    (congrArg F.size (get_position D.items j (prefixSelected_mem_items hj)).symm) a))
      (hcopy (position D.items j (prefixSelected_mem_items hj)) (position_mem_prefix D.items j hj))

theorem ChunkSource.placement_orient_preserved
    {backend : D.Backend W Q S C F owner kind}
    (rootImage rootImage' : Fin r → Fin hostN) {n m : ℕ} (hnm : n ≤ m)
    (E : D.Prefix W Q S C F owner kind backend rootImage n)
    (E' : D.Prefix W Q S C F owner kind backend rootImage' m)
    (horient : ∀ i ∈ branchPrefix (ownerCutoff (listOwner owner D.items) n),
      (D.chosen W Q S C F owner kind E').orient i = (D.chosen W Q S C F owner kind E).orient i)
    (j : Fin b) (hj : j ∈ prefixSelected D.items (ownerCutoff (listOwner owner D.items) n)) :
    (D.placement W Q S C F owner kind E').orient
        ⟨j, prefixSelected_mono D.items (ownerCutoff_mono (listOwner owner D.items) hnm) hj⟩ =
      (D.placement W Q S C F owner kind E).orient ⟨j, hj⟩ :=
  horient (position D.items j (prefixSelected_mem_items hj)) (position_mem_prefix D.items j hj)

end Erdos547b.ZhaoSourceGeneralizedChunk

#print axioms Erdos547b.ZhaoSourceGeneralizedChunk.ChunkSource.exists_skip
#print axioms Erdos547b.ZhaoSourceGeneralizedChunk.ChunkSource.placement_preserved
#print axioms Erdos547b.ZhaoSourceGeneralizedChunk.ChunkSource.placement_orient_preserved
