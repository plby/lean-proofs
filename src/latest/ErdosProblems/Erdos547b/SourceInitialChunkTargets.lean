/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceGeneralizedChunkPreservation

/-!
# Concrete initial targets for newly reserved mixed-kind chunks

Source owner order makes the earlier prefix empty. Its actual requirement
is exactly the designated initial target used by the incidence selector.
This connects that selector to the actual first chunk successor.
-/

open scoped SimpleGraph Classical
noncomputable section

namespace Erdos547b.ZhaoSourceFamilyCapacity

open Finset SimpleGraph Erdos547b.RegularPair
open Erdos547b.ZhaoLemma611Full Erdos547b.ZhaoSourceDegreeFormRootRows
open Erdos547b.ZhaoSourceEmbeddingHost Erdos547b.ZhaoSourceActualChunkEmbedding
open Erdos547b.ZhaoSourceMixedRootRequirements Erdos547b.ZhaoSourceActualPartThreeStep
open Erdos547b.ZhaoSourceParameterSchedule

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G) (Q : Certificate W)

def initialRequirement (kind : FamilyKind) (e : MatchingEdge Q.claim67.M) : Requirement W Q :=
  match kind with
  | .threshold _ => some (.threshold e)
  | .appendix _ => some (.appendix e (initialTarget W Q kind e))

theorem initialRequirement_good_of_live
    (S : CleanSourceWitness W Q) (C : Index W) (kind : FamilyKind)
    (e : MatchingEdge Q.claim67.M) (z : Fin hostN)
    (hz : EligibleLiveRoot W Q S C e (initialTarget W Q kind e) z) :
    requirementGood W Q S C (initialRequirement W Q kind e) z := by
  cases kind with
  | threshold ratio =>
      intro c _
      have h := hz c
      change (rootDensity W S (Sum.inl C) (edgeVertex W Q e c) - 2 * (epsilon α : ℝ)) *
        (edgeWhole W Q e c).card ≤ _ at h
      rw [edgeWhole_card] at h
      exact h
  | appendix _ => exact hz

end Erdos547b.ZhaoSourceFamilyCapacity

namespace Erdos547b.ZhaoSourceGeneralizedChunk

open Finset SimpleGraph Erdos547b.RegularPair
open Erdos547b.ZhaoLemma611Full Erdos547b.ZhaoSourceDegreeFormRootRows
open Erdos547b.ZhaoSourceParameterSchedule Erdos547b.ZhaoSourceDegreeFormBounds
open Erdos547b.ZhaoSourceEmbeddingHost Erdos547b.ZhaoSourceActualChunkEmbedding
open Erdos547b.ZhaoSourceParentCleanup Erdos547b.ZhaoSourceFamilyCapacity
open Erdos547b.ZhaoSourcePendingPlacement Erdos547b.ZhaoSourceSortedBranchOrder
open Erdos547b.ZhaoSourcePendingOwnerInterval Erdos547b.ZhaoSourcePendingInterval
open Erdos547b.ZhaoSourceResidualRootPacking Erdos547b.ZhaoSourceActiveChunk
open Erdos547b.ZhaoLemma58DynamicBatchAppend Erdos547b.ZhaoLemma58ChosenOwnerBatches
open Erdos547b.ZhaoLemma58ThresholdResidualCapacity Erdos547b.ZhaoSourceMixedRootRequirements

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G) (Q : Certificate W)
variable (S : CleanSourceWitness W Q) (C : Index W)
variable {b r : ℕ} (F : OrderedRootedForest b) (owner : Fin b → Fin r) (kind : FamilyKind)
variable (D : ChunkSource W Q S C F owner kind)

theorem ChunkSource.cutoff_zero_of_no_earlier_owner (n : ℕ)
    (hafter : ∀ i ∈ D.items, n ≤ (owner i).val) :
    ownerCutoff (listOwner owner D.items) n = 0 := by
  apply Finset.card_eq_zero.mpr
  apply Finset.filter_eq_empty_iff.mpr
  intro i _ hlt
  exact (not_lt_of_ge (hafter _ (List.get_mem D.items i))) hlt

theorem ChunkSource.used_empty_of_cutoff_zero
    {backend : D.Backend W Q S C F owner kind} {rootImage : Fin r → Fin hostN} {n : ℕ}
    (E : D.Prefix W Q S C F owner kind backend rootImage n)
    (hcut : ownerCutoff (listOwner owner D.items) n = 0) (c : Fin 2) :
    (D.chosen W Q S C F owner kind E).used c = ∅ := by
  apply Finset.card_eq_zero.mp
  change ((D.chosen W Q S C F owner kind E).state.used c).card = 0
  rw [PartialDynamicAttachedForestEmbedding.card_used]
  simp only [hcut, branchPrefix_zero, Finset.sum_empty]

theorem ChunkSource.requirement_eq_initial_of_cutoff_zero
    {backend : D.Backend W Q S C F owner kind} {rootImage : Fin r → Fin hostN} {n : ℕ}
    (E : D.Prefix W Q S C F owner kind backend rootImage n)
    (hcut : ownerCutoff (listOwner owner D.items) n = 0) :
    D.requirement W Q S C F owner kind E = initialRequirement W Q kind D.edge := by
  cases kind with
  | threshold _ => rfl
  | appendix lambda =>
      have hused := D.used_empty_of_cutoff_zero W Q S C F owner (.appendix lambda) E hcut
      simp only [ChunkSource.requirement, initialRequirement, hused, Finset.sdiff_empty]
      rfl

theorem ChunkSource.exists_prefix_of_no_earlier_owner
    (hα : 0 < α) (hα1 : α ≤ 1 / 4) (hhost : hostN = 2 * q)
    (horder : orderThreshold α M ≤ q)
    (backend : D.Backend W Q S C F owner kind) (rootImage : Fin r → Fin hostN) (n : ℕ)
    (hafter : ∀ i ∈ D.items, n ≤ (owner i).val) :
    Nonempty (D.Prefix W Q S C F owner kind backend rootImage n) := by
  obtain ⟨initial⟩ := D.exists_initial_prefix W Q S C F owner kind hα hα1 hhost horder backend rootImage
  have hcut := D.cutoff_zero_of_no_earlier_owner W Q S C F owner kind n hafter
  have hselected : branchPrefix (b := D.items.length) (ownerCutoff (listOwner owner D.items) 0) =
      branchPrefix (ownerCutoff (listOwner owner D.items) n) := by
    rw [hcut, ownerCutoff_zero]
  cases kind with
  | threshold ratio =>
      exact ⟨castPartialSelected _ _ _ _ _ hselected initial⟩
  | appendix lambda =>
      let out := castChosenSelected (listForest F D.items) (embeddingHost W)
        (fun i => rootImage (listOwner owner D.items i))
        (residualSide (edgeWhole W Q D.edge) (deleted W Q D.edge)) hselected initial.val
      refine ⟨⟨out, ?_⟩⟩
      unfold ChunkSource.LiveInvariant
      rw [used_castChosenSelected, used_castChosenSelected]
      exact initial.property

end Erdos547b.ZhaoSourceGeneralizedChunk

#print axioms Erdos547b.ZhaoSourceFamilyCapacity.initialRequirement_good_of_live
#print axioms Erdos547b.ZhaoSourceGeneralizedChunk.ChunkSource.requirement_eq_initial_of_cutoff_zero
#print axioms Erdos547b.ZhaoSourceGeneralizedChunk.ChunkSource.exists_prefix_of_no_earlier_owner
