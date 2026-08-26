/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceInitialChunkTargets
import ErdosProblems.Erdos547b.SourceCapacityFamilyState

/-!
# Fresh reserved and completed chunks at the concrete family capacity

The source capacity constructs the backend, the empty earlier prefix and
the actual current-owner step. A current-only chunk gives a fully closed
original-index placement; a chunk with later owners gives an active state.
-/

open scoped SimpleGraph Classical
noncomputable section

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
open Erdos547b.ZhaoSourceOriginalBranchPlacement Erdos547b.ZhaoSourceCapacityFamilyState

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G) (Q : Certificate W)
variable (S : CleanSourceWitness W Q) (C : Index W)
variable {b r : ℕ} (F : OrderedRootedForest b) (owner : Fin b → Fin r) (kind : FamilyKind)
variable (D : ChunkSource W Q S C F owner kind)

theorem ChunkSource.exists_fresh_advance
    (hα : 0 < α) (hα1 : α ≤ 1 / 4) (hhost : hostN = 2 * q)
    (horder : orderThreshold α M ≤ q) (hC : C = Q.A ∨ C = Q.B) (hkind : kind.Valid α)
    (rootImage : Fin r → Fin hostN) (n : Fin r)
    (hafter : ∀ i ∈ D.items, n.val ≤ (owner i).val)
    (z : Fin hostN) (hz : requirementGood W Q S C (initialRequirement W Q kind D.edge) z) :
    ∃ backend : D.Backend W Q S C F owner kind,
      Nonempty (D.Prefix W Q S C F owner kind backend (Function.update rootImage n z) (n.val + 1)) := by
  obtain ⟨backend⟩ := D.exists_backend W Q S C F owner kind hα hα1 hhost horder hC hkind
  obtain ⟨initial⟩ := D.exists_prefix_of_no_earlier_owner W Q S C F owner kind hα hα1 hhost horder
    backend rootImage n.val hafter
  have hcut := D.cutoff_zero_of_no_earlier_owner W Q S C F owner kind n.val hafter
  have hgood : requirementGood W Q S C (D.requirement W Q S C F owner kind initial) z := by
    rw [D.requirement_eq_initial_of_cutoff_zero W Q S C F owner kind initial hcut]
    exact hz
  obtain ⟨out, _, _⟩ := D.exists_advance W Q S C F owner kind hα hα1 hhost horder hkind
    rootImage n initial z hgood
  exact ⟨backend, ⟨out⟩⟩

theorem ChunkSource.exists_fresh_active
    (hα : 0 < α) (hα1 : α ≤ 1 / 4) (hhost : hostN = 2 * q)
    (horder : orderThreshold α M ≤ q) (hC : C = Q.A ∨ C = Q.B) (hkind : kind.Valid α)
    (rootImage : Fin r → Fin hostN) (n : Fin r)
    (hafter : ∀ i ∈ D.items, n.val ≤ (owner i).val)
    (z : Fin hostN) (hz : requirementGood W Q S C (initialRequirement W Q kind D.edge) z) :
    ∃ A : ActiveState W Q S C F owner kind (Function.update rootImage n z) (n.val + 1),
      A.source = D := by
  obtain ⟨backend, ⟨E⟩⟩ := D.exists_fresh_advance W Q S C F owner kind
    hα hα1 hhost horder hC hkind rootImage n hafter z hz
  exact ⟨activeStateOfPrefix W Q S C F owner kind hα hkind D backend E, rfl⟩

/-- Current-only source chunks are completely copied after this one
actual owner step, including their external attachment edges. -/
theorem ChunkSource.exists_fresh_closed
    (hα : 0 < α) (hα1 : α ≤ 1 / 4) (hhost : hostN = 2 * q)
    (horder : orderThreshold α M ≤ q) (hC : C = Q.A ∨ C = Q.B) (hkind : kind.Valid α)
    (rootImage : Fin r → Fin hostN) (n : Fin r)
    (howner : ∀ i ∈ D.items, owner i = n)
    (z : Fin hostN) (hz : requirementGood W Q S C (initialRequirement W Q kind D.edge) z) :
    ∃ P : BranchPlacement F (embeddingHost W) D.items.toFinset
        (fun i => Function.update rootImage n z (owner i))
        (fun e => residualSide (edgeWhole W Q e) (deleted W Q e)),
      (∀ i, P.edge i = D.edge) ∧
      ∀ i, 0 < rootDensity W S (Sum.inl C) (edgeVertex W Q (P.edge i) (P.orient i 0)) := by
  obtain ⟨backend, ⟨E⟩⟩ := D.exists_fresh_advance W Q S C F owner kind
    hα hα1 hhost horder hC hkind rootImage n
    (fun i hi => (congrArg Fin.val (howner i hi)).ge) z hz
  have hselected : prefixSelected D.items (ownerCutoff (listOwner owner D.items) (n.val + 1)) =
      D.items.toFinset := by
    rw [prefixSelected_ownerCutoff D.items owner D.owner_mono]
    apply Finset.filter_eq_self.mpr
    intro i hi
    rw [howner i (List.mem_toFinset.mp hi)]
    exact Nat.lt_succ_self _
  let P := Erdos547b.ZhaoSourceReservationFamilyState.castPlacement W Q F owner hselected
    (D.placement W Q S C F owner kind E)
  refine ⟨P, fun _ => rfl, ?_⟩
  intro i
  exact D.placement_root_positive W Q S C F owner kind hα hkind E ⟨i.1, hselected.symm ▸ i.2⟩

end Erdos547b.ZhaoSourceGeneralizedChunk

#print axioms Erdos547b.ZhaoSourceGeneralizedChunk.ChunkSource.exists_fresh_advance
#print axioms Erdos547b.ZhaoSourceGeneralizedChunk.ChunkSource.exists_fresh_active
#print axioms Erdos547b.ZhaoSourceGeneralizedChunk.ChunkSource.exists_fresh_closed
