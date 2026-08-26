/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceFreshCapacityChunk
import ErdosProblems.Erdos547b.SourcePendingReservation

/-!
# Actual capacity-aware look-ahead reservation

Reserve future source mass until saturation, then realize only the current
owner's prefix. The concrete kind controls both the capacity and the root
test. All later root-map values remain unconstrained.
-/

open scoped SimpleGraph Classical
noncomputable section

namespace Erdos547b.ZhaoSourceCapacityReservationToActive

open Finset SimpleGraph Erdos547b.RegularPair
open Erdos547b.ZhaoStability Erdos547b.ZhaoDegreeForm Erdos547b.ZhaoEvenReducedPadding
open Erdos547b.ZhaoLemma611Full Erdos547b.ZhaoRichClaim61Lemma611
open Erdos547b.ZhaoSourceDegreeFormRootRows Erdos547b.ZhaoSourceDegreeFormBounds
open Erdos547b.ZhaoSourceParameterSchedule Erdos547b.ZhaoSourceFreshChunkBounds
open Erdos547b.ZhaoSourceFamilyCapacity Erdos547b.ZhaoSourceCapacityFamilyState
open Erdos547b.ZhaoSourceGeneralizedChunk Erdos547b.ZhaoSourceMixedRootRequirements
open Erdos547b.ZhaoSourceSaturatedPacking Erdos547b.ZhaoSourcePendingReservation
open Erdos547b.ZhaoSourceSortedBranchOrder

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G) (Q : Certificate W)
variable (S : CleanSourceWitness W Q) (C : Index W)
variable {b r : ℕ} (F : OrderedRootedForest b) (owner : Fin b → Fin r) (kind : FamilyKind)

theorem exists_lookahead_active
    (hα : 0 < α) (hα1 : α ≤ 1 / 4) (hhost : hostN = 2 * q)
    (horder : orderThreshold α M ≤ q) (hC : C = Q.A ∨ C = Q.B) (hkind : kind.Valid α)
    (e : MatchingEdge Q.claim67.M)
    (he : e ∈ edgesAwayFromDistinguished Q.claim67.M (padFinset (large W))
      (Sum.inl Q.A) (Sum.inl Q.B))
    (hedge : edgeValid W Q S C kind e)
    (rootImage : Fin r → Fin hostN) (n : Fin r) (pending future : List (Fin b))
    (hnd : (pending ++ future).Nodup)
    (hordered : (pending ++ future).Pairwise (fun i j => owner i ≤ owner j))
    (hcurrent : ∀ i ∈ pending, owner i = n)
    (hfuture : ∀ i ∈ future, n.val < (owner i).val)
    (hbranch : ∀ i ∈ pending ++ future, kind.BranchValid F i)
    (hsmall : ∀ i, F.size i ≤ freshBranchBound α W.clusterSize)
    (hcap : (freshBranchBound α W.clusterSize : ℝ) < capacity W Q S C kind e)
    (hpending : mass (fun i => (F.size i : ℝ)) pending ≤
      capacity W Q S C kind e - freshBranchBound α W.clusterSize)
    (hz : requirementGood W Q S C (initialRequirement W Q kind e) (rootImage n)) :
    ∃ R : PendingReservation (fun i => (F.size i : ℝ)) pending future
        (capacity W Q S C kind e) (freshBranchBound α W.clusterSize),
      ∃ X : ActiveState W Q S C F owner kind rootImage (n.val + 1),
        X.source.items = R.reserved ∧ X.source.edge = e ∧
        ∀ i ∈ R.remaining, n.val < (owner i).val := by
  obtain ⟨R⟩ := exists_pendingReservation (fun i => (F.size i : ℝ)) pending future
    (capacity W Q S C kind e) (freshBranchBound α W.clusterSize) (Nat.cast_nonneg _) hcap
    (fun i _ => ⟨Nat.cast_nonneg _, by exact_mod_cast hsmall i⟩) hpending
  have hRmem : ∀ i ∈ R.reserved, i ∈ pending ++ future := by
    intro i hi
    exact R.flatten ▸ List.mem_append_left R.remaining hi
  have hndR : R.reserved.Nodup := (List.nodup_append.mp (R.flatten.symm ▸ hnd)).1
  have horderR : R.reserved.Pairwise (fun i j => owner i ≤ owner j) :=
    (List.pairwise_append.mp (R.flatten.symm ▸ hordered)).1
  let D : ChunkSource W Q S C F owner kind := {
    edge := e
    edge_away := he
    edge_valid := hedge
    items := R.reserved
    nodup := hndR
    owner_mono := monotone_listOwner_of_pairwise owner R.reserved horderR
    fits := R.fits
    branch_valid := fun i hi => hbranch i (hRmem i hi)
    small := fun i _ => hsmall i }
  have hafter : ∀ i ∈ D.items, n.val ≤ (owner i).val := by
    intro i hi
    rcases List.mem_append.mp (hRmem i hi) with hp | hf
    · exact (congrArg Fin.val (hcurrent i hp)).ge
    · exact (hfuture i hf).le
  have hactive := D.exists_fresh_active W Q S C F owner kind hα hα1 hhost horder hC hkind
    rootImage n hafter (rootImage n) hz
  rw [Function.update_eq_self n rootImage] at hactive
  obtain ⟨X, hX⟩ := hactive
  refine ⟨R, X, ?_, ?_, ?_⟩
  · exact congrArg (fun d => d.items) hX
  · exact congrArg (fun d => d.edge) hX
  · intro i hi
    exact hfuture i (List.mem_of_mem_drop hi)

end Erdos547b.ZhaoSourceCapacityReservationToActive

#print axioms Erdos547b.ZhaoSourceCapacityReservationToActive.exists_lookahead_active
