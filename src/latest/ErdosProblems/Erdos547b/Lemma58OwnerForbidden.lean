/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Lemma58OwnerLocalStep

/-!
# Owner-specific target cleaning in the dynamic Lemma 5.8 recursion

Before an owner batch is embedded, a finite bad set may be deleted from each
literal residual matching endpoint.  The local threshold/Appendix constructor
works in that smaller live pair, and its output is then monotonically viewed
inside the original residual pair.  This is the target-cleaning hook needed
for the finitely many future cut-parent constraints.
-/

open scoped SimpleGraph
noncomputable section

namespace Erdos547b.ZhaoLemma58OwnerForbidden

open Finset Fintype SimpleGraph
open Erdos547b.RegularPair
open Erdos547b.ZhaoLemma58GroupedSmallForest
open Erdos547b.ZhaoLemma58DynamicBatchAppend
open Erdos547b.ZhaoLemma58ChosenOwnerBatches
open Erdos547b.ZhaoLemma58OwnerLocalStep
open Erdos547b.ZhaoClaim616SourceBridge.OrderedBranchForest

universe v

/-- A dynamic attached embedding remains valid after enlarging each displayed
endpoint reservoir. -/
def DynamicAttachedForestEmbedding.mono
    {b : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    {F : OrderedRootedForest b} {G : SimpleGraph B}
    {externalParent : Fin b → B} {orient : Fin b → Fin 2 ≃ Fin 2}
    {smallLive largeLive : Fin 2 → Finset B}
    (E : DynamicAttachedForestEmbedding F G externalParent orient smallLive)
    (hsub : ∀ c, smallLive c ⊆ largeLive c) :
    DynamicAttachedForestEmbedding F G externalParent orient largeLive where
  embedding := E.embedding
  attach := E.attach
  map_side := fun i a ↦ hsub _ (E.map_side i a)

/-- The literal live endpoint after deleting the bad vertices assigned to the
current owner. -/
def ownerCleanedLive {B : Type v} [DecidableEq B]
    (live bad : Fin 2 → Finset B) (c : Fin 2) : Finset B :=
  live c \ bad c

theorem ownerCleanedLive_subset {B : Type v} [DecidableEq B]
    (live bad : Fin 2 → Finset B) (c : Fin 2) :
    ownerCleanedLive live bad c ⊆ live c :=
  Finset.sdiff_subset

/-- Owner-recursive Lemma 5.8 with dynamically chosen orientations and an
owner-specific target-cleaning deletion.  The only local premise is the
source/host datum consumed by the already checked concrete constructors. -/
theorem exists_dynamicEmbedding_of_ownerLocalStepsWithForbidden
    {b r : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    (F : OrderedRootedForest b) (G : SimpleGraph B) [DecidableRel G.Adj]
    (externalParent : Fin b → B)
    (whole available : Fin 2 → Finset B)
    (havailable : ∀ c, available c ⊆ whole c)
    (hwholeDisjoint : Disjoint (whole 0) (whole 1))
    (owner : Fin b → Fin r) (rho density : ℝ)
    (bad : Fin r → Fin 2 → Finset B)
    (hdata : ∀ n (hn : n < r)
      (Eprefix : ChosenPartialDynamicEmbedding F G externalParent available
        (ownerPrefix Finset.univ owner n)),
      Nonempty (OwnerLocalStepData
        (selectedForest F (ownerBatch Finset.univ owner ⟨n, hn⟩)) G
        (fun k ↦ externalParent
          (Erdos547b.ZhaoClaim616SourceBridge.OrderedBranchForest.selectedEquiv
            (ownerBatch Finset.univ owner ⟨n, hn⟩) k))
        whole
        (ownerCleanedLive (fun c ↦ available c \ Eprefix.used c)
          (bad ⟨n, hn⟩)) rho density)) :
    ∃ orient : Fin b → Fin 2 ≃ Fin 2,
      Nonempty (DynamicAttachedForestEmbedding
        F G externalParent orient available) := by
  apply exists_dynamicAttachedForestEmbedding_of_chosenOwnerBatches
    F G externalParent whole available havailable hwholeDisjoint owner
  intro n hn Eprefix
  obtain ⟨D⟩ := hdata n hn Eprefix
  obtain ⟨localOrient, ⟨E⟩⟩ := D.realize
    (selectedForest F (ownerBatch Finset.univ owner ⟨n, hn⟩)) G
    (fun k ↦ externalParent
      (Erdos547b.ZhaoClaim616SourceBridge.OrderedBranchForest.selectedEquiv
        (ownerBatch Finset.univ owner ⟨n, hn⟩) k))
    whole
    (ownerCleanedLive (fun c ↦ available c \ Eprefix.used c)
      (bad ⟨n, hn⟩)) rho density
  exact ⟨localOrient,
    ⟨Erdos547b.ZhaoLemma58OwnerForbidden.DynamicAttachedForestEmbedding.mono E
      (fun c ↦ ownerCleanedLive_subset
        (fun c ↦ available c \ Eprefix.used c) (bad ⟨n, hn⟩) c)⟩⟩

end Erdos547b.ZhaoLemma58OwnerForbidden

#print axioms Erdos547b.ZhaoLemma58OwnerForbidden.exists_dynamicEmbedding_of_ownerLocalStepsWithForbidden
