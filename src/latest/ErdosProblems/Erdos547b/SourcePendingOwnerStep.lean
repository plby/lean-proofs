/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceActualPendingPlan
import ErdosProblems.Erdos547b.SourcePendingOwnerInterval
import ErdosProblems.Erdos547b.SourcePendingRootSelection

/-!
# An actual pending-owner successor

Choose a fresh root adjacent to its actual old cut parent and extend that
owner's consecutive pending branches. The root stays eligible on the
pending pair, typical to the opposite root reservoir, and eligible on
almost all unused matching edges. An already prescribed first root has a
separate image-preserving extension, without selecting a replacement.
-/

open scoped SimpleGraph Classical
noncomputable section

namespace Erdos547b.ZhaoSourcePendingOwnerStep

open Finset SimpleGraph Erdos547b.RegularPair
open Erdos547b.ZhaoStability Erdos547b.ZhaoDegreeForm Erdos547b.ZhaoEvenReducedPadding
open Erdos547b.ZhaoLemma611Full Erdos547b.ZhaoRichClaim61Lemma611
open Erdos547b.ZhaoSourceParameterSchedule Erdos547b.ZhaoSourceDegreeFormRootRows
open Erdos547b.ZhaoSourceEmbeddingHost Erdos547b.ZhaoSourceActualChunkEmbedding
open Erdos547b.ZhaoSourceOnlineMatchingRoot Erdos547b.ZhaoSourceParentCleanup
open Erdos547b.ZhaoSourceActualPendingPlan Erdos547b.ZhaoSourcePendingRootSelection
open Erdos547b.ZhaoSourcePendingInterval Erdos547b.ZhaoSourcePendingOwnerInterval
open Erdos547b.ZhaoLemma58DynamicBatchAppend Erdos547b.ZhaoLemma58GroupedSmallForest
open Erdos547b.ZhaoLemma58ThresholdResidualCapacity

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G) (Q : Certificate W)

/-- The first pending owner may already have a fixed root from an earlier
closed chunk. Reuse that exact root and leave the entire root map unchanged. -/
theorem extend_at_prescribed_root
    {S : CleanSourceWitness W Q} {C : Index W} {fixed : MatchingEdge Q.claim67.M}
    {b r : ℕ} {F : OrderedRootedForest b} (P : ActualPendingPlan W Q S C fixed F)
    (owner : Fin b → Fin r) (hmono : Monotone owner)
    (n : Fin r) (rootImage : Fin r → Fin hostN)
    (E : PartialDynamicAttachedForestEmbedding F (embeddingHost W) (fun i => rootImage (owner i))
      P.orient (residualSide (edgeWhole W Q fixed) (deleted W Q fixed))
      (branchPrefix (ownerCutoff owner n.val)))
    (hz : EligibleRoot W Q S C fixed (rootImage n)) :
    ∃ E' : PartialDynamicAttachedForestEmbedding F (embeddingHost W) (fun i => rootImage (owner i))
        P.orient (residualSide (edgeWhole W Q fixed) (deleted W Q fixed))
        (branchPrefix (ownerCutoff owner (n.val + 1))),
      ∀ j hj, E'.forestCopy.componentCopy j
          (branchPrefix_mono (ownerCutoff_mono owner (Nat.le_succ n.val)) hj) =
        E.forestCopy.componentCopy j hj := by
  apply P.extend_interval W Q (fun i => rootImage (owner i))
    (ownerCutoff owner n.val) (ownerCutoff owner (n.val + 1))
    (ownerCutoff_mono owner (Nat.le_succ n.val)) (ownerCutoff_le owner _) E (rootImage n) hz
  intro i hlo hhi
  rw [owner_eq_of_mem_interval owner hmono n i hlo hhi]

/-- A genuine graph-theoretic owner step on the fixed pending pair. The
old parent degree can come from permanent cleaning or an earlier root's
reservoir constraint. Future root values are completely unrestricted. -/
theorem exists_pending_owner_step
    (hα : 0 < α) (hα1 : α ≤ 1 / 4)
    (S : CleanSourceWitness W Q) (s t : Fin 2)
    (fixed : MatchingEdge Q.claim67.M)
    (hfixed : fixed ∈ edgesAwayFromDistinguished Q.claim67.M (padFinset (large W))
      (Sum.inl Q.A) (Sum.inl Q.B))
    {b r : ℕ} (F : OrderedRootedForest b)
    (P : ActualPendingPlan W Q S (rootCluster W Q s) fixed F)
    (owner : Fin b → Fin r) (hmono : Monotone owner)
    (n : Fin r) (rootImage : Fin r → Fin hostN)
    (E : PartialDynamicAttachedForestEmbedding F (embeddingHost W) (fun i => rootImage (owner i))
      P.orient (residualSide (edgeWhole W Q fixed) (deleted W Q fixed))
      (branchPrefix (ownerCutoff owner n.val)))
    (v : Fin hostN)
    (hdegree : ((densityCutoff α : ℝ) - (epsilon α : ℝ)) * (sourceQuota W : ℝ) ≤
      (#((reservoir W Q s).filter ((embeddingHost W).Adj v)) : ℝ))
    (used : Finset (Fin hostN)) (hused : (used.card : ℝ) ≤ (epsilon α : ℝ) * W.clusterSize)
    (remaining : Finset (MatchingEdge Q.claim67.M))
    (hremaining : remaining ⊆ edgesAwayFromDistinguished Q.claim67.M
      (padFinset (large W)) (Sum.inl Q.A) (Sum.inl Q.B)) :
    ∃ z ∈ reservoir W Q s, (embeddingHost W).Adj v z ∧ z ∉ used ∧
      EligibleRoot W Q S (rootCluster W Q s) fixed z ∧
      ((padGraph (reduced W)).Adj (Sum.inl (rootCluster W Q s)) (Sum.inl (rootCluster W Q t)) →
        ((densityCutoff α : ℝ) - (epsilon α : ℝ)) * (sourceQuota W : ℝ) ≤
          (#((reservoir W Q t).filter ((embeddingHost W).Adj z)) : ℝ)) ∧
      (∃ bad ⊆ remaining,
        (bad.card : ℝ) ≤ 2 * (rootTypicality α : ℝ) * remaining.card ∧
        ∀ e ∈ remaining \ bad, EligibleRoot W Q S (rootCluster W Q s) e z) ∧
      ∃ E' : PartialDynamicAttachedForestEmbedding F (embeddingHost W)
          (fun i => Function.update rootImage n z (owner i)) P.orient
          (residualSide (edgeWhole W Q fixed) (deleted W Q fixed))
          (branchPrefix (ownerCutoff owner (n.val + 1))),
        ∀ j hj, E'.forestCopy.componentCopy j
            (branchPrefix_mono (ownerCutoff_mono owner (Nat.le_succ n.val)) hj) =
          E.forestCopy.componentCopy j hj := by
  obtain ⟨z, hz, hadj, hfresh, heligible, hrootDegree, hremainingAccess⟩ :=
    exists_eligible_root_after_parent_degree W Q hα hα1 S s t v hdegree
      fixed hfixed used hused remaining hremaining
  refine ⟨z, hz, hadj, hfresh, heligible, hrootDegree, hremainingAccess, ?_⟩
  exact exists_owner_extension F (embeddingHost W) owner hmono P.orient
    (residualSide (edgeWhole W Q fixed) (deleted W Q fixed)) n rootImage E z
    (fun i p E => P.step i p E z heligible)

end Erdos547b.ZhaoSourcePendingOwnerStep

#print axioms Erdos547b.ZhaoSourcePendingOwnerStep.extend_at_prescribed_root
#print axioms Erdos547b.ZhaoSourcePendingOwnerStep.exists_pending_owner_step
