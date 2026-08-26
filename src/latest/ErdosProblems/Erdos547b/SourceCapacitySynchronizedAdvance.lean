/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceCapacityFamilyBudgetAdvance
import ErdosProblems.Erdos547b.SourceCapacityFamilyRoot

/-!
# One actual root and simultaneous capacity-aware family successors

Choose the shared root from the actual mixed-family state, then construct
each family's complete successor from its concrete capacity budget.
Initial and cut-parent roots use the same image-preserving interface.
-/

open scoped SimpleGraph BigOperators Classical
noncomputable section

namespace Erdos547b.ZhaoSourceCapacitySynchronizedAdvance

open Finset SimpleGraph Erdos547b.RegularPair
open Erdos547b.ZhaoStability Erdos547b.ZhaoDegreeForm Erdos547b.ZhaoEvenReducedPadding
open Erdos547b.ZhaoLemma611Full Erdos547b.ZhaoRichClaim61Lemma611
open Erdos547b.ZhaoSourceDegreeFormRootRows Erdos547b.ZhaoSourceDegreeFormBounds
open Erdos547b.ZhaoSourceParameterSchedule Erdos547b.ZhaoSourceFreshChunkBounds
open Erdos547b.ZhaoSourceFamilyCapacity Erdos547b.ZhaoSourceCapacityFamilyState
open Erdos547b.ZhaoSourceCapacityFamilyBudgetAdvance Erdos547b.ZhaoSourceCapacityFamilyRoot
open Erdos547b.ZhaoSourceSaturatedPacking Erdos547b.ZhaoSourceEmbeddingHost
open Erdos547b.ZhaoSourceParentCleanup Erdos547b.ZhaoSourceRootExclusions
open Erdos547b.ZhaoSourceFamilyOwnerAdvance (processedFamily_mono)

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G) (Q : Certificate W)
variable (S : CleanSourceWitness W Q) (s t : Fin 2)
variable {b r k : ℕ} (F : OrderedRootedForest b) (owner : Fin b → Fin r)

theorem exists_synchronizedFamilyAdvance
    (hα : 0 < α) (hα1 : α ≤ 1 / 4) (hhost : hostN = 2 * q)
    (horder : orderThreshold α M ≤ q) (hk : k ≤ 3)
    (kinds : Fin k → FamilyKind) (hkind : ∀ j, (kinds j).Valid α)
    (allocation : Fin k → Finset (MatchingEdge Q.claim67.M)) (family : Fin k → List (Fin b))
    (hdisjoint : Pairwise (fun i j => Disjoint (allocation i) (allocation j)))
    (rootImage : Fin r → Fin hostN) (n : Fin r)
    (A : ∀ j, FamilyState W Q S (rootCluster W Q s) F owner (kinds j)
      (allocation j) (family j) rootImage n.val)
    (hbranch : ∀ j, ∀ i ∈ family j, (kinds j).BranchValid F i)
    (hedge : ∀ j, ∀ e ∈ allocation j, edgeValid W Q S (rootCluster W Q s) (kinds j) e)
    (hsmall : ∀ i, F.size i ≤ freshBranchBound α W.clusterSize)
    (haway : ∀ j, allocation j ⊆ edgesAwayFromDistinguished Q.claim67.M
      (padFinset (large W)) (Sum.inl Q.A) (Sum.inl Q.B))
    (globalCount : ℕ) (hglobal : (Finset.univ.biUnion allocation).card ≤ globalCount)
    (hbudget : ∀ j, family j ≠ [] → mass (fun i => (F.size i : ℝ)) (family j) ≤
      (∑ e ∈ allocation j, capacity W Q S (rootCluster W Q s) (kinds j) e) -
        (freshBranchBound α W.clusterSize : ℝ) * (allocation j).card -
        4 * (rootTypicality α : ℝ) * W.clusterSize * globalCount)
    (used : Finset (Fin hostN)) (hused : (used.card : ℝ) ≤ (epsilon α : ℝ) * W.clusterSize)
    (parent : Option (Fin hostN))
    (hparent : ∀ v, parent = some v →
      ((densityCutoff α : ℝ) - (epsilon α : ℝ)) * (sourceQuota W : ℝ) ≤
        (#((reservoir W Q s).filter ((embeddingHost W).Adj v)) : ℝ)) :
    ∃ z ∈ reservoir W Q s, z ∉ used ∧
      (∀ v, parent = some v → (embeddingHost W).Adj v z) ∧
      ((padGraph (reduced W)).Adj (Sum.inl (rootCluster W Q s)) (Sum.inl (rootCluster W Q t)) →
        ((densityCutoff α : ℝ) - (epsilon α : ℝ)) * (sourceQuota W : ℝ) ≤
          (#((reservoir W Q t).filter ((embeddingHost W).Adj z)) : ℝ)) ∧
      ∃ D : ∀ j, FamilyState W Q S (rootCluster W Q s) F owner (kinds j) (allocation j) (family j)
          (Function.update rootImage n z) (n.val + 1),
        ∀ j i hi, ((D j).currentPlacement W Q S (rootCluster W Q s) F owner (kinds j)).forestCopy.componentCopy i
            (processedFamily_mono owner (Nat.le_succ n.val) (family j) hi) =
          ((A j).currentPlacement W Q S (rootCluster W Q s) F owner (kinds j)).forestCopy.componentCopy i hi := by
  obtain ⟨z, hz, hfresh, hAdj, hactive, hdegree, bad, hbad⟩ := exists_capacityFamily_root W Q S s t F owner
    hα hα1 hhost horder hk kinds hkind allocation family hdisjoint rootImage n.val A haway
    globalCount hglobal used hused parent hparent
  have hstep (j : Fin k) := exists_familyAdvance W Q S (rootCluster W Q s) F owner (kinds j)
    hα hα1 hhost horder (rootCluster_cases W Q s) (hkind j) (hbranch j) (hedge j) hsmall (haway j)
    rootImage n (A j) globalCount (hbudget j) z (hactive j) (bad j) (hbad j).1 (hbad j).2.1 (hbad j).2.2
  choose D hD using hstep
  exact ⟨z, hz, hfresh, hAdj, hdegree, D, hD⟩

end Erdos547b.ZhaoSourceCapacitySynchronizedAdvance

#print axioms Erdos547b.ZhaoSourceCapacitySynchronizedAdvance.exists_synchronizedFamilyAdvance
