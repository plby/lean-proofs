/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceCapacityFamilyRoot
import ErdosProblems.Erdos547b.SourceMarkedMixedRootSelection

/-!
# The marked common root for actual ordinary capacity states

Active requirements and live targets are read from the stored ordinary
states. The common root additionally has the verified marked-group degrees.
-/

open scoped SimpleGraph Classical
noncomputable section

namespace Erdos547b.ZhaoSourceMarkedCapacityFamilyRoot

open Finset SimpleGraph Erdos547b.RegularPair
open Erdos547b.ZhaoStability Erdos547b.ZhaoEvenReducedPadding
open Erdos547b.ZhaoLemma611Full Erdos547b.ZhaoRichClaim61Lemma611
open Erdos547b.ZhaoSourceDegreeFormRootRows Erdos547b.ZhaoSourceDegreeFormBounds
open Erdos547b.ZhaoSourceParameterSchedule Erdos547b.ZhaoSourceEmbeddingHost
open Erdos547b.ZhaoSourceParentCleanup Erdos547b.ZhaoSourceActualChunkEmbedding
open Erdos547b.ZhaoSourceRootExclusions Erdos547b.ZhaoSourceMixedRootRequirements
open Erdos547b.ZhaoSourceActualPartThreeStep Erdos547b.ZhaoSourceFamilyCapacity
open Erdos547b.ZhaoSourceCapacityFamilyState Erdos547b.ZhaoSourceNearFullMatching
open Erdos547b.ZhaoSourcePrivatePairGeometry Erdos547b.ZhaoSourceMarkedAvailableSets
open Erdos547b.ZhaoSourceMarkedRootExclusions Erdos547b.ZhaoSourceMarkedMixedRootSelection

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G) (Q : Certificate W) (S : CleanSourceWitness W Q)
variable {fb : ℝ} (O : Output W Q S fb)
variable {C : Finset (EvenPadding (Index W))} (P : Geometry W Q S O C)
variable (t : Fin 2) {b r k : ℕ} (F : OrderedRootedForest b) (owner : Fin b → Fin r)

theorem exists_marked_capacityFamily_root
    (hα : 0 < α) (hα1 : α ≤ 1 / 4) (hhost : hostN = 2 * q)
    (horder : orderThreshold α M ≤ q) (hk : k ≤ 3) (hCV1 : C ⊆ O.D.V1)
    (kinds : Fin k → FamilyKind) (hkind : ∀ j, (kinds j).Valid α)
    (allocation : Fin k → Finset (MatchingEdge Q.claim67.M)) (family : Fin k → List (Fin b))
    (hdisjoint : Pairwise (fun i j => Disjoint (allocation i) (allocation j)))
    (rootImage : Fin r → Fin hostN) (stage : ℕ)
    (A : ∀ j, FamilyState W Q S (rootCluster W Q 0) F owner (kinds j)
      (allocation j) (family j) rootImage stage)
    (haway : ∀ j, allocation j ⊆ edgesAwayFromDistinguished Q.claim67.M
      (padFinset (large W)) (Sum.inl Q.A) (Sum.inl Q.B))
    (globalCount : ℕ) (hglobal : (Finset.univ.biUnion allocation).card ≤ globalCount)
    (used : Finset (Fin hostN)) (hused : (used.card : ℝ) ≤ (epsilon α : ℝ) * W.clusterSize)
    (parent : Option (Fin hostN))
    (hparent : ∀ v, parent = some v →
      ((densityCutoff α : ℝ) - (epsilon α : ℝ)) * (sourceQuota W : ℝ) ≤
        ((reservoir W Q 0).filter ((embeddingHost W).Adj v)).card) :
    ∃ z ∈ reservoir W Q 0, z ∉ used ∧
      (∀ v, parent = some v → (embeddingHost W).Adj v z) ∧
      (∀ j, requirementGood W Q S (rootCluster W Q 0)
        (activeRequirement W Q S (rootCluster W Q 0) F owner (kinds j) (A j).active) z) ∧
      ((padGraph (reduced W)).Adj (Sum.inl (rootCluster W Q 0)) (Sum.inl (rootCluster W Q t)) →
        ((densityCutoff α : ℝ) - (epsilon α : ℝ)) * (sourceQuota W : ℝ) ≤
          ((reservoir W Q t).filter ((embeddingHost W).Adj z)).card) ∧
      16 * (badGroups W Q S O P z).card ≤ C.card ∧
      (∀ x, x ∉ badGroups W Q S O P z →
        (1 - 2 * (eta α : ℝ) - (gamma α : ℝ)) * W.clusterSize ≤
          (((whole W (P.center x)).filter ((embeddingHost W).Adj z)).card : ℝ)) ∧
      ∃ bad : Fin k → Finset (MatchingEdge Q.claim67.M), ∀ j,
        bad j ⊆ (A j).unusedEdges W Q S (rootCluster W Q 0) F owner (kinds j) ∧
        ((bad j).card : ℝ) ≤ 2 * (rootTypicality α : ℝ) * globalCount ∧
        ∀ e ∈ (A j).unusedEdges W Q S (rootCluster W Q 0) F owner (kinds j) \ bad j,
          requirementGood W Q S (rootCluster W Q 0) (initialRequirement W Q (kinds j) e) z := by
  let requirements := fun j => activeRequirement W Q S (rootCluster W Q 0) F owner (kinds j) (A j).active
  let unused := fun j => (A j).unusedEdges W Q S (rootCluster W Q 0) F owner (kinds j)
  let remaining := Finset.univ.biUnion unused
  let raw := allocatedTarget W Q kinds allocation
  have hvalid (j : Fin k) : requirementValid W Q S (rootCluster W Q 0) (requirements j) :=
    activeRequirement_valid W Q S (rootCluster W Q 0) F owner (kinds j)
      hα hα1 hhost horder (hkind j) (A j).active
  have hremaining : remaining ⊆ edgesAwayFromDistinguished Q.claim67.M
      (padFinset (large W)) (Sum.inl Q.A) (Sum.inl Q.B) := by
    intro e he
    obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp he
    exact haway j (Finset.mem_sdiff.mp hj).1
  have hraw : ∀ e ∈ remaining, ∀ c, raw e c ⊆ edgeWhole W Q e c :=
    fun e _ c => allocatedTarget_subset W Q kinds allocation e c
  have hrawLarge : ∀ e ∈ remaining, ∀ c,
      (epsilon α : ℝ) * W.clusterSize ≤ (raw e c).card :=
    fun e _ c => allocatedTarget_large W Q hα hα1 hhost horder kinds allocation e c
  have hremainingCard : remaining.card ≤ globalCount := by
    apply (Finset.card_le_card (show remaining ⊆ Finset.univ.biUnion allocation from ?_)).trans hglobal
    intro e he
    obtain ⟨j, hj, hje⟩ := Finset.mem_biUnion.mp he
    exact Finset.mem_biUnion.mpr ⟨j, hj, (Finset.mem_sdiff.mp hje).1⟩
  obtain ⟨z, hz, hfresh, hAdj, hactive, hdegree, hgcount, hggood, bad, _, hcount, hgood⟩ :=
    exists_mixed_marked_root W Q S O P hα hα1 hCV1 t hk requirements hvalid
      used hused parent hparent remaining hremaining raw hraw hrawLarge
  have hδ : (0 : ℝ) ≤ rootTypicality α := by
    exact_mod_cast (rootTypicality_margin hα hα1).1.le
  have hcountGlobal : (bad.card : ℝ) ≤ 2 * (rootTypicality α : ℝ) * globalCount := by
    have hc : (remaining.card : ℝ) ≤ globalCount := by exact_mod_cast hremainingCard
    exact hcount.trans (mul_le_mul_of_nonneg_left hc (by positivity))
  refine ⟨z, hz, hfresh, hAdj, hactive, hdegree, hgcount, hggood, (fun j => bad ∩ unused j), ?_⟩
  intro j
  refine ⟨Finset.inter_subset_right, ?_, ?_⟩
  · have hc : ((bad ∩ unused j).card : ℝ) ≤ bad.card := by
      exact_mod_cast Finset.card_le_card (Finset.inter_subset_left (s₁ := bad) (s₂ := unused j))
    exact hc.trans hcountGlobal
  · intro e he
    obtain ⟨hu, hnot⟩ := Finset.mem_sdiff.mp he
    have heGlobal : e ∈ remaining \ bad := by
      refine Finset.mem_sdiff.mpr ⟨Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, hu⟩, ?_⟩
      intro hb
      exact hnot (Finset.mem_inter.mpr ⟨hb, hu⟩)
    have htarget := hgood e heGlobal
    have heAllocated : e ∈ allocation j := (Finset.mem_sdiff.mp hu).1
    have hrawEq : raw e = initialTarget W Q (kinds j) e :=
      allocatedTarget_eq W Q kinds allocation hdisjoint j e heAllocated
    rw [hrawEq] at htarget
    exact initialRequirement_good_of_live W Q S (rootCluster W Q 0) (kinds j) e z htarget

end Erdos547b.ZhaoSourceMarkedCapacityFamilyRoot

#print axioms Erdos547b.ZhaoSourceMarkedCapacityFamilyRoot.exists_marked_capacityFamily_root
