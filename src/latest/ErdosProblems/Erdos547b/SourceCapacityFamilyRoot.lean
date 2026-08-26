/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceCapacityFamilyRequirements
import ErdosProblems.Erdos547b.SourceMixedRootSelection

/-!
# One root from actual capacity-aware family states

The requirements and initial targets come from the stored prefixes and
disjoint source allocations. The output gives a common fresh root and an
absolute bad-edge allowance for each family, including the initial case.
-/

open scoped SimpleGraph Classical
noncomputable section

namespace Erdos547b.ZhaoSourceCapacityFamilyRoot

open Finset SimpleGraph Erdos547b.RegularPair
open Erdos547b.ZhaoStability Erdos547b.ZhaoDegreeForm Erdos547b.ZhaoEvenReducedPadding
open Erdos547b.ZhaoLemma611Full Erdos547b.ZhaoRichClaim61Lemma611
open Erdos547b.ZhaoSourceDegreeFormRootRows Erdos547b.ZhaoSourceDegreeFormBounds
open Erdos547b.ZhaoSourceParameterSchedule Erdos547b.ZhaoSourceEmbeddingHost
open Erdos547b.ZhaoSourceParentCleanup Erdos547b.ZhaoSourceActualChunkEmbedding
open Erdos547b.ZhaoSourceRootExclusions Erdos547b.ZhaoSourceMixedRootRequirements
open Erdos547b.ZhaoSourceMixedRootSelection Erdos547b.ZhaoSourceActualPartThreeStep
open Erdos547b.ZhaoSourceFamilyCapacity Erdos547b.ZhaoSourceCapacityFamilyState

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G) (Q : Certificate W)
variable (S : CleanSourceWitness W Q) (s t : Fin 2)
variable {b r k : ℕ} (F : OrderedRootedForest b) (owner : Fin b → Fin r)

theorem exists_capacityFamily_root
    (hα : 0 < α) (hα1 : α ≤ 1 / 4)
    (hhost : hostN = 2 * q) (horder : orderThreshold α M ≤ q) (hk : k ≤ 3)
    (kinds : Fin k → FamilyKind) (hkind : ∀ j, (kinds j).Valid α)
    (allocation : Fin k → Finset (MatchingEdge Q.claim67.M)) (family : Fin k → List (Fin b))
    (hdisjoint : Pairwise (fun i j => Disjoint (allocation i) (allocation j)))
    (rootImage : Fin r → Fin hostN) (stage : ℕ)
    (A : ∀ j, FamilyState W Q S (rootCluster W Q s) F owner (kinds j)
      (allocation j) (family j) rootImage stage)
    (haway : ∀ j, allocation j ⊆ edgesAwayFromDistinguished Q.claim67.M
      (padFinset (large W)) (Sum.inl Q.A) (Sum.inl Q.B))
    (globalCount : ℕ) (hglobal : (Finset.univ.biUnion allocation).card ≤ globalCount)
    (used : Finset (Fin hostN)) (hused : (used.card : ℝ) ≤ (epsilon α : ℝ) * W.clusterSize)
    (parent : Option (Fin hostN))
    (hparent : ∀ v, parent = some v →
      ((densityCutoff α : ℝ) - (epsilon α : ℝ)) * (sourceQuota W : ℝ) ≤
        (#((reservoir W Q s).filter ((embeddingHost W).Adj v)) : ℝ)) :
    ∃ z ∈ reservoir W Q s, z ∉ used ∧
      (∀ v, parent = some v → (embeddingHost W).Adj v z) ∧
      (∀ j, requirementGood W Q S (rootCluster W Q s)
        (activeRequirement W Q S (rootCluster W Q s) F owner (kinds j) (A j).active) z) ∧
      ((padGraph (reduced W)).Adj (Sum.inl (rootCluster W Q s)) (Sum.inl (rootCluster W Q t)) →
        ((densityCutoff α : ℝ) - (epsilon α : ℝ)) * (sourceQuota W : ℝ) ≤
          (#((reservoir W Q t).filter ((embeddingHost W).Adj z)) : ℝ)) ∧
      ∃ bad : Fin k → Finset (MatchingEdge Q.claim67.M), ∀ j,
        bad j ⊆ (A j).unusedEdges W Q S (rootCluster W Q s) F owner (kinds j) ∧
        ((bad j).card : ℝ) ≤ 2 * (rootTypicality α : ℝ) * globalCount ∧
        ∀ e ∈ (A j).unusedEdges W Q S (rootCluster W Q s) F owner (kinds j) \ bad j,
          requirementGood W Q S (rootCluster W Q s) (initialRequirement W Q (kinds j) e) z := by
  let requirements := fun j => activeRequirement W Q S (rootCluster W Q s) F owner (kinds j) (A j).active
  let unused := fun j => (A j).unusedEdges W Q S (rootCluster W Q s) F owner (kinds j)
  let remaining := Finset.univ.biUnion unused
  let raw := allocatedTarget W Q kinds allocation
  have hvalid (j : Fin k) : requirementValid W Q S (rootCluster W Q s) (requirements j) :=
    activeRequirement_valid W Q S (rootCluster W Q s) F owner (kinds j)
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
  have hchoose : ∃ z ∈ reservoir W Q s, z ∉ used ∧
      (∀ v, parent = some v → (embeddingHost W).Adj v z) ∧
      (∀ j, requirementGood W Q S (rootCluster W Q s) (requirements j) z) ∧
      ((padGraph (reduced W)).Adj (Sum.inl (rootCluster W Q s)) (Sum.inl (rootCluster W Q t)) →
        ((densityCutoff α : ℝ) - (epsilon α : ℝ)) * (sourceQuota W : ℝ) ≤
          (#((reservoir W Q t).filter ((embeddingHost W).Adj z)) : ℝ)) ∧
      ∃ bad ⊆ remaining, (bad.card : ℝ) ≤ 2 * (rootTypicality α : ℝ) * remaining.card ∧
        ∀ e ∈ remaining \ bad, EligibleLiveRoot W Q S (rootCluster W Q s) e (raw e) z := by
    cases parent with
    | none =>
        obtain ⟨z, hz, hfresh, hactive, hdegree, bad, hb, hc, hg⟩ :=
          exists_initial_mixed_root W Q hα hα1 S s t hk requirements hvalid used hused
            remaining hremaining raw hraw hrawLarge
        exact ⟨z, hz, hfresh, by simp, hactive, hdegree, bad, hb, hc, hg⟩
    | some v =>
        obtain ⟨z, hz, hadj, hfresh, hactive, hdegree, bad, hb, hc, hg⟩ :=
          exists_mixed_root_after_parent_degree W Q hα hα1 S s t v (hparent v rfl)
            hk requirements hvalid used hused remaining hremaining raw hraw hrawLarge
        refine ⟨z, hz, hfresh, ?_, hactive, hdegree, bad, hb, hc, hg⟩
        intro v' hv
        exact Option.some.inj hv ▸ hadj
  obtain ⟨z, hz, hfresh, hparentAdj, hactive, hdegree, bad, _, hcount, hgood⟩ := hchoose
  have hδ : (0 : ℝ) ≤ rootTypicality α := by
    exact_mod_cast (rootTypicality_margin hα hα1).1.le
  have hcountGlobal : (bad.card : ℝ) ≤ 2 * (rootTypicality α : ℝ) * globalCount := by
    have hc : (remaining.card : ℝ) ≤ globalCount := by exact_mod_cast hremainingCard
    exact hcount.trans (mul_le_mul_of_nonneg_left hc (by positivity))
  refine ⟨z, hz, hfresh, hparentAdj, hactive, hdegree, (fun j => bad ∩ unused j), ?_⟩
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
    exact initialRequirement_good_of_live W Q S (rootCluster W Q s) (kinds j) e z htarget

end Erdos547b.ZhaoSourceCapacityFamilyRoot

#print axioms Erdos547b.ZhaoSourceCapacityFamilyRoot.exists_capacityFamily_root
