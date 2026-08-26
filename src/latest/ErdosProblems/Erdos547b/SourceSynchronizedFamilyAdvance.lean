/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceFamilyBudgetAdvance
import ErdosProblems.Erdos547b.SourceMultiPendingRoot

/-!
# One actual root and simultaneous successors for up to three families

The family matchings need not have equal sizes. Each family is charged
the same explicit global bad-edge allowance. Both the initial root and
an already embedded cut parent are handled without future-root premises.
-/

open scoped SimpleGraph BigOperators Classical
noncomputable section

namespace Erdos547b.ZhaoSourceSynchronizedFamilyAdvance

open Finset SimpleGraph Erdos547b.RegularPair
open Erdos547b.ZhaoSourceFamilyBudgetAdvance Erdos547b.ZhaoSourceFamilyOwnerAdvance
open Erdos547b.ZhaoSourceReservationFamilyState Erdos547b.ZhaoSourceMultiPendingRoot
open Erdos547b.ZhaoSourceSaturatedPacking
open Erdos547b.ZhaoStability Erdos547b.ZhaoDegreeForm Erdos547b.ZhaoEvenReducedPadding
open Erdos547b.ZhaoLemma611Full Erdos547b.ZhaoRichClaim61Lemma611
open Erdos547b.ZhaoSourceDegreeFormRootRows Erdos547b.ZhaoSourceDegreeFormBounds
open Erdos547b.ZhaoSourceOnlineMatchingRoot Erdos547b.ZhaoSourceParameterSchedule
open Erdos547b.ZhaoSourceEmbeddingHost Erdos547b.ZhaoSourceParentCleanup
open Erdos547b.ZhaoSourceRootExclusions Erdos547b.ZhaoSourceFreshChunkBounds

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G) (Q : Certificate W)
variable (S : CleanSourceWitness W Q) (s t : Fin 2)
variable {b r k : ℕ} (F : OrderedRootedForest b) (owner : Fin b → Fin r)

/-- Choose one fresh root, retain its parent adjacency and opposite-root
degree, and construct every served family's actual successor. The `none`
parent case is the initial-root construction. -/
theorem exists_synchronizedFamilyAdvance
    (hα : 0 < α) (hα1 : α ≤ 1 / 4)
    (hhost : hostN = 2 * q) (horder : orderThreshold α M ≤ q)
    (hk : k ≤ 3)
    (all : Fin k → Finset (MatchingEdge Q.claim67.M)) (family : Fin k → List (Fin b))
    (rootImage : Fin r → Fin hostN) (n : Fin r)
    (A : ∀ j, FamilyState W Q S (rootCluster W Q s) F owner (all j) (family j) rootImage n.val)
    (hsmall : ∀ i, F.size i ≤ freshBranchBound α W.clusterSize)
    (haway : ∀ j, all j ⊆ edgesAwayFromDistinguished Q.claim67.M
      (padFinset (large W)) (Sum.inl Q.A) (Sum.inl Q.B))
    (globalCount : ℕ) (hglobal : (Finset.univ.biUnion all).card ≤ globalCount)
    (hbudget : ∀ j, mass (fun i => (F.size i : ℝ)) (family j) ≤
      (∑ e ∈ all j, partOneCapacity W Q S (rootCluster W Q s) e) -
        (freshBranchBound α W.clusterSize : ℝ) * (all j).card -
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
      ∃ D : ∀ j, FamilyState W Q S (rootCluster W Q s) F owner (all j) (family j)
          (Function.update rootImage n z) (n.val + 1),
        ∀ j i hi, ((D j).currentPlacement W Q S (rootCluster W Q s) F owner).forestCopy.componentCopy i
            (processedFamily_mono owner (Nat.le_succ n.val) (family j) hi) =
          ((A j).currentPlacement W Q S (rootCluster W Q s) F owner).forestCopy.componentCopy i hi := by
  let fixed := Finset.univ.biUnion fun j : Fin k =>
    activeEdges W Q S (rootCluster W Q s) F owner (A j).active
  let remaining := Finset.univ.biUnion fun j : Fin k =>
    all j \ (A j).reservedEdges W Q S (rootCluster W Q s) F owner
  have hfixed : fixed ⊆ edgesAwayFromDistinguished Q.claim67.M
      (padFinset (large W)) (Sum.inl Q.A) (Sum.inl Q.B) := by
    intro e he
    obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp he
    exact haway j ((A j).active_subset hj)
  have hfixedCard : fixed.card ≤ 3 := by
    have hone (j : Fin k) : (activeEdges W Q S (rootCluster W Q s) F owner (A j).active).card ≤ 1 := by
      cases (A j).active <;> simp [activeEdges]
    calc
      fixed.card ≤ ∑ j : Fin k, (activeEdges W Q S (rootCluster W Q s) F owner (A j).active).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ _j : Fin k, 1 := Finset.sum_le_sum (fun j _ => hone j)
      _ = k := by simp
      _ ≤ 3 := hk
  have hremaining : remaining ⊆ edgesAwayFromDistinguished Q.claim67.M
      (padFinset (large W)) (Sum.inl Q.A) (Sum.inl Q.B) := by
    intro e he
    obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp he
    exact haway j (Finset.mem_sdiff.mp hj).1
  have hremainingCard : remaining.card ≤ globalCount := by
    apply (Finset.card_le_card (show remaining ⊆ Finset.univ.biUnion all from ?_)).trans hglobal
    intro e he
    obtain ⟨j, hj, hje⟩ := Finset.mem_biUnion.mp he
    exact Finset.mem_biUnion.mpr ⟨j, hj, (Finset.mem_sdiff.mp hje).1⟩
  have hchoose : ∃ z ∈ reservoir W Q s, z ∉ used ∧
      (∀ v, parent = some v → (embeddingHost W).Adj v z) ∧
      (∀ e ∈ fixed, EligibleRoot W Q S (rootCluster W Q s) e z) ∧
      ((padGraph (reduced W)).Adj (Sum.inl (rootCluster W Q s)) (Sum.inl (rootCluster W Q t)) →
        ((densityCutoff α : ℝ) - (epsilon α : ℝ)) * (sourceQuota W : ℝ) ≤
          (#((reservoir W Q t).filter ((embeddingHost W).Adj z)) : ℝ)) ∧
      ∃ bad ⊆ remaining, (bad.card : ℝ) ≤ 2 * (rootTypicality α : ℝ) * remaining.card ∧
        ∀ e ∈ remaining \ bad, EligibleRoot W Q S (rootCluster W Q s) e z := by
    cases parent with
    | none =>
      obtain ⟨z, hz, hfresh, hfixedGood, hdegree, bad, hb, hcount, hgood⟩ :=
        exists_initial_multi_eligible_root W Q hα hα1 S s t fixed hfixed hfixedCard used hused
          remaining hremaining
      exact ⟨z, hz, hfresh, by simp, hfixedGood, hdegree, bad, hb, hcount, hgood⟩
    | some v =>
      obtain ⟨z, hz, hadj, hfresh, hfixedGood, hdegree, bad, hb, hcount, hgood⟩ :=
        exists_multi_eligible_after_parent_degree W Q hα hα1 S s t v (hparent v rfl)
          fixed hfixed hfixedCard used hused remaining hremaining
      refine ⟨z, hz, hfresh, ?_, hfixedGood, hdegree, bad, hb, hcount, hgood⟩
      intro v' hv
      have h := Option.some.inj hv
      exact h ▸ hadj
  obtain ⟨z, hz, hfresh, hAdj, hfixedGood, hdegree, bad, _, hbadCount, hgood⟩ := hchoose
  have hδ : (0 : ℝ) ≤ rootTypicality α := by
    exact_mod_cast (rootTypicality_margin hα hα1).1.le
  have hbadGlobal : (bad.card : ℝ) ≤ 2 * (rootTypicality α : ℝ) * globalCount := by
    have hc : (remaining.card : ℝ) ≤ globalCount := by exact_mod_cast hremainingCard
    exact hbadCount.trans (mul_le_mul_of_nonneg_left hc (by positivity))
  have hstep (j : Fin k) :
      ∃ D : FamilyState W Q S (rootCluster W Q s) F owner (all j) (family j)
          (Function.update rootImage n z) (n.val + 1),
        ∀ i hi, (D.currentPlacement W Q S (rootCluster W Q s) F owner).forestCopy.componentCopy i
            (processedFamily_mono owner (Nat.le_succ n.val) (family j) hi) =
          ((A j).currentPlacement W Q S (rootCluster W Q s) F owner).forestCopy.componentCopy i hi := by
    let unused := all j \ (A j).reservedEdges W Q S (rootCluster W Q s) F owner
    apply exists_familyAdvance W Q S (rootCluster W Q s) F owner rootImage n (A j)
      hα hα1 hhost horder (rootCluster_cases W Q s) hsmall (haway j) globalCount (hbudget j) z
      (bad := bad ∩ unused)
    · intro x hx _
      apply hfixedGood
      apply Finset.mem_biUnion.mpr
      refine ⟨j, Finset.mem_univ _, ?_⟩
      rw [hx]
      exact Finset.mem_singleton.mpr rfl
    · exact Finset.inter_subset_right
    · have hc : ((bad ∩ unused).card : ℝ) ≤ bad.card := by
        exact_mod_cast Finset.card_le_card (Finset.inter_subset_left (s₁ := bad) (s₂ := unused))
      exact hc.trans hbadGlobal
    · intro e he
      obtain ⟨hu, hnot⟩ := Finset.mem_sdiff.mp he
      apply hgood e
      refine Finset.mem_sdiff.mpr ⟨Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, hu⟩, ?_⟩
      intro hb
      exact hnot (Finset.mem_inter.mpr ⟨hb, hu⟩)
  choose D hD using hstep
  exact ⟨z, hz, hfresh, hAdj, hdegree, D, hD⟩

end Erdos547b.ZhaoSourceSynchronizedFamilyAdvance

#print axioms Erdos547b.ZhaoSourceSynchronizedFamilyAdvance.exists_synchronizedFamilyAdvance
