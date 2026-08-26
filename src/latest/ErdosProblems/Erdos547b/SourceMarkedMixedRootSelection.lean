/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceMarkedRootExclusions
import ErdosProblems.Erdos547b.SourceMixedRootSelection

/-!
# One common root for marked groups and ordinary families

The additional many-bad-groups exclusion fits the existing parent-pool
budget. Ordinary matching selection is performed inside the same live pool.
-/

open scoped SimpleGraph BigOperators Classical
noncomputable section

namespace Erdos547b.ZhaoSourceMarkedMixedRootSelection

open Finset SimpleGraph
open Erdos547b.ZhaoSourceDegreeFormRootRows Erdos547b.ZhaoSourceNearFullMatching
open Erdos547b.ZhaoSourcePrivatePairGeometry Erdos547b.ZhaoSourceMarkedAvailableSets
open Erdos547b.ZhaoSourceMarkedRootExclusions Erdos547b.ZhaoSourceEmbeddingHost
open Erdos547b.ZhaoSourceParentCleanup Erdos547b.ZhaoSourceParameterSchedule
open Erdos547b.ZhaoSourceMixedRootRequirements Erdos547b.ZhaoSourceMixedRootSelection
open Erdos547b.ZhaoSourceRootReconnection Erdos547b.ZhaoSourceRootExclusions
open Erdos547b.ZhaoSourcePendingInitialRoot Erdos547b.ZhaoSourceLiveMatchingRoot
open Erdos547b.ZhaoSourcePendingRootSelection
open Erdos547b.ZhaoSourceActualPartThreeStep Erdos547b.ZhaoSourceActualChunkEmbedding
open Erdos547b.ZhaoStability Erdos547b.ZhaoEvenReducedPadding
open Erdos547b.ZhaoLemma611Full Erdos547b.ZhaoRichClaim61Lemma611

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G) (Q : Certificate W) (S : CleanSourceWitness W Q)
variable {fb : ℝ} (O : Output W Q S fb)
variable {C : Finset (EvenPadding (Index W))} (P : Geometry W Q S O C)

theorem mixedForbidden_sharp (hα : 0 < α) (hα1 : α ≤ 1 / 4)
    (s t : Fin 2) {k : ℕ} (hk : k ≤ 3) (requirements : Fin k → Requirement W Q)
    (hvalid : ∀ j, requirementValid W Q S (rootCluster W Q s) (requirements j))
    (used : Finset (Fin hostN)) (hused : (used.card : ℝ) ≤ (epsilon α : ℝ) * W.clusterSize) :
    ((mixedForbidden W Q S s t requirements used).card : ℝ) ≤
      8 * (epsilon α : ℝ) * W.clusterSize := by
  let bad := Finset.univ.biUnion (fun j => requirementBad W Q S (rootCluster W Q s) (requirements j))
  have he : (0 : ℝ) ≤ epsilon α := by exact_mod_cast (parameter_pos hα).2.2.2.2.2.2.2.le
  have hbad : (bad.card : ℝ) ≤ (k : ℝ) * (2 * (epsilon α : ℝ) * W.clusterSize) := by
    calc
      _ ≤ ∑ j, ((requirementBad W Q S (rootCluster W Q s) (requirements j)).card : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
          (s := (Finset.univ : Finset (Fin k)))
          (t := fun j => requirementBad W Q S (rootCluster W Q s) (requirements j))
      _ ≤ ∑ _j : Fin k, 2 * (epsilon α : ℝ) * W.clusterSize :=
        Finset.sum_le_sum (fun j _ => card_requirementBad_le W Q hα hα1 S _
          (rootCluster_cases W Q s) (requirements j) (hvalid j))
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hkR : (k : ℝ) ≤ 3 := by exact_mod_cast hk
  have hkScale := mul_le_mul_of_nonneg_right hkR
    (show 0 ≤ 2 * (epsilon α : ℝ) * W.clusterSize by positivity)
  have hr := card_badToward_le W Q hα hα1 (Sum.inl (rootCluster W Q s)) t
  change ((badToward W Q (Sum.inl (rootCluster W Q s)) t).card : ℝ) ≤
    (epsilon α : ℝ) * (whole W (rootCluster W Q s)).card at hr
  rw [whole_card] at hr
  have hu : ((mixedForbidden W Q S s t requirements used).card : ℝ) ≤
      (used.card : ℝ) + bad.card + (badToward W Q (Sum.inl (rootCluster W Q s)) t).card := by
    exact_mod_cast (Finset.card_union_le (used ∪ bad)
      (badToward W Q (Sum.inl (rootCluster W Q s)) t)).trans
        (Nat.add_le_add_right (Finset.card_union_le used bad) _)
  nlinarith only [hused, hbad, hkScale, hr, hu]

def combinedForbidden (t : Fin 2) {k : ℕ} (requirements : Fin k → Requirement W Q)
    (used : Finset (Fin hostN)) :=
  mixedForbidden W Q S 0 t requirements used ∪ excludedRoots W Q S O P

theorem combinedForbidden_card_le (hα : 0 < α) (hα1 : α ≤ 1 / 4)
    (t : Fin 2) {k : ℕ} (hk : k ≤ 3) (requirements : Fin k → Requirement W Q)
    (hvalid : ∀ j, requirementValid W Q S (rootCluster W Q 0) (requirements j))
    (used : Finset (Fin hostN)) (hused : (used.card : ℝ) ≤ (epsilon α : ℝ) * W.clusterSize) :
    ((combinedForbidden W Q S O P t requirements used).card : ℝ) ≤
      (3 * (rootTypicality α : ℝ) + 6 * (epsilon α : ℝ)) * W.clusterSize := by
  have hm := mixedForbidden_sharp W Q S hα hα1 0 t hk requirements hvalid used hused
  have hg := excludedRoots_card_le W Q S O P hα hα1
  have he := mul_le_mul_of_nonneg_right (typicality_bounds hα hα1).2.2.1
    (Nat.cast_nonneg W.clusterSize : (0 : ℝ) ≤ W.clusterSize)
  have hu : ((combinedForbidden W Q S O P t requirements used).card : ℝ) ≤
      (mixedForbidden W Q S 0 t requirements used).card + (excludedRoots W Q S O P).card := by
    exact_mod_cast Finset.card_union_le (mixedForbidden W Q S 0 t requirements used) (excludedRoots W Q S O P)
  nlinarith only [hm, hg, he, hu]

theorem exists_mixed_marked_root (hα : 0 < α) (hα1 : α ≤ 1 / 4)
    (hCV1 : C ⊆ O.D.V1) (t : Fin 2) {k : ℕ} (hk : k ≤ 3)
    (requirements : Fin k → Requirement W Q)
    (hvalid : ∀ j, requirementValid W Q S (rootCluster W Q 0) (requirements j))
    (used : Finset (Fin hostN)) (hused : (used.card : ℝ) ≤ (epsilon α : ℝ) * W.clusterSize)
    (parent : Option (Fin hostN))
    (hparent : ∀ v, parent = some v →
      ((densityCutoff α : ℝ) - (epsilon α : ℝ)) * (sourceQuota W : ℝ) ≤
        ((reservoir W Q 0).filter ((embeddingHost W).Adj v)).card)
    (remaining : Finset (MatchingEdge Q.claim67.M))
    (hremaining : remaining ⊆ edgesAwayFromDistinguished Q.claim67.M (padFinset (large W))
      (Sum.inl Q.A) (Sum.inl Q.B))
    (raw : MatchingEdge Q.claim67.M → Fin 2 → Finset (Fin hostN))
    (hraw : ∀ e ∈ remaining, ∀ c, raw e c ⊆ edgeWhole W Q e c)
    (hrawLarge : ∀ e ∈ remaining, ∀ c, (epsilon α : ℝ) * W.clusterSize ≤ (raw e c).card) :
    ∃ z ∈ reservoir W Q 0, z ∉ used ∧
      (∀ v, parent = some v → (embeddingHost W).Adj v z) ∧
      (∀ j, requirementGood W Q S (rootCluster W Q 0) (requirements j) z) ∧
      ((padGraph (reduced W)).Adj (Sum.inl (rootCluster W Q 0)) (Sum.inl (rootCluster W Q t)) →
        ((densityCutoff α : ℝ) - (epsilon α : ℝ)) * (sourceQuota W : ℝ) ≤
          ((reservoir W Q t).filter ((embeddingHost W).Adj z)).card) ∧
      16 * (badGroups W Q S O P z).card ≤ C.card ∧
      (∀ x, x ∉ badGroups W Q S O P z →
        (1 - 2 * (eta α : ℝ) - (gamma α : ℝ)) * W.clusterSize ≤
          (((whole W (P.center x)).filter ((embeddingHost W).Adj z)).card : ℝ)) ∧
      ∃ bad ⊆ remaining, (bad.card : ℝ) ≤ 2 * (rootTypicality α : ℝ) * remaining.card ∧
        ∀ e ∈ remaining \ bad, EligibleLiveRoot W Q S (rootCluster W Q 0) e (raw e) z := by
  let excluded := combinedForbidden W Q S O P t requirements used
  let pool := match parent with
    | none => reservoir W Q 0 \ excluded
    | some v => parentPool W Q 0 v excluded
  have hexcluded : (excluded.card : ℝ) ≤
      (3 * (rootTypicality α : ℝ) + 6 * (epsilon α : ℝ)) * W.clusterSize :=
    combinedForbidden_card_le W Q S O P hα hα1 t hk requirements hvalid used hused
  have hpoolFacts : ∀ z ∈ pool, z ∈ reservoir W Q 0 ∧ z ∉ excluded ∧
      ∀ v, parent = some v → (embeddingHost W).Adj v z := by
    intro z hz
    cases parent with
    | none => exact ⟨(Finset.mem_sdiff.mp hz).1, (Finset.mem_sdiff.mp hz).2, by simp⟩
    | some v =>
        obtain ⟨hzR, hvz, hn⟩ := (mem_parentPool W Q).mp hz
        exact ⟨hzR, hn, fun v' hv => Option.some.inj hv ▸ hvz⟩
  have hpool : pool ⊆ reservoir W Q 0 \ mixedForbidden W Q S 0 t requirements used := by
    intro z hz
    have h := hpoolFacts z hz
    exact Finset.mem_sdiff.mpr ⟨h.1, fun hb => h.2.1 (Finset.mem_union_left _ hb)⟩
  have hpoolCard : (rootTypicality α : ℝ) * W.clusterSize < pool.card := by
    cases parent with
    | none => exact initialPool_large W Q hα hα1 0 excluded hexcluded
    | some v => exact parentPool_large_of_degree W Q hα hα1 0 v (hparent v rfl) excluded hexcluded
  obtain ⟨z, hz, hfresh, hactive, hdegree, hremainingGood⟩ := exists_mixed_root_from_pool W Q
    hα hα1 S 0 t requirements hvalid used remaining hremaining raw hraw hrawLarge pool hpool hpoolCard
  have hfacts := hpoolFacts z hz
  have hzA : z ∈ whole W Q.A := by
    simpa [rootCluster] using reservoir_subset W Q 0 hfacts.1
  have hnotGroup : z ∉ excludedRoots W Q S O P :=
    fun hb => hfacts.2.1 (Finset.mem_union_right _ hb)
  obtain ⟨hcount, hgood⟩ := good_groups_of_not_excluded W Q S O P hα hα1 hCV1 z hzA hnotGroup
  exact ⟨z, hfacts.1, hfresh, hfacts.2.2, hactive, hdegree, hcount, hgood, hremainingGood⟩

end Erdos547b.ZhaoSourceMarkedMixedRootSelection

#print axioms Erdos547b.ZhaoSourceMarkedMixedRootSelection.combinedForbidden_card_le
#print axioms Erdos547b.ZhaoSourceMarkedMixedRootSelection.exists_mixed_marked_root
