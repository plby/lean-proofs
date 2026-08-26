/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceMarkedGroupCapacity
import ErdosProblems.Erdos547b.SourceMixedRootRequirements

/-!
# A single small root exclusion for all private marked groups

Double counting deletes roots bad for too many intermediate clusters.
This costs only rootTypicality times one cluster, independently of the
number of private groups. The same deletion fits the mixed-root budget.
-/

open scoped SimpleGraph BigOperators Classical
noncomputable section

namespace Erdos547b.ZhaoSourceMarkedRootExclusions

open Finset SimpleGraph
open Erdos547b.ZhaoSourceDegreeFormRootRows Erdos547b.ZhaoSourceNearFullMatching
open Erdos547b.ZhaoSourcePrivatePairGeometry Erdos547b.ZhaoSourceMarkedAvailableSets
open Erdos547b.ZhaoSourceMarkedGroupCapacity Erdos547b.ZhaoSourceEmbeddingHost
open Erdos547b.ZhaoSourceParentCleanup Erdos547b.ZhaoSourceParameterSchedule
open Erdos547b.ZhaoSourceOnlineRootSelection Erdos547b.ZhaoSourceRootIncidence
open Erdos547b.ZhaoSourceMixedRootRequirements Erdos547b.ZhaoSourceRootExclusions
open Erdos547b.ZhaoSourceActualChunkEmbedding Erdos547b.ZhaoRichClaim61Lemma611
open Erdos547b.ZhaoStability Erdos547b.ZhaoEvenReducedPadding
open Erdos547b.ZhaoLemma59HierarchicalCanonical.HierarchicalSegmentForest

theorem typicality_bounds {α : ℚ} (hα : 0 < α) (hα1 : α ≤ 1 / 4) :
    0 < (rootTypicality α : ℝ) ∧ 16 * (rootTypicality α : ℝ) ≤ 1 ∧
      (epsilon α : ℝ) ≤ (rootTypicality α : ℝ) ∧ 2 * (epsilon α : ℝ) ≤ (gamma α : ℝ) := by
  have hd := rootTypicality_margin hα hα1
  have hσ := (reservoir_cleanup_bounds hα hα1).2.1
  have hd1 : rootTypicality α ≤ 1 := by linarith only [hd.2, hσ]
  have he : epsilon α ≤ rootTypicality α := by
    have h := mul_le_mul_of_nonneg_left hd1 hd.1.le
    nlinarith only [h, rootTypicality_sq α]
  have heg := (parameter_upper_bounds hα hα1).2.2.2.2.2.2
  have hg := (parameter_pos hα).2.2.2.2.2.2.1
  refine ⟨by exact_mod_cast hd.1, ?_, by exact_mod_cast he, ?_⟩
  · have h : 16 * rootTypicality α ≤ 1 := by linarith only [hd.2, hσ]
    exact_mod_cast h
  · have h : 2 * epsilon α ≤ gamma α := by linarith only [heg, hg]
    exact_mod_cast h

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G) (Q : Certificate W) (S : CleanSourceWitness W Q)
variable {fb : ℝ} (O : Output W Q S fb)
variable {C : Finset (EvenPadding (Index W))} (P : Geometry W Q S O C)

def badAt (x : {c // c ∈ C}) : Finset (Fin hostN) :=
  targetLowDegreeVertices (embeddingHost W) (epsilon α : ℝ)
    (whole W Q.A) (whole W (P.center x)) (whole W Q.A) (whole W (P.center x))

def badGroups (z : Fin hostN) : Finset {c // c ∈ C} :=
  badTargets Finset.univ (badAt W Q S O P) z

def excludedRoots : Finset (Fin hostN) :=
  manyBadRoots (whole W Q.A) Finset.univ (badAt W Q S O P) (rootTypicality α : ℝ)

theorem badAt_card_le (hα : 0 < α) (hα1 : α ≤ 1 / 4) (x : {c // c ∈ C}) :
    ((badAt W Q S O P x).card : ℝ) ≤ (epsilon α : ℝ) * W.clusterSize := by
  have he : (epsilon α : ℝ) ≤ 1 := by
    linarith only [(Erdos547b.ZhaoSourceMarkedGroupCapacity.parameter_bounds hα hα1).2.2.2]
  have hlarge (c : Index W) : (epsilon α : ℝ) * (whole W c).card ≤ (whole W c).card := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right he (Nat.cast_nonneg (whole W c).card)
  have h := card_targetLowDegreeVertices_le (embeddingHost W)
    (embedding_pair_of_adj W (P.center_adj x).symm).1
    (Finset.Subset.refl _) (Finset.Subset.refl _) (hlarge Q.A) (hlarge (P.center x))
  simpa only [badAt, whole_card] using h

theorem excludedRoots_card_le (hα : 0 < α) (hα1 : α ≤ 1 / 4) :
    ((excludedRoots W Q S O P).card : ℝ) ≤ (rootTypicality α : ℝ) * W.clusterSize := by
  have hs : (epsilon α : ℝ) ≤ (rootTypicality α : ℝ) ^ 2 := by
    exact_mod_cast (rootTypicality_sq α).symm.le
  have h := card_manyBadRoots_le (whole W Q.A) Finset.univ (badAt W Q S O P)
    (epsilon α : ℝ) (rootTypicality α : ℝ) (typicality_bounds hα hα1).1 hs
    (fun x _ => by simpa only [whole_card] using badAt_card_le W Q S O P hα hα1 x)
  simpa only [excludedRoots, whole_card] using h

theorem ne_roots_of_mem_V1 {x : EvenPadding (Index W)} (hx : x ∈ O.D.V1) :
    x ≠ Sum.inl Q.A ∧ x ≠ Sum.inl Q.B := by
  obtain ⟨e, he, h0 | h1⟩ := (mem_matchingSupport O.D.Min x).mp hx
  · subst x
    exact endpoint_ne_distinguished_of_mem_away Q.claim67.M (padFinset (large W))
      (Sum.inl Q.A) (Sum.inl Q.B) (O.min_subset_away W Q S he) 0
  · subst x
    exact endpoint_ne_distinguished_of_mem_away Q.claim67.M (padFinset (large W))
      (Sum.inl Q.A) (Sum.inl Q.B) (O.min_subset_away W Q S he) 1

theorem good_groups_of_not_excluded (hα : 0 < α) (hα1 : α ≤ 1 / 4)
    (hCV1 : C ⊆ O.D.V1) (z : Fin hostN) (hz : z ∈ whole W Q.A)
    (hnot : z ∉ excludedRoots W Q S O P) :
    16 * (badGroups W Q S O P z).card ≤ C.card ∧
      ∀ x, x ∉ badGroups W Q S O P z →
        (1 - 2 * (eta α : ℝ) - (gamma α : ℝ)) * W.clusterSize ≤
          (((whole W (P.center x)).filter ((embeddingHost W).Adj z)).card : ℝ) := by
  have hcount : ((badGroups W Q S O P z).card : ℝ) ≤ (rootTypicality α : ℝ) * C.card := by
    apply le_of_not_gt
    intro h
    apply hnot
    apply Finset.mem_filter.mpr
    exact ⟨hz, by simpa only [badGroups, Finset.card_univ, Fintype.card_coe] using h⟩
  constructor
  · have hscale := mul_le_mul_of_nonneg_right (typicality_bounds hα hα1).2.1
      (Nat.cast_nonneg C.card : (0 : ℝ) ≤ C.card)
    have h : (16 : ℝ) * (badGroups W Q S O P z).card ≤ C.card := by
      nlinarith only [hcount, hscale]
    exact_mod_cast h
  · intro x hx
    have hnotBad : z ∉ badAt W Q S O P x := by
      intro hb
      exact hx (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb⟩)
    have hlower := target_degree_ge_of_not_mem_lowDegree (embeddingHost W) (epsilon α : ℝ)
      (whole W Q.A) (whole W (P.center x)) (whole W Q.A) (whole W (P.center x)) z hz hnotBad
    rw [whole_card] at hlower
    have hxV1 : Sum.inl (P.center x) ∈ O.D.V1 := by rw [← P.center_eq x]; exact hCV1 x.2
    have hne := ne_roots_of_mem_V1 W Q S O hxV1
    have hd := P.center_density x
    have hη := (Erdos547b.ZhaoSourceNearFullNumerics.parameter_bounds hα hα1).2.1
    have hpos : 0 < rootDensity W S (Sum.inl Q.A) (Sum.inl (P.center x)) := by
      linarith only [hd, hη]
    have hsource := (source_pair_A W S hne.1 hne.2 hpos).2.2
    change rootDensity W S (Sum.inl Q.A) (Sum.inl (P.center x)) ≤
      ((embeddingHost W).edgeDensity (whole W Q.A) (whole W (P.center x)) : ℝ) +
        (epsilon α : ℝ) at hsource
    have hcoeff : 1 - 2 * (eta α : ℝ) - (gamma α : ℝ) ≤
        ((embeddingHost W).edgeDensity (whole W Q.A) (whole W (P.center x)) : ℝ) - (epsilon α : ℝ) := by
      linarith only [hd, hsource, (typicality_bounds hα hα1).2.2.2]
    exact (mul_le_mul_of_nonneg_right hcoeff (Nat.cast_nonneg W.clusterSize)).trans hlower

end Erdos547b.ZhaoSourceMarkedRootExclusions

#print axioms Erdos547b.ZhaoSourceMarkedRootExclusions.excludedRoots_card_le
#print axioms Erdos547b.ZhaoSourceMarkedRootExclusions.good_groups_of_not_excluded
