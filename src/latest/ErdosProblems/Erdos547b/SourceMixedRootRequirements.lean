/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceLiveMatchingRoot
import ErdosProblems.Erdos547b.SourceMultiPendingRoot

/-!
# Concrete mixed pending-root constraints

A threshold chunk tests whole endpoints; an Appendix chunk tests its
current live subsets. Missing chunks impose no condition. Both genuine
requirements cost at most two epsilon-cluster exceptional sets.
-/

open scoped SimpleGraph BigOperators Classical
noncomputable section

namespace Erdos547b.ZhaoSourceMixedRootRequirements

open Finset SimpleGraph
open Erdos547b.ZhaoStability Erdos547b.ZhaoDegreeForm Erdos547b.ZhaoEvenReducedPadding
open Erdos547b.ZhaoLemma611Full Erdos547b.ZhaoRichClaim61Lemma611
open Erdos547b.ZhaoSourceParameterSchedule Erdos547b.ZhaoSourceDegreeFormRootRows
open Erdos547b.ZhaoSourceEmbeddingHost Erdos547b.ZhaoSourceActualChunkEmbedding
open Erdos547b.ZhaoSourceOnlineMatchingRoot Erdos547b.ZhaoSourceActualPartThreeStep
open Erdos547b.ZhaoSourceParentCleanup Erdos547b.ZhaoSourceRootExclusions
open Erdos547b.ZhaoSourceLiveRootExclusions

inductive PendingRequirement (V Edge : Type) where
  | threshold (edge : Edge)
  | appendix (edge : Edge) (live : Fin 2 → Finset V)

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G) (Q : Certificate W)

abbrev Requirement := Option (PendingRequirement (Fin hostN) (MatchingEdge Q.claim67.M))

def requirementBad (S : CleanSourceWitness W Q) (C : Index W) (r : Requirement W Q) : Finset (Fin hostN) :=
  match r with
  | none => ∅
  | some (.threshold e) => badForEdge W Q S C e
  | some (.appendix e live) => badForLiveEdge W Q C e live

def requirementGood (S : CleanSourceWitness W Q) (C : Index W) (r : Requirement W Q)
    (z : Fin hostN) : Prop :=
  match r with
  | none => True
  | some (.threshold e) => EligibleRoot W Q S C e z
  | some (.appendix e live) => EligibleLiveRoot W Q S C e live z

def requirementValid (S : CleanSourceWitness W Q) (C : Index W) (r : Requirement W Q) : Prop :=
  match r with
  | none => True
  | some (.threshold e) => e ∈ edgesAwayFromDistinguished Q.claim67.M (padFinset (large W))
      (Sum.inl Q.A) (Sum.inl Q.B)
  | some (.appendix e live) =>
      e ∈ edgesAwayFromDistinguished Q.claim67.M (padFinset (large W)) (Sum.inl Q.A) (Sum.inl Q.B) ∧
        ∀ c, 0 < rootDensity W S (Sum.inl C) (edgeVertex W Q e c) ∧
          live c ⊆ edgeWhole W Q e c ∧ (epsilon α : ℝ) * W.clusterSize ≤ (live c).card

theorem card_requirementBad_le (hα : 0 < α) (hα1 : α ≤ 1 / 4)
    (S : CleanSourceWitness W Q) (C : Index W) (hC : C = Q.A ∨ C = Q.B)
    (r : Requirement W Q) (hr : requirementValid W Q S C r) :
    ((requirementBad W Q S C r).card : ℝ) ≤ 2 * (epsilon α : ℝ) * W.clusterSize := by
  cases r with
  | none =>
      have he : (0 : ℝ) ≤ epsilon α := by exact_mod_cast (parameter_pos hα).2.2.2.2.2.2.2.le
      simp only [requirementBad, Finset.card_empty, Nat.cast_zero]
      positivity
  | some r =>
      cases r with
      | threshold e => exact card_badForEdge_le W Q hα hα1 S C hC e hr
      | appendix e live =>
          exact card_badForLiveEdge_le W Q hα hα1 S C hC e hr.1 live
            (fun c => (hr.2 c).1) (fun c => (hr.2 c).2.1) (fun c => (hr.2 c).2.2)

theorem requirementGood_of_not_mem
    (S : CleanSourceWitness W Q) (C : Index W) (hC : C = Q.A ∨ C = Q.B)
    (r : Requirement W Q) (hr : requirementValid W Q S C r)
    (z : Fin hostN) (hz : z ∈ clusterVertices (assignment W) C)
    (hgood : z ∉ requirementBad W Q S C r) : requirementGood W Q S C r z := by
  cases r with
  | none => trivial
  | some r =>
      cases r with
      | threshold e => exact eligibleRoot_of_not_mem_badForEdge W Q S C hC e hr z hz hgood
      | appendix e live =>
          exact eligibleLiveRoot_of_not_mem_bad W Q S C hC e hr.1 live
            (fun c => (hr.2 c).1) z hz hgood

def mixedForbidden (S : CleanSourceWitness W Q) (s t : Fin 2) {k : ℕ}
    (requirements : Fin k → Requirement W Q) (used : Finset (Fin hostN)) : Finset (Fin hostN) :=
  used ∪ Finset.univ.biUnion (fun j => requirementBad W Q S (rootCluster W Q s) (requirements j)) ∪
    badToward W Q (Sum.inl (rootCluster W Q s)) t

/-- Three whole/live requirements fit the unchanged root-pool margin. -/
theorem card_mixedForbidden_le (hα : 0 < α) (hα1 : α ≤ 1 / 4)
    (S : CleanSourceWitness W Q) (s t : Fin 2) {k : ℕ} (hk : k ≤ 3)
    (requirements : Fin k → Requirement W Q)
    (hvalid : ∀ j, requirementValid W Q S (rootCluster W Q s) (requirements j))
    (used : Finset (Fin hostN)) (hused : (used.card : ℝ) ≤ (epsilon α : ℝ) * W.clusterSize) :
    ((mixedForbidden W Q S s t requirements used).card : ℝ) ≤
      (3 * (rootTypicality α : ℝ) + 6 * (epsilon α : ℝ)) * W.clusterSize := by
  let bad := Finset.univ.biUnion (fun j => requirementBad W Q S (rootCluster W Q s) (requirements j))
  have he : (0 : ℝ) ≤ epsilon α := by exact_mod_cast (parameter_pos hα).2.2.2.2.2.2.2.le
  have hN : (0 : ℝ) ≤ W.clusterSize := Nat.cast_nonneg _
  have hbad : (bad.card : ℝ) ≤ (k : ℝ) * (2 * (epsilon α : ℝ) * W.clusterSize) := by
    calc
      _ ≤ ∑ j, ((requirementBad W Q S (rootCluster W Q s) (requirements j)).card : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
          (s := (Finset.univ : Finset (Fin k)))
          (t := fun j => requirementBad W Q S (rootCluster W Q s) (requirements j))
      _ ≤ ∑ _j : Fin k, 2 * (epsilon α : ℝ) * W.clusterSize :=
        Finset.sum_le_sum (fun j _ => card_requirementBad_le W Q hα hα1 S _
          (rootCluster_cases W Q s) (requirements j) (hvalid j))
      _ = _ := by simp [nsmul_eq_mul]
  have hkReal : (k : ℝ) ≤ 3 := by exact_mod_cast hk
  have hbadSix : (bad.card : ℝ) ≤ 6 * (epsilon α : ℝ) * W.clusterSize := by
    have hm := mul_le_mul_of_nonneg_right hkReal (by positivity : 0 ≤ 2 * (epsilon α : ℝ) * W.clusterSize)
    nlinarith only [hbad, hm]
  have hr := card_badToward_le W Q hα hα1 (Sum.inl (rootCluster W Q s)) t
  have hc : (padCluster (clusterVertices (assignment W)) (Sum.inl (rootCluster W Q s))).card =
      W.clusterSize := by
    change (clusterVertices (assignment W) (rootCluster W Q s)).card = _
    rw [clusterVertices_partitionAssignment]
    exact W.equal_clusters _ (rootCluster W Q s).2
  rw [hc] at hr
  have hu : ((mixedForbidden W Q S s t requirements used).card : ℝ) ≤
      (used.card : ℝ) + bad.card + (badToward W Q (Sum.inl (rootCluster W Q s)) t).card := by
    exact_mod_cast (Finset.card_union_le (used ∪ bad)
      (badToward W Q (Sum.inl (rootCluster W Q s)) t)).trans
        (Nat.add_le_add_right (Finset.card_union_le used bad) _)
  have hδ := rootTypicality_margin hα hα1
  have hσ := (reservoir_cleanup_bounds hα hα1).2.1
  have hδ1 : rootTypicality α ≤ 1 := by linarith only [hδ.2, hσ]
  have heδQ : epsilon α ≤ rootTypicality α := by
    have hm := mul_le_mul_of_nonneg_left hδ1 hδ.1.le
    have hs := rootTypicality_sq α
    nlinarith only [hm, hs]
  have heδ : (epsilon α : ℝ) ≤ rootTypicality α := by exact_mod_cast heδQ
  have hm := mul_le_mul_of_nonneg_right heδ hN
  linarith only [hu, hused, hbadSix, hr, hm]

theorem requirements_good_of_not_mem_mixedForbidden
    (S : CleanSourceWitness W Q) (s t : Fin 2) {k : ℕ}
    (requirements : Fin k → Requirement W Q)
    (hvalid : ∀ j, requirementValid W Q S (rootCluster W Q s) (requirements j))
    (used : Finset (Fin hostN)) (z : Fin hostN) (hz : z ∈ reservoir W Q s)
    (hgood : z ∉ mixedForbidden W Q S s t requirements used) :
    ∀ j, requirementGood W Q S (rootCluster W Q s) (requirements j) z := by
  intro j
  apply requirementGood_of_not_mem W Q S _ (rootCluster_cases W Q s) (requirements j)
    (hvalid j) z (reservoir_subset W Q s hz)
  intro hbad
  exact hgood (Finset.mem_union_left _ (Finset.mem_union_right _
    (Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ j, hbad⟩)))

end Erdos547b.ZhaoSourceMixedRootRequirements

#print axioms Erdos547b.ZhaoSourceMixedRootRequirements.card_requirementBad_le
#print axioms Erdos547b.ZhaoSourceMixedRootRequirements.requirementGood_of_not_mem
#print axioms Erdos547b.ZhaoSourceMixedRootRequirements.card_mixedForbidden_le
#print axioms Erdos547b.ZhaoSourceMixedRootRequirements.requirements_good_of_not_mem_mixedForbidden
