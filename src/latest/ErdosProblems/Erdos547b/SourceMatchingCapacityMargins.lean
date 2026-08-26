/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceMatchingPendingPlan
import ErdosProblems.Erdos547b.SourceAbsoluteBadBudget

/-! # The three-gamma reserve for an arbitrary physical matching -/

open scoped SimpleGraph BigOperators Classical
noncomputable section

namespace Erdos547b.ZhaoSourceMatchingCapacityMargins

open Finset SimpleGraph Erdos547b.ZhaoStability Erdos547b.ZhaoDegreeForm
open Erdos547b.ZhaoEvenReducedPadding Erdos547b.ZhaoLemma611Full
open Erdos547b.ZhaoRichClaim61Lemma611
open Erdos547b.ZhaoSourceParameterSchedule Erdos547b.ZhaoSourceDegreeFormRootRows
open Erdos547b.ZhaoSourceMatchingGeometry Erdos547b.ZhaoSourceMatchingPendingPlan
open Erdos547b.ZhaoSourceActualChunkEmbedding Erdos547b.ZhaoSourceFreshChunkBounds
open Erdos547b.ZhaoSourceAbsoluteBadBudget

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G) (Q : Certificate W) (S : CleanSourceWitness W Q)
variable (P : (padGraph (reduced W)).Subgraph) (C : Index W)

def pairWeight (e : MatchingEdge P) : ℝ :=
  (rootDensity W S (Sum.inl C) (pairVertex W P e 0) +
    rootDensity W S (Sum.inl C) (pairVertex W P e 1)) * W.clusterSize

theorem pairWeight_nonneg (e : MatchingEdge P) : 0 ≤ pairWeight W Q S P C e := by
  unfold pairWeight rootDensity twoRootSourceDensity rootedSourceDensity
  split_ifs <;> positivity

theorem pairWeight_le (hC : C = Q.A ∨ C = Q.B) (e : MatchingEdge P) :
    pairWeight W Q S P C e ≤ 2 * W.clusterSize := by
  have h0 := source_entry_le_one W Q S C hC (pairVertex W P e 0)
  have h1 := source_entry_le_one W Q S C hC (pairVertex W P e 1)
  exact mul_le_mul_of_nonneg_right (by linarith only [h0, h1]) (Nat.cast_nonneg W.clusterSize)

theorem capacity_eq_weight_sub (e : MatchingEdge P) :
    capacity W Q P S C e = pairWeight W Q S P C e -
      (2 * (gamma α : ℝ) + 3 * (epsilon α : ℝ)) * W.clusterSize := by
  unfold capacity pairWeight
  ring

theorem effectiveCapacity_lower (hα : 0 < α) (hα1 : α ≤ 1 / 4)
    (edges : Finset (MatchingEdge P)) (globalCount : ℕ)
    (hedges : (W.clusterSize : ℝ) * edges.card ≤ q)
    (hglobal : (W.clusterSize : ℝ) * globalCount ≤ q) :
    (∑ e ∈ edges, pairWeight W Q S P C e) - 3 * (gamma α : ℝ) * q ≤
      (∑ e ∈ edges, capacity W Q P S C e) -
        (freshBranchBound α W.clusterSize : ℝ) * edges.card -
        4 * (rootTypicality α : ℝ) * W.clusterSize * globalCount := by
  have hε : (0 : ℝ) ≤ epsilon α := by exact_mod_cast (parameter_pos hα).2.2.2.2.2.2.2.le
  have hγ : (0 : ℝ) ≤ gamma α := by exact_mod_cast (parameter_pos hα).2.2.2.2.2.2.1.le
  have hδ : (0 : ℝ) ≤ rootTypicality α := by exact_mod_cast (rootTypicality_margin hα hα1).1.le
  have hN : (0 : ℝ) ≤ W.clusterSize := Nat.cast_nonneg _
  have hsum : (∑ e ∈ edges, capacity W Q P S C e) =
      (∑ e ∈ edges, pairWeight W Q S P C e) -
        (2 * (gamma α : ℝ) + 3 * (epsilon α : ℝ)) * W.clusterSize * edges.card := by
    simp only [capacity_eq_weight_sub, Finset.sum_sub_distrib, Finset.sum_const,
      nsmul_eq_mul, mul_comm (edges.card : ℝ)]
  have hloss := mul_le_mul_of_nonneg_left hedges (by positivity :
    0 ≤ 2 * (gamma α : ℝ) + 3 * (epsilon α : ℝ))
  have hbad := mul_le_mul_of_nonneg_left hglobal (by positivity : 0 ≤ 4 * (rootTypicality α : ℝ))
  have hsmall : (freshBranchBound α W.clusterSize : ℝ) ≤ (epsilon α : ℝ) * W.clusterSize := by
    have hfloor : (freshBranchBound α W.clusterSize : ℝ) ≤ (epsilon α : ℝ) * W.clusterSize / 2 :=
      Nat.floor_le (by positivity)
    nlinarith only [hfloor, mul_nonneg hε hN]
  have hslack : (freshBranchBound α W.clusterSize : ℝ) * edges.card ≤ (epsilon α : ℝ) * q := by
    have h1 := mul_le_mul_of_nonneg_right hsmall (Nat.cast_nonneg edges.card : (0 : ℝ) ≤ edges.card)
    have h2 := mul_le_mul_of_nonneg_left hedges hε
    nlinarith only [h1, h2]
  have hmargin : 4 * (rootTypicality α : ℝ) + 4 * (epsilon α : ℝ) ≤ gamma α := by
    exact_mod_cast (source_aggregation_margin hα hα1).le
  have hqMargin := mul_le_mul_of_nonneg_right hmargin (Nat.cast_nonneg q : (0 : ℝ) ≤ q)
  nlinarith only [hsum, hloss, hbad, hslack, hqMargin]

theorem capacityBudget_of_row_margin (hα : 0 < α) (hα1 : α ≤ 1 / 4)
    (edges : Finset (MatchingEdge P)) (globalCount : ℕ)
    (hedges : (W.clusterSize : ℝ) * edges.card ≤ q)
    (hglobal : (W.clusterSize : ℝ) * globalCount ≤ q)
    (demand : ℝ) (hbudget : demand + 3 * (gamma α : ℝ) * q ≤ ∑ e ∈ edges, pairWeight W Q S P C e) :
    demand ≤ (∑ e ∈ edges, capacity W Q P S C e) -
      (freshBranchBound α W.clusterSize : ℝ) * edges.card -
      4 * (rootTypicality α : ℝ) * W.clusterSize * globalCount := by
  have h := effectiveCapacity_lower W Q S P C hα hα1 edges globalCount hedges hglobal
  linarith only [hbudget, h]

end Erdos547b.ZhaoSourceMatchingCapacityMargins

#print axioms Erdos547b.ZhaoSourceMatchingCapacityMargins.pairWeight_nonneg
#print axioms Erdos547b.ZhaoSourceMatchingCapacityMargins.pairWeight_le
#print axioms Erdos547b.ZhaoSourceMatchingCapacityMargins.capacityBudget_of_row_margin
