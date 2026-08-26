/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceFamilyCapacity

/-!
# The source three-gamma margin pays both actual family capacities

The conservative Appendix loss, branch-packing slack and absolute global
bad-edge allowance all fit the same source margin. Ideal weights retain
the genuine threshold or nonextreme gain; they are not graph premises.
-/

open scoped SimpleGraph BigOperators Classical
noncomputable section

namespace Erdos547b.ZhaoSourceCapacityBudgetMargins

open Finset SimpleGraph Erdos547b.ZhaoSourceParameterSchedule
open Erdos547b.ZhaoSourceDegreeFormRootRows Erdos547b.ZhaoSourceActualChunkEmbedding
open Erdos547b.ZhaoSourceOnlineMatchingRoot Erdos547b.ZhaoSourceActualPartTwoPlan
open Erdos547b.ZhaoSourceFamilyCapacity Erdos547b.ZhaoSourceFreshChunkBounds
open Erdos547b.ZhaoLemma611Full

theorem source_mixed_aggregation_margin {α : ℚ} (hα : 0 < α) (hα1 : α ≤ 1 / 4) :
    4 * rootTypicality α + 31 * epsilon α < gamma α := by
  have hg := (parameter_pos hα).2.2.2.2.2.2.1
  have hupper := parameter_upper_bounds hα hα1
  have hd1 := (reservoir_cleanup_bounds hα hα1).2.2.2.2.2
  have hg1 : gamma α ≤ 1 := by linarith only [hupper.2.2.2.2.2.1, hd1]
  have hδg : rootTypicality α ≤ gamma α / 1000 :=
    div_le_div_of_nonneg_right (pow_succ_le_self hg.le hg1 5) (by norm_num)
  linarith only [hδg, hupper.2.2.2.2.2.2, hg]

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G) (Q : Certificate W) (S : CleanSourceWitness W Q) (C : Index W)

def idealCapacity (kind : FamilyKind) (e : MatchingEdge Q.claim67.M) : ℝ :=
  let dx := rootDensity W S (Sum.inl C) (edgeVertex W Q e 0)
  let dy := rootDensity W S (Sum.inl C) (edgeVertex W Q e 1)
  match kind with
  | .threshold ratio => (dx + dy + ratio / (1 - ratio) * |dy - dx|) * W.clusterSize
  | .appendix lambda => (dx + dy + lambda) * W.clusterSize

theorem idealCapacity_sub_loss_le (hα : 0 < α) (kind : FamilyKind) (e : MatchingEdge Q.claim67.M) :
    idealCapacity W Q S C kind e - (2 * (gamma α : ℝ) + 30 * (epsilon α : ℝ)) * W.clusterSize ≤
      capacity W Q S C kind e := by
  have hε : (0 : ℝ) ≤ epsilon α := by exact_mod_cast (parameter_pos hα).2.2.2.2.2.2.2.le
  have hN : (0 : ℝ) ≤ W.clusterSize := Nat.cast_nonneg _
  cases kind with
  | threshold ratio =>
      unfold idealCapacity capacity partTwoCapacity partOneCapacity
      nlinarith only [mul_nonneg hε hN]
  | appendix lambda =>
      unfold idealCapacity capacity
      exact le_of_eq (by ring)

theorem effectiveCapacity_lower (hα : 0 < α) (hα1 : α ≤ 1 / 4)
    (kind : FamilyKind) (edges : Finset (MatchingEdge Q.claim67.M)) (globalCount : ℕ)
    (hedges : (W.clusterSize : ℝ) * edges.card ≤ q)
    (hglobal : (W.clusterSize : ℝ) * globalCount ≤ q) :
    (∑ e ∈ edges, idealCapacity W Q S C kind e) - 3 * (gamma α : ℝ) * q ≤
      (∑ e ∈ edges, capacity W Q S C kind e) -
        (freshBranchBound α W.clusterSize : ℝ) * edges.card -
        4 * (rootTypicality α : ℝ) * W.clusterSize * globalCount := by
  have hε : (0 : ℝ) ≤ epsilon α := by exact_mod_cast (parameter_pos hα).2.2.2.2.2.2.2.le
  have hγ : (0 : ℝ) ≤ gamma α := by exact_mod_cast (parameter_pos hα).2.2.2.2.2.2.1.le
  have hδ : (0 : ℝ) ≤ rootTypicality α := by exact_mod_cast (rootTypicality_margin hα hα1).1.le
  have hN : (0 : ℝ) ≤ W.clusterSize := Nat.cast_nonneg _
  have hsum : (∑ e ∈ edges, idealCapacity W Q S C kind e) -
      (2 * (gamma α : ℝ) + 30 * (epsilon α : ℝ)) * W.clusterSize * edges.card ≤
        ∑ e ∈ edges, capacity W Q S C kind e := by
    have h := Finset.sum_le_sum (fun e (_ : e ∈ edges) => idealCapacity_sub_loss_le W Q S C hα kind e)
    simpa only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
      mul_comm (edges.card : ℝ)] using h
  have hloss := mul_le_mul_of_nonneg_left hedges (by positivity : 0 ≤ 2 * (gamma α : ℝ) + 30 * (epsilon α : ℝ))
  have hbad := mul_le_mul_of_nonneg_left hglobal (by positivity : 0 ≤ 4 * (rootTypicality α : ℝ))
  have hsmall : (freshBranchBound α W.clusterSize : ℝ) ≤ (epsilon α : ℝ) * W.clusterSize := by
    have hfloor : (freshBranchBound α W.clusterSize : ℝ) ≤ (epsilon α : ℝ) * W.clusterSize / 2 :=
      Nat.floor_le (by positivity)
    nlinarith only [hfloor, mul_nonneg hε hN]
  have hslack : (freshBranchBound α W.clusterSize : ℝ) * edges.card ≤ (epsilon α : ℝ) * q := by
    have h1 := mul_le_mul_of_nonneg_right hsmall (Nat.cast_nonneg edges.card : (0 : ℝ) ≤ edges.card)
    have h2 := mul_le_mul_of_nonneg_left hedges hε
    nlinarith only [h1, h2]
  have hmargin : 4 * (rootTypicality α : ℝ) + 31 * (epsilon α : ℝ) ≤ gamma α := by
    exact_mod_cast (source_mixed_aggregation_margin hα hα1).le
  have hqMargin := mul_le_mul_of_nonneg_right hmargin (Nat.cast_nonneg q : (0 : ℝ) ≤ q)
  nlinarith only [hsum, hloss, hbad, hslack, hqMargin]

theorem capacityBudget_of_ideal_margin (hα : 0 < α) (hα1 : α ≤ 1 / 4)
    (kind : FamilyKind) (edges : Finset (MatchingEdge Q.claim67.M)) (globalCount : ℕ)
    (hedges : (W.clusterSize : ℝ) * edges.card ≤ q)
    (hglobal : (W.clusterSize : ℝ) * globalCount ≤ q)
    (demand : ℝ) (hbudget : demand + 3 * (gamma α : ℝ) * q ≤ ∑ e ∈ edges, idealCapacity W Q S C kind e) :
    demand ≤ (∑ e ∈ edges, capacity W Q S C kind e) -
      (freshBranchBound α W.clusterSize : ℝ) * edges.card -
      4 * (rootTypicality α : ℝ) * W.clusterSize * globalCount := by
  have h := effectiveCapacity_lower W Q S C hα hα1 kind edges globalCount hedges hglobal
  linarith only [hbudget, h]

end Erdos547b.ZhaoSourceCapacityBudgetMargins

#print axioms Erdos547b.ZhaoSourceCapacityBudgetMargins.source_mixed_aggregation_margin
#print axioms Erdos547b.ZhaoSourceCapacityBudgetMargins.idealCapacity_sub_loss_le
#print axioms Erdos547b.ZhaoSourceCapacityBudgetMargins.effectiveCapacity_lower
#print axioms Erdos547b.ZhaoSourceCapacityBudgetMargins.capacityBudget_of_ideal_margin
