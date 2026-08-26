/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceCapacityBudgetMargins
import ErdosProblems.Erdos547b.Claim615SourceFamilyTarget

/-!
# Actual exceptional-row gains pay the selected forest

The unbalanced gain is bounded below by ratio times the density gap;
the Appendix gain is exactly lambda times the matching volume. Both
are compared with the literal family-dependent ceiling and overshoot.
-/

open scoped SimpleGraph BigOperators Classical
noncomputable section

namespace Erdos547b.ZhaoSourceExceptionalIdealGains

open Finset SimpleGraph Erdos547b.TreePartition
open Erdos547b.ZhaoSourceCapacityBudgetMargins Erdos547b.ZhaoSourceFamilyCapacity
open Erdos547b.ZhaoSourceDegreeFormRootRows Erdos547b.ZhaoSourceActualChunkEmbedding
open Erdos547b.ZhaoSourceParameterSchedule Erdos547b.ZhaoLemma611Full
open Erdos547b.ZhaoClaim615SourceFamilyTarget Erdos547b.ZhaoClaim615SourceSelection
open Erdos547b.ZhaoClaim617BranchCount Erdos547b.ZhaoClaim616SourceBridge

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G) (Q : Certificate W) (S : CleanSourceWitness W Q)
variable (C : Index W)

@[simp] theorem ordinary_idealCapacity (e : MatchingEdge Q.claim67.M) :
    idealCapacity W Q S C (.threshold 0) e = rowWeight W S (Sum.inl C) e := by
  simp only [idealCapacity, zero_div, zero_mul, add_zero]
  exact mul_comm _ _

theorem threshold_idealGain (ratio eta : ℝ)
    (hratio : 0 ≤ ratio) (hratio1 : ratio ≤ 1 / 2)
    (e : MatchingEdge Q.claim67.M)
    (hgap : eta ≤ |rootDensity W S (Sum.inl C) (edgeVertex W Q e 1) -
      rootDensity W S (Sum.inl C) (edgeVertex W Q e 0)|) :
    rowWeight W S (Sum.inl C) e + ratio * eta * W.clusterSize ≤
      idealCapacity W Q S C (.threshold ratio) e := by
  have hden : 0 < 1 - ratio := by linarith only [hratio1]
  have hrdiv : ratio ≤ ratio / (1 - ratio) := by
    apply (le_div_iff₀ hden).mpr
    nlinarith only [sq_nonneg ratio]
  have hgain := (mul_le_mul_of_nonneg_left hgap hratio).trans
    (mul_le_mul_of_nonneg_right hrdiv (abs_nonneg _))
  have hN := mul_le_mul_of_nonneg_right hgain (Nat.cast_nonneg W.clusterSize : (0 : ℝ) ≤ W.clusterSize)
  dsimp only [idealCapacity, rowWeight, edgeVertex]
  dsimp only [edgeVertex] at hN
  nlinarith only [hN]

theorem threshold_idealGain_sum (ratio eta : ℝ)
    (hratio : 0 ≤ ratio) (hratio1 : ratio ≤ 1 / 2)
    (edges : Finset (MatchingEdge Q.claim67.M))
    (hgap : ∀ e ∈ edges, eta ≤ |rootDensity W S (Sum.inl C) (edgeVertex W Q e 1) -
      rootDensity W S (Sum.inl C) (edgeVertex W Q e 0)|) :
    (∑ e ∈ edges, rowWeight W S (Sum.inl C) e) + ratio * eta * W.clusterSize * edges.card ≤
      ∑ e ∈ edges, idealCapacity W Q S C (.threshold ratio) e := by
  have h := Finset.sum_le_sum (fun e he => threshold_idealGain W Q S C ratio eta hratio hratio1 e (hgap e he))
  simpa only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
    mul_comm (edges.card : ℝ)] using h

theorem appendix_idealGain_sum (lambda : ℝ)
    (edges : Finset (MatchingEdge Q.claim67.M)) :
    (∑ e ∈ edges, rowWeight W S (Sum.inl C) e) + lambda * W.clusterSize * edges.card =
      ∑ e ∈ edges, idealCapacity W Q S C (.appendix lambda) e := by
  have h (e : MatchingEdge Q.claim67.M) :
      idealCapacity W Q S C (.appendix lambda) e =
        rowWeight W S (Sum.inl C) e + lambda * W.clusterSize := by
    dsimp only [idealCapacity, rowWeight, edgeVertex]
    ring
  simp only [h, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
    mul_comm (edges.card : ℝ)]

variable {U : Type*} [Fintype U] [DecidableEq U]
variable {T : SimpleGraph U} [DecidableRel T.Adj]
variable {globalRoot : U} {small : ℕ}
variable (P : ZhaoForestPartition T globalRoot small)

theorem selected_real_lower
    {available : Finset (BranchIndex P)} {a eta n : ℝ} {slack : ℕ}
    (F0 : SelectedF0 P available (exceptionalForestTarget a eta n) slack) :
    a + eta ^ 3 * n ≤ (branchMass P F0.selected : ℝ) := by
  exact (exceptionalForestTarget_lower a eta n).trans (by exact_mod_cast F0.lower)

theorem selected_real_upper
    {available : Finset (BranchIndex P)} {a eta n : ℝ} {slack : ℕ}
    (F0 : SelectedF0 P available (exceptionalForestTarget a eta n) slack)
    (hnonneg : 0 ≤ a + eta ^ 3 * n) :
    (branchMass P F0.selected : ℝ) < a + eta ^ 3 * n + 1 + slack := by
  have hupper : (branchMass P F0.selected : ℝ) <
      (exceptionalForestTarget a eta n : ℝ) + slack := by exact_mod_cast F0.upper
  have hceil := exceptionalForestTarget_lt_add_one hnonneg
  linarith only [hupper, hceil]

/-- Select the actual family and pay its whole ideal budget, including the
integral ceiling and the strict one-branch overshoot. -/
theorem exists_selectedF0_with_idealBudget
    (available : Finset (BranchIndex P)) (eta : ℝ) (slack : ℕ)
    (kind : FamilyKind) (edges : Finset (MatchingEdge Q.claim67.M))
    (hslack : 0 < slack)
    (hsmall : ∀ i ∈ available, (branchForest P).branches.size i ≤ slack)
    (hnonneg : 0 ≤ (∑ e ∈ edges, rowWeight W S (Sum.inl C) e) + eta ^ 3 * q)
    (hmass : (∑ e ∈ edges, rowWeight W S (Sum.inl C) e) + eta ^ 3 * q ≤ (branchMass P available : ℝ))
    (hgain : (∑ e ∈ edges, rowWeight W S (Sum.inl C) e) + eta ^ 3 * q + 1 + slack +
        3 * (gamma α : ℝ) * q ≤ ∑ e ∈ edges, idealCapacity W Q S C kind e) :
    ∃ F0 : SelectedF0 P available
        (exceptionalForestTarget (∑ e ∈ edges, rowWeight W S (Sum.inl C) e) eta q) slack,
      (∑ i ∈ F0.selected, ((branchForest P).branches.size i : ℝ)) + 3 * (gamma α : ℝ) * q ≤
        ∑ e ∈ edges, idealCapacity W Q S C kind e := by
  obtain ⟨F0⟩ := exists_selectedF0_for_exceptionalDegree P available
    (∑ e ∈ edges, rowWeight W S (Sum.inl C) e) eta q slack hslack hsmall hmass
  refine ⟨F0, ?_⟩
  have hupper := selected_real_upper P F0 hnonneg
  have hmassCast : (branchMass P F0.selected : ℝ) =
      ∑ i ∈ F0.selected, ((branchForest P).branches.size i : ℝ) := by
    simp only [branchMass, Nat.cast_sum]
  rw [hmassCast] at hupper
  linarith only [hupper, hgain]

end Erdos547b.ZhaoSourceExceptionalIdealGains

#print axioms Erdos547b.ZhaoSourceExceptionalIdealGains.threshold_idealGain_sum
#print axioms Erdos547b.ZhaoSourceExceptionalIdealGains.appendix_idealGain_sum
#print axioms Erdos547b.ZhaoSourceExceptionalIdealGains.selected_real_lower
#print axioms Erdos547b.ZhaoSourceExceptionalIdealGains.exists_selectedF0_with_idealBudget
