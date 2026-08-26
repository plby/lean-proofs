/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceActualPartTwoPlan
import ErdosProblems.Erdos547b.SourceAbsoluteBadBudget

/-!
# Part-2 capacity bounds and absolute bad-edge accounting

The balanced gain does not invalidate the two-cluster cost bound. Thus the
same absolute global bad-edge allowance applies to this larger capacity.
The residual packing constructed here uses that actual larger capacity.
-/

open scoped SimpleGraph BigOperators Classical
noncomputable section

namespace Erdos547b.ZhaoSourcePartTwoCapacity

open Finset SimpleGraph
open Erdos547b.ZhaoSourceDegreeFormRootRows Erdos547b.ZhaoSourceActualChunkEmbedding
open Erdos547b.ZhaoSourceOnlineMatchingRoot Erdos547b.ZhaoSourceActualPartTwoPlan
open Erdos547b.ZhaoSourceParameterSchedule Erdos547b.ZhaoSourceFreshChunkBounds
open Erdos547b.ZhaoSourceAbsoluteBadBudget Erdos547b.ZhaoSourceSaturatedPacking
open Erdos547b.ZhaoLemma611Full

theorem ratio_coefficient_le_one {ratio : ℝ} (hratio : 0 ≤ ratio)
    (hratioHalf : ratio ≤ 1 / 2) : 0 ≤ ratio / (1 - ratio) ∧ ratio / (1 - ratio) ≤ 1 := by
  have hden : 0 < 1 - ratio := by linarith only [hratioHalf]
  refine ⟨div_nonneg hratio hden.le, ?_⟩
  rw [div_le_one hden]
  linarith only [hratioHalf]

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G) (Q : Certificate W)

theorem partOneCapacity_le_partTwoCapacity
    (S : CleanSourceWitness W Q) (C : Index W) (ratio : ℝ)
    (hratio : 0 ≤ ratio) (hratioHalf : ratio ≤ 1 / 2) (e : MatchingEdge Q.claim67.M) :
    partOneCapacity W Q S C e ≤ partTwoCapacity W Q S C ratio e := by
  have hcoef := (ratio_coefficient_le_one hratio hratioHalf).1
  exact le_add_of_nonneg_right (mul_nonneg (mul_nonneg hcoef (abs_nonneg _)) (Nat.cast_nonneg _))

/-- Each bad edge still costs at most two cluster orders, despite the gain. -/
theorem partTwoCapacity_le_twice_clusterSize
    (hα : 0 < α) (S : CleanSourceWitness W Q) (C : Index W)
    (hC : C = Q.A ∨ C = Q.B) (ratio : ℝ)
    (hratio : 0 ≤ ratio) (hratioHalf : ratio ≤ 1 / 2) (e : MatchingEdge Q.claim67.M) :
    partTwoCapacity W Q S C ratio e ≤ 2 * W.clusterSize := by
  let dx := rootDensity W S (Sum.inl C) (edgeVertex W Q e 0)
  let dy := rootDensity W S (Sum.inl C) (edgeVertex W Q e 1)
  have h0 : dx ≤ 1 := source_entry_le_one W Q S C hC _
  have h1 : dy ≤ 1 := source_entry_le_one W Q S C hC _
  have hg : (0 : ℝ) < gamma α := by exact_mod_cast (parameter_pos hα).2.2.2.2.2.2.1
  have he : (0 : ℝ) < epsilon α := by exact_mod_cast (parameter_pos hα).2.2.2.2.2.2.2
  have hgain := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (ratio_coefficient_le_one hratio hratioHalf).2 (abs_nonneg (dy - dx)))
    (Nat.cast_nonneg W.clusterSize : (0 : ℝ) ≤ W.clusterSize)
  have hcoeff : dx + dy - 2 * (gamma α : ℝ) - 3 * (epsilon α : ℝ) + |dy - dx| ≤ 2 := by
    rcases le_total dx dy with hxy | hyx
    · rw [abs_of_nonneg (sub_nonneg.mpr hxy)]
      linarith only [h1, hg, he]
    · rw [abs_of_nonpos (sub_nonpos.mpr hyx)]
      linarith only [h0, hg, he]
  have hscaled := mul_le_mul_of_nonneg_right hcoeff
    (Nat.cast_nonneg W.clusterSize : (0 : ℝ) ≤ W.clusterSize)
  change (dx + dy - 2 * (gamma α : ℝ) - 3 * (epsilon α : ℝ)) * W.clusterSize +
    ratio / (1 - ratio) * |dy - dx| * W.clusterSize ≤ 2 * W.clusterSize
  nlinarith only [hgain, hscaled]

/-- A uniform source gap supplies its full scalar balanced gain on a
finite submatching; losses are exactly the original Part-1 pair losses. -/
theorem sum_partTwoCapacity_lower
    (S : CleanSourceWitness W Q) (C : Index W) (ratio gap : ℝ)
    (hratio : 0 ≤ ratio) (hratioHalf : ratio ≤ 1 / 2)
    (edges : Finset (MatchingEdge Q.claim67.M))
    (hgap : ∀ e ∈ edges, gap ≤
      |rootDensity W S (Sum.inl C) (edgeVertex W Q e 1) -
        rootDensity W S (Sum.inl C) (edgeVertex W Q e 0)|) :
    (∑ e ∈ edges, partOneCapacity W Q S C e) +
      ratio / (1 - ratio) * gap * W.clusterSize * edges.card ≤
        ∑ e ∈ edges, partTwoCapacity W Q S C ratio e := by
  have hcoef := (ratio_coefficient_le_one hratio hratioHalf).1
  calc
    _ = ∑ e ∈ edges,
        (partOneCapacity W Q S C e + ratio / (1 - ratio) * gap * W.clusterSize) := by
      rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_comm (edges.card : ℝ)]
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro e he
      exact add_le_add_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hgap e he) hcoef)
          (Nat.cast_nonneg W.clusterSize)) _

/-- Construct the actual finite residual packing with Part-2 capacities
and the absolute global bad-edge loss used by synchronized families. -/
theorem exists_partTwoResidualPacking
    {Item : Type*} (hα : 0 < α) (S : CleanSourceWitness W Q) (C : Index W)
    (hC : C = Q.A ∨ C = Q.B) (ratio : ℝ)
    (hratio : 0 ≤ ratio) (hratioHalf : ratio ≤ 1 / 2)
    (all used bad : Finset (MatchingEdge Q.claim67.M)) (items : List Item)
    (weight : Item → ℝ) (consumed : ℝ) (globalCount : ℕ)
    (hused : used ⊆ all) (hbad : bad ⊆ all \ used)
    (hcount : (bad.card : ℝ) ≤ 2 * (rootTypicality α : ℝ) * globalCount)
    (hledger : (∑ e ∈ used, (partTwoCapacity W Q S C ratio e - freshBranchBound α W.clusterSize)) ≤ consumed)
    (hsmall : ∀ i ∈ items, 0 < weight i ∧ weight i ≤ freshBranchBound α W.clusterSize)
    (hbudget : mass weight items + consumed ≤
      (∑ e ∈ all, partTwoCapacity W Q S C ratio e) -
        (freshBranchBound α W.clusterSize : ℝ) * all.card -
          4 * (rootTypicality α : ℝ) * W.clusterSize * globalCount) :
    Nonempty (SaturatedPacking
      (((all \ used) \ bad).filter (fun e =>
        (freshBranchBound α W.clusterSize : ℝ) < partTwoCapacity W Q S C ratio e)).toList
      items weight (partTwoCapacity W Q S C ratio) (freshBranchBound α W.clusterSize)) := by
  exact exists_residualPacking_absolute all used bad items weight (partTwoCapacity W Q S C ratio)
    (freshBranchBound α W.clusterSize) (rootTypicality α : ℝ) W.clusterSize consumed globalCount
    hused hbad hcount (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    (fun e _ => partTwoCapacity_le_twice_clusterSize W Q hα S C hC ratio hratio hratioHalf e)
    hledger hsmall hbudget

end Erdos547b.ZhaoSourcePartTwoCapacity

#print axioms Erdos547b.ZhaoSourcePartTwoCapacity.partOneCapacity_le_partTwoCapacity
#print axioms Erdos547b.ZhaoSourcePartTwoCapacity.partTwoCapacity_le_twice_clusterSize
#print axioms Erdos547b.ZhaoSourcePartTwoCapacity.sum_partTwoCapacity_lower
#print axioms Erdos547b.ZhaoSourcePartTwoCapacity.exists_partTwoResidualPacking
