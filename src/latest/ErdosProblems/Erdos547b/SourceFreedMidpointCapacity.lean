/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceFreedMidpointSystem
import ErdosProblems.Erdos547b.SourceMidpointNumerics
import ErdosProblems.Erdos547b.SourceNearFullNumerics

/-! # Actual midpoint neighbor capacities pay the integral path counts -/

open scoped SimpleGraph BigOperators Classical
noncomputable section

namespace Erdos547b.ZhaoSourceFreedMidpointCapacity

open Finset SimpleGraph Erdos547EC2 Erdos547b.ZhaoStability
open Erdos547b.ZhaoSourceDegreeFormRootRows Erdos547b.ZhaoSourceDegreeFormBounds
open Erdos547b.ZhaoSourceParameterSchedule Erdos547b.ZhaoSourceNearFullMatching
open Erdos547b.ZhaoSourceClaim617Switch Erdos547b.ZhaoSourceEmbeddingHost
open Erdos547b.ZhaoSourceFreedClusterGeometry Erdos547b.ZhaoSourceFreedMidpointSystem
open Erdos547b.ZhaoSourceMidpointNumerics Erdos547b.ZhaoSourceNearFullNumerics
open Erdos547b.ZhaoSourceFreshChunkBounds Erdos547b.ZhaoEvenReducedPadding
open Erdos547b.ZhaoClaim617SwitchNumerics Erdos547b.ZhaoSourceClaim617PathNumerics

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G) (Q : Certificate W) (S : CleanSourceWitness W Q)
variable {fb : ℝ} (O : Output W Q S fb) (sw : Switch W Q S O)

theorem freed_volume_lower (hα : 0 < α) (hα1 : α ≤ 1 / 4) (hhost : hostN = 2 * q)
    (horder : orderThreshold α M ≤ q) :
    (49 / 10 : ℝ) * (rho α : ℝ) * (1 - (degreeError α : ℝ)) * q ≤
      (Fintype.card (FreedIndex W Q S O sw) : ℝ) * W.clusterSize := by
  have hm : (49 / 10 : ℝ) * (rho α : ℝ) * paddedHalf (Index W) <
      (Fintype.card (FreedIndex W Q S O sw) : ℝ) := by
    rw [freedIndex_card]
    exact (switchCount_bounds (scale_lower W Q S O hα hα1 hhost horder)).1
  have hvol := (sharp_paddedVolume W hα hα1 hhost horder).1
  have hr : (0 : ℝ) ≤ rho α := by exact_mod_cast (parameter_pos hα).2.1.le
  have hmN := mul_le_mul_of_nonneg_right hm.le (Nat.cast_nonneg W.clusterSize : (0 : ℝ) ≤ W.clusterSize)
  have hvolScale := mul_le_mul_of_nonneg_left hvol (by positivity : 0 ≤ (49 / 10 : ℝ) * (rho α : ℝ))
  nlinarith only [hmN, hvolScale]

private theorem factors_nonneg (hα : 0 < α) (hα1 : α ≤ 1 / 4) :
    0 ≤ 1 - 2 * (eta α : ℝ) - 2 * (epsilon α : ℝ) ∧
    0 ≤ 1 - (rootTypicality α : ℝ) ∧
    0 ≤ 1 - 2 * (fourthRoot α : ℝ) ^ 2 - (rootTypicality α : ℝ) - (epsilon α : ℝ) := by
  obtain ⟨h₁, h₂, h₃, _⟩ := midpoint_factors hα hα1
  constructor
  · exact_mod_cast (show 0 ≤ 1 - 2 * eta α - 2 * epsilon α by linarith only [h₁])
  constructor
  · exact_mod_cast (show 0 ≤ 1 - rootTypicality α by linarith only [h₂])
  · exact_mod_cast (show 0 ≤ 1 - 2 * fourthRoot α ^ 2 - rootTypicality α - epsilon α by linarith only [h₃])

variable (D : Data W Q S O sw)

theorem low_raw_lower (hα : 0 < α) (hα1 : α ≤ 1 / 4) (hhost : hostN = 2 * q)
    (horder : orderThreshold α M ≤ q) (e : FreedIndex W Q S O sw) :
    (1 - 2 * (fourthRoot α : ℝ) ^ 2 - (rootTypicality α : ℝ) - (epsilon α : ℝ)) * W.clusterSize ≤
      (raw W Q S O sw D 1 e).card := by
  have hc : (sourceQuota W : ℝ) < 2 * (fourthRoot α : ℝ) ^ 2 * W.clusterSize + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have hs : (2 : ℝ) < (epsilon α : ℝ) * W.clusterSize := by
    subst hostN
    exact epsilon_mul_clusterSize_gt_two hα hα1 W horder
  change _ ≤ ((D e).low.card : ℝ)
  nlinarith only [hc, hs, (D e).low_card]

theorem high_raw_lower (e : FreedIndex W Q S O sw) :
    2 * (fourthRoot α : ℝ) ^ 2 * W.clusterSize ≤ (raw W Q S O sw D 0 e).card := by
  change _ ≤ ((D e).high.card : ℝ)
  rw [(D e).high_card]
  exact Nat.le_ceil _

theorem low_pool_capacity (hα : 0 < α) (hα1 : α ≤ 1 / 4) (hhost : hostN = 2 * q)
    (horder : orderThreshold α M ≤ q)
    {z : Fin hostN} (hz : z ∈ clusterVertices (assignment W) Q.A)
    (havoid : z ∉ rootAvoid W Q S O sw D 0) :
    (9 / 2 : ℝ) * (rho α : ℝ) * q ≤ (degreeInto (embeddingHost W) z (pool W Q S O sw D 1) : ℝ) := by
  obtain ⟨hc, hr, hl⟩ := factors_nonneg hα hα1
  have hactual := pool_degree_lower W Q S O sw D hα hα1 1
    ((1 - 2 * (fourthRoot α : ℝ) ^ 2 - (rootTypicality α : ℝ) - (epsilon α : ℝ)) * W.clusterSize)
    (mul_nonneg hl (Nat.cast_nonneg _)) (low_raw_lower W Q S O sw D hα hα1 hhost horder) hz havoid
  have hvol := freed_volume_lower W Q S O sw hα hα1 hhost horder
  have hvolScale := mul_le_mul_of_nonneg_left hvol (mul_nonneg (mul_nonneg hc hr) hl)
  have hcoef := (Rat.cast_le (K := ℝ)).mpr (low_coefficient_margin hα hα1)
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_mul, Rat.cast_sub, Rat.cast_one, Rat.cast_pow] at hcoef
  have hρ : (0 : ℝ) ≤ rho α := by exact_mod_cast (parameter_pos hα).2.1.le
  have hcoefScale := mul_le_mul_of_nonneg_right hcoef (mul_nonneg hρ (Nat.cast_nonneg q : (0 : ℝ) ≤ q))
  nlinarith only [hactual, hvolScale, hcoefScale]

theorem high_pool_capacity (hα : 0 < α) (hα1 : α ≤ 1 / 4) (hhost : hostN = 2 * q)
    (horder : orderThreshold α M ≤ q)
    {z : Fin hostN} (hz : z ∈ clusterVertices (assignment W) Q.A)
    (havoid : z ∉ rootAvoid W Q S O sw D 0) :
    5 * (rho α : ℝ) * (fourthRoot α : ℝ) ^ 2 * q ≤
      (degreeInto (embeddingHost W) z (pool W Q S O sw D 0) : ℝ) := by
  obtain ⟨hc, hr, _⟩ := factors_nonneg hα hα1
  have hactual := pool_degree_lower W Q S O sw D hα hα1 0
    (2 * (fourthRoot α : ℝ) ^ 2 * W.clusterSize) (by positivity)
    (high_raw_lower W Q S O sw D) hz havoid
  have hvol := freed_volume_lower W Q S O sw hα hα1 hhost horder
  have hvolScale := mul_le_mul_of_nonneg_left hvol
    (mul_nonneg (mul_nonneg hc hr) (show 0 ≤ 2 * (fourthRoot α : ℝ) ^ 2 by positivity))
  have hcoef := (Rat.cast_le (K := ℝ)).mpr (high_coefficient_margin hα hα1)
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_mul, Rat.cast_sub, Rat.cast_one] at hcoef
  have hρ : (0 : ℝ) ≤ rho α := by exact_mod_cast (parameter_pos hα).2.1.le
  have hcoefScale := mul_le_mul_of_nonneg_right hcoef
    (mul_nonneg (mul_nonneg hρ (sq_nonneg (fourthRoot α : ℝ))) (Nat.cast_nonneg q : (0 : ℝ) ≤ q))
  nlinarith only [hactual, hvolScale, hcoefScale]

theorem pool_degree_counts (hα : 0 < α) (hα1 : α ≤ 1 / 4) (hhost : hostN = 2 * q)
    (horder : orderThreshold α M ≤ q)
    {z : Fin hostN} (hz : z ∈ clusterVertices (assignment W) Q.A)
    (havoid : z ∉ rootAvoid W Q S O sw D 0) :
    highCount α q ≤ degreeInto (embeddingHost W) z (pool W Q S O sw D 0) ∧
      postponedCount α q ≤ degreeInto (embeddingHost W) z (pool W Q S O sw D 1) := by
  constructor
  · exact_mod_cast ((highCount_lt_high_capacity hα hα1 horder).trans_le
      (high_pool_capacity W Q S O sw D hα hα1 hhost horder hz havoid)).le
  · exact_mod_cast ((postponedCount_lt_low_capacity hα hα1 horder).trans_le
      (low_pool_capacity W Q S O sw D hα hα1 hhost horder hz havoid)).le

end Erdos547b.ZhaoSourceFreedMidpointCapacity

#print axioms Erdos547b.ZhaoSourceFreedMidpointCapacity.low_pool_capacity
#print axioms Erdos547b.ZhaoSourceFreedMidpointCapacity.high_pool_capacity
#print axioms Erdos547b.ZhaoSourceFreedMidpointCapacity.pool_degree_counts
