/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourcePathCoreMass
import ErdosProblems.Erdos547b.SourceClaim617PathNumerics
import ErdosProblems.Erdos547b.SourceNearFullNumerics

/-! # The integral path saving pays the switched two-row surplus -/

open scoped SimpleGraph BigOperators Classical
noncomputable section

namespace Erdos547b.ZhaoSourcePathCoreNumerics

open Finset SimpleGraph Erdos547b.TreePartition Erdos547b.ZhaoStability
open Erdos547b.ZhaoSourceDegreeFormRootRows Erdos547b.ZhaoSourceDegreeFormBounds
open Erdos547b.ZhaoSourceParameterSchedule Erdos547b.ZhaoSourceNearFullNumerics
open Erdos547b.ZhaoSourceClaim617PathNumerics Erdos547b.ZhaoSourcePathCoreMass
open Erdos547b.ZhaoClaim617CleanLoss Erdos547b.ZhaoEvenReducedPadding

theorem switch_coefficient_margin {α : ℚ} (hα : 0 < α) (hα1 : α ≤ 1 / 4) :
    9 * eta α + 6 * gamma α + 9 * degreeError α / 500 ≤ rho α := by
  obtain ⟨_, hr0, he0, _, _, _, _, _⟩ := parameter_pos hα
  obtain ⟨hr11, hrr1, her, hte3, hdt, hgd, _⟩ := parameter_upper_bounds hα hα1
  have hr1 : rho α ≤ 1 := hrr1.trans hr11
  have he1 : eta α ≤ 1 := by linarith only [her, hr1]
  have he3 : eta α ^ 3 ≤ eta α := pow_succ_le_self he0.le he1 2
  linarith only [her, hte3, hdt, hgd, he3, hr0]

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G)

theorem switch_surplus_margin (hα : 0 < α) (hα1 : α ≤ 1 / 4)
    (hhost : hostN = 2 * q) (horder : orderThreshold α M ≤ q) :
    5 * (rho α : ℝ) * paddedHalf (Index W) * W.clusterSize +
      9 * (eta α : ℝ) * q + 6 * (gamma α : ℝ) * q + 4 * W.clusterSize ≤
        8 * (rho α : ℝ) * q := by
  subst hostN
  have hN := (degreeForm_source_bounds hα hα1 W horder).2.2
  have hv := (sharp_paddedVolume W hα hα1 rfl horder).2
  have hr : (0 : ℝ) ≤ rho α := by exact_mod_cast (parameter_pos hα).2.1.le
  have hr1 : (rho α : ℝ) ≤ 1 := by
    exact_mod_cast (parameter_upper_bounds hα hα1).2.1.trans (parameter_upper_bounds hα hα1).1
  have hcoef : 9 * (eta α : ℝ) + 6 * (gamma α : ℝ) + 9 * (degreeError α : ℝ) / 500 ≤ rho α := by
    exact_mod_cast switch_coefficient_margin hα hα1
  have hscaled := mul_le_mul_of_nonneg_right hcoef (Nat.cast_nonneg q : (0 : ℝ) ≤ q)
  have hvolume := mul_le_mul_of_nonneg_left hv (by positivity : 0 ≤ 5 * (rho α : ℝ))
  have hρN := mul_le_mul_of_nonneg_right hr1 (Nat.cast_nonneg W.clusterSize : (0 : ℝ) ≤ W.clusterSize)
  have hrq := mul_nonneg hr (Nat.cast_nonneg q : (0 : ℝ) ≤ q)
  nlinarith only [hN, hscaled, hvolume, hρN, hrq]

variable {U : Type*} [Fintype U] [DecidableEq U]
variable {T : SimpleGraph U} [DecidableRel T.Adj]
variable {globalRoot : U} {small : ℕ} (P : ZhaoForestPartition T globalRoot small)
variable (hp : postponedCount α q ≤ (cleanBranches P).card) (hT : T.IsTree)

include hT in
theorem core_row_surplus (hα : 0 < α) (hα1 : α ≤ 1 / 4)
    (hhost : hostN = 2 * q) (horder : orderThreshold α M ≤ q)
    (hcard : Fintype.card U = q + 1) (row : ℝ)
    (hrow : (1 - 9 * (eta α : ℝ)) * q -
      5 * (rho α : ℝ) * paddedHalf (Index W) * W.clusterSize < row) :
    coreMass P hp 0 + coreMass P hp 1 + 2 * (3 * (gamma α : ℝ) * q) +
      2 * (2 * (W.clusterSize : ℝ)) < row := by
  have hmass := coreMass_sum_add_paths_le P hp hT hcard
  have hmargin := switch_surplus_margin W hα hα1 hhost horder
  have hceil : 4 * (rho α : ℝ) * q ≤ (postponedCount α q : ℝ) := Nat.le_ceil _
  nlinarith only [hmass, hmargin, hceil, hrow]

end Erdos547b.ZhaoSourcePathCoreNumerics

#print axioms Erdos547b.ZhaoSourcePathCoreNumerics.switch_surplus_margin
#print axioms Erdos547b.ZhaoSourcePathCoreNumerics.core_row_surplus
