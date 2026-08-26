/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceExceptionalCountBounds

/-!
# Finite padded-volume gates for the near-full matching

The target controls both source order and padded cluster count. The
extra distinguished-edge deletion and floor loss remain explicit.
-/

open scoped SimpleGraph Classical
noncomputable section

namespace Erdos547b.ZhaoSourceNearFullNumerics

open Finset SimpleGraph
open Erdos547b.ZhaoSourceExceptionalCountBounds Erdos547b.ZhaoSourceExceptionalNumerics
open Erdos547b.ZhaoSourceDegreeFormRootRows Erdos547b.ZhaoSourceDegreeFormBounds
open Erdos547b.ZhaoSourceParameterSchedule Erdos547b.ZhaoDegreeFormQuantitative
open Erdos547b.ZhaoEvenReducedPadding

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G)

def targetA : ℝ :=
  (1 - 8 * (eta α : ℝ)) * max (q : ℝ) ((paddedHalf (Index W) : ℝ) * W.clusterSize)

theorem sharp_paddedVolume (hα : 0 < α) (hα1 : α ≤ 1 / 4)
    (hhost : hostN = 2 * q) (horder : orderThreshold α M ≤ q) :
    (1 - (degreeError α : ℝ)) * q ≤ (paddedHalf (Index W) : ℝ) * W.clusterSize ∧
      (paddedHalf (Index W) : ℝ) * W.clusterSize ≤ q + W.clusterSize := by
  subst hostN
  have hE := (degreeForm_source_bounds hα hα1 W horder).1
  have hcover : (W.exceptional.card : ℝ) + (Fintype.card (Index W) : ℝ) * W.clusterSize = 2 * q := by
    have hn : W.exceptional.card + Fintype.card (Index W) * W.clusterSize = 2 * q := by
      simpa only [Index, Fintype.card_coe] using exceptional_add_clusters_eq_host W
    exact_mod_cast hn
  have hlo : (Fintype.card (Index W) : ℝ) * W.clusterSize ≤
      2 * (paddedHalf (Index W) : ℝ) * W.clusterSize := by
    exact_mod_cast Nat.mul_le_mul_right W.clusterSize (card_le_paddedCard (Index W))
  have hup : 2 * (paddedHalf (Index W) : ℝ) * W.clusterSize ≤
      ((Fintype.card (Index W) : ℝ) + 1) * W.clusterSize := by
    exact_mod_cast Nat.mul_le_mul_right W.clusterSize (paddedCard_le_card_add_one (Index W))
  have hd : (0 : ℝ) ≤ degreeError α := by exact_mod_cast (parameter_pos hα).2.2.2.2.1.le
  constructor
  · nlinarith only [hcover, hlo, hE, mul_nonneg hd (Nat.cast_nonneg q : (0 : ℝ) ≤ q)]
  · nlinarith only [hcover, hup, (Nat.cast_nonneg W.exceptional.card : (0 : ℝ) ≤ W.exceptional.card),
      (Nat.cast_nonneg W.clusterSize : (0 : ℝ) ≤ W.clusterSize)]

theorem parameter_bounds (hα : 0 < α) (hα1 : α ≤ 1 / 4) :
    0 < (eta α : ℝ) ∧ (eta α : ℝ) < 1 / 16 ∧
      (degreeError α : ℝ) ≤ (eta α : ℝ) / 1000 ∧
      10 * (fourthRoot α : ℝ) ^ 2 + 4 * (fourthRoot α : ℝ) ≤ (eta α : ℝ) / 1000 := by
  have hp := parameter_pos hα
  have hu := parameter_upper_bounds hα hα1
  have he1 := (parameter_gates hα hα1).2.1
  have heSmall : eta α < 1 / 16 := by linarith only [hu.2.2.1, hu.2.1, hu.1]
  have he3 : eta α ^ 3 ≤ eta α := pow_succ_le_self hp.2.2.1.le he1 2
  have hmargin := exceptional_saving_margin hα hα1
  have hlast : 10 * fourthRoot α ^ 2 + 4 * fourthRoot α ≤ eta α / 1000 := by
    linarith only [hmargin, he3, hp.2.2.2.1, hp.2.2.2.2.2.2.1]
  have hd : degreeError α ≤ eta α / 1000 := by
    linarith only [(parameter_gates hα hα1).2.2.2.2]
  refine ⟨by exact_mod_cast hp.2.2.1, ?_, by exact_mod_cast hd, by exact_mod_cast hlast⟩
  have h16 : 16 * eta α < 1 := by linarith only [heSmall]
  have h16R : (16 : ℝ) * (eta α : ℝ) < 1 := by exact_mod_cast h16
  linarith only [h16R]

theorem actual_matching_gates (hα : 0 < α) (hα1 : α ≤ 1 / 4)
    (hhost : hostN = 2 * q) (horder : orderThreshold α M ≤ q) :
    0 ≤ targetA W ∧
      targetA W + 4 * (eta α : ℝ) * ((paddedHalf (Index W) : ℝ) * W.clusterSize) +
        3 * (eta α : ℝ) * q + 4 * (fourthRoot α : ℝ) * q + 14 * W.clusterSize <
          (1 - 10 * (fourthRoot α : ℝ) ^ 2) * q ∧
      targetA W < ((paddedHalf (Index W) / 2 : ℕ) : ℝ) *
        (W.clusterSize * (2 - 3 * (eta α : ℝ))) := by
  subst hostN
  obtain ⟨he, heSmall, hd, ht⟩ := parameter_bounds hα hα1
  obtain ⟨hvlo, hvhi⟩ := sharp_paddedVolume W hα hα1 rfl horder
  have hvhalf := (paddedVolume_bounds W hα hα1 rfl horder).1
  have hN := (degreeForm_source_bounds hα hα1 W horder).2.2
  have hq : (0 : ℝ) < q := by
    have hh := W.five_ordinaryParts_le_host
    have hp := W.ordinaryParts_pos
    have hn : 0 < q := by omega
    exact_mod_cast hn
  have hN0 : (0 : ℝ) ≤ W.clusterSize := Nat.cast_nonneg _
  have hdq := mul_le_mul_of_nonneg_right hd hq.le
  have htq := mul_le_mul_of_nonneg_right ht hq.le
  have heq : 0 < (eta α : ℝ) * q := mul_pos he hq
  have hc : 0 ≤ 1 - 8 * (eta α : ℝ) := by linarith only [heSmall]
  have hc1 : 1 - 8 * (eta α : ℝ) ≤ 1 := by linarith only [he]
  have hvmax : max (q : ℝ) ((paddedHalf (Index W) : ℝ) * W.clusterSize) ≤ q + W.clusterSize :=
    max_le (by linarith only [hN0]) hvhi
  have htarget := mul_le_mul_of_nonneg_left hvmax hc
  have htarget0 : 0 ≤ targetA W := mul_nonneg hc ((le_max_left _ _).trans' hq.le)
  have hev := mul_le_mul_of_nonneg_left hvhi he.le
  refine ⟨htarget0, ?_, ?_⟩
  · dsimp only [targetA] at htarget ⊢
    nlinarith only [htarget, hev, htq, hN, hdq, heq, mul_nonneg he.le hN0]
  · have hmax : max (q : ℝ) ((paddedHalf (Index W) : ℝ) * W.clusterSize) ≤
        (paddedHalf (Index W) : ℝ) * W.clusterSize + (degreeError α : ℝ) * q := by
      have hd0 : (0 : ℝ) ≤ degreeError α := by exact_mod_cast (parameter_pos hα).2.2.2.2.1.le
      exact max_le (by nlinarith only [hvlo]) (le_add_of_nonneg_right (mul_nonneg hd0 hq.le))
    have htarget' := mul_le_mul_of_nonneg_left hmax hc
    have hdc := mul_le_mul_of_nonneg_right hc1
      (show 0 ≤ (degreeError α : ℝ) * q by
        exact mul_nonneg (by exact_mod_cast (parameter_pos hα).2.2.2.2.1.le) hq.le)
    have hdiv : paddedHalf (Index W) ≤ 2 * (paddedHalf (Index W) / 2) + 1 := by omega
    have hdivR : (paddedHalf (Index W) : ℝ) ≤ 2 * ((paddedHalf (Index W) / 2 : ℕ) : ℝ) + 1 := by
      exact_mod_cast hdiv
    have hdivN := mul_le_mul_of_nonneg_right hdivR hN0
    have hcoef : 0 ≤ 1 - 3 * (eta α : ℝ) / 2 := by linarith only [heSmall]
    have hcap := mul_le_mul_of_nonneg_right hdivN hcoef
    have hehalf := mul_le_mul_of_nonneg_left hvhalf he.le
    dsimp only [targetA] at htarget' ⊢
    nlinarith only [htarget', hdc, hcap, hehalf, hN, hdq, heq, mul_nonneg he.le hN0]

end Erdos547b.ZhaoSourceNearFullNumerics

#print axioms Erdos547b.ZhaoSourceNearFullNumerics.sharp_paddedVolume
#print axioms Erdos547b.ZhaoSourceNearFullNumerics.parameter_bounds
#print axioms Erdos547b.ZhaoSourceNearFullNumerics.actual_matching_gates
