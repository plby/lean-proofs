/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceExceptionalNumerics
import ErdosProblems.Erdos547b.SourceExceptionalRowBounds

/-!
# The actual half-exceptional count satisfies the source gates

The degree-form cover and the possible single dummy cluster give the
padded volume inequalities. The fresh scale absorbs both integer losses.
-/

open scoped SimpleGraph BigOperators Classical
noncomputable section

namespace Erdos547b.ZhaoSourceExceptionalCountBounds

open Finset SimpleGraph
open Erdos547b.ZhaoSourceExceptionalNumerics Erdos547b.ZhaoSourceExceptionalRowBounds
open Erdos547b.ZhaoSourceDegreeFormRootRows Erdos547b.ZhaoSourceDegreeFormBounds
open Erdos547b.ZhaoSourceParameterSchedule Erdos547b.ZhaoSourceFreshChunkBounds
open Erdos547b.ZhaoDegreeFormQuantitative Erdos547b.ZhaoEvenReducedPadding

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G)

def exceptionalCount : ℕ := ⌈(eta α : ℝ) * paddedHalf (Index W) / 2⌉₊

theorem paddedVolume_bounds (hα : 0 < α) (hα1 : α ≤ 1 / 4)
    (hhost : hostN = 2 * q) (horder : orderThreshold α M ≤ q) :
    (q : ℝ) / 2 ≤ (paddedHalf (Index W) : ℝ) * W.clusterSize ∧
      (paddedHalf (Index W) : ℝ) * W.clusterSize ≤ 2 * q := by
  subst hostN
  obtain ⟨hE, _, hN⟩ := degreeForm_source_bounds hα hα1 W horder
  have hd : (degreeError α : ℝ) ≤ 1 := by
    exact_mod_cast (reservoir_cleanup_bounds hα hα1).2.2.2.2.2
  have hdq := mul_le_mul_of_nonneg_right hd (Nat.cast_nonneg q : (0 : ℝ) ≤ q)
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
  have hq : (0 : ℝ) ≤ q := Nat.cast_nonneg _
  constructor
  · nlinarith only [hcover, hlo, hE, hdq]
  · nlinarith only [hcover, hup, hN, hdq, hq, (Nat.cast_nonneg W.exceptional.card : (0 : ℝ) ≤ W.exceptional.card)]

theorem actual_half_selection_gates (hα : 0 < α) (hα1 : α ≤ 1 / 4)
    (hhost : hostN = 2 * q) (horder : orderThreshold α M ≤ q) :
    2 * (W.clusterSize : ℝ) * exceptionalCount W + (eta α : ℝ) ^ 3 * q + 1 ≤ (α : ℝ) / 32 * q ∧
      (eta α : ℝ) ^ 3 * q + 1 + freshBranchBound α W.clusterSize + 3 * (gamma α : ℝ) * q ≤
        ((α : ℝ) / 16) * (eta α : ℝ) * W.clusterSize * exceptionalCount W := by
  subst hostN
  obtain ⟨hetaQ, heta1Q, hratioQ, hsmallQ, hdQ⟩ := parameter_gates hα hα1
  have heta : (0 : ℝ) ≤ eta α := by exact_mod_cast hetaQ.le
  have heps : (0 : ℝ) ≤ epsilon α := by exact_mod_cast (parameter_pos hα).2.2.2.2.2.2.2.le
  have hgamma : (0 : ℝ) ≤ gamma α := by exact_mod_cast (parameter_pos hα).2.2.2.2.2.2.1.le
  have hN := (degreeForm_source_bounds hα hα1 W horder).2.2
  have hdR : (1000 : ℝ) * (degreeError α : ℝ) ≤ eta α := by exact_mod_cast hdQ
  have hdq := mul_le_mul_of_nonneg_right hdR (Nat.cast_nonneg q : (0 : ℝ) ≤ q)
  have hNsmall : (W.clusterSize : ℝ) ≤ (eta α : ℝ) * q / 1000 := by
    nlinarith only [hN, hdq, mul_nonneg heta (Nat.cast_nonneg q : (0 : ℝ) ≤ q)]
  obtain ⟨hvolLo, hvolHi⟩ := paddedVolume_bounds W hα hα1 rfl horder
  have hcountLo : (eta α : ℝ) * paddedHalf (Index W) / 2 ≤ (exceptionalCount W : ℝ) := Nat.le_ceil _
  have hcountHi : (exceptionalCount W : ℝ) ≤ (eta α : ℝ) * paddedHalf (Index W) / 2 + 1 :=
    (Nat.ceil_lt_add_one (by positivity)).le
  have hratio : (8 : ℝ) * (eta α : ℝ) ≤ (α : ℝ) / 16 := by exact_mod_cast hratioQ
  have h := half_selection_gates (eta α : ℝ) ((α : ℝ) / 16) (epsilon α : ℝ) (gamma α : ℝ)
    q W.clusterSize (paddedHalf (Index W)) (exceptionalCount W) (freshBranchBound α W.clusterSize)
    heta (by exact_mod_cast heta1Q) hratio heps hgamma (by exact_mod_cast hsmallQ)
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) hNsmall hvolLo hvolHi hcountLo hcountHi
    (epsilon_mul_clusterSize_gt_two hα hα1 W horder).le (Nat.floor_le (by positivity))
  constructor
  · convert h.1 using 1
    ring
  · exact h.2

theorem actual_nonextreme_gates (hα : 0 < α) (hα1 : α ≤ 1 / 4)
    (hhost : hostN = 2 * q) (horder : orderThreshold α M ≤ q) :
    2 * (W.clusterSize : ℝ) * exceptionalCount W + (eta α : ℝ) ^ 3 * q + 1 <
        (q : ℝ) / 2 - 12 * (fourthRoot α : ℝ) ^ 2 * q ∧
      (eta α : ℝ) ^ 3 * q + 1 + freshBranchBound α W.clusterSize + 3 * (gamma α : ℝ) * q ≤
        (eta α : ℝ) * W.clusterSize * exceptionalCount W := by
  obtain ⟨hmass, hgain⟩ := actual_half_selection_gates W hα hα1 hhost horder
  have hq : (0 : ℝ) < q := by
    have h := W.five_ordinaryParts_le_host
    have hp := W.ordinaryParts_pos
    have hqNat : 0 < q := by omega
    exact_mod_cast hqNat
  have ha4Q : 4 * α ≤ 1 := by linarith only [hα1]
  have ha4 : (4 : ℝ) * (α : ℝ) ≤ 1 := by exact_mod_cast ha4Q
  have ha : (α : ℝ) ≤ 1 / 4 := by linarith only [ha4]
  have ht : (11 : ℝ) * (fourthRoot α : ℝ) ^ 2 ≤ (α : ℝ) := by
    exact_mod_cast (reservoir_cleanup_bounds hα hα1).2.2.1
  have htq := mul_le_mul_of_nonneg_right ht hq.le
  have haq := mul_le_mul_of_nonneg_right ha hq.le
  have heta : (0 : ℝ) ≤ eta α := by exact_mod_cast (parameter_pos hα).2.2.1.le
  constructor
  · nlinarith only [hmass, htq, haq, hq]
  · have hr : (α : ℝ) / 16 ≤ 1 := by linarith only [ha]
    have hmul := mul_le_mul_of_nonneg_right hr
      (show 0 ≤ (eta α : ℝ) * W.clusterSize * exceptionalCount W by positivity)
    nlinarith only [hgain, hmul]

end Erdos547b.ZhaoSourceExceptionalCountBounds

#print axioms Erdos547b.ZhaoSourceExceptionalCountBounds.paddedVolume_bounds
#print axioms Erdos547b.ZhaoSourceExceptionalCountBounds.actual_half_selection_gates
#print axioms Erdos547b.ZhaoSourceExceptionalCountBounds.actual_nonextreme_gates
