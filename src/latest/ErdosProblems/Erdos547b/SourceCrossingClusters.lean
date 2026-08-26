/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceNearFullFromHost
import ErdosProblems.Erdos547b.Claim616SharpCrossing

/-!
# Actual crossing-cluster selection at the source scale

The integral scale is floor(rho*k/10). All rounding, missed-support and
reserved-support losses are paid from the actual degree-form volume.
-/

open scoped SimpleGraph BigOperators Classical
noncomputable section

namespace Erdos547b.ZhaoSourceCrossingClusters

open Finset SimpleGraph Erdos547EC2
open Erdos547b.ZhaoSourceNearFullFromHost Erdos547b.ZhaoSourceNearFullMatching
open Erdos547b.ZhaoSourceNearFullNumerics Erdos547b.ZhaoClaim616SharpCrossing
open Erdos547b.ZhaoSourceDegreeFormRootRows Erdos547b.ZhaoSourceDegreeFormBounds
open Erdos547b.ZhaoSourceParameterSchedule Erdos547b.ZhaoSourceExceptionalCountBounds
open Erdos547b.ZhaoStability Erdos547b.ZhaoEvenReducedPadding Erdos547b.ZhaoSourceClaim61Numerics

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G) (Q : Certificate W) (S : CleanSourceWitness W Q)

def crossingScale : ℕ := ⌊(rho α : ℝ) * paddedHalf (Index W) / 10⌋₊

theorem scale_bounds {fb : ℝ} (O : Output W Q S fb)
    (hα : 0 < α) (hα1 : α ≤ 1 / 4) (hhost : hostN = 2 * q)
    (horder : orderThreshold α M ≤ q) :
    0 < crossingScale W ∧
      (rho α : ℝ) * paddedHalf (Index W) / 20 ≤ (crossingScale W : ℝ) ∧
      10 * (crossingScale W : ℝ) ≤ (rho α : ℝ) * paddedHalf (Index W) ∧
      9 * crossingScale W ≤ paddedHalf (Index W) ∧
      missed W + (matchingSupport O.D.Mb).card + 4 ≤ crossingScale W := by
  subst hostN
  have hp := parameter_pos hα
  have hu := parameter_upper_bounds hα hα1
  obtain ⟨he, _, hd, ht⟩ := parameter_bounds hα hα1
  have hr : (0 : ℝ) < rho α := by exact_mod_cast hp.2.1
  have hr1 : (rho α : ℝ) ≤ 1 := by exact_mod_cast hu.2.1.trans hu.1
  have her : (eta α : ℝ) ≤ (rho α : ℝ) / 1000000 := by exact_mod_cast hu.2.2.1
  have hdρ : (degreeError α : ℝ) ≤ rho α := by linarith only [hd, her, hr]
  have hk0 : (0 : ℝ) ≤ paddedHalf (Index W) := Nat.cast_nonneg _
  have hq : (0 : ℝ) < q := by
    have hh := W.five_ordinaryParts_le_host
    have hc := W.ordinaryParts_pos
    have hn : 0 < q := by omega
    exact_mod_cast hn
  have hN := (degreeForm_source_bounds hα hα1 W horder).2.2
  have hv := (paddedVolume_bounds W hα hα1 rfl horder).1
  have hNk := mul_le_mul_of_nonneg_left hN hk0
  have hdk : (250 : ℝ) ≤ (degreeError α : ℝ) * paddedHalf (Index W) := by
    nlinarith only [hNk, hv, hq]
  have hρk : (250 : ℝ) ≤ (rho α : ℝ) * paddedHalf (Index W) :=
    hdk.trans (mul_le_mul_of_nonneg_right hdρ hk0)
  have hflo : (rho α : ℝ) * paddedHalf (Index W) / 10 < (crossingScale W : ℝ) + 1 := Nat.lt_floor_add_one _
  have hfhi : (crossingScale W : ℝ) ≤ (rho α : ℝ) * paddedHalf (Index W) / 10 :=
    Nat.floor_le (by positivity)
  have hlo : (rho α : ℝ) * paddedHalf (Index W) / 20 ≤ (crossingScale W : ℝ) := by
    linarith only [hρk, hflo]
  refine ⟨?_, hlo, by linarith only [hfhi], ?_, ?_⟩
  · have hpos : (0 : ℝ) < crossingScale W := by linarith only [hlo, hρk]
    exact_mod_cast hpos
  · have hρk1 := mul_le_mul_of_nonneg_right hr1 hk0
    have hbound : 9 * (crossingScale W : ℝ) ≤ paddedHalf (Index W) := by
      nlinarith only [hfhi, hρk1, mul_nonneg hr.le hk0]
    exact_mod_cast hbound
  · have hceil : (matchingDefect ((fourthRoot α : ℝ) ^ 2) (paddedHalf (Index W)) : ℝ) ≤
        4 * (fourthRoot α : ℝ) ^ 2 * paddedHalf (Index W) + 1 :=
      (Nat.ceil_lt_add_one (by positivity)).le
    have hmiss : (missed W : ℝ) ≤ 8 * (fourthRoot α : ℝ) ^ 2 * paddedHalf (Index W) + 3 := by
      unfold missed
      push_cast
      linarith only [hceil]
    have hreserved := reserved_support_bound W Q S O hα
    have htρ : 8 * (fourthRoot α : ℝ) ^ 2 + 4 * (fourthRoot α : ℝ) ≤ (rho α : ℝ) / 1000 := by
      linarith only [ht, her, hr, sq_nonneg (fourthRoot α : ℝ)]
    have htk := mul_le_mul_of_nonneg_right htρ hk0
    have hbound : (missed W : ℝ) + (matchingSupport O.D.Mb).card + 4 ≤ (crossingScale W : ℝ) := by
      nlinarith only [hmiss, hreserved, htk, hlo, hρk]
    exact_mod_cast hbound

theorem exists_crossingClusters {fb : ℝ} (O : Output W Q S fb)
    (hα : 0 < α) (hα1 : α ≤ 1 / 4) (hhost : hostN = 2 * q)
    (horder : orderThreshold α M ≤ q)
    (hcross : (rho α : ℝ) * (paddedHalf (Index W) : ℝ) ^ 2 <
      ((padGraph (reduced W)).interedges O.D.V1 O.D.V2).card) :
    ∃ C : Finset (EvenPadding (Index W)), C ⊆ O.D.V1 ∧ C ⊆ Q.claim67.O ∧
      C.card = crossingScale W ∧
      ∀ x ∈ C, 8 * crossingScale W ≤ degreeInto (padGraph (reduced W)) x
        (O.D.V2 ∩ (matchingSupport O.D.Mout \ matchingSupport O.D.Mb)) := by
  obtain ⟨_, _, hscale, h9, hbudget⟩ := scale_bounds W Q S O hα hα1 hhost horder
  have hST : O.D.V1.card + O.D.V2.card = 2 * paddedHalf (Index W) := by
    rw [O.D.V2_card, card_evenPadding]
    change O.D.V1.card + (2 * paddedHalf (Index W) - O.D.V1.card) = 2 * paddedHalf (Index W)
    have h := O.D.V1_card_upper
    omega
  have hcrossNat : 10 * crossingScale W * paddedHalf (Index W) <
      ((padGraph (reduced W)).interedges O.D.V1 O.D.V2).card := by
    have hscaled := mul_le_mul_of_nonneg_right hscale
      (Nat.cast_nonneg (paddedHalf (Index W)) : (0 : ℝ) ≤ paddedHalf (Index W))
    have hR : 10 * (crossingScale W : ℝ) * paddedHalf (Index W) <
        ((padGraph (reduced W)).interedges O.D.V1 O.D.V2).card := by nlinarith only [hscaled, hcross]
    exact_mod_cast hR
  have hheavy := card_crossHeavy_ge_of_balanced_cut (padGraph (reduced W)) O.D.V1 O.D.V2
    (crossingScale W) (paddedHalf (Index W)) O.D.V1_card_upper hST h9 hcrossNat
  exact exists_cluster_set_of_heavy (padGraph (reduced W)) (padFinset (large W))
    (missed W) (crossingScale W) Q.claim67 O.D.Min O.D.Mout O.D.Mb
    O.D.support_union O.D.V1_subset_O (by omega) hheavy

end Erdos547b.ZhaoSourceCrossingClusters

#print axioms Erdos547b.ZhaoSourceCrossingClusters.scale_bounds
#print axioms Erdos547b.ZhaoSourceCrossingClusters.exists_crossingClusters
