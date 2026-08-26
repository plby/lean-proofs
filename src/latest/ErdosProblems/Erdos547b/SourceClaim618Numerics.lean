/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Claim618RoundedNumerics
import ErdosProblems.Erdos547b.SourcePhysicalUnbalancedNumerics
import ErdosProblems.Erdos547b.SourceNearFullFromHost

/-! # The actual source schedule supplies all rounded Claim 6.18 gates -/

open scoped SimpleGraph Classical
noncomputable section
namespace Erdos547b.ZhaoSourceClaim618Numerics

open Finset SimpleGraph Erdos547b.ZhaoSourceParameterSchedule
open Erdos547b.ZhaoSourceDegreeFormRootRows Erdos547b.ZhaoSourceDegreeFormBounds
open Erdos547b.ZhaoSourceNearFullNumerics Erdos547b.ZhaoEvenReducedPadding
open Erdos547b.ZhaoSourcePhysicalUnbalancedNumerics Erdos547b.ZhaoSourceNearFullFromHost
open Erdos547b.ZhaoSourceNearFullMatching Erdos547b.ZhaoClaim618RoundedNumerics
open Erdos547b.ZhaoSourceClaim61Numerics

theorem parameter_gates {α : ℚ} (hα : 0 < α) (hα1 : α ≤ 1 / 4) :
    0 < (rhoOne α : ℝ) ∧ (rhoOne α : ℝ) ≤ 1 ∧ 0 ≤ (eta α : ℝ) ∧
      (eta α : ℝ) ≤ 1 / 100000 ∧ (eta α : ℝ) ≤ (rhoOne α : ℝ) ^ 2 / 1000 := by
  have hp := parameter_pos hα
  have hu := parameter_upper_bounds hα hα1
  have hr3 : rhoOne α ^ 3 ≤ rhoOne α ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hu.1 (sq_nonneg (rhoOne α))
    nlinarith only [h]
  have hρ : rho α ≤ 1 := hu.2.1.trans hu.1
  have he : eta α ≤ 1 / 100000 := by linarith only [hu.2.2.1, hρ]
  have her : eta α ≤ rhoOne α ^ 2 / 1000 := by
    have h := hu.2.2.1
    unfold rho at h
    linarith only [h, hr3, sq_nonneg (rhoOne α)]
  refine ⟨by exact_mod_cast hp.1, by exact_mod_cast hu.1,
    by exact_mod_cast hp.2.2.1.le, ?_, by exact_mod_cast her⟩
  have hcast : (eta α : ℝ) ≤ ((1 / 100000 : ℚ) : ℝ) := Rat.cast_le.mpr he
  norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] at hcast
  exact hcast

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G)

theorem actual_scales (hα : 0 < α) (hα1 : α ≤ 1 / 4) :
    1000 ≤ (rhoOne α : ℝ) ^ 2 * paddedHalf (Index W) ∧
      (missed W : ℝ) ≤ (rhoOne α : ℝ) * paddedHalf (Index W) / 100 := by
  obtain ⟨hr, hr1, he, _heSmall, her2⟩ := parameter_gates hα hα1
  have hlarge := eta_mul_paddedHalf_large W hα hα1
  have hk : (0 : ℝ) ≤ paddedHalf (Index W) := Nat.cast_nonneg _
  have hr2 : (rhoOne α : ℝ) ^ 2 ≤ rhoOne α := by
    nlinarith only [mul_nonneg hr.le (sub_nonneg.mpr hr1)]
  have her : (eta α : ℝ) ≤ rhoOne α := by linarith only [her2, hr2, hr]
  have her2k := mul_le_mul_of_nonneg_right her2 hk
  have herk := mul_le_mul_of_nonneg_right her hk
  have ht := (parameter_bounds hα hα1).2.2.2
  have ht0 : (0 : ℝ) ≤ fourthRoot α := by exact_mod_cast (parameter_pos hα).2.2.2.1.le
  have ht' : 8 * (fourthRoot α : ℝ) ^ 2 ≤ (eta α : ℝ) / 1000 := by
    nlinarith only [ht, ht0, sq_nonneg (fourthRoot α : ℝ)]
  have htk := mul_le_mul_of_nonneg_right ht' hk
  have hceil := Nat.ceil_lt_add_one (by positivity : 0 ≤ 4 * (fourthRoot α : ℝ) ^ 2 * paddedHalf (Index W))
  have hm : (missed W : ℝ) ≤ 8 * (fourthRoot α : ℝ) ^ 2 * paddedHalf (Index W) + 3 := by
    dsimp only [missed, matchingDefect]
    push_cast
    linarith only [hceil]
  constructor
  · nlinarith only [hlarge, her2k]
  · nlinarith only [hm, htk, herk, hlarge]

variable (Q : Certificate W) (S : CleanSourceWitness W Q)

theorem actual_gates {fb : ℝ} (O : Output W Q S fb) (hα : 0 < α) (hα1 : α ≤ 1 / 4) :
    let r := (rhoOne α : ℝ)
    let k := paddedHalf (Index W)
    0 < k ∧ 0 < initialCount r k ∧ (initialCount r k : ℝ) ≤ 8 * r * k ∧
    2 * (neighborCount r k + exceptionalCount (eta α : ℝ) k + 1) + missed W ≤ initialCount r k ∧
    partnerDegree r k + exceptionalCount (eta α : ℝ) k ≤ auxiliaryDegree r k ∧
    terminalCount r k * initialCount r k + O.D.V2.card * auxiliaryDegree r k ≤
      initialCount r k * neighborCount r k ∧
    16 * (rho α : ℝ) * (k : ℝ) ^ 2 ≤ (terminalCount r k * partnerDegree r k : ℕ) := by
  obtain ⟨hr, hr1, he, heSmall, her⟩ := parameter_gates hα hα1
  obtain ⟨hscale, hmiss⟩ := actual_scales W hα hα1
  have hv := (support_bounds W Q S O).2.2.2
  simpa only [rho, Rat.cast_pow] using rounded_gates (rhoOne α : ℝ) (eta α : ℝ)
    (paddedHalf (Index W)) (missed W) O.D.V2.card hr hr1 he heSmall her hscale hmiss hv

end Erdos547b.ZhaoSourceClaim618Numerics

#print axioms Erdos547b.ZhaoSourceClaim618Numerics.parameter_gates
#print axioms Erdos547b.ZhaoSourceClaim618Numerics.actual_scales
#print axioms Erdos547b.ZhaoSourceClaim618Numerics.actual_gates
