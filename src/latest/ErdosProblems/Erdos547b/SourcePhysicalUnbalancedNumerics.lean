/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceNearFullNumerics

/-! # Pay the physical-row exceptional-target and distinguished-edge errors -/

open scoped SimpleGraph Classical
noncomputable section

namespace Erdos547b.ZhaoSourcePhysicalUnbalancedNumerics

open Finset SimpleGraph Erdos547b.ZhaoSourceParameterSchedule
open Erdos547b.ZhaoSourceDegreeFormRootRows Erdos547b.ZhaoSourceDegreeFormBounds
open Erdos547b.ZhaoSourceNearFullNumerics Erdos547b.ZhaoEvenReducedPadding

theorem error_separation {α : ℚ} (hα : 0 < α) (hα1 : α ≤ 1 / 4) :
    2 * (epsilon α : ℝ) ≤ eta α ∧ 8 * (rootTypicality α : ℝ) ≤ eta α := by
  have hp := parameter_pos hα
  have ht : (0 : ℝ) ≤ fourthRoot α := by exact_mod_cast hp.2.2.2.1.le
  have hε : (epsilon α : ℝ) ≤ (degreeError α : ℝ) / 1000000 := by
    exact_mod_cast (reservoir_cleanup_bounds hα hα1).2.2.2.2.1
  have hδ : 4 * (rootTypicality α : ℝ) < (fourthRoot α : ℝ) ^ 2 / 2 := by
    exact_mod_cast (rootTypicality_margin hα hα1).2
  obtain ⟨hη, _, hd, hlast⟩ := parameter_bounds hα hα1
  constructor <;> linarith only [hε, hδ, hη, hd, hlast, ht]

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G)

theorem eta_mul_paddedHalf_large (hα : 0 < α) (hα1 : α ≤ 1 / 4) :
    1000000 < (eta α : ℝ) * paddedHalf (Index W) := by
  have hk : reducedHalfLower α ≤ paddedHalf (Index W) := by
    have h := W.lower_parts
    change 2 * reducedHalfLower α ≤ W.partition.parts.card at h
    simp only [paddedHalf, Index, Fintype.card_coe]
    omega
  have hp := parameter_pos hα
  have hε : epsilon α ≤ eta α := by
    have h := (error_separation hα hα1).1
    have hR : (epsilon α : ℝ) ≤ eta α := by
      have heR : (0 : ℝ) ≤ epsilon α := by exact_mod_cast hp.2.2.2.2.2.2.2.le
      linarith only [h, heR]
    exact_mod_cast hR
  have hcut : densityCutoff α ≤ 1 := by
    have hd := (reservoir_cleanup_bounds hα hα1).2.2.2.2.2
    unfold densityCutoff
    linarith only [hd]
  have hprodε : densityCutoff α * epsilon α ≤ epsilon α := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hcut hp.2.2.2.2.2.2.2.le
  have hprod : densityCutoff α * epsilon α ≤ eta α := hprodε.trans hε
  have hkQ : (reducedHalfLower α : ℚ) ≤ paddedHalf (Index W) := by exact_mod_cast hk
  have hs := mul_le_mul_of_nonneg_right hprod (Nat.cast_nonneg (reducedHalfLower α) : (0 : ℚ) ≤ _)
  have ht := mul_le_mul_of_nonneg_left hkQ hp.2.2.1.le
  have h : (1000000 : ℚ) < eta α * paddedHalf (Index W) :=
    (reducedHalfLower_product hα).trans_le (hs.trans ht)
  exact_mod_cast h

theorem exceptional_target_margin (hα : 0 < α) (hα1 : α ≤ 1 / 4) :
    2 * (rootTypicality α : ℝ) * Fintype.card (Index W) + 4 ≤
      (eta α : ℝ) * paddedHalf (Index W) := by
  have hδ : (0 : ℝ) ≤ rootTypicality α := by
    exact_mod_cast (rootTypicality_margin hα hα1).1.le
  have hc : (Fintype.card (Index W) : ℝ) ≤ 2 * paddedHalf (Index W) := by
    exact_mod_cast card_le_paddedCard (Index W)
  have hcδ := mul_le_mul_of_nonneg_left hc (by positivity : 0 ≤ 2 * (rootTypicality α : ℝ))
  have hscale := mul_le_mul_of_nonneg_right (error_separation hα hα1).2
    (Nat.cast_nonneg (paddedHalf (Index W)) : (0 : ℝ) ≤ _)
  have hlarge := eta_mul_paddedHalf_large W hα hα1
  nlinarith only [hcδ, hscale, hlarge]

end Erdos547b.ZhaoSourcePhysicalUnbalancedNumerics

#print axioms Erdos547b.ZhaoSourcePhysicalUnbalancedNumerics.error_separation
#print axioms Erdos547b.ZhaoSourcePhysicalUnbalancedNumerics.eta_mul_paddedHalf_large
#print axioms Erdos547b.ZhaoSourcePhysicalUnbalancedNumerics.exceptional_target_margin
