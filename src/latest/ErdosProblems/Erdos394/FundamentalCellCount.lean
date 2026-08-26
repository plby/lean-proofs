import Mathlib.Algebra.Module.ZLattice.Basic

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Finite packing by translates of a fundamental domain
-/

open Set MeasureTheory
open scoped ENNReal Pointwise

namespace Erdos394

/-- A finite collection of lattice translates of a fundamental domain has
measure `|A| μ(F)`.  Consequently, if all those cells lie in `E`, their total
measure is at most `μ(E)`. -/
theorem fundamentalDomain_finset_card_mul_measure_le
    {G α : Type*} [AddGroup G] [AddAction G α]
    [MeasurableSpace α] [MeasurableConstVAdd G α]
    {F E : Set α} {μ : Measure α} [VAddInvariantMeasure G α μ]
    (hF : IsAddFundamentalDomain G F μ) (A : Finset G)
    (hsub : (⋃ g ∈ A, g +ᵥ F) ⊆ E) :
    (A.card : ℝ≥0∞) * μ F ≤ μ E := by
  have hdisj : Set.Pairwise (↑A)
      (fun g h : G ↦ AEDisjoint μ (g +ᵥ F) (h +ᵥ F)) := by
    intro g hg h hA hne
    exact hF.aedisjoint hne
  have hmeasure : μ (⋃ g ∈ A, g +ᵥ F) =
      ∑ g ∈ A, μ (g +ᵥ F) :=
    measure_biUnion_finset₀ hdisj fun g _ ↦ hF.nullMeasurableSet_vadd g
  calc
    (A.card : ℝ≥0∞) * μ F = ∑ g ∈ A, μ (g +ᵥ F) := by
      simp [measure_vadd, nsmul_eq_mul]
    _ = μ (⋃ g ∈ A, g +ᵥ F) := hmeasure.symm
    _ ≤ μ E := measure_mono hsub

/-- Real-valued form when the containing set has finite measure. -/
theorem fundamentalDomain_finset_card_mul_measureReal_le
    {G α : Type*} [AddGroup G] [AddAction G α]
    [MeasurableSpace α] [MeasurableConstVAdd G α]
    {F E : Set α} {μ : Measure α} [VAddInvariantMeasure G α μ]
    (hF : IsAddFundamentalDomain G F μ) (A : Finset G)
    (hsub : (⋃ g ∈ A, g +ᵥ F) ⊆ E) (hE : μ E ≠ ∞) :
    (A.card : ℝ) * μ.real F ≤ μ.real E := by
  have h := fundamentalDomain_finset_card_mul_measure_le hF A hsub
  have ht := ENNReal.toReal_mono hE h
  rw [ENNReal.toReal_mul] at ht
  norm_num at ht
  exact ht

end Erdos394
