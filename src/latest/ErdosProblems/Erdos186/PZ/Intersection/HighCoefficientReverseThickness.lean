/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.Intersection.HighCoefficientReverseCoefficient
import ErdosProblems.Erdos186.PZ.Intersection.ZonotopeSeparation

/-!
# High-coefficient zonotope thickness on the reverse side

This is the reverse-oriented counterpart of the forward thickness criterion.
The CFP witness is selected on `A₂ - a`, while the target generators are its
canonical negation in `a - A₂`.
-/

namespace Erdos186.PZ.Intersection

open scoped BigOperators

noncomputable section

set_option autoImplicit false

namespace ConvexPoolsData

variable {d : ℕ} {A : Finset (LatticePoint d)}
    {a₀ : realImage A} {c : realImage A → ℝ} {mu : ℝ}

/-- A narrow-slab cardinality estimate on the reverse canonical core implies
the requested coordinate cube lies in the reverse centered zonotope. -/
theorem cube_subset_centeredZonotope_of_highCoefficient_reverseSlabCard
    (D : ConvexPoolsData A a₀ c mu) {theta scale radius : ℝ}
    (htheta : 0 ≤ theta) (hscale : 0 ≤ scale)
    {s Dmax k loss slab : ℕ}
    (W : CFP.EnhancedCFPWitness
      (Reduction.identifiedTranslate (D.largeA₂ theta) D.a)
      s Dmax k loss)
    (threshold : ((Fin d → ℝ) →L[ℝ] ℝ) → ℝ)
    (hthreshold : ∀ f, 0 ≤ threshold f)
    (hslab : ∀ f : (Fin d → ℝ) →L[ℝ] ℝ, f ≠ 0 →
      ((canonicalRoundingCore
          (reverseEnhancedCFPWitnessOfIdentifiedTranslate
            D.a (D.largeA₂ theta) W)).filter fun x ↦
        ¬threshold f ≤ |f (realVector x)|).card ≤ slab)
    (hnumeric : ∀ f : (Fin d → ℝ) →L[ℝ] ℝ, f ≠ 0 →
      radius * ∑ i, |f (Pi.single i 1)| ≤
        threshold f * (scale * theta *
          (((Reduction.identifiedTranslate (D.largeA₂ theta) D.a).card -
            (loss + s + slab) : ℕ) : ℝ))) :
    {y : Fin d → ℝ | ∀ i, |y i| ≤ radius} ⊆
      centeredZonotope
        (canonicalRoundingCore
          (reverseEnhancedCFPWitnessOfIdentifiedTranslate
            D.a (D.largeA₂ theta) W))
        (D.scaledReverseCoefficient scale) := by
  let Wrev := reverseEnhancedCFPWitnessOfIdentifiedTranslate
    D.a (D.largeA₂ theta) W
  let input := orientedTranslate .reverse D.a (D.largeA₂ theta)
  let core := canonicalRoundingCore Wrev
  let q := D.scaledReverseCoefficient scale
  have hqnonneg : ∀ x ∈ core, 0 ≤ q x := by
    intro x hx
    exact (D.scaledReverseCoefficient_bounds_on_reverseCanonicalRoundingCore
      hscale W x hx).1
  apply cube_subset_centeredZonotope_of_outsideSlabMass
    core q hqnonneg radius threshold
  intro f
  by_cases hf : f = 0
  · subst f
    simp only [zero_apply, abs_zero,
      Finset.sum_const_zero, mul_zero]
    exact mul_nonneg (hthreshold 0) (Finset.sum_nonneg fun x hx ↦
      hqnonneg x (Finset.mem_filter.mp hx).1)
  let outside := core.filter fun x ↦ threshold f ≤ |f (realVector x)|
  have hcardNat : input.card - ((loss + s) + slab) ≤ outside.card := by
    apply card_sub_missing_slab_le_filter_ge input core
      (canonicalRoundingCore_subset_input Wrev)
      (fun x ↦ threshold f ≤ |f (realVector x)|) (loss + s) slab
    · exact card_sdiff_canonicalRoundingCore_le Wrev
    · simpa only [core, Wrev] using hslab f hf
  have hcardReal :
      (((input.card - (loss + s + slab) : ℕ) : ℝ)) ≤
        (outside.card : ℝ) := by
    exact_mod_cast hcardNat
  have hmass : scale * theta * (outside.card : ℝ) ≤
      ∑ x ∈ outside, q x := by
    apply minRadius_mul_card_filter_le_sum core q
      (fun x ↦ threshold f ≤ |f (realVector x)|) (scale * theta)
    intro x hx
    exact D.scaledReverseCoefficient_lower_on_reverseCanonicalRoundingCore
      hscale W x hx
  calc
    radius * ∑ i, |f (Pi.single i 1)| ≤
        threshold f * (scale * theta *
          ((((Reduction.identifiedTranslate (D.largeA₂ theta) D.a).card -
            (loss + s + slab) : ℕ)) : ℝ)) := hnumeric f hf
    _ = threshold f * (scale * theta *
          (((input.card - (loss + s + slab) : ℕ)) : ℝ)) := by
      simp only [input, card_orientedTranslate,
        Reduction.card_identifiedTranslate]
    _ ≤ threshold f * (scale * theta * (outside.card : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ (hthreshold f)
      exact mul_le_mul_of_nonneg_left hcardReal
        (mul_nonneg hscale htheta)
    _ ≤ threshold f * (∑ x ∈ outside, q x) :=
      mul_le_mul_of_nonneg_left hmass (hthreshold f)

end ConvexPoolsData

end

end Erdos186.PZ.Intersection
