/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.Intersection.HighCoefficientThickness
import ErdosProblems.Erdos186.PZ.Intersection.NegateWitness

/-!
# High-coefficient radii on the reverse side

The second side of the intersection argument uses the reverse deviations
`a - x`.  This file supplies the reverse analogue of the forward radii from
`HighCoefficientThickness` and specializes the resulting estimates to the
witness obtained by negating the canonical witness for `A₂ - a`.
-/

namespace Erdos186.PZ.Intersection

noncomputable section

set_option autoImplicit false

/-- Negating a witness commutes with removing its reserved generators. -/
@[simp] theorem canonicalRoundingCore_negateEnhancedCFPWitness
    {d s Dmax k loss : ℕ} {X : Finset (LatticePoint d)}
    (W : CFP.EnhancedCFPWitness X s Dmax k loss) :
    canonicalRoundingCore (negateEnhancedCFPWitness W) =
      (canonicalRoundingCore W).image (fun x ↦ -x) := by
  classical
  simp only [canonicalRoundingCore, negateEnhancedCFPWitness.core,
    negateEnhancedCFPWitness.reserved]
  rw [Finset.image_sdiff W.core W.reserved neg_injective]

namespace ConvexPoolsData

variable {d : ℕ} {A : Finset (LatticePoint d)}
    {a₀ : realImage A} {c : realImage A → ℝ} {mu : ℝ}

/-- The centered-zonotope radius on the reverse deviation set. -/
def scaledReverseCoefficient (D : ConvexPoolsData A a₀ c mu)
    (scale : ℝ) (y : LatticePoint d) : ℝ :=
  scale * D.reverseCoefficient y

/-- Membership in the oriented reverse high-coefficient pool retains the
coefficient lower bound. -/
theorem reverseCoefficient_lower_of_mem_orientedTranslate_largeA₂
    (D : ConvexPoolsData A a₀ c mu) {theta : ℝ} {y : LatticePoint d}
    (hy : y ∈ orientedTranslate .reverse D.a (D.largeA₂ theta)) :
    theta ≤ D.reverseCoefficient y := by
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
  simpa [orientedDeviation] using D.coefficient_lower_largeA₂ hx

/-- A canonical CFP core selected directly on the oriented reverse pool has
uniformly positive scaled reverse radii. -/
theorem scaledReverseCoefficient_lower_on_canonicalRoundingCore
    (D : ConvexPoolsData A a₀ c mu) {theta scale : ℝ}
    (hscale : 0 ≤ scale) {s Dmax k loss : ℕ}
    (W : CFP.EnhancedCFPWitness
      (orientedTranslate .reverse D.a (D.largeA₂ theta))
      s Dmax k loss) :
    ∀ y ∈ canonicalRoundingCore W,
      scale * theta ≤ D.scaledReverseCoefficient scale y := by
  intro y hy
  dsimp only [scaledReverseCoefficient]
  exact mul_le_mul_of_nonneg_left
    (D.reverseCoefficient_lower_of_mem_orientedTranslate_largeA₂
      (W.core_subset (canonicalRoundingCore_subset_core W hy))) hscale

/-- The same reverse radii are nonnegative and inherit the original
coefficient cap. -/
theorem scaledReverseCoefficient_bounds_on_canonicalRoundingCore
    (D : ConvexPoolsData A a₀ c mu) {theta scale : ℝ}
    (hscale : 0 ≤ scale) {s Dmax k loss : ℕ}
    (W : CFP.EnhancedCFPWitness
      (orientedTranslate .reverse D.a (D.largeA₂ theta))
      s Dmax k loss) :
    ∀ y ∈ canonicalRoundingCore W,
      0 ≤ D.scaledReverseCoefficient scale y ∧
        D.scaledReverseCoefficient scale y ≤
          scale * (mu * A.card)⁻¹ := by
  intro y hy
  have hyInput : y ∈
      orientedTranslate .reverse D.a (D.largeA₂ theta) :=
    W.core_subset (canonicalRoundingCore_subset_core W hy)
  have hyFull : y ∈ orientedTranslate .reverse D.a D.A₂ := by
    rw [orientedTranslate] at hyInput ⊢
    exact (Finset.image_mono (orientedDeviation .reverse D.a)
      (D.largeA₂_subset theta)) hyInput
  have hb := D.reverseCoefficient_bounds hyFull
  dsimp only [scaledReverseCoefficient]
  exact ⟨mul_nonneg hscale hb.1,
    mul_le_mul_of_nonneg_left hb.2 hscale⟩

/-- The lower radius estimate, specialized to the canonical reverse witness
obtained from a witness selected on `A₂ - a`. -/
theorem scaledReverseCoefficient_lower_on_reverseCanonicalRoundingCore
    (D : ConvexPoolsData A a₀ c mu) {theta scale : ℝ}
    (hscale : 0 ≤ scale) {s Dmax k loss : ℕ}
    (W : CFP.EnhancedCFPWitness
      (Reduction.identifiedTranslate (D.largeA₂ theta) D.a)
      s Dmax k loss) :
    ∀ y ∈ canonicalRoundingCore
        (reverseEnhancedCFPWitnessOfIdentifiedTranslate
          D.a (D.largeA₂ theta) W),
      scale * theta ≤ D.scaledReverseCoefficient scale y := by
  exact D.scaledReverseCoefficient_lower_on_canonicalRoundingCore hscale
    (reverseEnhancedCFPWitnessOfIdentifiedTranslate
      D.a (D.largeA₂ theta) W)

/-- Nonnegativity and the coefficient cap, specialized to the canonical
reverse witness obtained from a witness selected on `A₂ - a`. -/
theorem scaledReverseCoefficient_bounds_on_reverseCanonicalRoundingCore
    (D : ConvexPoolsData A a₀ c mu) {theta scale : ℝ}
    (hscale : 0 ≤ scale) {s Dmax k loss : ℕ}
    (W : CFP.EnhancedCFPWitness
      (Reduction.identifiedTranslate (D.largeA₂ theta) D.a)
      s Dmax k loss) :
    ∀ y ∈ canonicalRoundingCore
        (reverseEnhancedCFPWitnessOfIdentifiedTranslate
          D.a (D.largeA₂ theta) W),
      0 ≤ D.scaledReverseCoefficient scale y ∧
        D.scaledReverseCoefficient scale y ≤
          scale * (mu * A.card)⁻¹ := by
  exact D.scaledReverseCoefficient_bounds_on_canonicalRoundingCore hscale
    (reverseEnhancedCFPWitnessOfIdentifiedTranslate
      D.a (D.largeA₂ theta) W)

end ConvexPoolsData

end

end Erdos186.PZ.Intersection
