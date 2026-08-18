/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.Intersection.WeightedSourceThickness
import ErdosProblems.Erdos186.PZ.Intersection.HighCoefficientPostCFPAssembly

/-!
# The exact weighted source mass budget

This file records the scalar term produced by the weighted-slab argument at
the canonical coefficient scale.  It makes explicit the precise additional
source inequality that would be needed to turn the weighted cardinal slab
bound into positive zonotope thickness.
-/

namespace Erdos186.PZ.Intersection

noncomputable section

set_option autoImplicit false

namespace ConvexPoolsData

variable {d : ℕ} {A : Finset (LatticePoint d)}
    {a₀ : realImage A} {c : realImage A → ℝ} {mu : ℝ}

/-- At the canonical scale, every omitted point costs exactly `1 / 2` and
the uniform balanced-side mass lower bound is `mu * |A| / 4 - 1 / 2`. -/
theorem weightedRetainedMass_highCoefficientZonotopeScale
    (D : ConvexPoolsData A a₀ c mu) (hmu : 0 < mu) (omitted : ℕ) :
    highCoefficientZonotopeScale D *
          ((1 - 2 * (mu * A.card)⁻¹) / 2) -
        (omitted : ℝ) *
          (highCoefficientZonotopeScale D * (mu * A.card)⁻¹) =
      mu * (A.card : ℝ) / 4 - ((omitted : ℝ) + 1) / 2 := by
  have hscaleCap := D.highCoefficientZonotopeScale_mul_cap hmu
  rw [hscaleCap]
  have hcard : (0 : ℝ) < (A.card : ℝ) := by
    exact_mod_cast (Finset.card_pos.mpr ⟨D.a, D.a_mem⟩)
  have hne : mu * (A.card : ℝ) ≠ 0 := (mul_pos hmu hcard).ne'
  unfold highCoefficientZonotopeScale
  field_simp [hne]
  ring

/-- Consequently, positive retained weighted mass is equivalent to a single
strict source inequality.  In the application, `omitted = loss + s + slab`. -/
theorem weightedRetainedMass_highCoefficientZonotopeScale_pos_iff
    (D : ConvexPoolsData A a₀ c mu) (hmu : 0 < mu) (omitted : ℕ) :
    0 < highCoefficientZonotopeScale D *
          ((1 - 2 * (mu * A.card)⁻¹) / 2) -
        (omitted : ℝ) *
          (highCoefficientZonotopeScale D * (mu * A.card)⁻¹) ↔
      2 * ((omitted : ℝ) + 1) < mu * (A.card : ℝ) := by
  rw [D.weightedRetainedMass_highCoefficientZonotopeScale hmu]
  constructor <;> intro h <;> linarith

/-- Specialized spelling of the exact inequality after paying the CFP loss,
reserved directions, and the functional slab. -/
theorem weightedRetainedMass_source_pos_iff
    (D : ConvexPoolsData A a₀ c mu) (hmu : 0 < mu)
    (loss s slab : ℕ) :
    0 < highCoefficientZonotopeScale D *
          ((1 - 2 * (mu * A.card)⁻¹) / 2) -
        (((loss + s + slab : ℕ) : ℝ) *
          (highCoefficientZonotopeScale D * (mu * A.card)⁻¹)) ↔
      2 * ((((loss + s + slab : ℕ) : ℝ)) + 1) <
        mu * (A.card : ℝ) := by
  exact D.weightedRetainedMass_highCoefficientZonotopeScale_pos_iff hmu
    (loss + s + slab)

/-- The exact retained mass with a real-valued slab bound.  This is the
ceiling-free, strongest version of the weighted route. -/
theorem weightedRetainedMass_realSlab_highCoefficientZonotopeScale
    (D : ConvexPoolsData A a₀ c mu) (hmu : 0 < mu)
    (missing : ℕ) (slabBound : ℝ) :
    highCoefficientZonotopeScale D *
          ((1 - 2 * (mu * A.card)⁻¹) / 2) -
        ((missing : ℝ) + slabBound) *
          (highCoefficientZonotopeScale D * (mu * A.card)⁻¹) =
      mu * (A.card : ℝ) / 4 -
        ((missing : ℝ) + slabBound + 1) / 2 := by
  have hscaleCap := D.highCoefficientZonotopeScale_mul_cap hmu
  rw [hscaleCap]
  have hcard : (0 : ℝ) < (A.card : ℝ) := by
    exact_mod_cast (Finset.card_pos.mpr ⟨D.a, D.a_mem⟩)
  have hne : mu * (A.card : ℝ) ≠ 0 := (mul_pos hmu hcard).ne'
  unfold highCoefficientZonotopeScale
  field_simp [hne]
  ring

/-- Hence the strongest weighted argument still requires exactly
`2 * (missing + slabBound + 1) < mu * |A|`. -/
theorem weightedRetainedMass_realSlab_highCoefficientZonotopeScale_pos_iff
    (D : ConvexPoolsData A a₀ c mu) (hmu : 0 < mu)
    (missing : ℕ) (slabBound : ℝ) :
    0 < highCoefficientZonotopeScale D *
          ((1 - 2 * (mu * A.card)⁻¹) / 2) -
        ((missing : ℝ) + slabBound) *
          (highCoefficientZonotopeScale D * (mu * A.card)⁻¹) ↔
      2 * ((missing : ℝ) + slabBound + 1) <
        mu * (A.card : ℝ) := by
  rw [D.weightedRetainedMass_realSlab_highCoefficientZonotopeScale hmu]
  constructor <;> intro h <;> linarith

/-- Source specialization with the ideal ceiling-free slab budget
`delta * population`.  The left side is the exact mass available for a
separating-functional thickness argument. -/
theorem weightedRetainedMass_sourceDensity_pos_iff
    (D : ConvexPoolsData A a₀ c mu) (hmu : 0 < mu)
    (missing population : ℕ) (delta : ℝ) :
    0 < highCoefficientZonotopeScale D *
          ((1 - 2 * (mu * A.card)⁻¹) / 2) -
        ((missing : ℝ) + delta * (population : ℝ)) *
          (highCoefficientZonotopeScale D * (mu * A.card)⁻¹) ↔
      2 * ((missing : ℝ) + delta * (population : ℝ) + 1) <
        mu * (A.card : ℝ) := by
  exact D.weightedRetainedMass_realSlab_highCoefficientZonotopeScale_pos_iff
    hmu missing (delta * (population : ℝ))

end ConvexPoolsData

end

end Erdos186.PZ.Intersection
