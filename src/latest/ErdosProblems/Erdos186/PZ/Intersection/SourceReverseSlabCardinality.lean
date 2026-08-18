/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.Intersection.SourceSlabCardinality
import ErdosProblems.Erdos186.PZ.Intersection.HighCoefficientReverseCoefficient

/-!
# Transporting source slab bounds to the reverse side

The selector is applied to the forward deviation set `X - a`, whereas the
second PZ side uses the negated witness on `a - X`.  Absolute values of real
linear functionals are invariant under this negation, so the canonical-core
slab cardinality is unchanged.
-/

namespace Erdos186.PZ.Intersection

noncomputable section

set_option autoImplicit false

/-- Transporting a witness across an equality of its indexed types leaves
the underlying canonical rounding core unchanged. -/
private theorem canonicalRoundingCore_eq_mpr
    {d s D k loss : ℕ} {X Y : Finset (LatticePoint d)}
    (h : X = Y)
    (W : CFP.EnhancedCFPWitness Y s D k loss) :
    canonicalRoundingCore
        (Eq.mpr (congrArg (fun Z ↦ CFP.EnhancedCFPWitness Z s D k loss) h) W) =
      canonicalRoundingCore W := by
  cases h
  rfl

/-- Negating the selected witness preserves the cardinality of every
absolute-functional slab in its canonical rounding core. -/
theorem card_filter_reverseCanonicalRoundingCore_abs_functional
    {d s D k loss : ℕ} {X : Finset (LatticePoint d)}
    (a : LatticePoint d)
    (W : CFP.EnhancedCFPWitness (Reduction.identifiedTranslate X a)
      s D k loss)
    (f : (Fin d → ℝ) →L[ℝ] ℝ) (u : ℝ) :
    ((canonicalRoundingCore
        (reverseEnhancedCFPWitnessOfIdentifiedTranslate a X W)).filter
        fun x ↦ |f (realVector x)| < u).card =
      ((canonicalRoundingCore W).filter
        fun x ↦ |f (realVector x)| < u).card := by
  classical
  have hcore :
      canonicalRoundingCore
          (reverseEnhancedCFPWitnessOfIdentifiedTranslate a X W) =
        (canonicalRoundingCore W).image (fun x ↦ -x) := by
    unfold reverseEnhancedCFPWitnessOfIdentifiedTranslate
    rw [canonicalRoundingCore_eq_mpr
      (orientedTranslate_reverse_eq_image_neg_identifiedTranslate a X)]
    exact canonicalRoundingCore_negateEnhancedCFPWitness W
  have hneg (y : LatticePoint d) :
      |f (realVector (-y))| = |f (realVector y)| := by
    have hvector : realVector (-y) = -realVector y := by
      ext i
      simp only [realVector, Pi.neg_apply, Int.cast_neg]
    rw [hvector, map_neg, abs_neg]
  rw [hcore]
  have hfilter :
      ((canonicalRoundingCore W).image (fun x ↦ -x)).filter
          (fun x ↦ |f (realVector x)| < u) =
        ((canonicalRoundingCore W).filter
          (fun x ↦ |f (realVector x)| < u)).image (fun x ↦ -x) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨⟨y, hy, rfl⟩, hfy⟩
      refine ⟨y, ⟨hy, ?_⟩, rfl⟩
      rwa [hneg] at hfy
    · rintro ⟨y, ⟨hy, hfy⟩, rfl⟩
      refine ⟨⟨y, hy, rfl⟩, ?_⟩
      rwa [hneg]
  rw [hfilter, Finset.card_image_of_injective _ neg_injective]

/-- A source slab-cardinality estimate for the selected forward witness can
therefore be used verbatim on the canonically oriented reverse witness. -/
theorem reverseCanonicalRoundingCore_slab_card_le_of_forward
    {d s D k loss slab : ℕ} {X : Finset (LatticePoint d)}
    (a : LatticePoint d)
    (W : CFP.EnhancedCFPWitness (Reduction.identifiedTranslate X a)
      s D k loss)
    (f : (Fin d → ℝ) →L[ℝ] ℝ) (u : ℝ)
    (hslab : ((canonicalRoundingCore W).filter
      fun x ↦ |f (realVector x)| < u).card ≤ slab) :
    ((canonicalRoundingCore
        (reverseEnhancedCFPWitnessOfIdentifiedTranslate a X W)).filter
      fun x ↦ |f (realVector x)| < u).card ≤ slab := by
  rw [card_filter_reverseCanonicalRoundingCore_abs_functional a W f u]
  exact hslab

end

end Erdos186.PZ.Intersection
