/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.Intersection.HighCoefficientThickness
import ErdosProblems.Erdos186.PZ.Intersection.SourceSlabCardinality

/-!
# Source slab cardinality implies high-coefficient zonotope thickness

This file is the direct interface between the source-level slab contradiction
and the separating-hyperplane criterion for the forward high-coefficient
zonotope.  All remaining hypotheses are displayed scalar inequalities.
-/

namespace Erdos186.PZ.Intersection

open scoped BigOperators

noncomputable section

set_option autoImplicit false

theorem coefficientMass_nonneg {d : ℕ}
    (f : (Fin d → ℝ) →L[ℝ] ℝ) : 0 ≤ coefficientMass f := by
  unfold coefficientMass
  exact Finset.sum_nonneg fun _ _ ↦ abs_nonneg _

namespace ConvexPoolsData

/-- The source slab-cardinality theorem supplies the exact slab hypothesis
in `cube_subset_centeredZonotope_of_highCoefficient_slabCard`.  The final
radius inequality is scalar: it says the surviving high-coefficient mass is
large enough for the requested cube. -/
theorem exists_sourceForwardZonotopeThicknessConstants
    {beta eta : ℝ}
    {context : Reduction.HigherDimensionalContext beta eta}
    (selector : Reduction.BoundedCFPSelector context)
    {ambient : ℕ} {A : Finset (LatticePoint ambient)}
    (hA : selector.Eligible A)
    (hd : 0 < (selector.chosen A hA).dimension) :
    ∃ factorBound : ℕ, ∃ constant : ℝ, 1 ≤ constant ∧
      ∀ {delta gamma mu theta scale radius t : ℝ}
        {a₀ : realImage (selector.chosen A hA).identifiedCore}
        {c : realImage (selector.chosen A hA).identifiedCore → ℝ}
        (D : ConvexPoolsData
          (selector.chosen A hA).identifiedCore a₀ c mu)
        {s Dmax k loss slab : ℕ}
        (W : CFP.EnhancedCFPWitness
          (Reduction.identifiedTranslate (D.largeA₁ theta) D.a)
          s Dmax k loss),
        Reduction.IsBoundedCoordinateIrreducible selector A hA
            delta gamma →
        selector.CandidateClosedAt A hA delta →
        0 < gamma → 0 ≤ theta → 0 ≤ scale → 0 < t →
        delta * (A.card : ℝ) ≤ (slab : ℝ) →
        1 ≤ (2 * ((selector.chosen A hA).dimension : ℝ) * t) *
          ((controlIntegerBox (selector.chosen A hA).progression
            (2 * context.scaleDen
              (selector.chosen A hA).dimension)).carrier.card : ℝ) →
        (∀ (Z : Finset
            (LatticePoint (selector.chosen A hA).dimension))
          (hZ : selector.Eligible Z),
          delta * (A.card : ℝ) ≤ (Z.card : ℝ) →
          (2 : ℝ) ^ (selector.chosen A hA).dimension *
              (2 * (context.scaleDen
                (selector.chosen A hA).dimension : ℝ)) ^
                  (selector.chosen A hA).dimension *
              (3 : ℝ) ^ (selector.chosen A hA).dimension * constant *
              (((2 * context.scaleDen
                  (selector.chosen A hA).dimension + 1) ^
                    (selector.chosen A hA).dimension *
                  2 ^ (selector.chosen A hA).dimension : ℕ) : ℝ) <
            ((selector.chosen Z hZ).dilation : ℝ) * gamma) →
        (2 : ℝ) ^ (selector.chosen A hA).dimension *
              (2 * (context.scaleDen
                (selector.chosen A hA).dimension : ℝ)) ^
                  (selector.chosen A hA).dimension *
              (3 : ℝ) ^ (selector.chosen A hA).dimension * constant *
              (2 * ((selector.chosen A hA).dimension : ℝ) * t) *
              (((2 * context.scaleDen
                  (selector.chosen A hA).dimension + 1) ^
                    (selector.chosen A hA).dimension *
                  2 ^ (selector.chosen A hA).dimension : ℕ) : ℝ) <
            gamma →
        radius ≤ t * (scale * theta *
          (((Reduction.identifiedTranslate (D.largeA₁ theta) D.a).card -
            (loss + s + slab) : ℕ) : ℝ)) →
        {y : Fin (selector.chosen A hA).dimension → ℝ |
          ∀ i, |y i| ≤ radius} ⊆
          centeredZonotope (canonicalRoundingCore W)
            (D.scaledForwardCoefficient scale) := by
  obtain ⟨factorBound, constant, hconstant, hslabCard⟩ :=
    exists_sourceFunctionalSlabCardinalityConstants selector hA hd
  refine ⟨factorBound, constant, hconstant, ?_⟩
  intro delta gamma mu theta scale radius t a₀ c D s Dmax k loss slab W
    hirr hclosed hgamma htheta hscale ht hdenseSlab hboxScale hlow hfull
    hradius
  apply D.cube_subset_centeredZonotope_of_highCoefficient_slabCard
    htheta hscale W (fun f ↦ t * coefficientMass f)
  · intro f
    exact mul_nonneg ht.le (coefficientMass_nonneg f)
  · intro f hf
    simpa only [not_le] using
      hslabCard hirr hclosed hgamma (D.largeA₁ theta)
        ((D.largeA₁_subset theta).trans
          (D.A₁_subset_erase.trans (Finset.erase_subset _ _)))
        D.a
        ((selector.chosen A hA).identifiedCore_subset_coefficientBox D.a_mem)
        W f t gamma slab rfl hf ht hdenseSlab hboxScale hlow hfull
  · intro f _hf
    have hmass : 0 ≤ coefficientMass f := coefficientMass_nonneg f
    calc
      radius * ∑ i, |f (Pi.single i 1)| =
          radius * coefficientMass f := by rfl
      _ ≤ (t * (scale * theta *
          (((Reduction.identifiedTranslate (D.largeA₁ theta) D.a).card -
            (loss + s + slab) : ℕ) : ℝ))) * coefficientMass f :=
        mul_le_mul_of_nonneg_right hradius hmass
      _ = (t * coefficientMass f) * (scale * theta *
          (((Reduction.identifiedTranslate (D.largeA₁ theta) D.a).card -
            (loss + s + slab) : ℕ) : ℝ)) := by ring

end ConvexPoolsData

end

end Erdos186.PZ.Intersection
