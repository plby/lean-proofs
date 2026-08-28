import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationExhaustionSequence
import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationExhaustionSmooth
import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationDbarPlane

/-!
# Global antiholomorphic primitives on the actual covering vector space

Every smooth closed `(0,1)` form on `ℂ²` has a genuine global smooth
primitive.  Local primitives are constructed by Cauchy–Green integrals;
their differences are approximated by actual entire polynomials; the
resulting geometrically compatible sequence is glued by its convergent
analytic tails.  No compact-support or global-Cousin hypothesis remains.
-/

noncomputable section

open scoped ContDiff

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassification

theorem exists_smooth_global_dbar_primitive {f g : ℂ × ℂ → ℂ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (hclosed : IsDbarClosed f g) :
    ∃ u : ℂ × ℂ → ℂ, ContDiff ℝ ∞ u ∧
      (∀ q, dbarFirst u q = f q) ∧ ∀ q, dbarSecond u q = g q := by
  obtain ⟨u, hu, hstage, hb⟩ := exists_compatible_primitiveSequence hf hg hclosed
  exact exists_smooth_primitive_of_exhaustion isOpen_exhaustionDomain monotone_exhaustionDomain
    cover_exhaustionDomain hu hstage hb

open PeriodTorusLineBundleClassificationPolydiscAnalytic (complexPairEquiv)

/-- The unrestricted global primitive in the actual `ComplexPlane₂`
coordinates, with derivatives defined by literal coordinate replacement. -/
theorem exists_smooth_global_dbar_primitive_cover {f g : ComplexPlane₂ → ℂ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hclosed : ∀ z, dbarCoordinate g 0 z = dbarCoordinate f 1 z) :
    ∃ u : ComplexPlane₂ → ℂ, ContDiff ℝ ∞ u ∧
      (∀ z, dbarCoordinate u 0 z = f z) ∧ ∀ z, dbarCoordinate u 1 z = g z := by
  have he : ContDiff ℝ ∞ complexPairEquiv.symm :=
    complexPairEquiv.symm.contDiff.restrict_scalars ℝ
  obtain ⟨u, hu, hdu, hdv⟩ := exists_smooth_global_dbar_primitive (hf.comp he) (hg.comp he)
    (pair_isDbarClosed hclosed)
  refine ⟨u ∘ complexPairEquiv, hu.comp (complexPairEquiv.contDiff.restrict_scalars ℝ), ?_, ?_⟩
  · intro z
    simpa only [dbarCoordinate_pair_zero, Function.comp_apply,
      ContinuousLinearEquiv.symm_apply_apply] using hdu (complexPairEquiv z)
  · intro z
    simpa only [dbarCoordinate_pair_one, Function.comp_apply,
      ContinuousLinearEquiv.symm_apply_apply] using hdv (complexPairEquiv z)

end Wikipedia.HopfProblem.PeriodTorusLineBundleClassification
