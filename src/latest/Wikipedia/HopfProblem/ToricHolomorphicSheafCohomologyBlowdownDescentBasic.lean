import Wikipedia.HopfProblem.AffineBlowupExceptional
import Mathlib.Geometry.Manifold.Complex

/-!
# Continuous descent along the actual incidence blowdown

The restriction of a holomorphic function to the exceptional sphere is
constant by the compact complex maximum principle. All other fibres are
singletons. Properness and surjectivity of the actual projection then
give continuity of the descended function.
-/

noncomputable section

open Set Topology
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicSheafCohomology.BlowdownDescent

open AffineBlowup ToricCharts

local notation "I₂" => 𝓘(ℂ, CoordinateSpace 2)

theorem exceptional_values_eq {f : Space → ℂ} (hf : ContMDiff I₂ 𝓘(ℂ) ω f)
    (l m : RiemannSphere) : f (exceptionalInclusion l) = f (exceptionalInclusion m) :=
  ((hf.comp exceptionalInclusion_holomorphic).mdifferentiable (by simp)).apply_eq_of_compactSpace
    l m

theorem fibre_values_eq {f : Space → ℂ} (hf : ContMDiff I₂ 𝓘(ℂ) ω f)
    {x y : Space} (hxy : projection x = projection y) : f x = f y := by
  by_cases hx : projection x = 0
  · have hy : projection y = 0 := hxy.symm.trans hx
    have he (z : Space) (hz : projection z = 0) : exceptionalInclusion (direction z) = z := by
      apply Subtype.ext
      exact Prod.ext hz.symm rfl
    rw [← he x hx, ← he y hy]
    exact exceptional_values_eq hf _ _
  · have he : x = y := by
      apply Subtype.ext
      apply Prod.ext hxy
      apply incidence_direction_unique hx (incidence_point x)
      rw [hxy]
      exact incidence_point y
    rw [he]

/-- The value at any point above a base vector. Independence of the choice
is proved from holomorphicity, rather than assumed in this definition. -/
def descend (f : Space → ℂ) (v : CoordinateSpace 2) : ℂ :=
  f (projection_surjective v).choose

theorem descend_projection {f : Space → ℂ} (hf : ContMDiff I₂ 𝓘(ℂ) ω f) (x : Space) :
    descend f (projection x) = f x :=
  fibre_values_eq hf (projection_surjective (projection x)).choose_spec

theorem descend_comp_projection {f : Space → ℂ} (hf : ContMDiff I₂ 𝓘(ℂ) ω f) :
    descend f ∘ projection = f := funext (descend_projection hf)

theorem projection_isQuotientMap : IsQuotientMap projection :=
  projection_isClosedMap.isQuotientMap continuous_projection projection_surjective

theorem descend_continuous {f : Space → ℂ} (hf : ContMDiff I₂ 𝓘(ℂ) ω f) :
    Continuous (descend f) := by
  apply projection_isQuotientMap.continuous_iff.mpr
  rw [descend_comp_projection hf]
  exact hf.continuous

theorem descent_unique {f : Space → ℂ} {g h : CoordinateSpace 2 → ℂ}
    (hg : ∀ x, g (projection x) = f x) (hh : ∀ x, h (projection x) = f x) : g = h := by
  funext v
  obtain ⟨x, rfl⟩ := projection_surjective v
  exact (hg x).trans (hh x).symm

end Wikipedia.HopfProblem.HolomorphicSheafCohomology.BlowdownDescent
