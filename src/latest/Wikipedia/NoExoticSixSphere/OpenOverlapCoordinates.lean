import Wikipedia.NoExoticSixSphere.OpenOverlap

/-!
# Smooth overlap coordinates from an actual partial diffeomorphism

The overlap retains the same ambient point. A proved coordinate identity on
that actual overlap allows smoothness to be checked using a local coordinate
change, with source membership at every overlap point.
-/

open TopologicalSpace
open scoped Manifold ContDiff

namespace NoExoticSixSphere.OpenOverlap

variable {B H X E H' N F H'' P : Type*}
  [NormedAddCommGroup B] [NormedSpace ℝ B] [TopologicalSpace H]
  {I : ModelWithCorners ℝ B H} [TopologicalSpace X] (U V : Opens X)
  [ChartedSpace H U]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E H'} [TopologicalSpace N] [ChartedSpace H' N]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H'']
  {K : ModelWithCorners ℝ F H''} [TopologicalSpace P] [ChartedSpace H'' P]

theorem contMDiff_coordinates (c : U → N) (d : V → P)
    (Φ : PartialDiffeomorph J K N P ∞) (hc : ContMDiff I J ∞ c)
    (hsource : ∀ x : domain U V, c x.val ∈ Φ.source)
    (heq : ∀ x : domain U V, d (map U V x) = Φ (c x.val)) :
    ContMDiff I K ∞ (d ∘ map U V) := by
  intro x
  have hΦ := Φ.contMDiffOn_toFun.contMDiffAt (Φ.open_source.mem_nhds (hsource x))
  have hh := hΦ.comp x ((hc.comp contMDiff_subtype_val).contMDiffAt (x := x))
  exact hh.congr_of_eventuallyEq (Filter.Eventually.of_forall heq)

end NoExoticSixSphere.OpenOverlap
