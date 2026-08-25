import StackExchange.Puzzling139335.N4MiddleInvolutions.Basic
import StackExchange.Puzzling139335.RectangularHull.CornerGeometry
import Mathlib.Analysis.Convex.Hull

/-!
# The convex hull of the actual middle union

Compactness is used for the original union to obtain uniform strict height
bounds.  Convexity then extends those same bounds to its convex hull.
-/

open Set

namespace Puzzling139335.N4MiddleInvolutions.Reflection

def middleHull (d : SquareDissection) : Set Plane := convexHull ℝ (middleUnion d)

theorem middleUnion_subset_middleHull (d : SquareDissection) :
    middleUnion d ⊆ middleHull d := subset_convexHull ℝ (middleUnion d)

theorem middleHull_convex (d : SquareDissection) : Convex ℝ (middleHull d) :=
  convex_convexHull ℝ (middleUnion d)

theorem middleHull_nonempty (d : SquareDissection) : (middleHull d).Nonempty :=
  (middleUnion_nonempty d).mono (middleUnion_subset_middleHull d)

theorem middleHull_subset_square (d : SquareDissection) : middleHull d ⊆ unitSquare :=
  convexHull_min (middleUnion_subset_square d) RectangularHull.convex_unitSquare

theorem middleHull_image_of_middleUnion_image (d : SquareDissection)
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (he : e '' middleUnion d = middleUnion d) :
    e '' middleHull d = middleHull d := by
  exact (e.toAffineEquiv.toAffineMap.image_convexHull (middleUnion d)).trans
    (congrArg (convexHull ℝ) he)

theorem middleHull_horizontal_image {d : SquareDissection}
    (h : N4OuterPair.Configuration d) :
    ReflectionSeparation.horizontal '' middleHull d = middleHull d :=
  middleHull_image_of_middleUnion_image d _ h.middle_union_reflected

theorem middleUnion_strict_height {d : SquareDissection}
    (h : N4OuterPair.Configuration d) (hc : d.HasProtectedCenter)
    {p : Plane} (hp : p ∈ middleUnion d) : 0 < p 1 ∧ p 1 < 1 := by
  rcases hp with hp | hp
  · exact h.middle_strict_height hc (Or.inl rfl) hp
  · exact h.middle_strict_height hc (Or.inr rfl) hp

/-- Both extremal heights are attained in the actual middle union and
remain strict outer-side bounds for its whole convex hull. -/
theorem middleHull_exists_strict_height_strip {d : SquareDissection}
    (h : N4OuterPair.Configuration d) (hc : d.HasProtectedCenter) :
    ∃ l t : ℝ, 0 < l ∧ l ≤ t ∧ t < 1 ∧
      ∀ p ∈ middleHull d, l ≤ p 1 ∧ p 1 ≤ t := by
  obtain ⟨a, ha, hmin⟩ := (middleUnion_isCompact d).exists_isMinOn
    (middleUnion_nonempty d) ((EuclideanSpace.proj 1).continuous.continuousOn)
  obtain ⟨b, hb, hmax⟩ := (middleUnion_isCompact d).exists_isMaxOn
    (middleUnion_nonempty d) ((EuclideanSpace.proj 1).continuous.continuousOn)
  have hab : a 1 ≤ b 1 := isMinOn_iff.mp hmin _ hb
  refine ⟨a 1, b 1, (middleUnion_strict_height h hc ha).1, hab,
    (middleUnion_strict_height h hc hb).2, ?_⟩
  have hsub : middleUnion d ⊆ {p : Plane | p 1 ∈ Icc (a 1) (b 1)} := by
    intro p hp
    exact ⟨isMinOn_iff.mp hmin p hp, isMaxOn_iff.mp hmax p hp⟩
  exact convexHull_min hsub
    ((convex_Icc (a 1) (b 1)).linear_preimage (EuclideanSpace.proj 1).toLinearMap)

end Puzzling139335.N4MiddleInvolutions.Reflection
