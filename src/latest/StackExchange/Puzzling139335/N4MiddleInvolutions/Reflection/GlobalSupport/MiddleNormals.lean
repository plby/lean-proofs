import StackExchange.Puzzling139335.N4MiddleInvolutions.Reflection.Hull
import StackExchange.Puzzling139335.N4MiddleInvolutions.Reflection.Coefficient
import StackExchange.Puzzling139335.N4MiddleInvolutions.Reflection.GlobalSupport.FiniteObstruction

/-! The finite-normal obstruction applied to the actual middle hull. -/

open Set ComplexConjugate

namespace Puzzling139335.N4MiddleInvolutions.Reflection

open PlaneIsometries

/-- In a protected-center outer-pair configuration, an ordinary reflection
between the middle pieces forces each unit supporting normal of their hull
to be purely imaginary. -/
theorem middleHull_unit_support_normal_re_eq_zero {d : SquareDissection}
    (h : N4OuterPair.Configuration d) (hc : d.HasProtectedCenter)
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (he : e '' d.piece 2 = d.piece 3)
    (c : ℂ) (u : Circle)
    (hform : ∀ p, complexEquiv (e p) =
      c + (u : ℂ) * conj ((complexEquiv p - c) / (u : ℂ)))
    {z : ℂ} (hz : z ∈ complexUnitSupportingNormals (middleHull d)) : z.re = 0 := by
  have heU : e '' middleUnion d = middleUnion d :=
    middleUnion_image_of_involution e (involutive_of_axis_form e c u hform) he
  have heK : e '' middleHull d = middleHull d :=
    middleHull_image_of_middleUnion_image d e heU
  obtain ⟨l, t, hl, hlt, ht, hstrip⟩ := middleHull_exists_strict_height_strip h hc
  have hheight : t - l < 1 := by linarith
  exact unit_support_normal_re_eq_zero_of_reflections
    (middleHull_convex d) (middleHull_subset_square d) hlt hheight hstrip
    e heK (middleHull_horizontal_image h) c u
    (axis_square_ne_one_of_middle_reflection h hc e he c u hform) hform hz

end Puzzling139335.N4MiddleInvolutions.Reflection
