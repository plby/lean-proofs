import StackExchange.Puzzling139335.N4MiddleInvolutions.Reflection.SupportTransport
import StackExchange.Puzzling139335.N4MiddleInvolutions.Reflection.FiniteNormals

/-!
# The finite-normal obstruction in a strict horizontal strip

Horizontal reflection and an ordinary reflection with a nonidentity
rotation product constrain every unit supporting segment of a convex set
in a strict-height substrip of the square to have a purely imaginary normal.
The support-normal actions come from invariance of this actual set.
-/

open Set ComplexConjugate

namespace Puzzling139335.N4MiddleInvolutions.Reflection

open PlaneIsometries

/-- In a strip of height less than one, two reflection symmetries with a
nonidentity rotation product force every unit supporting normal to have
zero real coordinate. -/
theorem unit_support_normal_re_eq_zero_of_reflections {K : Set Plane}
    (hConv : Convex ℝ K) (hSquare : K ⊆ unitSquare)
    {l t : ℝ} (hlt : l ≤ t) (hheight : t - l < 1)
    (hstrip : ∀ p ∈ K, l ≤ p 1 ∧ p 1 ≤ t)
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (heK : e '' K = K)
    (hhK : ReflectionSeparation.horizontal '' K = K)
    (c : ℂ) (u : Circle) (hu : u ^ 2 ≠ 1)
    (hform : ∀ p, complexEquiv (e p) =
      c + (u : ℂ) * conj ((complexEquiv p - c) / (u : ℂ)))
    {z : ℂ} (hz : z ∈ complexUnitSupportingNormals K) : z.re = 0 := by
  obtain ⟨s, hs, hcard⟩ :=
    exists_finset_complexUnitSupportingNormals hConv hSquare hlt hheight hstrip
  have hmem (w : ℂ) : w ∈ s ↔ w ∈ complexUnitSupportingNormals K := by
    change w ∈ (s : Set ℂ) ↔ _
    rw [hs]
  have hrot : ∀ w ∈ s, ((u ^ 2 : Circle) : ℂ) * w ∈ s := by
    intro w hw
    apply (hmem _).mpr
    exact mul_mem_complexSupportingNormalsAtLeast_of_axis_form_and_horizontal
      e heK hhK c u hform ((hmem w).mp hw)
  have hconj : ∀ w ∈ s, conj w ∈ s := by
    intro w hw
    apply (hmem _).mpr
    exact conj_mem_complexSupportingNormalsAtLeast_of_horizontal hhK ((hmem w).mp hw)
  rcases re_eq_zero_or_exists_im_eq_zero s hcard (u ^ 2) hu hrot hconj
      ((hmem z).mpr hz) with hzre | ⟨w, hw, hwim⟩
  · exact hzre
  · exact (not_mem_complexUnitSupportingNormals_of_im_eq_zero hstrip hheight hwim
      ((hmem w).mp hw)).elim

end Puzzling139335.N4MiddleInvolutions.Reflection
