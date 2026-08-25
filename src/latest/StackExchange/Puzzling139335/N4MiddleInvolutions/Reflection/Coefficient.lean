import StackExchange.Puzzling139335.N4MiddleInvolutions.Basic
import StackExchange.Puzzling139335.N4MiddleInvolutions.Reflection.NormalForm

/-!
# The middle mirror is not parallel to the horizontal midline

Two distinct parallel mirrors would give a nonzero translation preserving
the compact middle union. Coordinate maxima prove the needed contradiction
directly, without classifying a generated symmetry group.
-/

open Set ComplexConjugate

namespace Puzzling139335.N4MiddleInvolutions.Reflection

open PlaneIsometries

/-- The product of a middle reflection with the horizontal reflection has
a nonidentity rotation coefficient. -/
theorem axis_square_ne_one_of_middle_reflection {d : SquareDissection}
    (h : N4OuterPair.Configuration d) (hc : d.HasProtectedCenter)
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (he : e '' d.piece 2 = d.piece 3)
    (c : ℂ) (u : Circle)
    (hform : ∀ p, complexEquiv (e p) =
      c + (u : ℂ) * conj ((complexEquiv p - c) / (u : ℂ))) : u ^ 2 ≠ 1 := by
  intro hu
  have huC : (u : ℂ) ^ 2 = 1 := by
    simpa only [Circle.coe_pow, Circle.coe_one] using
      congrArg (fun v : Circle => (v : ℂ)) hu
  have heC (p : Plane) : complexEquiv (e p) = c + conj (complexEquiv p - c) := by
    rw [hform, ← complexReflection_axis_form]
    simp only [complexReflection, Circle.coe_pow, huC, one_mul]
  have he0 (p : Plane) : e p 0 = p 0 := by
    have hcoord := congrArg Complex.re (heC p)
    simp only [complexEquiv_re, Complex.add_re, Complex.conj_re,
      Complex.sub_re] at hcoord
    linarith
  have he1 (p : Plane) : e p 1 = 2 * c.im - p 1 := by
    have hcoord := congrArg Complex.im (heC p)
    simp only [complexEquiv_im, Complex.add_im, Complex.conj_im,
      Complex.sub_im] at hcoord
    linarith
  have heU : e '' middleUnion d = middleUnion d :=
    middleUnion_image_of_involution e (involutive_of_axis_form e c u hform) he
  have heMap : MapsTo e (middleUnion d) (middleUnion d) :=
    fun p hp => heU ▸ mem_image_of_mem e hp
  have hhMap : MapsTo ReflectionSeparation.horizontal (middleUnion d) (middleUnion d) :=
    fun p hp => (show ReflectionSeparation.horizontal '' middleUnion d = middleUnion d
      from h.middle_union_reflected) ▸ mem_image_of_mem _ hp
  obtain ⟨p, hp, hmax⟩ := (middleUnion_isCompact d).exists_isMaxOn
    (middleUnion_nonempty d) ((EuclideanSpace.proj 1).continuous.continuousOn)
  have hupper := isMaxOn_iff.mp hmax _ (heMap (hhMap hp))
  have hlower := isMaxOn_iff.mp hmax _ (hhMap (heMap hp))
  change e (ReflectionSeparation.horizontal p) 1 ≤ p 1 at hupper
  change ReflectionSeparation.horizontal (e p) 1 ≤ p 1 at hlower
  simp only [he1, ReflectionSeparation.horizontal_apply_one] at hupper hlower
  have haxis : 2 * c.im = 1 := by linarith
  apply center_not_fixed_of_middle_pair h hc e he
  apply plane_ext
  · exact he0 squareCenter
  · rw [he1, haxis, squareCenter_apply_one]
    norm_num

end Puzzling139335.N4MiddleInvolutions.Reflection
