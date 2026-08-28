import Wikipedia.NoExoticSixSphere.JamesSphereClockCoordinates

/-!
# Distinct interior times of the actual suspension quotient

Equality with any non-pole value determines the time coordinate even
when the sphere letters differ. In particular the upper and lower
generator halves avoid the opposite punctures of the concrete cover.
-/

noncomputable section

open scoped unitInterval OnePoint

namespace NoExoticSixSphere.JamesSphere

theorem loopEvaluation_time_eq (n : ℕ) {x y : Sphere n} (hx : x ≠ spherePole n)
    {s t : I} (hs₀ : 0 < (s : ℝ)) (hs₁ : (s : ℝ) < 1)
    (h : loopEvaluation n (x, s) = loopEvaluation n (y, t)) : s = t := by
  have hx' : (euclideanOnePointSphere n).symm x ≠ OnePoint.infty := by
    intro he
    have he' := congrArg (euclideanOnePointSphere n) he
    rw [Homeomorph.apply_symm_apply, euclideanOnePointSphere_infty] at he'
    exact hx he'
  obtain ⟨a, ha⟩ := OnePoint.ne_infty_iff_exists.mp hx'
  obtain ⟨v, hv⟩ := OnePoint.ne_infty_iff_exists.mp (clock_ne_infty s hs₀ hs₁)
  have he := (EuclideanFactorProduct.productCoordinates n 1).onePointCongr.injective
    ((euclideanOnePointSphere (n + 1)).injective h)
  change OnePointProduct.map ((euclideanOnePointSphere n).symm x,
      CubicalProductSuspension.clock s) =
    OnePointProduct.map ((euclideanOnePointSphere n).symm y,
      CubicalProductSuspension.clock t) at he
  rw [← ha, ← hv, OnePointProduct.map_coe] at he
  have ht := ((OnePointProduct.map_eq_coe_iff _ (a, v)).mp he.symm).2
  have hc : CubicalProductSuspension.clock s = CubicalProductSuspension.clock t :=
    hv.symm.trans ht.symm
  rcases (clock_eq_iff s t).mp hc with hc | ⟨hc, _⟩
  · exact hc
  · rcases hc with hc | hc
    · have hz := congrArg Subtype.val hc
      change (s : ℝ) = 0 at hz
      linarith
    · have hz := congrArg Subtype.val hc
      change (s : ℝ) = 1 at hz
      linarith

theorem upper_half_avoids_lower (n : ℕ) (x : Sphere n) (t : I) (ht : (1 : ℝ) / 2 ≤ t) :
    loopEvaluation n (x, t) ≠ lowerPuncture n := by
  intro he
  have he' := loopEvaluation_time_eq n
    (SpherePoleCompactification.ne_neg (spherePole n)).symm
    (by norm_num [lowerTime]) (by norm_num [lowerTime]) he.symm
  have he'' := congrArg Subtype.val he'
  change (1 : ℝ) / 4 = (t : ℝ) at he''
  linarith

theorem lower_half_avoids_upper (n : ℕ) (x : Sphere n) (t : I) (ht : (t : ℝ) ≤ 1 / 2) :
    loopEvaluation n (x, t) ≠ upperPuncture n := by
  intro he
  have he' := loopEvaluation_time_eq n
    (SpherePoleCompactification.ne_neg (spherePole n)).symm
    (by norm_num [upperTime]) (by norm_num [upperTime]) he.symm
  have he'' := congrArg Subtype.val he'
  change (3 : ℝ) / 4 = (t : ℝ) at he''
  linarith

end NoExoticSixSphere.JamesSphere
