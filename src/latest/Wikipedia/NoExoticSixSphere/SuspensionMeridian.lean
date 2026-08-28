import Wikipedia.NoExoticSixSphere.SphereProductSuspensionComparison

/-!
# The actual collapsed meridian of the suspension quotient

The exceptional fiber is the unit-sphere part of the closed half-plane
whose tail is a nonnegative multiple of the original stereographic pole.
This description includes both new poles. It is the genuine infinity
fiber of the constructed quotient; all remaining fibers are singleton.
-/

noncomputable section

open Set Function Topology
open scoped OnePoint

namespace NoExoticSixSphere.SuspensionProductComparison

def meridian (n : ℕ) : Set (Sphere (n + 1)) :=
  {y | ∃ c : ℝ, 0 ≤ c ∧ SphereCylinder.tail n y.val = c • (spherePole n).val}

def meridianCenter (n : ℕ) : Sphere (n + 1) :=
  SphereMapSuspension.equator n (spherePole n)

theorem tail_meridianCenter (n : ℕ) :
    SphereCylinder.tail n (meridianCenter n).val = (spherePole n).val := by
  ext i
  exact SphereMapSuspension.equator_tail (spherePole n) i

theorem meridianCenter_mem (n : ℕ) : meridianCenter n ∈ meridian n :=
  ⟨1, zero_le_one, by rw [one_smul, tail_meridianCenter]⟩

theorem neg_meridianCenter_not_mem (n : ℕ) : -meridianCenter n ∉ meridian n := by
  rintro ⟨c, hc, he⟩
  have hzero := congrArg (fun v : EuclideanSpace ℝ (Fin (n + 1)) ↦ v 0) he
  have ht : SphereCylinder.tail n (-meridianCenter n).val = -(spherePole n).val := by
    change SphereCylinder.tail n (-(meridianCenter n).val) = _
    rw [map_neg, tail_meridianCenter]
  rw [ht] at hzero
  have hp : (spherePole n).val 0 = 1 := by simp [spherePole]
  change -(spherePole n).val 0 = c * (spherePole n).val 0 at hzero
  rw [hp, mul_one] at hzero
  linarith

theorem inverse_pole_iff_meridian (n : ℕ) {y : Sphere (n + 1)}
    (hy : y ∈ SphereCylinder.band n) :
    (SphereCylinder.inverse n y).2 = spherePole n ↔ y ∈ meridian n := by
  have hn : ‖SphereCylinder.tail n y.val‖ ≠ 0 := norm_ne_zero_iff.mpr hy
  have hv : (SphereCylinder.inverse n y).2.val =
      ‖SphereCylinder.tail n y.val‖⁻¹ • SphereCylinder.tail n y.val := by
    change (SphereRadialRetraction.retract _ (SphereCylinder.tail n y.val)).val = _
    rw [SphereRadialRetraction.retract, dif_neg hy]
    rfl
  constructor
  · intro he
    refine ⟨‖SphereCylinder.tail n y.val‖, norm_nonneg _, ?_⟩
    have hh : ‖SphereCylinder.tail n y.val‖ • (SphereCylinder.inverse n y).2.val =
        SphereCylinder.tail n y.val := by
      rw [hv, smul_smul, mul_inv_cancel₀ hn, one_smul]
    rw [he] at hh
    exact hh.symm
  · rintro ⟨c, hc, he⟩
    have hc0 : c ≠ 0 := by
      intro h
      rw [h, zero_smul] at he
      exact hy he
    have hcp : 0 < c := lt_of_le_of_ne hc hc0.symm
    apply Subtype.ext
    change (SphereRadialRetraction.retract _ (SphereCylinder.tail n y.val)).val = _
    rw [SphereRadialRetraction.retract, dif_neg hy]
    change NormedSpace.normalize (SphereCylinder.tail n y.val) = (spherePole n).val
    rw [he, NormedSpace.normalize_smul_of_pos hcp]
    exact NormedSpace.normalize_eq_self_of_norm_eq_one (by simp)

theorem quotient_eq_infty_iff (n : ℕ) (y : Sphere (n + 1)) :
    quotient n y = ∞ ↔ y ∈ meridian n := by
  by_cases hy : y ∈ SphereCylinder.band n
  · have hq := quotient_point n (SphereCylinder.inverse n y)
    rw [SphereCylinder.point_inverse n y hy] at hq
    rw [hq, OnePointProduct.map_eq_infty_iff]
    simp only [OnePoint.coe_ne_infty, false_or]
    rw [Homeomorph.symm_apply_eq, euclideanOnePointSphere_infty]
    exact inverse_pole_iff_meridian n hy
  · have ht : SphereCylinder.tail n y.val = 0 := not_not.mp hy
    have hm : y ∈ meridian n := ⟨0, le_rfl, by rw [ht, zero_smul]⟩
    exact iff_of_true (quotient_of_not_mem_band n hy) hm

theorem isClosed_meridian (n : ℕ) : IsClosed (meridian n) := by
  have he : meridian n = (quotient n) ⁻¹' {∞} :=
    Set.ext fun y ↦ (quotient_eq_infty_iff n y).symm
  rw [he]
  exact OnePoint.isClosed_infty.preimage (quotient n).continuous

theorem isCompact_meridian (n : ℕ) : IsCompact (meridian n) :=
  (isClosed_meridian n).isCompact

theorem quotient_surjective (n : ℕ) : Surjective (quotient n) := by
  intro z
  induction z using OnePoint.rec with
  | infty => exact ⟨meridianCenter n, (quotient_eq_infty_iff n _).mpr (meridianCenter_mem n)⟩
  | coe p => exact ⟨finitePoint n p, quotient_finitePoint n p⟩

theorem isQuotientMap_quotient (n : ℕ) : IsQuotientMap (quotient n) :=
  IsQuotientMap.of_surjective_continuous (quotient_surjective n) (quotient n).continuous

theorem quotient_eq_iff (n : ℕ) (x y : Sphere (n + 1)) :
    quotient n x = quotient n y ↔ x = y ∨ x ∈ meridian n ∧ y ∈ meridian n := by
  constructor
  · intro h
    by_cases hx : quotient n x = ∞
    · exact Or.inr ⟨(quotient_eq_infty_iff n x).mp hx,
        (quotient_eq_infty_iff n y).mp (h.symm.trans hx)⟩
    · obtain ⟨p, hp⟩ := OnePoint.ne_infty_iff_exists.mp hx
      have hpx := (quotient_eq_coe_iff n x p).mp hp.symm
      have hpy := (quotient_eq_coe_iff n y p).mp (h.symm.trans hp.symm)
      exact Or.inl (hpx.symm.trans hpy)
  · rintro (rfl | ⟨hx, hy⟩)
    · rfl
    · exact ((quotient_eq_infty_iff n x).mpr hx).trans
        ((quotient_eq_infty_iff n y).mpr hy).symm

end NoExoticSixSphere.SuspensionProductComparison
