import StackExchange.Puzzling139335.CentralRotation.RotationAlgebra.Direct

/-!
# The algebra of the first overlapping boundary arc

Let `h` be the half-turn about `O` and `F = h ∘ g⁻¹`.  If `F` is a direct
nontranslation and `F^[m] ∘ g⁻¹` is a half-turn, its multiplier forces the
actual finite-period identity `F^[m+1] = id`.  The overlap map is consequently
`F⁻¹ ∘ h ∘ F`, centered at `g O`.

The direct formulas are explicit complex-coordinate data for actual affine
isometries.  The existence of the first overlap and its half-turn property
belong to the separate arc-topology argument.
-/

namespace Puzzling139335.CentralRotation.RotationAlgebra

open PlaneIsometries Set

/-- The multiplier of `F^[m] ∘ g⁻¹` is `-r^(m+1)` when `F = h ∘ g⁻¹`. -/
theorem overlap_map_coordinate_sub (F g : Plane ≃ᵃⁱ[ℝ] Plane) (O : Plane)
    (r : Circle) (b : ℂ)
    (hform : ∀ x, complexEquiv (F x) = (r : ℂ) * complexEquiv x + b)
    (hF : ∀ x, F x = AffineIsometryEquiv.pointReflection ℝ O (g.symm x))
    (m : ℕ) (x y : Plane) :
    complexEquiv (((F : Plane → Plane)^[m]) (g.symm x)) -
      complexEquiv (((F : Plane → Plane)^[m]) (g.symm y)) =
      -((r : ℂ) ^ (m + 1)) * (complexEquiv x - complexEquiv y) := by
  calc
    complexEquiv (((F : Plane → Plane)^[m]) (g.symm x)) -
        complexEquiv (((F : Plane → Plane)^[m]) (g.symm y)) =
        (r : ℂ) ^ m * (complexEquiv (g.symm x) - complexEquiv (g.symm y)) :=
      iterate_coordinate_sub hform m _ _
    _ = (r : ℂ) ^ m *
        ((2 * complexEquiv O - complexEquiv (F x)) -
          (2 * complexEquiv O - complexEquiv (F y))) := by
      rw [inverse_eq_reflection_comp F g O hF x,
        inverse_eq_reflection_comp F g O hF y,
        complex_pointReflection, complex_pointReflection]
    _ = -((r : ℂ) ^ (m + 1)) * (complexEquiv x - complexEquiv y) := by
      rw [hform, hform, pow_succ]
      ring

/-- The overlap map being a half-turn forces the rotational multiplier's
`(m+1)`st power to equal one. -/
theorem coefficient_pow_eq_one_of_overlap_halfTurn
    (F g : Plane ≃ᵃⁱ[ℝ] Plane) (O : Plane) (r : Circle) (b : ℂ)
    (hform : ∀ x, complexEquiv (F x) = (r : ℂ) * complexEquiv x + b)
    (hF : ∀ x, F x = AffineIsometryEquiv.pointReflection ℝ O (g.symm x))
    {m : ℕ} {z : Plane}
    (hk : ∀ x, ((F : Plane → Plane)^[m]) (g.symm x) =
      AffineIsometryEquiv.pointReflection ℝ z x) : (r : ℂ) ^ (m + 1) = 1 := by
  have hdiff := overlap_map_coordinate_sub F g O r b hform hF m
    (complexEquiv.symm 1) 0
  simp only [hk, complex_pointReflection, complexEquiv.apply_symm_apply,
    map_zero] at hdiff
  linear_combination hdiff

/-- All the affine conclusions of the first-overlap argument, including
the finite-period identity and the unique half-turn center. -/
theorem overlap_halfTurn_algebra (F g : Plane ≃ᵃⁱ[ℝ] Plane) (O : Plane)
    (r : Circle) (hr : r ≠ 1) (b : ℂ)
    (hform : ∀ x, complexEquiv (F x) = (r : ℂ) * complexEquiv x + b)
    (hF : ∀ x, F x = AffineIsometryEquiv.pointReflection ℝ O (g.symm x))
    {m : ℕ} {z : Plane}
    (hk : ∀ x, ((F : Plane → Plane)^[m]) (g.symm x) =
      AffineIsometryEquiv.pointReflection ℝ z x) :
    (r : ℂ) ^ (m + 1) = 1 ∧
      (F : Plane → Plane)^[m + 1] = id ∧
      (∀ x, ((F : Plane → Plane)^[m]) (g.symm x) =
        F.symm (AffineIsometryEquiv.pointReflection ℝ O (F x))) ∧ z = g O := by
  have hpower := coefficient_pow_eq_one_of_overlap_halfTurn F g O r b hform hF hk
  have hperiod := direct_iterate_eq_id_of_coefficient_ne_one F r hr b hform hpower
  refine ⟨hpower, hperiod, iterate_comp_inverse_eq_conjugate F g O hF hperiod, ?_⟩
  have hzfixed : ((F : Plane → Plane)^[m]) (g.symm z) = z := by
    rw [hk, AffineIsometryEquiv.pointReflection_self]
  have hcenter : AffineIsometryEquiv.pointReflection ℝ (g O) z = z :=
    (iterate_comp_inverse_eq_pointReflection F g O hF hperiod z).symm.trans hzfixed
  exact AffineIsometryEquiv.pointReflection_fixed_iff.mp hcenter

/-- Applying the algebra directly to `g` derives the required formula and
nonidentity coefficient of `F`; these are not extra geometric assumptions. -/
theorem first_overlap_center (F g : Plane ≃ᵃⁱ[ℝ] Plane) (O : Plane)
    (a : Circle) (b : ℂ)
    (hg : ∀ x, complexEquiv (g x) = (a : ℂ) * complexEquiv x + b)
    (hnot : ∀ c, g ≠ AffineIsometryEquiv.pointReflection ℝ c)
    (hF : ∀ x, F x = AffineIsometryEquiv.pointReflection ℝ O (g.symm x))
    {m : ℕ} {z : Plane}
    (hk : ∀ x, ((F : Plane → Plane)^[m]) (g.symm x) =
      AffineIsometryEquiv.pointReflection ℝ z x) : z = g O := by
  have ha := direct_coefficient_ne_neg_one_of_no_pointReflection g a b hg hnot
  have hr := neg_inv_coefficient_ne_one a ha
  exact (overlap_halfTurn_algebra F g O (-a⁻¹) hr
    (2 * complexEquiv O + (a : ℂ)⁻¹ * b)
    (direct_form_reflection_comp_inverse F g O a b hg hF) hF hk).2.2.2

/-- If the half-turn center lies on the image of the cut, the original
center lies on the cut itself. -/
theorem first_overlap_forces_center_mem (F g : Plane ≃ᵃⁱ[ℝ] Plane) (O : Plane)
    (a : Circle) (b : ℂ)
    (hg : ∀ x, complexEquiv (g x) = (a : ℂ) * complexEquiv x + b)
    (hnot : ∀ c, g ≠ AffineIsometryEquiv.pointReflection ℝ c)
    (hF : ∀ x, F x = AffineIsometryEquiv.pointReflection ℝ O (g.symm x))
    {m : ℕ} {z : Plane} {cut : Set Plane}
    (hk : ∀ x, ((F : Plane → Plane)^[m]) (g.symm x) =
      AffineIsometryEquiv.pointReflection ℝ z x)
    (hz : z ∈ g '' cut) : O ∈ cut := by
  have hcenter := first_overlap_center F g O a b hg hnot hF hk
  obtain ⟨x, hx, hxz⟩ := hz
  have hxO : x = O := g.injective (hxz.trans hcenter)
  exact hxO ▸ hx

end Puzzling139335.CentralRotation.RotationAlgebra
