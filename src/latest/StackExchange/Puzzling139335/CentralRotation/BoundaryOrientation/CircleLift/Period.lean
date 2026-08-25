import StackExchange.Puzzling139335.CentralRotation.DecreasingLift

/-!
# The unit-period law for monotone real lifts

Injectivity of a circle homeomorphism prevents its real lift from traversing
more than one full turn on a unit interval.  The endpoints of that interval
have equal circle images, so their lifted difference is an integer.  Strict
monotonicity determines that integer as `1` or `-1`.
-/

open Set

namespace Puzzling139335.CentralRotation.BoundaryOrientation

private theorem lift_ne_on_open_unit_interval
    (e : AddCircle (1 : ℝ) ≃ₜ AddCircle (1 : ℝ)) {φ : ℝ → ℝ}
    (hlift : ∀ t : ℝ, (φ t : AddCircle (1 : ℝ)) = e (t : AddCircle (1 : ℝ)))
    {t u : ℝ} (hu : u ∈ Ioo t (t + 1)) :
    (φ u : AddCircle (1 : ℝ)) ≠ (φ t : AddCircle (1 : ℝ)) := by
  intro h
  have hsource : (u : AddCircle (1 : ℝ)) = (t : AddCircle (1 : ℝ)) := by
    apply e.injective
    simpa only [hlift] using h
  have hut : u = t :=
    (AddCircle.coe_eq_coe_iff_of_mem_Ico
      (show u ∈ Ico t (t + (1 : ℝ)) from ⟨hu.1.le, hu.2⟩)
      (show t ∈ Ico t (t + (1 : ℝ)) from ⟨le_rfl, by linarith⟩)).mp hsource
  exact (ne_of_gt hu.1) hut

private theorem lift_unit_interval_integer_shift
    (e : AddCircle (1 : ℝ) ≃ₜ AddCircle (1 : ℝ)) {φ : ℝ → ℝ}
    (hlift : ∀ t : ℝ, (φ t : AddCircle (1 : ℝ)) = e (t : AddCircle (1 : ℝ)))
    (t : ℝ) : ∃ n : ℤ, φ (t + 1) = φ t + n := by
  apply circle_eq_iff_exists_int.mp
  rw [hlift (t + 1), hlift t]
  apply congrArg e
  exact circle_eq_iff_exists_int.mpr ⟨1, by simp⟩

/-- An increasing real lift of a circle homeomorphism advances by one on each
unit interval. -/
theorem increasing_lift_add_one
    (e : AddCircle (1 : ℝ) ≃ₜ AddCircle (1 : ℝ)) {φ : ℝ → ℝ}
    (hφ : Continuous φ)
    (hlift : ∀ t : ℝ, (φ t : AddCircle (1 : ℝ)) = e (t : AddCircle (1 : ℝ)))
    (hmono : StrictMono φ) (t : ℝ) : φ (t + 1) = φ t + 1 := by
  have hspan : φ (t + 1) ≤ φ t + 1 := by
    by_contra h
    have hlarge : φ t + 1 < φ (t + 1) := lt_of_not_ge h
    obtain ⟨u, hu, heq⟩ :=
      intermediate_value_Ioo (show t ≤ t + 1 by linarith) hφ.continuousOn
        (show φ t + 1 ∈ Ioo (φ t) (φ (t + 1)) from ⟨by linarith, hlarge⟩)
    exact lift_ne_on_open_unit_interval e hlift hu
      (circle_eq_iff_exists_int.mpr ⟨1, by simpa using heq⟩)
  obtain ⟨n, hn⟩ := lift_unit_interval_integer_shift e hlift t
  have hpos : (0 : ℝ) < n := by
    have hlt := hmono (show t < t + 1 by linarith)
    linarith
  have hle : (n : ℝ) ≤ 1 := by linarith
  have hpos' : (0 : ℤ) < n := by exact_mod_cast hpos
  have hle' : n ≤ (1 : ℤ) := by exact_mod_cast hle
  have hn_one : n = 1 := by omega
  simpa only [hn_one, Int.cast_one] using hn

/-- A decreasing real lift of a circle homeomorphism retreats by one on each
unit interval. -/
theorem decreasing_lift_add_one
    (e : AddCircle (1 : ℝ) ≃ₜ AddCircle (1 : ℝ)) {φ : ℝ → ℝ}
    (hφ : Continuous φ)
    (hlift : ∀ t : ℝ, (φ t : AddCircle (1 : ℝ)) = e (t : AddCircle (1 : ℝ)))
    (hanti : StrictAnti φ) (t : ℝ) : φ (t + 1) = φ t - 1 := by
  have hspan : φ t - 1 ≤ φ (t + 1) := by
    by_contra h
    have hsmall : φ (t + 1) < φ t - 1 := lt_of_not_ge h
    obtain ⟨u, hu, heq⟩ :=
      intermediate_value_Ioo' (show t ≤ t + 1 by linarith) hφ.continuousOn
        (show φ t - 1 ∈ Ioo (φ (t + 1)) (φ t) from ⟨hsmall, by linarith⟩)
    exact lift_ne_on_open_unit_interval e hlift hu
      (circle_eq_iff_exists_int.mpr ⟨-1, by simpa [sub_eq_add_neg] using heq⟩)
  obtain ⟨n, hn⟩ := lift_unit_interval_integer_shift e hlift t
  have hneg : (n : ℝ) < 0 := by
    have hlt := hanti (show t < t + 1 by linarith)
    linarith
  have hle : (-1 : ℝ) ≤ n := by linarith
  have hneg' : n < (0 : ℤ) := by exact_mod_cast hneg
  have hle' : (-1 : ℤ) ≤ n := by exact_mod_cast hle
  have hn_neg_one : n = -1 := by omega
  simpa only [hn_neg_one, Int.cast_neg, Int.cast_one, sub_eq_add_neg] using hn

end Puzzling139335.CentralRotation.BoundaryOrientation
