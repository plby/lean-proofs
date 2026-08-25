import StackExchange.Puzzling139335.PlaneIsometries
import StackExchange.Puzzling139335.N4MiddleInvolutions.HalfTurn.Scalar

/-!
# An orientation-free obstruction to fitting the base and arm

The coordinate classification of an actual affine isometry supplies unit-circle
parameters. Obliqueness makes both parameters nonzero. The four strict coordinate
displacement bounds then contradict the scalar obstruction, for either parity of
the isometry. No change of placement or global orientation is assumed.
-/

open Set

namespace Puzzling139335.N4MiddleInvolutions.HalfTurn

open PlaneIsometries

noncomputable section

/-- An oblique image of the unit base and half-unit left arm cannot satisfy
all four strict half-unit displacement bounds about the image of `q`. -/
theorem oblique_base_arm_fit_impossible (e : Plane ≃ᵃⁱ[ℝ] Plane) (q : Plane)
    (hu : 1 / 2 ≤ q 0) (hv : q 1 ∈ Icc (0 : ℝ) (1 / 2))
    (hoblique₀ : e (!₂[0, 0] : Plane) 0 ≠ e (!₂[1, 0] : Plane) 0)
    (hoblique₁ : e (!₂[0, 0] : Plane) 1 ≠ e (!₂[1, 0] : Plane) 1)
    (hxA : |e (!₂[0, 0] : Plane) 0 - e q 0| < 1 / 2)
    (hyA : |e (!₂[0, 0] : Plane) 1 - e q 1| < 1 / 2)
    (hxM : |e (!₂[0, (1 / 2 : ℝ)] : Plane) 0 - e q 0| < 1 / 2)
    (hyM : |e (!₂[0, (1 / 2 : ℝ)] : Plane) 1 - e q 1| < 1 / 2) : False := by
  let A : Plane := !₂[0, 0]
  let B : Plane := !₂[1, 0]
  let M : Plane := !₂[0, (1 / 2 : ℝ)]
  obtain ⟨c, s, hunit, he | he⟩ := affine_coordinate_classification e
  all_goals
    have hcolumn₀ : e B 0 - e A 0 = c := by
      rw [he B, he A]
      simp [directCoordinates, reversingCoordinates, A, B]
    have hcolumn₁ : e B 1 - e A 1 = s := by
      rw [he B, he A]
      simp [directCoordinates, reversingCoordinates, A, B]
    have hc : c ≠ 0 := by
      intro hc
      exact hoblique₀ (sub_eq_zero.mp (hcolumn₀.trans hc)).symm
    have hs : s ≠ 0 := by
      intro hs
      exact hoblique₁ (sub_eq_zero.mp (hcolumn₁.trans hs)).symm
    rw [he A, he q] at hxA hyA
    rw [he M, he q] at hxM hyM
    simp only [directCoordinates, reversingCoordinates, A, M,
      Matrix.cons_val_zero, Matrix.cons_val_one, mul_zero, zero_add, sub_zero] at hxA hyA hxM hyM
  · apply abs_placement_bounds_impossible hc hs hunit hu hv.1 hv.2
    · rw [abs_lt] at hxA ⊢
      constructor <;> nlinarith only [hxA.1, hxA.2]
    · rw [abs_lt] at hyA ⊢
      constructor <;> nlinarith only [hyA.1, hyA.2]
    · rw [abs_lt] at hxM ⊢
      constructor <;> nlinarith only [hxM.1, hxM.2]
    · rw [abs_lt] at hyM ⊢
      constructor <;> nlinarith only [hyM.1, hyM.2]
  · have hunit' : c ^ 2 + (-s) ^ 2 = 1 := by simpa only [neg_sq] using hunit
    apply abs_placement_bounds_impossible hc (neg_ne_zero.mpr hs) hunit' hu hv.1 hv.2
    · rw [abs_lt] at hxA ⊢
      constructor <;> nlinarith only [hxA.1, hxA.2]
    · rw [abs_lt] at hyA ⊢
      constructor <;> nlinarith only [hyA.1, hyA.2]
    · rw [abs_lt] at hxM ⊢
      constructor <;> nlinarith only [hxM.1, hxM.2]
    · rw [abs_lt] at hyM ⊢
      constructor <;> nlinarith only [hyM.1, hyM.2]

end

end Puzzling139335.N4MiddleInvolutions.HalfTurn
