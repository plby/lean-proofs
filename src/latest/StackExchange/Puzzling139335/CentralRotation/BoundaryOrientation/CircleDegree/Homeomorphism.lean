import StackExchange.Puzzling139335.CentralRotation.BoundaryOrientation.CircleDegree.Maps
import StackExchange.Puzzling139335.CentralRotation.BoundaryOrientation.CircleLift

/-!
# The two degrees of circle homeomorphisms

The existence and monotonicity of a real lift are proved in `CircleLift`.
Here the actual lift formulas identify degree and select its orientation.
-/

noncomputable section

namespace Puzzling139335.CentralRotation.BoundaryOrientation.CircleDegree

/-- A circle homeomorphism viewed as a continuous map. -/
def homeomorphMap (e : Circle ≃ₜ Circle) : C(Circle, Circle) := ⟨e, e.continuous⟩

@[simp] theorem homeomorphMap_apply (e : Circle ≃ₜ Circle) (x : Circle) :
    homeomorphMap e x = e x := rfl

theorem degree_eq_one_of_increasing_lift (e : Circle ≃ₜ Circle) {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hlift : ∀ t : ℝ, (φ t : Circle) = e (t : Circle))
    (hmono : StrictMono φ) : degree (homeomorphMap e) = 1 := by
  rw [degree_eq_sub_of_lift (homeomorphMap e) hφ hlift]
  have h := increasing_lift_add_one e hφ hlift hmono 0
  simp only [zero_add] at h
  linarith

theorem degree_eq_neg_one_of_decreasing_lift (e : Circle ≃ₜ Circle) {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hlift : ∀ t : ℝ, (φ t : Circle) = e (t : Circle))
    (hanti : StrictAnti φ) : degree (homeomorphMap e) = -1 := by
  rw [degree_eq_sub_of_lift (homeomorphMap e) hφ hlift]
  have h := decreasing_lift_add_one e hφ hlift hanti 0
  simp only [zero_add] at h
  linarith

/-- Every circle homeomorphism has degree `1` or `-1`. -/
theorem degree_homeomorph_eq_one_or_neg_one (e : Circle ≃ₜ Circle) :
    degree (homeomorphMap e) = 1 ∨ degree (homeomorphMap e) = -1 := by
  obtain ⟨φ, hφ, hlift, hmono | hanti⟩ := exists_strictMono_or_strictAnti_lift e
  · exact Or.inl (degree_eq_one_of_increasing_lift e hφ hlift hmono)
  · exact Or.inr (degree_eq_neg_one_of_decreasing_lift e hφ hlift hanti)

theorem degree_homeomorph_ne_zero (e : Circle ≃ₜ Circle) :
    degree (homeomorphMap e) ≠ 0 := by
  rcases degree_homeomorph_eq_one_or_neg_one e with h | h <;> rw [h] <;> norm_num

/-- Negative degree supplies an actual decreasing real lift, including its
unit-period law. -/
theorem exists_decreasing_lift_of_degree_neg (e : Circle ≃ₜ Circle)
    (hdegree : degree (homeomorphMap e) < 0) :
    ∃ φ : ℝ → ℝ, Continuous φ ∧
      (∀ t : ℝ, (φ t : Circle) = e (t : Circle)) ∧
      StrictAnti φ ∧ ∀ t : ℝ, φ (t + 1) = φ t - 1 := by
  obtain ⟨φ, hφ, hlift, hmono | hanti⟩ := exists_monotone_lift e
  · have h := degree_eq_one_of_increasing_lift e hφ hlift hmono.1
    linarith
  · exact ⟨φ, hφ, hlift, hanti⟩

/-- Positive degree supplies an actual increasing real lift. -/
theorem exists_increasing_lift_of_degree_pos (e : Circle ≃ₜ Circle)
    (hdegree : 0 < degree (homeomorphMap e)) :
    ∃ φ : ℝ → ℝ, Continuous φ ∧
      (∀ t : ℝ, (φ t : Circle) = e (t : Circle)) ∧
      StrictMono φ ∧ ∀ t : ℝ, φ (t + 1) = φ t + 1 := by
  obtain ⟨φ, hφ, hlift, hmono | hanti⟩ := exists_monotone_lift e
  · exact ⟨φ, hφ, hlift, hmono⟩
  · have h := degree_eq_neg_one_of_decreasing_lift e hφ hlift hanti.1
    linarith

theorem degree_eq_neg_one_iff_decreasing_lift (e : Circle ≃ₜ Circle) :
    degree (homeomorphMap e) = -1 ↔
      ∃ φ : ℝ → ℝ, Continuous φ ∧
        (∀ t : ℝ, (φ t : Circle) = e (t : Circle)) ∧ StrictAnti φ := by
  constructor
  · intro h
    obtain ⟨φ, hφ, hlift, hanti, _⟩ := exists_decreasing_lift_of_degree_neg e (by linarith)
    exact ⟨φ, hφ, hlift, hanti⟩
  · rintro ⟨φ, hφ, hlift, hanti⟩
    exact degree_eq_neg_one_of_decreasing_lift e hφ hlift hanti

theorem degree_eq_one_iff_increasing_lift (e : Circle ≃ₜ Circle) :
    degree (homeomorphMap e) = 1 ↔
      ∃ φ : ℝ → ℝ, Continuous φ ∧
        (∀ t : ℝ, (φ t : Circle) = e (t : Circle)) ∧ StrictMono φ := by
  constructor
  · intro h
    obtain ⟨φ, hφ, hlift, hmono, _⟩ := exists_increasing_lift_of_degree_pos e (by linarith)
    exact ⟨φ, hφ, hlift, hmono⟩
  · rintro ⟨φ, hφ, hlift, hmono⟩
    exact degree_eq_one_of_increasing_lift e hφ hlift hmono

end Puzzling139335.CentralRotation.BoundaryOrientation.CircleDegree

end
