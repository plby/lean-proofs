import StackExchange.Puzzling139335.N4Diagonal.Contacts.Facing
import StackExchange.Puzzling139335.N4Diagonal.Contacts.Maps

/-!
# Actual side-contact exclusions in both diagonal assignments

The undesired side contacts of the explicit placements are empty or finite.
The facing-contact statements include equal angles and both endpoint angles;
they use the actual one-corner placements recorded by the model.
-/

open Set

namespace Puzzling139335.N4Diagonal

open ThreeCorners

private theorem image_contact_empty {P : Set Plane} {g : Plane → Plane}
    {i : Fin 2} {c : ℝ} (hpoint : ∀ x ∈ P, (g x) i ≠ c) :
    g '' P ∩ {x : Plane | x i = c} = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  rintro _ ⟨⟨x, hx, rfl⟩, hside⟩
  exact hpoint x hx hside

private theorem image_contact_finite {P : Set Plane} {g : Plane → Plane}
    {i : Fin 2} {c : ℝ} {v : Plane}
    (hpoint : ∀ x ∈ P, (g x) i = c → x = v) :
    (g '' P ∩ {x : Plane | x i = c}).Finite := by
  apply (finite_singleton (g v)).subset
  rintro _ ⟨⟨x, hx, rfl⟩, hside⟩
  exact congrArg g (hpoint x hx hside)

namespace Model

theorem top_contact_empty (m : Model) : m.P ∩ {x : Plane | x 1 = 1} = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  rintro x ⟨hx, hside⟩
  exact (ne_of_lt (m.coordinate_lt_one hx 1)) hside

theorem right_contact_empty (m : Model) : m.P ∩ {x : Plane | x 0 = 1} = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  rintro x ⟨hx, hside⟩
  exact (ne_of_lt (m.coordinate_lt_one hx 0)) hside

theorem reflected_bottom_contact_empty (m : Model) :
    ReflectionSeparation.antiDiagonal '' m.P ∩ {x : Plane | x 1 = 0} = ∅ := by
  apply image_contact_empty
  intro x hx hside
  rw [ReflectionSeparation.antiDiagonal_apply_one] at hside
  linarith [m.coordinate_lt_one hx 0]

theorem reflected_left_contact_empty (m : Model) :
    ReflectionSeparation.antiDiagonal '' m.P ∩ {x : Plane | x 0 = 0} = ∅ := by
  apply image_contact_empty
  intro x hx hside
  rw [ReflectionSeparation.antiDiagonal_apply_zero] at hside
  linarith [m.coordinate_lt_one hx 1]

/-- Assignment I: the first placement cannot reach the left side. -/
theorem firstPlus_one_left_empty (m : Model) :
    firstPlus 1 m.p m.θ '' m.P ∩ {x : Plane | x 0 = 0} = ∅ := by
  apply image_contact_empty
  intro x hx hside
  have hstrict := m.first_negative_ray_projection_lt_one hx
  rw [inner_neg_left] at hstrict
  simp only [firstPlus_one_apply, Matrix.cons_val_zero] at hside
  linarith

/-- Assignment II: the first placement cannot reach the right side. -/
theorem firstPlus_three_right_empty (m : Model) :
    firstPlus 3 m.p m.θ '' m.P ∩ {x : Plane | x 0 = 1} = ∅ := by
  apply image_contact_empty
  intro x hx hside
  have hstrict := m.first_negative_ray_projection_lt_one hx
  rw [inner_neg_left] at hstrict
  simp only [firstPlus_three_apply, Matrix.cons_val_zero] at hside
  linarith

/-- Assignment I, preserving parity: the last placement misses the bottom. -/
theorem lastPlus_three_bottom_empty (m : Model) :
    lastPlus 3 m.q m.β '' m.P ∩ {x : Plane | x 1 = 0} = ∅ := by
  apply image_contact_empty
  intro x hx hside
  have hstrict := m.last_negative_ray_projection_lt_one hx
  rw [inner_neg_left] at hstrict
  simp only [lastPlus_three_apply, Matrix.cons_val_one, Matrix.cons_val_fin_one] at hside
  linarith

/-- Assignment II, preserving parity: the last placement misses the top. -/
theorem lastPlus_one_top_empty (m : Model) :
    lastPlus 1 m.q m.β '' m.P ∩ {x : Plane | x 1 = 1} = ∅ := by
  apply image_contact_empty
  intro x hx hside
  have hstrict := m.last_negative_ray_projection_lt_one hx
  rw [inner_neg_left] at hstrict
  simp only [lastPlus_one_apply, Matrix.cons_val_one, Matrix.cons_val_fin_one] at hside
  linarith

/-- Assignment I, reversing parity: the last placement misses the right side. -/
theorem lastMinus_three_right_empty (m : Model) :
    lastMinus 3 m.q m.β '' m.P ∩ {x : Plane | x 0 = 1} = ∅ := by
  apply image_contact_empty
  intro x hx hside
  have hstrict := m.last_negative_ray_projection_lt_one hx
  rw [inner_neg_left] at hstrict
  simp only [lastMinus_three_apply, Matrix.cons_val_zero] at hside
  linarith

/-- Assignment II, reversing parity: the last placement misses the left side. -/
theorem lastMinus_one_left_empty (m : Model) :
    lastMinus 1 m.q m.β '' m.P ∩ {x : Plane | x 0 = 0} = ∅ := by
  apply image_contact_empty
  intro x hx hside
  have hstrict := m.last_negative_ray_projection_lt_one hx
  rw [inner_neg_left] at hstrict
  simp only [lastMinus_one_apply, Matrix.cons_val_zero] at hside
  linarith

theorem firstPlus_one_top_finite (m : Model) :
    (firstPlus 1 m.p m.θ '' m.P ∩ {x : Plane | x 1 = 1}).Finite := by
  apply image_contact_finite (v := m.q)
  intro x hx hside
  apply m.first_facing_contact_subset
  refine ⟨hx, ?_⟩
  simpa only [firstPlus_one_apply, Matrix.cons_val_one, Matrix.cons_val_fin_one] using hside

theorem firstPlus_three_bottom_finite (m : Model) :
    (firstPlus 3 m.p m.θ '' m.P ∩ {x : Plane | x 1 = 0}).Finite := by
  apply image_contact_finite (v := m.q)
  intro x hx hside
  apply m.first_facing_contact_subset
  refine ⟨hx, ?_⟩
  simp only [firstPlus_three_apply, Matrix.cons_val_one, Matrix.cons_val_fin_one] at hside
  linarith

theorem lastPlus_three_right_finite (m : Model) :
    (lastPlus 3 m.q m.β '' m.P ∩ {x : Plane | x 0 = 1}).Finite := by
  apply image_contact_finite (v := m.p)
  intro x hx hside
  apply m.last_facing_contact_subset
  refine ⟨hx, ?_⟩
  rw [inner_neg_left]
  simpa only [lastPlus_three_apply, Matrix.cons_val_zero] using hside

theorem lastPlus_one_left_finite (m : Model) :
    (lastPlus 1 m.q m.β '' m.P ∩ {x : Plane | x 0 = 0}).Finite := by
  apply image_contact_finite (v := m.p)
  intro x hx hside
  apply m.last_facing_contact_subset
  refine ⟨hx, ?_⟩
  rw [inner_neg_left]
  simp only [lastPlus_one_apply, Matrix.cons_val_zero] at hside
  linarith

theorem lastMinus_three_bottom_finite (m : Model) :
    (lastMinus 3 m.q m.β '' m.P ∩ {x : Plane | x 1 = 0}).Finite := by
  apply image_contact_finite (v := m.p)
  intro x hx hside
  apply m.last_facing_contact_subset
  refine ⟨hx, ?_⟩
  rw [inner_neg_left]
  simp only [lastMinus_three_apply, Matrix.cons_val_one, Matrix.cons_val_fin_one] at hside
  linarith

theorem lastMinus_one_top_finite (m : Model) :
    (lastMinus 1 m.q m.β '' m.P ∩ {x : Plane | x 1 = 1}).Finite := by
  apply image_contact_finite (v := m.p)
  intro x hx hside
  apply m.last_facing_contact_subset
  refine ⟨hx, ?_⟩
  rw [inner_neg_left]
  simpa only [lastMinus_one_apply, Matrix.cons_val_one, Matrix.cons_val_fin_one] using hside

end Model

end Puzzling139335.N4Diagonal
