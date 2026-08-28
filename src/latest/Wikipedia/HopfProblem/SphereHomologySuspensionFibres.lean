import Wikipedia.HopfProblem.SphereHomologySuspensionCoordinates

/-!
# Exact fibres of the latitude map

Two literal cylinder points have the same image exactly when they have
the same height and either lie on the same end slice or are identical.
Thus the equivalence relation is precisely the unreduced suspension
relation, not a quotient with additional identifications.
-/

noncomputable section

open scoped unitInterval

namespace Wikipedia.HopfProblem.SphereHomology.Latitude

theorem point_zero_eq (n : ℕ) (x y : UnitSphere n) : point n 0 x = point n 0 y := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · change radius 0 * x.val j = radius 0 * y.val j
    rw [radius_zero, zero_mul, zero_mul]

theorem point_one_eq (n : ℕ) (x y : UnitSphere n) : point n 1 x = point n 1 y := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · change radius 1 * x.val j = radius 1 * y.val j
    rw [radius_one, zero_mul, zero_mul]

/-- The latitude construction collapses exactly the two cylinder end slices. -/
theorem point_eq_iff (n : ℕ) (t s : unitInterval) (x y : UnitSphere n) :
    point n t x = point n s y ↔ t = s ∧ (t = 0 ∨ t = 1 ∨ x = y) := by
  constructor
  · intro h
    have hh := congrArg (fun p : UnitSphere (n + 1) => p.val 0) h
    change height t = height s at hh
    have ht : t = s := height_injective hh
    subst s
    refine ⟨rfl, ?_⟩
    by_cases h0 : t = 0
    · exact Or.inl h0
    by_cases h1 : t = 1
    · exact Or.inr (Or.inl h1)
    refine Or.inr (Or.inr ?_)
    ext i
    have hi := congrArg (fun p : UnitSphere (n + 1) => p.val i.succ) h
    change radius t * x.val i = radius t * y.val i at hi
    exact mul_left_cancel₀ (ne_of_gt (radius_pos_of_interior t h0 h1)) hi
  · rintro ⟨rfl, h0 | h1 | rfl⟩
    · subst t
      exact point_zero_eq n x y
    · subst t
      exact point_one_eq n x y
    · rfl

end Wikipedia.HopfProblem.SphereHomology.Latitude
