import Wikipedia.HopfProblem.SingularCohomologyCupCochainsDifferential

/-!
# Exact cochains under Alexander–Whitney multiplication

These identities provide actual primitives when one factor is a
coboundary and the other is a cocycle.
-/

noncomputable section

namespace Wikipedia.HopfProblem.SingularCohomologyCup

open FirstHurewicz SingularCohomologyFree

variable {X : Type} [TopologicalSpace X]

@[simp] theorem castCochain_castCochain {l m n : ℕ} (h : l = m) (k : m = n)
    (α : Cochain X l) :
    castCochain k (castCochain h α) = castCochain (h.trans k) α := by
  subst m
  subst n
  rfl

theorem castCochain_injective {m n : ℕ} (h : m = n) :
    Function.Injective (castCochain (X := X) h) := by
  subst n
  exact fun _ _ hα => hα

theorem coboundary_castCochain {m n : ℕ} (h : m = n) (α : Cochain X m) :
    coboundary (castCochain h α) =
      castCochain (congrArg (fun k => k + 1) h) (coboundary α) := by
  subst n
  rfl

/-- The primitive of a left coboundary times a cocycle is their cup product. -/
theorem cup_coboundary_left_of_cocycle {p q : ℕ} (α : Cochain X p) (β : Cochain X q)
    (hβ : coboundary β = 0) :
    cup (coboundary α) β = castCochain (by omega) (coboundary (cup α β)) := by
  have h : coboundary (cup α β) =
      castCochain (by omega) (cup (coboundary α) β) := by
    rw [coboundary_cup_cast, hβ, cup_zero_right, smul_zero, add_zero]
  apply castCochain_injective (show (p + 1) + q = p + q + 1 by omega)
  simpa only [castCochain_castCochain, castCochain_rfl] using h.symm

/-- The sign-adjusted cup product is an actual primitive for a right coboundary. -/
theorem cup_coboundary_right_of_cocycle {p q : ℕ} (α : Cochain X p) (β : Cochain X q)
    (hα : coboundary α = 0) :
    cup α (coboundary β) = coboundary ((-1 : ℤ) ^ p • cup α β) := by
  have hs : (-1 : ℤ) ^ p * (-1 : ℤ) ^ p = 1 := by
    rw [← mul_pow]
    norm_num
  rw [coboundary_smul, coboundary_cup_cast, hα, cup_zero_left,
    castCochain_zero, zero_add, smul_smul, hs, one_smul]

end Wikipedia.HopfProblem.SingularCohomologyCup
