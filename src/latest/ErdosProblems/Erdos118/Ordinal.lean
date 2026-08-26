import ErdosProblems.Erdos118.Partition
import Mathlib.SetTheory.Cardinal.Ordinal

/-!
# The concrete ordinal used for Erdős Problem 118

Elementary ordinal and cardinal calculations, kept separate from the
positive and negative graph constructions to avoid circular imports.
-/

open Cardinal Ordinal

namespace Erdos118

/-- The intended concrete counterexample. Both exponents are ordinal. -/
noncomputable def lambda : Ordinal.{0} := ω ^ (ω ^ (2 : Ordinal))

theorem lambda_eq_natural_inner_power :
    lambda = (ω : Ordinal.{0}) ^ (ω ^ (2 : ℕ)) := by
  unfold lambda
  congr 1
  simpa using (Ordinal.opow_natCast (ω : Ordinal.{0}) 2)

theorem card_lambda : lambda.card = ℵ₀ := by
  have htwo : (ω : Ordinal.{0}) ^ (2 : Ordinal.{0}) = ω ^ (2 : ℕ) := by
    simpa using (Ordinal.opow_natCast (ω : Ordinal.{0}) 2)
  rw [lambda, Ordinal.card_omega0_opow
    (Ordinal.opow_ne_zero _ Ordinal.omega0_ne_zero), htwo, pow_two,
    Ordinal.card_mul, Ordinal.card_omega0, Cardinal.aleph0_mul_aleph0, max_self]

theorem lambda_countable : Countable lambda.ToType := by
  rw [← Cardinal.mk_le_aleph0_iff, Cardinal.mk_toType, card_lambda]

theorem omega_lt_lambda : (ω : Ordinal.{0}) < lambda := by
  have hexp : (1 : Ordinal.{0}) < ω ^ (2 : Ordinal.{0}) := by
    calc
      (1 : Ordinal.{0}) < ω := Ordinal.one_lt_omega0
      _ = ω ^ (1 : Ordinal.{0}) := (Ordinal.opow_one _).symm
      _ ≤ ω ^ (2 : Ordinal.{0}) := by
        exact Ordinal.opow_le_opow_right (a := (ω : Ordinal.{0}))
          (b := (1 : Ordinal.{0})) (c := (2 : Ordinal.{0}))
          Ordinal.omega0_pos (by simp)
  simpa only [lambda, Ordinal.opow_one] using
    (Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).mpr hexp

/-- A concrete guard against replacing red order type by red cardinality. -/
theorem same_cardinal_different_order_type :
    (ω : Ordinal.{0}).card = lambda.card ∧ (ω : Ordinal.{0}) ≠ lambda := by
  exact ⟨by rw [Ordinal.card_omega0, card_lambda], omega_lt_lambda.ne⟩

end Erdos118
