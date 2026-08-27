/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib.Algebra.Group.Units.Defs
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic

/-!
# The unit-group bijection behind prime presieve normalization

The ring need not be a field. Inverting only units makes the map valid
for arbitrary composite presieve moduli as well as the one-element ring.
-/

namespace Erdos4b.FGKMT

noncomputable section

variable {A ι : Type*} [CommRing A]

def preSieveUnitPullback (a : ι → A) (j : ι) (q u : Aˣ) : A :=
  ↑(q * u⁻¹) - a j

def preSieveUnitPushforward (a : ι → A) (j : ι) (q : Aˣ)
    (t : A) (ht : IsUnit (t + a j)) : Aˣ := q * ht.unit⁻¹

theorem preSieveUnitPullback_mul (a : ι → A) (j : ι) (q u : Aˣ) (i : ι) :
    (preSieveUnitPullback a j q u + a i) * (u : A) =
      (q : A) + (a i - a j) * (u : A) := by
  have hc : (↑(q * u⁻¹) : A) * u = q := by
    rw [Units.val_mul, mul_assoc, Units.inv_mul, mul_one]
  unfold preSieveUnitPullback
  linear_combination hc

theorem preSieveUnitPullback_isUnit_iff (a : ι → A) (j : ι) (q u : Aˣ) (i : ι) :
    IsUnit (preSieveUnitPullback a j q u + a i) ↔
      IsUnit ((q : A) + (a i - a j) * (u : A)) := by
  rw [← preSieveUnitPullback_mul, u.isUnit.mul_right_iff]

theorem preSieveUnitPullback_pushforward (a : ι → A) (j : ι) (q : Aˣ)
    (t : A) (ht : IsUnit (t + a j)) :
    preSieveUnitPullback a j q (preSieveUnitPushforward a j q t ht) = t := by
  have hg : q * (q * ht.unit⁻¹)⁻¹ = ht.unit := by
    rw [mul_inv_rev, inv_inv, mul_left_comm, mul_inv_cancel, mul_one]
  unfold preSieveUnitPullback preSieveUnitPushforward
  rw [hg, ht.unit_spec]
  ring

theorem preSieveUnitPushforward_pullback (a : ι → A) (j : ι) (q u : Aˣ)
    (hu : IsUnit (preSieveUnitPullback a j q u + a j)) :
    preSieveUnitPushforward a j q (preSieveUnitPullback a j q u) hu = u := by
  have huunit : hu.unit = q * u⁻¹ := by
    apply Units.ext
    rw [hu.unit_spec]
    simp only [preSieveUnitPullback, sub_add_cancel]
  unfold preSieveUnitPushforward
  rw [huunit]
  rw [mul_inv_rev, inv_inv, mul_left_comm, mul_inv_cancel, mul_one]

def preSieveUnitEquiv (a : ι → A) (j : ι) (q : Aˣ) :
    {u : Aˣ // ∀ i, IsUnit ((q : A) + (a i - a j) * (u : A))} ≃
      {t : A // ∀ i, IsUnit (t + a i)} where
  toFun u := ⟨preSieveUnitPullback a j q u.val,
    fun i => (preSieveUnitPullback_isUnit_iff a j q u.val i).mpr (u.property i)⟩
  invFun t := ⟨preSieveUnitPushforward a j q t.val (t.property j), fun i => by
    apply (preSieveUnitPullback_isUnit_iff a j q _ i).mp
    rw [preSieveUnitPullback_pushforward]
    exact t.property i⟩
  left_inv u := Subtype.ext (preSieveUnitPushforward_pullback a j q u.val _)
  right_inv t := Subtype.ext (preSieveUnitPullback_pushforward a j q t.val (t.property j))

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.preSieveUnitEquiv
