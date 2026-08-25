import Mathlib.Algebra.Group.Basic

/-!
# Two involutions whose product has odd period

If the product of two involutions has period `2 * m + 1`, its `m`-th
power intertwines those involutions. This algebraic statement applies to
the actual affine isometries without any assumptions about a tiling action.
-/

namespace Puzzling139335.N4MiddleInvolutions.Reflection.Dynamics

/-- An odd period of a product of involutions gives an intertwining power. -/
theorem pow_mul_involution_eq_of_odd_period {G : Type*} [Group G]
    (e H : G) (he : e * e = 1) (hH : H * H = 1) (m : ℕ)
    (hperiod : (e * H) ^ (2 * m + 1) = 1) :
    (e * H) ^ m * e = H * (e * H) ^ m := by
  have hcancel : (e * H) ^ (m + 1) * (e * H) ^ m = 1 := by
    rw [← pow_add]
    simpa only [Nat.two_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hperiod
  have hinv : (e * H) ^ (m + 1) = ((e * H) ^ m)⁻¹ :=
    eq_inv_of_mul_eq_one_left hcancel
  calc
    (e * H) ^ m * e = (e * H) ^ (m + 1) * H := by
      rw [pow_succ, mul_assoc, mul_assoc, hH, mul_one]
    _ = ((e * H) ^ m)⁻¹ * H := by rw [hinv]
    _ = (H * e) ^ m * H := by
      rw [← inv_pow, mul_inv_rev,
        inv_eq_of_mul_eq_one_left he, inv_eq_of_mul_eq_one_left hH]
    _ = H * (e * H) ^ m := mul_pow_mul H e m

/-- Version with a separately named product. -/
theorem pow_mul_involution_eq_of_product_odd_period {G : Type*} [Group G]
    (e H g : G) (he : e * e = 1) (hH : H * H = 1) (hg : g = e * H)
    (m : ℕ) (hperiod : g ^ (2 * m + 1) = 1) :
    g ^ m * e = H * g ^ m := by
  subst g
  exact pow_mul_involution_eq_of_odd_period e H he hH m hperiod

end Puzzling139335.N4MiddleInvolutions.Reflection.Dynamics
