import Wikipedia.NoExoticSixSphere.QuaternionCommutatorNativePrimitivity
import Wikipedia.HomotopyGroupsOfSpheres.SphereThreeSix

/-!
# The original quaternionic Samelson square has order twelve

The explicit seven-sphere map proves generation by this particular
commutator class. Combining generation with the actual sixth sphere
group calculation determines its exact order. In particular, the
class is not a square in the native sixth quaternion homotopy group.
-/

noncomputable section

open scoped Topology

namespace NoExoticSixSphere.QuaternionSamelsonOrder

open Wikipedia.HomotopyGroupsOfSpheres QuaternionSamelson
open Wikipedia.HopfProblem.UnitQuaternionSphere
open QuaternionCommutatorNativeSphere

def residueEquiv : π_ 6 UnitQuaternions 1 ≃* Multiplicative (ZMod 12) :=
  (homeomorphMulEquiv (N := Fin 6) sphereHomeomorph 1).trans
    (pi6_sphere_three_mulEquiv (sphereHomeomorph 1))

theorem card_twelve : Nat.card (π_ 6 UnitQuaternions 1) = 12 := by
  rw [Nat.card_congr residueEquiv.toEquiv]
  simp

theorem orderOf_nu : orderOf nu = 12 :=
  (orderOf_eq_card_of_zpowers_eq_top samelsonSubgroup_eq_top).trans card_twelve

theorem nu_pow_eq_one_iff_dvd (k : ℕ) : nu ^ k = 1 ↔ 12 ∣ k := by
  rw [← orderOf_dvd_iff_pow_eq_one, orderOf_nu]

theorem nu_zpow_eq_one_iff_dvd (k : ℤ) : nu ^ k = 1 ↔ (12 : ℤ) ∣ k := by
  rw [← orderOf_dvd_iff_zpow_eq_one, orderOf_nu]
  norm_num

theorem nu_pow_twelve : nu ^ 12 = 1 :=
  (nu_pow_eq_one_iff_dvd 12).mpr (dvd_refl 12)

theorem nu_pow_six_ne_one : nu ^ 6 ≠ 1 := by
  rw [ne_eq, nu_pow_eq_one_iff_dvd]
  decide

theorem pow_twelve (a : π_ 6 UnitQuaternions 1) : a ^ 12 = 1 := by
  have h := pow_card_eq_one' (x := a)
  rwa [card_twelve] at h

theorem square_ne_nu (a : π_ 6 UnitQuaternions 1) : a ^ 2 ≠ nu := by
  intro h
  apply nu_pow_six_ne_one
  rw [← h, ← pow_mul]
  exact pow_twelve a

end NoExoticSixSphere.QuaternionSamelsonOrder
