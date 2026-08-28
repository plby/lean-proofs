import Wikipedia.HopfProblem.UnitQuaternionSphere
import Mathlib.Topology.Instances.Matrix
import Mathlib.Tactic.NoncommRing

/-!
# Quaternionic rank-one unitary transformations

These matrix identities are valid in every finite rank. They supply the
unitary column-completion maps used in quaternionic rank reduction.
-/

noncomputable section

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicRankOne

local notation "ℍ" => Quaternion ℝ

variable {N : Type*} [Fintype N] [DecidableEq N]

/-- The quaternionic Hermitian pairing, with conjugation in the first variable. -/
def pairing (u v : N → ℍ) : ℍ := ∑ i, star (u i) * v i

/-- A rank-one quaternionic matrix with the coefficient in its specified order. -/
def rankOne (u : N → ℍ) (c : ℍ) : Matrix N N ℍ :=
  fun i j => u i * c * star (u j)

omit [Fintype N] [DecidableEq N] in
theorem star_rankOne (u : N → ℍ) (c : ℍ) :
    star (rankOne u c) = rankOne u (star c) := by
  apply Matrix.ext
  intro i j
  simp only [Matrix.star_apply, rankOne, star_mul, star_star, mul_assoc]

omit [Fintype N] [DecidableEq N] in
theorem rankOne_add (u : N → ℍ) (c d : ℍ) :
    rankOne u (c + d) = rankOne u c + rankOne u d := by
  apply Matrix.ext
  intro i j
  simp only [rankOne, mul_add, add_mul, Matrix.add_apply]

omit [DecidableEq N] in
theorem rankOne_mul (u : N → ℍ) (c d : ℍ) :
    rankOne u c * rankOne u d = rankOne u (c * pairing u u * d) := by
  apply Matrix.ext
  intro i j
  simp only [Matrix.mul_apply, rankOne, pairing, Finset.mul_sum, Finset.sum_mul, mul_assoc]

theorem coefficient_identity (c : ℍ) (hc : c ≠ 0) :
    c * (c⁻¹ + (star c)⁻¹) * star c = star c + c := by
  rw [mul_add, add_mul, mul_inv_cancel₀ hc, one_mul, mul_assoc,
    inv_mul_cancel₀ (star_ne_zero.mpr hc), mul_one]

/-- A rank-one correction is unitary when its scalar coefficient matches the vector norm. -/
theorem one_sub_rankOne_unitary (u : N → ℍ) (c : ℍ) (hc : c ≠ 0)
    (hu : pairing u u = c⁻¹ + (star c)⁻¹) :
    1 - rankOne u c ∈ unitary (Matrix N N ℍ) := by
  have hleft : star c * pairing u u * c = c + star c := by
    rw [hu, add_comm c⁻¹]
    simpa only [star_star] using coefficient_identity (star c) (star_ne_zero.mpr hc)
  have hright : c * pairing u u * star c = star c + c := by
    rw [hu]
    exact coefficient_identity c hc
  constructor
  · rw [star_sub, star_one, star_rankOne, sub_mul, mul_sub, mul_sub,
      one_mul, mul_one, rankOne_mul, hleft, rankOne_add]
    simp only [one_mul]
    abel
  · rw [star_sub, star_one, star_rankOne, sub_mul, mul_sub, mul_sub,
      one_mul, mul_one, rankOne_mul, hright, rankOne_add]
    simp only [one_mul]
    abel

/-- The coordinate vector at a chosen index. -/
def axis (j : N) : N → ℍ := Pi.single j 1

omit [Fintype N] in
@[simp] theorem axis_self (j : N) : axis j j = 1 := by simp [axis]

omit [Fintype N] in
theorem axis_of_ne (i j : N) (h : i ≠ j) : axis j i = 0 := by simp [axis, h]

theorem pairing_add_axis (v : N → ℍ) (j : N) :
    pairing (v + axis j) (v + axis j) = pairing v v + star (v j) + v j + 1 := by
  simp only [pairing, Pi.add_apply, star_add, add_mul, mul_add, Finset.sum_add_distrib]
  have h₁ : (∑ i, star (v i) * axis j i) = star (v j) := by
    simp [axis, Pi.single_apply]
  have h₂ : (∑ i, star (axis j i) * v i) = v j := by
    simp [axis, Pi.single_apply, apply_ite]
  have h₃ : (∑ i, star (axis j i) * axis j i) = 1 := by
    simp [axis, Pi.single_apply]
  rw [h₁, h₂, h₃]
  abel

/-- The denominator is nonzero away from the antipodal coordinate value. -/
theorem one_add_star_ne_zero (a : ℍ) (ha : a ≠ -1) : 1 + star a ≠ 0 := by
  intro h
  have hs : star a = -1 := eq_neg_of_add_eq_zero_right h
  have ht := congrArg star hs
  simp only [star_star, star_neg, star_one] at ht
  exact ha ht

/-- The unnormalized Householder-type matrix sends the chosen axis to minus the unit column. -/
def columnReflectionMatrix (v : N → ℍ) (j : N) : Matrix N N ℍ :=
  1 - rankOne (v + axis j) (1 + star (v j))⁻¹

theorem columnReflectionMatrix_unitary (v : N → ℍ) (j : N)
    (hv : pairing v v = 1) (ha : v j ≠ -1) :
    columnReflectionMatrix v j ∈ unitary (Matrix N N ℍ) := by
  apply one_sub_rankOne_unitary _ _ (inv_ne_zero (one_add_star_ne_zero _ ha))
  simp only [pairing_add_axis, hv, inv_inv, star_inv₀, star_add, star_one, star_star]
  abel

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicRankOne
