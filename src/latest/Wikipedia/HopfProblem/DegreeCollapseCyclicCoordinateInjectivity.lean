import Mathlib.Tactic

/-!
# A nonzero integer homomorphism on a subgroup of the integers is injective

An injective integer coordinate gives the proportionality relation between
any two original elements. A second nonzero integer coordinate can then
have no nonzero kernel. This avoids choosing a generator of the subgroup.
-/

noncomputable section

open Function

namespace Wikipedia.HopfProblem.DegreeCollapse.CyclicCoordinateInjectivity

variable {G : Type*} [AddCommGroup G]

theorem proportional (i : G →+ ℤ) (hi : Injective i) (x y : G) :
    i x • y = i y • x := by
  apply hi
  rw [map_zsmul, map_zsmul, zsmul_eq_mul, zsmul_eq_mul, Int.cast_id, Int.cast_id, mul_comm]

theorem injective_of_nonzero (i : G →+ ℤ) (hi : Injective i) (j : G →+ ℤ)
    (hj : ∃ w : G, j w ≠ 0) : Injective j := by
  obtain ⟨w, hw⟩ := hj
  intro x y hxy
  have hz : j (x - y) = 0 := by rw [map_sub, hxy, sub_self]
  have he := congrArg j (proportional i hi (x - y) w)
  simp only [map_zsmul, zsmul_eq_mul, Int.cast_id, hz, mul_zero] at he
  have hi0 : i (x - y) = 0 := (mul_eq_zero.mp he).resolve_right hw
  have hx0 : x - y = 0 := hi (hi0.trans i.map_zero.symm)
  exact sub_eq_zero.mp hx0

end Wikipedia.HopfProblem.DegreeCollapse.CyclicCoordinateInjectivity
