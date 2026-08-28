import Wikipedia.HopfProblem.EllipticFlatTorus

/-!
# Elliptic arithmetic for real vertical translations

The real vertical direction is the fourth coordinate basis vector, so it
does not change the gamma coordinate. The gamma obstruction for the actual
order-three and order-four twists therefore still excludes every nontrivial
iterate, even after a real vertical translation. The fourth coordinate then
forces that translation to be integral.
-/

noncomputable section

open scoped Matrix
open Wikipedia.HopfProblem.Elliptic

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.FiniteActionFixed.Elliptic

/-- An admissible elliptic iterate below its order cannot equal a real vertical
translation modulo the actual integral lattice unless the iterate is zero. -/
theorem flatAffine_iterate_eq_zero_of_vertical_congruent (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) (r : ℕ) (hrm : r < j.order)
    (x : RealCoordinates) (s : ℝ)
    (h : FlatCongruent ((flatAffine j v)^[r] x)
      (x + s • Pi.basisFun ℝ (Fin 4) 3)) : r = 0 := by
  by_contra hr
  have hrpos : 0 < r := Nat.pos_of_ne_zero hr
  obtain ⟨w, hw⟩ := h
  have hgamma : (flatAffine j v)^[r] x 0 - x 0 = (w 0 : ℝ) := by
    simpa [Pi.basisFun_apply, Pi.single_apply, realCast] using congrFun hw 0
  rw [flatAffine_iterate_gamma] at hgamma
  have hm : (j.order : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt j.order_pos)
  have hreal : (r : ℝ) * (γ v : ℝ) = (j.order : ℝ) * (w 0 : ℝ) := by
    field_simp [hm] at hgamma
    nlinarith
  have hint : (r : ℤ) * γ v = (j.order : ℤ) * w 0 := by exact_mod_cast hreal
  cases j with
  | three =>
    have ha : ¬ 3 ∣ γ v := by simpa [AdmissibleTwist] using hv.2
    change r < 3 at hrm
    change (r : ℤ) * γ v = 3 * w 0 at hint
    interval_cases r <;> norm_num at hint <;> omega
  | four =>
    have ha : Odd (γ v) := by simpa [AdmissibleTwist] using hv.2
    rcases ha with ⟨a, ha⟩
    change r < 4 at hrm
    change (r : ℤ) * γ v = 4 * w 0 at hint
    interval_cases r <;> norm_num at hint <;> omega

/-- Equality modulo the integral lattice forces both the elliptic iterate to
be trivial and the real vertical translation to be an integer. -/
theorem flatAffine_iterate_vertical_congruent (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) (r : ℕ) (hrm : r < j.order)
    (x : RealCoordinates) (s : ℝ)
    (h : FlatCongruent ((flatAffine j v)^[r] x)
      (x + s • Pi.basisFun ℝ (Fin 4) 3)) :
    r = 0 ∧ ∃ n : ℤ, s = (n : ℝ) := by
  have hr := flatAffine_iterate_eq_zero_of_vertical_congruent j v hv r hrm x s h
  refine ⟨hr, ?_⟩
  subst r
  obtain ⟨w, hw⟩ := h
  have h₃ := congrFun hw 3
  simp [Pi.basisFun_apply, realCast] at h₃
  refine ⟨-(w 3), ?_⟩
  rw [Int.cast_neg]
  linarith

/-- The same obstruction holds on the original quotient real torus, for the
actual affine permutation and actual quotient map. -/
theorem flatTorusPermutation_pow_eq_vertical (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) (r : ℕ) (hrm : r < j.order)
    (x : RealCoordinates) (s : ℝ)
    (h : (flatTorusPermutation j v ^ r) (standardLattice.mkQ x) =
      standardLattice.mkQ (x + s • Pi.basisFun ℝ (Fin 4) 3)) :
    r = 0 ∧ ∃ n : ℤ, s = (n : ℝ) := by
  rw [flatTorusPermutation_pow_mkQ] at h
  exact flatAffine_iterate_vertical_congruent j v hv r hrm x s
    ((flatTorus_mkQ_eq_iff _ _).mp h)

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.FiniteActionFixed.Elliptic
