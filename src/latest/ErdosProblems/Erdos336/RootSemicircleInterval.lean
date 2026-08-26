import ErdosProblems.Erdos336.IntegerHalfInterval
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos336

open scoped Real

/-- The roots of unity lying in any rotated open semicircle occupy a genuinely
short consecutive interval in their cyclic exponent group. -/
theorem roots_in_rotated_open_semicircle
    (m : ℕ) [NeZero m] (r : Circle) :
    ∃ α : ZMod m, ∀ j : ZMod m,
      r * ZMod.toCircle j ∈ Circle.centeredArc (Real.pi / 2) →
      ∃ q : ℕ, 2 * q < m ∧ j = α + (q : ZMod m) := by
  let ρ : ℝ := Complex.arg (r : ℂ)
  let fac : ℝ := (m : ℝ) / (2 * Real.pi)
  let A : ℝ := fac * (-Real.pi / 2 - ρ)
  let α : ZMod m := (Int.floor A + 1 : ℤ)
  refine ⟨α, ?_⟩
  intro j hj
  rcases hj with ⟨u, hu, hueq⟩
  have hphase : r * ZMod.toCircle j =
      Circle.exp (ρ + 2 * Real.pi * ((j.val : ℝ) / m)) := by
    rw [show r = Circle.exp ρ by
      simpa [ρ] using (Circle.exp_arg r).symm]
    rw [ZMod.toCircle_eq_circleExp]
    rw [← Circle.exp_add]
  rw [hphase] at hueq
  obtain ⟨z, hz⟩ := Circle.exp_eq_exp.mp hueq
  let n : ℤ := (j.val : ℤ) + z * (m : ℤ)
  have hmR : (0 : ℝ) < m := by
    exact_mod_cast NeZero.pos m
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hfac : 0 < fac := by
    dsimp [fac]
    positivity
  have hnEq : (n : ℝ) = fac * (u - ρ) := by
    dsimp [n, fac]
    push_cast
    rw [hz]
    field_simp [ne_of_gt hpi, ne_of_gt hmR]
    ring
  change |u| < Real.pi / 2 at hu
  have hub := (abs_lt.mp hu)
  have hlow : A < (n : ℝ) := by
    rw [hnEq]
    dsimp [A]
    exact mul_lt_mul_of_pos_left (by linarith) hfac
  have hfacpi : fac * Real.pi = (m : ℝ) / 2 := by
    dsimp [fac]
    field_simp [ne_of_gt hpi]
  have hupp : (n : ℝ) < A + (m : ℝ) / 2 := by
    rw [hnEq]
    calc
      fac * (u - ρ) < fac * (Real.pi / 2 - ρ) :=
        mul_lt_mul_of_pos_left (by linarith) hfac
      _ = fac * (-Real.pi / 2 - ρ) + fac * Real.pi := by ring
      _ = A + (m : ℝ) / 2 := by rw [hfacpi]
  obtain ⟨q, hq, hnlabel⟩ :=
    integer_open_half_interval_label A m (NeZero.pos m) n hlow hupp
  refine ⟨q, hq, ?_⟩
  have hncast : (n : ZMod m) = j := by
    dsimp [n]
    push_cast
    simp
  have hlabelCast := congrArg (fun x : ℤ => (x : ZMod m)) hnlabel
  have hlabel : (n : ZMod m) = α + (q : ZMod m) := by
    simpa [α] using hlabelCast
  rw [hncast] at hlabel
  exact hlabel

end Erdos336
