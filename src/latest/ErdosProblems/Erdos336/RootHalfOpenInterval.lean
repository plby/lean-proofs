import ErdosProblems.Erdos336.FourierNineTenths
import ErdosProblems.Erdos336.IntegerHalfInterval
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos336

open scoped Real

lemma circle_exp_lowerArg (z : Circle) : Circle.exp (circleLowerArg z) = z := by
  unfold circleLowerArg
  by_cases h : Complex.arg (z : ℂ) = Real.pi
  · simp only [h, if_true]
    calc
      Circle.exp (-Real.pi) = Circle.exp Real.pi := by
        rw [Circle.exp_eq_exp]
        refine ⟨-1, ?_⟩
        push_cast
        ring
      _ = z := by rw [← h]; exact Circle.exp_arg z
  · simp only [h, if_false]
    exact Circle.exp_arg z

lemma integer_closed_open_half_interval_label
    (A : ℝ) (m : ℕ) (hm : 0 < m) (n : ℤ)
    (hlow : A ≤ (n : ℝ))
    (hupp : (n : ℝ) < A + (m : ℝ) / 2) :
    ∃ q : ℕ, 2 * q < m ∧
      n = Int.ceil A + (q : ℤ) := by
  let a : ℤ := Int.ceil A
  have haA : (a : ℝ) ≥ A := by
    simpa [a] using Int.le_ceil A
  have han : a ≤ n := by
    dsimp [a]
    exact (Int.ceil_le).2 hlow
  let q : ℕ := (n - a).toNat
  have hqInt : (q : ℤ) = n - a := by
    dsimp [q]
    exact Int.toNat_of_nonneg (sub_nonneg.mpr han)
  have hqR : (q : ℝ) < (m : ℝ) / 2 := by
    have hqCast : (q : ℝ) = (n : ℝ) - (a : ℝ) := by
      exact_mod_cast hqInt
    rw [hqCast]
    nlinarith
  have htwoR : ((2 * q : ℕ) : ℝ) < (m : ℝ) := by
    push_cast
    nlinarith
  have htwo : 2 * q < m := by exact_mod_cast htwoR
  refine ⟨q, htwo, ?_⟩
  rw [hqInt]
  omega

/-- The roots whose lower principal arguments lie in a half-open semicircle
occupy a cyclic interval of span strictly below half. -/
theorem roots_in_halfopen_semicircle
    (m : ℕ) [NeZero m] (r : Circle) (θ : ℝ)
    (hθ0 : 0 ≤ θ) (hθpi : θ ≤ Real.pi) :
    ∃ α : ZMod m, ∀ j : ZMod m,
      semicircleArcMem (circleLowerArg (r * ZMod.toCircle j)) θ →
      ∃ q : ℕ, 2 * q < m ∧ j = α + (q : ZMod m) := by
  let ρ : ℝ := Complex.arg (r : ℂ)
  let fac : ℝ := (m : ℝ) / (2 * Real.pi)
  let A : ℝ := fac * (θ - Real.pi - ρ)
  let α : ZMod m := (Int.ceil A : ℤ)
  refine ⟨α, ?_⟩
  intro j hj
  have hj' : θ - Real.pi ≤ circleLowerArg (r * ZMod.toCircle j) ∧
      circleLowerArg (r * ZMod.toCircle j) < θ := by
    rw [semicircleArcMem] at hj
    simp only [not_lt.mpr hθ0, if_false] at hj
    exact hj
  let u := circleLowerArg (r * ZMod.toCircle j)
  have hphase : r * ZMod.toCircle j =
      Circle.exp (ρ + 2 * Real.pi * ((j.val : ℝ) / m)) := by
    rw [show r = Circle.exp ρ by
      simpa [ρ] using (Circle.exp_arg r).symm]
    rw [ZMod.toCircle_eq_circleExp]
    rw [← Circle.exp_add]
  have hueq : Circle.exp (ρ + 2 * Real.pi * ((j.val : ℝ) / m)) =
      Circle.exp u := by
    rw [← hphase]
    exact (circle_exp_lowerArg _).symm
  obtain ⟨z, hz⟩ := Circle.exp_eq_exp.mp hueq
  let n : ℤ := (j.val : ℤ) - z * (m : ℤ)
  have hmR : (0 : ℝ) < m := by exact_mod_cast NeZero.pos m
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hfac : 0 < fac := by
    dsimp [fac]
    positivity
  have hnEq : (n : ℝ) = fac * (u - ρ) := by
    dsimp [n, fac]
    push_cast
    field_simp [ne_of_gt hpi, ne_of_gt hmR] at hz ⊢
    linear_combination hz
  have hlow : A ≤ (n : ℝ) := by
    rw [hnEq]
    dsimp [A, u] at *
    exact mul_le_mul_of_nonneg_left (by linarith [hj'.1]) hfac.le
  have hfacpi : fac * Real.pi = (m : ℝ) / 2 := by
    dsimp [fac]
    field_simp [ne_of_gt hpi]
  have hupp : (n : ℝ) < A + (m : ℝ) / 2 := by
    rw [hnEq]
    calc
      fac * (u - ρ) < fac * (θ - ρ) :=
        mul_lt_mul_of_pos_left (by simpa [u] using hj'.2) hfac
      _ = fac * (θ - Real.pi - ρ) + fac * Real.pi := by ring
      _ = A + (m : ℝ) / 2 := by rw [hfacpi]
  obtain ⟨q, hq, hnlabel⟩ :=
    integer_closed_open_half_interval_label A m (NeZero.pos m) n hlow hupp
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
