import ErdosProblems.Erdos421.LogDifference
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Data.Nat.Factorial.Basic

/-! # Differentiating finite differences of arbitrary order -/

namespace Erdos421

noncomputable def iteratedDifference : List ℝ → (ℝ → ℝ) → ℝ → ℝ
  | [], f, x => f x
  | h :: hs, f, x => iteratedDifference hs f x - iteratedDifference hs f (x + h)

theorem iteratedDifference_const_mul (hs : List ℝ) (f : ℝ → ℝ) (c x : ℝ) :
    iteratedDifference hs (fun y ↦ c * f y) x = c * iteratedDifference hs f x := by
  induction hs generalizing x with
  | nil => rfl
  | cons h hs ih =>
    simp only [iteratedDifference, ih]
    ring

theorem hasDerivAt_iteratedDifference (f g : ℝ → ℝ)
    (hfg : ∀ x, 0 < x → HasDerivAt f (g x) x) (hs : List ℝ)
    (hhs : ∀ h ∈ hs, 0 ≤ h) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (iteratedDifference hs f) (iteratedDifference hs g x) x := by
  induction hs generalizing x with
  | nil => exact hfg x hx
  | cons h hs ih =>
    have hh : 0 ≤ h := hhs h (List.mem_cons_self ..)
    have htail : ∀ a ∈ hs, 0 ≤ a := fun a ha ↦ hhs a (List.mem_cons_of_mem h ha)
    have hxH : 0 < x + h := by linarith
    have h₁ := ih htail hx
    have h₂ := (ih htail hxH).comp x ((hasDerivAt_id x).add_const h)
    simpa only [iteratedDifference, mul_one, Function.comp_apply, id_eq] using! h₁.fun_sub h₂

noncomputable def reciprocalDifference (k : ℕ) (hs : List ℝ) (x : ℝ) : ℝ :=
  iteratedDifference hs (fun y ↦ 1 / y ^ (k + 1)) x

theorem reciprocalDifference_cons (k : ℕ) (h : ℝ) (hs : List ℝ) (x : ℝ) :
    reciprocalDifference k (h :: hs) x =
      reciprocalDifference k hs x - reciprocalDifference k hs (x + h) := rfl

theorem hasDerivAt_reciprocal_nat_pow (k : ℕ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun y ↦ 1 / y ^ (k + 1))
      (-((k + 1 : ℕ) : ℝ) * (1 / x ^ (k + 2))) x := by
  have h := ((hasDerivAt_id x).pow (k + 1)).inv (pow_ne_zero _ hx.ne')
  have heq : -(((k + 1 : ℕ) : ℝ) * x ^ k) / (x ^ (k + 1)) ^ 2 =
      -((k + 1 : ℕ) : ℝ) * (1 / x ^ (k + 2)) := by
    simp only [pow_succ]
    field_simp
  simpa only [Pi.pow_apply, id_eq, Nat.add_sub_cancel, mul_one, heq, one_div] using! h

theorem hasDerivAt_reciprocalDifference (k : ℕ) (hs : List ℝ)
    (hhs : ∀ h ∈ hs, 0 ≤ h) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (reciprocalDifference k hs)
      (-((k + 1 : ℕ) : ℝ) * reciprocalDifference (k + 1) hs x) x := by
  have h := hasDerivAt_iteratedDifference (fun y ↦ 1 / y ^ (k + 1))
    (fun y ↦ -((k + 1 : ℕ) : ℝ) * (1 / y ^ (k + 2)))
    (fun _ hy ↦ hasDerivAt_reciprocal_nat_pow k hy) hs hhs hx
  rw [iteratedDifference_const_mul] at h
  exact h

theorem reciprocalDifference_mean_value (k : ℕ) (hs : List ℝ)
    (hhs : ∀ h ∈ hs, 0 ≤ h) {x h : ℝ} (hx : 0 < x) (hh : 0 < h) :
    ∃ c ∈ Set.Ioo x (x + h), reciprocalDifference k (h :: hs) x =
      ((k + 1 : ℕ) : ℝ) * h * reciprocalDifference (k + 1) hs c := by
  have hderiv := fun y hy ↦ hasDerivAt_reciprocalDifference k hs hhs (x := y) hy
  have hcont : ContinuousOn (reciprocalDifference k hs) (Set.Icc x (x + h)) := by
    intro y hy
    exact (hderiv y (hx.trans_le hy.1)).continuousAt.continuousWithinAt
  obtain ⟨c, hc, hval⟩ := exists_hasDerivAt_eq_slope (reciprocalDifference k hs)
    (fun y ↦ -((k + 1 : ℕ) : ℝ) * reciprocalDifference (k + 1) hs y)
    (show x < x + h by linarith) hcont (fun y hy ↦ hderiv y (hx.trans hy.1))
  refine ⟨c, hc, ?_⟩
  rw [reciprocalDifference_cons]
  rw [add_sub_cancel_left] at hval
  have heq := (eq_div_iff hh.ne').mp hval
  nlinarith

end Erdos421
