import Wikipedia.HopfProblem.PeriodTorusAppellHumbertData
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.Tactic.LinearCombination

/-!
# The integer cocycle of logarithmic factors

The logarithmic defect of a factor of automorphy takes values in
`2πi ℤ`.  This file records the algebraic consequences of that equality:
the integer defect is unique and obeys the two-cocycle identity.  Its
commutator is an actual alternating integral bilinear form on the period
lattice.  Existence of logarithms and of the integer defect is proved
separately; neither is an additional field in a line-bundle definition.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassification

/-- The integer defect equation for logarithms on the actual covering space. -/
def HasIntegerLogDefect (p : PeriodDomain)
    (b : p.lattice → ComplexPlane₂ → ℂ) (n : p.lattice → p.lattice → ℤ) : Prop :=
  ∀ l m z, b (l + m) z - b l (z + m) - b m z =
    (n l m : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)

private theorem two_pi_I_ne_zero :
    (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
  exact mul_ne_zero (mul_ne_zero (by norm_num)
    (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero

variable {p : PeriodDomain} {b : p.lattice → ComplexPlane₂ → ℂ}
  {n n' : p.lattice → p.lattice → ℤ}

namespace HasIntegerLogDefect

/-- Associativity of translation gives the integral two-cocycle identity. -/
theorem cocycle (h : HasIntegerLogDefect p b n) (l m k : p.lattice) :
    n l m + n (l + m) k = n m k + n l (m + k) := by
  apply Int.cast_injective (α := ℂ)
  apply mul_right_cancel₀ two_pi_I_ne_zero
  push_cast
  have h₁ := h l m (k : ComplexPlane₂)
  have h₂ := h (l + m) k 0
  have h₃ := h m k 0
  have h₄ := h l (m + k) 0
  simp only [zero_add, Submodule.coe_add, add_assoc] at h₂ h₃ h₄
  rw [add_comm (k : ComplexPlane₂) (m : ComplexPlane₂)] at h₁
  linear_combination -h₁ - h₂ + h₃ + h₄

/-- A normalized logarithm has zero defect when the first translation is zero. -/
theorem zero_left (h : HasIntegerLogDefect p b n) (hb : ∀ z, b 0 z = 0)
    (l : p.lattice) : n 0 l = 0 := by
  have hn := h 0 l 0
  simp only [zero_add, hb, sub_zero, sub_self] at hn
  have hc : (n 0 l : ℂ) = 0 :=
    (mul_eq_zero.mp hn.symm).resolve_right two_pi_I_ne_zero
  exact_mod_cast hc

/-- A normalized logarithm has zero defect when the second translation is zero. -/
theorem zero_right (h : HasIntegerLogDefect p b n) (hb : ∀ z, b 0 z = 0)
    (l : p.lattice) : n l 0 = 0 := by
  have hn := h l 0 0
  simp only [add_zero, Submodule.coe_zero, hb, sub_self] at hn
  have hc : (n l 0 : ℂ) = 0 :=
    (mul_eq_zero.mp hn.symm).resolve_right two_pi_I_ne_zero
  exact_mod_cast hc

/-- The integer defect is fixed by the chosen logarithms. -/
theorem unique (h : HasIntegerLogDefect p b n) (h' : HasIntegerLogDefect p b n') :
    n = n' := by
  funext l m
  apply Int.cast_injective (α := ℂ)
  apply mul_right_cancel₀ two_pi_I_ne_zero
  exact (h l m 0).symm.trans (h' l m 0)

end HasIntegerLogDefect

/-- The integral commutator of a logarithmic two-cocycle. -/
def integerLogCommutator (n : p.lattice → p.lattice → ℤ) (l m : p.lattice) : ℤ :=
  n l m - n m l

@[simp] theorem integerLogCommutator_self (n : p.lattice → p.lattice → ℤ)
    (l : p.lattice) : integerLogCommutator n l l = 0 := sub_self _

theorem integerLogCommutator_swap (n : p.lattice → p.lattice → ℤ)
    (l m : p.lattice) : integerLogCommutator n l m = -integerLogCommutator n m l := by
  simp only [integerLogCommutator, neg_sub]

/-- On an abelian translation lattice the commutator is additive in its first slot. -/
theorem integerLogCommutator_add_left (h : HasIntegerLogDefect p b n)
    (l m k : p.lattice) :
    integerLogCommutator n (l + m) k =
      integerLogCommutator n l k + integerLogCommutator n m k := by
  have h₁ := h.cocycle l m k
  have h₂ := h.cocycle k l m
  have h₃ := h.cocycle l k m
  rw [add_comm k l] at h₂
  rw [add_comm k m] at h₃
  simp only [integerLogCommutator]
  linear_combination h₁ + h₂ - h₃

/-- Additivity in the second slot follows from skew symmetry. -/
theorem integerLogCommutator_add_right (h : HasIntegerLogDefect p b n)
    (l m k : p.lattice) :
    integerLogCommutator n l (m + k) =
      integerLogCommutator n l m + integerLogCommutator n l k := by
  rw [integerLogCommutator_swap n l (m + k), integerLogCommutator_add_left h]
  rw [neg_add, ← integerLogCommutator_swap n l m, ← integerLogCommutator_swap n l k]

theorem integerLogCommutator_smul_left (h : HasIntegerLogDefect p b n)
    (a : ℤ) (l m : p.lattice) :
    integerLogCommutator n (a • l) m = a • integerLogCommutator n l m := by
  let f : p.lattice →+ ℤ := AddMonoidHom.mk' (fun l => integerLogCommutator n l m)
    (fun l k => integerLogCommutator_add_left h l k m)
  change f (a • l) = a • f l
  exact f.map_zsmul a l

theorem integerLogCommutator_smul_right (h : HasIntegerLogDefect p b n)
    (a : ℤ) (l m : p.lattice) :
    integerLogCommutator n l (a • m) = a • integerLogCommutator n l m := by
  let f : p.lattice →+ ℤ := AddMonoidHom.mk' (integerLogCommutator n l)
    (integerLogCommutator_add_right h l)
  change f (a • m) = a • f m
  exact f.map_zsmul a m

/-- The commutator is a genuine integral bilinear form, with no normalization required. -/
def integerLogAlternatingForm (h : HasIntegerLogDefect p b n) :
    LinearMap.BilinForm ℤ p.lattice :=
  LinearMap.mk₂ ℤ (integerLogCommutator n)
    (integerLogCommutator_add_left h) (integerLogCommutator_smul_left h)
    (integerLogCommutator_add_right h)
    (fun a l m => integerLogCommutator_smul_right h a l m)

@[simp] theorem integerLogAlternatingForm_apply (h : HasIntegerLogDefect p b n)
    (l m : p.lattice) : integerLogAlternatingForm h l m = n l m - n m l := rfl

theorem integerLogAlternatingForm_isAlt (h : HasIntegerLogDefect p b n) :
    (integerLogAlternatingForm h).IsAlt := by
  intro l
  exact sub_self _

/-- Evaluation of the integral form is the alternating difference of logarithms. -/
theorem integerLogAlternatingForm_log_difference (h : HasIntegerLogDefect p b n)
    (l m : p.lattice) (z : ComplexPlane₂) :
    (integerLogAlternatingForm h l m : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) =
      b m (z + l) - b m z - b l (z + m) + b l z := by
  have h₁ := h l m z
  have h₂ := h m l z
  rw [add_comm m l] at h₂
  simp only [integerLogAlternatingForm_apply, Int.cast_sub]
  linear_combination -h₁ + h₂

end Wikipedia.HopfProblem.PeriodTorusLineBundleClassification
