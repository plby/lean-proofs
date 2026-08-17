import Mathlib
import UnitFractions.ForMathlib.BasicEstimates

/-!
# A weak Mertens lower bound for the rough-number sieve

The project already contains an axiom-free proof that the reciprocal partial
Euler product is `O(log x)`, namely
`weak_mertens_third_upper_all`.  We package its (global) real constant as a
positive natural number and invert the estimate.  Keeping this module
independent of the definitions in `RoughNumbers` avoids an import cycle.
-/

open scoped BigOperators

namespace Erdos54

/-- The positive real constant supplied by the existing weak Mertens theorem. -/
private noncomputable def roughMertensRealConstant : ℝ :=
  Classical.choose weak_mertens_third_upper_all

private theorem roughMertensRealConstant_pos : 0 < roughMertensRealConstant :=
  (Classical.choose_spec weak_mertens_third_upper_all).1

private theorem partialEulerProduct_le_roughMertensRealConstant
    (x : ℝ) (hx : 2 ≤ x) :
    ‖partial_euler_product ⌊x⌋₊‖ ≤
      roughMertensRealConstant * ‖Real.log x‖ :=
  (Classical.choose_spec weak_mertens_third_upper_all).2 x hx

/-- A fixed positive natural constant which absorbs the unspecified constant
in the weak Mertens estimate. -/
noncomputable def roughMertensConstant : ℕ :=
  ⌈roughMertensRealConstant⌉₊

theorem roughMertensConstant_pos : 0 < roughMertensConstant := by
  exact Nat.ceil_pos.mpr roughMertensRealConstant_pos

private theorem primesUpTo_eq_Icc (w : ℕ) :
    (Finset.range (w + 1)).filter Nat.Prime =
      (Finset.Icc 1 w).filter Nat.Prime := by
  ext p
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc,
    Nat.lt_add_one_iff]
  constructor
  · rintro ⟨hpw, hp⟩
    exact ⟨⟨hp.one_le, hpw⟩, hp⟩
  · rintro ⟨⟨_, hpw⟩, hp⟩
    exact ⟨hpw, hp⟩

private theorem eulerProduct_mul_partialEulerProduct (w : ℕ) :
    (∏ p ∈ (Finset.range (w + 1)).filter Nat.Prime,
        (1 - 1 / (p : ℝ))) * partial_euler_product w = 1 := by
  rw [partial_euler_product, primesUpTo_eq_Icc]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_eq_one
  intro p hp
  have hpPrime : p.Prime := (Finset.mem_filter.mp hp).2
  have hpos : 0 < (1 - 1 / (p : ℝ)) := by
    rw [sub_pos, div_lt_one (by exact_mod_cast hpPrime.pos)]
    exact_mod_cast hpPrime.one_lt
  field_simp

private theorem eulerProduct_eq_partialEulerProduct_inv (w : ℕ) :
    (∏ p ∈ (Finset.range (w + 1)).filter Nat.Prime,
        (1 - 1 / (p : ℝ))) = (partial_euler_product w)⁻¹ := by
  have hpPos : 0 < partial_euler_product w :=
    lt_of_lt_of_le zero_lt_one partial_euler_trivial_lower_bound
  exact (mul_eq_one_iff_eq_inv₀ hpPos.ne').mp
    (eulerProduct_mul_partialEulerProduct w)

/-- A weak, axiom-free Mertens lower bound with a fixed natural constant.
This is the only analytic prime-product estimate needed by the rough-number
sieve after rescaling the secondary logarithmic parameter by
`roughMertensConstant`. -/
theorem roughEulerProduct_lower {w : ℕ} (hw : 2 ≤ w) :
    1 / ((roughMertensConstant : ℝ) * Real.log w) ≤
      ∏ p ∈ (Finset.range (w + 1)).filter Nat.Prime,
        (1 - 1 / (p : ℝ)) := by
  have hwR : (2 : ℝ) ≤ w := by exact_mod_cast hw
  have hpartial := partialEulerProduct_le_roughMertensRealConstant (w : ℝ) hwR
  rw [Nat.floor_natCast] at hpartial
  have hpartialPos : 0 < partial_euler_product w :=
    lt_of_lt_of_le zero_lt_one partial_euler_trivial_lower_bound
  have hlogPos : 0 < Real.log (w : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < w by omega))
  rw [Real.norm_of_nonneg hpartialPos.le,
    Real.norm_of_nonneg (Real.log_nonneg
      (by exact_mod_cast (show 1 ≤ w by omega)))] at hpartial
  have hcK : roughMertensRealConstant ≤ roughMertensConstant :=
    Nat.le_ceil roughMertensRealConstant
  have hupper : partial_euler_product w ≤
      (roughMertensConstant : ℝ) * Real.log w :=
    hpartial.trans (mul_le_mul_of_nonneg_right hcK hlogPos.le)
  rw [eulerProduct_eq_partialEulerProduct_inv]
  simpa only [one_div] using
    (one_div_le_one_div_of_le hpartialPos hupper)

#print axioms roughEulerProduct_lower

end Erdos54
