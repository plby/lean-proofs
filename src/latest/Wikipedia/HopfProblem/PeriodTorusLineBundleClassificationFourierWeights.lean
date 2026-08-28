import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-!
# Summable elliptic weights on the Fourier lattice

The product of the one-coordinate elliptic multipliers is positive, dominates
the coordinate norm, and has summable reciprocal. This gives summable
majorants for every polynomial order without any hypothesis on Fourier
coefficients.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassification

open scoped BigOperators

/-- The multiplier of the product of the one-coordinate elliptic operators. -/
def fourierEllipticWeight {d : Type*} [Fintype d] (k : d → ℤ) : ℝ :=
  ∏ i, (1 + (2 * Real.pi * (k i : ℝ)) ^ 2)

theorem one_le_fourierEllipticWeight {d : Type*} [Fintype d] (k : d → ℤ) :
    1 ≤ fourierEllipticWeight k := by
  exact Finset.one_le_prod (fun i _ => by nlinarith [sq_nonneg (2 * Real.pi * (k i : ℝ))])

theorem fourierEllipticWeight_pos {d : Type*} [Fintype d] (k : d → ℤ) :
    0 < fourierEllipticWeight k :=
  zero_lt_one.trans_le (one_le_fourierEllipticWeight k)

theorem fourierEllipticWeight_ne_zero {d : Type*} [Fintype d] (k : d → ℤ) :
    fourierEllipticWeight k ≠ 0 := (fourierEllipticWeight_pos k).ne'

private theorem sq_le_fourier_frequency_sq (x : ℝ) :
    x ^ 2 ≤ (2 * Real.pi * x) ^ 2 := by
  have hpi : 1 ≤ (2 * Real.pi) ^ 2 := by nlinarith [Real.two_le_pi]
  calc
    x ^ 2 = 1 * x ^ 2 := (one_mul _).symm
    _ ≤ (2 * Real.pi) ^ 2 * x ^ 2 :=
      mul_le_mul_of_nonneg_right hpi (sq_nonneg x)
    _ = (2 * Real.pi * x) ^ 2 := (mul_pow _ _ _).symm

/-- The reciprocal one-coordinate multiplier is summable over all integers. -/
theorem summable_inv_fourierEllipticFactor :
    Summable (fun n : ℤ => (1 + (2 * Real.pi * (n : ℝ)) ^ 2)⁻¹) := by
  have hp : Summable (fun n : ℤ => 1 / (n : ℝ) ^ 2) :=
    Real.summable_one_div_int_pow.mpr (by norm_num)
  apply hp.of_norm_bounded_eventually
  filter_upwards [Filter.eventually_cofinite_ne (0 : ℤ)] with n hn
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (by positivity))]
  rw [← one_div]
  apply one_div_le_one_div_of_le (sq_pos_of_ne_zero hn')
  exact (sq_le_fourier_frequency_sq (n : ℝ)).trans (le_add_of_nonneg_left zero_le_one)

/-- Summability of the reciprocal product weight in every finite dimension. -/
theorem summable_inv_fourierEllipticWeight {d : Type*} [Fintype d] :
    Summable (fun k : d → ℤ => (fourierEllipticWeight k)⁻¹) := by
  classical
  refine Fintype.induction_empty_option
    (P := fun d _ => Summable (fun k : d → ℤ => (fourierEllipticWeight k)⁻¹))
    ?_ ?_ ?_ d
  · intro α β _ e h
    let : Fintype α := Fintype.ofEquiv β e.symm
    have he : Function.Injective (fun k : β → ℤ => fun i : α => k (e i)) := by
      intro k l hkl
      funext j
      simpa only [e.apply_symm_apply] using congrFun hkl (e.symm j)
    refine (h.comp_injective he).congr (fun k => ?_)
    change (∏ i : α, (1 + (2 * Real.pi * (k (e i) : ℝ)) ^ 2))⁻¹ =
      (∏ i : β, (1 + (2 * Real.pi * (k i : ℝ)) ^ 2))⁻¹
    exact congrArg Inv.inv (e.prod_comp (fun i : β => (1 + (2 * Real.pi * (k i : ℝ)) ^ 2)))
  · exact summable_of_hasFiniteSupport (Set.toFinite _)
  · intro α _ h
    have hm := summable_inv_fourierEllipticFactor.mul_of_nonneg h
      (fun n => by positivity)
      (fun k => inv_nonneg.mpr (fourierEllipticWeight_pos k).le)
    have hs := hm.comp_injective
      (Equiv.piOptionEquivProd (β := fun _ : Option α => ℤ)).injective
    refine hs.congr (fun k => ?_)
    change (1 + (2 * Real.pi * (k none : ℝ)) ^ 2)⁻¹ *
      (fourierEllipticWeight (fun i => k (some i)))⁻¹ = (fourierEllipticWeight k)⁻¹
    simp only [fourierEllipticWeight, Fintype.prod_option, mul_inv_rev, mul_comm]

/-- Every coordinate multiplier is bounded by the full elliptic multiplier. -/
theorem fourierEllipticFactor_le_weight {d : Type*} [Fintype d] (k : d → ℤ) (i : d) :
    1 + (2 * Real.pi * (k i : ℝ)) ^ 2 ≤ fourierEllipticWeight k := by
  classical
  have h := Finset.prod_le_prod_of_subset_of_one_le
    (s := {i}) (t := Finset.univ)
    (f := fun j => (1 + (2 * Real.pi * (k j : ℝ)) ^ 2))
    (Finset.subset_univ _)
    (fun j _ => by positivity)
    (fun j _ _ => by nlinarith [sq_nonneg (2 * Real.pi * (k j : ℝ))])
  simpa only [Finset.prod_singleton, fourierEllipticWeight] using h

/-- The real coordinate sup norm is bounded by the product weight. -/
theorem norm_cast_le_fourierEllipticWeight {d : Type*} [Fintype d] (k : d → ℤ) :
    ‖(fun i => (k i : ℝ))‖ ≤ fourierEllipticWeight k := by
  apply (pi_norm_le_iff_of_nonneg (fourierEllipticWeight_pos k).le).mpr
  intro i
  rw [Real.norm_eq_abs]
  have habs : |(k i : ℝ)| ≤ 1 + (k i : ℝ) ^ 2 := by
    nlinarith [sq_nonneg (|(k i : ℝ)| - 1), sq_abs (k i : ℝ), abs_nonneg (k i : ℝ)]
  have hs : 1 + (k i : ℝ) ^ 2 ≤ 1 + (2 * Real.pi * (k i : ℝ)) ^ 2 := by
    linarith [sq_le_fourier_frequency_sq (k i : ℝ)]
  exact habs.trans (hs.trans (fourierEllipticFactor_le_weight k i))

/-- A polynomially weighted reciprocal is bounded by a constant times the
summable reciprocal product weight. -/
theorem polynomial_mul_inv_fourierEllipticWeight_le {d : Type*} [Fintype d]
    (r : ℕ) (k : d → ℤ) :
    (1 + ‖(fun i => (k i : ℝ))‖) ^ r / fourierEllipticWeight k ^ (r + 1) ≤
      (2 : ℝ) ^ r * (fourierEllipticWeight k)⁻¹ := by
  have hw := fourierEllipticWeight_pos k
  have hb : 1 + ‖(fun i => (k i : ℝ))‖ ≤ 2 * fourierEllipticWeight k := by
    linarith [norm_cast_le_fourierEllipticWeight k, one_le_fourierEllipticWeight k]
  calc
    (1 + ‖(fun i => (k i : ℝ))‖) ^ r / fourierEllipticWeight k ^ (r + 1) ≤
        (2 * fourierEllipticWeight k) ^ r / fourierEllipticWeight k ^ (r + 1) :=
      div_le_div_of_nonneg_right (pow_le_pow_left₀ (by positivity) hb r) (pow_pos hw _).le
    _ = (2 : ℝ) ^ r * (fourierEllipticWeight k)⁻¹ := by
      rw [mul_pow, pow_succ]
      field_simp

/-- Summability at every polynomial order, with no coefficient-decay premise. -/
theorem summable_polynomial_mul_inv_fourierEllipticWeight {d : Type*} [Fintype d]
    (r : ℕ) :
    Summable (fun k : d → ℤ =>
      (1 + ‖(fun i => (k i : ℝ))‖) ^ r / fourierEllipticWeight k ^ (r + 1)) := by
  apply ((summable_inv_fourierEllipticWeight (d := d)).mul_left ((2 : ℝ) ^ r)).of_nonneg_of_le
  · intro k
    exact div_nonneg (pow_nonneg (by positivity) _) (pow_pos (fourierEllipticWeight_pos k) _).le
  · exact polynomial_mul_inv_fourierEllipticWeight_le r

end Wikipedia.HopfProblem.PeriodTorusLineBundleClassification
