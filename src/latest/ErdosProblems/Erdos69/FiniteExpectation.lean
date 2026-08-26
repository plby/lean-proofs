import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Option
import Mathlib.Tactic

/-!
# Finite probability laws

Finite weighted sums suffice for the moment comparison. This module keeps
normalization and nonnegativity explicit.
-/

open scoped BigOperators

namespace Erdos69.Elementary

structure FiniteLaw (Ω : Type*) [Fintype Ω] where
  mass : Ω → ℝ
  nonneg : ∀ x, 0 ≤ mass x
  total : ∑ x, mass x = 1

namespace FiniteLaw

variable {Ω : Type*} [Fintype Ω]

noncomputable def mean (μ : FiniteLaw Ω) (f : Ω → ℝ) : ℝ := ∑ x, μ.mass x * f x

noncomputable def complexMean (μ : FiniteLaw Ω) (f : Ω → ℂ) : ℂ :=
  ∑ x, (μ.mass x : ℂ) * f x

theorem mean_nonneg (μ : FiniteLaw Ω) {f : Ω → ℝ} (hf : ∀ x, 0 ≤ f x) :
    0 ≤ μ.mean f := Finset.sum_nonneg (fun x _ ↦ mul_nonneg (μ.nonneg x) (hf x))

theorem mean_mono (μ : FiniteLaw Ω) {f g : Ω → ℝ} (h : ∀ x, f x ≤ g x) :
    μ.mean f ≤ μ.mean g :=
  Finset.sum_le_sum (fun x _ ↦ mul_le_mul_of_nonneg_left (h x) (μ.nonneg x))

@[simp] theorem mean_const (μ : FiniteLaw Ω) (c : ℝ) : μ.mean (fun _ ↦ c) = c := by
  rw [mean, ← Finset.sum_mul, μ.total, one_mul]

theorem mean_add (μ : FiniteLaw Ω) (f g : Ω → ℝ) :
    μ.mean (fun x ↦ f x + g x) = μ.mean f + μ.mean g := by
  simp [mean, mul_add, Finset.sum_add_distrib]

theorem mean_sub (μ : FiniteLaw Ω) (f g : Ω → ℝ) :
    μ.mean (fun x ↦ f x - g x) = μ.mean f - μ.mean g := by
  simp [mean, mul_sub, Finset.sum_sub_distrib]

theorem mean_mul_const (μ : FiniteLaw Ω) (f : Ω → ℝ) (c : ℝ) :
    μ.mean (fun x ↦ f x * c) = μ.mean f * c := by
  simp [mean, mul_assoc, Finset.sum_mul]

theorem mean_const_mul (μ : FiniteLaw Ω) (c : ℝ) (f : Ω → ℝ) :
    μ.mean (fun x ↦ c * f x) = c * μ.mean f := by
  simpa only [mul_comm] using μ.mean_mul_const f c

theorem mean_sum {ι : Type*} (μ : FiniteLaw Ω) (s : Finset ι) (f : ι → Ω → ℝ) :
    μ.mean (fun x ↦ ∑ i ∈ s, f i x) = ∑ i ∈ s, μ.mean (f i) := by
  simp only [mean, Finset.mul_sum]
  exact Finset.sum_comm

theorem abs_mean_le (μ : FiniteLaw Ω) (f : Ω → ℝ) :
    |μ.mean f| ≤ μ.mean (fun x ↦ |f x|) := by
  calc
    |μ.mean f| ≤ ∑ x, |μ.mass x * f x| := Finset.abs_sum_le_sum_abs _ _
    _ = μ.mean (fun x ↦ |f x|) := by
      simp [mean, abs_mul, abs_of_nonneg (μ.nonneg _)]

theorem complexMean_real (μ : FiniteLaw Ω) (f : Ω → ℝ) :
    μ.complexMean (fun x ↦ (f x : ℂ)) = (μ.mean f : ℂ) := by
  simp [complexMean, mean]

theorem complexMean_sub (μ : FiniteLaw Ω) (f g : Ω → ℂ) :
    μ.complexMean (fun x ↦ f x - g x) = μ.complexMean f - μ.complexMean g := by
  simp [complexMean, mul_sub, Finset.sum_sub_distrib]

theorem norm_complexMean_le (μ : FiniteLaw Ω) (f : Ω → ℂ) :
    ‖μ.complexMean f‖ ≤ μ.mean (fun x ↦ ‖f x‖) := by
  calc
    ‖μ.complexMean f‖ ≤ ∑ x, ‖(μ.mass x : ℂ) * f x‖ := norm_sum_le _ _
    _ = μ.mean (fun x ↦ ‖f x‖) := by
      simp [mean, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (μ.nonneg _)]

theorem norm_complexMean_sub_le (μ : FiniteLaw Ω) (f g : Ω → ℂ) :
    ‖μ.complexMean f - μ.complexMean g‖ ≤ μ.mean (fun x ↦ ‖f x - g x‖) := by
  rw [← μ.complexMean_sub]
  exact μ.norm_complexMean_le _

noncomputable def uniform (T : ℕ) (hT : 0 < T) : FiniteLaw (Fin T) where
  mass := fun _ ↦ (1 : ℝ) / T
  nonneg := fun _ ↦ by positivity
  total := by
    have h : (T : ℝ) ≠ 0 := by exact_mod_cast hT.ne'
    simp [h]

noncomputable def categorical (ι : Type*) [Fintype ι] (p : ℕ)
    (hp : 0 < p) (hcard : Fintype.card ι ≤ p) : FiniteLaw (Option ι) where
  mass := fun i ↦ match i with
    | none => 1 - (Fintype.card ι : ℝ) / p
    | some _ => (1 : ℝ) / p
  nonneg := by
    intro i
    cases i with
    | none =>
      apply sub_nonneg.mpr
      apply (div_le_one (by exact_mod_cast hp : (0 : ℝ) < p)).mpr
      exact_mod_cast hcard
    | some i => positivity
  total := by
    rw [Fintype.sum_option]
    simp [div_eq_mul_inv]

noncomputable def independentProduct {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : ι → FiniteLaw Ω) : FiniteLaw (ι → Ω) := by
  classical
  exact {
    mass := fun x ↦ ∏ i, (μ i).mass (x i)
    nonneg := fun x ↦ Finset.prod_nonneg (fun i _ ↦ (μ i).nonneg (x i))
    total := by rw [← Fintype.prod_sum]; simp [FiniteLaw.total]
  }

theorem independentProduct_mean_prod {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : ι → FiniteLaw Ω) (f : ι → Ω → ℝ) :
    (independentProduct μ).mean (fun x ↦ ∏ i, f i (x i)) =
      ∏ i, (μ i).mean (f i) := by
  classical
  unfold mean independentProduct
  simp only [← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i x ↦ (μ i).mass x * f i x)).symm

theorem independentProduct_complexMean_prod {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : ι → FiniteLaw Ω) (f : ι → Ω → ℂ) :
    (independentProduct μ).complexMean (fun x ↦ ∏ i, f i (x i)) =
      ∏ i, (μ i).complexMean (f i) := by
  classical
  unfold complexMean independentProduct
  simp only [Complex.ofReal_prod, ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i x ↦ ((μ i).mass x : ℂ) * f i x)).symm

def optionalValue {ι : Type*} (c : ι → ℝ) : Option ι → ℝ
  | none => 0
  | some i => c i

theorem categorical_mean {ι : Type*} [Fintype ι] (p : ℕ) (hp : 0 < p)
    (hc : Fintype.card ι ≤ p) (c : ι → ℝ) :
    (categorical ι p hp hc).mean (optionalValue c) = (∑ i, c i) / p := by
  simp [mean, categorical, optionalValue, Fintype.sum_option, div_eq_mul_inv,
    ← Finset.sum_mul, mul_comm]

theorem categorical_mean_square {ι : Type*} [Fintype ι] (p : ℕ) (hp : 0 < p)
    (hc : Fintype.card ι ≤ p) (c : ι → ℝ) :
    (categorical ι p hp hc).mean (fun x ↦ optionalValue c x ^ 2) =
      (∑ i, c i ^ 2) / p := by
  simp [mean, categorical, optionalValue, Fintype.sum_option, div_eq_mul_inv,
    ← Finset.mul_sum, mul_comm]

theorem optionalValue_abs_le {ι : Type*} [Fintype ι] (c : ι → ℝ)
    (x : Option ι) : |optionalValue c x| ≤ ∑ i, |c i| := by
  cases x with
  | none => simp only [optionalValue, abs_zero]; positivity
  | some i => exact Finset.single_le_sum (fun j _ ↦ abs_nonneg (c j)) (Finset.mem_univ i)

theorem sum_sq_le_mass_sq {ι : Type*} [Fintype ι] (c : ι → ℝ) :
    (∑ i, c i ^ 2) ≤ (∑ i, |c i|) ^ 2 := by
  simpa only [sq_abs] using
    Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ) (f := fun i ↦ |c i|)
      (fun i _ ↦ abs_nonneg (c i))

end FiniteLaw

end Erdos69.Elementary
