import ErdosProblems.Erdos4.DirectMoments
import Mathlib.Data.Finset.Powerset

/-!
# Finite probability laws for the FGKMT covering induction

All probability calculations use finite real sums. The definitions keep
normalization and nonnegativity explicit, and include the second-moment
estimate used to control the reweighting normalizers in each round.
-/

open scoped BigOperators

namespace Erdos4.FGKMT

structure FiniteLaw (Ω : Type*) [Fintype Ω] where
  weight : Ω → ℝ
  nonneg : ∀ o, 0 ≤ weight o
  total : ∑ o, weight o = 1

namespace FiniteLaw

variable {Ω : Type*} [Fintype Ω] (μ : FiniteLaw Ω)

noncomputable def mean (f : Ω → ℝ) : ℝ := ∑ o, μ.weight o * f o

noncomputable def prob (E : Ω → Prop) : ℝ := by
  classical
  exact ∑ o, if E o then μ.weight o else 0

theorem mean_const (a : ℝ) : μ.mean (fun _ => a) = a := by
  simp only [mean, ← Finset.sum_mul, μ.total, one_mul]

theorem mean_nonneg {f : Ω → ℝ} (hf : ∀ o, 0 ≤ f o) : 0 ≤ μ.mean f :=
  Finset.sum_nonneg (fun o _ho => mul_nonneg (μ.nonneg o) (hf o))

theorem mean_mono {f g : Ω → ℝ} (h : ∀ o, f o ≤ g o) : μ.mean f ≤ μ.mean g :=
  Finset.sum_le_sum (fun o _ho => mul_le_mul_of_nonneg_left (h o) (μ.nonneg o))

theorem mean_add (f g : Ω → ℝ) : μ.mean (fun o => f o + g o) = μ.mean f + μ.mean g := by
  simp only [mean, mul_add, Finset.sum_add_distrib]

theorem mean_sub (f g : Ω → ℝ) : μ.mean (fun o => f o - g o) = μ.mean f - μ.mean g := by
  simp only [mean, mul_sub, Finset.sum_sub_distrib]

theorem mean_mul_const (f : Ω → ℝ) (a : ℝ) : μ.mean (fun o => f o * a) = μ.mean f * a := by
  simp only [mean, ← mul_assoc, Finset.sum_mul]

theorem mean_const_mul (a : ℝ) (f : Ω → ℝ) : μ.mean (fun o => a * f o) = a * μ.mean f := by
  simpa only [mul_comm a] using μ.mean_mul_const f a

theorem mean_finset_sum {ι : Type*} (s : Finset ι) (f : ι → Ω → ℝ) :
    μ.mean (fun o => ∑ i ∈ s, f i o) = ∑ i ∈ s, μ.mean (f i) := by
  simp only [mean, Finset.mul_sum]
  exact Finset.sum_comm

theorem mean_congr {f g : Ω → ℝ} (h : ∀ o, f o = g o) : μ.mean f = μ.mean g :=
  Finset.sum_congr rfl (fun o _ho => congrArg (μ.weight o * ·) (h o))

theorem mean_congr_support {f g : Ω → ℝ} (h : ∀ o, 0 < μ.weight o → f o = g o) :
    μ.mean f = μ.mean g := by
  apply Finset.sum_congr rfl
  intro o _ho
  by_cases hw : μ.weight o = 0
  · simp only [hw, zero_mul]
  · rw [h o (lt_of_le_of_ne (μ.nonneg o) (Ne.symm hw))]

theorem mean_mono_support {f g : Ω → ℝ} (h : ∀ o, 0 < μ.weight o → f o ≤ g o) :
    μ.mean f ≤ μ.mean g := by
  apply Finset.sum_le_sum
  intro o _ho
  by_cases hw : μ.weight o = 0
  · simp only [hw, zero_mul, le_refl]
  · exact mul_le_mul_of_nonneg_left (h o (lt_of_le_of_ne (μ.nonneg o) (Ne.symm hw))) (μ.nonneg o)

theorem abs_mean_le (f : Ω → ℝ) : |μ.mean f| ≤ μ.mean (fun o => |f o|) := by
  calc
    _ ≤ ∑ o, |μ.weight o * f o| := Finset.abs_sum_le_sum_abs _ _
    _ = _ := by simp only [mean, abs_mul, abs_of_nonneg (μ.nonneg _)]

theorem prob_nonneg (E : Ω → Prop) : 0 ≤ μ.prob E := by
  classical
  exact Finset.sum_nonneg (fun o _ho => by split_ifs; exact μ.nonneg o; rfl)

theorem prob_le_one (E : Ω → Prop) : μ.prob E ≤ 1 := by
  classical
  calc
    _ ≤ ∑ o, μ.weight o := Finset.sum_le_sum (fun o _ho => by split_ifs; rfl; exact μ.nonneg o)
    _ = _ := μ.total

theorem prob_eq_mean (E : Ω → Prop) [DecidablePred E] :
    μ.prob E = μ.mean (fun o => if E o then 1 else 0) := by
  classical
  unfold prob mean
  apply Finset.sum_congr rfl
  intro o _ho
  by_cases he : E o <;> simp [he]

theorem prob_mono {E F : Ω → Prop} (h : ∀ o, E o → F o) : μ.prob E ≤ μ.prob F := by
  classical
  unfold prob
  apply Finset.sum_le_sum
  intro o _ho
  by_cases he : E o
  · simp only [if_pos he, if_pos (h o he), le_refl]
  · simp only [if_neg he]
    split_ifs
    · exact μ.nonneg o
    · rfl

theorem prob_compl (E : Ω → Prop) : μ.prob (fun o => ¬E o) = 1 - μ.prob E := by
  classical
  have hh : μ.prob E + μ.prob (fun o => ¬E o) = 1 := by
    rw [prob, prob, ← Finset.sum_add_distrib]
    convert μ.total using 1
    apply Finset.sum_congr rfl
    intro o _ho
    by_cases h : E o <;> simp [h]
  linarith

theorem prob_exists_finset_le {ι : Type*} (s : Finset ι) (E : ι → Ω → Prop) :
    μ.prob (fun o => ∃ i ∈ s, E i o) ≤ ∑ i ∈ s, μ.prob (E i) := by
  classical
  rw [prob_eq_mean]
  calc
    _ ≤ μ.mean (fun o => ∑ i ∈ s, if E i o then 1 else 0) := by
      apply μ.mean_mono
      intro o
      by_cases he : ∃ i ∈ s, E i o
      · rw [if_pos he]
        obtain ⟨i, hi, hei⟩ := he
        have hh := Finset.single_le_sum (s := s) (f := fun j => if E j o then (1 : ℝ) else 0)
          (fun j _hj => by split_ifs <;> norm_num) hi
        simpa only [if_pos hei] using hh
      · rw [if_neg he]
        exact Finset.sum_nonneg (fun i _hi => by split_ifs <;> norm_num)
    _ = _ := by rw [mean_finset_sum]; simp only [← prob_eq_mean]

theorem prob_le_of_lower (E : Ω → Prop) (f : Ω → ℝ) {a : ℝ} (ha : 0 < a)
    (hf : ∀ o, 0 ≤ f o) (hlower : ∀ o, E o → a ≤ f o) : μ.prob E ≤ μ.mean f / a := by
  classical
  apply (le_div_iff₀ ha).mpr
  rw [prob, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro o _ho
  by_cases he : E o
  · simpa only [if_pos he] using mul_le_mul_of_nonneg_left (hlower o he) (μ.nonneg o)
  · simp only [if_neg he, zero_mul]
    exact mul_nonneg (μ.nonneg o) (hf o)

theorem chebyshev (f : Ω → ℝ) (a : ℝ) {t : ℝ} (ht : 0 < t) :
    μ.prob (fun o => t ≤ |f o - a|) ≤ μ.mean (fun o => (f o - a) ^ 2) / t ^ 2 := by
  apply μ.prob_le_of_lower _ _ (sq_pos_of_pos ht) (fun o => sq_nonneg _)
  intro o ho
  have hh := pow_le_pow_left₀ ht.le ho 2
  simpa only [sq_abs] using hh

theorem mean_sq_sub_one (f : Ω → ℝ) :
    μ.mean (fun o => (f o - 1) ^ 2) = μ.mean (fun o => f o ^ 2) - 2 * μ.mean f + 1 := by
  have heq : (fun o => (f o - 1) ^ 2) = (fun o => (f o ^ 2 - 2 * f o) + 1) := by
    funext o
    ring
  rw [heq, mean_add, mean_sub, mean_const_mul, mean_const]

theorem normalizer_bad_mass_le (f : Ω → ℝ) {η e t : ℝ} (ht : 0 < t)
    (hfirst : |μ.mean f - 1| ≤ η) (hsecond : μ.mean (fun o => f o ^ 2) ≤ 1 + η + e) :
    μ.prob (fun o => t ≤ |f o - 1|) ≤ (3 * η + e) / t ^ 2 := by
  apply (μ.chebyshev f 1 ht).trans
  apply div_le_div_of_nonneg_right _ (sq_nonneg t)
  rw [mean_sq_sub_one]
  have hh := (abs_le.mp hfirst).1
  linarith

end FiniteLaw

end Erdos4.FGKMT
