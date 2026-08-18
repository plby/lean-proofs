import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.Algebra
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# A finite Marcinkiewicz--Zygmund inequality

This file proves the even-moment estimate used by the Croot--Sisask sampling
argument.  Everything is an ordinary finite sum: `A ^^ n` is the set of
`n`-tuples with entries in `A`, equipped with counting measure.  Thus no
measure-theoretic independence infrastructure is needed.

The final result, `RCLike.marcinkiewicz_zygmund`, applies to real- or
complex-valued functions of mean zero.  Its deliberately coarse explicit
constant is

`(8 * m) ^ m * n ^ (m - 1)`

for the moment `2 * m`.  This is the form needed after centering the samples
in the proof of almost-periodicity.
-/

open Finset Fintype Nat

namespace Erdos140

variable {ι : Type*} {A : Finset ι} {m n : ℕ}

local notation:70 s:70 " ^^ " n:71 => Fintype.piFinset fun _ : Fin n ↦ s

private lemma mz_step_one (hA : A.Nonempty) (f : ι → ℝ) (a : Fin n → ι)
    (hf : ∀ i, ∑ a ∈ A ^^ n, f (a i) = 0) :
    |∑ i, f (a i)| ^ (m + 1) ≤
      (∑ b ∈ A ^^ n, |∑ i, (f (a i) - f (b i))| ^ (m + 1)) / #A ^ n := by
  let B := A ^^ n
  calc
    |∑ i, f (a i)| ^ (m + 1)
        = |∑ i, (f (a i) - (∑ b ∈ B, f (b i)) / #B)| ^ (m + 1) := by
          simp only [B, hf, sub_zero, zero_div]
    _ = |(∑ b ∈ B, ∑ i, (f (a i) - f (b i))) / #B| ^ (m + 1) := by
          simp only [sum_sub_distrib]
          rw [sum_const, sub_div, sum_comm, sum_div, nsmul_eq_mul, card_piFinset,
            prod_const, Finset.card_univ, Fintype.card_fin, Nat.cast_pow,
            mul_div_cancel_left₀]
          positivity
    _ = |∑ b ∈ B, ∑ i, (f (a i) - f (b i))| ^ (m + 1) / #B ^ (m + 1) := by
          rw [abs_div, div_pow, Nat.abs_cast]
    _ ≤ (∑ b ∈ B, |∑ i, (f (a i) - f (b i))|) ^ (m + 1) / #B ^ (m + 1) := by
          gcongr
          exact IsAbsoluteValue.abv_sum _ _ _
    _ = (∑ b ∈ B, |∑ i, (f (a i) - f (b i))|) ^ (m + 1) / #B ^ m / #B := by
          rw [div_div, ← _root_.pow_succ]
    _ ≤ (∑ b ∈ B, |∑ i, (f (a i) - f (b i))| ^ (m + 1)) / #B := by
          gcongr
          exact pow_sum_div_card_le_sum_pow (fun _ _ ↦ abs_nonneg _) _
    _ = _ := by simp [B]

private lemma mz_step_one' (hA : A.Nonempty) (f : ι → ℝ)
    (hf : ∀ i, ∑ a ∈ A ^^ n, f (a i) = 0) (m : ℕ) (a : Fin n → ι) :
    |∑ i, f (a i)| ^ m ≤
      (∑ b ∈ A ^^ n, |∑ i, (f (a i) - f (b i))| ^ m) / #A ^ n := by
  cases m
  · simp only [_root_.pow_zero, sum_const, prod_const, Nat.smul_one_eq_cast,
      Finset.card_fin, card_piFinset, ← Nat.cast_pow]
    rw [div_self]
    rw [Nat.cast_ne_zero, ← pos_iff_ne_zero]
    exact pow_pos (Finset.card_pos.2 hA) _
  · exact mz_step_one hA f a hf

private lemma mz_step_two_aux (A : Finset ι) (f : ι → ℝ) (ε : Fin n → ℝ)
    (hε : ε ∈ ({-1, 1} : Finset ℝ) ^^ n) (g : (Fin n → ℝ) → ℝ) :
    ∑ a ∈ A ^^ n, ∑ b ∈ A ^^ n, g (ε * (f ∘ a - f ∘ b)) =
      ∑ a ∈ A ^^ n, ∑ b ∈ A ^^ n, g (f ∘ a - f ∘ b) := by
  rw [← sum_product', ← sum_product']
  let swapper : (Fin n → ι) × (Fin n → ι) → (Fin n → ι) × (Fin n → ι) := by
    intro xy
    exact (fun i ↦ if ε i = 1 then xy.1 i else xy.2 i,
      fun i ↦ if ε i = 1 then xy.2 i else xy.1 i)
  have h₁ : ∀ a ∈ (A ^^ n) ×ˢ (A ^^ n), swapper a ∈ (A ^^ n) ×ˢ (A ^^ n) := by
    simp only [mem_product, mem_piFinset, ← forall_and, swapper]
    intro a h i
    split_ifs
    · exact h i
    · exact (h i).symm
  have h₂ : ∀ a ∈ (A ^^ n) ×ˢ (A ^^ n), swapper (swapper a) = a := fun a _ ↦ by
    ext <;> simp only [swapper] <;> split_ifs <;> rfl
  refine sum_nbij' swapper swapper h₁ h₁ h₂ h₂ ?_
  rintro ⟨a, b⟩ _
  congr with i : 1
  simp only [mem_piFinset, mem_insert, mem_singleton] at hε
  simp only [Pi.mul_apply, Pi.sub_apply, Function.comp_apply, swapper]
  split_ifs with h
  · simp [h]
  rw [(hε i).resolve_right h]
  ring

private lemma mz_step_two (f : ι → ℝ) :
    ∑ a ∈ A ^^ n, ∑ b ∈ A ^^ n, (∑ i, (f (a i) - f (b i))) ^ (2 * m) =
      2⁻¹ ^ n * ∑ ε ∈ ({-1, 1} : Finset ℝ) ^^ n,
        ∑ a ∈ A ^^ n, ∑ b ∈ A ^^ n,
          (∑ i, ε i * (f (a i) - f (b i))) ^ (2 * m) := by
  let B := A ^^ n
  have h : ∀ ε ∈ ({-1, 1} : Finset ℝ) ^^ n,
      ∑ a ∈ B, ∑ b ∈ B, (∑ i, ε i * (f (a i) - f (b i))) ^ (2 * m) =
        ∑ a ∈ B, ∑ b ∈ B, (∑ i, (f (a i) - f (b i))) ^ (2 * m) :=
    fun ε hε ↦ mz_step_two_aux A f _ hε fun z : Fin n → ℝ ↦ univ.sum z ^ (2 * m)
  rw [Finset.sum_congr rfl h, sum_const, card_piFinset_const, card_pair,
    nsmul_eq_mul, Nat.cast_pow, Nat.cast_two, inv_pow, inv_mul_cancel_left₀]
  · positivity
  · norm_num

private lemma mz_step_three (f : ι → ℝ) :
    ∑ ε ∈ ({-1, 1} : Finset ℝ) ^^ n,
        ∑ a ∈ A ^^ n, ∑ b ∈ A ^^ n,
          (∑ i, ε i * (f (a i) - f (b i))) ^ (2 * m) =
      ∑ a ∈ A ^^ n, ∑ b ∈ A ^^ n, ∑ k ∈ piAntidiag univ (2 * m),
        (multinomial univ k * ∏ t, (f (a t) - f (b t)) ^ k t) *
          ∑ ε ∈ ({-1, 1} : Finset ℝ) ^^ n, ∏ t, ε t ^ k t := by
  simp only [@sum_comm _ _ (Fin n → ℝ) _ _ (A ^^ n), sum_pow_eq_sum_piAntidiag]
  refine sum_congr rfl fun a _ ↦ ?_
  refine sum_congr rfl fun b _ ↦ ?_
  simp only [mul_pow, prod_mul_distrib, @sum_comm _ _ (Fin n → ℝ),
    ← mul_sum, ← sum_mul]
  refine sum_congr rfl fun k _ ↦ ?_
  rw [← mul_assoc, mul_right_comm]

private lemma mz_step_four {k : Fin n → ℕ} :
    ∑ ε ∈ ({-1, 1} : Finset ℝ) ^^ n, ∏ t, ε t ^ k t =
      2 ^ n * ite (∀ i, Even (k i)) 1 0 := by
  calc
    _ = ∏ i, ∑ j ∈ ({-1, 1} : Finset ℝ), j ^ k i := by
          rw [← sum_prod_piFinset]
    _ = ∏ i, if Even (k i) then 2 else 0 := by
          congr with i
          split_ifs <;>
            simp_all [sum_pair (show (-1 : ℝ) ≠ 1 by norm_num), one_add_one_eq_two]
    _ = _ := by simp [Fintype.prod_ite_zero]

private lemma mz_step_six {f : ι → ℝ} {a b : Fin n → ι} :
    ∑ k ∈ piAntidiag univ m,
        (multinomial univ fun a ↦ 2 * k a : ℝ) *
          ∏ i, (f (a i) - f (b i)) ^ (2 * k i) ≤
      m ^ m * (∑ i, (f (a i) - f (b i)) ^ 2) ^ m := by
  rw [sum_pow_eq_sum_piAntidiag, mul_sum]
  refine sum_le_sum fun k hk ↦ ?_
  rw [mem_piAntidiag] at hk
  simp only [← mul_assoc, pow_mul]
  gcongr
  norm_cast
  refine multinomial_two_mul_le_mul_multinomial.trans ?_
  rw [hk.1]

private lemma mz_step_seven {f : ι → ℝ} {a b : Fin n → ι} :
    m ^ m * (∑ i, (f (a i) - f (b i)) ^ 2 : ℝ) ^ m ≤
      m ^ m * 2 ^ m * (∑ i, (f (a i) ^ 2 + f (b i) ^ 2)) ^ m := by
  rw [← mul_pow, ← mul_pow, ← mul_pow, mul_assoc, mul_sum _ _ (2 : ℝ)]
  gcongr with i
  exact add_sq_le.trans_eq (by simp)

private lemma mz_step_eight {f : ι → ℝ} {a b : Fin n → ι} :
    m ^ m * 2 ^ m * (∑ i, (f (a i) ^ 2 + f (b i) ^ 2)) ^ m ≤
      m ^ m * 2 ^ (m + (m - 1)) *
        ((∑ i, f (a i) ^ 2) ^ m + (∑ i, f (b i) ^ 2) ^ m) := by
  rw [pow_add, ← mul_assoc _ _ (2 ^ _), mul_assoc _ (2 ^ (m - 1)), sum_add_distrib]
  gcongr
  refine add_pow_le ?_ ?_ m <;> positivity

private lemma mz_end_step {f : ι → ℝ} (hm : 1 ≤ m) (hA : A.Nonempty) :
    (∑ a ∈ A ^^ n, ∑ b ∈ A ^^ n, ∑ k ∈ piAntidiag univ m,
      ↑(multinomial univ fun i ↦ 2 * k i) *
        ∏ t, (f (a t) - f (b t)) ^ (2 * k t)) / #A ^ n ≤
      (4 * m) ^ m * ∑ a ∈ A ^^ n, (∑ i, f (a i) ^ 2) ^ m := by
  let B := A ^^ n
  calc
    (∑ a ∈ B, ∑ b ∈ B, ∑ k ∈ piAntidiag univ m,
      (multinomial univ fun i ↦ 2 * k i : ℝ) *
        ∏ t, (f (a t) - f (b t)) ^ (2 * k t)) / #A ^ n
        ≤ (∑ a ∈ B, ∑ b ∈ B, m ^ m * 2 ^ (m + (m - 1)) *
            ((∑ i, f (a i) ^ 2) ^ m + (∑ i, f (b i) ^ 2) ^ m) : ℝ) /
            #A ^ n := by
          gcongr
          exact mz_step_six.trans <| mz_step_seven.trans mz_step_eight
    _ = _ := by
      simp only [mul_add, sum_add_distrib, sum_const, nsmul_eq_mul, ← mul_sum]
      rw [← mul_add, ← two_mul, ← mul_assoc 2, ← mul_assoc 2, mul_right_comm 2,
        ← _root_.pow_succ', add_assoc, Nat.sub_add_cancel hm, pow_add, ← mul_pow,
        ← mul_pow, card_piFinset, prod_const, Finset.card_univ, Fintype.card_fin,
        Nat.cast_pow, mul_div_cancel_left₀]
      · norm_num
        dsimp [B]
      · positivity

namespace Real

attribute [-instance] decidableForallFin

/-- The finite Marcinkiewicz--Zygmund inequality in its square-function form.
The `n` coordinate samples are independent because the sum ranges over the
entire product `A ^^ n`. -/
theorem marcinkiewicz_zygmund_square (m : ℕ) (f : ι → ℝ)
    (hf : ∀ i, ∑ a ∈ A ^^ n, f (a i) = 0) :
    ∑ a ∈ A ^^ n, (∑ i, f (a i)) ^ (2 * m) ≤
      (4 * m) ^ m * ∑ a ∈ A ^^ n, (∑ i, f (a i) ^ 2) ^ m := by
  obtain rfl | hm := m.eq_zero_or_pos
  · simp
  have hm' : 1 ≤ m := by rwa [Nat.succ_le_iff]
  obtain rfl | hA := A.eq_empty_or_nonempty
  · cases n <;> cases m <;> simp
  let B := A ^^ n
  calc
    ∑ a ∈ B, (∑ i, f (a i)) ^ (2 * m)
        ≤ ∑ a ∈ A ^^ n,
            (∑ b ∈ B, |∑ i, (f (a i) - f (b i))| ^ (2 * m)) / #A ^ n := by
          gcongr
          simpa [pow_mul, sq_abs] using mz_step_one' hA f hf (2 * m) _
    _ = (∑ a ∈ A ^^ n, ∑ b ∈ A ^^ n,
          ∑ k ∈ piAntidiag univ (2 * m) with ∀ i, 2 ∣ k i,
            multinomial univ (fun i ↦ k i) *
              ∏ t, (f (a t) - f (b t)) ^ k t) / #A ^ n := by
      rw [← sum_div]
      simp only [pow_mul, sq_abs]
      simp only [← pow_mul]
      rw [mz_step_two, mz_step_three, mul_comm, inv_pow, ← div_eq_mul_inv, div_div]
      simp only [mz_step_four, mul_ite, mul_zero, mul_one, ← sum_filter, ← sum_mul,
        even_iff_two_dvd]
      rw [mul_comm, mul_div_mul_left]
      positivity
    _ = (∑ a ∈ A ^^ n, ∑ b ∈ A ^^ n,
          ∑ k ∈ (piAntidiag univ m).map
            ⟨(2 • ·), fun _ _ h ↦ funext fun i ↦
              mul_right_injective₀ two_ne_zero (congr_fun h i)⟩,
            multinomial univ (fun i ↦ k i) *
              ∏ t, (f (a t) - f (b t)) ^ k t) / #A ^ n := by
      rw [map_nsmul_piAntidiag_univ m (ι := Fin n) (n := 2) two_ne_zero]
    _ = (∑ a ∈ A ^^ n, ∑ b ∈ A ^^ n, ∑ k ∈ piAntidiag univ m,
          multinomial univ (fun i ↦ 2 * k i) *
            ∏ t, (f (a t) - f (b t)) ^ (2 * k t)) / #A ^ n := by
      simp
    _ ≤ _ := mz_end_step hm' hA

/-- A one-sum version of finite Marcinkiewicz--Zygmund for real functions.
Compared with the square-function form, Hölder costs `n^(m-1)`. -/
theorem marcinkiewicz_zygmund (hm : m ≠ 0) (f : ι → ℝ)
    (hf : ∀ i, ∑ a ∈ A ^^ n, f (a i) = 0) :
    ∑ a ∈ A ^^ n, (∑ i, f (a i)) ^ (2 * m) ≤
      (4 * m) ^ m * n ^ (m - 1) *
        ∑ a ∈ A ^^ n, ∑ i, f (a i) ^ (2 * m) := by
  obtain _ | m := m
  · simp at hm
  obtain rfl | hn := n.eq_zero_or_pos
  · simp
  calc
    ∑ a ∈ A ^^ n, (∑ i, f (a i)) ^ (2 * (m + 1))
        ≤ (4 * ↑(m + 1)) ^ (m + 1) *
            ∑ a ∈ A ^^ n, (∑ i, f (a i) ^ 2) ^ (m + 1) :=
          marcinkiewicz_zygmund_square _ f hf
    _ ≤ (4 * ↑(m + 1)) ^ (m + 1) *
          (∑ a ∈ A ^^ n, n ^ m * ∑ i, f (a i) ^ (2 * (m + 1))) := by
      gcongr with a
      rw [← div_le_iff₀' (by positivity)]
      simpa only [Finset.card_fin, pow_mul] using
        pow_sum_div_card_le_sum_pow (f := fun i ↦ f (a i) ^ 2) (s := univ)
          (fun i _ ↦ by positivity) m
    _ ≤ (4 * ↑(m + 1)) ^ (m + 1) * n ^ m *
          ∑ a ∈ A ^^ n, ∑ i, f (a i) ^ (2 * (m + 1)) := by
      simp_rw [mul_assoc, mul_sum]
      rfl

end Real

namespace RCLike

variable {𝕜 : Type*} [RCLike 𝕜]

/-- The finite Marcinkiewicz--Zygmund inequality for real- or complex-valued
mean-zero samples.  This is the form directly used by Croot--Sisask. -/
theorem marcinkiewicz_zygmund (hm : m ≠ 0) (f : ι → 𝕜)
    (hf : ∀ i, ∑ a ∈ A ^^ n, f (a i) = 0) :
    ∑ a ∈ A ^^ n, ‖∑ i, f (a i)‖ ^ (2 * m) ≤
      (8 * m) ^ m * n ^ (m - 1) *
        ∑ a ∈ A ^^ n, ∑ i, ‖f (a i)‖ ^ (2 * m) := by
  let f₁ x : ℝ := _root_.RCLike.re (f x)
  let f₂ x : ℝ := _root_.RCLike.im (f x)
  let B := A ^^ n
  have hf₁ i : ∑ a ∈ B, f₁ (a i) = 0 := by rw [← map_sum, hf, map_zero]
  have hf₂ i : ∑ a ∈ B, f₂ (a i) = 0 := by rw [← map_sum, hf, map_zero]
  have h₁ := Real.marcinkiewicz_zygmund hm _ hf₁
  have h₂ := Real.marcinkiewicz_zygmund hm _ hf₂
  simp only [pow_mul, _root_.RCLike.norm_sq_eq_def]
  simp only [← sq, map_sum, map_sum]
  calc
    ∑ a ∈ B,
        ((∑ i, _root_.RCLike.re (f (a i))) ^ 2 +
          (∑ i, _root_.RCLike.im (f (a i))) ^ 2) ^ m ≤
      ∑ a ∈ B, 2 ^ (m - 1) *
        (((∑ i, _root_.RCLike.re (f (a i))) ^ 2) ^ m +
          ((∑ i, _root_.RCLike.im (f (a i))) ^ 2) ^ m) := by
          gcongr with a
          apply add_pow_le <;> positivity
    _ = 2 ^ (m - 1) *
        (∑ a ∈ B, (∑ i, _root_.RCLike.re (f (a i))) ^ (2 * m) +
          ∑ a ∈ B, (∑ i, _root_.RCLike.im (f (a i))) ^ (2 * m)) := by
      simp only [← sum_add_distrib, mul_sum, pow_mul]
    _ ≤ 2 ^ (m - 1) *
        ((4 * m) ^ m * n ^ (m - 1) *
            ∑ a ∈ B, ∑ i, _root_.RCLike.re (f (a i)) ^ (2 * m) +
          (4 * m) ^ m * n ^ (m - 1) *
            ∑ a ∈ B, ∑ i, _root_.RCLike.im (f (a i)) ^ (2 * m)) := by
      gcongr
    _ = 2 ^ (m - 1) *
        ((4 * m) ^ m * n ^ (m - 1) *
          ∑ a ∈ B, ∑ i,
            (_root_.RCLike.re (f (a i)) ^ (2 * m) +
              _root_.RCLike.im (f (a i)) ^ (2 * m))) := by
      simp_rw [sum_add_distrib, mul_add]
    _ ≤ 2 ^ (m - 1) *
        ((4 * m) ^ m * n ^ (m - 1) *
          ∑ a ∈ B, ∑ i,
            2 * (_root_.RCLike.re (f (a i)) ^ 2 +
              _root_.RCLike.im (f (a i)) ^ 2) ^ m) := by
      simp_rw [pow_mul]
      gcongr
      apply pow_add_pow_le' <;> positivity
    _ = (8 * m) ^ m * n ^ (m - 1) *
        ∑ a ∈ B, ∑ i,
          (_root_.RCLike.re (f (a i)) ^ 2 +
            _root_.RCLike.im (f (a i)) ^ 2) ^ m := by
      simp_rw [← mul_sum, show (8 : ℝ) = 2 * 4 by norm_num, mul_pow,
        ← pow_sub_one_mul hm (2 : ℝ)]
      ring

end RCLike

end Erdos140

#print axioms Erdos140.RCLike.marcinkiewicz_zygmund
