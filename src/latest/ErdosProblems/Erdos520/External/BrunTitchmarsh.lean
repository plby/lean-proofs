/-
Copyright (c) 2024 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Arend Mellendijk

Vendored proof excerpt through `primesBetween_le`, adapted to the Erdős project module paths.
-/

import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.NumberTheory.Primorial
import ErdosProblems.Erdos520.External.Sieve.Selberg
import ErdosProblems.Erdos520.External.Sieve.SelbergBounds

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Sieve SelbergSieve BoundingSieve
open Filter Asymptotics
open scoped Nat ArithmeticFunction BigOperators ArithmeticFunction.zeta ArithmeticFunction.omega

noncomputable section
namespace BrunTitchmarsh

/-- Sifting primes ≤ z from the interval [x, x+y] -/
def primeInterSieve (x y z : ℝ) (hz : 1 ≤ z) : SelbergSieve where
  support := Finset.Icc (Nat.ceil x) (Nat.floor (x+y))
  prodPrimes := primorial (Nat.floor z)
  prodPrimes_squarefree := primorial_squarefree _
  weights := fun _ ↦ 1
  weights_nonneg := fun _ ↦ zero_le_one
  totalMass := y
  nu := (ζ : ArithmeticFunction ℝ).pdiv .id
  nu_mult := by arith_mult
  nu_pos_of_prime := fun p hp _ ↦ by
    simp [if_neg hp.ne_zero, Nat.pos_of_ne_zero hp.ne_zero]
  nu_lt_one_of_prime := fun p hp _ ↦ by
    simp only [ArithmeticFunction.pdiv_apply, ArithmeticFunction.natCoe_apply,
      ArithmeticFunction.zeta_apply, hp.ne_zero, ↓reduceIte, Nat.cast_one,
      ArithmeticFunction.id_apply, one_div]
    apply inv_lt_one_of_one_lt₀
    exact_mod_cast hp.one_lt
  level := z
  one_le_level := hz

/-- The number of primes in the interval [a, b] -/
def primesBetween (a b : ℝ) : ℕ :=
  (Finset.Icc (Nat.ceil a) (Nat.floor b)).filter Nat.Prime |>.card

variable (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 1 ≤ z)

open Classical in
theorem siftedSum_eq_card :
    siftedSum (s := toBoundingSieve (self := primeInterSieve x y z hz)) =
      ((Finset.Icc (Nat.ceil x) (Nat.floor (x+y))).filter
        (fun d ↦ ∀ p : ℕ, p.Prime → p ≤ z → ¬p ∣ d)).card := by
  apply Sieve.siftedSum_eq
  · exact fun _ _ ↦ rfl
  · exact hz
  · rfl

open Classical in
theorem primesBetween_subset :
  (Finset.Icc (Nat.ceil x) (Nat.floor (x+y))).filter Nat.Prime ⊆
    (Finset.Icc (Nat.ceil x) (Nat.floor (x+y))).filter
      (fun d ↦ ∀ p : ℕ, p.Prime → p ≤ z → ¬p ∣ d) ∪
      (Finset.Icc 1 (Nat.floor z)) := by
  intro p
  simp only [Finset.mem_filter, Finset.mem_Icc, Nat.ceil_le, Finset.mem_union, and_imp]
  intro hx hxy hp
  by_cases hpz : p ≤ z
  · right
    rw [Nat.le_floor_iff (by linarith)]
    have := hp.ne_zero
    exact ⟨by omega, hpz⟩
  · refine Or.inl ⟨⟨hx, hxy⟩, fun q hq hqz ↦ ?_⟩
    rw [hp.dvd_iff_eq (hq.ne_one)]
    rintro rfl
    exact hpz hqz

theorem primesBetween_le_siftedSum_add :
    primesBetween x (x+y) ≤
      siftedSum (s := toBoundingSieve (self := primeInterSieve x y z hz)) + z := by
  classical
  trans ↑((Finset.Icc (Nat.ceil x) (Nat.floor (x+y))).filter
      (fun d ↦ ∀ p : ℕ, p.Prime → p ≤ z → ¬p ∣ d) ∪
      (Finset.Icc 1 (Nat.floor z))).card
  · rw [primesBetween]
    exact_mod_cast Finset.card_le_card (primesBetween_subset _ _ _)
  trans ↑((Finset.Icc (Nat.ceil x) (Nat.floor (x+y))).filter
      (fun d ↦ ∀ p : ℕ, p.Prime → p ≤ z → ¬p ∣ d)).card +
      ↑(Finset.Icc 1 (Nat.floor z)).card
  · exact_mod_cast Finset.card_union_le _ _
  rw [siftedSum_eq_card]
  gcongr
  rw [Nat.card_Icc]
  simp only [add_tsub_cancel_right]
  apply Nat.floor_le
  linarith

section Remainder

theorem Ioc_filter_dvd_eq (d a b : ℕ) (hd : d ≠ 0) :
  Finset.filter (fun x ↦ d ∣ x) (Finset.Ioc a b) =
    Finset.image (fun x ↦ x * d) (Finset.Ioc (a / d) (b / d)) := by
  ext n
  simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_image]
  constructor
  · intro hn
    rcases hn with ⟨⟨han, hnb⟩, hd⟩
    refine ⟨n/d, ⟨Nat.div_lt_div_of_lt_of_dvd hd han,
      Nat.div_le_div_right (Nat.le_floor hnb)⟩, Nat.div_mul_cancel hd⟩
  · rintro ⟨r, ⟨ha, ha'⟩, rfl⟩
    refine ⟨⟨(Nat.div_lt_iff_lt_mul (by omega)).mp ha, Nat.mul_le_of_le_div d r b ha'⟩,
      Nat.dvd_mul_left d r⟩

theorem card_Ioc_filter_dvd (d a b : ℕ) (hd : d ≠ 0) :
    (Finset.filter (fun x ↦ d ∣ x) (Finset.Ioc a b)).card =
      b / d - a / d := by
  rw [Ioc_filter_dvd_eq _ _ _ hd, Finset.card_image_of_injective _ <| mul_left_injective₀ hd,
    Nat.card_Ioc]

include hx in
theorem multSum_eq (d : ℕ) (hd : d ≠ 0) :
    multSum (s := toBoundingSieve (self := primeInterSieve x y z hz)) d =
      ↑(⌊x + y⌋₊ / d - (⌈x⌉₊ - 1) / d) := by
  unfold multSum
  rw [primeInterSieve]
  simp only [Finset.sum_boole, Nat.cast_inj]
  trans ↑(Finset.Ioc (Nat.ceil x - 1) (Nat.floor (x+y)) |>.filter (d ∣ ·) |>.card)
  · rw [← Finset.Icc_add_one_left_eq_Ioc, Nat.sub_add_cancel (Nat.one_le_ceil_iff.mpr hx)]
  · rw [BrunTitchmarsh.card_Ioc_filter_dvd _ _ _ hd]

include hx in
theorem rem_eq (d : ℕ) (hd : d ≠ 0) :
    rem (s := toBoundingSieve (self := primeInterSieve x y z hz)) d =
      ↑(⌊x + y⌋₊ / d - (⌈x⌉₊ - 1) / d) - (↑d)⁻¹ * y := by
  unfold rem
  rw [multSum_eq x y z hx hz d hd]
  simp [primeInterSieve, if_neg hd]

theorem Nat.ceil_le_self_add_one (x : ℝ) (hx : 0 ≤ x) : Nat.ceil x ≤ x + 1 := by
  trans Nat.floor x + 1
  · exact_mod_cast Nat.ceil_le_floor_add_one x
  · gcongr
    exact Nat.floor_le hx

theorem floor_approx (x : ℝ) (hx : 0 ≤ x) :
    ∃ C, |C| ≤ 1 ∧ ↑((Nat.floor x)) = x + C := by
  use ↑(Nat.floor x) - x
  simp only [add_sub_cancel, and_true]
  rw [abs_le]
  refine ⟨by linarith [Nat.lt_floor_add_one x], by linarith [Nat.floor_le hx]⟩

theorem ceil_approx (x : ℝ) (hx : 0 ≤ x) : ∃ C, |C| ≤ 1 ∧ ↑((Nat.ceil x)) = x + C := by
  use ↑(Nat.ceil x) - x
  simp only [add_sub_cancel, and_true, abs_le]
  refine ⟨by linarith [Nat.le_ceil x], ?_⟩
  rw [tsub_le_iff_right, add_comm]
  exact Nat.ceil_le_self_add_one x hx

theorem nat_div_approx (a b : ℕ) : ∃ C, |C| ≤ 1 ∧ ↑(a/b) = (a/b : ℝ) + C := by
  rw [← Nat.floor_div_eq_div (K := ℝ)]
  exact floor_approx (a/b:ℝ) (by positivity)

theorem floor_div_approx (x : ℝ) (hx : 0 ≤ x) (d : ℕ) :
    ∃ C, |C| ≤ 2 ∧ ↑((Nat.floor x)/d) = x / d + C := by
  by_cases hd : d = 0
  · simp [hd]
  · obtain ⟨C₁, hC₁_le, hC₁⟩ := nat_div_approx (Nat.floor x) d
    obtain ⟨C₂, hC₂_le, hC₂⟩ := floor_approx x hx
    rw [hC₁, hC₂]
    refine ⟨C₁ + C₂/d, ?_, by ring⟩
    have : |C₁ + C₂/d| ≤ |C₁| + |C₂/d| := abs_add_le C₁ (C₂ / ↑d)
    have : |C₂/d| ≤ |C₂| := by
      rw [abs_div]
      refine div_le_self (abs_nonneg C₂) ?_
      simp only [Nat.abs_cast, Nat.one_le_cast]
      omega
    linarith

include hx hy in
theorem abs_rem_le {d : ℕ} (hd : d ≠ 0) :
    |rem (s := toBoundingSieve (self := primeInterSieve x y z hz)) d| ≤ 5 := by
  rw [rem_eq _ _ _ hx hz _ hd]
  have hpush : ↑(⌊x + y⌋₊ / d - (⌈x⌉₊ - 1) / d) =
      (↑(⌊x + y⌋₊ / d) - ↑((⌈x⌉₊ - 1) / d) : ℝ) := by
    rw [Nat.cast_sub]
    gcongr
    rw [Nat.le_floor_iff, ← add_le_add_iff_right 1]
    · rw_mod_cast [Nat.sub_add_cancel (by simp [hx])]
      linarith [Nat.ceil_le_self_add_one x (le_of_lt hx)]
    linarith
  rw [hpush]
  obtain ⟨C₁, hC₁_le, hC₁⟩ := floor_div_approx (x + y) (by linarith) d
  obtain ⟨C₂, hC₂_le, hC₂⟩ := nat_div_approx (Nat.ceil x - 1) d
  obtain ⟨C₃, hC₃_le, hC₃⟩ := ceil_approx (x) (by linarith)
  rw [hC₁, hC₂, Nat.cast_sub, hC₃]
  · ring_nf
    rw [(by ring_nf : |(↑d)⁻¹ - (↑d)⁻¹ * C₃ + C₁ - C₂| = |(↑d)⁻¹ - (↑d)⁻¹ * C₃ + (C₁ - C₂)|)]
    have : |(↑d)⁻¹ - (↑d)⁻¹ * C₃ + (C₁ - C₂)| ≤
        |(↑d)⁻¹ - (↑d)⁻¹ * C₃| + |C₁ - C₂| := abs_add_le _ _
    have : |(↑d)⁻¹ - (↑d)⁻¹ * C₃| ≤
        |(↑d)⁻¹| + |(↑d)⁻¹ * C₃| := abs_sub _ _
    have : |C₁ - C₂| ≤ |C₁| + |C₂| := abs_sub _ _
    have : |(d:ℝ)⁻¹| ≤ 1 := by
      rw [abs_inv, Nat.abs_cast]
      exact Nat.cast_inv_le_one _
    have : |(↑d)⁻¹ * C₃| ≤ |C₃| := by
      rw [inv_mul_eq_div, abs_div]
      refine div_le_self (abs_nonneg _) ?_
      rw [Nat.abs_cast, Nat.one_le_cast]
      omega
    linarith
  · simp [hx]

end Remainder

theorem boudingSum_ge : (primeInterSieve x y z hz).selbergBoundingSum ≥ Real.log z / 2 := by
  apply boundingSum_ge_log
  · exact rfl
  · intro p hpp hp
    erw [prime_dvd_primorial_iff]
    · exact Nat.le_floor hp
    · exact hpp

include hx hy in
theorem primeSieve_rem_sum_le :
    ∑ d ∈ (primeInterSieve x y z hz).prodPrimes.divisors,
        (if (d : ℝ) ≤ z then (3:ℝ) ^ ω d *
          |rem (s := toBoundingSieve (self := primeInterSieve x y z hz)) d| else 0)
      ≤ 5 * z * (1 + Real.log z) ^ 3 := by
  refine rem_sum_le_of_const (primeInterSieve x y z hz) 5 (fun d hd ↦ ?_)
  apply abs_rem_le _ _ _ <;> linarith

include hx hy in
theorem siftedSum_le (hz : 1 < z) :
    siftedSum (s := toBoundingSieve (self := primeInterSieve x y z (le_of_lt hz)))
      ≤ 2 * y / Real.log z + 5 * z * (1 + Real.log z) ^ 3 := by
  apply le_trans (SelbergSieve.selberg_bound_simple ..)
  calc _ ≤ y / (Real.log z / 2) + 5 * z * (1 + Real.log z) ^ 3 := ?_
       _ = _ := by ring
  gcongr
  · linarith [Real.log_pos hz]
  · rfl
  · exact boudingSum_ge _ _ _ _
  · exact primeSieve_rem_sum_le x y z hx hy _

include hx hy in
theorem primesBetween_le (hz : 1 < z) :
    primesBetween x (x+y) ≤ 2 * y / Real.log z + 6 * z * (1 + Real.log z) ^ 3 := by
  have : z ≤ z * (1 + Real.log z) ^ 3 := by
    apply le_mul_of_one_le_right
    · linarith
    · apply one_le_pow₀
      linarith [Real.log_nonneg (by linarith)]
  linarith [siftedSum_le _ _ _ hx hy hz, primesBetween_le_siftedSum_add x y z hz.le]


end BrunTitchmarsh
