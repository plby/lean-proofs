/-
Adapted from Jayyhk/erdos-lean, problems/696/Erdos696.lean,
revision 806d0b587ea7a2fb5afd5154edfe416a0cd404a4.
Source: https://www.erdosproblems.com/forum/thread/696#post-6848
All upstream heartbeat overrides have been removed.
-/

import Mathlib

namespace Erdos696

-- === Inlined from SelbergSieve4.Tactic.AesopDiv ===
/-
Copyright (c) 2026 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arend Mellendijk
-/

/-!
# LeanPool.SelbergSieve4.Tactic.AesopDiv
-/

namespace LPSieve
open Finset

/-- Wrapper predicate for divisibility. -/
protected def MyDvd (a b : ℕ) : Prop := a ∣ b
open LPSieve (MyDvd)

@[simp]
theorem myDvd_iff (a b : ℕ) : MyDvd a b ↔ a ∣ b := by
  exact Iff.rfl

theorem dvd_of_myDvd (a b : ℕ) : MyDvd a b → a ∣ b := (myDvd_iff a b).mp

theorem myDvd_of_dvd (a b : ℕ) : a ∣ b → MyDvd a b := (myDvd_iff a b).mpr

theorem myDvd_trans {a b c : ℕ} : MyDvd a b → MyDvd b c → MyDvd a c := by
  intro hab hbc
  exact (myDvd_iff a c).mpr (Nat.dvd_trans ((myDvd_iff a b).mp hab) ((myDvd_iff b c).mp hbc))

theorem myDvd_of_mem_divisors {a b : ℕ} : a ∈ b.divisors → MyDvd a b := by
  rw [myDvd_iff]; exact Nat.dvd_of_mem_divisors

theorem myDvd_of_mem_primeFactors {a b : ℕ} : a ∈ b.primeFactors → MyDvd a b := by
  rw [myDvd_iff]; exact Nat.dvd_of_mem_primeFactors

theorem eq_zero_of_zero_myDvd (a : ℕ) : MyDvd 0 a → a = 0 := by
  intro h
  exact eq_zero_of_zero_dvd ((myDvd_iff 0 a).mp h)

theorem zero_mem_divisors (a : ℕ) (h : 0 ∈ a.divisors) : False := by simp at h

theorem mem_zero_divisors (a : ℕ) (h : a ∈ Nat.divisors 0) : False := by simp at h

theorem zero_lt_zero (h : 0 < 0) : False := by linarith

theorem test {n m : ℕ} : n ∣ m ∧ m ≠ 0 → n ∈ m.divisors := Nat.mem_divisors.mpr

theorem dvd_of_gcd_dvd_left (a b c : ℕ) (h : MyDvd c (a.gcd b)) : MyDvd c a :=
  myDvd_trans h (myDvd_of_dvd _ _ <| Nat.gcd_dvd_left a b)

theorem dvd_of_gcd_dvd_right (a b c : ℕ) (h : MyDvd c (a.gcd b)) : MyDvd c b :=
  myDvd_trans h (myDvd_of_dvd _ _ <| Nat.gcd_dvd_right a b)

theorem gcd_dvd_of_dvd_left (a b c : ℕ) (h : MyDvd a c) : MyDvd (a.gcd b) c :=
  myDvd_trans (myDvd_of_dvd _ _ <| Nat.gcd_dvd_left a b) h

theorem gcd_dvd_of_dvd_right (a b c : ℕ) (h : MyDvd b c) : MyDvd (a.gcd b) c :=
  myDvd_trans (myDvd_of_dvd _ _ <| Nat.gcd_dvd_right a b) h

theorem gcd_myDvd_left (a b : ℕ) : MyDvd (a.gcd b) a :=
  myDvd_of_dvd _ _ (gcd_dvd_left a b)

theorem gcd_myDvd_right (a b : ℕ) : MyDvd (a.gcd b) b :=
  myDvd_of_dvd _ _ (gcd_dvd_right a b)

theorem gcd_eq_zero_left (a b : ℕ) (h : a.gcd b = 0) : a = 0 := by
  rw [Nat.gcd_eq_zero_iff] at h; exact h.1
theorem gcd_eq_zero_right (a b : ℕ) (h : a.gcd b = 0) : b = 0 := by
  rw [Nat.gcd_eq_zero_iff] at h; exact h.2

theorem dvd_of_lcm_dvd_left (a b c : ℕ) (h : MyDvd (a.lcm b) c) : MyDvd a c :=
  myDvd_trans (myDvd_of_dvd _ _ <| Nat.dvd_lcm_left a b) h

theorem dvd_of_lcm_dvd_right (a b c : ℕ) (h : MyDvd (a.lcm b) c) : MyDvd b c :=
  myDvd_trans (myDvd_of_dvd _ _ <| Nat.dvd_lcm_right a b) h

theorem dvd_lcm_of_dvd_left (a b c : ℕ) (h : MyDvd c a) : MyDvd c (a.lcm b) :=
  myDvd_trans h (myDvd_of_dvd _ _ <| Nat.dvd_lcm_left a b)

theorem dvd_lcm_of_dvd_right (a b c : ℕ) (h : MyDvd c b) : MyDvd c (a.lcm b) :=
  myDvd_trans h (myDvd_of_dvd _ _ <| Nat.dvd_lcm_right a b)

theorem myDvd_lcm_left (a b : ℕ) : MyDvd a (a.lcm b) :=
  myDvd_of_dvd _ _ (dvd_lcm_left a b)

theorem myDvd_lcm_right (a b : ℕ) : MyDvd b (a.lcm b) :=
  myDvd_of_dvd _ _ (dvd_lcm_right a b)

theorem lcm_eq_zero_left (a b : ℕ) (h : a.lcm b = 0) : a = 0 ∨ b = 0 := by
  rw [←lcm_eq_nat_lcm, _root_.lcm_eq_zero_iff] at h; exact h

theorem squarefree_of_myDvd (a b : ℕ) (hb : Squarefree b) (h : MyDvd a b) :
    Squarefree a := by
  rw[myDvd_iff] at h
  exact Squarefree.squarefree_of_dvd h hb

/-- Run `aesop` with the divisibility lemma pack inlined and simp disabled. -/
macro (name := aesopDiv) "aesopDiv" c:Aesop.tactic_clause* : tactic =>
`(tactic|
  aesop $c*
    (config := { enableSimp := false })
    (add safe [LPSieve.dvd_of_myDvd, LPSieve.test, LPSieve.gcd_dvd_of_dvd_left,
               LPSieve.gcd_dvd_of_dvd_right, LPSieve.gcd_myDvd_left, LPSieve.gcd_myDvd_right,
               LPSieve.dvd_lcm_of_dvd_left, LPSieve.dvd_lcm_of_dvd_right,
               LPSieve.myDvd_lcm_left, LPSieve.myDvd_lcm_right, Nat.pos_of_ne_zero])
    (add safe destruct [LPSieve.myDvd_of_dvd])
    (add safe forward [LPSieve.myDvd_trans, LPSieve.myDvd_of_mem_divisors,
                       LPSieve.myDvd_of_mem_primeFactors, not_squarefree_zero,
                       LPSieve.eq_zero_of_zero_myDvd, LPSieve.zero_mem_divisors,
                       LPSieve.mem_zero_divisors, LPSieve.zero_lt_zero,
                       LPSieve.dvd_of_gcd_dvd_left, LPSieve.dvd_of_gcd_dvd_right,
                       LPSieve.gcd_eq_zero_left, LPSieve.gcd_eq_zero_right,
                       LPSieve.dvd_of_lcm_dvd_left, LPSieve.dvd_of_lcm_dvd_right,
                       LPSieve.lcm_eq_zero_left, Squarefree.squarefree_of_dvd,
                       LPSieve.squarefree_of_myDvd,
                       $(Lean.mkIdent `LPSieve.prodPrimes_ne_zero):ident,
                       $(Lean.mkIdent `LPSieve.prodPrimes_squarefree):ident]))

/-- `aesop?` companion variant of `aesopDiv`. -/
macro (name := aesopDiv?) "aesopDiv?" c:Aesop.tactic_clause* : tactic =>
`(tactic|
  aesop? $c*
    (config := { enableSimp := false })
    (add safe [LPSieve.dvd_of_myDvd, LPSieve.test, LPSieve.gcd_dvd_of_dvd_left,
               LPSieve.gcd_dvd_of_dvd_right, LPSieve.gcd_myDvd_left, LPSieve.gcd_myDvd_right,
               LPSieve.dvd_lcm_of_dvd_left, LPSieve.dvd_lcm_of_dvd_right,
               LPSieve.myDvd_lcm_left, LPSieve.myDvd_lcm_right, Nat.pos_of_ne_zero])
    (add safe destruct [LPSieve.myDvd_of_dvd])
    (add safe forward [LPSieve.myDvd_trans, LPSieve.myDvd_of_mem_divisors,
                       LPSieve.myDvd_of_mem_primeFactors, not_squarefree_zero,
                       LPSieve.eq_zero_of_zero_myDvd, LPSieve.zero_mem_divisors,
                       LPSieve.mem_zero_divisors, LPSieve.zero_lt_zero,
                       LPSieve.dvd_of_gcd_dvd_left, LPSieve.dvd_of_gcd_dvd_right,
                       LPSieve.gcd_eq_zero_left, LPSieve.gcd_eq_zero_right,
                       LPSieve.dvd_of_lcm_dvd_left, LPSieve.dvd_of_lcm_dvd_right,
                       LPSieve.lcm_eq_zero_left, Squarefree.squarefree_of_dvd,
                       LPSieve.squarefree_of_myDvd,
                       $(Lean.mkIdent `LPSieve.prodPrimes_ne_zero):ident,
                       $(Lean.mkIdent `LPSieve.prodPrimes_squarefree):ident]))

end LPSieve



-- === Inlined from SelbergSieve4.ForMathlib.Basic ===
/-
Copyright (c) 2026 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arend Mellendijk
-/
/-!
# LeanPool.SelbergSieve4.ForMathlib.Basic
-/

namespace Aux

open BigOperators ArithmeticFunction
/- Lemmas in this file are singled out as suitable for addition to Mathlib with minor
modifications. -/

variable {R : Type*}

theorem mult_lcm_eq_of_ne_zero [CommGroupWithZero R] (f : ArithmeticFunction R)
    (h_mult : f.IsMultiplicative) (x y : ℕ)
    (hf : f (x.gcd y) ≠ 0) :
    f (x.lcm y) = f x * f y / f (x.gcd y) := by
  rw [←h_mult.lcm_apply_mul_gcd_apply]
  field_simp

theorem prod_factors_of_mult (f : ArithmeticFunction ℝ)
    (h_mult : ArithmeticFunction.IsMultiplicative f) {l : ℕ} (hl : Squarefree l) :
    ∏ a ∈ l.primeFactors, f a = f l := by
  rw [←IsMultiplicative.map_prod_of_subset_primeFactors h_mult l _ Finset.Subset.rfl,
    Nat.prod_primeFactors_of_squarefree hl]

end Aux



-- === Inlined from SelbergSieve4.ForMathlib.ProdsAntidiagonal ===
/-
Copyright (c) 2026 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arend Mellendijk
-/


/-!
# LeanPool.SelbergSieve4.ForMathlib.ProdsAntidiagonal
-/

section LPSieveProdsAntidiagonal
open scoped ArithmeticFunction.omega

/-- Alias for the multiplicative antidiagonal indexed by `Fin d`. -/
abbrev _root_.Nat.finMulAntidiagonal (d n : ℕ) : Finset (Fin d → ℕ) :=
  Nat.finMulAntidiag d n

/-- Membership in the multiplicative antidiagonal. -/
theorem _root_.Nat.mem_finMulAntidiagonal {d n : ℕ} {f : Fin d → ℕ} :
    f ∈ Nat.finMulAntidiagonal d n ↔ ∏ i, f i = n ∧ n ≠ 0 :=
  Nat.mem_finMulAntidiag

theorem _root_.Nat.finMulAntidiagonal_univ_eq {d m n : ℕ} (hmn : m ∣ n) (hn : n ≠ 0) :
    Nat.finMulAntidiagonal d m =
      (Fintype.piFinset fun _ : Fin d => n.divisors).filter (fun f => ∏ i, f i = m) :=
  Nat.finMulAntidiag_eq_piFinset_divisors_filter hmn hn

theorem _root_.Nat.card_finMulAntidiagonal {d n : ℕ} (hn : Squarefree n) :
    (Nat.finMulAntidiagonal d n).card = d ^ ω n := by
  simpa [Nat.finMulAntidiagonal] using Nat.card_finMulAntidiag_of_squarefree (d := d) hn

end LPSieveProdsAntidiagonal



-- === Inlined from SelbergSieve4.AuxResults ===
/-
Copyright (c) 2026 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arend Mellendijk
-/

/-!
# LeanPool.SelbergSieve4.AuxResults
-/

--import LPSelbergSieve.AesopDiv
noncomputable section

local macro_rules | `($x ^ $y)   => `(HPow.hPow $x $y)
open scoped BigOperators ArithmeticFunction.zeta ArithmeticFunction.Moebius ArithmeticFunction.omega

open Nat ArithmeticFunction Finset

namespace Aux

theorem sum_over_dvd_ite {α : Type _} [Ring α] {P : ℕ} (hP : P ≠ 0) {n : ℕ} (hn : n ∣ P)
    {f : ℕ → α} : ∑ d ∈ n.divisors, f d = ∑ d ∈ P.divisors, if d ∣ n then f d else 0 :=
  by
  rw [←Finset.sum_filter, Nat.divisors_filter_dvd_of_dvd hP hn]

theorem sum_intro {α M : Type _} [AddCommMonoid M] [DecidableEq α] (s : Finset α)
    {f : α → M} (d : α)
     (hd : d ∈ s) :
    f d = ∑ k ∈ s, if k = d then f k else 0 := by
  trans (∑ k ∈ s, if k = d then f d else 0)
  · rw [sum_eq_single_of_mem d hd]
    · rw [if_pos rfl]
    · intro _ _ h
      rw [if_neg h]
  apply sum_congr rfl; intro k _; apply if_ctx_congr Iff.rfl _ (fun _ => rfl)
  intro h; rw [h]

theorem ite_sum_zero {p : Prop} [Decidable p] (s : Finset ℕ) (f : ℕ → ℝ) :
    (if p then (∑ x ∈ s, f x) else 0) = ∑ x ∈ s, if p then f x else 0 := by
  split_ifs <;> simp

theorem conv_lambda_sq_larger_sum (f : ℕ → ℕ → ℕ → ℝ) (n : ℕ) :
    (∑ d ∈ n.divisors,
        ∑ d1 ∈ d.divisors,
          ∑ d2 ∈ d.divisors, if d = Nat.lcm d1 d2 then f d1 d2 d else 0) =
      ∑ d ∈ n.divisors,
        ∑ d1 ∈ n.divisors,
          ∑ d2 ∈ n.divisors, if d = Nat.lcm d1 d2 then f d1 d2 d else 0 := by
  apply sum_congr rfl; intro d hd
  rw [mem_divisors] at hd
  simp_rw [←Nat.divisors_filter_dvd_of_dvd hd.2 hd.1, sum_filter, ←ite_and, ite_sum_zero, ←ite_and]
  congr with d1
  congr with d2
  congr
  rw [eq_iff_iff]
  refine ⟨fun ⟨_, _, h⟩ ↦ h, ?_⟩
  rintro rfl
  exact ⟨Nat.dvd_lcm_left d1 d2, Nat.dvd_lcm_right d1 d2, rfl⟩

-- theorem dvd_iff_mul_of_dvds {P : ℕ} (k d l m : ℕ) (hd : d ∈ P.divisors) :
--     k = d / l ∧ l ∣ d ∧ d ∣ m ↔ d = k * l ∧ d ∣ m := by
--   constructor
--   · intro ⟨hk_eq, hld, hdm⟩
--     exact ⟨Nat.eq_mul_of_div_eq_left hld hk_eq.symm, hdm⟩
--   · intro ⟨hd_eq, hdm⟩
--     refine ⟨?_, ?_, hdm⟩
--     · apply (Nat.div_eq_of_eq_mul_left _ hd_eq).symm
--       apply Nat.pos_of_ne_zero
--       apply right_ne_zero_of_mul (a:=k)
--       rw [←hd_eq]
--       apply _root_.ne_of_gt
--       apply Nat.pos_of_mem_divisors hd
--     · use k; rw [hd_eq, mul_comm]

theorem moebius_inv_dvd_lower_bound (l m : ℕ) (hm : Squarefree m) :
    (∑ d ∈ m.divisors, if l ∣ d then (μ d:ℤ) else 0) = if l = m then (μ l:ℤ) else 0 := by
  have hm_pos : 0 < m := Nat.pos_of_ne_zero <| Squarefree.ne_zero hm
  revert hm
  revert m
  apply (ArithmeticFunction.sum_eq_iff_sum_smul_moebius_eq_on {n | Squarefree n}
    (fun _ _ => Squarefree.squarefree_of_dvd)).mpr
  intro m hm_pos hm
  rw [sum_divisorsAntidiagonal' (f:= fun x y => μ x • if l=y then μ l else 0)]--
  by_cases hl : l ∣ m
  · rw [if_pos hl, sum_eq_single l]
    · have hmul : m / l * l = m := Nat.div_mul_cancel hl
      rw [if_pos rfl, smul_eq_mul, ←isMultiplicative_moebius.map_mul_of_coprime, hmul]
      apply coprime_of_squarefree_mul; rw [hmul]; exact hm
    · intro d _ hdl; rw[if_neg <| hdl.symm, smul_zero]
    · intro h; rw[mem_divisors] at h; exfalso; exact h ⟨hl, (Nat.ne_of_lt hm_pos).symm⟩
  · rw [if_neg hl, sum_eq_zero]; intro d hd
    rw [if_neg, smul_zero]
    by_contra h; rw [←h] at hd; exact hl (dvd_of_mem_divisors hd)

theorem moebius_inv_dvd_lower_bound' {P : ℕ} (hP : Squarefree P) (l m : ℕ)
    (hm : m ∣ P) :
    (∑ d ∈ P.divisors, if l ∣ d ∧ d ∣ m then μ d else 0) = if l = m then μ l else 0 := by
  rw [←moebius_inv_dvd_lower_bound _ _ (Squarefree.squarefree_of_dvd hm hP),
    sum_over_dvd_ite hP.ne_zero hm]
  simp_rw[ite_and, ←sum_filter, filter_comm]

theorem moebius_inv_dvd_lower_bound_real {P : ℕ} (hP : Squarefree P) (l m : ℕ)
    (hm : m ∣ P) :
    (∑ d ∈ P.divisors, if l ∣ d ∧ d ∣ m then (μ d : ℝ) else 0) =
      if l = m then (μ l : ℝ) else 0 := by
  norm_cast
  apply moebius_inv_dvd_lower_bound' hP l m hm

theorem gcd_dvd_mul (m n : ℕ) : m.gcd n ∣ m * n := by
  calc
    m.gcd n ∣ m := Nat.gcd_dvd_left m n
    _ ∣ m * n := ⟨n, rfl⟩

theorem multiplicative_zero_of_zero_dvd (f : ArithmeticFunction ℝ)
    (h_mult : IsMultiplicative f) {m n : ℕ}
    (h_sq : Squarefree n) (hmn : m ∣ n) (h_zero : f m = 0) : f n = 0 := by
  rcases hmn with ⟨k, rfl⟩
  simp only [MulZeroClass.zero_mul, h_mult.map_mul_of_coprime
    (coprime_of_squarefree_mul h_sq), h_zero]

theorem primeDivisors_nonempty (n : ℕ) (hn : 2 ≤ n) : n.primeFactors.Nonempty := by
  unfold Finset.Nonempty
  simp_rw[Nat.mem_primeFactors_of_ne_zero (by positivity)]
  apply Nat.exists_prime_and_dvd (by linarith)

theorem div_mult_of_dvd_squarefree (f : ArithmeticFunction ℝ) (h_mult : IsMultiplicative f)
    (l d : ℕ) (hdl : d ∣ l)
    (hl : Squarefree l) (hd : f d ≠ 0) : f l / f d = f (l / d) := by
  apply div_eq_of_eq_mul hd
  rw [← h_mult.right, Nat.div_mul_cancel hdl]
  apply coprime_of_squarefree_mul
  convert hl
  exact Nat.div_mul_cancel hdl

theorem inv_sub_antitoneOn_gt {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    (c : R) :
    AntitoneOn (fun x : R ↦ (x-c)⁻¹) (Set.Ioi c) := by
  refine antitoneOn_iff_forall_lt.mpr ?_
  intro a ha b hb hab
  rw [Set.mem_Ioi] at ha hb
  gcongr

theorem inv_sub_antitoneOn_Icc {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    (a b c : R) (ha : c < a) :
    AntitoneOn (fun x ↦ (x-c)⁻¹) (Set.Icc a b) := by
  by_cases hab : a ≤ b
  · exact inv_sub_antitoneOn_gt c |>.mono <| (Set.Icc_subset_Ioi_iff hab).mpr ha
  · simp [hab, Set.Subsingleton.antitoneOn]

theorem inv_antitoneOn_pos {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] :
    AntitoneOn (fun x:R ↦ x⁻¹) (Set.Ioi 0) := by
  convert inv_sub_antitoneOn_gt (R:=R) 0; ring

theorem inv_antitoneOn_Icc {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    (a b : R) (ha : 0 < a) :
    AntitoneOn (fun x ↦ x⁻¹) (Set.Icc a b) := by
  convert inv_sub_antitoneOn_Icc a b 0 ha; ring

theorem log_add_one_le_sum_inv (n : ℕ) :
    Real.log ↑(n+1) ≤ ∑ d ∈ Finset.Icc 1 n, (d:ℝ)⁻¹ := by
  calc _ = ∫ x in (1)..↑(n+1), x⁻¹ := ?_
       _ = ∫ x in (1:ℕ)..↑(n+1), x⁻¹ := ?_
       _ ≤ _ := ?_
  · rw[integral_inv (by simp[(show ¬ (1:ℝ) ≤ 0 by norm_num)] )]; congr; ring
  · congr; norm_num
  · apply AntitoneOn.integral_le_sum_Ico (by norm_num)
    apply inv_antitoneOn_Icc
    norm_num

theorem log_le_sum_inv (y : ℝ) (hy : 1 ≤ y) :
    Real.log y ≤ ∑ d ∈ Finset.Icc 1 (⌊y⌋₊), (d:ℝ)⁻¹ := by
  calc _ ≤ Real.log ↑(Nat.floor y + 1) := ?_
       _ ≤ _ := ?_
  · gcongr
    apply (le_ceil y).trans
    norm_cast
    exact ceil_le_floor_add_one y
  · apply log_add_one_le_sum_inv

theorem sum_inv_le_log (n : ℕ) (hn : 1 ≤ n) :
    ∑ d ∈ Finset.Icc 1 n, (d : ℝ)⁻¹ ≤ 1 + Real.log ↑n :=
  by
  rw [← Finset.sum_erase_add (Icc 1 n) _ (by simp [hn] : 1 ∈ Icc 1 n), add_comm]
  gcongr
  · norm_num
  simp only [Icc_erase_left]
  calc
    ∑ d ∈ Ico 2 (n + 1), (d : ℝ)⁻¹ = ∑ d ∈ Ico 2 (n + 1), (↑(d + 1) - 1)⁻¹ := ?_
    _ ≤ ∫ x in (2).. ↑(n + 1), (x - 1)⁻¹  := ?_
    _ = Real.log ↑n := ?_
  · congr; norm_num;
  · apply @AntitoneOn.sum_le_integral_Ico 2 (n + 1) fun x : ℝ => (x - 1)⁻¹
    · linarith [hn]
    apply inv_sub_antitoneOn_Icc; norm_num
  rw [intervalIntegral.integral_comp_sub_right _ 1, integral_inv]
  · norm_num
  norm_num; simp[hn, show (0:ℝ) < 1 by norm_num]

theorem sum_inv_le_log_real (y : ℝ) (hy : 1 ≤ y) :
    ∑ d ∈ Finset.Icc 1 (⌊y⌋₊), (d:ℝ)⁻¹ ≤ 1 + Real.log y := by
  trans (1 + Real.log (⌊y⌋₊))
  · apply sum_inv_le_log (⌊y⌋₊)
    apply le_floor; norm_cast
  gcongr
  · norm_cast; apply Nat.lt_of_succ_le; apply le_floor; norm_cast
  · apply floor_le; linarith

theorem natLe_prod {f : ι → ℕ} {s : Finset ι} {i : ι} (hi : i ∈ s)
    (hf : ∀ i ∈ s, f i ≠ 0) :
    f i ≤ ∏ j ∈ s, f j := by
  classical
  rw [←prod_erase_mul (a:=i) (h:= hi)]
  exact Nat.le_mul_of_pos_left _ <|
    prod_pos fun j hj => Nat.pos_of_ne_zero (hf j (mem_of_mem_erase hj))


-- Lemma 3.1 in Heath-Brown's notes
theorem sum_pow_cardDistinctFactors_div_self_le_log_pow {P k : ℕ} (x : ℝ) (hx : 1 ≤ x)
    (hP : Squarefree P) :
    (∑ d ∈ P.divisors, if d ≤ x then (k:ℝ) ^ (ω d) / (d : ℝ) else (0 : ℝ))
    ≤ (1 + Real.log x) ^ k := by
  have hx_pos : 0 < x := by
    linarith
  calc
    _ = ∑ d ∈ P.divisors,
          ∑ a ∈ Fintype.piFinset fun _i : Fin k => P.divisors,
            if ∏ i, a i = d ∧ d ∣ P then if ↑d ≤ x then (d : ℝ)⁻¹ else 0 else 0 := ?_
    _ = ∑ a ∈ Fintype.piFinset fun _i : Fin k => P.divisors,
          if ∏ i, a i ∣ P then if ↑(∏ i, a i) ≤ x then ∏ i, (a i : ℝ)⁻¹ else 0 else 0 := ?_
    _ ≤ ∑ a ∈ Fintype.piFinset fun _i : Fin k => P.divisors,
          if ↑(∏ i, a i) ≤ x then ∏ i, (a i : ℝ)⁻¹ else 0 := ?_ -- do we need this one?
    _ ≤ ∑ a ∈ Fintype.piFinset fun _i : Fin k => P.divisors,
          ∏ i, if ↑(a i) ≤ x then (a i : ℝ)⁻¹ else 0 := ?_
    _ = ∏ _i : Fin k, ∑ d ∈ P.divisors, if ↑d ≤ x then (d : ℝ)⁻¹ else 0 := by rw [prod_univ_sum]
    _ = (∑ d ∈ P.divisors, if ↑d ≤ x then (d : ℝ)⁻¹ else 0) ^ k := by
      rw [prod_const, Finset.card_fin]
    _ ≤ (1 + Real.log x) ^ k := ?_
  · apply sum_congr rfl; intro d hd
    rw [mem_divisors] at hd
    simp_rw [ite_and];
    rw [←sum_filter, Finset.sum_const, ←finMulAntidiagonal_univ_eq hd.1 hd.2,
      card_finMulAntidiagonal <| hP.squarefree_of_dvd hd.1, if_pos hd.1]
    simp only [div_eq_mul_inv, nsmul_eq_mul, cast_pow, mul_ite, mul_zero]
  · rw [sum_comm]; apply sum_congr rfl; intro a _; rw [sum_eq_single (∏ i, a i)]
    · apply if_ctx_congr _ _ (fun _ => rfl)
      · rw [Iff.comm, iff_and_self]
        exact fun _ => rfl
      intro; rw [cast_prod, ← prod_inv_distrib]
    · exact fun d _ hd_ne ↦ if_neg fun h => hd_ne.symm h.1
    · exact fun h ↦ if_neg fun h' => h (mem_divisors.mpr ⟨h'.2, hP.ne_zero⟩)
  · apply sum_le_sum; intro a _
    by_cases h : (∏ i, a i ∣ P)
    · rw [if_pos h]
    rw [if_neg h]
    split_ifs with h'
    · apply prod_nonneg; intro i _; norm_num
    · rfl
  · apply sum_le_sum; intro a ha
    split_ifs with h
    · apply le_of_eq
      apply prod_congr rfl
      intro i hi
      have hai_le_x : ↑(a i) ≤ x := by
        refine le_trans ?_ h
        norm_cast
        rw [←prod_erase_mul (a:=i) (h:= hi)]
        apply Nat.le_mul_of_pos_left
        rw [Fintype.mem_piFinset] at ha
        apply prod_pos
        intro j hj
        apply pos_of_mem_divisors (ha j)
      rw [if_pos hai_le_x]
    · apply prod_nonneg; intro j _
      split_ifs
      · norm_num
      · rfl
  · rw [←sum_filter]
    gcongr
    trans (∑ d ∈ Icc 1 (floor x), (d:ℝ)⁻¹)
    · apply sum_le_sum_of_subset_of_nonneg
      · intro d
        rw[mem_filter, mem_Icc]
        intro hd
        constructor
        · rw [Nat.succ_le_iff]
          exact pos_of_mem_divisors hd.1
        · rw [le_floor_iff]
          · exact hd.2
          · exact le_of_lt hx_pos
      · norm_num
    apply sum_inv_le_log_real
    linarith

theorem sum_pow_cardDistinctFactors_le_self_mul_log_pow {P h : ℕ} (x : ℝ) (hx : 1 ≤ x)
    (hP : Squarefree P) :
    (∑ d ∈ P.divisors, if ↑d ≤ x then (h : ℝ) ^ ω d else (0 : ℝ)) ≤ x * (1 + Real.log x) ^ h := by
  trans (∑ d ∈ P.divisors, x * if ↑d ≤ x then (h : ℝ) ^ ω d / d else (0 : ℝ))
  · simp_rw [mul_ite, mul_zero, ←sum_filter]
    gcongr with i hi
    rw [div_eq_mul_inv, mul_comm _ (i:ℝ)⁻¹, ←mul_assoc]
    trans (1*(h:ℝ)^ω i)
    · rw [one_mul]
    gcongr
    rw [mem_filter] at hi
    rw [←div_eq_mul_inv]
    apply one_le_div (by norm_cast; apply Nat.pos_of_mem_divisors hi.1) |>.mpr hi.2
  rw [←mul_sum];
  gcongr
  apply sum_pow_cardDistinctFactors_div_self_le_log_pow x hx hP


end Aux

end -- close `noncomputable section` opened in AuxResults



-- === Inlined from SelbergSieve4.UpperBoundSieve ===
/-
Copyright (c) 2026 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arend Mellendijk
-/

/-!
# LeanPool.SelbergSieve4.UpperBoundSieve
-/

section LPSieveUpperBound
open scoped BigOperators ArithmeticFunction.zeta ArithmeticFunction.Moebius ArithmeticFunction.omega

namespace LPSieve

/-- A real-valued divisor weight majorizing the delta function at `1`. -/
def UpperMoebius (μ_plus : ℕ → ℝ) : Prop :=
  ∀ n : ℕ, (if n=1 then 1 else 0) ≤ ∑ d ∈ n.divisors, μ_plus d

/-- Upper-bound sieve weights with their majorization property. -/
structure UpperBoundSieve where mk ::
  /-- Upper-bound Moebius weight. -/
  μPlus : ℕ → ℝ
  hμPlus : UpperMoebius μPlus

instance ubToμPlus : CoeFun UpperBoundSieve fun _ => ℕ → ℝ where coe ub := ub.μPlus

/-- A real-valued divisor weight minorizing the delta function at `1`. -/
def LowerMoebius (μMinus : ℕ → ℝ) : Prop :=
  ∀ n : ℕ, ∑ d ∈ n.divisors, μMinus d ≤ (if n=1 then 1 else 0)

/-- Lower-bound sieve weights with their minorization property. -/
structure LowerBoundSieve where mk ::
  /-- Lower-bound Moebius weight. -/
  μMinus : ℕ → ℝ
  hμMinus : LowerMoebius μMinus

instance lbToμMinus : CoeFun LowerBoundSieve fun _ => ℕ → ℝ where coe lb := lb.μMinus

end LPSieve

end LPSieveUpperBound



-- === Inlined from SelbergSieve4.SieveLemmas ===
/-
Copyright (c) 2026 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arend Mellendijk
-/

/-!
# LeanPool.SelbergSieve4.SieveLemmas
-/

noncomputable section

open scoped BigOperators ArithmeticFunction.zeta ArithmeticFunction.Moebius ArithmeticFunction.omega

open Finset Real Nat Aux

local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y)

/-- Data for a finite weighted sieve problem. -/
structure LPSieve where mk ::
  /-- Finite support of integers being sifted. -/
  support : Finset ℕ
  /-- Product of the primes used by the sieve. -/
  prodPrimes : ℕ
  prodPrimes_squarefree : Squarefree prodPrimes
  /-- Nonnegative weights on the support. -/
  weights : ℕ → ℝ
  weights_nonneg : ∀ n : ℕ, 0 ≤ weights n
  /-- Main term for the weighted support. -/
  totalMass : ℝ
  /-- Local density arithmetic function. -/
  nu : ArithmeticFunction ℝ
  nu_mult : nu.IsMultiplicative
  nu_pos_of_prime : ∀ p : ℕ, p.Prime → p ∣ prodPrimes → 0 < nu p
  nu_lt_one_of_prime : ∀ p : ℕ, p.Prime → p ∣ prodPrimes → nu p < 1

attribute [arith_mult] LPSieve.nu_mult

namespace LPSieve

variable (s : LPSieve)
local notation3 "ν" => LPSieve.nu s
local notation3 "P" => LPSieve.prodPrimes s
local notation3 "a" => LPSieve.weights s
local notation3 "X" => LPSieve.totalMass s
local notation3 "A" => LPSieve.support s

/-- Weighted count of support elements divisible by `d`. -/
@[simp]
def multSum (d : ℕ) : ℝ :=
  ∑ n ∈ A, if d ∣ n then a n else 0

local notation3 "𝒜" => LPSieve.multSum s

-- A_d = ν (d)/d X + R_d
/-- Remainder term after subtracting the expected main term from `multSum`. -/
@[simp]
def rem (d : ℕ) : ℝ :=
  𝒜 d - ν d * X

local notation3 "R" => LPSieve.rem s

/-- Weighted count of support elements coprime to the sieve modulus. -/
def siftedSum : ℝ :=
  ∑ d ∈ A, if Coprime P d then a d else 0

open scoped ArithmeticFunction
/-- Selberg local factor product used in the simple upper-bound sieve. -/
def selbergTerms : ArithmeticFunction ℝ :=
  s.nu.pmul (.prodPrimeFactors fun p =>  1 / (1 - ν p))

local notation3 "g" => LPSieve.selbergTerms s

/-- Expands `selbergTerms` as a product over the prime factors of `d`. -/
theorem selbergTerms_apply (d : ℕ) :
    g d = ν d * ∏ p ∈ d.primeFactors, 1/(1 - ν p) := by
  unfold selbergTerms
  by_cases h : d=0
  · rw [h]; simp
  rw [ArithmeticFunction.pmul_apply, ArithmeticFunction.prodPrimeFactors_apply h]


/-- Main contribution of an upper-bound sieve weight. -/
def mainSum (μPlus : ℕ → ℝ) : ℝ :=
  ∑ d ∈ divisors P, μPlus d * ν d

/-- Error contribution of an upper-bound sieve weight. -/
def errSum (μPlus : ℕ → ℝ) : ℝ :=
  ∑ d ∈ divisors P, |μPlus d| * |R d|

section SieveLemmas

theorem prodPrimes_ne_zero : P ≠ 0 :=
  Squarefree.ne_zero s.prodPrimes_squarefree

theorem squarefree_of_dvd_prodPrimes {d : ℕ} (hd : d ∣ P) : Squarefree d :=
  Squarefree.squarefree_of_dvd hd s.prodPrimes_squarefree

theorem squarefree_of_mem_divisors_prodPrimes {d : ℕ} (hd : d ∈ divisors P) : Squarefree d := by
  simp only [Nat.mem_divisors] at hd
  exact Squarefree.squarefree_of_dvd hd.left s.prodPrimes_squarefree

theorem nu_pos_of_dvd_prodPrimes {d : ℕ} (hd : d ∣ P) : 0 < ν d := by
  calc
    0 < ∏ p ∈ d.primeFactors, ν p := by
      apply prod_pos
      intro p hpd
      have hp_prime : p.Prime := by exact prime_of_mem_primeFactors hpd
      have hp_dvd : p ∣ P := (dvd_of_mem_primeFactors hpd).trans hd
      exact s.nu_pos_of_prime p hp_prime hp_dvd
    _ = ν d := prod_factors_of_mult ν s.nu_mult
      (Squarefree.squarefree_of_dvd hd s.prodPrimes_squarefree)

theorem nu_ne_zero {d : ℕ} (hd : d ∣ P) : ν d ≠ 0 := by
  apply _root_.ne_of_gt
  exact nu_pos_of_dvd_prodPrimes s hd

theorem nu_ne_zero_of_mem_divisors_prodPrimes {d : ℕ} (hd : d ∈ divisors P) : ν d ≠ 0 := by
  apply _root_.ne_of_gt
  rw [mem_divisors] at hd
  apply s.nu_pos_of_dvd_prodPrimes hd.left

theorem multSum_eq_main_err (d : ℕ) : s.multSum d = ν d * X + R d := by
  dsimp [rem]
  ring

/-- Kronecker delta at `1`, valued in the reals. -/
def delta (n : ℕ) : ℝ := if n=1 then 1 else 0

local notation "δ" => delta

theorem siftedSum_as_delta : s.siftedSum = ∑ d ∈ s.support, a d * δ (Nat.gcd P d) :=
  by
  dsimp only [siftedSum]
  apply sum_congr rfl
  intro d _
  dsimp only [Nat.Coprime, delta] at *
  rw [mul_ite_zero]
  exact if_congr Iff.rfl (symm <| mul_one _) rfl

-- Unused ?
theorem nu_lt_self_of_dvd_prodPrimes : ∀ d : ℕ, d ∣ P → d ≠ 1 → ν d < 1 := by
  intro d hdP hd_ne_one
  have hd_sq : Squarefree d := Squarefree.squarefree_of_dvd hdP s.prodPrimes_squarefree
  calc
    ν d = ∏ p ∈ d.primeFactors, ν p :=
      eq_comm.mp (prod_factors_of_mult ν s.nu_mult hd_sq)
    _ < ∏ p ∈ d.primeFactors, 1 := by
      have hd_ne_zero : d ≠ 0 := by aesopDiv
      apply prod_lt_prod_of_nonempty
      · intro p hp
        simp only [mem_primeFactors] at hp
        apply s.nu_pos_of_prime p (by aesop) (by aesopDiv)
      · intro p hpd; rw [mem_primeFactors_of_ne_zero hd_ne_zero] at hpd
        apply s.nu_lt_one_of_prime p hpd.left (by aesopDiv)
      · apply primeDivisors_nonempty _ <| (two_le_iff d).mpr ⟨hd_ne_zero, hd_ne_one⟩
    _ = 1 := by
      simp

-- Facts about g
@[aesop safe]
theorem selbergTerms_pos (l : ℕ) (hl : l ∣ P) : 0 < g l := by
  rw [selbergTerms_apply]
  apply mul_pos
  · exact s.nu_pos_of_dvd_prodPrimes hl
  · apply prod_pos
    intro p hp
    rw [one_div_pos]
    have hp_prime : p.Prime := prime_of_mem_primeFactors hp
    have hp_dvd : p ∣ P := (Nat.dvd_of_mem_primeFactors hp).trans hl
    linarith only [s.nu_lt_one_of_prime p hp_prime hp_dvd]

theorem selbergTerms_mult : ArithmeticFunction.IsMultiplicative g := by
  unfold selbergTerms
  arith_mult

theorem one_div_selbergTerms_eq_conv_moebius_nu (l : ℕ) (hl : Squarefree l)
    (hnu_nonzero : ν l ≠ 0) : 1 / g l = ∑ d ∈ l.divisors, (μ <| l / d) * (ν d)⁻¹ :=
  by
  rw [selbergTerms_apply]
  simp only [one_div, mul_inv, inv_inv, Finset.prod_inv_distrib]
  rw [(s.nu_mult).prodPrimeFactors_one_sub_of_squarefree _ hl]
  rw [mul_sum]
  apply symm
  rw [← Nat.sum_divisorsAntidiagonal' fun d e : ℕ => ↑(μ d) * (ν e)⁻¹]
  rw [Nat.sum_divisorsAntidiagonal fun d e : ℕ => ↑(μ d) * (ν e)⁻¹]
  apply sum_congr rfl; intro d hd
  have hd_dvd : d ∣ l := dvd_of_mem_divisors hd
  rw [←div_mult_of_dvd_squarefree ν s.nu_mult l d (dvd_of_mem_divisors hd) hl, inv_div]
  · ring
  · revert hnu_nonzero; contrapose!
    exact multiplicative_zero_of_zero_dvd ν s.nu_mult hl hd_dvd

theorem nu_eq_conv_one_div_selbergTerms (d : ℕ) (hdP : d ∣ P) :
    (ν d)⁻¹ = ∑ l ∈ divisors P, if l ∣ d then 1 / g l else 0 := by
  apply symm
  rw [←sum_filter, Nat.divisors_filter_dvd_of_dvd s.prodPrimes_ne_zero hdP]
  have hd_pos : 0 < d :=
    Nat.pos_of_ne_zero <| ne_zero_of_dvd_ne_zero s.prodPrimes_ne_zero hdP
  revert hdP; revert d
  apply (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq_on _ (fun _ _ => Nat.dvd_trans)).mpr
  intro l _ hlP
  rw [sum_divisorsAntidiagonal' (f:=fun x y => (μ <| x) * (ν y)⁻¹) (n:=l)]
  apply symm
  exact s.one_div_selbergTerms_eq_conv_moebius_nu l
    (Squarefree.squarefree_of_dvd hlP s.prodPrimes_squarefree)
    (_root_.ne_of_gt <| s.nu_pos_of_dvd_prodPrimes hlP)

theorem conv_selbergTerms_eq_selbergTerms_mul_nu {d : ℕ} (hd : d ∣ P) :
    (∑ l ∈ divisors P, if l ∣ d then g l else 0) = g d * (ν d)⁻¹ := by
  calc
    (∑ l ∈ divisors P, if l ∣ d then g l else 0) =
        ∑ l ∈ divisors P, if l ∣ d then g (d / l) else 0 := by
      rw [← sum_over_dvd_ite s.prodPrimes_ne_zero hd]
      rw [← Nat.sum_divisorsAntidiagonal fun x _ => g x]
      rw [Nat.sum_divisorsAntidiagonal' fun x _ => g x]
      rw [sum_over_dvd_ite s.prodPrimes_ne_zero hd]
    _ = g d * ∑ l ∈ divisors P, if l ∣ d then 1 / g l else 0 := by
      rw [mul_sum]; apply sum_congr rfl; intro l hl
      rw [mul_ite_zero]
      apply if_ctx_congr Iff.rfl _ (fun _ => rfl)
      intro h
      rw [← div_mult_of_dvd_squarefree g s.selbergTerms_mult d l]
      · ring
      · exact h
      · apply Squarefree.squarefree_of_dvd hd s.prodPrimes_squarefree
      · apply _root_.ne_of_gt
        rw [mem_divisors] at hl
        apply selbergTerms_pos
        exact hl.left
    _ = g d * (ν d)⁻¹ := by rw [← s.nu_eq_conv_one_div_selbergTerms d hd]

theorem upper_bound_of_UpperBoundSieve (μPlus : UpperBoundSieve) :
    s.siftedSum ≤ ∑ d ∈ divisors P, μPlus d * s.multSum d := by
  have hμ : ∀ n, δ n ≤ ∑ d ∈ n.divisors, μPlus d := μPlus.hμPlus
  rw [siftedSum_as_delta]
  trans (∑ n ∈ s.support, a n * ∑ d ∈ (Nat.gcd P n).divisors, μPlus d)
  · apply Finset.sum_le_sum; intro n _
    exact mul_le_mul_of_nonneg_left (hμ (Nat.gcd P n)) (s.weights_nonneg n)
  apply le_of_eq
  trans (∑ n ∈ s.support, ∑ d ∈ divisors P, if d ∣ n then a n * μPlus d else 0)
  · apply sum_congr rfl; intro n _
    rw [mul_sum, sum_over_dvd_ite s.prodPrimes_ne_zero (Nat.gcd_dvd_left _ _),
      sum_congr rfl]; intro d hd
    apply if_congr _ rfl rfl
    rw [Nat.dvd_gcd_iff, and_iff_right (dvd_of_mem_divisors hd)]
  rw [sum_comm, sum_congr rfl]; intro d _
  dsimp only [multSum]
  rw [mul_sum, sum_congr rfl]; intro n _
  rw [←ite_zero_mul, mul_comm]

theorem siftedSum_le_mainSum_errSum_of_UpperBoundSieve (μPlus : UpperBoundSieve) :
    s.siftedSum ≤ X * s.mainSum μPlus + s.errSum μPlus := by
  dsimp only [mainSum, errSum]
  trans (∑ d ∈ divisors P, μPlus d * s.multSum d)
  · apply upper_bound_of_UpperBoundSieve
  trans ( X * ∑ d ∈ divisors P, μPlus d * ν d + ∑ d ∈ divisors P, μPlus d * R d )
  · apply le_of_eq
    rw [mul_sum, ←sum_add_distrib]
    apply sum_congr rfl; intro d _
    dsimp only [rem]; ring
  apply _root_.add_le_add (le_rfl)
  apply sum_le_sum; intro d _
  rw [←abs_mul]
  exact le_abs_self (UpperBoundSieve.μPlus μPlus d * rem s d)

end SieveLemmas

section LambdaSquared

/-- Lambda-squared upper-bound weights generated from a function on divisors. -/
def lambdaSquared (weights : ℕ → ℝ) : ℕ → ℝ := fun d =>
  ∑ d1 ∈ d.divisors, ∑ d2 ∈ d.divisors, if d = Nat.lcm d1 d2 then weights d1 * weights d2 else 0

private theorem lambdaSquared_eq_zero_of_support_wlog {w : ℕ → ℝ} {y : ℝ}
    (hw : ∀ (d : ℕ), ¬↑(d ^ 2) ≤ y → w d = 0)
    {d : ℕ} (hd : ¬↑d ≤ y) (d1 : ℕ) (d2 : ℕ) (h : d = Nat.lcm d1 d2)
    (hle : d1 ≤ d2) :
    w d1 * w d2 = 0 := by
  rw [hw d2]
  · ring
  by_contra hyp
  apply hd
  apply le_trans _ hyp
  norm_cast
  calc _ ≤ (d1.lcm d2) := by rw [h]
      _ ≤ (d1*d2) := Nat.div_le_self _ _
      _ ≤ _       := ?_
  · rw [sq]; gcongr
theorem lambdaSquared_eq_zero_of_support (w : ℕ → ℝ) (y : ℝ)
    (hw : ∀ d : ℕ, ¬d ^ 2 ≤ y → w d = 0) (d : ℕ) (hd : ¬d ≤ y) :
    lambdaSquared w d = 0 := by
  dsimp only [lambdaSquared]
  by_cases hy : 0 ≤ y
  swap
  · push Not at hd hy
    have : ∀ d' : ℕ, w d' = 0 := by
      intro d'; apply hw
      have : (0:ℝ) ≤ (d') ^ 2 := by norm_num
      linarith
    apply sum_eq_zero; intro d1 _
    apply sum_eq_zero; intro d2 _
    rw [this d1, this d2]
    simp only [ite_self, MulZeroClass.mul_zero]
  apply sum_eq_zero; intro d1 _; apply sum_eq_zero; intro d2 _
  split_ifs with h
  swap
  · rfl
  rcases Nat.le_or_le d1 d2 with hle | hle
  · apply lambdaSquared_eq_zero_of_support_wlog hw hd d1 d2 h hle
  · rw[mul_comm]
    apply lambdaSquared_eq_zero_of_support_wlog hw hd d2 d1 (Nat.lcm_comm d1 d2 ▸ h) hle

theorem upperMoebius_of_lambda_sq (weights : ℕ → ℝ) (hw : weights 1 = 1) :
    UpperMoebius <| lambdaSquared weights := by
  dsimp [UpperMoebius, lambdaSquared]
  intro n
  have h_sq :
    (∑ d ∈ n.divisors, ∑ d1 ∈ d.divisors, ∑ d2 ∈ d.divisors,
      if d = Nat.lcm d1 d2 then weights d1 * weights d2 else 0) =
      (∑ d ∈ n.divisors, weights d) ^ 2 := by
    rw [sq, mul_sum, conv_lambda_sq_larger_sum _ n, sum_comm]
    apply sum_congr rfl; intro d1 hd1
    rw [sum_mul, sum_comm]
    apply sum_congr rfl; intro d2 hd2
    rw [←Aux.sum_intro]
    · ring
    · rw [mem_divisors, Nat.lcm_dvd_iff]
      exact ⟨⟨dvd_of_mem_divisors hd1, dvd_of_mem_divisors hd2⟩, (mem_divisors.mp hd1).2⟩
  rw [h_sq]
  split_ifs with hn
  · rw [hn]; simp [hw]
  · apply sq_nonneg

-- local notation3 "ν" => LPSieve.nu s
-- local notation3 "P" => LPSieve.prodPrimes s
-- local notation3 "a" => LPSieve.weights s
-- local notation3 "X" => LPSieve.totalMass s
-- local notation3 "R" => LPSieve.rem s
-- local notation3 "g" => LPSieve.selbergTerms s

theorem lambdaSquared_mainSum_eq_quad_form (w : ℕ → ℝ) :
    s.mainSum (lambdaSquared w) =
      ∑ d1 ∈ divisors P, ∑ d2 ∈ divisors P,
        ν d1 * w d1 * ν d2 * w d2 * (ν (d1.gcd d2))⁻¹ := by
  dsimp only [mainSum, lambdaSquared]
  trans (∑ d ∈ divisors P, ∑ d1 ∈ divisors d, ∑ d2 ∈ divisors d,
          if d = d1.lcm d2 then w d1 * w d2 * ν d else 0)
  · rw [sum_congr rfl]; intro d _
    rw [sum_mul, sum_congr rfl]; intro d1 _
    rw [sum_mul, sum_congr rfl]; intro d2 _
    rw [ite_zero_mul]
  trans (∑ d ∈ divisors P, ∑ d1 ∈ divisors P, ∑ d2 ∈ divisors P,
          if d = d1.lcm d2 then w d1 * w d2 * ν d else 0)
  · apply conv_lambda_sq_larger_sum
  rw [sum_comm, sum_congr rfl]; intro d1 hd1
  rw [sum_comm, sum_congr rfl]; intro d2 hd2
  have h : d1.lcm d2 ∣ P := Nat.lcm_dvd_iff.mpr ⟨dvd_of_mem_divisors hd1, dvd_of_mem_divisors hd2⟩
  rw [←sum_intro (divisors P) (d1.lcm d2) (mem_divisors.mpr ⟨h, s.prodPrimes_ne_zero⟩ )]
  rw [mult_lcm_eq_of_ne_zero ν s.nu_mult _ _ _]
  · ring
  · refine _root_.ne_of_gt (s.nu_pos_of_dvd_prodPrimes ?_)
    trans d1
    · exact Nat.gcd_dvd_left d1 d2
    · exact dvd_of_mem_divisors hd1

theorem lambdaSquared_mainSum_eq_diag_quad_form (w : ℕ → ℝ) :
    s.mainSum (lambdaSquared w) =
      ∑ l ∈ divisors P,
        1 / g l * (∑ d ∈ divisors P, if l ∣ d then ν d * w d else 0) ^ 2 :=
  by
  rw [s.lambdaSquared_mainSum_eq_quad_form w]
  trans (∑ d1 ∈ divisors P, ∑ d2 ∈ divisors P, (∑ l ∈ divisors P,
          if l ∣ d1.gcd d2 then 1 / g l * (ν d1 * w d1) * (ν d2 * w d2) else 0))
  · apply sum_congr rfl; intro d1 hd1; apply sum_congr rfl; intro d2 _
    have hgcd_dvd: d1.gcd d2 ∣ P := Trans.trans (Nat.gcd_dvd_left d1 d2) (dvd_of_mem_divisors hd1)
    rw [s.nu_eq_conv_one_div_selbergTerms _ hgcd_dvd, mul_sum]
    apply sum_congr rfl; intro l _
    rw [mul_ite_zero]; apply if_congr Iff.rfl _ rfl
    ring
  trans (∑ l ∈ divisors P, ∑ d1 ∈ divisors P, ∑ d2 ∈ divisors P,
        if l ∣ Nat.gcd d1 d2 then 1 / selbergTerms s l * (ν d1 * w d1) * (ν d2 * w d2) else 0)
  · apply symm; rw [sum_comm, sum_congr rfl]; intro d1 _; rw[sum_comm];
  apply sum_congr rfl; intro l _
  rw [sq, sum_mul, mul_sum, sum_congr rfl]; intro d1 _
  rw [mul_sum, mul_sum, sum_congr rfl]; intro d2 _
  rw [ite_zero_mul_ite_zero, mul_ite_zero]
  apply if_congr (Nat.dvd_gcd_iff) _ rfl;
  ring

end LambdaSquared

end LPSieve

end -- close `noncomputable section` opened in SieveLemmas



-- === Inlined from SelbergSieve4.Selberg ===
/-
Copyright (c) 2026 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arend Mellendijk
-/

/-!
# LeanPool.SelbergSieve4.Selberg
-/

noncomputable section

open scoped BigOperators LPSieve ArithmeticFunction.Moebius ArithmeticFunction.omega

open Finset Real Nat LPSieve.UpperBoundSieve ArithmeticFunction LPSieve

local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y)

/-- A Selberg sieve is a finite sieve together with a sieve level. -/
structure LPSelbergSieve extends LPSieve where mk ::
  /-- LPSieve level. -/
  level : ℝ
  one_le_level : 1 ≤ level

namespace LPSelbergSieve

variable (s : LPSelbergSieve)
local notation3 "ν" => LPSieve.nu (toLPSieve s)
local notation3 "P" => LPSieve.prodPrimes (toLPSieve s)
local notation3 "a" => LPSieve.weights (toLPSieve s)
local notation3 "X" => LPSieve.totalMass (toLPSieve s)
local notation3 "R" => LPSieve.rem (toLPSieve s)  -- this one seems broken
local notation3 "g" => LPSieve.selbergTerms (toLPSieve s)
local notation3 "y" => LPSelbergSieve.level s
local notation3 "hy" => LPSelbergSieve.one_le_level s

/-- Selberg bounding sum over divisors below the square-root level. -/
def selbergBoundingSum : ℝ :=
  ∑ l ∈ divisors P, if l ^ 2 ≤ y then g l else 0
local notation3 "S" => LPSelbergSieve.selbergBoundingSum s

@[aesop safe]
theorem selbergBoundingSum_pos :
    0 < S := by
  dsimp only [selbergBoundingSum]
  rw [← sum_filter]
  apply sum_pos;
  · intro l hl
    rw [mem_filter, mem_divisors] at hl
    · apply s.selbergTerms_pos _ (hl.1.1)
  · simp_rw [Finset.Nonempty, mem_filter]; use 1
    constructor
    · apply one_mem_divisors.mpr s.prodPrimes_ne_zero
    rw [one_pow, cast_one]
    exact s.one_le_level

theorem selbergBoundingSum_ne_zero : S ≠ 0 := by
  apply _root_.ne_of_gt
  exact s.selbergBoundingSum_pos

theorem selbergBoundingSum_nonneg : 0 ≤ S := _root_.le_of_lt s.selbergBoundingSum_pos

/-- Selberg weights attached to the sieve. -/
def selbergWeights : ℕ → ℝ := fun d =>
  if d ∣ P then
    (ν d)⁻¹ * g d * μ d * S⁻¹ *
      ∑ m ∈ divisors P, if (d * m) ^ 2 ≤ y ∧ m.Coprime d then g m else 0
  else 0

-- This notation traditionally uses λ, which is unavailable in lean
local notation3 "γ" => LPSelbergSieve.selbergWeights s

theorem selbergWeights_eq_zero_of_not_dvd {d : ℕ} (hd : ¬ d ∣ P) :
    γ d = 0 := by
  rw [selbergWeights, if_neg hd]

theorem selbergWeights_eq_zero (d : ℕ) (hd : ¬d ^ 2 ≤ y) :
    γ d = 0 := by
  dsimp only [selbergWeights]
  split_ifs with h
  · rw [mul_eq_zero_of_right _]
    apply Finset.sum_eq_zero
    refine fun m hm => if_neg ?_
    intro hyp
    have : (d^2:ℝ) ≤ (d*m)^2 := by
      norm_cast;
      refine Nat.pow_le_pow_left ?h 2
      exact Nat.le_mul_of_pos_right _ (Nat.pos_of_mem_divisors hm)
    linarith [hyp.1]
  · rfl

@[aesop safe]
theorem selbergWeights_mul_mu_nonneg (d : ℕ) (hdP : d ∣ P) :
    0 ≤ γ d * μ d :=
  by
  have := s.selbergBoundingSum_nonneg
  dsimp only [selbergWeights]
  rw [if_pos hdP]; rw [mul_assoc]
  trans ((μ d :ℝ)^2 * (ν d)⁻¹ * g d * S⁻¹ * ∑ m ∈ divisors P,
          if (d * m) ^ 2 ≤ y ∧ Coprime m d then g m else 0)
  swap
  · apply le_of_eq
    ring
  apply mul_nonneg
  · apply div_nonneg
    · apply mul_nonneg
      · apply mul_nonneg
        · apply sq_nonneg
        · rw [inv_nonneg]
          exact le_of_lt <| s.nu_pos_of_dvd_prodPrimes hdP
      · exact le_of_lt <| s.selbergTerms_pos d hdP
    · exact s.selbergBoundingSum_nonneg
  · apply sum_nonneg; intro m hm
    split_ifs with h
    · exact le_of_lt <| s.selbergTerms_pos m (dvd_of_mem_divisors hm)
    · rfl

lemma sum_mul_subst (k n : ℕ) {f : ℕ → ℝ} (h : ∀ l, l ∣ n → ¬ k ∣ l → f l = 0) :
      ∑ l ∈ n.divisors, f l
    = ∑ m ∈ n.divisors, if k*m ∣ n then f (k*m) else 0 := by
  by_cases hn: n = 0
  · simp [hn]
  by_cases hkn : k ∣ n
  swap
  · rw [sum_eq_zero, sum_eq_zero]
    · rintro m _
      rw [if_neg]
      rintro h
      apply hkn
      exact (Nat.dvd_mul_right k m).trans h
    · intro l hl; apply h l (dvd_of_mem_divisors hl)
      apply fun hkl => hkn <| hkl.trans (dvd_of_mem_divisors hl)
  trans (∑ l ∈ n.divisors, ∑ m ∈ n.divisors, if l=k*m then f l else 0)
  · rw [sum_congr rfl]; intro l hl
    by_cases hkl : k ∣ l
    swap
    · rw [h l (dvd_of_mem_divisors hl) hkl, sum_eq_zero]
      intro m _
      rw [ite_id]
    rw [sum_eq_single (l/k)]
    · rw[if_pos]; rw [Nat.mul_div_cancel' hkl]
    · intro m hmn hmlk
      apply if_neg; revert hmlk; contrapose!; intro hlkm
      rw [hlkm, mul_comm, Nat.mul_div_cancel]
      aesopDiv
    · contrapose!; intro _
      rw [mem_divisors]
      exact ⟨Trans.trans (Nat.div_dvd_of_dvd hkl) (dvd_of_mem_divisors hl), hn⟩
  · rw [sum_comm, sum_congr rfl]; intro m _
    split_ifs with hdvd
    · rw [←Aux.sum_intro]
      aesopDiv
    · apply sum_eq_zero; intro l hl
      apply if_neg;
      aesopDiv

--Important facts about the selberg weights
theorem selbergWeights_eq_dvds_sum (d : ℕ) :
    ν d * γ d =
      S⁻¹ * μ d *
        ∑ l ∈ divisors P, if d ∣ l ∧ l ^ 2 ≤ y then g l else 0 := by
  by_cases h_dvd : d ∣ P
  swap
  · dsimp only [selbergWeights]; rw [if_neg h_dvd]
    rw [sum_eq_zero]
    · ring
    · intro l hl; rw [mem_divisors] at hl
      rw [if_neg]; push Not; intro h
      exfalso; exact h_dvd (dvd_trans h hl.left)
  dsimp only [selbergWeights]
  rw [if_pos h_dvd]
  repeat rw [mul_sum]
  -- change of variables l=m*d
  apply symm
  rw [sum_mul_subst d P]
  · apply sum_congr rfl
    intro m hm
    rw [mul_ite_zero, ←ite_and, mul_ite_zero, mul_ite_zero]
    apply if_ctx_congr _ _ fun _ => rfl
    · rw [coprime_comm]
      constructor
      · intro h
        exact ⟨h.2.2,
          coprime_of_squarefree_mul <| Squarefree.squarefree_of_dvd h.1 s.prodPrimes_squarefree⟩
      · intro h
        exact ⟨Coprime.mul_dvd_of_dvd_of_dvd h.2 h_dvd (dvd_of_mem_divisors hm),
          Nat.dvd_mul_right d m, h.1⟩
    · intro h
      trans ((ν d)⁻¹ * (ν d) * g d * μ d / S * g m)
      · rw [inv_mul_cancel₀ (s.nu_ne_zero h_dvd), s.selbergTerms_mult.map_mul_of_coprime
          <| coprime_comm.mp h.2]
        ring
      ring
  · intro l _ hdl
    rw [if_neg, mul_zero]
    push Not; intro h; contradiction

theorem selbergWeights_diagonalisation (l : ℕ) (hl : l ∈ divisors P) :
    (∑ d ∈ divisors P, if l ∣ d then ν d * γ d else 0) =
      if l ^ 2 ≤ y then g l * μ l * S⁻¹ else 0 := by
  calc
    (∑ d ∈ divisors P, if l ∣ d then ν d * γ d else 0) =
        ∑ d ∈ divisors P, ∑ k ∈ divisors P,
          if l ∣ d ∧ d ∣ k ∧ k ^ 2 ≤ y then g k * S⁻¹ * (μ d:ℝ) else 0 := by
      apply sum_congr rfl; intro d _
      rw [selbergWeights_eq_dvds_sum, ← boole_mul, mul_sum, mul_sum]
      apply sum_congr rfl; intro k _
      rw [mul_ite_zero, ite_zero_mul_ite_zero]
      apply if_ctx_congr Iff.rfl _ (fun _ => rfl);
      intro _; ring
    _ = ∑ k ∈ divisors P, if k ^ 2 ≤ y then
            (∑ d ∈ divisors P, if l ∣ d ∧ d ∣ k then (μ d:ℝ) else 0) * g k * S⁻¹
          else 0 := by
      rw [sum_comm]; apply sum_congr rfl; intro k _
      apply symm
      rw [← boole_mul, sum_mul, sum_mul, mul_sum, sum_congr rfl]
      intro d _
      rw [ite_zero_mul, ite_zero_mul, ite_zero_mul, one_mul, ←ite_and]
      apply if_ctx_congr _ _ (fun _ => rfl)
      · tauto
      intro _; ring
    _ = if l ^ 2 ≤ y then g l * μ l * S⁻¹ else 0 := by
      rw [Aux.sum_intro (f:=fun _ => if l^2 ≤ y then g l * μ l * S⁻¹ else 0) (divisors P) l hl]
      apply sum_congr rfl; intro k hk
      rw [Aux.moebius_inv_dvd_lower_bound_real s.prodPrimes_squarefree l _ (dvd_of_mem_divisors hk),
        ←ite_and, ite_zero_mul, ite_zero_mul, ← ite_and]
      apply if_ctx_congr _ _ fun _ => rfl
      · rw [and_comm, eq_comm]
        apply and_congr_right
        intro heq
        rw [heq]
      intro h
      rw[h.1]
      ring

/-- Lambda-squared upper-bound weight generated by the Selberg weights. -/
def selbergMuPlus : ℕ → ℝ :=
  LPSieve.lambdaSquared γ
local notation3 "μ⁺" => LPSelbergSieve.selbergMuPlus s

theorem weight_one_of_selberg : γ 1 = 1 := by
  dsimp only [selbergWeights]
  rw [if_pos (one_dvd P), s.nu_mult.left, s.selbergTerms_mult.left]
  -- rw [ArithmeticFunction.moebius_apply_one, Int.cast_one]
  simp only [inv_one, mul_one, isUnit_one, IsUnit.squarefree, moebius_apply_of_squarefree,
    cardFactors_one, _root_.pow_zero, Int.cast_one, selbergBoundingSum, cast_pow, one_mul,
    coprime_one_right_eq_true, and_true]
  have hS : (∑ x ∈ divisors P, if (x : ℝ) ^ 2 ≤ y then g x else 0) ≠ 0 := by
    simpa [selbergBoundingSum, Nat.cast_pow] using s.selbergBoundingSum_ne_zero
  exact inv_mul_cancel₀ hS

theorem selbergμPlus_eq_zero (d : ℕ) (hd : ¬d ≤ y) : μ⁺ d = 0 :=
  by
  apply LPSieve.lambdaSquared_eq_zero_of_support _ y _ d hd
  apply s.selbergWeights_eq_zero

/-- Upper-bound sieve induced by the Selberg weights. -/
def selbergUbSieve : UpperBoundSieve :=
  ⟨μ⁺, LPSieve.upperMoebius_of_lambda_sq γ (s.weight_one_of_selberg)⟩

-- proved for general lambda squared sieves
theorem mainSum_eq_diag_quad_form :
    s.mainSum μ⁺ =
      ∑ l ∈ divisors P,
        1 / g l *
          (∑ d ∈ divisors P, if l ∣ d then ν d * γ d else 0) ^ 2 :=
  by apply lambdaSquared_mainSum_eq_diag_quad_form

theorem selberg_bound_simple_mainSum :
    s.mainSum μ⁺ = S⁻¹ :=
  by
  rw [mainSum_eq_diag_quad_form]
  trans (∑ l ∈ divisors P, (if l ^ 2 ≤ y then g l *  (S⁻¹) ^ 2 else 0))
  · apply sum_congr rfl; intro l hl
    rw [s.selbergWeights_diagonalisation l hl, ite_pow, zero_pow, mul_ite_zero]
    · apply if_congr Iff.rfl _ rfl
      trans (1 / g l * g l * g l * (μ l : ℝ)^2  * (S⁻¹) ^ 2)
      · ring
      norm_cast
      rw [moebius_sq_eq_one_of_squarefree <| s.squarefree_of_mem_divisors_prodPrimes hl]
      rw [one_div_mul_cancel <| _root_.ne_of_gt <| s.selbergTerms_pos l <| dvd_of_mem_divisors hl]
      ring
    · linarith
  conv => {lhs; congr; {skip}; {ext i; rw [← ite_zero_mul]}}
  dsimp only [selbergBoundingSum]
  rw [←sum_mul, sq, ←mul_assoc]
  have hS : (∑ l ∈ divisors P, if ↑(l ^ 2) ≤ y then g l else 0) ≠ 0 := by
    simpa [selbergBoundingSum] using s.selbergBoundingSum_ne_zero
  rw [mul_inv_cancel₀ hS, one_mul]

lemma eq_gcd_mul_of_dvd_of_coprime {k d m : ℕ} (hkd : k ∣ d) (hmd : Coprime m d)
    (hk : k ≠ 0) :
    k = d.gcd (k*m) := by
  rcases hkd with ⟨r, hr⟩
  have hrdvd : r ∣ d := by
    use k
    rw [mul_comm]
    exact hr
  apply symm; rw [hr, Nat.gcd_mul_left, mul_eq_left₀ hk, Nat.gcd_comm]
  apply Coprime.coprime_dvd_right hrdvd hmd

private lemma _helper {k m d : ℕ} (hkd : k ∣ d) (hk : k ∈ divisors P)
    (hm : m ∈ divisors P) :
    k * m ∣ P ∧ k = Nat.gcd d (k * m) ∧ (k * m) ^ 2 ≤ y ↔
    (k * m) ^ 2 ≤ y ∧ Coprime m d := by
  constructor
  · intro h
    constructor
    · exact h.2.2
    · rcases hkd with ⟨r, hr⟩
      rw [hr, Nat.gcd_mul_left, eq_comm, mul_eq_left₀ (by aesopDiv)] at h
      rw [hr, coprime_comm, Nat.coprime_mul_iff_left]
      constructor
      · apply coprime_of_squarefree_mul <| Squarefree.squarefree_of_dvd h.1 s.prodPrimes_squarefree
      · exact h.2.1
  · intro h
    constructor
    · apply Coprime.mul_dvd_of_dvd_of_dvd
      · rw [coprime_comm]; exact Coprime.coprime_dvd_right hkd h.2
      · exact dvd_of_mem_divisors hk
      · exact dvd_of_mem_divisors hm
    constructor
    · exact eq_gcd_mul_of_dvd_of_coprime hkd h.2 (by aesopDiv)
    · exact h.1

theorem selbergBoundingSum_ge {d : ℕ} (hdP : d ∣ P) :
    S ≥ γ d * ↑(μ d) * S := by
  calc
  _ = (∑ k ∈ divisors P, ∑ l ∈ divisors P, if k = d.gcd l ∧ l ^ 2 ≤ y then g l else 0) := by
    dsimp only [selbergBoundingSum]
    rw [sum_comm, sum_congr rfl]; intro l _
    simp_rw [ite_and]
    rw [←Aux.sum_intro]
    · rw [mem_divisors]
      exact ⟨(Nat.gcd_dvd_left d l).trans (hdP), s.prodPrimes_ne_zero⟩
  _ = (∑ k ∈ divisors P,
          if k ∣ d then
            g k * ∑ m ∈ divisors P, if (k * m) ^ 2 ≤ y ∧ m.Coprime d then g m else 0
          else 0) := by
    apply sum_congr rfl; intro k hk
    rw [mul_sum]
    split_ifs with hkd
    swap
    · rw [sum_eq_zero]; intro l _
      rw [if_neg]
      push Not; intro h; exfalso
      rw [h] at hkd
      exact hkd <| Nat.gcd_dvd_left d l
    rw [sum_mul_subst k P]
    · rw [sum_congr rfl]; intro m hm
      rw [mul_ite_zero, ← ite_and]
      apply if_ctx_congr _ _ fun _ => rfl
      · apply s._helper hkd hk hm
      · intro h
        apply s.selbergTerms_mult.2
        rw [coprime_comm]
        apply h.2.coprime_dvd_right hkd
    · intro l _ hkl
      apply if_neg
      push Not; intro h; exfalso
      rw [h] at hkl
      exact hkl (Nat.gcd_dvd_right d l)
  _ ≥ (∑ k ∈ divisors P, if k ∣ d
          then g k * ∑ m ∈ divisors P, if (d * m) ^ 2 ≤ y ∧ m.Coprime d then g m else 0
          else 0 ) := by
    apply sum_le_sum; intro k _
    split_ifs with hkd
    swap
    · rfl
    apply mul_le_mul le_rfl
    · apply sum_le_sum; intro m hm
      split_ifs with h h' h'
      · rfl
      · exfalso; apply h'
        refine ⟨?_, h.2⟩
        trans ((d*m)^2:ℝ)
        · norm_cast
          gcongr
          refine Nat.le_of_dvd ?_ hkd
          apply Nat.pos_of_ne_zero
          apply ne_zero_of_dvd_ne_zero s.prodPrimes_ne_zero hdP
        exact h.1
      · refine le_of_lt <| s.selbergTerms_pos m <| dvd_of_mem_divisors hm
      · rfl
    · apply sum_nonneg; intro m hm
      split_ifs
      · apply le_of_lt <| s.selbergTerms_pos m <| dvd_of_mem_divisors hm
      · rfl
    · exact le_of_lt <| s.selbergTerms_pos k <| Trans.trans hkd hdP
  _ = _ := by
    conv => enter [1, 2, k]; rw [← ite_zero_mul]
    rw [←sum_mul, s.conv_selbergTerms_eq_selbergTerms_mul_nu hdP]
    trans (S * S⁻¹ * (μ d:ℝ)^2 * (ν d)⁻¹ * g d *
      (∑ m ∈ divisors P, if (d*m) ^ 2 ≤ y ∧ Coprime m d then g m else 0))
    · rw [mul_inv_cancel₀ s.selbergBoundingSum_ne_zero, ←Int.cast_pow,
        moebius_sq_eq_one_of_squarefree]
      · ring
      · exact Squarefree.squarefree_of_dvd hdP s.prodPrimes_squarefree
    dsimp only [selbergWeights]; rw [if_pos hdP]
    ring

theorem selberg_bound_weights (d : ℕ) : |γ d| ≤ 1 := by
  by_cases hdP : d ∣ P
  swap
  · rw [s.selbergWeights_eq_zero_of_not_dvd hdP]; simp only [zero_le_one, abs_zero]
  have : 1*S ≥ γ d * ↑(μ d) * S := by
    rw[one_mul]
    exact s.selbergBoundingSum_ge hdP
  replace this : γ d * μ d ≤ 1 := by
    apply le_of_mul_le_mul_of_pos_right this (s.selbergBoundingSum_pos)
  convert this using 1
  rw [← abs_of_nonneg <| s.selbergWeights_mul_mu_nonneg d hdP,
    abs_mul, ←Int.cast_abs, abs_moebius_eq_one_of_squarefree <|
    (s.prodPrimes_squarefree.squarefree_of_dvd hdP), Int.cast_one, mul_one]


theorem selberg_bound_muPlus (n : ℕ) (hn : n ∈ divisors P) :
    |μ⁺ n| ≤ (3:ℝ) ^ ω n := by
  let f : ℕ → ℕ → ℝ := fun x z : ℕ => if n = x.lcm z then 1 else 0
  dsimp only [selbergMuPlus, lambdaSquared]
  calc
    |∑ d1 ∈ n.divisors, ∑ d2 ∈ n.divisors, if n = d1.lcm d2 then γ d1 * γ d2 else 0| ≤
        ∑ d1 ∈ n.divisors, |∑ d2 ∈ n.divisors, if n = d1.lcm d2 then γ d1 * γ d2 else 0| := ?_
    _ ≤ ∑ d1 ∈ n.divisors, ∑ d2 ∈ n.divisors, |if n = d1.lcm d2 then γ d1 * γ d2 else 0| := ?_
    _ ≤ ∑ d1 ∈ n.divisors, ∑ d2 ∈ n.divisors, f d1 d2 := ?_
    _ = (n.divisors ×ˢ n.divisors).sum fun p => f p.fst p.snd := ?_
    _ = Finset.card ((n.divisors ×ˢ n.divisors).filter fun p : ℕ × ℕ => n = p.fst.lcm p.snd) := ?_
    _ = (3:ℕ) ^ ω n := ?_
    _ = (3:ℝ) ^ ω n := ?_
  · apply abs_sum_le_sum_abs
  · gcongr; apply abs_sum_le_sum_abs
  · gcongr with d1 _ d2
    rw [apply_ite abs, abs_zero, abs_mul]
    simp only [f]
    by_cases h : n = d1.lcm d2
    · rw [if_pos h, if_pos h]
      apply mul_le_one₀ (s.selberg_bound_weights d1) (abs_nonneg <| γ d2)
        (s.selberg_bound_weights d2)
    · rw [if_neg h, if_neg h]
  · rw [← Finset.sum_product']
  · rw [← sum_filter, Finset.sum_const, nsmul_one]
  · rw [← Nat.card_pair_lcm_eq (s.squarefree_of_mem_divisors_prodPrimes hn)]
    congr; ext; rw[eq_comm]
  norm_num

theorem selberg_bound_simple_errSum :
    s.errSum μ⁺ ≤
      ∑ d ∈ divisors P, if (d : ℝ) ≤ y then (3:ℝ) ^ ω d * |R d| else 0 := by
  dsimp only [errSum]
  gcongr with d hd
  split_ifs with h
  · apply mul_le_mul
    · apply s.selberg_bound_muPlus d hd
    · exact le_rfl
    · exact abs_nonneg <| R d
    · exact pow_nonneg (by linarith) (ω d)
  · rw [s.selbergμPlus_eq_zero d h, abs_zero, zero_mul]

theorem selberg_bound_simple :
    s.siftedSum ≤
      X / S +
        ∑ d ∈ divisors P, if (d : ℝ) ≤ y then (3:ℝ) ^ ω d * |R d| else 0 := by
  let μPlus := s.selbergUbSieve
  calc
    s.siftedSum ≤ X * s.mainSum μPlus + s.errSum μPlus :=
      s.siftedSum_le_mainSum_errSum_of_UpperBoundSieve μPlus
    _ ≤ _ := ?_
  gcongr
  · erw [s.selberg_bound_simple_mainSum, div_eq_mul_inv]
  · apply s.selberg_bound_simple_errSum

end LPSelbergSieve

end -- close `noncomputable section` opened in Selberg



-- === Inlined from SelbergSieve4.Applications.PrimeCountingUpperBound ===
/-
Copyright (c) 2026 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arend Mellendijk
-/

/-!
# LeanPool.SelbergSieve4.Applications.PrimeCountingUpperBound
-/

noncomputable section
open scoped Nat Nat.Prime ArithmeticFunction.zeta ArithmeticFunction.Moebius
open scoped ArithmeticFunction.omega BigOperators

namespace PrimeUpperBound

attribute [local instance] Classical.propDecidable

local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y)

lemma prodDistinctPrimes_squarefree (s : Finset ℕ) (h : ∀ p ∈ s, p.Prime) :
    Squarefree (∏ p ∈ s, p) := by
  refine Iff.mpr Nat.squarefree_iff_prime_squarefree ?_
  intro p hp; by_contra h_dvd
  by_cases hps : p ∈ s
  · rw [← Finset.mul_prod_erase (a := p) (h := hps),
      mul_dvd_mul_iff_left (Nat.Prime.ne_zero hp)] at h_dvd
    obtain ⟨q, hq⟩ := Prime.exists_mem_finset_dvd (Nat.Prime.prime hp) h_dvd
    rw [Finset.mem_erase] at hq
    exact hq.1.1 <| ((Nat.prime_dvd_prime_iff_eq hp (h q hq.1.2)).mp hq.2).symm
  · have : p ∣ ∏ p ∈ s, p := Trans.trans (dvd_mul_right p p) h_dvd
    obtain ⟨q, hq⟩ := Prime.exists_mem_finset_dvd (Nat.Prime.prime hp) this
    have heq : p = q := (Nat.prime_dvd_prime_iff_eq hp (h q hq.1)).mp hq.2
    rw [heq] at hps; exact hps hq.1

lemma primorial_squarefree (n : ℕ) : Squarefree (primorial n) := by
  apply prodDistinctPrimes_squarefree
  simp_rw [Finset.mem_filter]
  exact fun _ h => h.2

theorem zeta_pos_of_prime :
    ∀ (p : ℕ), Nat.Prime p → (0 : ℝ) < (↑ζ : ArithmeticFunction ℝ) p := by
  intro p hp
  rw [ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply, if_neg (Nat.Prime.ne_zero hp)]
  norm_num

theorem zeta_lt_self_of_prime :
    ∀ (p : ℕ), Nat.Prime p → (↑ζ : ArithmeticFunction ℝ) p < (p : ℝ) := by
  intro p hp
  rw [ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply, if_neg (Nat.Prime.ne_zero hp)]
  norm_num
  exact Nat.succ_le_iff.mp (Nat.Prime.two_le hp)

/-- Selberg sieve specialized to primes at most the real level `y`. -/
def primeSieve (N : ℕ) (y : ℝ) (hy : 1 ≤ y) : LPSelbergSieve := {
  support := Finset.range (N + 1)
  prodPrimes := primorial (Nat.floor y)
  prodPrimes_squarefree := primorial_squarefree _
  weights := fun _ => 1
  weights_nonneg := fun _ => zero_le_one
  totalMass := N
  nu := (ζ : ArithmeticFunction ℝ).pdiv .id
  nu_mult := by arith_mult
  nu_pos_of_prime := fun p hp _ => by
    simp [if_neg hp.ne_zero, Nat.pos_of_ne_zero hp.ne_zero]
  nu_lt_one_of_prime := fun p hp _ => by
    simpa [hp.ne_zero] using
      (inv_lt_one_of_one_lt₀ (by norm_cast; exact hp.one_lt) : (p : ℝ)⁻¹ < 1)
  level := y
  one_le_level := hy
}

theorem prime_dvd_primorial_iff (n p : ℕ) (hp : p.Prime) :
    p ∣ primorial n ↔ p ≤ n := by
  unfold primorial
  constructor
  · intro h
    let h' : ∃ i, i ∈ Finset.filter Nat.Prime (Finset.range (n + 1)) ∧ p ∣ i :=
      Prime.exists_mem_finset_dvd (Nat.Prime.prime hp) h
    obtain ⟨q, hq⟩ := h'
    rw [Finset.mem_filter, Finset.mem_range] at hq
    rw [prime_dvd_prime_iff_eq (Nat.Prime.prime hp) (Nat.Prime.prime hq.1.2)] at hq
    rw [hq.2]
    exact Nat.lt_succ_iff.mp hq.1.1
  · intro h
    apply Finset.dvd_prod_of_mem
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨Nat.lt_succ_iff.mpr h, hp⟩

theorem siftedSum_eq (s : LPSelbergSieve) (hw : ∀ i ∈ s.support, s.weights i = 1)
    (z : ℝ) (hz : 1 ≤ z) (hP : s.prodPrimes = primorial (Nat.floor z)) :
    s.siftedSum =
      (s.support.filter (fun d => ∀ p : ℕ, p.Prime → p ≤ z → ¬p ∣ d)).card := by
  dsimp only [LPSieve.siftedSum]
  rw [Finset.card_eq_sum_ones, ←Finset.sum_filter, Nat.cast_sum]
  apply Finset.sum_congr
  · rw [hP]
    ext d
    constructor
    · intro hd
      rw [Finset.mem_filter] at *
      constructor
      · exact hd.1
      · intro p hpp hpy
        rw [← Nat.Prime.coprime_iff_not_dvd hpp]
        apply Nat.Coprime.coprime_dvd_left _ hd.2
        rw [prime_dvd_primorial_iff _ _ hpp]
        apply Nat.le_floor hpy
    · intro h
      rw [Finset.mem_filter] at *
      constructor
      · exact h.1
      refine Nat.coprime_of_dvd ?_
      intro p hp
      erw [prime_dvd_primorial_iff _ _ hp]
      intro hpy
      apply h.2 p hp
      trans ↑(Nat.floor z)
      · norm_cast
      · apply Nat.floor_le
        linarith only [hz]
  · simp_rw [Nat.cast_one]
    intro x hx
    rw [Finset.mem_filter] at hx
    apply hw x hx.1

theorem primeSieve_siftedSum_eq (N : ℕ) (y : ℝ) (hy : 1 ≤ y) :
    (primeSieve N y hy).siftedSum =
      ((Finset.range (N + 1)).filter (fun d => ∀ p : ℕ, p.Prime → p ≤ y → ¬p ∣ d)).card := by
  apply siftedSum_eq
  · exact fun _ _ => rfl
  · exact hy
  · rfl

theorem prime_subset (N : ℕ) (y : ℝ) :
    (Finset.range (N + 1)).filter Nat.Prime ⊆
      ((Finset.range (N + 1)).filter (fun d => ∀ p : ℕ, p.Prime → p ≤ y → ¬p ∣ d))
      ∪ Finset.Icc 1 (Nat.floor y) := by
  intro p
  simp_rw [Finset.mem_union, Finset.mem_filter]
  intro h
  by_cases hp_le : p ≤ y
  · right
    rw [Finset.mem_Icc]
    exact ⟨le_of_lt h.2.one_lt, Nat.le_floor hp_le⟩
  · left
    constructor
    · exact h.1
    · intro q hq hq'
      rw [prime_dvd_prime_iff_eq hq.prime h.2.prime]
      intro hqp
      rw [hqp] at hq'
      linarith only [hp_le, hq']


theorem pi_le_siftedSum (N : ℕ) (y : ℝ) (hy : 1 ≤ y) :
    π N ≤ (primeSieve N y hy).siftedSum + y := by
  trans ((primeSieve N y hy).siftedSum + Nat.floor y)
  · have : (Finset.Icc 1 (Nat.floor y)).card = Nat.floor y := by
      rw [Nat.card_Icc]; norm_num
    rw [primeSieve_siftedSum_eq, ←this]
    unfold Nat.primeCounting
    unfold Nat.primeCounting'
    rw [Nat.count_eq_card_filter_range]
    norm_cast
    trans (((Finset.range (N + 1)).filter
        (fun d => ∀ p : ℕ, p.Prime → p ≤ y → ¬p ∣ d))
      ∪ Finset.Icc 1 (Nat.floor y)).card
    · exact Finset.card_le_card (prime_subset N y)
    apply Finset.card_union_le
  · gcongr
    apply Nat.floor_le
    linarith only [hy]

/-- Predicate asserting that an arithmetic function is completely multiplicative. -/
def CompletelyMultiplicative (f : ArithmeticFunction ℝ) : Prop :=
  f 1 = 1 ∧ ∀ a b, f (a * b) = f a * f b

namespace CompletelyMultiplicative
open ArithmeticFunction
theorem zeta : CompletelyMultiplicative ζ := by
  unfold CompletelyMultiplicative
  constructor
  · simp [ArithmeticFunction.zeta_apply]
  intro a b
  by_cases ha : a = 0
  · simp [ArithmeticFunction.zeta_apply, ha]
  by_cases hb : b = 0
  · simp [ArithmeticFunction.zeta_apply, hb]
  simp [ArithmeticFunction.zeta_apply, ha, hb, mul_eq_zero]

theorem id : CompletelyMultiplicative ArithmeticFunction.id := by
  constructor <;> simp

theorem pmul (f g : ArithmeticFunction ℝ) (hf : CompletelyMultiplicative f)
    (hg : CompletelyMultiplicative g) :
    CompletelyMultiplicative (ArithmeticFunction.pmul f g) := by
  constructor
  · rw [pmul_apply, hf.1, hg.1, mul_one]
  intro a b
  simp_rw [pmul_apply, hf.2, hg.2]; ring

theorem pdiv {f g : ArithmeticFunction ℝ} (hf : CompletelyMultiplicative f)
    (hg : CompletelyMultiplicative g) :
    CompletelyMultiplicative (ArithmeticFunction.pdiv f g) := by
  constructor
  · rw [pdiv_apply, hf.1, hg.1, div_one]
  intro a b
  simp_rw [pdiv_apply, hf.2, hg.2]; ring

theorem isMultiplicative {f : ArithmeticFunction ℝ} (hf : CompletelyMultiplicative f) :
    ArithmeticFunction.IsMultiplicative f :=
  ⟨hf.1, fun _ => hf.2 _ _⟩

theorem apply_pow (f : ArithmeticFunction ℝ) (hf : CompletelyMultiplicative f) (a n : ℕ) :
    f (a^n) = f a ^ n := by
  induction n with
  | zero => simpa using hf.1
  | succ n' ih =>
      calc
        f (a ^ (n' + 1)) = f (a ^ n' * a) := by rw [pow_succ]
        _ = f (a ^ n') * f a := hf.2 _ _
        _ = f a ^ n' * f a := by rw [ih]
        _ = f a ^ (n' + 1) := by rw [pow_succ]

end CompletelyMultiplicative

theorem prod_factors_one_div_compMult_ge (M : ℕ) (f : ArithmeticFunction ℝ)
    (hf : CompletelyMultiplicative f) (hf_nonneg : ∀ n, 0 ≤ f n) (d : ℕ)
    (hd : Squarefree d) (hf_size : ∀ n, n.Prime → n ∣ d → f n < 1) :
    f d * ∏ p ∈ d.primeFactors, 1 / (1 - f p)
    ≥ ∏ p ∈ d.primeFactors, ∑ n ∈ Finset.Icc 1 M, f (p ^ n) := by
  calc
    f d * ∏ p ∈ d.primeFactors, 1 / (1 - f p)
        = ∏ p ∈ d.primeFactors, f p / (1 - f p) := by
      conv => { lhs; congr; rw [←Nat.prod_primeFactors_of_squarefree hd] }
      rw [hf.isMultiplicative.map_prod_of_subset_primeFactors _ _ subset_rfl,
        ← Finset.prod_mul_distrib]
      simp_rw [one_div, div_eq_mul_inv]
    _ ≥ ∏ p ∈ d.primeFactors, ∑ n ∈ Finset.Icc 1 M, (f p) ^ n := by
      gcongr with p hp
      · exact fun p _ => Finset.sum_nonneg fun n _ => pow_nonneg (hf_nonneg p) n
      rw [Nat.mem_primeFactors_of_ne_zero hd.ne_zero] at hp
      simpa [← Finset.Ico_succ_right_eq_Icc, pow_one] using
        (geom_sum_Ico_le_of_lt_one (m := 1) (n := M.succ) (x := f p) (hf_nonneg p)
          (hf_size p hp.1 hp.2))
    _ = ∏ p ∈ d.primeFactors, ∑ n ∈ Finset.Icc 1 M, f (p ^ n) := by
      simp_rw [hf.apply_pow]

theorem prod_factors_sum_pow_compMult (M : ℕ) (hM : M ≠ 0)
    (f : ArithmeticFunction ℝ) (hf : CompletelyMultiplicative f) (d : ℕ)
    (hd : Squarefree d) :
    ∏ p ∈ d.primeFactors, ∑ n ∈ Finset.Icc 1 M, f (p ^ n)
    = ∑ m ∈ (d ^ M).divisors.filter (d ∣ ·), f m := by
  rw [Finset.prod_sum]
  let i : (a : _) → (ha : a ∈ Finset.pi d.primeFactors fun p => Finset.Icc 1 M) → ℕ :=
    fun a _ => ∏ p ∈ d.primeFactors.attach, p.1 ^ (a p p.2)
  have hfact_i : ∀ a ha,
      ∀ p, Nat.factorization (i a ha) p = if hp : p ∈ d.primeFactors then a p hp else 0 := by
    intro a ha p
    by_cases hp : p ∈ d.primeFactors
    · rw [dif_pos hp, Nat.factorization_prod, Finset.sum_apply',
        Finset.sum_eq_single ⟨p, hp⟩, Nat.factorization_pow, Finsupp.smul_apply,
          Nat.Prime.factorization_self (Nat.prime_of_mem_primeFactors hp)]
      · ring
      · intro q _ hq
        rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_zero]
        right
        apply Nat.factorization_eq_zero_of_not_dvd
        rw [Nat.Prime.dvd_iff_eq (Nat.prime_of_mem_primeFactors q.2)
          (Nat.prime_of_mem_primeFactors hp).ne_one, ← exists_eq_subtype_mk_iff]
        push Not
        exact fun _ => hq
      · intro h
        exfalso
        exact h (Finset.mem_attach _ _)
      · exact fun q _ => pow_ne_zero _ (ne_of_gt (Nat.pos_of_mem_primeFactors q.2))
    · rw [dif_neg hp]
      by_cases hpp : p.Prime
      swap
      · apply Nat.factorization_eq_zero_of_not_prime _ hpp
      apply Nat.factorization_eq_zero_of_not_dvd
      intro hp_dvd
      obtain ⟨⟨q, hq⟩, _, hp_dvd_pow⟩ := Prime.exists_mem_finset_dvd hpp.prime hp_dvd
      apply hp
      rw [Nat.mem_primeFactors]
      constructor
      · exact hpp
      · refine ⟨?_, hd.ne_zero⟩
        trans q
        · apply Nat.Prime.dvd_of_dvd_pow hpp hp_dvd_pow
        · apply Nat.dvd_of_mem_primeFactors hq
  have hi_ne_zero : ∀ (a : _) (ha : a ∈ Finset.pi d.primeFactors fun _p => Finset.Icc 1 M),
      i a ha ≠ 0 := by
    intro a ha
    erw [Finset.prod_ne_zero_iff]
    exact fun p _ => pow_ne_zero _ (ne_of_gt (Nat.pos_of_mem_primeFactors p.property))
  have hi : ∀ (a : _) (ha : a ∈ Finset.pi d.primeFactors fun _p => Finset.Icc 1 M),
      i a ha ∈ (d ^ M).divisors.filter (d ∣ ·) := by
    intro a ha
    rw [Finset.mem_filter, Nat.mem_divisors,
      ← Nat.factorization_le_iff_dvd hd.ne_zero (hi_ne_zero a ha),
      ←Nat.factorization_le_iff_dvd (hi_ne_zero a ha) (pow_ne_zero _ hd.ne_zero)]
    constructor; constructor
    · rw [Finsupp.le_iff]; intro p _
      rw [hfact_i a ha]
      by_cases hp : p ∈ d.primeFactors
      · rw [dif_pos hp]
        rw [Nat.factorization_pow, Finsupp.smul_apply]
        simp_rw [Finset.mem_pi, Finset.mem_Icc] at ha
        trans (M • 1)
        · norm_num
          exact (ha p hp).2
        · gcongr
          rw [Nat.mem_primeFactors_of_ne_zero hd.ne_zero] at hp
          rw [←Nat.Prime.dvd_iff_one_le_factorization hp.1 hd.ne_zero]
          exact hp.2
      · rw [dif_neg hp]; norm_num
    · apply pow_ne_zero _ hd.ne_zero
    · rw [Finsupp.le_iff]; intro p hp
      rw [Nat.support_factorization] at hp
      rw [hfact_i a ha]
      rw [dif_pos hp]
      trans 1
      · exact hd.natFactorization_le_one p
      simp_rw [Finset.mem_pi, Finset.mem_Icc] at ha
      exact (ha p hp).1
  have h : ∀ (a : _) (ha : a ∈ Finset.pi d.primeFactors fun _p => Finset.Icc 1 M),
      ∏ p ∈ d.primeFactors.attach, f (p.1 ^ (a p p.2)) = f (i a ha) := by
    intro a ha
    apply symm
    apply hf.isMultiplicative.map_prod
    intro x _ y _ hxy
    simp_rw [Finset.mem_pi, Finset.mem_Icc, Nat.succ_le_iff] at ha
    apply (Nat.coprime_pow_left_iff (ha x x.2).1 ..).mpr
    apply (Nat.coprime_pow_right_iff (ha y y.2).1 ..).mpr
    have hxp := Nat.prime_of_mem_primeFactors x.2
    rw [Nat.Prime.coprime_iff_not_dvd hxp]
    rw [Nat.prime_dvd_prime_iff_eq hxp (Nat.prime_of_mem_primeFactors y.2)]
    exact fun hc => hxy (Subtype.ext hc)
  have i_inj : ∀ a ha b hb, i a ha = i b hb → a = b := by
    intro a ha b hb hiab
    apply_fun Nat.factorization at hiab
    ext p hp
    obtain hiabp := DFunLike.ext_iff.mp hiab p
    rw [hfact_i a ha, hfact_i b hb, dif_pos hp, dif_pos hp] at hiabp
    exact hiabp
  have i_surj : ∀ (b : ℕ), b ∈ (d^M).divisors.filter (d ∣ ·) → ∃ a ha, i a ha = b := by
    intro b hb
    have h : (fun p _ => (Nat.factorization b) p) ∈
        Finset.pi d.primeFactors fun p => Finset.Icc 1 M := by
      rw [Finset.mem_pi]
      intro p hp
      rw [Finset.mem_Icc]
      rw [Finset.mem_filter] at hb
      have hb_ne_zero : b ≠ 0 := ne_of_gt <| Nat.pos_of_mem_divisors hb.1
      have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
      constructor
      · rw [←Nat.Prime.dvd_iff_one_le_factorization hpp hb_ne_zero]
        · exact Trans.trans (Nat.dvd_of_mem_primeFactors hp) hb.2
      · rw [Nat.mem_divisors] at hb
        trans Nat.factorization (d^M) p
        · exact (Nat.factorization_le_iff_dvd hb_ne_zero hb.left.right).mpr hb.left.left p
        rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
        have : d.factorization p ≤ 1 := by
          apply hd.natFactorization_le_one
        exact (mul_le_iff_le_one_right (Nat.pos_of_ne_zero hM)).mpr this
    use (fun p _ => Nat.factorization b p)
    use h
    apply Nat.eq_of_factorization_eq
    · apply hi_ne_zero _ h
    · exact ne_of_gt <| Nat.pos_of_mem_divisors (Finset.mem_filter.mp hb).1
    intro p
    rw [hfact_i (fun p _ => (Nat.factorization b) p) h p]
    rw [Finset.mem_filter, Nat.mem_divisors] at hb
    by_cases hp : p ∈ d.primeFactors
    · rw [dif_pos hp]
    · rw [dif_neg hp, eq_comm, Nat.factorization_eq_zero_iff, ←or_assoc]
      rw [Nat.mem_primeFactors] at hp
      left
      push Not at hp
      by_cases hpp : p.Prime
      · right
        intro hpb
        exact hd.ne_zero <| hp hpp (hpp.dvd_of_dvd_pow (hpb.trans hb.1.1))
      · left
        exact hpp
  exact Finset.sum_bij i hi i_inj i_surj h

theorem lem0 (P : ℕ) {s : Finset ℕ} (h : ∀ p ∈ s, p ∣ P) (h' : ∀ p ∈ s, p.Prime) :
    ∏ p ∈ s, p ∣ P := by
  simp_rw [Nat.prime_iff] at h'
  apply Finset.prod_primes_dvd _ h' h

lemma sqrt_le_self (x : ℝ) (hx : 1 ≤ x) : Real.sqrt x ≤ x := by
  refine Iff.mpr Real.sqrt_le_iff ?_
  constructor
  · linarith
  nlinarith [sq_nonneg (x - 1)]

lemma nat_squarefree_dvd_pow (a b N : ℕ) (ha : Squarefree a) (hab : a ∣ b ^ N) :
    a ∣ b := by
  by_cases hb : b = 0
  · rw [hb]
    exact Nat.dvd_zero a
  rw [← Nat.factorization_le_iff_dvd ha.ne_zero hb]
  intro p
  by_cases hp : p.Prime
  · by_cases hpa : p ∣ a
    · have hp_b : p ∣ b := hp.dvd_of_dvd_pow (hpa.trans hab)
      exact (ha.natFactorization_le_one p).trans
        ((hp.dvd_iff_one_le_factorization hb).mp hp_b)
    · rw [Nat.factorization_eq_zero_of_not_dvd hpa]
      exact Nat.zero_le _
  · rw [Nat.factorization_eq_zero_of_not_prime a hp]
    exact Nat.zero_le _

theorem selbergBoundingSum_ge_sum_div (s : LPSelbergSieve)
    (hP : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ s.level → p ∣ s.prodPrimes)
    (hnu : CompletelyMultiplicative s.nu) (hnu_nonneg : ∀ n, 0 ≤ s.nu n)
    (hnu_lt : ∀ p, p.Prime → p ∣ s.prodPrimes → s.nu p < 1) :
    s.selbergBoundingSum ≥
      ∑ m ∈ Finset.Icc 1 (Nat.floor (Real.sqrt s.level)), s.nu m := by
  calc ∑ l ∈ s.prodPrimes.divisors, (if l ^ 2 ≤ s.level then s.selbergTerms l else 0)
     ≥ ∑ l ∈ s.prodPrimes.divisors.filter (fun l : ℕ => l ^ 2 ≤ s.level),
        ∑ m ∈ (l ^ Nat.floor s.level).divisors.filter (l ∣ ·), s.nu m := ?_
   _ ≥ ∑ m ∈ Finset.Icc 1 (Nat.floor (Real.sqrt s.level)), s.nu m := ?_
  · rw [← Finset.sum_filter]
    apply Finset.sum_le_sum
    intro l hl
    rw [Finset.mem_filter, Nat.mem_divisors] at hl
    have hlsq : Squarefree l := Squarefree.squarefree_of_dvd hl.1.1 s.prodPrimes_squarefree
    trans (∏ p ∈ l.primeFactors, ∑ n ∈ Finset.Icc 1 (Nat.floor s.level), s.nu (p ^ n))
    · rw [prod_factors_sum_pow_compMult (Nat.floor s.level) _ s.nu]
      · exact hnu
      · exact hlsq
      · rw [ne_eq, Nat.floor_eq_zero, not_lt]
        exact s.one_le_level
    · rw [s.selbergTerms_apply l]
      apply prod_factors_one_div_compMult_ge _ _ hnu _ _ hlsq
      · intro p hpp hpl
        apply hnu_lt p hpp (Trans.trans hpl hl.1.1)
      · exact hnu_nonneg
  rw [← Finset.sum_biUnion]
  · apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro m hm
      have hprod_pos : 0 < (∏ p ∈ m.primeFactors, p) := by
        apply Finset.prod_pos
        intro p hp
        exact Nat.pos_of_mem_primeFactors hp
      have hprod_ne_zero : (∏ p ∈ m.primeFactors, p) ^ ⌊s.level⌋₊ ≠ 0 :=
        pow_ne_zero _ (ne_of_gt hprod_pos)
      rw [Finset.mem_biUnion]
      simp_rw [Finset.mem_filter, Nat.mem_divisors]
      rw [Finset.mem_Icc, Nat.le_floor_iff (Real.sqrt_nonneg s.level)] at hm
      have hm_ne_zero : m ≠ 0 := by
        exact ne_of_gt <| Nat.succ_le_iff.mp hm.1
      use ∏ p ∈ m.primeFactors, p
      constructor
      · constructor
        · constructor
          · apply lem0 <;> intro p hp
            · apply hP p <| Nat.prime_of_mem_primeFactors hp
              trans (m : ℝ)
              · norm_cast
                exact Nat.le_of_mem_primeFactors hp
              trans (Real.sqrt s.level)
              · exact hm.2
              apply sqrt_le_self s.level s.one_le_level
            · exact Nat.prime_of_mem_primeFactors hp
          · exact s.prodPrimes_ne_zero
        · rw [← Real.sqrt_le_sqrt_iff (by linarith only [s.one_le_level]), Nat.cast_pow,
            Real.sqrt_sq]
          · trans (m : ℝ)
            · norm_cast
              apply Nat.le_of_dvd (Nat.succ_le_iff.mp hm.1)
              exact Nat.prod_primeFactors_dvd m
            · exact hm.2
          · apply le_of_lt
            norm_cast
      · constructor
        · constructor
          · rw [← Nat.factorization_le_iff_dvd _ hprod_ne_zero, Nat.factorization_pow]
            · intro p
              have hy_mul_prod_nonneg :
                  0 ≤ ⌊s.level⌋₊ * (Nat.factorization (∏ p ∈ m.primeFactors, p)) p :=
                Nat.zero_le _
              trans (Nat.factorization m) p * 1
              · rw [mul_one]
              trans ⌊s.level⌋₊ * Nat.factorization (∏ p ∈ m.primeFactors, p) p
              swap
              · apply le_rfl
              by_cases hpp : p.Prime
              swap
              · rw [Nat.factorization_eq_zero_of_not_prime _ hpp, zero_mul]
                exact hy_mul_prod_nonneg
              by_cases hpdvd : p ∣ m
              swap
              · rw [Nat.factorization_eq_zero_of_not_dvd hpdvd, zero_mul]
                exact hy_mul_prod_nonneg
              apply mul_le_mul
              · trans m
                · exact le_of_lt <| Nat.factorization_lt p hm_ne_zero
                apply Nat.le_floor
                refine le_trans hm.2 ?_
                apply sqrt_le_self _ s.one_le_level
              · rw [← Nat.Prime.pow_dvd_iff_le_factorization hpp <| ne_of_gt hprod_pos,
                  pow_one]
                apply Finset.dvd_prod_of_mem
                rw [Nat.mem_primeFactors]
                exact ⟨hpp, hpdvd, hm_ne_zero⟩
              · norm_num
              · norm_num
            · exact hm_ne_zero
          · exact hprod_ne_zero
        · exact Nat.prod_primeFactors_dvd m
    · intro i _ _
      apply hnu_nonneg
  · intro i hi j hj hij t hti htj x hx
    exfalso
    specialize hti hx
    specialize htj hx
    simp_rw [Finset.mem_coe, Finset.mem_filter, Nat.mem_divisors] at *
    have h : ∀ i j {n}, i ∣ s.prodPrimes → i ∣ x → x ∣ j ^ n → i ∣ j := by
      intro i j n hiP hix hij
      apply nat_squarefree_dvd_pow i j n (s.squarefree_of_dvd_prodPrimes hiP)
      exact Trans.trans hix hij
    have hidvdj : i ∣ j := by
      apply h i j hi.1.1 hti.2 htj.1.1
    have hjdvdi : j ∣ i := by
      apply h j i hj.1.1 htj.2 hti.1.1
    exact hij <| Nat.dvd_antisymm hidvdj hjdvdi

theorem boundingSum_ge_sum (s : LPSelbergSieve) (hnu : s.nu = (ζ : ArithmeticFunction ℝ).pdiv .id)
    (hP : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ s.level → p ∣ s.prodPrimes) :
    s.selbergBoundingSum ≥
      ∑ m ∈ Finset.Icc 1 (Nat.floor (Real.sqrt s.level)), 1 / (m : ℝ) := by
  trans ∑ m ∈ Finset.Icc 1 (Nat.floor (Real.sqrt s.level)),
      (ζ : ArithmeticFunction ℝ).pdiv .id m
  · rw [← hnu]
    apply selbergBoundingSum_ge_sum_div
    · intro p hpp hple
      apply hP p hpp hple
    · rw [hnu]
      exact CompletelyMultiplicative.zeta.pdiv CompletelyMultiplicative.id
    · intro n
      rw [hnu]
      apply div_nonneg
      · by_cases h : n = 0 <;> simp [h]
      · simp
    · intro p hpp _
      rw [hnu]
      simpa [ArithmeticFunction.pdiv_apply, ArithmeticFunction.natCoe_apply,
        ArithmeticFunction.zeta_apply, if_neg hpp.ne_zero, ArithmeticFunction.id_apply,
        one_div] using
          (inv_lt_one_of_one_lt₀ (by norm_cast; exact hpp.one_lt) : (p : ℝ)⁻¹ < 1)
  apply le_of_eq
  apply Finset.sum_congr rfl
  intro m hm
  rw [Finset.mem_Icc] at hm
  simp only [one_div, ArithmeticFunction.pdiv_apply, ArithmeticFunction.natCoe_apply,
    ArithmeticFunction.zeta_apply_ne (show m ≠ 0 by omega), Nat.cast_one,
    ArithmeticFunction.id_apply]

theorem boundingSum_ge_log (s : LPSelbergSieve) (hnu : s.nu = (ζ : ArithmeticFunction ℝ).pdiv .id)
    (hP : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ s.level → p ∣ s.prodPrimes) :
    s.selbergBoundingSum ≥ Real.log (s.level) / 2 := by
  trans (∑ m ∈ Finset.Icc 1 (Nat.floor (Real.sqrt s.level)), 1 / (m : ℝ))
  · exact boundingSum_ge_sum s hnu hP
  trans (Real.log (Real.sqrt s.level))
  · rw [ge_iff_le]
    simp_rw [one_div]
    apply Aux.log_le_sum_inv (Real.sqrt s.level)
    rw [Real.le_sqrt] <;> linarith [s.one_le_level]
  · apply ge_of_eq
    refine Real.log_sqrt ?h.hx
    linarith [s.one_le_level]

theorem primeSieve_boundingSum_ge (N : ℕ) (y : ℝ) (hy : 1 ≤ y) :
    (primeSieve N y hy).selbergBoundingSum ≥ Real.log y / 2 := by
  apply boundingSum_ge_log
  · rfl
  · intro p hpp hp
    erw [prime_dvd_primorial_iff _ _ hpp]
    exact Nat.le_floor hp

theorem card_range_filter_dvd (N d : ℕ) (hd : d ≠ 0) :
    ((Finset.range N).filter (d ∣ ·)).card = Nat.ceil ((N : ℝ) / d) := by
  let f : (i : ℕ) → i < (Nat.ceil ((N : ℝ) / d)) → ℕ := fun i _ => d * i
  apply Finset.card_eq_of_bijective f
  · intro k hk
    rw [Finset.mem_filter, Finset.mem_range] at hk
    use k / d
    constructor
    · refine Nat.mul_div_cancel' hk.2
    · rw [Nat.lt_ceil]
      rw [Nat.cast_div hk.2 (by exact_mod_cast hd : (d : ℝ) ≠ 0)]
      exact div_lt_div_of_pos_right
        (by exact_mod_cast hk.1 : (k : ℝ) < N)
        (by norm_cast; exact Nat.pos_of_ne_zero hd)
  · intro k hk
    rw [Finset.mem_filter, Finset.mem_range]
    rw [Nat.lt_ceil, lt_div_iff₀ (by norm_cast; exact Nat.pos_of_ne_zero hd : (0 : ℝ) < d),
      mul_comm] at hk
    norm_cast at hk
    exact ⟨hk, dvd_mul_right ..⟩
  · exact fun _ _ _ _ hij => Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hd) hij

theorem primeSieve_multSum_eq (N : ℕ) (y : ℝ) (hy : 1 ≤ y) (d : ℕ) (hd : d ≠ 0) :
    (primeSieve N y hy).multSum d = Nat.ceil (((N + 1 : ℕ) : ℝ) / d) := by
  unfold primeSieve
  simp only [LPSieve.multSum, Finset.sum_boole, Nat.cast_inj]
  apply card_range_filter_dvd
  exact hd


theorem primeSieve_rem_eq (N : ℕ) (y : ℝ) (hy : 1 ≤ y) (d : ℕ) (hd : d ≠ 0) :
    (primeSieve N y hy).rem d = Nat.ceil (((N + 1 : ℕ) : ℝ) / d) - N / d := by
  unfold LPSieve.rem
  rw [primeSieve_multSum_eq (hd := hd)]
  unfold primeSieve
  rw [ArithmeticFunction.pdiv_apply, ArithmeticFunction.natCoe_apply,
    ArithmeticFunction.zeta_apply, if_neg hd]
  rw [ArithmeticFunction.natCoe_apply, ArithmeticFunction.id_apply]
  ring_nf

theorem primeSieve_abs_rem_eq (N : ℕ) (y : ℝ) (hy : 1 ≤ y) (d : ℕ) (hd : d ≠ 0) :
    |(primeSieve N y hy).rem d| ≤ 2 := by
  rw [primeSieve_rem_eq (hd:=hd), abs_le]
  constructor
  · apply le_sub_right_of_add_le
    trans ((N + 1) / ↑d)
    · rw [add_comm, add_div]
      have : 0 ≤ 1/(d:ℝ) := by
        norm_num
      linarith
    simpa [Nat.cast_add, Nat.cast_one] using Nat.le_ceil (((N + 1 : ℕ) : ℝ) / d)
  · apply sub_left_le_of_le_add
    trans ↑(Nat.floor ((N+1)/d:ℝ)+1)
    · norm_cast
      apply Nat.ceil_le_floor_add_one
    trans ((N+1)/d+1:ℝ)
    · push_cast
      have hfloor : (↑⌊(↑N + 1) / (d : ℝ)⌋₊ : ℝ) ≤ (↑N + 1) / (d : ℝ) := by
        exact Nat.floor_le
          (div_nonneg (by norm_cast; norm_num) (by norm_num) :
            0 ≤ ((↑N + 1) / (d : ℝ)))
      simpa [add_comm, add_left_comm, add_assoc] using add_le_add_right hfloor 1
    have : 1 / (d : ℝ) ≤ 1 := by
      rw [one_div]
      apply inv_le_one_of_one_le₀
      norm_cast
      linarith [Nat.pos_of_ne_zero hd]
    rw [add_div]
    linarith

open ArithmeticFunction

theorem rem_sum_le_of_const (s : LPSelbergSieve) (C : ℝ) (hrem : ∀ d > 0, |s.rem d| ≤ C) :
    ∑ d ∈ s.prodPrimes.divisors,
        (if (d : ℝ) ≤ s.level then (3 : ℝ) ^ ω d * |s.rem d| else 0)
      ≤ C * s.level * (1 + Real.log s.level) ^ 3 := by
  rw [← Finset.sum_filter]
  trans (∑ d ∈ Finset.filter (fun d : ℕ => ↑d ≤ s.level)
      (s.toLPSieve.prodPrimes.divisors), 3 ^ ω d * C)
  · gcongr with d hd
    · norm_cast
    rw [Finset.mem_filter, Nat.mem_divisors] at hd
    apply hrem d
    apply Nat.pos_of_ne_zero
    apply ne_zero_of_dvd_ne_zero hd.1.2 hd.1.1
  rw [← Finset.sum_mul, mul_comm, mul_assoc]
  gcongr
  · linarith [abs_nonneg <| s.rem 1, hrem 1 (by norm_num)]
  simp_rw [Nat.cast_pow]
  push_cast
  rw [Finset.sum_filter]
  apply Aux.sum_pow_cardDistinctFactors_le_self_mul_log_pow (hx := s.one_le_level)
  apply LPSieve.prodPrimes_squarefree

theorem primeSieve_rem_sum_le (N : ℕ) (y : ℝ) (hy : 1 ≤ y) :
    ∑ d ∈ (primeSieve N y hy).prodPrimes.divisors,
        (if (d : ℝ) ≤ y then (3 : ℝ) ^ ω d * |(primeSieve N y hy).rem d| else 0)
      ≤ 2 * y * (1 + Real.log y) ^ 3 := by
  apply rem_sum_le_of_const
  intro d hd
  push_cast
  apply primeSieve_abs_rem_eq
  omega

theorem pi_le_of_y (N : ℕ) (y : ℝ) (hy_lt : 1 < y) :
    π N ≤ 2 * N / Real.log y + 3 * y * (1 + Real.log y) ^ 3 := by
  have hy : 1 ≤ y := le_of_lt hy_lt
  trans ((primeSieve N y hy).siftedSum + y)
  · apply pi_le_siftedSum
  suffices LPSieve.siftedSum (primeSieve N y hy).toLPSieve ≤
      2 * N / Real.log y + 2 * y * (1 + Real.log y) ^ 3 by
    push_cast at *
    have : y * (1 : ℝ) ≤ y * (1 + Real.log y) ^ 3 := by
      have hy_nonneg : 0 ≤ y := by linarith
      have hbase : (1 : ℝ) ≤ 1 + Real.log y := by linarith [Real.log_nonneg hy]
      have hpow : (1 : ℝ) ≤ (1 + Real.log y)^3 := one_le_pow₀ hbase
      have hdiff : (0 : ℝ) ≤ y * ((1 + Real.log y)^3 - 1) :=
        mul_nonneg hy_nonneg (sub_nonneg.mpr hpow)
      nlinarith
    rw [mul_one] at this
    linarith
  trans ((primeSieve N y hy).totalMass / (primeSieve N y hy).selbergBoundingSum) +
      ∑ d ∈ (primeSieve N y hy).prodPrimes.divisors,
        (if (d : ℝ) ≤ y then (3 : ℝ) ^ ω d * |(primeSieve N y hy).rem d| else 0)
  · apply (LPSelbergSieve.selberg_bound_simple)
  gcongr (?_ + ?_)
  · trans (N / (Real.log y / 2))
    · gcongr (?_ / ?_)
      · linarith [Real.log_pos hy_lt]
      · rfl
      rw [←ge_iff_le]
      apply primeSieve_boundingSum_ge
    rw [div_eq_mul_inv, inv_div, ←mul_div_assoc, mul_comm]
    push_cast
    rfl
  · apply primeSieve_rem_sum_le

lemma primeCounting_zero :
  π 0 = 0 := by decide
lemma primeCounting_one :
  π 1 = 0 := by decide

theorem loglog_nonneg (x : ℝ) (hx : 3 ≤ x) :
    0 ≤ Real.log (Real.log x) := by
  apply Real.log_nonneg
  rw [← Real.log_exp 1]
  gcongr
  trans 3
  · have := Real.exp_one_lt_d9
    trans (2.7182818286)
    · linarith [Real.exp_one_lt_d9]
    · norm_num
  · exact hx

theorem loglog_bigO_log :
    (fun N : ℕ => Real.log (Real.log N)) =O[Filter.atTop] (fun N : ℕ => Real.log N) := by
  apply Asymptotics.IsBigO.of_bound'
  rw [Filter.eventually_iff, Filter.mem_atTop_sets]
  use 10
  intro x hx; simp only [Real.norm_eq_abs, Set.mem_setOf_eq]
  rw [←Nat.cast_le (α:=ℝ)] at hx
  conv at hx => {lhs; norm_num}
  rw [le_abs]; left
  rw [abs_le]
  constructor
  · linarith only [Real.log_natCast_nonneg x, loglog_nonneg x (by linarith)]
  linarith [Real.log_le_sub_one_of_pos (x:= Real.log x) (Real.log_pos (by linarith))]


theorem _lemma5 : (Real.log ∘ Real.log) =o[Filter.atTop] Real.log := by
  simpa [Function.comp_def] using
    Asymptotics.IsLittleO.comp_tendsto Real.isLittleO_log_id_atTop Real.tendsto_log_atTop

theorem _lemma4 :
    (fun N : ℕ => Real.log (Real.log N)) =o[Filter.atTop] (fun N : ℕ => Real.log N) := by
  exact Asymptotics.IsLittleO.comp_tendsto _lemma5 tendsto_natCast_atTop_atTop

theorem _lemma3 (c : ℝ) :
    (fun N : ℕ => Real.log N) =O[Filter.atTop]
      (fun N : ℕ => Real.log N - c * Real.log (Real.log N)) := by
  exact (_lemma4.const_mul_left c).right_isBigO_sub

theorem _lemma2 (c : ℝ) :
    (fun N : ℕ => Real.log N + c * Real.log (Real.log N)) =O[Filter.atTop]
      (fun N : ℕ => Real.log N) := by
  apply Asymptotics.IsBigO.add
  · exact Asymptotics.isBigO_refl _ _
  apply Asymptotics.IsBigO.const_mul_left
  apply loglog_bigO_log

theorem pi_le_id_div_log_of_eps (N : ℕ) (ε : ℝ) (_hε_pos : ε > 0) (hε : ε < 1) :
    π N ≤ 2 / (1 - ε) * N / Real.log N +
      3 * (N : ℝ) ^ (1 - ε) * (1 + (1 - ε) * Real.log N) ^ 3 := by
  by_cases hN : N = 0
  · rw [hN, primeCounting_zero]
    norm_num
    rw [Real.zero_rpow (by linarith : 1 - ε ≠ 0)]
  by_cases hN_one : N = 1
  · rw [hN_one, primeCounting_one]
    norm_num
  · have : 1 < (N : ℝ) ^ (1 - ε) := by
      apply Real.one_lt_rpow
      · norm_cast
        rw [Nat.one_lt_iff_ne_zero_and_ne_one]
        exact ⟨hN, hN_one⟩
      · linarith
    have h := pi_le_of_y N ((N : ℝ) ^ (1 - ε)) this
    rw [Real.log_rpow (by norm_cast; exact Nat.pos_of_ne_zero hN)] at h
    convert h using 1 <;> field_simp <;> ring

theorem pi_le_id_div_log (N : ℕ) :
    π N ≤ (4 : ℝ) * N / Real.log N +
      (3 : ℝ) * (N : ℝ) ^ (1 / 2 : ℝ) * (1 + (1 / 2) * Real.log N) ^ 3 := by
  have h := pi_le_id_div_log_of_eps N (1 / 2) (by linarith) (by linarith)
  apply le_trans h
  gcongr ?_ + ?_
  · norm_num
  · norm_num

theorem _lemma0 :
    (fun N : ℕ => 4 * N / Real.log N) =O[Filter.atTop]
      fun N : ℕ => N / Real.log N := by
  simp_rw [mul_div_assoc]
  apply Asymptotics.IsBigO.const_mul_left
  exact Asymptotics.isBigO_refl _ _

theorem _lemma7 :
    ((fun x : ℝ => 1 + 1 / 2 * Real.log x) ∘ fun N : ℕ => (N : ℝ)) =O[Filter.atTop]
      ((fun x : ℝ => x ^ (1 / 12 : ℝ)) ∘ fun N : ℕ => ↑N) := by
  apply Asymptotics.IsBigO.comp_tendsto (l := Filter.atTop)
  · apply Asymptotics.IsBigO.add
    · apply Asymptotics.IsBigO.of_bound'
      rw [Filter.eventually_iff, Filter.mem_atTop_sets]
      use 1
      intro x hx
      simp only [norm_one, Real.norm_eq_abs, Set.mem_setOf_eq]
      rw [Real.abs_rpow_of_nonneg (by linarith)]
      apply Real.one_le_rpow
      · rw [le_abs]
        left
        linarith
      · norm_num
    · apply (isLittleO_log_rpow_atTop (by norm_num)).isBigO.const_mul_left _
  · exact tendsto_natCast_atTop_atTop

theorem _lemma8 :
    ((fun x : ℝ => x ^ (1 / 2 : ℝ) * x ^ (1 / 4 : ℝ)) ∘ fun N : ℕ => (N : ℝ))
      =O[Filter.atTop] ((fun x : ℝ => x / Real.log x) ∘ fun N : ℕ => ↑N) := by
  apply Asymptotics.IsBigO.comp_tendsto (l := Filter.atTop)
  · simp_rw [div_eq_mul_inv]
    trans (fun x => x * x ^ (-1 / 4 : ℝ))
    · apply Asymptotics.IsBigO.of_bound'
      rw [Filter.eventually_iff, Filter.mem_atTop_sets]
      use 1
      intro x hx
      simp only [norm_mul, Real.norm_eq_abs, Set.mem_setOf_eq]
      rw [← abs_mul, ← abs_mul]
      apply le_of_eq
      apply congr_arg
      trans (x ^ (1 : ℝ) * x ^ (-1 / 4 : ℝ))
      · rw [← Real.rpow_add (by linarith), ← Real.rpow_add (by linarith)]
        norm_num
      · rw [Real.rpow_one]
    · apply Asymptotics.IsBigO.mul
      · apply Asymptotics.isBigO_refl
      trans (fun x => (x ^ (1 / 4 : ℝ))⁻¹)
      · apply Asymptotics.IsBigO.of_bound'
        rw [Filter.eventually_iff, Filter.mem_atTop_sets]
        use 1
        intro x hx
        simp only [Real.norm_eq_abs, Set.mem_setOf_eq]
        rw [neg_div, Real.rpow_neg (by linarith : 0 ≤ x), abs_inv]
      apply Asymptotics.IsBigO.inv_rev
      · apply (isLittleO_log_rpow_atTop (by norm_num)).isBigO
      · rw [Filter.eventually_iff, Filter.mem_atTop_sets]
        use 100
        intro x hx
        rw [Set.mem_setOf_eq]
        intro hlog
        exfalso
        have hlog_pos : 0 < Real.log x := Real.log_pos (by linarith)
        linarith
  · exact tendsto_natCast_atTop_atTop

theorem _lemma1 :
    (fun N : ℕ => (3 : ℝ) * (N : ℝ) ^ (1 / 2 : ℝ) *
      (1 + (1 / 2) * Real.log N) ^ 3) =O[Filter.atTop]
      fun N : ℕ => N / Real.log N := by
  simp_rw [mul_assoc]
  apply Asymptotics.IsBigO.const_mul_left
  trans (fun N : ℕ => (N : ℝ) ^ (1 / 2 : ℝ) * (N : ℝ) ^ (1 / 4 : ℝ))
  · have h0 : (fun N : ℕ => (N : ℝ) ^ (1 / 2 : ℝ)) =O[Filter.atTop]
        (fun N : ℕ => (N : ℝ) ^ (1 / 2 : ℝ)) := by
      apply Asymptotics.isBigO_refl
    have h1 : (fun N : ℕ => (1 + 1 / 2 * Real.log N) ^ 3) =O[Filter.atTop]
        (fun N : ℕ => (N : ℝ) ^ (1 / 4 : ℝ)) := by
      trans (fun N : ℕ => ((N : ℝ) ^ (1 / 12 : ℝ)) ^ 3)
      · apply Asymptotics.IsBigO.pow
        apply _lemma7
      · simp_rw [← Real.rpow_natCast]
        conv => { lhs; ext N; rw [← Real.rpow_mul (Nat.cast_nonneg N)] }
        norm_num
        apply Asymptotics.isBigO_refl
    apply h0.mul h1
  · apply _lemma8

lemma _lemma9 :
    (fun N : ℕ => (π N : ℝ)) =O[Filter.atTop]
      (fun N : ℕ => 4 * N / Real.log N +
        3 * (N : ℝ) ^ (1 / 2 : ℝ) * (1 + (1 / 2) * Real.log N) ^ 3) := by
  apply Asymptotics.isBigO_of_le
  intro N
  simp_rw [RCLike.norm_natCast, Nat.cast_ofNat, Real.norm_eq_abs]
  apply le_trans _ (le_abs_self _)
  apply pi_le_id_div_log N


theorem pi_ll :
    (fun N : ℕ => (π N : ℝ)) =O[Filter.atTop] (fun N : ℕ => N / Real.log N) := by
  trans (fun N : ℕ => 4 * N / Real.log N +
      3 * (N : ℝ) ^ (1 / 2 : ℝ) * (1 + (1 / 2) * Real.log N) ^ 3)
  · exact _lemma9
  · apply Asymptotics.IsBigO.add
    · simp_rw [mul_div_assoc]
      apply Asymptotics.IsBigO.const_mul_left
      apply Asymptotics.isBigO_refl
    · apply _lemma1

theorem pi_le_mul : ∃ N C, ∀ n ≥ N, π n ≤ C*n/Real.log n := by
  obtain ⟨C, h⟩ := pi_ll.bound
  rw [Filter.eventually_iff, Filter.mem_atTop_sets] at h
  obtain ⟨N, h⟩ := h
  simp only [ge_iff_le, RCLike.norm_natCast, norm_div, Real.norm_eq_abs, Set.mem_setOf_eq] at h
  use N
  use C
  intro n
  specialize h n
  rw [abs_of_nonneg (Real.log_natCast_nonneg n)] at h
  intro hnN
  rw [mul_div_assoc]
  apply h (by linarith only [hnN])

end PrimeUpperBound
end



-- === Inlined from SelbergSieve4.Applications.BrunTitchmarsh ===
/-
Copyright (c) 2026 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arend Mellendijk
-/

/-!
# LeanPool.SelbergSieve4.Applications.BrunTitchmarsh
-/

noncomputable section
open PrimeUpperBound
open scoped Nat ArithmeticFunction.zeta ArithmeticFunction.Moebius ArithmeticFunction.omega
  BigOperators

namespace BrunTitchmarsh

/-- LPSieve that removes primes at most `z` from the interval `[x, x + y]`. -/
def primeInterSieve (x y z : ℝ) (hz : 1 ≤ z) : LPSelbergSieve := {
  support := Finset.Icc (Nat.ceil x) (Nat.floor (x+y))
  prodPrimes := primorial (Nat.floor z)
  prodPrimes_squarefree := primorial_squarefree _
  weights := fun _ => 1
  weights_nonneg := fun _ => zero_le_one
  totalMass := y
  nu := (ζ : ArithmeticFunction ℝ).pdiv .id
  nu_mult := by arith_mult
  nu_pos_of_prime := fun p hp _ => by
    simp[if_neg hp.ne_zero, Nat.pos_of_ne_zero hp.ne_zero]
  nu_lt_one_of_prime := fun p hp _ => by
    simpa [hp.ne_zero] using
      (inv_lt_one_of_one_lt₀ (by norm_cast; exact hp.one_lt) : (p : ℝ)⁻¹ < 1)
  level := z
  one_le_level := hz
}

/-- Number of primes in the real interval `[a, b]`. -/
def primesBetween (a b : ℝ) : ℕ :=
  (Finset.Icc (Nat.ceil a) (Nat.floor b)).filter (Nat.Prime) |>.card

theorem primesBetween_eq_ncard {a b : ℝ} (hb : 0 ≤ b) :
    primesBetween a b = Set.ncard {p : ℕ | a ≤ p ∧ p ≤ b ∧ p.Prime} := by
  unfold primesBetween
  rw [← Set.ncard_coe_finset]
  congr
  ext p
  simp only [Finset.coe_filter, Finset.mem_Icc, Nat.ceil_le, Nat.le_floor_iff hb,
    Set.mem_setOf_eq, and_assoc]

variable (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 1 ≤ z)

open Classical in
theorem siftedSum_eq_card :
    (primeInterSieve x y z hz).siftedSum =
      ((Finset.Icc (Nat.ceil x) (Nat.floor (x+y))).filter
        (fun d => ∀ p : ℕ, p.Prime → p ≤ z → ¬p ∣ d)).card := by
  apply PrimeUpperBound.siftedSum_eq
  · exact fun _ _ => rfl
  · exact hz
  · rfl

open Classical in
theorem primesBetween_subset :
  (Finset.Icc (Nat.ceil x) (Nat.floor (x+y))).filter (Nat.Prime) ⊆
    (Finset.Icc (Nat.ceil x) (Nat.floor (x+y))).filter
      (fun d => ∀ p : ℕ, p.Prime → p ≤ z → ¬p ∣ d) ∪
    (Finset.Icc 1 (Nat.floor z)) := by
  intro p hp_mem
  simp only [Finset.mem_filter, Finset.mem_Icc] at hp_mem
  rw [Finset.mem_union]
  rcases hp_mem with ⟨hp_range, hp⟩
  by_cases hpz : p ≤ z
  · right
    exact Finset.mem_Icc.mpr ⟨hp.one_le, (Nat.le_floor_iff (by linarith)).mpr hpz⟩
  · left
    refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr hp_range, ?_⟩
    intro q hq hqz
    rw[hp.dvd_iff_eq (hq.ne_one)]
    rintro rfl
    exact hpz hqz

theorem primesBetween_le_siftedSum_add :
    primesBetween x (x+y) ≤ (primeInterSieve x y z hz).siftedSum + z := by
  classical
  trans ↑(((Finset.Icc (Nat.ceil x) (Nat.floor (x+y))).filter
      (fun d => ∀ p : ℕ, p.Prime → p ≤ z → ¬p ∣ d)) ∪
        (Finset.Icc 1 (Nat.floor z))).card
  · rw[primesBetween]
    norm_cast
    apply Finset.card_le_card
    apply primesBetween_subset
  trans ↑((Finset.Icc (Nat.ceil x) (Nat.floor (x+y))).filter
      (fun d => ∀ p : ℕ, p.Prime → p ≤ z → ¬p ∣ d)).card
    + ↑(Finset.Icc 1 (Nat.floor z)).card
  · norm_cast
    apply Finset.card_union_le
  rw[siftedSum_eq_card]
  gcongr
  rw[Nat.card_Icc]
  simp only [add_tsub_cancel_right]
  apply Nat.floor_le
  linarith

section Remainder

theorem Ioc_filter_dvd_eq (d a b : ℕ) (hd : d ≠ 0) :
  Finset.filter (fun x => d ∣ x) (Finset.Ioc a b) =
    Finset.image (fun x => x * d) (Finset.Ioc (a / d) (b / d)) := by
  ext n
  simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_image]
  constructor
  · intro hn
    use  n/d
    rcases hn with ⟨⟨han, hnb⟩, hd⟩
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · exact Nat.div_lt_div_of_lt_of_dvd hd han
    · exact Nat.div_le_div_right hnb
    · exact Nat.div_mul_cancel hd
  · rintro ⟨r, ⟨ha, ha'⟩, rfl⟩
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · refine (Nat.div_lt_iff_lt_mul ?_).mp ha
      omega
    · exact Nat.mul_le_of_le_div d r b ha'
    · exact Nat.dvd_mul_left d r

theorem card_Ioc_filter_dvd (d a b : ℕ) (hd : d ≠ 0) :
    (Finset.filter (fun x => d ∣ x) (Finset.Ioc a b)).card = b / d - a / d  := by
  rw [Ioc_filter_dvd_eq _ _ _ hd]
  rw [Finset.card_image_of_injective _ <| mul_left_injective₀ hd]
  simp

theorem multSum_eq (hx : 0 < x) (d : ℕ) (hd : d ≠ 0) :
    (primeInterSieve x y z hz).multSum d = ↑(⌊x + y⌋₊ / d - (⌈x⌉₊ - 1) / d) := by
  unfold LPSieve.multSum
  rw[primeInterSieve]
  simp only [Finset.sum_boole, Nat.cast_inj]
  trans ↑(Finset.Ioc (Nat.ceil x - 1) (Nat.floor (x+y)) |>.filter (d ∣ ·) |>.card)
  · rw [← Finset.Icc_succ_left_eq_Ioc]
    congr
    simpa [Nat.pred_eq_sub_one] using
      (Nat.succ_pred_eq_of_pos (Nat.ceil_pos.mpr hx)).symm
  · rw[card_Ioc_filter_dvd _ _ _ hd]

theorem rem_eq (hx : 0 < x) (d : ℕ) (hd : d ≠ 0) :
    (primeInterSieve x y z hz).rem d =
      ↑(⌊x + y⌋₊ / d - (⌈x⌉₊ - 1) / d) - (↑d)⁻¹ * y := by
  unfold LPSieve.rem
  rw[multSum_eq x y z hz hx d hd]
  simp [primeInterSieve, if_neg hd]

theorem natCeil_le_self_add_one (x : ℝ) (hx : 0 ≤ x) : Nat.ceil x ≤ x + 1 := by
  trans Nat.floor x + 1
  · norm_cast
    exact Nat.ceil_le_floor_add_one x
  gcongr
  apply Nat.floor_le hx

theorem floor_approx (x : ℝ) (hx : 0 ≤ x) : ∃ C, |C| ≤ 1 ∧  ↑((Nat.floor x)) = x + C := by
  use ↑(Nat.floor x) - x
  constructor
  · rw[abs_le]
    constructor
    · simp only [neg_le_sub_iff_le_add]
      linarith [Nat.lt_floor_add_one x]
    · simp only [tsub_le_iff_right]
      linarith [Nat.floor_le hx]
  · ring

theorem ceil_approx (x : ℝ) (hx : 0 ≤ x) : ∃ C, |C| ≤ 1 ∧  ↑((Nat.ceil x)) = x + C := by
  use ↑(Nat.ceil x) - x
  constructor
  · rw[abs_le]
    constructor
    · simp only [neg_le_sub_iff_le_add]
      linarith [Nat.le_ceil x]
    · simp only [tsub_le_iff_right]
      rw[add_comm]
      exact natCeil_le_self_add_one x hx
  · ring

theorem nat_div_approx (a b : ℕ) : ∃ C, |C| ≤ 1 ∧ ↑(a/b) = (a/b : ℝ) + C := by
  rw[←Nat.floor_div_eq_div (K:=ℝ)]
  apply floor_approx (a/b:ℝ) (by positivity)

theorem floor_div_approx (x : ℝ) (hx : 0 ≤ x) (d : ℕ) :
    ∃ C, |C| ≤ 2 ∧  ↑((Nat.floor x)/d) = x / d + C := by
  by_cases hd : d = 0
  · simp [hd]
  obtain ⟨C₁, hC₁_le, hC₁⟩ := nat_div_approx (Nat.floor x) d
  obtain ⟨C₂, hC₂_le, hC₂⟩ := floor_approx x hx
  rw[hC₁, hC₂]
  use  C₁ + C₂/d
  refine ⟨?_, by ring⟩
  have : |C₁ + C₂/d| ≤ |C₁| + |C₂/d| := abs_add_le C₁ (C₂ / ↑d)
  have : |C₂/d| ≤ |C₂| := by
    rw[abs_div]
    apply div_le_self
    · exact abs_nonneg C₂
    · simp only [Nat.abs_cast, Nat.one_le_cast]
      omega
  linarith

theorem abs_rem_le (hx : 0 < x) (hy : 0 < y) {d : ℕ} (hd : d ≠ 0) :
    |(primeInterSieve x y z hz).rem d| ≤ 5 := by
  rw[rem_eq x y z hz hx _ hd]
  have hpush : ↑(⌊x + y⌋₊ / d - (⌈x⌉₊ - 1) / d) =
      (↑(⌊x + y⌋₊ / d) - ↑((⌈x⌉₊ - 1) / d) : ℝ) := by
    rw [Nat.cast_sub]
    gcongr
    rw[Nat.le_floor_iff]
    · rw[←add_le_add_iff_right 1]
      norm_cast
      rw [Nat.sub_add_cancel]
      · linarith [natCeil_le_self_add_one x (le_of_lt hx)]
      · simp [hx]
    · linarith
  rw[hpush]
  obtain ⟨C₁, hC₁_le, hC₁⟩ := floor_div_approx (x + y) (by linarith) d
  obtain ⟨C₂, hC₂_le, hC₂⟩ := nat_div_approx (Nat.ceil x - 1) d
  obtain ⟨C₃, hC₃_le, hC₃⟩ := ceil_approx (x) (by linarith)
  rw[hC₁, hC₂, Nat.cast_sub, hC₃]
  · ring_nf
    have hinv : |(d:ℝ)⁻¹| ≤ 1 := by
      rw[abs_inv]
      simp only [Nat.abs_cast]
      apply Nat.cast_inv_le_one
    have hmul : |(↑d)⁻¹*C₃| ≤ |C₃| := by
      rw[inv_mul_eq_div, abs_div]
      apply div_le_self
      · exact abs_nonneg _
      · simp only [Nat.abs_cast, Nat.one_le_cast]
        omega
    calc
      |(↑d)⁻¹ - (↑d)⁻¹ * C₃ + C₁ - C₂| =
        |(↑d)⁻¹ - (↑d)⁻¹ * C₃ + (C₁ - C₂)| := by ring_nf
      _ ≤ |(↑d)⁻¹ - (↑d)⁻¹*C₃| + |C₁ - C₂| := abs_add_le _ _
      _ ≤ (|(↑d)⁻¹| + |(↑d)⁻¹*C₃|) + (|C₁| + |C₂|) := by
        exact add_le_add (abs_sub _ _) (abs_sub _ _)
      _ ≤ (1 + |C₃|) + (2 + 1) := by
        gcongr
      _ ≤ 5 := by
        linarith
  · simp [hx]

end Remainder

theorem boudingSum_ge :
    (primeInterSieve x y z hz).selbergBoundingSum ≥ Real.log z / 2 := by
  apply boundingSum_ge_log
  · rfl
  · intro p hpp hp
    erw [prime_dvd_primorial_iff]
    · exact Nat.le_floor hp
    · exact hpp

theorem primeSieve_rem_sum_le (hx : 0 < x) (hy : 0 < y) :
    ∑ d ∈ (primeInterSieve x y z hz).prodPrimes.divisors,
      (if (d : ℝ) ≤ z then (3:ℝ) ^ ω d * |(primeInterSieve x y z hz).rem d| else 0)
      ≤ 5 * z * (1+Real.log z)^3 := by
  apply rem_sum_le_of_const (primeInterSieve x y z hz) 5 ?_
  intro d hd
  exact abs_rem_le x y z hz hx hy (ne_of_gt hd)

theorem siftedSum_le (hx : 0 < x) (hy : 0 < y) (hz : 1 < z) :
    (primeInterSieve x y z (le_of_lt hz)).siftedSum ≤
      2 * y / Real.log z + 5 * z * (1+Real.log z)^3  := by
  apply le_trans (LPSelbergSieve.selberg_bound_simple ..)
  calc _ ≤ y / (Real.log z / 2) + 5 * z * (1+Real.log z)^3 := ?_
       _ = _ := by ring
  gcongr
  · linarith [Real.log_pos hz]
  · rfl
  · apply boudingSum_ge
  · apply primeSieve_rem_sum_le x y z (le_of_lt hz) hx hy

theorem primesBetween_le (hx : 0 < x) (hy : 0 < y) (hz : 1 < z) :
    primesBetween x (x+y) ≤ 2 * y / Real.log z + 6 * z * (1+Real.log z)^3 := by
  have : z ≤ z * (1+Real.log z)^3 := by
    apply le_mul_of_one_le_right
    · linarith
    apply one_le_pow₀
    linarith [Real.log_nonneg (by linarith)]
  linarith [siftedSum_le x y z hx hy hz,
    primesBetween_le_siftedSum_add x y z (le_of_lt hz)]

end BrunTitchmarsh

end -- close `noncomputable section` opened in Applications.BrunTitchmarsh



-- === Inlined from SelbergSieve4.MainResults ===
/-
Copyright (c) 2026 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arend Mellendijk
-/

/-!
# LeanPool.SelbergSieve4.MainResults
-/

section LPSieveMainResults

open scoped BigOperators ArithmeticFunction.zeta ArithmeticFunction.Moebius ArithmeticFunction.omega
  LPSieve Nat Nat.Prime
end LPSieveMainResults

end Erdos696
