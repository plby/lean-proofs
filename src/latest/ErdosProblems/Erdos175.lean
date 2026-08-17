/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This file formalizes the resolution of Erdős Problem 175.

Mathematical sources:
* A. Granville and O. Ramaré, "Explicit bounds on exponential sums and the
  scarcity of squarefree binomial coefficients", Mathematika 43 (1996),
  73--107.
* G. Velammal, "Is the binomial coefficient (2n choose n) squarefree?",
  Hardy--Ramanujan Journal 18 (1995), 23--45.

The detailed reconstruction and declaration map are in `tex/175.tex`.

Progress log:
* Phase 1 complete: the Granville--Ramaré argument and all formal dependencies
  are recorded in `tex/175.tex`.
* Phase 2 verified here: Kummer's binary reduction and a kernel-checked carry
  certificate for every `3 ≤ k < 8192`.
* The companion modules in `Erdos175/` formalize the explicit large-`n`
  estimates from Sections 7--10 of Granville--Ramaré.
-/

import Mathlib
import ErdosProblems.Erdos175.FinalLarge

namespace Erdos175

open Nat

/-- The central binomial coefficient. -/
def centralBinom (n : ℕ) : ℕ := Nat.choose (2 * n) n

/-- Every central binomial coefficient is positive. -/
lemma centralBinom_pos (n : ℕ) : 0 < centralBinom n := by
  exact Nat.choose_pos (by omega)

/-- The base-two digit sum of a positive natural number is positive. -/
lemma digitSum_two_pos {n : ℕ} (hn : n ≠ 0) : 0 < (Nat.digits 2 n).sum := by
  have hnil : Nat.digits 2 n ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr hn
  have hlast : (Nat.digits 2 n).getLast hnil ≠ 0 := Nat.getLast_digit_ne_zero 2 hn
  have hmem : (Nat.digits 2 n).getLast hnil ∈ Nat.digits 2 n := List.getLast_mem hnil
  have hle := List.single_le_sum (fun x _ => Nat.zero_le x) _ hmem
  omega

/-- Kummer's identity at two: the two-adic valuation of the central binomial
coefficient is the binary digit sum of its index. -/
lemma padicValNat_two_centralBinom (n : ℕ) :
    padicValNat 2 (centralBinom n) = (Nat.digits 2 n).sum := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcb : centralBinom n = Nat.choose (n + n) n := by
    rw [centralBinom, two_mul]
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp [centralBinom]
  have hdd : (Nat.digits 2 (n + n)).sum = (Nat.digits 2 n).sum := by
    have h2 : n + n = 2 ^ 1 * n := by ring
    rw [h2, Nat.digits_base_pow_mul (by norm_num) hn]
    simp
  have key :=
    sub_one_mul_padicValNat_choose_eq_sub_sum_digits' (p := 2) (k := n) (n := n)
  rw [hcb]
  rw [hdd] at key
  simp only [show (2 : ℕ) - 1 = 1 from rfl, one_mul] at key
  omega

/-- A positive natural has binary digit sum one exactly when it is a power of
two. -/
lemma digitSum_two_eq_one_iff {n : ℕ} (hn : 0 < n) :
    (Nat.digits 2 n).sum = 1 ↔ ∃ k, n = 2 ^ k := by
  constructor
  · intro hs
    obtain ⟨k, m, hm, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hn.ne'
    have hmpos : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; simp at hn)
    rw [Nat.digits_base_pow_mul (by norm_num) hmpos] at hs
    simp only [List.sum_append, List.sum_replicate, smul_eq_mul, Nat.mul_zero,
      zero_add] at hs
    have hmod : m % 2 = 1 := Nat.odd_iff.mp hm
    rw [Nat.digits_of_two_le_of_pos (by norm_num) hmpos, hmod, List.sum_cons] at hs
    have hzero : (Nat.digits 2 (m / 2)).sum = 0 := by omega
    have hm2 : m / 2 = 0 := by
      by_contra h
      exact absurd hzero (digitSum_two_pos h).ne'
    have hm1 : m = 1 := by omega
    exact ⟨k, by rw [hm1, mul_one]⟩
  · rintro ⟨k, rfl⟩
    rw [show (2 : ℕ) ^ k = 2 ^ k * 1 from (mul_one _).symm,
      Nat.digits_base_pow_mul (by norm_num) one_pos,
      Nat.digits_of_two_le_of_pos (by norm_num) one_pos]
    simp

/-- Except at powers of two, the central binomial coefficient is divisible by
four. -/
lemma four_dvd_centralBinom_iff (n : ℕ) (hn : 2 ≤ n) :
    4 ∣ centralBinom n ↔ ¬ ∃ k : ℕ, n = 2 ^ k := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpos : 0 < n := by omega
  have hcb0 : centralBinom n ≠ 0 := (centralBinom_pos n).ne'
  have hdvd : 4 ∣ centralBinom n ↔ 2 ≤ padicValNat 2 (centralBinom n) := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num]
    exact padicValNat_dvd_iff_le hcb0
  rw [hdvd, padicValNat_two_centralBinom]
  have hs1 : 0 < (Nat.digits 2 n).sum := digitSum_two_pos hpos.ne'
  rw [show (¬ ∃ k, n = 2 ^ k) ↔ (Nat.digits 2 n).sum ≠ 1 from
    (digitSum_two_eq_one_iff hpos).not.symm]
  omega

/-- The number of carries in the base-`p` addition `n + n`.  This is written
in exactly the finite form used by Mathlib's Kummer theorem. -/
def centralCarryCount (p n : ℕ) : ℕ :=
  ((Finset.Ico 1 (Nat.log p (n + n) + 1)).filter fun i =>
    p ^ i ≤ n % p ^ i + n % p ^ i).card

/-- Kummer identifies `centralCarryCount` with the valuation of the central
binomial coefficient. -/
lemma padicValNat_centralBinom_eq_centralCarryCount
    {p : ℕ} (hp : p.Prime) (n : ℕ) :
    padicValNat p (centralBinom n) = centralCarryCount p n := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [centralBinom, show 2 * n = n + n by omega]
  exact padicValNat_choose' (Nat.lt_succ_self _)

/-- The small prime used by the finite Granville--Ramaré certificate. -/
def finitePrime (k : ℕ) : ℕ :=
  if k = 6 then 5 else if k = 8 then 7 else 3

lemma finitePrime_prime (k : ℕ) : (finitePrime k).Prime := by
  simp only [finitePrime]
  split_ifs <;> norm_num

/-- A bounded carry count used to make the finite certificate kernel-checkable.
The first twenty-eight digit positions suffice throughout the certified range. -/
def lowCarryCount (p n : ℕ) : ℕ :=
  ((Finset.Icc 1 28).filter fun i =>
    p ^ i ≤ n % p ^ i + n % p ^ i).card

/-- Every carry detected in the first twenty-eight positions is one of the
carries counted by Kummer's full formula. -/
lemma lowCarryCount_le_centralCarryCount {p n : ℕ} (hp : 2 ≤ p) (hn : n ≠ 0) :
    lowCarryCount p n ≤ centralCarryCount p n := by
  apply Finset.card_le_card
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_Icc] at hi
  simp only [Finset.mem_filter, Finset.mem_Ico]
  refine ⟨⟨hi.1.1, ?_⟩, hi.2⟩
  have hpow : p ^ i ≤ n + n := by
    calc
      p ^ i ≤ n % p ^ i + n % p ^ i := hi.2
      _ ≤ n + n := Nat.add_le_add (Nat.mod_le _ _) (Nat.mod_le _ _)
  have hlog : i ≤ Nat.log p (n + n) :=
    (Nat.le_log_iff_pow_le (by omega) (by omega)).2 hpow
  omega

/-- The reflected Granville--Ramaré computation, split into `26 × 64` cases
so that `decide` produces a proof term checked by the Lean kernel. -/
lemma finite_low_carry_check :
    ∀ b : Fin 26, ∀ j : Fin 64,
      let k := 64 * (b : ℕ) + (j : ℕ)
      3 ≤ k → k < 1617 →
      2 ≤ lowCarryCount (finitePrime k) (npowBinRecAuto k (2 : ℕ)) := by
  decide

/-- The repeated-squaring evaluator used by the certificate agrees with
ordinary natural exponentiation. -/
lemma npowBinRecAuto_two_eq (k : ℕ) : npowBinRecAuto k (2 : ℕ) = 2 ^ k := by
  rw [← npowRec_eq_npowBinRec]
  induction k with
  | zero => rfl
  | succ k ih =>
      change npowRec k 2 * 2 = Nat.pow 2 k * 2
      exact congrArg (fun x : ℕ => x * 2) ih

/-- The same bounded certificate through exponent `1727`.  This slightly
larger range is useful with an elementary effective Chebyshev estimate whose
constants are weaker than the published sharp estimate. -/
lemma finite_low_carry_check_1728 :
    ∀ b : Fin 27, ∀ j : Fin 64,
      let k := 64 * (b : ℕ) + (j : ℕ)
      3 ≤ k → k < 1728 →
      2 ≤ lowCarryCount (finitePrime k) (npowBinRecAuto k (2 : ℕ)) := by
  decide

/-- Every exponent below the alternate effective cutoff has at least two
certified carries. -/
lemma finite_carry_check_1728 :
    ∀ k : Fin 1728, 3 ≤ (k : ℕ) →
      2 ≤ centralCarryCount (finitePrime k) (2 ^ (k : ℕ)) := by
  intro k hk3
  let b : Fin 27 := ⟨(k : ℕ) / 64, by omega⟩
  let j : Fin 64 := ⟨(k : ℕ) % 64, Nat.mod_lt _ (by norm_num)⟩
  have hkdecomp : 64 * (b : ℕ) + (j : ℕ) = (k : ℕ) := by
    dsimp [b, j]
    omega
  have hlow : 2 ≤ lowCarryCount (finitePrime k) (2 ^ (k : ℕ)) := by
    simpa only [hkdecomp, npowBinRecAuto_two_eq] using
      finite_low_carry_check_1728 b j (by omega) (by omega)
  exact hlow.trans (lowCarryCount_le_centralCarryCount (by
    simp only [finitePrime]
    split_ifs <;> omega) (by positivity))

/-- First kernel-checkable block of the finite certificate through the final
weakened analytic cutoff. -/
lemma finite_low_carry_check_2304_0 :
    ∀ a : Fin 5, ∀ b : Fin 4, ∀ j : Fin 64,
      let k := 256 * (a : ℕ) + 64 * (b : ℕ) + (j : ℕ)
      3 ≤ k →
      2 ≤ lowCarryCount (finitePrime k) (npowBinRecAuto k (2 : ℕ)) := by
  decide

/-- Second kernel-checkable block of the finite certificate through the final
weakened analytic cutoff. -/
lemma finite_low_carry_check_2304_1 :
    ∀ a : Fin 4, ∀ b : Fin 4, ∀ j : Fin 64,
      let k := 1280 + 256 * (a : ℕ) + 64 * (b : ℕ) + (j : ℕ)
      3 ≤ k →
      2 ≤ lowCarryCount (finitePrime k) (npowBinRecAuto k (2 : ℕ)) := by
  decide

/-- The two reflected blocks cover all exponents below `2304`. -/
lemma finite_low_carry_check_2304 :
    ∀ a : Fin 9, ∀ b : Fin 4, ∀ j : Fin 64,
      let k := 256 * (a : ℕ) + 64 * (b : ℕ) + (j : ℕ)
      3 ≤ k →
      2 ≤ lowCarryCount (finitePrime k) (npowBinRecAuto k (2 : ℕ)) := by
  intro a b j
  dsimp only
  by_cases ha : (a : ℕ) < 5
  · let a0 : Fin 5 := ⟨a, ha⟩
    simpa [a0] using finite_low_carry_check_2304_0 a0 b j
  · let a1 : Fin 4 := ⟨(a : ℕ) - 5, by omega⟩
    have hae :
        1280 + 256 * (a1 : ℕ) + 64 * (b : ℕ) + (j : ℕ) =
          256 * (a : ℕ) + 64 * (b : ℕ) + (j : ℕ) := by
      dsimp [a1]
      omega
    simpa only [hae] using finite_low_carry_check_2304_1 a1 b j

/-- Every exponent below `2304` has at least two certified carries. -/
lemma finite_carry_check_2304 :
    ∀ k : Fin 2304, 3 ≤ (k : ℕ) →
      2 ≤ centralCarryCount (finitePrime k) (2 ^ (k : ℕ)) := by
  intro k hk3
  let a : Fin 9 := ⟨(k : ℕ) / 256, by omega⟩
  let b : Fin 4 := ⟨((k : ℕ) % 256) / 64, by omega⟩
  let j : Fin 64 := ⟨(k : ℕ) % 64, Nat.mod_lt _ (by norm_num)⟩
  have hkdecomp :
      256 * (a : ℕ) + 64 * (b : ℕ) + (j : ℕ) = (k : ℕ) := by
    dsimp [a, b, j]
    omega
  have hlow : 2 ≤ lowCarryCount (finitePrime k) (2 ^ (k : ℕ)) := by
    simpa only [hkdecomp, npowBinRecAuto_two_eq] using
      finite_low_carry_check_2304 a b j (by omega)
  exact hlow.trans (lowCarryCount_le_centralCarryCount (by
    simp only [finitePrime]
    split_ifs <;> omega) (by positivity))

/-- Three reflected blocks cover the range below the robust cutoff `2816`
without changing Lean's default proof limits. -/
lemma finite_low_carry_check_2816_0 :
    ∀ a : Fin 4, ∀ b : Fin 4, ∀ j : Fin 64,
      let k := 256 * (a : ℕ) + 64 * (b : ℕ) + (j : ℕ)
      3 ≤ k →
      2 ≤ lowCarryCount (finitePrime k) (npowBinRecAuto k (2 : ℕ)) := by
  decide

lemma finite_low_carry_check_2816_1 :
    ∀ a : Fin 4, ∀ b : Fin 4, ∀ j : Fin 64,
      let k := 1024 + 256 * (a : ℕ) + 64 * (b : ℕ) + (j : ℕ)
      3 ≤ k →
      2 ≤ lowCarryCount (finitePrime k) (npowBinRecAuto k (2 : ℕ)) := by
  decide

lemma finite_low_carry_check_2816_2 :
    ∀ a : Fin 3, ∀ b : Fin 4, ∀ j : Fin 64,
      let k := 2048 + 256 * (a : ℕ) + 64 * (b : ℕ) + (j : ℕ)
      3 ≤ k →
      2 ≤ lowCarryCount (finitePrime k) (npowBinRecAuto k (2 : ℕ)) := by
  decide

lemma finite_low_carry_check_2816 :
    ∀ a : Fin 11, ∀ b : Fin 4, ∀ j : Fin 64,
      let k := 256 * (a : ℕ) + 64 * (b : ℕ) + (j : ℕ)
      3 ≤ k →
      2 ≤ lowCarryCount (finitePrime k) (npowBinRecAuto k (2 : ℕ)) := by
  intro a b j
  dsimp only
  by_cases ha : (a : ℕ) < 4
  · let a0 : Fin 4 := ⟨a, ha⟩
    simpa [a0] using finite_low_carry_check_2816_0 a0 b j
  · by_cases ha' : (a : ℕ) < 8
    · let a1 : Fin 4 := ⟨(a : ℕ) - 4, by omega⟩
      have hae :
          1024 + 256 * (a1 : ℕ) + 64 * (b : ℕ) + (j : ℕ) =
            256 * (a : ℕ) + 64 * (b : ℕ) + (j : ℕ) := by
        dsimp [a1]
        omega
      simpa only [hae] using finite_low_carry_check_2816_1 a1 b j
    · let a2 : Fin 3 := ⟨(a : ℕ) - 8, by omega⟩
      have hae :
          2048 + 256 * (a2 : ℕ) + 64 * (b : ℕ) + (j : ℕ) =
            256 * (a : ℕ) + 64 * (b : ℕ) + (j : ℕ) := by
        dsimp [a2]
        omega
      simpa only [hae] using finite_low_carry_check_2816_2 a2 b j

/-- Every exponent below the robust analytic cutoff has at least two
certified carries. -/
lemma finite_carry_check_2816 :
    ∀ k : Fin 2816, 3 ≤ (k : ℕ) →
      2 ≤ centralCarryCount (finitePrime k) (2 ^ (k : ℕ)) := by
  intro k hk3
  let a : Fin 11 := ⟨(k : ℕ) / 256, by omega⟩
  let b : Fin 4 := ⟨((k : ℕ) % 256) / 64, by omega⟩
  let j : Fin 64 := ⟨(k : ℕ) % 64, Nat.mod_lt _ (by norm_num)⟩
  have hkdecomp :
      256 * (a : ℕ) + 64 * (b : ℕ) + (j : ℕ) = (k : ℕ) := by
    dsimp [a, b, j]
    omega
  have hlow : 2 ≤ lowCarryCount (finitePrime k) (2 ^ (k : ℕ)) := by
    simpa only [hkdecomp, npowBinRecAuto_two_eq] using
      finite_low_carry_check_2816 a b j (by omega)
  exact hlow.trans (lowCarryCount_le_centralCarryCount (by
    simp only [finitePrime]
    split_ifs <;> omega) (by positivity))

/- The final finite certificate is split into eight independent blocks of
`1024 = 4 * 4 * 64` exponents.  Keeping each reflected proposition this small
lets ordinary `decide` construct a proof term under Lean's default limits. -/
lemma finite_low_carry_check_8192_0 :
    ∀ a : Fin 4, ∀ b : Fin 4, ∀ j : Fin 64,
      let k := 256 * (a : ℕ) + 64 * (b : ℕ) + (j : ℕ)
      3 ≤ k → 2 ≤ lowCarryCount (finitePrime k) (npowBinRecAuto k (2 : ℕ)) := by
  decide

lemma finite_low_carry_check_8192_1 :
    ∀ a : Fin 4, ∀ b : Fin 4, ∀ j : Fin 64,
      let k := 1024 + 256 * (a : ℕ) + 64 * (b : ℕ) + (j : ℕ)
      3 ≤ k → 2 ≤ lowCarryCount (finitePrime k) (npowBinRecAuto k (2 : ℕ)) := by
  decide

lemma finite_low_carry_check_8192_2 :
    ∀ a : Fin 4, ∀ b : Fin 4, ∀ j : Fin 64,
      let k := 2048 + 256 * (a : ℕ) + 64 * (b : ℕ) + (j : ℕ)
      3 ≤ k → 2 ≤ lowCarryCount (finitePrime k) (npowBinRecAuto k (2 : ℕ)) := by
  decide

lemma finite_low_carry_check_8192_3 :
    ∀ a : Fin 4, ∀ b : Fin 4, ∀ j : Fin 64,
      let k := 3072 + 256 * (a : ℕ) + 64 * (b : ℕ) + (j : ℕ)
      3 ≤ k → 2 ≤ lowCarryCount (finitePrime k) (npowBinRecAuto k (2 : ℕ)) := by
  decide

lemma finite_low_carry_check_8192_4 :
    ∀ a : Fin 4, ∀ b : Fin 4, ∀ j : Fin 64,
      let k := 4096 + 256 * (a : ℕ) + 64 * (b : ℕ) + (j : ℕ)
      3 ≤ k → 2 ≤ lowCarryCount (finitePrime k) (npowBinRecAuto k (2 : ℕ)) := by
  decide

lemma finite_low_carry_check_8192_5 :
    ∀ a : Fin 4, ∀ b : Fin 4, ∀ j : Fin 64,
      let k := 5120 + 256 * (a : ℕ) + 64 * (b : ℕ) + (j : ℕ)
      3 ≤ k → 2 ≤ lowCarryCount (finitePrime k) (npowBinRecAuto k (2 : ℕ)) := by
  decide

lemma finite_low_carry_check_8192_6 :
    ∀ a : Fin 4, ∀ b : Fin 4, ∀ j : Fin 64,
      let k := 6144 + 256 * (a : ℕ) + 64 * (b : ℕ) + (j : ℕ)
      3 ≤ k → 2 ≤ lowCarryCount (finitePrime k) (npowBinRecAuto k (2 : ℕ)) := by
  decide

lemma finite_low_carry_check_8192_7 :
    ∀ a : Fin 4, ∀ b : Fin 4, ∀ j : Fin 64,
      let k := 7168 + 256 * (a : ℕ) + 64 * (b : ℕ) + (j : ℕ)
      3 ≤ k → 2 ≤ lowCarryCount (finitePrime k) (npowBinRecAuto k (2 : ℕ)) := by
  decide

lemma finite_low_carry_check_8192 :
    ∀ q : Fin 8, ∀ a : Fin 4, ∀ b : Fin 4, ∀ j : Fin 64,
      let k := 1024 * (q : ℕ) + 256 * (a : ℕ) + 64 * (b : ℕ) + (j : ℕ)
      3 ≤ k → 2 ≤ lowCarryCount (finitePrime k) (npowBinRecAuto k (2 : ℕ)) := by
  intro q a b j
  fin_cases q <;>
    simp only [Nat.mul_zero, zero_add, Nat.reduceMul] <;>
    first
    | exact finite_low_carry_check_8192_0 a b j
    | exact finite_low_carry_check_8192_1 a b j
    | exact finite_low_carry_check_8192_2 a b j
    | exact finite_low_carry_check_8192_3 a b j
    | exact finite_low_carry_check_8192_4 a b j
    | exact finite_low_carry_check_8192_5 a b j
    | exact finite_low_carry_check_8192_6 a b j
    | exact finite_low_carry_check_8192_7 a b j

/-- Every exponent below `8192` has at least two certified carries. -/
lemma finite_carry_check_8192 :
    ∀ k : Fin 8192, 3 ≤ (k : ℕ) →
      2 ≤ centralCarryCount (finitePrime k) (2 ^ (k : ℕ)) := by
  intro k hk3
  let q : Fin 8 := ⟨(k : ℕ) / 1024, by omega⟩
  let a : Fin 4 := ⟨((k : ℕ) % 1024) / 256, by omega⟩
  let b : Fin 4 := ⟨((k : ℕ) % 256) / 64, by omega⟩
  let j : Fin 64 := ⟨(k : ℕ) % 64, Nat.mod_lt _ (by norm_num)⟩
  have hkdecomp :
      1024 * (q : ℕ) + 256 * (a : ℕ) + 64 * (b : ℕ) + (j : ℕ) = (k : ℕ) := by
    dsimp [q, a, b, j]
    omega
  have hlow : 2 ≤ lowCarryCount (finitePrime k) (2 ^ (k : ℕ)) := by
    simpa only [hkdecomp, npowBinRecAuto_two_eq] using
      finite_low_carry_check_8192 q a b j (by omega)
  exact hlow.trans (lowCarryCount_le_centralCarryCount (by
    simp only [finitePrime]
    split_ifs <;> omega) (by positivity))

/-- Every exponent below the analytic cutoff has at least two certified
base-`p` carries. -/
lemma finite_carry_check :
    ∀ k : Fin 1617, 3 ≤ (k : ℕ) →
      2 ≤ centralCarryCount (finitePrime k) (2 ^ (k : ℕ)) := by
  intro k hk3
  let b : Fin 26 := ⟨(k : ℕ) / 64, by omega⟩
  let j : Fin 64 := ⟨(k : ℕ) % 64, Nat.mod_lt _ (by norm_num)⟩
  have hkdecomp : 64 * (b : ℕ) + (j : ℕ) = (k : ℕ) := by
    dsimp [b, j]
    omega
  have hlow : 2 ≤ lowCarryCount (finitePrime k) (2 ^ (k : ℕ)) := by
    simpa only [hkdecomp, npowBinRecAuto_two_eq] using
      finite_low_carry_check b j (by omega) (by omega)
  exact hlow.trans (lowCarryCount_le_centralCarryCount (by
    simp only [finitePrime]
    split_ifs <;> omega) (by positivity))

/-- Every power of two below the analytic cutoff has a certified prime-square
divisor of its central binomial coefficient. -/
lemma exists_prime_sq_dvd_centralBinom_two_pow_of_lt
    {k : ℕ} (hk3 : 3 ≤ k) (hk : k < 1617) :
    ∃ p : ℕ, p.Prime ∧ p ^ 2 ∣ centralBinom (2 ^ k) := by
  let k' : Fin 1617 := ⟨k, hk⟩
  let p := finitePrime k
  have hp : p.Prime := finitePrime_prime k
  letI : Fact p.Prime := ⟨hp⟩
  have hcarry : 2 ≤ centralCarryCount p (2 ^ k) := by
    simpa [k', p] using finite_carry_check k' hk3
  have hval : 2 ≤ padicValNat p (centralBinom (2 ^ k)) := by
    simpa [padicValNat_centralBinom_eq_centralCarryCount hp] using hcarry
  have hdvd : p ^ 2 ∣ centralBinom (2 ^ k) :=
    (padicValNat_dvd_iff_le (centralBinom_pos (2 ^ k)).ne').mpr hval
  exact ⟨p, hp, hdvd⟩

/-- The corresponding finite conclusion for the alternate cutoff `1728`. -/
lemma exists_prime_sq_dvd_centralBinom_two_pow_of_lt_1728
    {k : ℕ} (hk3 : 3 ≤ k) (hk : k < 1728) :
    ∃ p : ℕ, p.Prime ∧ p ^ 2 ∣ centralBinom (2 ^ k) := by
  let k' : Fin 1728 := ⟨k, hk⟩
  let p := finitePrime k
  have hp : p.Prime := finitePrime_prime k
  letI : Fact p.Prime := ⟨hp⟩
  have hcarry : 2 ≤ centralCarryCount p (2 ^ k) := by
    simpa [k', p] using finite_carry_check_1728 k' hk3
  have hval : 2 ≤ padicValNat p (centralBinom (2 ^ k)) := by
    simpa [padicValNat_centralBinom_eq_centralCarryCount hp] using hcarry
  have hdvd : p ^ 2 ∣ centralBinom (2 ^ k) :=
    (padicValNat_dvd_iff_le (centralBinom_pos (2 ^ k)).ne').mpr hval
  exact ⟨p, hp, hdvd⟩

/-- The finite conclusion through the cutoff used by the weakened analytic
estimate. -/
lemma exists_prime_sq_dvd_centralBinom_two_pow_of_lt_2304
    {k : ℕ} (hk3 : 3 ≤ k) (hk : k < 2304) :
    ∃ p : ℕ, p.Prime ∧ p ^ 2 ∣ centralBinom (2 ^ k) := by
  let k' : Fin 2304 := ⟨k, hk⟩
  let p := finitePrime k
  have hp : p.Prime := finitePrime_prime k
  letI : Fact p.Prime := ⟨hp⟩
  have hcarry : 2 ≤ centralCarryCount p (2 ^ k) := by
    simpa [k', p] using finite_carry_check_2304 k' hk3
  have hval : 2 ≤ padicValNat p (centralBinom (2 ^ k)) := by
    simpa [padicValNat_centralBinom_eq_centralCarryCount hp] using hcarry
  have hdvd : p ^ 2 ∣ centralBinom (2 ^ k) :=
    (padicValNat_dvd_iff_le (centralBinom_pos (2 ^ k)).ne').mpr hval
  exact ⟨p, hp, hdvd⟩

/-- The finite conclusion through the robust analytic cutoff `2816`. -/
lemma exists_prime_sq_dvd_centralBinom_two_pow_of_lt_2816
    {k : ℕ} (hk3 : 3 ≤ k) (hk : k < 2816) :
    ∃ p : ℕ, p.Prime ∧ p ^ 2 ∣ centralBinom (2 ^ k) := by
  let k' : Fin 2816 := ⟨k, hk⟩
  let p := finitePrime k
  have hp : p.Prime := finitePrime_prime k
  letI : Fact p.Prime := ⟨hp⟩
  have hcarry : 2 ≤ centralCarryCount p (2 ^ k) := by
    simpa [k', p] using finite_carry_check_2816 k' hk3
  have hval : 2 ≤ padicValNat p (centralBinom (2 ^ k)) := by
    simpa [padicValNat_centralBinom_eq_centralCarryCount hp] using hcarry
  have hdvd : p ^ 2 ∣ centralBinom (2 ^ k) :=
    (padicValNat_dvd_iff_le (centralBinom_pos (2 ^ k)).ne').mpr hval
  exact ⟨p, hp, hdvd⟩

/-- The finite conclusion through the final coarse analytic cutoff `8192`. -/
lemma exists_prime_sq_dvd_centralBinom_two_pow_of_lt_8192
    {k : ℕ} (hk3 : 3 ≤ k) (hk : k < 8192) :
    ∃ p : ℕ, p.Prime ∧ p ^ 2 ∣ centralBinom (2 ^ k) := by
  let k' : Fin 8192 := ⟨k, hk⟩
  let p := finitePrime k
  have hp : p.Prime := finitePrime_prime k
  letI : Fact p.Prime := ⟨hp⟩
  have hcarry : 2 ≤ centralCarryCount p (2 ^ k) := by
    simpa [k', p] using finite_carry_check_8192 k' hk3
  have hval : 2 ≤ padicValNat p (centralBinom (2 ^ k)) := by
    simpa [padicValNat_centralBinom_eq_centralCarryCount hp] using hcarry
  have hdvd : p ^ 2 ∣ centralBinom (2 ^ k) :=
    (padicValNat_dvd_iff_le (centralBinom_pos (2 ^ k)).ne').mpr hval
  exact ⟨p, hp, hdvd⟩

/-- A prime-square divisor contradicts Mathlib's `Squarefree` predicate. -/
lemma not_squarefree_of_prime_sq_dvd {m p : ℕ} (hp : p.Prime)
    (hdvd : p ^ 2 ∣ m) : ¬ Squarefree m := by
  intro hm
  exact (Nat.squarefree_iff_prime_squarefree.mp hm p hp) (by
    simpa [pow_two] using hdvd)

/-- The final elementary assembly, parametrized only by the explicit
large-`n` theorem proved in the analytic part. -/
lemma erdos_175_of_large
    (hlarge : ∀ n : ℕ, 2 ^ 1617 ≤ n →
      ∃ p : ℕ, p.Prime ∧ p ^ 2 ∣ centralBinom n) :
    ∀ n : ℕ, 5 ≤ n → ¬ Squarefree (Nat.choose (2 * n) n) := by
  intro n hn
  change ¬ Squarefree (centralBinom n)
  by_cases hpow : ∃ k : ℕ, n = 2 ^ k
  · obtain ⟨k, rfl⟩ := hpow
    have hk3 : 3 ≤ k := by
      by_contra hk
      have hk' : k ≤ 2 := by omega
      interval_cases k <;> norm_num at hn
    by_cases hk : k < 1617
    · obtain ⟨p, hp, hdvd⟩ :=
        exists_prime_sq_dvd_centralBinom_two_pow_of_lt hk3 hk
      exact not_squarefree_of_prime_sq_dvd hp hdvd
    · obtain ⟨p, hp, hdvd⟩ := hlarge (2 ^ k) (by
        exact Nat.pow_le_pow_right (by norm_num) (by omega))
      exact not_squarefree_of_prime_sq_dvd hp hdvd
  · exact not_squarefree_of_prime_sq_dvd Nat.prime_two (by
      simpa using (four_dvd_centralBinom_iff n (by omega)).mpr hpow)

/-- Elementary assembly using the alternate effective cutoff. -/
lemma erdos_175_of_large_1728
    (hlarge : ∀ n : ℕ, 2 ^ 1728 ≤ n →
      ∃ p : ℕ, p.Prime ∧ p ^ 2 ∣ centralBinom n) :
    ∀ n : ℕ, 5 ≤ n → ¬ Squarefree (Nat.choose (2 * n) n) := by
  intro n hn
  change ¬ Squarefree (centralBinom n)
  by_cases hpow : ∃ k : ℕ, n = 2 ^ k
  · obtain ⟨k, rfl⟩ := hpow
    have hk3 : 3 ≤ k := by
      by_contra hk
      have hk' : k ≤ 2 := by omega
      interval_cases k <;> norm_num at hn
    by_cases hk : k < 1728
    · obtain ⟨p, hp, hdvd⟩ :=
        exists_prime_sq_dvd_centralBinom_two_pow_of_lt_1728 hk3 hk
      exact not_squarefree_of_prime_sq_dvd hp hdvd
    · obtain ⟨p, hp, hdvd⟩ := hlarge (2 ^ k) (by
        exact Nat.pow_le_pow_right (by norm_num) (by omega))
      exact not_squarefree_of_prime_sq_dvd hp hdvd
  · exact not_squarefree_of_prime_sq_dvd Nat.prime_two (by
      simpa using (four_dvd_centralBinom_iff n (by omega)).mpr hpow)

/-- The analytic estimate is only needed on powers of two: every other index
is already disposed of by the binary valuation. -/
lemma erdos_175_of_large_two_pow_1728
    (hlarge : ∀ k : ℕ, 2 ^ 1728 ≤ 2 ^ k →
      ∃ p : ℕ, p.Prime ∧ p ^ 2 ∣ centralBinom (2 ^ k)) :
    ∀ n : ℕ, 5 ≤ n → ¬ Squarefree (Nat.choose (2 * n) n) := by
  intro n hn
  change ¬ Squarefree (centralBinom n)
  by_cases hpow : ∃ k : ℕ, n = 2 ^ k
  · obtain ⟨k, rfl⟩ := hpow
    have hk3 : 3 ≤ k := by
      by_contra hk
      have hk' : k ≤ 2 := by omega
      interval_cases k <;> norm_num at hn
    by_cases hk : k < 1728
    · obtain ⟨p, hp, hdvd⟩ :=
        exists_prime_sq_dvd_centralBinom_two_pow_of_lt_1728 hk3 hk
      exact not_squarefree_of_prime_sq_dvd hp hdvd
    · obtain ⟨p, hp, hdvd⟩ := hlarge k (by
        exact Nat.pow_le_pow_right (by norm_num) (by omega))
      exact not_squarefree_of_prime_sq_dvd hp hdvd
  · exact not_squarefree_of_prime_sq_dvd Nat.prime_two (by
      simpa using (four_dvd_centralBinom_iff n (by omega)).mpr hpow)

/-- Final elementary assembly at the cutoff used by the weakened explicit
analytic estimates. -/
lemma erdos_175_of_large_two_pow_2304
    (hlarge : ∀ k : ℕ, 2 ^ 2304 ≤ 2 ^ k →
      ∃ p : ℕ, p.Prime ∧ p ^ 2 ∣ centralBinom (2 ^ k)) :
    ∀ n : ℕ, 5 ≤ n → ¬ Squarefree (Nat.choose (2 * n) n) := by
  intro n hn
  change ¬ Squarefree (centralBinom n)
  by_cases hpow : ∃ k : ℕ, n = 2 ^ k
  · obtain ⟨k, rfl⟩ := hpow
    have hk3 : 3 ≤ k := by
      by_contra hk
      have hk' : k ≤ 2 := by omega
      interval_cases k <;> norm_num at hn
    by_cases hk : k < 2304
    · obtain ⟨p, hp, hdvd⟩ :=
        exists_prime_sq_dvd_centralBinom_two_pow_of_lt_2304 hk3 hk
      exact not_squarefree_of_prime_sq_dvd hp hdvd
    · obtain ⟨p, hp, hdvd⟩ := hlarge k (by
        exact Nat.pow_le_pow_right (by norm_num) (by omega))
      exact not_squarefree_of_prime_sq_dvd hp hdvd
  · exact not_squarefree_of_prime_sq_dvd Nat.prime_two (by
      simpa using (four_dvd_centralBinom_iff n (by omega)).mpr hpow)

/-- Final elementary assembly at the robust explicit cutoff. -/
lemma erdos_175_of_large_two_pow_2816
    (hlarge : ∀ k : ℕ, 2 ^ 2816 ≤ 2 ^ k →
      ∃ p : ℕ, p.Prime ∧ p ^ 2 ∣ centralBinom (2 ^ k)) :
    ∀ n : ℕ, 5 ≤ n → ¬ Squarefree (Nat.choose (2 * n) n) := by
  intro n hn
  change ¬ Squarefree (centralBinom n)
  by_cases hpow : ∃ k : ℕ, n = 2 ^ k
  · obtain ⟨k, rfl⟩ := hpow
    have hk3 : 3 ≤ k := by
      by_contra hk
      have hk' : k ≤ 2 := by omega
      interval_cases k <;> norm_num at hn
    by_cases hk : k < 2816
    · obtain ⟨p, hp, hdvd⟩ :=
        exists_prime_sq_dvd_centralBinom_two_pow_of_lt_2816 hk3 hk
      exact not_squarefree_of_prime_sq_dvd hp hdvd
    · obtain ⟨p, hp, hdvd⟩ := hlarge k (by
        exact Nat.pow_le_pow_right (by norm_num) (by omega))
      exact not_squarefree_of_prime_sq_dvd hp hdvd
  · exact not_squarefree_of_prime_sq_dvd Nat.prime_two (by
      simpa using (four_dvd_centralBinom_iff n (by omega)).mpr hpow)

/-- Final elementary assembly at the coarse explicit cutoff `8192`. -/
lemma erdos_175_of_large_two_pow_8192
    (hlarge : ∀ k : ℕ, 2 ^ 8192 ≤ 2 ^ k →
      ∃ p : ℕ, p.Prime ∧ p ^ 2 ∣ centralBinom (2 ^ k)) :
    ∀ n : ℕ, 5 ≤ n → ¬ Squarefree (Nat.choose (2 * n) n) := by
  intro n hn
  change ¬ Squarefree (centralBinom n)
  by_cases hpow : ∃ k : ℕ, n = 2 ^ k
  · obtain ⟨k, rfl⟩ := hpow
    have hk3 : 3 ≤ k := by
      by_contra hk
      have hk' : k ≤ 2 := by omega
      interval_cases k <;> norm_num at hn
    by_cases hk : k < 8192
    · obtain ⟨p, hp, hdvd⟩ :=
        exists_prime_sq_dvd_centralBinom_two_pow_of_lt_8192 hk3 hk
      exact not_squarefree_of_prime_sq_dvd hp hdvd
    · obtain ⟨p, hp, hdvd⟩ := hlarge k (by
        exact Nat.pow_le_pow_right (by norm_num) (by omega))
      exact not_squarefree_of_prime_sq_dvd hp hdvd
  · exact not_squarefree_of_prime_sq_dvd Nat.prime_two (by
      simpa using (four_dvd_centralBinom_iff n (by omega)).mpr hpow)

/-- Erdős Problem 175: for every `n ≥ 5`, the central binomial coefficient
is not squarefree. -/
theorem erdos_175 {n : ℕ} (hn : 5 ≤ n) :
    ¬ Squarefree (Nat.choose (2 * n) n) := by
  apply erdos_175_of_large_two_pow_8192
    (fun k hkpow => ?_)
    n hn
  have hk : 8192 ≤ k :=
    (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hkpow
  simpa only [centralBinom] using FinalLarge.large_power_witness k hk

#print axioms finite_carry_check_8192
#print axioms Erdos175.erdos_175

end Erdos175
