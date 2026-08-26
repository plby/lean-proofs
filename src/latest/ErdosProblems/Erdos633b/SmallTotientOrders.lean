import ErdosProblems.Erdos633b.TotientQuadraticBound
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.GCD

/-! Exact finite totient checks under unchanged default limits. -/

namespace Erdos633b

def smallTotientOrders : Finset ℕ :=
  {7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 18, 20, 21, 22, 24, 26, 28, 30, 36, 42}

theorem smallTotientOrders_card : smallTotientOrders.card = 20 := by decide

theorem totient_gt_twelve_43_50 (n : ℕ) (hlo : 43 ≤ n) (hhi : n ≤ 50) :
    12 < n.totient := by
  interval_cases n
  · have hh : Nat.totient 43 = 42 :=
      (Nat.totient_prime_pow_succ (p := 43) (by norm_num) 0)
    rw [hh]
    decide
  · have hh : Nat.totient 44 = 20 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 4 11)
        have ha : Nat.totient 4 = 2 := (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 1)
        have hb : Nat.totient 11 = 10 := (Nat.totient_prime_pow_succ (p := 11) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide
  · have hh : Nat.totient 45 = 24 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 9 5)
        have ha : Nat.totient 9 = 6 := (Nat.totient_prime_pow_succ (p := 3) (by norm_num) 1)
        have hb : Nat.totient 5 = 4 := (Nat.totient_prime_pow_succ (p := 5) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide
  · have hh : Nat.totient 46 = 22 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 2 23)
        have ha : Nat.totient 2 = 1 := (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 0)
        have hb : Nat.totient 23 = 22 := (Nat.totient_prime_pow_succ (p := 23) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide
  · have hh : Nat.totient 47 = 46 :=
      (Nat.totient_prime_pow_succ (p := 47) (by norm_num) 0)
    rw [hh]
    decide
  · have hh : Nat.totient 48 = 16 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 16 3)
        have ha : Nat.totient 16 = 8 := (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 3)
        have hb : Nat.totient 3 = 2 := (Nat.totient_prime_pow_succ (p := 3) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide
  · have hh : Nat.totient 49 = 42 :=
      (Nat.totient_prime_pow_succ (p := 7) (by norm_num) 1)
    rw [hh]
    decide
  · have hh : Nat.totient 50 = 20 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 2 25)
        have ha : Nat.totient 2 = 1 := (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 0)
        have hb : Nat.totient 25 = 20 := (Nat.totient_prime_pow_succ (p := 5) (by norm_num) 1)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide

theorem totient_gt_twelve_51_58 (n : ℕ) (hlo : 51 ≤ n) (hhi : n ≤ 58) :
    12 < n.totient := by
  interval_cases n
  · have hh : Nat.totient 51 = 32 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 3 17)
        have ha : Nat.totient 3 = 2 := (Nat.totient_prime_pow_succ (p := 3) (by norm_num) 0)
        have hb : Nat.totient 17 = 16 := (Nat.totient_prime_pow_succ (p := 17) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide
  · have hh : Nat.totient 52 = 24 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 4 13)
        have ha : Nat.totient 4 = 2 := (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 1)
        have hb : Nat.totient 13 = 12 := (Nat.totient_prime_pow_succ (p := 13) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide
  · have hh : Nat.totient 53 = 52 :=
      (Nat.totient_prime_pow_succ (p := 53) (by norm_num) 0)
    rw [hh]
    decide
  · have hh : Nat.totient 54 = 18 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 2 27)
        have ha : Nat.totient 2 = 1 := (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 0)
        have hb : Nat.totient 27 = 18 := (Nat.totient_prime_pow_succ (p := 3) (by norm_num) 2)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide
  · have hh : Nat.totient 55 = 40 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 5 11)
        have ha : Nat.totient 5 = 4 := (Nat.totient_prime_pow_succ (p := 5) (by norm_num) 0)
        have hb : Nat.totient 11 = 10 := (Nat.totient_prime_pow_succ (p := 11) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide
  · have hh : Nat.totient 56 = 24 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 8 7)
        have ha : Nat.totient 8 = 4 := (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 2)
        have hb : Nat.totient 7 = 6 := (Nat.totient_prime_pow_succ (p := 7) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide
  · have hh : Nat.totient 57 = 36 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 3 19)
        have ha : Nat.totient 3 = 2 := (Nat.totient_prime_pow_succ (p := 3) (by norm_num) 0)
        have hb : Nat.totient 19 = 18 := (Nat.totient_prime_pow_succ (p := 19) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide
  · have hh : Nat.totient 58 = 28 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 2 29)
        have ha : Nat.totient 2 = 1 := (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 0)
        have hb : Nat.totient 29 = 28 := (Nat.totient_prime_pow_succ (p := 29) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide

theorem totient_gt_twelve_59_66 (n : ℕ) (hlo : 59 ≤ n) (hhi : n ≤ 66) :
    12 < n.totient := by
  interval_cases n
  · have hh : Nat.totient 59 = 58 :=
      (Nat.totient_prime_pow_succ (p := 59) (by norm_num) 0)
    rw [hh]
    decide
  · have hh : Nat.totient 60 = 16 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 4 15)
        have ha : Nat.totient 4 = 2 := (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 1)
        have hb : Nat.totient 15 = 8 := (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 3 5)
        have ha : Nat.totient 3 = 2 := (Nat.totient_prime_pow_succ (p := 3) (by norm_num) 0)
        have hb : Nat.totient 5 = 4 := (Nat.totient_prime_pow_succ (p := 5) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide
  · have hh : Nat.totient 61 = 60 :=
      (Nat.totient_prime_pow_succ (p := 61) (by norm_num) 0)
    rw [hh]
    decide
  · have hh : Nat.totient 62 = 30 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 2 31)
        have ha : Nat.totient 2 = 1 := (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 0)
        have hb : Nat.totient 31 = 30 := (Nat.totient_prime_pow_succ (p := 31) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide
  · have hh : Nat.totient 63 = 36 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 9 7)
        have ha : Nat.totient 9 = 6 := (Nat.totient_prime_pow_succ (p := 3) (by norm_num) 1)
        have hb : Nat.totient 7 = 6 := (Nat.totient_prime_pow_succ (p := 7) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide
  · have hh : Nat.totient 64 = 32 :=
      (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 5)
    rw [hh]
    decide
  · have hh : Nat.totient 65 = 48 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 5 13)
        have ha : Nat.totient 5 = 4 := (Nat.totient_prime_pow_succ (p := 5) (by norm_num) 0)
        have hb : Nat.totient 13 = 12 := (Nat.totient_prime_pow_succ (p := 13) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide
  · have hh : Nat.totient 66 = 20 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 2 33)
        have ha : Nat.totient 2 = 1 := (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 0)
        have hb : Nat.totient 33 = 20 := (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 3 11)
        have ha : Nat.totient 3 = 2 := (Nat.totient_prime_pow_succ (p := 3) (by norm_num) 0)
        have hb : Nat.totient 11 = 10 := (Nat.totient_prime_pow_succ (p := 11) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide

theorem totient_gt_twelve_67_74 (n : ℕ) (hlo : 67 ≤ n) (hhi : n ≤ 74) :
    12 < n.totient := by
  interval_cases n
  · have hh : Nat.totient 67 = 66 :=
      (Nat.totient_prime_pow_succ (p := 67) (by norm_num) 0)
    rw [hh]
    decide
  · have hh : Nat.totient 68 = 32 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 4 17)
        have ha : Nat.totient 4 = 2 := (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 1)
        have hb : Nat.totient 17 = 16 := (Nat.totient_prime_pow_succ (p := 17) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide
  · have hh : Nat.totient 69 = 44 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 3 23)
        have ha : Nat.totient 3 = 2 := (Nat.totient_prime_pow_succ (p := 3) (by norm_num) 0)
        have hb : Nat.totient 23 = 22 := (Nat.totient_prime_pow_succ (p := 23) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide
  · have hh : Nat.totient 70 = 24 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 2 35)
        have ha : Nat.totient 2 = 1 := (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 0)
        have hb : Nat.totient 35 = 24 := (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 5 7)
        have ha : Nat.totient 5 = 4 := (Nat.totient_prime_pow_succ (p := 5) (by norm_num) 0)
        have hb : Nat.totient 7 = 6 := (Nat.totient_prime_pow_succ (p := 7) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide
  · have hh : Nat.totient 71 = 70 :=
      (Nat.totient_prime_pow_succ (p := 71) (by norm_num) 0)
    rw [hh]
    decide
  · have hh : Nat.totient 72 = 24 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 8 9)
        have ha : Nat.totient 8 = 4 := (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 2)
        have hb : Nat.totient 9 = 6 := (Nat.totient_prime_pow_succ (p := 3) (by norm_num) 1)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide
  · have hh : Nat.totient 73 = 72 :=
      (Nat.totient_prime_pow_succ (p := 73) (by norm_num) 0)
    rw [hh]
    decide
  · have hh : Nat.totient 74 = 36 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 2 37)
        have ha : Nat.totient 2 = 1 := (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 0)
        have hb : Nat.totient 37 = 36 := (Nat.totient_prime_pow_succ (p := 37) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide

theorem totient_gt_twelve_75_82 (n : ℕ) (hlo : 75 ≤ n) (hhi : n ≤ 82) :
    12 < n.totient := by
  interval_cases n
  · have hh : Nat.totient 75 = 40 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 3 25)
        have ha : Nat.totient 3 = 2 := (Nat.totient_prime_pow_succ (p := 3) (by norm_num) 0)
        have hb : Nat.totient 25 = 20 := (Nat.totient_prime_pow_succ (p := 5) (by norm_num) 1)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide
  · have hh : Nat.totient 76 = 36 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 4 19)
        have ha : Nat.totient 4 = 2 := (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 1)
        have hb : Nat.totient 19 = 18 := (Nat.totient_prime_pow_succ (p := 19) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide
  · have hh : Nat.totient 77 = 60 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 7 11)
        have ha : Nat.totient 7 = 6 := (Nat.totient_prime_pow_succ (p := 7) (by norm_num) 0)
        have hb : Nat.totient 11 = 10 := (Nat.totient_prime_pow_succ (p := 11) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide
  · have hh : Nat.totient 78 = 24 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 2 39)
        have ha : Nat.totient 2 = 1 := (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 0)
        have hb : Nat.totient 39 = 24 := (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 3 13)
        have ha : Nat.totient 3 = 2 := (Nat.totient_prime_pow_succ (p := 3) (by norm_num) 0)
        have hb : Nat.totient 13 = 12 := (Nat.totient_prime_pow_succ (p := 13) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide
  · have hh : Nat.totient 79 = 78 :=
      (Nat.totient_prime_pow_succ (p := 79) (by norm_num) 0)
    rw [hh]
    decide
  · have hh : Nat.totient 80 = 32 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 16 5)
        have ha : Nat.totient 16 = 8 := (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 3)
        have hb : Nat.totient 5 = 4 := (Nat.totient_prime_pow_succ (p := 5) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide
  · have hh : Nat.totient 81 = 54 :=
      (Nat.totient_prime_pow_succ (p := 3) (by norm_num) 3)
    rw [hh]
    decide
  · have hh : Nat.totient 82 = 40 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 2 41)
        have ha : Nat.totient 2 = 1 := (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 0)
        have hb : Nat.totient 41 = 40 := (Nat.totient_prime_pow_succ (p := 41) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide

theorem totient_gt_twelve_83_90 (n : ℕ) (hlo : 83 ≤ n) (hhi : n ≤ 90) :
    12 < n.totient := by
  interval_cases n
  · have hh : Nat.totient 83 = 82 :=
      (Nat.totient_prime_pow_succ (p := 83) (by norm_num) 0)
    rw [hh]
    decide
  · have hh : Nat.totient 84 = 24 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 4 21)
        have ha : Nat.totient 4 = 2 := (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 1)
        have hb : Nat.totient 21 = 12 := (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 3 7)
        have ha : Nat.totient 3 = 2 := (Nat.totient_prime_pow_succ (p := 3) (by norm_num) 0)
        have hb : Nat.totient 7 = 6 := (Nat.totient_prime_pow_succ (p := 7) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide
  · have hh : Nat.totient 85 = 64 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 5 17)
        have ha : Nat.totient 5 = 4 := (Nat.totient_prime_pow_succ (p := 5) (by norm_num) 0)
        have hb : Nat.totient 17 = 16 := (Nat.totient_prime_pow_succ (p := 17) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide
  · have hh : Nat.totient 86 = 42 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 2 43)
        have ha : Nat.totient 2 = 1 := (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 0)
        have hb : Nat.totient 43 = 42 := (Nat.totient_prime_pow_succ (p := 43) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide
  · have hh : Nat.totient 87 = 56 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 3 29)
        have ha : Nat.totient 3 = 2 := (Nat.totient_prime_pow_succ (p := 3) (by norm_num) 0)
        have hb : Nat.totient 29 = 28 := (Nat.totient_prime_pow_succ (p := 29) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide
  · have hh : Nat.totient 88 = 40 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 8 11)
        have ha : Nat.totient 8 = 4 := (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 2)
        have hb : Nat.totient 11 = 10 := (Nat.totient_prime_pow_succ (p := 11) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide
  · have hh : Nat.totient 89 = 88 :=
      (Nat.totient_prime_pow_succ (p := 89) (by norm_num) 0)
    rw [hh]
    decide
  · have hh : Nat.totient 90 = 24 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 2 45)
        have ha : Nat.totient 2 = 1 := (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 0)
        have hb : Nat.totient 45 = 24 := (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 9 5)
        have ha : Nat.totient 9 = 6 := (Nat.totient_prime_pow_succ (p := 3) (by norm_num) 1)
        have hb : Nat.totient 5 = 4 := (Nat.totient_prime_pow_succ (p := 5) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide

theorem totient_gt_twelve_91_98 (n : ℕ) (hlo : 91 ≤ n) (hhi : n ≤ 98) :
    12 < n.totient := by
  interval_cases n
  · have hh : Nat.totient 91 = 72 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 7 13)
        have ha : Nat.totient 7 = 6 := (Nat.totient_prime_pow_succ (p := 7) (by norm_num) 0)
        have hb : Nat.totient 13 = 12 := (Nat.totient_prime_pow_succ (p := 13) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide
  · have hh : Nat.totient 92 = 44 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 4 23)
        have ha : Nat.totient 4 = 2 := (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 1)
        have hb : Nat.totient 23 = 22 := (Nat.totient_prime_pow_succ (p := 23) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide
  · have hh : Nat.totient 93 = 60 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 3 31)
        have ha : Nat.totient 3 = 2 := (Nat.totient_prime_pow_succ (p := 3) (by norm_num) 0)
        have hb : Nat.totient 31 = 30 := (Nat.totient_prime_pow_succ (p := 31) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide
  · have hh : Nat.totient 94 = 46 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 2 47)
        have ha : Nat.totient 2 = 1 := (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 0)
        have hb : Nat.totient 47 = 46 := (Nat.totient_prime_pow_succ (p := 47) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide
  · have hh : Nat.totient 95 = 72 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 5 19)
        have ha : Nat.totient 5 = 4 := (Nat.totient_prime_pow_succ (p := 5) (by norm_num) 0)
        have hb : Nat.totient 19 = 18 := (Nat.totient_prime_pow_succ (p := 19) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide
  · have hh : Nat.totient 96 = 32 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 32 3)
        have ha : Nat.totient 32 = 16 := (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 4)
        have hb : Nat.totient 3 = 2 := (Nat.totient_prime_pow_succ (p := 3) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide
  · have hh : Nat.totient 97 = 96 :=
      (Nat.totient_prime_pow_succ (p := 97) (by norm_num) 0)
    rw [hh]
    decide
  · have hh : Nat.totient 98 = 42 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 2 49)
        have ha : Nat.totient 2 = 1 := (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 0)
        have hb : Nat.totient 49 = 42 := (Nat.totient_prime_pow_succ (p := 7) (by norm_num) 1)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide

theorem totient_gt_twelve_99_106 (n : ℕ) (hlo : 99 ≤ n) (hhi : n ≤ 106) :
    12 < n.totient := by
  interval_cases n
  · have hh : Nat.totient 99 = 60 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 9 11)
        have ha : Nat.totient 9 = 6 := (Nat.totient_prime_pow_succ (p := 3) (by norm_num) 1)
        have hb : Nat.totient 11 = 10 := (Nat.totient_prime_pow_succ (p := 11) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide
  · have hh : Nat.totient 100 = 40 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 4 25)
        have ha : Nat.totient 4 = 2 := (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 1)
        have hb : Nat.totient 25 = 20 := (Nat.totient_prime_pow_succ (p := 5) (by norm_num) 1)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide
  · have hh : Nat.totient 101 = 100 :=
      (Nat.totient_prime_pow_succ (p := 101) (by norm_num) 0)
    rw [hh]
    decide
  · have hh : Nat.totient 102 = 32 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 2 51)
        have ha : Nat.totient 2 = 1 := (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 0)
        have hb : Nat.totient 51 = 32 := (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 3 17)
        have ha : Nat.totient 3 = 2 := (Nat.totient_prime_pow_succ (p := 3) (by norm_num) 0)
        have hb : Nat.totient 17 = 16 := (Nat.totient_prime_pow_succ (p := 17) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide
  · have hh : Nat.totient 103 = 102 :=
      (Nat.totient_prime_pow_succ (p := 103) (by norm_num) 0)
    rw [hh]
    decide
  · have hh : Nat.totient 104 = 48 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 8 13)
        have ha : Nat.totient 8 = 4 := (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 2)
        have hb : Nat.totient 13 = 12 := (Nat.totient_prime_pow_succ (p := 13) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide
  · have hh : Nat.totient 105 = 48 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 3 35)
        have ha : Nat.totient 3 = 2 := (Nat.totient_prime_pow_succ (p := 3) (by norm_num) 0)
        have hb : Nat.totient 35 = 24 := (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 5 7)
        have ha : Nat.totient 5 = 4 := (Nat.totient_prime_pow_succ (p := 5) (by norm_num) 0)
        have hb : Nat.totient 7 = 6 := (Nat.totient_prime_pow_succ (p := 7) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide
  · have hh : Nat.totient 106 = 52 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 2 53)
        have ha : Nat.totient 2 = 1 := (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 0)
        have hb : Nat.totient 53 = 52 := (Nat.totient_prime_pow_succ (p := 53) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide

theorem totient_gt_twelve_107_114 (n : ℕ) (hlo : 107 ≤ n) (hhi : n ≤ 114) :
    12 < n.totient := by
  interval_cases n
  · have hh : Nat.totient 107 = 106 :=
      (Nat.totient_prime_pow_succ (p := 107) (by norm_num) 0)
    rw [hh]
    decide
  · have hh : Nat.totient 108 = 36 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 4 27)
        have ha : Nat.totient 4 = 2 := (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 1)
        have hb : Nat.totient 27 = 18 := (Nat.totient_prime_pow_succ (p := 3) (by norm_num) 2)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide
  · have hh : Nat.totient 109 = 108 :=
      (Nat.totient_prime_pow_succ (p := 109) (by norm_num) 0)
    rw [hh]
    decide
  · have hh : Nat.totient 110 = 40 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 2 55)
        have ha : Nat.totient 2 = 1 := (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 0)
        have hb : Nat.totient 55 = 40 := (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 5 11)
        have ha : Nat.totient 5 = 4 := (Nat.totient_prime_pow_succ (p := 5) (by norm_num) 0)
        have hb : Nat.totient 11 = 10 := (Nat.totient_prime_pow_succ (p := 11) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide
  · have hh : Nat.totient 111 = 72 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 3 37)
        have ha : Nat.totient 3 = 2 := (Nat.totient_prime_pow_succ (p := 3) (by norm_num) 0)
        have hb : Nat.totient 37 = 36 := (Nat.totient_prime_pow_succ (p := 37) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide
  · have hh : Nat.totient 112 = 48 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 16 7)
        have ha : Nat.totient 16 = 8 := (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 3)
        have hb : Nat.totient 7 = 6 := (Nat.totient_prime_pow_succ (p := 7) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide
  · have hh : Nat.totient 113 = 112 :=
      (Nat.totient_prime_pow_succ (p := 113) (by norm_num) 0)
    rw [hh]
    decide
  · have hh : Nat.totient 114 = 36 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 2 57)
        have ha : Nat.totient 2 = 1 := (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 0)
        have hb : Nat.totient 57 = 36 := (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 3 19)
        have ha : Nat.totient 3 = 2 := (Nat.totient_prime_pow_succ (p := 3) (by norm_num) 0)
        have hb : Nat.totient 19 = 18 := (Nat.totient_prime_pow_succ (p := 19) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide

theorem totient_gt_twelve_115_122 (n : ℕ) (hlo : 115 ≤ n) (hhi : n ≤ 122) :
    12 < n.totient := by
  interval_cases n
  · have hh : Nat.totient 115 = 88 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 5 23)
        have ha : Nat.totient 5 = 4 := (Nat.totient_prime_pow_succ (p := 5) (by norm_num) 0)
        have hb : Nat.totient 23 = 22 := (Nat.totient_prime_pow_succ (p := 23) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide
  · have hh : Nat.totient 116 = 56 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 4 29)
        have ha : Nat.totient 4 = 2 := (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 1)
        have hb : Nat.totient 29 = 28 := (Nat.totient_prime_pow_succ (p := 29) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide
  · have hh : Nat.totient 117 = 72 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 9 13)
        have ha : Nat.totient 9 = 6 := (Nat.totient_prime_pow_succ (p := 3) (by norm_num) 1)
        have hb : Nat.totient 13 = 12 := (Nat.totient_prime_pow_succ (p := 13) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide
  · have hh : Nat.totient 118 = 58 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 2 59)
        have ha : Nat.totient 2 = 1 := (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 0)
        have hb : Nat.totient 59 = 58 := (Nat.totient_prime_pow_succ (p := 59) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide
  · have hh : Nat.totient 119 = 96 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 7 17)
        have ha : Nat.totient 7 = 6 := (Nat.totient_prime_pow_succ (p := 7) (by norm_num) 0)
        have hb : Nat.totient 17 = 16 := (Nat.totient_prime_pow_succ (p := 17) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide
  · have hh : Nat.totient 120 = 32 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 8 15)
        have ha : Nat.totient 8 = 4 := (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 2)
        have hb : Nat.totient 15 = 8 := (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 3 5)
        have ha : Nat.totient 3 = 2 := (Nat.totient_prime_pow_succ (p := 3) (by norm_num) 0)
        have hb : Nat.totient 5 = 4 := (Nat.totient_prime_pow_succ (p := 5) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide
  · have hh : Nat.totient 121 = 110 :=
      (Nat.totient_prime_pow_succ (p := 11) (by norm_num) 1)
    rw [hh]
    decide
  · have hh : Nat.totient 122 = 60 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 2 61)
        have ha : Nat.totient 2 = 1 := (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 0)
        have hb : Nat.totient 61 = 60 := (Nat.totient_prime_pow_succ (p := 61) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide

theorem totient_gt_twelve_123_130 (n : ℕ) (hlo : 123 ≤ n) (hhi : n ≤ 130) :
    12 < n.totient := by
  interval_cases n
  · have hh : Nat.totient 123 = 80 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 3 41)
        have ha : Nat.totient 3 = 2 := (Nat.totient_prime_pow_succ (p := 3) (by norm_num) 0)
        have hb : Nat.totient 41 = 40 := (Nat.totient_prime_pow_succ (p := 41) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide
  · have hh : Nat.totient 124 = 60 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 4 31)
        have ha : Nat.totient 4 = 2 := (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 1)
        have hb : Nat.totient 31 = 30 := (Nat.totient_prime_pow_succ (p := 31) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide
  · have hh : Nat.totient 125 = 100 :=
      (Nat.totient_prime_pow_succ (p := 5) (by norm_num) 2)
    rw [hh]
    decide
  · have hh : Nat.totient 126 = 36 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 2 63)
        have ha : Nat.totient 2 = 1 := (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 0)
        have hb : Nat.totient 63 = 36 := (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 9 7)
        have ha : Nat.totient 9 = 6 := (Nat.totient_prime_pow_succ (p := 3) (by norm_num) 1)
        have hb : Nat.totient 7 = 6 := (Nat.totient_prime_pow_succ (p := 7) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide
  · have hh : Nat.totient 127 = 126 :=
      (Nat.totient_prime_pow_succ (p := 127) (by norm_num) 0)
    rw [hh]
    decide
  · have hh : Nat.totient 128 = 64 :=
      (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 6)
    rw [hh]
    decide
  · have hh : Nat.totient 129 = 84 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 3 43)
        have ha : Nat.totient 3 = 2 := (Nat.totient_prime_pow_succ (p := 3) (by norm_num) 0)
        have hb : Nat.totient 43 = 42 := (Nat.totient_prime_pow_succ (p := 43) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide
  · have hh : Nat.totient 130 = 48 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 2 65)
        have ha : Nat.totient 2 = 1 := (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 0)
        have hb : Nat.totient 65 = 48 := (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 5 13)
        have ha : Nat.totient 5 = 4 := (Nat.totient_prime_pow_succ (p := 5) (by norm_num) 0)
        have hb : Nat.totient 13 = 12 := (Nat.totient_prime_pow_succ (p := 13) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide

theorem totient_gt_twelve_131_138 (n : ℕ) (hlo : 131 ≤ n) (hhi : n ≤ 138) :
    12 < n.totient := by
  interval_cases n
  · have hh : Nat.totient 131 = 130 :=
      (Nat.totient_prime_pow_succ (p := 131) (by norm_num) 0)
    rw [hh]
    decide
  · have hh : Nat.totient 132 = 40 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 4 33)
        have ha : Nat.totient 4 = 2 := (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 1)
        have hb : Nat.totient 33 = 20 := (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 3 11)
        have ha : Nat.totient 3 = 2 := (Nat.totient_prime_pow_succ (p := 3) (by norm_num) 0)
        have hb : Nat.totient 11 = 10 := (Nat.totient_prime_pow_succ (p := 11) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide
  · have hh : Nat.totient 133 = 108 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 7 19)
        have ha : Nat.totient 7 = 6 := (Nat.totient_prime_pow_succ (p := 7) (by norm_num) 0)
        have hb : Nat.totient 19 = 18 := (Nat.totient_prime_pow_succ (p := 19) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide
  · have hh : Nat.totient 134 = 66 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 2 67)
        have ha : Nat.totient 2 = 1 := (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 0)
        have hb : Nat.totient 67 = 66 := (Nat.totient_prime_pow_succ (p := 67) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide
  · have hh : Nat.totient 135 = 72 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 27 5)
        have ha : Nat.totient 27 = 18 := (Nat.totient_prime_pow_succ (p := 3) (by norm_num) 2)
        have hb : Nat.totient 5 = 4 := (Nat.totient_prime_pow_succ (p := 5) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide
  · have hh : Nat.totient 136 = 64 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 8 17)
        have ha : Nat.totient 8 = 4 := (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 2)
        have hb : Nat.totient 17 = 16 := (Nat.totient_prime_pow_succ (p := 17) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide
  · have hh : Nat.totient 137 = 136 :=
      (Nat.totient_prime_pow_succ (p := 137) (by norm_num) 0)
    rw [hh]
    decide
  · have hh : Nat.totient 138 = 44 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 2 69)
        have ha : Nat.totient 2 = 1 := (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 0)
        have hb : Nat.totient 69 = 44 := (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 3 23)
        have ha : Nat.totient 3 = 2 := (Nat.totient_prime_pow_succ (p := 3) (by norm_num) 0)
        have hb : Nat.totient 23 = 22 := (Nat.totient_prime_pow_succ (p := 23) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide

theorem totient_gt_twelve_139_146 (n : ℕ) (hlo : 139 ≤ n) (hhi : n ≤ 146) :
    12 < n.totient := by
  interval_cases n
  · have hh : Nat.totient 139 = 138 :=
      (Nat.totient_prime_pow_succ (p := 139) (by norm_num) 0)
    rw [hh]
    decide
  · have hh : Nat.totient 140 = 48 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 4 35)
        have ha : Nat.totient 4 = 2 := (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 1)
        have hb : Nat.totient 35 = 24 := (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 5 7)
        have ha : Nat.totient 5 = 4 := (Nat.totient_prime_pow_succ (p := 5) (by norm_num) 0)
        have hb : Nat.totient 7 = 6 := (Nat.totient_prime_pow_succ (p := 7) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide
  · have hh : Nat.totient 141 = 92 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 3 47)
        have ha : Nat.totient 3 = 2 := (Nat.totient_prime_pow_succ (p := 3) (by norm_num) 0)
        have hb : Nat.totient 47 = 46 := (Nat.totient_prime_pow_succ (p := 47) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide
  · have hh : Nat.totient 142 = 70 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 2 71)
        have ha : Nat.totient 2 = 1 := (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 0)
        have hb : Nat.totient 71 = 70 := (Nat.totient_prime_pow_succ (p := 71) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide
  · have hh : Nat.totient 143 = 120 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 11 13)
        have ha : Nat.totient 11 = 10 := (Nat.totient_prime_pow_succ (p := 11) (by norm_num) 0)
        have hb : Nat.totient 13 = 12 := (Nat.totient_prime_pow_succ (p := 13) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide
  · have hh : Nat.totient 144 = 48 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 16 9)
        have ha : Nat.totient 16 = 8 := (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 3)
        have hb : Nat.totient 9 = 6 := (Nat.totient_prime_pow_succ (p := 3) (by norm_num) 1)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide
  · have hh : Nat.totient 145 = 112 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 5 29)
        have ha : Nat.totient 5 = 4 := (Nat.totient_prime_pow_succ (p := 5) (by norm_num) 0)
        have hb : Nat.totient 29 = 28 := (Nat.totient_prime_pow_succ (p := 29) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide
  · have hh : Nat.totient 146 = 72 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 2 73)
        have ha : Nat.totient 2 = 1 := (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 0)
        have hb : Nat.totient 73 = 72 := (Nat.totient_prime_pow_succ (p := 73) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide

theorem totient_gt_twelve_147_154 (n : ℕ) (hlo : 147 ≤ n) (hhi : n ≤ 154) :
    12 < n.totient := by
  interval_cases n
  · have hh : Nat.totient 147 = 84 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 3 49)
        have ha : Nat.totient 3 = 2 := (Nat.totient_prime_pow_succ (p := 3) (by norm_num) 0)
        have hb : Nat.totient 49 = 42 := (Nat.totient_prime_pow_succ (p := 7) (by norm_num) 1)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide
  · have hh : Nat.totient 148 = 72 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 4 37)
        have ha : Nat.totient 4 = 2 := (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 1)
        have hb : Nat.totient 37 = 36 := (Nat.totient_prime_pow_succ (p := 37) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide
  · have hh : Nat.totient 149 = 148 :=
      (Nat.totient_prime_pow_succ (p := 149) (by norm_num) 0)
    rw [hh]
    decide
  · have hh : Nat.totient 150 = 40 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 2 75)
        have ha : Nat.totient 2 = 1 := (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 0)
        have hb : Nat.totient 75 = 40 := (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 3 25)
        have ha : Nat.totient 3 = 2 := (Nat.totient_prime_pow_succ (p := 3) (by norm_num) 0)
        have hb : Nat.totient 25 = 20 := (Nat.totient_prime_pow_succ (p := 5) (by norm_num) 1)
        rw [ha, hb] at h
        exact h)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide
  · have hh : Nat.totient 151 = 150 :=
      (Nat.totient_prime_pow_succ (p := 151) (by norm_num) 0)
    rw [hh]
    decide
  · have hh : Nat.totient 152 = 72 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 8 19)
        have ha : Nat.totient 8 = 4 := (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 2)
        have hb : Nat.totient 19 = 18 := (Nat.totient_prime_pow_succ (p := 19) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide
  · have hh : Nat.totient 153 = 96 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 9 17)
        have ha : Nat.totient 9 = 6 := (Nat.totient_prime_pow_succ (p := 3) (by norm_num) 1)
        have hb : Nat.totient 17 = 16 := (Nat.totient_prime_pow_succ (p := 17) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide
  · have hh : Nat.totient 154 = 60 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 2 77)
        have ha : Nat.totient 2 = 1 := (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 0)
        have hb : Nat.totient 77 = 60 := (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 7 11)
        have ha : Nat.totient 7 = 6 := (Nat.totient_prime_pow_succ (p := 7) (by norm_num) 0)
        have hb : Nat.totient 11 = 10 := (Nat.totient_prime_pow_succ (p := 11) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide

theorem totient_gt_twelve_155_162 (n : ℕ) (hlo : 155 ≤ n) (hhi : n ≤ 162) :
    12 < n.totient := by
  interval_cases n
  · have hh : Nat.totient 155 = 120 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 5 31)
        have ha : Nat.totient 5 = 4 := (Nat.totient_prime_pow_succ (p := 5) (by norm_num) 0)
        have hb : Nat.totient 31 = 30 := (Nat.totient_prime_pow_succ (p := 31) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide
  · have hh : Nat.totient 156 = 48 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 4 39)
        have ha : Nat.totient 4 = 2 := (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 1)
        have hb : Nat.totient 39 = 24 := (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 3 13)
        have ha : Nat.totient 3 = 2 := (Nat.totient_prime_pow_succ (p := 3) (by norm_num) 0)
        have hb : Nat.totient 13 = 12 := (Nat.totient_prime_pow_succ (p := 13) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide
  · have hh : Nat.totient 157 = 156 :=
      (Nat.totient_prime_pow_succ (p := 157) (by norm_num) 0)
    rw [hh]
    decide
  · have hh : Nat.totient 158 = 78 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 2 79)
        have ha : Nat.totient 2 = 1 := (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 0)
        have hb : Nat.totient 79 = 78 := (Nat.totient_prime_pow_succ (p := 79) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide
  · have hh : Nat.totient 159 = 104 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 3 53)
        have ha : Nat.totient 3 = 2 := (Nat.totient_prime_pow_succ (p := 3) (by norm_num) 0)
        have hb : Nat.totient 53 = 52 := (Nat.totient_prime_pow_succ (p := 53) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide
  · have hh : Nat.totient 160 = 64 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 32 5)
        have ha : Nat.totient 32 = 16 := (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 4)
        have hb : Nat.totient 5 = 4 := (Nat.totient_prime_pow_succ (p := 5) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide
  · have hh : Nat.totient 161 = 132 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 7 23)
        have ha : Nat.totient 7 = 6 := (Nat.totient_prime_pow_succ (p := 7) (by norm_num) 0)
        have hb : Nat.totient 23 = 22 := (Nat.totient_prime_pow_succ (p := 23) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide
  · have hh : Nat.totient 162 = 54 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 2 81)
        have ha : Nat.totient 2 = 1 := (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 0)
        have hb : Nat.totient 81 = 54 := (Nat.totient_prime_pow_succ (p := 3) (by norm_num) 3)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide

theorem totient_gt_twelve_163_170 (n : ℕ) (hlo : 163 ≤ n) (hhi : n ≤ 170) :
    12 < n.totient := by
  interval_cases n
  · have hh : Nat.totient 163 = 162 :=
      (Nat.totient_prime_pow_succ (p := 163) (by norm_num) 0)
    rw [hh]
    decide
  · have hh : Nat.totient 164 = 80 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 4 41)
        have ha : Nat.totient 4 = 2 := (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 1)
        have hb : Nat.totient 41 = 40 := (Nat.totient_prime_pow_succ (p := 41) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide
  · have hh : Nat.totient 165 = 80 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 3 55)
        have ha : Nat.totient 3 = 2 := (Nat.totient_prime_pow_succ (p := 3) (by norm_num) 0)
        have hb : Nat.totient 55 = 40 := (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 5 11)
        have ha : Nat.totient 5 = 4 := (Nat.totient_prime_pow_succ (p := 5) (by norm_num) 0)
        have hb : Nat.totient 11 = 10 := (Nat.totient_prime_pow_succ (p := 11) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide
  · have hh : Nat.totient 166 = 82 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 2 83)
        have ha : Nat.totient 2 = 1 := (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 0)
        have hb : Nat.totient 83 = 82 := (Nat.totient_prime_pow_succ (p := 83) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide
  · have hh : Nat.totient 167 = 166 :=
      (Nat.totient_prime_pow_succ (p := 167) (by norm_num) 0)
    rw [hh]
    decide
  · have hh : Nat.totient 168 = 48 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 8 21)
        have ha : Nat.totient 8 = 4 := (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 2)
        have hb : Nat.totient 21 = 12 := (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 3 7)
        have ha : Nat.totient 3 = 2 := (Nat.totient_prime_pow_succ (p := 3) (by norm_num) 0)
        have hb : Nat.totient 7 = 6 := (Nat.totient_prime_pow_succ (p := 7) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide
  · have hh : Nat.totient 169 = 156 :=
      (Nat.totient_prime_pow_succ (p := 13) (by norm_num) 1)
    rw [hh]
    decide
  · have hh : Nat.totient 170 = 64 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 2 85)
        have ha : Nat.totient 2 = 1 := (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 0)
        have hb : Nat.totient 85 = 64 := (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 5 17)
        have ha : Nat.totient 5 = 4 := (Nat.totient_prime_pow_succ (p := 5) (by norm_num) 0)
        have hb : Nat.totient 17 = 16 := (Nat.totient_prime_pow_succ (p := 17) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide

theorem totient_gt_twelve_171_178 (n : ℕ) (hlo : 171 ≤ n) (hhi : n ≤ 178) :
    12 < n.totient := by
  interval_cases n
  · have hh : Nat.totient 171 = 108 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 9 19)
        have ha : Nat.totient 9 = 6 := (Nat.totient_prime_pow_succ (p := 3) (by norm_num) 1)
        have hb : Nat.totient 19 = 18 := (Nat.totient_prime_pow_succ (p := 19) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide
  · have hh : Nat.totient 172 = 84 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 4 43)
        have ha : Nat.totient 4 = 2 := (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 1)
        have hb : Nat.totient 43 = 42 := (Nat.totient_prime_pow_succ (p := 43) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide
  · have hh : Nat.totient 173 = 172 :=
      (Nat.totient_prime_pow_succ (p := 173) (by norm_num) 0)
    rw [hh]
    decide
  · have hh : Nat.totient 174 = 56 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 2 87)
        have ha : Nat.totient 2 = 1 := (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 0)
        have hb : Nat.totient 87 = 56 := (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 3 29)
        have ha : Nat.totient 3 = 2 := (Nat.totient_prime_pow_succ (p := 3) (by norm_num) 0)
        have hb : Nat.totient 29 = 28 := (Nat.totient_prime_pow_succ (p := 29) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide
  · have hh : Nat.totient 175 = 120 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 25 7)
        have ha : Nat.totient 25 = 20 := (Nat.totient_prime_pow_succ (p := 5) (by norm_num) 1)
        have hb : Nat.totient 7 = 6 := (Nat.totient_prime_pow_succ (p := 7) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide
  · have hh : Nat.totient 176 = 80 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 16 11)
        have ha : Nat.totient 16 = 8 := (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 3)
        have hb : Nat.totient 11 = 10 := (Nat.totient_prime_pow_succ (p := 11) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide
  · have hh : Nat.totient 177 = 116 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 3 59)
        have ha : Nat.totient 3 = 2 := (Nat.totient_prime_pow_succ (p := 3) (by norm_num) 0)
        have hb : Nat.totient 59 = 58 := (Nat.totient_prime_pow_succ (p := 59) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide
  · have hh : Nat.totient 178 = 88 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 2 89)
        have ha : Nat.totient 2 = 1 := (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 0)
        have hb : Nat.totient 89 = 88 := (Nat.totient_prime_pow_succ (p := 89) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide

theorem totient_gt_twelve_179_186 (n : ℕ) (hlo : 179 ≤ n) (hhi : n ≤ 186) :
    12 < n.totient := by
  interval_cases n
  · have hh : Nat.totient 179 = 178 :=
      (Nat.totient_prime_pow_succ (p := 179) (by norm_num) 0)
    rw [hh]
    decide
  · have hh : Nat.totient 180 = 48 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 4 45)
        have ha : Nat.totient 4 = 2 := (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 1)
        have hb : Nat.totient 45 = 24 := (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 9 5)
        have ha : Nat.totient 9 = 6 := (Nat.totient_prime_pow_succ (p := 3) (by norm_num) 1)
        have hb : Nat.totient 5 = 4 := (Nat.totient_prime_pow_succ (p := 5) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide
  · have hh : Nat.totient 181 = 180 :=
      (Nat.totient_prime_pow_succ (p := 181) (by norm_num) 0)
    rw [hh]
    decide
  · have hh : Nat.totient 182 = 72 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 2 91)
        have ha : Nat.totient 2 = 1 := (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 0)
        have hb : Nat.totient 91 = 72 := (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 7 13)
        have ha : Nat.totient 7 = 6 := (Nat.totient_prime_pow_succ (p := 7) (by norm_num) 0)
        have hb : Nat.totient 13 = 12 := (Nat.totient_prime_pow_succ (p := 13) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide
  · have hh : Nat.totient 183 = 120 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 3 61)
        have ha : Nat.totient 3 = 2 := (Nat.totient_prime_pow_succ (p := 3) (by norm_num) 0)
        have hb : Nat.totient 61 = 60 := (Nat.totient_prime_pow_succ (p := 61) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide
  · have hh : Nat.totient 184 = 88 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 8 23)
        have ha : Nat.totient 8 = 4 := (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 2)
        have hb : Nat.totient 23 = 22 := (Nat.totient_prime_pow_succ (p := 23) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide
  · have hh : Nat.totient 185 = 144 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 5 37)
        have ha : Nat.totient 5 = 4 := (Nat.totient_prime_pow_succ (p := 5) (by norm_num) 0)
        have hb : Nat.totient 37 = 36 := (Nat.totient_prime_pow_succ (p := 37) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide
  · have hh : Nat.totient 186 = 60 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 2 93)
        have ha : Nat.totient 2 = 1 := (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 0)
        have hb : Nat.totient 93 = 60 := (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 3 31)
        have ha : Nat.totient 3 = 2 := (Nat.totient_prime_pow_succ (p := 3) (by norm_num) 0)
        have hb : Nat.totient 31 = 30 := (Nat.totient_prime_pow_succ (p := 31) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide

theorem totient_gt_twelve_187_194 (n : ℕ) (hlo : 187 ≤ n) (hhi : n ≤ 194) :
    12 < n.totient := by
  interval_cases n
  · have hh : Nat.totient 187 = 160 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 11 17)
        have ha : Nat.totient 11 = 10 := (Nat.totient_prime_pow_succ (p := 11) (by norm_num) 0)
        have hb : Nat.totient 17 = 16 := (Nat.totient_prime_pow_succ (p := 17) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide
  · have hh : Nat.totient 188 = 92 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 4 47)
        have ha : Nat.totient 4 = 2 := (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 1)
        have hb : Nat.totient 47 = 46 := (Nat.totient_prime_pow_succ (p := 47) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide
  · have hh : Nat.totient 189 = 108 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 27 7)
        have ha : Nat.totient 27 = 18 := (Nat.totient_prime_pow_succ (p := 3) (by norm_num) 2)
        have hb : Nat.totient 7 = 6 := (Nat.totient_prime_pow_succ (p := 7) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide
  · have hh : Nat.totient 190 = 72 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 2 95)
        have ha : Nat.totient 2 = 1 := (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 0)
        have hb : Nat.totient 95 = 72 := (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 5 19)
        have ha : Nat.totient 5 = 4 := (Nat.totient_prime_pow_succ (p := 5) (by norm_num) 0)
        have hb : Nat.totient 19 = 18 := (Nat.totient_prime_pow_succ (p := 19) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide
  · have hh : Nat.totient 191 = 190 :=
      (Nat.totient_prime_pow_succ (p := 191) (by norm_num) 0)
    rw [hh]
    decide
  · have hh : Nat.totient 192 = 64 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 64 3)
        have ha : Nat.totient 64 = 32 := (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 5)
        have hb : Nat.totient 3 = 2 := (Nat.totient_prime_pow_succ (p := 3) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide
  · have hh : Nat.totient 193 = 192 :=
      (Nat.totient_prime_pow_succ (p := 193) (by norm_num) 0)
    rw [hh]
    decide
  · have hh : Nat.totient 194 = 96 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 2 97)
        have ha : Nat.totient 2 = 1 := (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 0)
        have hb : Nat.totient 97 = 96 := (Nat.totient_prime_pow_succ (p := 97) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide

theorem totient_gt_twelve_195_202 (n : ℕ) (hlo : 195 ≤ n) (hhi : n ≤ 202) :
    12 < n.totient := by
  interval_cases n
  · have hh : Nat.totient 195 = 96 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 3 65)
        have ha : Nat.totient 3 = 2 := (Nat.totient_prime_pow_succ (p := 3) (by norm_num) 0)
        have hb : Nat.totient 65 = 48 := (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 5 13)
        have ha : Nat.totient 5 = 4 := (Nat.totient_prime_pow_succ (p := 5) (by norm_num) 0)
        have hb : Nat.totient 13 = 12 := (Nat.totient_prime_pow_succ (p := 13) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide
  · have hh : Nat.totient 196 = 84 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 4 49)
        have ha : Nat.totient 4 = 2 := (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 1)
        have hb : Nat.totient 49 = 42 := (Nat.totient_prime_pow_succ (p := 7) (by norm_num) 1)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide
  · have hh : Nat.totient 197 = 196 :=
      (Nat.totient_prime_pow_succ (p := 197) (by norm_num) 0)
    rw [hh]
    decide
  · have hh : Nat.totient 198 = 60 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 2 99)
        have ha : Nat.totient 2 = 1 := (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 0)
        have hb : Nat.totient 99 = 60 := (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 9 11)
        have ha : Nat.totient 9 = 6 := (Nat.totient_prime_pow_succ (p := 3) (by norm_num) 1)
        have hb : Nat.totient 11 = 10 := (Nat.totient_prime_pow_succ (p := 11) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide
  · have hh : Nat.totient 199 = 198 :=
      (Nat.totient_prime_pow_succ (p := 199) (by norm_num) 0)
    rw [hh]
    decide
  · have hh : Nat.totient 200 = 80 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 8 25)
        have ha : Nat.totient 8 = 4 := (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 2)
        have hb : Nat.totient 25 = 20 := (Nat.totient_prime_pow_succ (p := 5) (by norm_num) 1)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide
  · have hh : Nat.totient 201 = 132 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 3 67)
        have ha : Nat.totient 3 = 2 := (Nat.totient_prime_pow_succ (p := 3) (by norm_num) 0)
        have hb : Nat.totient 67 = 66 := (Nat.totient_prime_pow_succ (p := 67) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide
  · have hh : Nat.totient 202 = 100 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 2 101)
        have ha : Nat.totient 2 = 1 := (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 0)
        have hb : Nat.totient 101 = 100 := (Nat.totient_prime_pow_succ (p := 101) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide

theorem totient_gt_twelve_203_210 (n : ℕ) (hlo : 203 ≤ n) (hhi : n ≤ 210) :
    12 < n.totient := by
  interval_cases n
  · have hh : Nat.totient 203 = 168 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 7 29)
        have ha : Nat.totient 7 = 6 := (Nat.totient_prime_pow_succ (p := 7) (by norm_num) 0)
        have hb : Nat.totient 29 = 28 := (Nat.totient_prime_pow_succ (p := 29) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide
  · have hh : Nat.totient 204 = 64 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 4 51)
        have ha : Nat.totient 4 = 2 := (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 1)
        have hb : Nat.totient 51 = 32 := (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 3 17)
        have ha : Nat.totient 3 = 2 := (Nat.totient_prime_pow_succ (p := 3) (by norm_num) 0)
        have hb : Nat.totient 17 = 16 := (Nat.totient_prime_pow_succ (p := 17) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide
  · have hh : Nat.totient 205 = 160 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 5 41)
        have ha : Nat.totient 5 = 4 := (Nat.totient_prime_pow_succ (p := 5) (by norm_num) 0)
        have hb : Nat.totient 41 = 40 := (Nat.totient_prime_pow_succ (p := 41) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide
  · have hh : Nat.totient 206 = 102 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 2 103)
        have ha : Nat.totient 2 = 1 := (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 0)
        have hb : Nat.totient 103 = 102 := (Nat.totient_prime_pow_succ (p := 103) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide
  · have hh : Nat.totient 207 = 132 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 9 23)
        have ha : Nat.totient 9 = 6 := (Nat.totient_prime_pow_succ (p := 3) (by norm_num) 1)
        have hb : Nat.totient 23 = 22 := (Nat.totient_prime_pow_succ (p := 23) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide
  · have hh : Nat.totient 208 = 96 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 16 13)
        have ha : Nat.totient 16 = 8 := (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 3)
        have hb : Nat.totient 13 = 12 := (Nat.totient_prime_pow_succ (p := 13) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide
  · have hh : Nat.totient 209 = 180 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 11 19)
        have ha : Nat.totient 11 = 10 := (Nat.totient_prime_pow_succ (p := 11) (by norm_num) 0)
        have hb : Nat.totient 19 = 18 := (Nat.totient_prime_pow_succ (p := 19) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide
  · have hh : Nat.totient 210 = 48 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 2 105)
        have ha : Nat.totient 2 = 1 := (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 0)
        have hb : Nat.totient 105 = 48 := (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 3 35)
        have ha : Nat.totient 3 = 2 := (Nat.totient_prime_pow_succ (p := 3) (by norm_num) 0)
        have hb : Nat.totient 35 = 24 := (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 5 7)
        have ha : Nat.totient 5 = 4 := (Nat.totient_prime_pow_succ (p := 5) (by norm_num) 0)
        have hb : Nat.totient 7 = 6 := (Nat.totient_prime_pow_succ (p := 7) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
        rw [ha, hb] at h
        exact h)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide

theorem totient_gt_twelve_211_218 (n : ℕ) (hlo : 211 ≤ n) (hhi : n ≤ 218) :
    12 < n.totient := by
  interval_cases n
  · have hh : Nat.totient 211 = 210 :=
      (Nat.totient_prime_pow_succ (p := 211) (by norm_num) 0)
    rw [hh]
    decide
  · have hh : Nat.totient 212 = 104 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 4 53)
        have ha : Nat.totient 4 = 2 := (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 1)
        have hb : Nat.totient 53 = 52 := (Nat.totient_prime_pow_succ (p := 53) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide
  · have hh : Nat.totient 213 = 140 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 3 71)
        have ha : Nat.totient 3 = 2 := (Nat.totient_prime_pow_succ (p := 3) (by norm_num) 0)
        have hb : Nat.totient 71 = 70 := (Nat.totient_prime_pow_succ (p := 71) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide
  · have hh : Nat.totient 214 = 106 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 2 107)
        have ha : Nat.totient 2 = 1 := (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 0)
        have hb : Nat.totient 107 = 106 := (Nat.totient_prime_pow_succ (p := 107) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide
  · have hh : Nat.totient 215 = 168 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 5 43)
        have ha : Nat.totient 5 = 4 := (Nat.totient_prime_pow_succ (p := 5) (by norm_num) 0)
        have hb : Nat.totient 43 = 42 := (Nat.totient_prime_pow_succ (p := 43) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide
  · have hh : Nat.totient 216 = 72 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 8 27)
        have ha : Nat.totient 8 = 4 := (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 2)
        have hb : Nat.totient 27 = 18 := (Nat.totient_prime_pow_succ (p := 3) (by norm_num) 2)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide
  · have hh : Nat.totient 217 = 180 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 7 31)
        have ha : Nat.totient 7 = 6 := (Nat.totient_prime_pow_succ (p := 7) (by norm_num) 0)
        have hb : Nat.totient 31 = 30 := (Nat.totient_prime_pow_succ (p := 31) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide
  · have hh : Nat.totient 218 = 108 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 2 109)
        have ha : Nat.totient 2 = 1 := (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 0)
        have hb : Nat.totient 109 = 108 := (Nat.totient_prime_pow_succ (p := 109) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide

theorem totient_gt_twelve_219_226 (n : ℕ) (hlo : 219 ≤ n) (hhi : n ≤ 226) :
    12 < n.totient := by
  interval_cases n
  · have hh : Nat.totient 219 = 144 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 3 73)
        have ha : Nat.totient 3 = 2 := (Nat.totient_prime_pow_succ (p := 3) (by norm_num) 0)
        have hb : Nat.totient 73 = 72 := (Nat.totient_prime_pow_succ (p := 73) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide
  · have hh : Nat.totient 220 = 80 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 4 55)
        have ha : Nat.totient 4 = 2 := (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 1)
        have hb : Nat.totient 55 = 40 := (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 5 11)
        have ha : Nat.totient 5 = 4 := (Nat.totient_prime_pow_succ (p := 5) (by norm_num) 0)
        have hb : Nat.totient 11 = 10 := (Nat.totient_prime_pow_succ (p := 11) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide
  · have hh : Nat.totient 221 = 192 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 13 17)
        have ha : Nat.totient 13 = 12 := (Nat.totient_prime_pow_succ (p := 13) (by norm_num) 0)
        have hb : Nat.totient 17 = 16 := (Nat.totient_prime_pow_succ (p := 17) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide
  · have hh : Nat.totient 222 = 72 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 2 111)
        have ha : Nat.totient 2 = 1 := (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 0)
        have hb : Nat.totient 111 = 72 := (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 3 37)
        have ha : Nat.totient 3 = 2 := (Nat.totient_prime_pow_succ (p := 3) (by norm_num) 0)
        have hb : Nat.totient 37 = 36 := (Nat.totient_prime_pow_succ (p := 37) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide
  · have hh : Nat.totient 223 = 222 :=
      (Nat.totient_prime_pow_succ (p := 223) (by norm_num) 0)
    rw [hh]
    decide
  · have hh : Nat.totient 224 = 96 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 32 7)
        have ha : Nat.totient 32 = 16 := (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 4)
        have hb : Nat.totient 7 = 6 := (Nat.totient_prime_pow_succ (p := 7) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide
  · have hh : Nat.totient 225 = 120 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 9 25)
        have ha : Nat.totient 9 = 6 := (Nat.totient_prime_pow_succ (p := 3) (by norm_num) 1)
        have hb : Nat.totient 25 = 20 := (Nat.totient_prime_pow_succ (p := 5) (by norm_num) 1)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide
  · have hh : Nat.totient 226 = 112 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 2 113)
        have ha : Nat.totient 2 = 1 := (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 0)
        have hb : Nat.totient 113 = 112 := (Nat.totient_prime_pow_succ (p := 113) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide

theorem totient_gt_twelve_227_234 (n : ℕ) (hlo : 227 ≤ n) (hhi : n ≤ 234) :
    12 < n.totient := by
  interval_cases n
  · have hh : Nat.totient 227 = 226 :=
      (Nat.totient_prime_pow_succ (p := 227) (by norm_num) 0)
    rw [hh]
    decide
  · have hh : Nat.totient 228 = 72 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 4 57)
        have ha : Nat.totient 4 = 2 := (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 1)
        have hb : Nat.totient 57 = 36 := (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 3 19)
        have ha : Nat.totient 3 = 2 := (Nat.totient_prime_pow_succ (p := 3) (by norm_num) 0)
        have hb : Nat.totient 19 = 18 := (Nat.totient_prime_pow_succ (p := 19) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide
  · have hh : Nat.totient 229 = 228 :=
      (Nat.totient_prime_pow_succ (p := 229) (by norm_num) 0)
    rw [hh]
    decide
  · have hh : Nat.totient 230 = 88 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 2 115)
        have ha : Nat.totient 2 = 1 := (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 0)
        have hb : Nat.totient 115 = 88 := (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 5 23)
        have ha : Nat.totient 5 = 4 := (Nat.totient_prime_pow_succ (p := 5) (by norm_num) 0)
        have hb : Nat.totient 23 = 22 := (Nat.totient_prime_pow_succ (p := 23) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide
  · have hh : Nat.totient 231 = 120 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 3 77)
        have ha : Nat.totient 3 = 2 := (Nat.totient_prime_pow_succ (p := 3) (by norm_num) 0)
        have hb : Nat.totient 77 = 60 := (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 7 11)
        have ha : Nat.totient 7 = 6 := (Nat.totient_prime_pow_succ (p := 7) (by norm_num) 0)
        have hb : Nat.totient 11 = 10 := (Nat.totient_prime_pow_succ (p := 11) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide
  · have hh : Nat.totient 232 = 112 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 8 29)
        have ha : Nat.totient 8 = 4 := (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 2)
        have hb : Nat.totient 29 = 28 := (Nat.totient_prime_pow_succ (p := 29) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide
  · have hh : Nat.totient 233 = 232 :=
      (Nat.totient_prime_pow_succ (p := 233) (by norm_num) 0)
    rw [hh]
    decide
  · have hh : Nat.totient 234 = 72 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 2 117)
        have ha : Nat.totient 2 = 1 := (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 0)
        have hb : Nat.totient 117 = 72 := (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 9 13)
        have ha : Nat.totient 9 = 6 := (Nat.totient_prime_pow_succ (p := 3) (by norm_num) 1)
        have hb : Nat.totient 13 = 12 := (Nat.totient_prime_pow_succ (p := 13) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide

theorem totient_gt_twelve_235_242 (n : ℕ) (hlo : 235 ≤ n) (hhi : n ≤ 242) :
    12 < n.totient := by
  interval_cases n
  · have hh : Nat.totient 235 = 184 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 5 47)
        have ha : Nat.totient 5 = 4 := (Nat.totient_prime_pow_succ (p := 5) (by norm_num) 0)
        have hb : Nat.totient 47 = 46 := (Nat.totient_prime_pow_succ (p := 47) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide
  · have hh : Nat.totient 236 = 116 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 4 59)
        have ha : Nat.totient 4 = 2 := (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 1)
        have hb : Nat.totient 59 = 58 := (Nat.totient_prime_pow_succ (p := 59) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide
  · have hh : Nat.totient 237 = 156 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 3 79)
        have ha : Nat.totient 3 = 2 := (Nat.totient_prime_pow_succ (p := 3) (by norm_num) 0)
        have hb : Nat.totient 79 = 78 := (Nat.totient_prime_pow_succ (p := 79) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide
  · have hh : Nat.totient 238 = 96 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 2 119)
        have ha : Nat.totient 2 = 1 := (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 0)
        have hb : Nat.totient 119 = 96 := (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 7 17)
        have ha : Nat.totient 7 = 6 := (Nat.totient_prime_pow_succ (p := 7) (by norm_num) 0)
        have hb : Nat.totient 17 = 16 := (Nat.totient_prime_pow_succ (p := 17) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide
  · have hh : Nat.totient 239 = 238 :=
      (Nat.totient_prime_pow_succ (p := 239) (by norm_num) 0)
    rw [hh]
    decide
  · have hh : Nat.totient 240 = 64 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 16 15)
        have ha : Nat.totient 16 = 8 := (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 3)
        have hb : Nat.totient 15 = 8 := (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 3 5)
        have ha : Nat.totient 3 = 2 := (Nat.totient_prime_pow_succ (p := 3) (by norm_num) 0)
        have hb : Nat.totient 5 = 4 := (Nat.totient_prime_pow_succ (p := 5) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide
  · have hh : Nat.totient 241 = 240 :=
      (Nat.totient_prime_pow_succ (p := 241) (by norm_num) 0)
    rw [hh]
    decide
  · have hh : Nat.totient 242 = 110 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 2 121)
        have ha : Nat.totient 2 = 1 := (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 0)
        have hb : Nat.totient 121 = 110 := (Nat.totient_prime_pow_succ (p := 11) (by norm_num) 1)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide

theorem totient_gt_twelve_243_250 (n : ℕ) (hlo : 243 ≤ n) (hhi : n ≤ 250) :
    12 < n.totient := by
  interval_cases n
  · have hh : Nat.totient 243 = 162 :=
      (Nat.totient_prime_pow_succ (p := 3) (by norm_num) 4)
    rw [hh]
    decide
  · have hh : Nat.totient 244 = 120 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 4 61)
        have ha : Nat.totient 4 = 2 := (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 1)
        have hb : Nat.totient 61 = 60 := (Nat.totient_prime_pow_succ (p := 61) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide
  · have hh : Nat.totient 245 = 168 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 5 49)
        have ha : Nat.totient 5 = 4 := (Nat.totient_prime_pow_succ (p := 5) (by norm_num) 0)
        have hb : Nat.totient 49 = 42 := (Nat.totient_prime_pow_succ (p := 7) (by norm_num) 1)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide
  · have hh : Nat.totient 246 = 80 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 2 123)
        have ha : Nat.totient 2 = 1 := (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 0)
        have hb : Nat.totient 123 = 80 := (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 3 41)
        have ha : Nat.totient 3 = 2 := (Nat.totient_prime_pow_succ (p := 3) (by norm_num) 0)
        have hb : Nat.totient 41 = 40 := (Nat.totient_prime_pow_succ (p := 41) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide
  · have hh : Nat.totient 247 = 216 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 13 19)
        have ha : Nat.totient 13 = 12 := (Nat.totient_prime_pow_succ (p := 13) (by norm_num) 0)
        have hb : Nat.totient 19 = 18 := (Nat.totient_prime_pow_succ (p := 19) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide
  · have hh : Nat.totient 248 = 120 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 8 31)
        have ha : Nat.totient 8 = 4 := (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 2)
        have hb : Nat.totient 31 = 30 := (Nat.totient_prime_pow_succ (p := 31) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide
  · have hh : Nat.totient 249 = 164 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 3 83)
        have ha : Nat.totient 3 = 2 := (Nat.totient_prime_pow_succ (p := 3) (by norm_num) 0)
        have hb : Nat.totient 83 = 82 := (Nat.totient_prime_pow_succ (p := 83) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide
  · have hh : Nat.totient 250 = 100 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 2 125)
        have ha : Nat.totient 2 = 1 := (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 0)
        have hb : Nat.totient 125 = 100 := (Nat.totient_prime_pow_succ (p := 5) (by norm_num) 2)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide

theorem totient_gt_twelve_251_258 (n : ℕ) (hlo : 251 ≤ n) (hhi : n ≤ 258) :
    12 < n.totient := by
  interval_cases n
  · have hh : Nat.totient 251 = 250 :=
      (Nat.totient_prime_pow_succ (p := 251) (by norm_num) 0)
    rw [hh]
    decide
  · have hh : Nat.totient 252 = 72 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 4 63)
        have ha : Nat.totient 4 = 2 := (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 1)
        have hb : Nat.totient 63 = 36 := (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 9 7)
        have ha : Nat.totient 9 = 6 := (Nat.totient_prime_pow_succ (p := 3) (by norm_num) 1)
        have hb : Nat.totient 7 = 6 := (Nat.totient_prime_pow_succ (p := 7) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide
  · have hh : Nat.totient 253 = 220 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 11 23)
        have ha : Nat.totient 11 = 10 := (Nat.totient_prime_pow_succ (p := 11) (by norm_num) 0)
        have hb : Nat.totient 23 = 22 := (Nat.totient_prime_pow_succ (p := 23) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide
  · have hh : Nat.totient 254 = 126 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 2 127)
        have ha : Nat.totient 2 = 1 := (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 0)
        have hb : Nat.totient 127 = 126 := (Nat.totient_prime_pow_succ (p := 127) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide
  · have hh : Nat.totient 255 = 128 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 3 85)
        have ha : Nat.totient 3 = 2 := (Nat.totient_prime_pow_succ (p := 3) (by norm_num) 0)
        have hb : Nat.totient 85 = 64 := (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 5 17)
        have ha : Nat.totient 5 = 4 := (Nat.totient_prime_pow_succ (p := 5) (by norm_num) 0)
        have hb : Nat.totient 17 = 16 := (Nat.totient_prime_pow_succ (p := 17) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide
  · have hh : Nat.totient 256 = 128 :=
      (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 7)
    rw [hh]
    decide
  · have hh : Nat.totient 257 = 256 :=
      (Nat.totient_prime_pow_succ (p := 257) (by norm_num) 0)
    rw [hh]
    decide
  · have hh : Nat.totient 258 = 84 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 2 129)
        have ha : Nat.totient 2 = 1 := (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 0)
        have hb : Nat.totient 129 = 84 := (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 3 43)
        have ha : Nat.totient 3 = 2 := (Nat.totient_prime_pow_succ (p := 3) (by norm_num) 0)
        have hb : Nat.totient 43 = 42 := (Nat.totient_prime_pow_succ (p := 43) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide

theorem totient_gt_twelve_259_266 (n : ℕ) (hlo : 259 ≤ n) (hhi : n ≤ 266) :
    12 < n.totient := by
  interval_cases n
  · have hh : Nat.totient 259 = 216 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 7 37)
        have ha : Nat.totient 7 = 6 := (Nat.totient_prime_pow_succ (p := 7) (by norm_num) 0)
        have hb : Nat.totient 37 = 36 := (Nat.totient_prime_pow_succ (p := 37) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide
  · have hh : Nat.totient 260 = 96 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 4 65)
        have ha : Nat.totient 4 = 2 := (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 1)
        have hb : Nat.totient 65 = 48 := (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 5 13)
        have ha : Nat.totient 5 = 4 := (Nat.totient_prime_pow_succ (p := 5) (by norm_num) 0)
        have hb : Nat.totient 13 = 12 := (Nat.totient_prime_pow_succ (p := 13) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide
  · have hh : Nat.totient 261 = 168 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 9 29)
        have ha : Nat.totient 9 = 6 := (Nat.totient_prime_pow_succ (p := 3) (by norm_num) 1)
        have hb : Nat.totient 29 = 28 := (Nat.totient_prime_pow_succ (p := 29) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide
  · have hh : Nat.totient 262 = 130 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 2 131)
        have ha : Nat.totient 2 = 1 := (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 0)
        have hb : Nat.totient 131 = 130 := (Nat.totient_prime_pow_succ (p := 131) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide
  · have hh : Nat.totient 263 = 262 :=
      (Nat.totient_prime_pow_succ (p := 263) (by norm_num) 0)
    rw [hh]
    decide
  · have hh : Nat.totient 264 = 80 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 8 33)
        have ha : Nat.totient 8 = 4 := (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 2)
        have hb : Nat.totient 33 = 20 := (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 3 11)
        have ha : Nat.totient 3 = 2 := (Nat.totient_prime_pow_succ (p := 3) (by norm_num) 0)
        have hb : Nat.totient 11 = 10 := (Nat.totient_prime_pow_succ (p := 11) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide
  · have hh : Nat.totient 265 = 208 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 5 53)
        have ha : Nat.totient 5 = 4 := (Nat.totient_prime_pow_succ (p := 5) (by norm_num) 0)
        have hb : Nat.totient 53 = 52 := (Nat.totient_prime_pow_succ (p := 53) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide
  · have hh : Nat.totient 266 = 108 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 2 133)
        have ha : Nat.totient 2 = 1 := (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 0)
        have hb : Nat.totient 133 = 108 := (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 7 19)
        have ha : Nat.totient 7 = 6 := (Nat.totient_prime_pow_succ (p := 7) (by norm_num) 0)
        have hb : Nat.totient 19 = 18 := (Nat.totient_prime_pow_succ (p := 19) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide

theorem totient_gt_twelve_267_274 (n : ℕ) (hlo : 267 ≤ n) (hhi : n ≤ 274) :
    12 < n.totient := by
  interval_cases n
  · have hh : Nat.totient 267 = 176 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 3 89)
        have ha : Nat.totient 3 = 2 := (Nat.totient_prime_pow_succ (p := 3) (by norm_num) 0)
        have hb : Nat.totient 89 = 88 := (Nat.totient_prime_pow_succ (p := 89) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide
  · have hh : Nat.totient 268 = 132 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 4 67)
        have ha : Nat.totient 4 = 2 := (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 1)
        have hb : Nat.totient 67 = 66 := (Nat.totient_prime_pow_succ (p := 67) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide
  · have hh : Nat.totient 269 = 268 :=
      (Nat.totient_prime_pow_succ (p := 269) (by norm_num) 0)
    rw [hh]
    decide
  · have hh : Nat.totient 270 = 72 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 2 135)
        have ha : Nat.totient 2 = 1 := (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 0)
        have hb : Nat.totient 135 = 72 := (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 27 5)
        have ha : Nat.totient 27 = 18 := (Nat.totient_prime_pow_succ (p := 3) (by norm_num) 2)
        have hb : Nat.totient 5 = 4 := (Nat.totient_prime_pow_succ (p := 5) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide
  · have hh : Nat.totient 271 = 270 :=
      (Nat.totient_prime_pow_succ (p := 271) (by norm_num) 0)
    rw [hh]
    decide
  · have hh : Nat.totient 272 = 128 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 16 17)
        have ha : Nat.totient 16 = 8 := (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 3)
        have hb : Nat.totient 17 = 16 := (Nat.totient_prime_pow_succ (p := 17) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide
  · have hh : Nat.totient 273 = 144 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 3 91)
        have ha : Nat.totient 3 = 2 := (Nat.totient_prime_pow_succ (p := 3) (by norm_num) 0)
        have hb : Nat.totient 91 = 72 := (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 7 13)
        have ha : Nat.totient 7 = 6 := (Nat.totient_prime_pow_succ (p := 7) (by norm_num) 0)
        have hb : Nat.totient 13 = 12 := (Nat.totient_prime_pow_succ (p := 13) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide
  · have hh : Nat.totient 274 = 136 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 2 137)
        have ha : Nat.totient 2 = 1 := (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 0)
        have hb : Nat.totient 137 = 136 := (Nat.totient_prime_pow_succ (p := 137) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide

theorem totient_gt_twelve_275_282 (n : ℕ) (hlo : 275 ≤ n) (hhi : n ≤ 282) :
    12 < n.totient := by
  interval_cases n
  · have hh : Nat.totient 275 = 200 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 25 11)
        have ha : Nat.totient 25 = 20 := (Nat.totient_prime_pow_succ (p := 5) (by norm_num) 1)
        have hb : Nat.totient 11 = 10 := (Nat.totient_prime_pow_succ (p := 11) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide
  · have hh : Nat.totient 276 = 88 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 4 69)
        have ha : Nat.totient 4 = 2 := (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 1)
        have hb : Nat.totient 69 = 44 := (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 3 23)
        have ha : Nat.totient 3 = 2 := (Nat.totient_prime_pow_succ (p := 3) (by norm_num) 0)
        have hb : Nat.totient 23 = 22 := (Nat.totient_prime_pow_succ (p := 23) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide
  · have hh : Nat.totient 277 = 276 :=
      (Nat.totient_prime_pow_succ (p := 277) (by norm_num) 0)
    rw [hh]
    decide
  · have hh : Nat.totient 278 = 138 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 2 139)
        have ha : Nat.totient 2 = 1 := (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 0)
        have hb : Nat.totient 139 = 138 := (Nat.totient_prime_pow_succ (p := 139) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide
  · have hh : Nat.totient 279 = 180 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 9 31)
        have ha : Nat.totient 9 = 6 := (Nat.totient_prime_pow_succ (p := 3) (by norm_num) 1)
        have hb : Nat.totient 31 = 30 := (Nat.totient_prime_pow_succ (p := 31) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide
  · have hh : Nat.totient 280 = 96 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 8 35)
        have ha : Nat.totient 8 = 4 := (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 2)
        have hb : Nat.totient 35 = 24 := (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 5 7)
        have ha : Nat.totient 5 = 4 := (Nat.totient_prime_pow_succ (p := 5) (by norm_num) 0)
        have hb : Nat.totient 7 = 6 := (Nat.totient_prime_pow_succ (p := 7) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide
  · have hh : Nat.totient 281 = 280 :=
      (Nat.totient_prime_pow_succ (p := 281) (by norm_num) 0)
    rw [hh]
    decide
  · have hh : Nat.totient 282 = 92 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 2 141)
        have ha : Nat.totient 2 = 1 := (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 0)
        have hb : Nat.totient 141 = 92 := (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 3 47)
        have ha : Nat.totient 3 = 2 := (Nat.totient_prime_pow_succ (p := 3) (by norm_num) 0)
        have hb : Nat.totient 47 = 46 := (Nat.totient_prime_pow_succ (p := 47) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide

theorem totient_gt_twelve_283_288 (n : ℕ) (hlo : 283 ≤ n) (hhi : n ≤ 288) :
    12 < n.totient := by
  interval_cases n
  · have hh : Nat.totient 283 = 282 :=
      (Nat.totient_prime_pow_succ (p := 283) (by norm_num) 0)
    rw [hh]
    decide
  · have hh : Nat.totient 284 = 140 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 4 71)
        have ha : Nat.totient 4 = 2 := (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 1)
        have hb : Nat.totient 71 = 70 := (Nat.totient_prime_pow_succ (p := 71) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide
  · have hh : Nat.totient 285 = 144 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 3 95)
        have ha : Nat.totient 3 = 2 := (Nat.totient_prime_pow_succ (p := 3) (by norm_num) 0)
        have hb : Nat.totient 95 = 72 := (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 5 19)
        have ha : Nat.totient 5 = 4 := (Nat.totient_prime_pow_succ (p := 5) (by norm_num) 0)
        have hb : Nat.totient 19 = 18 := (Nat.totient_prime_pow_succ (p := 19) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide
  · have hh : Nat.totient 286 = 120 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 2 143)
        have ha : Nat.totient 2 = 1 := (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 0)
        have hb : Nat.totient 143 = 120 := (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 11 13)
        have ha : Nat.totient 11 = 10 := (Nat.totient_prime_pow_succ (p := 11) (by norm_num) 0)
        have hb : Nat.totient 13 = 12 := (Nat.totient_prime_pow_succ (p := 13) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide
  · have hh : Nat.totient 287 = 240 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 7 41)
        have ha : Nat.totient 7 = 6 := (Nat.totient_prime_pow_succ (p := 7) (by norm_num) 0)
        have hb : Nat.totient 41 = 40 := (Nat.totient_prime_pow_succ (p := 41) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide
  · have hh : Nat.totient 288 = 96 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 32 9)
        have ha : Nat.totient 32 = 16 := (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 4)
        have hb : Nat.totient 9 = 6 := (Nat.totient_prime_pow_succ (p := 3) (by norm_num) 1)
        rw [ha, hb] at h
        exact h)
    rw [hh]
    decide

theorem le_forty_two_of_totient_le_twelve (n : ℕ) (hn : n.totient ≤ 12) : n ≤ 42 := by
  have hb := le_288_of_totient_le_twelve n hn
  by_contra h
  have hlo : 43 ≤ n := by omega
  by_cases h50 : n ≤ 50
  · exact (not_lt_of_ge hn) (totient_gt_twelve_43_50 n (by omega) h50)
  by_cases h58 : n ≤ 58
  · exact (not_lt_of_ge hn) (totient_gt_twelve_51_58 n (by omega) h58)
  by_cases h66 : n ≤ 66
  · exact (not_lt_of_ge hn) (totient_gt_twelve_59_66 n (by omega) h66)
  by_cases h74 : n ≤ 74
  · exact (not_lt_of_ge hn) (totient_gt_twelve_67_74 n (by omega) h74)
  by_cases h82 : n ≤ 82
  · exact (not_lt_of_ge hn) (totient_gt_twelve_75_82 n (by omega) h82)
  by_cases h90 : n ≤ 90
  · exact (not_lt_of_ge hn) (totient_gt_twelve_83_90 n (by omega) h90)
  by_cases h98 : n ≤ 98
  · exact (not_lt_of_ge hn) (totient_gt_twelve_91_98 n (by omega) h98)
  by_cases h106 : n ≤ 106
  · exact (not_lt_of_ge hn) (totient_gt_twelve_99_106 n (by omega) h106)
  by_cases h114 : n ≤ 114
  · exact (not_lt_of_ge hn) (totient_gt_twelve_107_114 n (by omega) h114)
  by_cases h122 : n ≤ 122
  · exact (not_lt_of_ge hn) (totient_gt_twelve_115_122 n (by omega) h122)
  by_cases h130 : n ≤ 130
  · exact (not_lt_of_ge hn) (totient_gt_twelve_123_130 n (by omega) h130)
  by_cases h138 : n ≤ 138
  · exact (not_lt_of_ge hn) (totient_gt_twelve_131_138 n (by omega) h138)
  by_cases h146 : n ≤ 146
  · exact (not_lt_of_ge hn) (totient_gt_twelve_139_146 n (by omega) h146)
  by_cases h154 : n ≤ 154
  · exact (not_lt_of_ge hn) (totient_gt_twelve_147_154 n (by omega) h154)
  by_cases h162 : n ≤ 162
  · exact (not_lt_of_ge hn) (totient_gt_twelve_155_162 n (by omega) h162)
  by_cases h170 : n ≤ 170
  · exact (not_lt_of_ge hn) (totient_gt_twelve_163_170 n (by omega) h170)
  by_cases h178 : n ≤ 178
  · exact (not_lt_of_ge hn) (totient_gt_twelve_171_178 n (by omega) h178)
  by_cases h186 : n ≤ 186
  · exact (not_lt_of_ge hn) (totient_gt_twelve_179_186 n (by omega) h186)
  by_cases h194 : n ≤ 194
  · exact (not_lt_of_ge hn) (totient_gt_twelve_187_194 n (by omega) h194)
  by_cases h202 : n ≤ 202
  · exact (not_lt_of_ge hn) (totient_gt_twelve_195_202 n (by omega) h202)
  by_cases h210 : n ≤ 210
  · exact (not_lt_of_ge hn) (totient_gt_twelve_203_210 n (by omega) h210)
  by_cases h218 : n ≤ 218
  · exact (not_lt_of_ge hn) (totient_gt_twelve_211_218 n (by omega) h218)
  by_cases h226 : n ≤ 226
  · exact (not_lt_of_ge hn) (totient_gt_twelve_219_226 n (by omega) h226)
  by_cases h234 : n ≤ 234
  · exact (not_lt_of_ge hn) (totient_gt_twelve_227_234 n (by omega) h234)
  by_cases h242 : n ≤ 242
  · exact (not_lt_of_ge hn) (totient_gt_twelve_235_242 n (by omega) h242)
  by_cases h250 : n ≤ 250
  · exact (not_lt_of_ge hn) (totient_gt_twelve_243_250 n (by omega) h250)
  by_cases h258 : n ≤ 258
  · exact (not_lt_of_ge hn) (totient_gt_twelve_251_258 n (by omega) h258)
  by_cases h266 : n ≤ 266
  · exact (not_lt_of_ge hn) (totient_gt_twelve_259_266 n (by omega) h266)
  by_cases h274 : n ≤ 274
  · exact (not_lt_of_ge hn) (totient_gt_twelve_267_274 n (by omega) h274)
  by_cases h282 : n ≤ 282
  · exact (not_lt_of_ge hn) (totient_gt_twelve_275_282 n (by omega) h282)
  exact (not_lt_of_ge hn) (totient_gt_twelve_283_288 n (by omega) hb)

theorem mem_smallTotientOrders (n : ℕ) (hn : 6 < n) (hφ : n.totient ≤ 12) :
    n ∈ smallTotientOrders := by
  have hb := le_forty_two_of_totient_le_twelve n hφ
  interval_cases n
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · have hh : Nat.totient 17 = 16 :=
      (Nat.totient_prime_pow_succ (p := 17) (by norm_num) 0)
    rw [hh] at hφ
    omega
  · decide
  · have hh : Nat.totient 19 = 18 :=
      (Nat.totient_prime_pow_succ (p := 19) (by norm_num) 0)
    rw [hh] at hφ
    omega
  · decide
  · decide
  · decide
  · have hh : Nat.totient 23 = 22 :=
      (Nat.totient_prime_pow_succ (p := 23) (by norm_num) 0)
    rw [hh] at hφ
    omega
  · decide
  · have hh : Nat.totient 25 = 20 :=
      (Nat.totient_prime_pow_succ (p := 5) (by norm_num) 1)
    rw [hh] at hφ
    omega
  · decide
  · have hh : Nat.totient 27 = 18 :=
      (Nat.totient_prime_pow_succ (p := 3) (by norm_num) 2)
    rw [hh] at hφ
    omega
  · decide
  · have hh : Nat.totient 29 = 28 :=
      (Nat.totient_prime_pow_succ (p := 29) (by norm_num) 0)
    rw [hh] at hφ
    omega
  · decide
  · have hh : Nat.totient 31 = 30 :=
      (Nat.totient_prime_pow_succ (p := 31) (by norm_num) 0)
    rw [hh] at hφ
    omega
  · have hh : Nat.totient 32 = 16 :=
      (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 4)
    rw [hh] at hφ
    omega
  · have hh : Nat.totient 33 = 20 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 3 11)
        have ha : Nat.totient 3 = 2 := (Nat.totient_prime_pow_succ (p := 3) (by norm_num) 0)
        have hb : Nat.totient 11 = 10 := (Nat.totient_prime_pow_succ (p := 11) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
    rw [hh] at hφ
    omega
  · have hh : Nat.totient 34 = 16 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 2 17)
        have ha : Nat.totient 2 = 1 := (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 0)
        have hb : Nat.totient 17 = 16 := (Nat.totient_prime_pow_succ (p := 17) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
    rw [hh] at hφ
    omega
  · have hh : Nat.totient 35 = 24 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 5 7)
        have ha : Nat.totient 5 = 4 := (Nat.totient_prime_pow_succ (p := 5) (by norm_num) 0)
        have hb : Nat.totient 7 = 6 := (Nat.totient_prime_pow_succ (p := 7) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
    rw [hh] at hφ
    omega
  · decide
  · have hh : Nat.totient 37 = 36 :=
      (Nat.totient_prime_pow_succ (p := 37) (by norm_num) 0)
    rw [hh] at hφ
    omega
  · have hh : Nat.totient 38 = 18 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 2 19)
        have ha : Nat.totient 2 = 1 := (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 0)
        have hb : Nat.totient 19 = 18 := (Nat.totient_prime_pow_succ (p := 19) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
    rw [hh] at hφ
    omega
  · have hh : Nat.totient 39 = 24 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 3 13)
        have ha : Nat.totient 3 = 2 := (Nat.totient_prime_pow_succ (p := 3) (by norm_num) 0)
        have hb : Nat.totient 13 = 12 := (Nat.totient_prime_pow_succ (p := 13) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
    rw [hh] at hφ
    omega
  · have hh : Nat.totient 40 = 16 :=
      (by
        have h := Nat.totient_mul
          (by norm_num only [Nat.Coprime] : Nat.Coprime 8 5)
        have ha : Nat.totient 8 = 4 := (Nat.totient_prime_pow_succ (p := 2) (by norm_num) 2)
        have hb : Nat.totient 5 = 4 := (Nat.totient_prime_pow_succ (p := 5) (by norm_num) 0)
        rw [ha, hb] at h
        exact h)
    rw [hh] at hφ
    omega
  · have hh : Nat.totient 41 = 40 :=
      (Nat.totient_prime_pow_succ (p := 41) (by norm_num) 0)
    rw [hh] at hφ
    omega
  · decide

theorem lcm_six_le_eighty_four_of_totient (n : ℕ) (hn : 6 < n) (hφ : n.totient ≤ 12) :
    n.lcm 6 ≤ 84 := by
  have hm := mem_smallTotientOrders n hn hφ
  simp only [smallTotientOrders, Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

end Erdos633b
