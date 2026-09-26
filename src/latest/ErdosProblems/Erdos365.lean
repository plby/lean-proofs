/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 365.

  "If two consecutive positive integers are powerful, must at least one be a
   perfect square?"

The answer is NO.  Solomon W. Golomb (1970) exhibited the counterexample
12167 = 23^3 and 12168 = 2^3 * 3^2 * 13^2: they are consecutive, both are
powerful, and neither is a perfect square (110^2 = 12100 < 12167 < 12168
< 12321 = 111^2).

This file proves the full statement, i.e. the exact negation of the question,
with an explicit witness.  It is self-contained: it uses only Lean core
(Init/Std), no mathlib, no `sorry`, no `admit` and no custom axioms.  Every
finite check is discharged by kernel reduction (`by decide`).

Informal authors:
- Solomon W. Golomb (counterexample, Amer. Math. Monthly 77 (1970), 848-852)

Formal authors:
- 1athena (Lean 4 formalization; developed with AI assistance, disclosed)

URLs:
- https://www.erdosproblems.com/latex/365
- https://doi.org/10.2307/2317020
-/

-- The bounded primality / divisibility sweeps below recurse about 1.2e4 deep,
-- which exceeds the default `maxRecDepth`; 1e5 was measured to be sufficient
-- (4e4 fails, 6e4 succeeds).  No heartbeat override is needed.
set_option maxRecDepth 100000

namespace Erdos365

------------------------------------------------------------------------------
-- Bounded universal quantification as a Bool computation
------------------------------------------------------------------------------

/-- `allUpToB f n == true` iff `f k == true` for every `k` with `0 ≤ k ≤ n`. -/
def allUpToB (f : Nat → Bool) : Nat → Bool
  | 0     => f 0
  | n + 1 => allUpToB f n && f (n + 1)

/-- helpers for Bool conjunction (Lean 4.33 core has no `Bool.and_eq_true.mp`) -/
theorem boolAndSplit {a b : Bool} (h : (a && b) = true) : a = true ∧ b = true := by
  cases a <;> cases b <;> simp_all

theorem boolAndIntro {a b : Bool} (ha : a = true) (hb : b = true) : (a && b) = true := by
  cases a <;> cases b <;> simp_all

theorem allUpToB_spec (f : Nat → Bool) :
    ∀ n, allUpToB f n = true → ∀ k, k ≤ n → f k = true
  | 0, h, k, hk => by
      have : k = 0 := Nat.eq_zero_of_le_zero hk
      subst k
      simpa [allUpToB] using h
  | n + 1, h, k, hk => by
      have h' : (allUpToB f n && f (n + 1)) = true := by simpa [allUpToB] using h
      have hp' := boolAndSplit h'
      have hn : allUpToB f n = true := hp'.1
      have h1 : f (n + 1) = true := hp'.2
      by_cases hkn : k ≤ n
      · exact allUpToB_spec f n hn k hkn
      · have hgt : n + 1 ≤ k := Nat.succ_le_of_lt (Nat.lt_of_not_ge hkn)
        have : k = n + 1 := Nat.le_antisymm hk hgt
        subst k
        exact h1

theorem allUpToB_of_all (f : Nat → Bool) :
    ∀ n, (∀ k, k ≤ n → f k = true) → allUpToB f n = true
  | 0, h => by simpa [allUpToB] using h 0 (Nat.le_refl 0)
  | n + 1, h => by
      have hn : allUpToB f n = true :=
        allUpToB_of_all f n (fun k hk => h k (Nat.le_trans hk (Nat.le_succ n)))
      have h1 : f (n + 1) = true := h (n + 1) (Nat.le_refl (n + 1))
      simp [allUpToB, hn, h1]

------------------------------------------------------------------------------
-- Primality, and the proof that the computable predicate is the textbook one
------------------------------------------------------------------------------

/-- true iff `d` is NOT a divisor of `p` strictly between 1 and `p`. -/
def noSmallFactorB (p d : Nat) : Bool :=
  !(decide (2 ≤ d) && decide (d < p) && decide (d ∣ p))

def isPrimeB (p : Nat) : Bool :=
  decide (2 ≤ p) && allUpToB (noSmallFactorB p) p

/-- `p` is prime (computable definition). -/
def IsPrime (p : Nat) : Prop := isPrimeB p = true

instance (p : Nat) : Decidable (IsPrime p) := by
  unfold IsPrime
  infer_instance

theorem isPrime_standard (p : Nat) :
    IsPrime p ↔ (2 ≤ p ∧ ∀ d : Nat, 2 ≤ d → d < p → ¬ d ∣ p) := by
  constructor
  · intro h
    constructor
    · exact of_decide_eq_true (boolAndSplit h).1
    · intro d hd2 hdp hdv
      have hAll : allUpToB (noSmallFactorB p) p = true := (boolAndSplit h).2
      have hf : noSmallFactorB p d = true :=
        allUpToB_spec (noSmallFactorB p) p hAll d (Nat.le_of_lt hdp)
      have hX : (decide (2 ≤ d) && decide (d < p) && decide (d ∣ p)) = true := by
        simp [hd2, hdp, hdv]
      simp [noSmallFactorB, hX] at hf
  · intro h
    rcases h with ⟨h2, hn⟩
    apply boolAndIntro
    · simp [h2]
    · apply allUpToB_of_all
      intro d hdle
      by_cases h1 : 2 ≤ d
      · by_cases h2 : d < p
        · by_cases h3 : d ∣ p
          · exfalso
            exact (hn d h1 h2) h3
          · simp [noSmallFactorB, h1, h2, h3]
        · simp [noSmallFactorB, h1, h2]
      · simp [noSmallFactorB, h1]

------------------------------------------------------------------------------
-- Powerful numbers and perfect squares
------------------------------------------------------------------------------

/-- Standard: `n` is powerful iff every prime divisor `p` of `n` has `p^2 | n`. -/
def Powerful (n : Nat) : Prop :=
  ∀ p : Nat, IsPrime p → p ∣ n → p * p ∣ n

/-- `n` is a perfect square. -/
def IsSquare (n : Nat) : Prop := ∃ k : Nat, k * k = n

------------------------------------------------------------------------------
-- 12167 = 23^3  is powerful
------------------------------------------------------------------------------

theorem powerful_12167 : Powerful 12167 := by
  intro p hp hpn
  have hp_le : p ≤ 12167 := Nat.le_of_dvd (by decide) hpn
  -- `p ∣ 12167` is tested first, so primality is only evaluated for the four
  -- genuine divisors of 23^3
  have hfin : allUpToB
      (fun q => !decide (q ∣ 12167) || !isPrimeB q || decide (q * q ∣ 12167))
      12167 = true := by
    decide
  have hpb : isPrimeB p = true := hp
  have hq := allUpToB_spec _ 12167 hfin p hp_le
  simp [hpn, hpb] at hq
  simpa using hq

------------------------------------------------------------------------------
-- 12168 = 2^3 * 3^2 * 13^2  is powerful
------------------------------------------------------------------------------

theorem powerful_12168 : Powerful 12168 := by
  intro p hp hpn
  have hp_le : p ≤ 12168 := Nat.le_of_dvd (by decide) hpn
  have hfin : allUpToB
      (fun q => !decide (q ∣ 12168) || !isPrimeB q || decide (q * q ∣ 12168))
      12168 = true := by
    decide
  have hpb : isPrimeB p = true := hp
  have hq := allUpToB_spec _ 12168 hfin p hp_le
  simp [hpn, hpb] at hq
  simpa using hq

------------------------------------------------------------------------------
-- neither 12167 nor 12168 is a perfect square
------------------------------------------------------------------------------

theorem not_square_12167 : ¬ IsSquare 12167 := by
  rintro ⟨k, hk⟩
  have hk0 : k ≠ 0 := by
    intro h0
    subst k
    change (0 : Nat) = 12167 at hk
    cases hk
  -- k <= k*k = 12167, so k lies inside the swept range
  have hk_le : k ≤ 12167 := by
    have h1 : k ≤ k * k := Nat.le_mul_of_pos_right k (Nat.pos_of_ne_zero hk0)
    simpa [hk] using h1
  have hfin : allUpToB (fun q => decide (q * q ≠ 12167)) 12167 = true := by
    decide
  have hq := allUpToB_spec _ 12167 hfin k hk_le
  exact (of_decide_eq_true hq) hk

theorem not_square_12168 : ¬ IsSquare 12168 := by
  rintro ⟨k, hk⟩
  have hk0 : k ≠ 0 := by
    intro h0
    subst k
    change (0 : Nat) = 12168 at hk
    cases hk
  have hk_le : k ≤ 12168 := by
    have h1 : k ≤ k * k := Nat.le_mul_of_pos_right k (Nat.pos_of_ne_zero hk0)
    simpa [hk] using h1
  have hfin : allUpToB (fun q => decide (q * q ≠ 12168)) 12168 = true := by
    decide
  have hq := allUpToB_spec _ 12168 hfin k hk_le
  exact (of_decide_eq_true hq) hk

------------------------------------------------------------------------------
-- the complete answer to the original yes/no question
------------------------------------------------------------------------------

/-- There exist two consecutive positive integers that are both powerful and
    of which NEITHER is a perfect square.  Witness: n = 12167. -/
theorem consecutive_powerful_neither_square :
    ∃ n : Nat, 0 < n ∧ Powerful n ∧ Powerful (n + 1) ∧ ¬ IsSquare n ∧ ¬ IsSquare (n + 1) := by
  refine ⟨12167, by decide, powerful_12167, ?_, not_square_12167, ?_⟩
  · simpa using powerful_12168
  · simpa using not_square_12168

/-- The original claim, stated verbatim, is false.  This is the exact negation
    of the catalogued question, so the result is a complete solution. -/
theorem original_claim_is_false :
    ¬ (∀ n : Nat, 0 < n → Powerful n → Powerful (n + 1) → IsSquare n ∨ IsSquare (n + 1)) := by
  intro h
  rcases h 12167 (by decide) powerful_12167 (by simpa using powerful_12168) with hs | hs
  · exact not_square_12167 hs
  · exact not_square_12168 hs

------------------------------------------------------------------------------
-- sanity checks
------------------------------------------------------------------------------

example : IsPrime 2 := by decide
example : IsPrime 3 := by decide
example : IsPrime 23 := by decide
example : ¬ IsPrime 4 := by decide
example : ¬ IsPrime 1 := by decide
example : ¬ IsPrime 0 := by decide
example : Powerful 1 := by
  intro p hp hpn
  have hstd := (isPrime_standard p).mp hp
  have h2 : 2 ≤ p := hstd.1
  have hp_le : p ≤ 1 := Nat.le_of_dvd (by decide) hpn
  have h21 : (2 : Nat) ≤ 1 := Nat.le_trans h2 hp_le
  have hlt : (1 : Nat) < 1 := Nat.lt_of_lt_of_le (by decide) h21
  exact False.elim ((Nat.lt_irrefl 1) hlt)

------------------------------------------------------------------------------
-- axiom audit: must NOT list sorryAx or any custom axiom
------------------------------------------------------------------------------

#print axioms consecutive_powerful_neither_square
#print axioms original_claim_is_false

/-- Main result (Erdős Problem 365): the answer to the question is **no**. -/
theorem not_erdos_365 :
    ¬ (∀ n : Nat, 0 < n → Powerful n → Powerful (n + 1) → IsSquare n ∨ IsSquare (n + 1)) :=
  original_claim_is_false

/-- Alias kept so the result is also reachable under the generic `erdos_NNN` name. -/
theorem erdos_365 :
    ¬ (∀ n : Nat, 0 < n → Powerful n → Powerful (n + 1) → IsSquare n ∨ IsSquare (n + 1)) :=
  not_erdos_365

#print axioms not_erdos_365
#print axioms erdos_365

end Erdos365
