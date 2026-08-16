import Wikipedia.GreenTao.Primes.ReducedResidues
import Wikipedia.GreenTao.Sieve.TruncatedDivisorSum
import Mathlib.Data.ZMod.Basic

/-!
# W-tricked prime weight and Selberg majorant

This file defines the two functions compared in the final transference
argument.  Both are localized to a short interval of standard
representatives.  Outside that interval the prime weight is zero and the
majorant is one; inside it, the majorant is the normalized Selberg square at
`W * n + b`.
-/

namespace Wikipedia.SzemeredisTheorem

/-- The fixed short interval used to prevent wraparound when a cyclic
progression is lifted back to the natural numbers. -/
def greenTaoInterval (N : ℕ) : Finset ℕ :=
  Finset.Icc (N / 64) (N / 4)

@[simp]
theorem mem_greenTaoInterval {N n : ℕ} :
    n ∈ greenTaoInterval N ↔ N / 64 ≤ n ∧ n ≤ N / 4 := by
  simp [greenTaoInterval]

/-- The chosen interval has less than half the width of a full residue
system, which is the hypothesis required by short-interval unwrapping. -/
theorem greenTaoInterval_twice_width_lt {N : ℕ} (hN : 0 < N) :
    2 * (((N / 4 : ℕ) : ℤ) - ((N / 64 : ℕ) : ℤ)) < (N : ℤ) := by
  have hquarter : 2 * (N / 4) < N := by
    omega
  have hquarter_int :
      2 * ((N / 4 : ℕ) : ℤ) < (N : ℤ) := by
    exact_mod_cast hquarter
  have hlower : 0 ≤ ((N / 64 : ℕ) : ℤ) := by
    positivity
  linarith

/-- The affine natural number represented by a W-tricked residue. -/
def wTrickedValue {N : ℕ} [NeZero N]
    (W b : ℕ) (n : ZMod N) : ℕ :=
  W * n.val + b

/-- Localized, logarithmically weighted indicator of W-tricked primes. -/
noncomputable def wTrickedPrimeWeight {N : ℕ} [NeZero N]
    (α : ℝ) (W b : ℕ) (n : ZMod N) : ℝ :=
  if n.val ∈ greenTaoInterval N ∧ Nat.Prime (wTrickedValue W b n) then
    α * ((W.totient : ℝ) / W) * Real.log (wTrickedValue W b n)
  else
    0

/-- Localized Selberg majorant. -/
noncomputable def wTrickedMajorant {N : ℕ} [NeZero N]
    (χ : ℝ → ℝ) (cχ : ℝ) (R W b : ℕ) (n : ZMod N) : ℝ :=
  if n.val ∈ greenTaoInterval N then
    normalizedSelbergMajorant χ cχ R W (wTrickedValue W b n)
  else
    1

theorem wTrickedPrimeWeight_nonneg {N : ℕ} [NeZero N]
    {α : ℝ} (hα : 0 ≤ α) (W b : ℕ) (n : ZMod N) :
    0 ≤ wTrickedPrimeWeight α W b n := by
  unfold wTrickedPrimeWeight
  split_ifs with h
  · exact mul_nonneg
      (mul_nonneg hα
        (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)))
      (Real.log_nonneg (by
        exact_mod_cast (Nat.one_le_iff_ne_zero.mpr h.2.ne_zero)))
  · exact le_rfl

theorem wTrickedPrimeWeight_pos_iff {N : ℕ} [NeZero N]
    {α : ℝ} (hα : 0 < α) {W : ℕ} (hW : 0 < W)
    (b : ℕ) (n : ZMod N) :
    0 < wTrickedPrimeWeight α W b n ↔
      n.val ∈ greenTaoInterval N ∧
        Nat.Prime (wTrickedValue W b n) := by
  by_cases h :
      n.val ∈ greenTaoInterval N ∧
        Nat.Prime (wTrickedValue W b n)
  · rw [wTrickedPrimeWeight, if_pos h]
    constructor
    · intro
      exact h
    · intro
      have htotient : 0 < (W.totient : ℝ) := by
        exact_mod_cast Nat.totient_pos.mpr hW
      have hWreal : 0 < (W : ℝ) := by
        exact_mod_cast hW
      have hpReal : 1 < (wTrickedValue W b n : ℝ) := by
        exact_mod_cast h.2.one_lt
      exact mul_pos (mul_pos hα (div_pos htotient hWreal))
        (Real.log_pos hpReal)
  · rw [wTrickedPrimeWeight, if_neg h]
    simpa using h

theorem wTrickedMajorant_nonneg {N : ℕ} [NeZero N]
    (χ : ℝ → ℝ) {cχ : ℝ} (hcχ : 0 ≤ cχ)
    {R : ℕ} (hR : 1 ≤ R) (W b : ℕ) (n : ZMod N) :
    0 ≤ wTrickedMajorant χ cχ R W b n := by
  unfold wTrickedMajorant
  split
  · exact normalizedSelbergMajorant_nonneg χ hcχ hR W _
  · exact zero_le_one

@[simp]
theorem wTrickedPrimeWeight_eq {N : ℕ} [NeZero N]
    (α : ℝ) (W b : ℕ) (n : ZMod N)
    (hn : n.val ∈ greenTaoInterval N)
    (hp : Nat.Prime (wTrickedValue W b n)) :
    wTrickedPrimeWeight α W b n =
      α * ((W.totient : ℝ) / W) *
        Real.log (wTrickedValue W b n) := by
  simp [wTrickedPrimeWeight, hn, hp]

@[simp]
theorem wTrickedMajorant_eq {N : ℕ} [NeZero N]
    (χ : ℝ → ℝ) (cχ : ℝ) (R W b : ℕ) (n : ZMod N)
    (hn : n.val ∈ greenTaoInterval N) :
    wTrickedMajorant χ cχ R W b n =
      normalizedSelbergMajorant χ cχ R W
        (wTrickedValue W b n) := by
  simp [wTrickedMajorant, hn]

/-- Pointwise domination reduced to its only substantive case: a prime
inside the short interval. -/
theorem wTrickedPrimeWeight_le_majorant_of_prime_bound
    {N : ℕ} [NeZero N]
    (α : ℝ) (W b : ℕ)
    (χ : ℝ → ℝ) {cχ : ℝ} (hcχ : 0 ≤ cχ)
    {R : ℕ} (hR : 1 ≤ R)
    (hprime :
      ∀ n : ZMod N,
        n.val ∈ greenTaoInterval N →
        Nat.Prime (wTrickedValue W b n) →
        α * ((W.totient : ℝ) / W) *
            Real.log (wTrickedValue W b n) ≤
          normalizedSelbergMajorant χ cχ R W
            (wTrickedValue W b n)) :
    ∀ n : ZMod N,
      wTrickedPrimeWeight α W b n ≤
        wTrickedMajorant χ cχ R W b n := by
  intro n
  by_cases hn : n.val ∈ greenTaoInterval N
  · by_cases hp : Nat.Prime (wTrickedValue W b n)
    · simpa [wTrickedPrimeWeight, wTrickedMajorant, hn, hp] using
        hprime n hn hp
    · simp [wTrickedPrimeWeight, wTrickedMajorant, hn, hp,
        normalizedSelbergMajorant_nonneg χ hcχ hR W
          (wTrickedValue W b n)]
  · simp [wTrickedPrimeWeight, wTrickedMajorant, hn]

/-- The exact prime-value identity for the Selberg square turns a scalar
logarithmic comparison into pointwise domination. -/
theorem wTrickedPrimeWeight_le_majorant
    {N : ℕ} [NeZero N]
    {α cχ : ℝ} (hcχ : 0 < cχ)
    {R W b : ℕ} (hR : 1 < R) (hW : 0 < W)
    (χ : ℝ → ℝ) (hχ0 : χ 0 = 1)
    (hχ : ∀ x : ℝ, 1 ≤ x → χ x = 0)
    (hscale :
      ∀ n : ZMod N,
        n.val ∈ greenTaoInterval N →
        Nat.Prime (wTrickedValue W b n) →
        R < wTrickedValue W b n ∧
          α * Real.log (wTrickedValue W b n) ≤
            Real.log R / cχ) :
    ∀ n : ZMod N,
      wTrickedPrimeWeight α W b n ≤
        wTrickedMajorant χ cχ R W b n := by
  apply wTrickedPrimeWeight_le_majorant_of_prime_bound
    α W b χ hcχ.le hR.le
  intro n hn hp
  rw [normalizedSelbergMajorant_prime_of_lt χ hcχ.ne'
    hR hW hp hχ0 hχ (hscale n hn hp).1]
  calc
    α * ((W.totient : ℝ) / W) *
          Real.log (wTrickedValue W b n) =
        ((W.totient : ℝ) / W) *
          (α * Real.log (wTrickedValue W b n)) := by ring
    _ ≤ ((W.totient : ℝ) / W) * (Real.log R / cχ) :=
      mul_le_mul_of_nonneg_left (hscale n hn hp).2
        (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))

end Wikipedia.SzemeredisTheorem
