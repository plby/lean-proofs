/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos822.LargePrimeResidueBlocks

/-!
# Elementary residue blocks for arbitrary moduli

For the repeated-prime-square correction we do not need a prime-counting
estimate.  A residue class modulo any positive integer has at most one
representative per modulus-length step, and this elementary fact gives a
summable reciprocal bound on the large-prime layer.
-/

namespace Erdos822

open scoped BigOperators

/-- Integers in an open-left, closed-right interval and one residue class. -/
def integerResidueInterval (d a L U : ℕ) : Finset ℕ :=
  (Finset.Ioc L U).filter fun q => q % d = a % d

@[simp]
theorem mem_integerResidueInterval_iff
    {d a L U q : ℕ} :
    q ∈ integerResidueInterval d a L U ↔
      L < q ∧ q ≤ U ∧ q % d = a % d := by
  simp [integerResidueInterval, and_assoc]

/-- One arbitrary residue class contributes at most one point per modulus
step inside an interval. -/
theorem card_integerResidueInterval_le
    {d a L U : ℕ} (hd : 0 < d) :
    (integerResidueInterval d a L U).card ≤ (U - L) / d + 1 := by
  classical
  by_cases hne : (integerResidueInterval d a L U).Nonempty
  · let Q := integerResidueInterval d a L U
    let q₀ := Q.min' hne
    let f : ℕ → ℕ := fun q => (q - q₀) / d
    have hq₀mem : q₀ ∈ Q := Finset.min'_mem Q hne
    have hq₀data := mem_integerResidueInterval_iff.mp hq₀mem
    have hrepr : ∀ q ∈ Q, d * f q + q₀ = q := by
      intro q hq
      have hqdata := mem_integerResidueInterval_iff.mp hq
      have hq₀q : q₀ ≤ q := Finset.min'_le Q q hq
      have hmod : q₀ ≡ q [MOD d] := by
        show q₀ % d = q % d
        exact hq₀data.2.2.trans hqdata.2.2.symm
      have hdvd : d ∣ q - q₀ := hmod.dvd'
      have hmul : d * ((q - q₀) / d) = q - q₀ :=
        Nat.mul_div_cancel' hdvd
      dsimp [f]
      rw [hmul]
      exact Nat.sub_add_cancel hq₀q
    have hcard :
        Q.card ≤ (Finset.range ((U - L) / d + 1)).card := by
      apply Finset.card_le_card_of_injOn f
      · intro q hq
        simp only [Finset.mem_coe, Finset.mem_range]
        have hqdata := mem_integerResidueInterval_iff.mp hq
        have hq₀q : q₀ ≤ q := Finset.min'_le Q q hq
        have hmul : d * f q ≤ U - L := by
          have hreprq := hrepr q hq
          have hq₀L : L < q₀ := hq₀data.1
          omega
        have hf : f q ≤ (U - L) / d :=
          (Nat.le_div_iff_mul_le hd).2 (by
            simpa [Nat.mul_comm] using hmul)
        omega
      · intro q hq q' hq' hf
        have hqrepr := hrepr q hq
        have hq'repr := hrepr q' hq'
        rw [hf] at hqrepr
        omega
    simpa [Q] using hcard
  · have hempty : integerResidueInterval d a L U = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hne
    rw [hempty]
    simp

/-- Reciprocal mass in an arbitrary residue interval is bounded by its
cardinality divided by the first possible integer. -/
theorem sum_inv_integerResidueInterval_le_card_div
    (d a L U : ℕ) :
    ∑ q ∈ integerResidueInterval d a L U, (1 : ℝ) / q ≤
      ((integerResidueInterval d a L U).card : ℝ) / (L + 1) := by
  calc
    (∑ q ∈ integerResidueInterval d a L U, (1 : ℝ) / q) ≤
        ∑ q ∈ integerResidueInterval d a L U,
          (1 : ℝ) / (L + 1) := by
      apply Finset.sum_le_sum
      intro q hq
      have hqdata := mem_integerResidueInterval_iff.mp hq
      have hLq : L + 1 ≤ q := by omega
      exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast hLq)
    _ = ((integerResidueInterval d a L U).card : ℝ) / (L + 1) := by
      rw [Finset.sum_const]
      simp
      ring

/-- A prime residue block is contained in the underlying integer residue
block with the same endpoints. -/
theorem largePrimeResidueBlock_subset_integerResidueInterval
    (N d a y j : ℕ) :
    largePrimeResidueBlock N d a y j ⊆
      integerResidueInterval d a (j * N ^ 21) ((j + 1) * N ^ 21) := by
  intro q hq
  rw [mem_largePrimeResidueBlock_iff] at hq
  rw [mem_integerResidueInterval_iff]
  exact ⟨hq.1, hq.2.1, hq.2.2.2.2⟩

/-- The large-prime reciprocal mass in one residue class is bounded by the
sum of elementary integer-residue blocks. -/
theorem sum_inv_largePrimeResidueClass_le_integer_blocks
    {N d a y : ℕ} (hN : 2 ≤ N) :
    ∑ q ∈ largePrimeResidueClass N d a y, (1 : ℝ) / q ≤
      ∑ j ∈ Finset.Icc 1 N,
        ∑ q ∈ integerResidueInterval d a
          (j * N ^ 21) ((j + 1) * N ^ 21), (1 : ℝ) / q := by
  calc
    (∑ q ∈ largePrimeResidueClass N d a y, (1 : ℝ) / q) ≤
        ∑ j ∈ Finset.Icc 1 N,
          ∑ q ∈ largePrimeResidueBlock N d a y j, (1 : ℝ) / q :=
      sum_inv_largePrimeResidueClass_le_sum_blocks hN
    _ ≤ ∑ j ∈ Finset.Icc 1 N,
          ∑ q ∈ integerResidueInterval d a
            (j * N ^ 21) ((j + 1) * N ^ 21), (1 : ℝ) / q := by
      apply Finset.sum_le_sum
      intro j hj
      apply Finset.sum_le_sum_of_subset_of_nonneg
        (largePrimeResidueBlock_subset_integerResidueInterval N d a y j)
      intro q hq hnot
      positivity

/-- A single integer residue block has the raw cardinality-over-endpoint
bound used before summing the harmonic kernel. -/
theorem sum_inv_integerResidueBlock_le
    {N d a j : ℕ} (hd : 0 < d) :
    ∑ q ∈ integerResidueInterval d a
        (j * N ^ 21) ((j + 1) * N ^ 21), (1 : ℝ) / q ≤
      (((N ^ 21 / d + 1 : ℕ) : ℝ) /
        (j * N ^ 21 + 1)) := by
  have hwidth :
      (j + 1) * N ^ 21 - j * N ^ 21 = N ^ 21 := by
    rw [show (j + 1) * N ^ 21 = j * N ^ 21 + N ^ 21 by ring]
    exact Nat.add_sub_cancel_left _ _
  calc
    (∑ q ∈ integerResidueInterval d a
        (j * N ^ 21) ((j + 1) * N ^ 21), (1 : ℝ) / q) ≤
        ((integerResidueInterval d a
          (j * N ^ 21) ((j + 1) * N ^ 21)).card : ℝ) /
          (j * N ^ 21 + 1) := by
      convert sum_inv_integerResidueInterval_le_card_div d a
        (j * N ^ 21) ((j + 1) * N ^ 21) using 1 <;>
        push_cast <;> rfl
    _ ≤ (((N ^ 21 / d + 1 : ℕ) : ℝ) /
        (j * N ^ 21 + 1)) := by
      apply div_le_div_of_nonneg_right
      · have hcard := card_integerResidueInterval_le
            (a := a) (L := j * N ^ 21)
            (U := (j + 1) * N ^ 21) hd
        rw [hwidth] at hcard
        exact_mod_cast hcard
      · positivity

/-- The raw integer-residue blocks sum to the expected
((1/d)+(1/N^21))-times-harmonic bound, with no primality assumption on d. -/
theorem sum_inv_largePrimeResidueClass_le_harmonic_of_pos
    {N d a y : ℕ} (hN : 2 ≤ N) (hd : 0 < d) :
    ∑ q ∈ largePrimeResidueClass N d a y, (1 : ℝ) / q ≤
      ((1 : ℝ) / d + (1 : ℝ) / (N ^ 21 : ℕ)) *
        (harmonic N : ℝ) := by
  have hL : 0 < N ^ 21 := by positivity
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hLR : (0 : ℝ) < (N ^ 21 : ℕ) := by exact_mod_cast hL
  calc
    (∑ q ∈ largePrimeResidueClass N d a y, (1 : ℝ) / q) ≤
        ∑ j ∈ Finset.Icc 1 N,
          ∑ q ∈ integerResidueInterval d a
            (j * N ^ 21) ((j + 1) * N ^ 21), (1 : ℝ) / q :=
      sum_inv_largePrimeResidueClass_le_integer_blocks hN
    _ ≤ ∑ j ∈ Finset.Icc 1 N,
          (((N ^ 21 / d + 1 : ℕ) : ℝ) /
            (j * N ^ 21 + 1)) := by
      apply Finset.sum_le_sum
      intro j hj
      exact sum_inv_integerResidueBlock_le hd
    _ ≤ ∑ j ∈ Finset.Icc 1 N,
          (((1 : ℝ) / d + (1 : ℝ) / (N ^ 21 : ℕ)) *
            ((1 : ℝ) / j)) := by
      apply Finset.sum_le_sum
      intro j hj
      have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
      have hjR : (0 : ℝ) < j := by exact_mod_cast (by omega : 0 < j)
      have hcast :
          ((N ^ 21 / d + 1 : ℕ) : ℝ) ≤
            ((N ^ 21 : ℕ) : ℝ) / d + 1 := by
        have hdiv :
            ((N ^ 21 / d : ℕ) : ℝ) ≤
              ((N ^ 21 : ℕ) : ℝ) / d :=
          Nat.cast_div_le (α := ℝ) (m := N ^ 21) (n := d)
        push_cast at hdiv ⊢
        linarith
      have hden :
          (j : ℝ) * (N ^ 21 : ℕ) ≤
            ((j * N ^ 21 + 1 : ℕ) : ℝ) := by
        push_cast
        nlinarith
      have hnum0 :
          0 ≤ ((N ^ 21 : ℕ) : ℝ) / d + 1 := by positivity
      calc
        (((N ^ 21 / d + 1 : ℕ) : ℝ) /
            (j * N ^ 21 + 1)) ≤
            (((N ^ 21 : ℕ) : ℝ) / d + 1) /
              (j * N ^ 21 + 1) := by
          exact div_le_div_of_nonneg_right hcast (by positivity)
        _ ≤ (((N ^ 21 : ℕ) : ℝ) / d + 1) /
              ((j : ℝ) * (N ^ 21 : ℕ)) := by
          exact div_le_div_of_nonneg_left hnum0
            (mul_pos hjR hLR) (by
              simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_one,
                Nat.cast_pow] using hden)
        _ = ((1 : ℝ) / d + (1 : ℝ) / (N ^ 21 : ℕ)) *
              ((1 : ℝ) / j) := by
          field_simp
    _ = ((1 : ℝ) / d + (1 : ℝ) / (N ^ 21 : ℕ)) *
        (harmonic N : ℝ) := by
      rw [← Finset.mul_sum]
      simp [harmonic_eq_sum_Icc, one_div]

end Erdos822
