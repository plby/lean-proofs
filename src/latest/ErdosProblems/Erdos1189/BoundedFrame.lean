/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Cardinality and modulus bounds for the selected truncated-center frame.
Informal source: Section 6 of Pickhardt and Omniscience Research Agent.
Formal author: OpenAI Codex.
-/

import ErdosProblems.Erdos1189.SeedAssembly

namespace Erdos1189

open Finset

def SeedFamily.moduli {N P B C : ℕ} (F : SeedFamily N P B C) : Finset ℕ :=
  insert P (frameModuli (seedModulus F.seed))

def frameBound (C P B : ℕ) : ℕ := (C + 16) * P ^ 2 + (C + 1) * P * B ^ 2

lemma first_block_le_frameBound (C P B : ℕ) : C * P ^ 2 ≤ frameBound C P B := by
  exact (Nat.mul_le_mul_right (P ^ 2) (Nat.le_add_right C 16)).trans (Nat.le_add_right _ _)

lemma second_block_le_frameBound (C P B : ℕ) : C * P * B ^ 2 ≤ frameBound C P B := by
  exact (Nat.mul_le_mul_right (B ^ 2) (Nat.mul_le_mul_right P (Nat.le_succ C))).trans
    (Nat.le_add_left _ _)

lemma terminal_block_le_frameBound (C P B : ℕ) :
    P * max (16 * P) (B ^ 2) ≤ frameBound C P B := by
  calc
    _ ≤ P * (16 * P + B ^ 2) := Nat.mul_le_mul_left P
      (max_le (Nat.le_add_right _ _) (Nat.le_add_left _ _))
    _ = 16 * P ^ 2 + P * B ^ 2 := by ring
    _ ≤ frameBound C P B := by
      unfold frameBound
      exact add_le_add (Nat.mul_le_mul_right (P ^ 2) (by omega))
        (Nat.mul_le_mul_right (B ^ 2) (Nat.le_mul_of_pos_left P (Nat.succ_pos C)))

lemma SeedFamily.modulus_le {P B C : ℕ} {D : Finset ℕ} (hP : P.Prime)
    (hB : B < P) (hD : D ⊆ Nat.primesLE B)
    (F : SeedFamily (frameInteger P D) P B C) (s : PrimeSlot (frameInteger P D)) :
    seedModulus F.seed s ≤ frameBound C P B := by
  have hDP : D ⊆ Nat.primesLE P := fun q hq => Nat.mem_primesLE.mpr
    ⟨(Nat.le_of_mem_primesLE (hD hq)).trans hB.le, Nat.prime_of_mem_primesLE (hD hq)⟩
  have hq : s.1.1.val ∈ Nat.primesLE P := Eq.mp
    (congrArg (fun S : Finset ℕ => s.1.1.val ∈ S) (frameInteger_primeFactors hDP)) s.1.1.2
  have hqle := Nat.le_of_mem_primesLE hq
  have he := s.1.2.isLt
  by_cases hqP : s.1.1.val = P
  · have hfac := congrArg (frameInteger P D).factorization hqP
    have hPexp := frameInteger_terminal_exponent hP hB hD
    have he0 : s.1.2.val = 0 := by omega
    have hm : seedModulus F.seed s = P * F.seed s := by
      simp only [seedModulus, he0, zero_add, pow_one, hqP]
    rw [hm]
    exact (Nat.mul_le_mul_left P (F.terminal_bound s hqP)).trans
      (terminal_block_le_frameBound C P B)
  · have hs := F.ordinary_bound s hqP
    have he2 := frameInteger_exponent_le_two hDP s.1.1.val
    have hecases : s.1.2.val = 0 ∨ s.1.2.val = 1 := by omega
    rcases hecases with he0 | he1
    · calc
        seedModulus F.seed s = s.1.1.val * F.seed s := by simp [seedModulus, he0]
        _ ≤ s.1.1.val * (C * s.1.1.val) := Nat.mul_le_mul_left _ hs
        _ = C * s.1.1.val ^ 2 := by ring
        _ ≤ C * P ^ 2 := Nat.mul_le_mul_left C (Nat.pow_le_pow_left hqle 2)
        _ ≤ frameBound C P B := first_block_le_frameBound C P B
    · have hqD : s.1.1.val ∈ D := by
        have hfac := frameInteger_factorization hDP s.1.1.val
        rw [if_pos hq] at hfac
        by_contra hn
        rw [if_neg hn] at hfac
        omega
      have hqB := Nat.le_of_mem_primesLE (hD hqD)
      calc
        seedModulus F.seed s = s.1.1.val ^ 2 * F.seed s := by simp [seedModulus, he1]
        _ ≤ s.1.1.val ^ 2 * (C * s.1.1.val) := Nat.mul_le_mul_left _ hs
        _ = C * s.1.1.val * s.1.1.val ^ 2 := by ring
        _ ≤ C * P * B ^ 2 := Nat.mul_le_mul (Nat.mul_le_mul_left C hqle)
          (Nat.pow_le_pow_left hqB 2)
        _ ≤ frameBound C P B := second_block_le_frameBound C P B

lemma SeedFamily.irreducible_frameInteger {P B C : ℕ} {D : Finset ℕ} (hP : P.Prime)
    (hB : B < P) (hD : D ⊆ Nat.primesLE B) (F : SeedFamily (frameInteger P D) P B C) :
    IsIrreducibleCoveringSet F.moduli ∧ F.moduli.card = simpsonWeight (frameInteger P D) + 1 := by
  have hDP : D ⊆ Nat.primesLE P := fun q hq => Nat.mem_primesLE.mpr
    ⟨(Nat.le_of_mem_primesLE (hD hq)).trans hB.le, Nat.prime_of_mem_primesLE (hD hq)⟩
  have hN := frameInteger_ne_zero hDP
  have hPexp := frameInteger_terminal_exponent hP hB hD
  have hPN : P ∣ frameInteger P D := by
    apply (hP.dvd_iff_one_le_factorization hN).mpr
    rw [hPexp]
  exact seed_frame hN hP hPN hPexp (frameInteger_exponent_le_two hDP) F.seed F.divisor
    F.supported F.injective F.terminal_nonunit F.terminal_power

lemma SeedFamily.all_moduli_le {P B C : ℕ} {D : Finset ℕ} (hP : P.Prime)
    (hB : B < P) (hD : D ⊆ Nat.primesLE B) (F : SeedFamily (frameInteger P D) P B C) :
    ∀ d ∈ F.moduli, d ≤ frameBound C P B := by
  intro d hd
  rcases mem_insert.mp hd with hdP | hd
  · subst d
    have hp := hP.two_le
    have hh : 16 * P ^ 2 ≤ frameBound C P B :=
      (Nat.mul_le_mul_right (P ^ 2) (Nat.le_add_left 16 C)).trans (Nat.le_add_right _ _)
    exact (show P ≤ 16 * P ^ 2 by nlinarith).trans hh
  · obtain ⟨s, rfl⟩ := mem_frameModuli.mp hd
    exact F.modulus_le hP hB hD s

lemma SeedFamily.contains_squarefree_products {N P B C : ℕ} (F : SeedFamily N P B C)
    {q d : ℕ} (hq : q.Prime) (hqP : q < P) (hd : d ∈ squarefreeUpto (q - 1)) :
    q * d ∈ F.moduli := by
  obtain ⟨s, hs, he, hd⟩ := F.small_squarefree q hq hqP d hd
  apply mem_insert_of_mem
  apply mem_frameModuli.mpr
  exact ⟨s, by simp only [seedModulus, he, zero_add, pow_one, hd, hs]⟩

end Erdos1189
