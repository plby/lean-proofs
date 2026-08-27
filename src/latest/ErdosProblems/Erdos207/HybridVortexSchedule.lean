/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.PaddedAbsorberSeparatedVortex

/-!
# A two-step hybrid vortex schedule

The first positive level retains a fixed fraction of the ambient vertices;
the terminal level is the flexible absorber root.  This makes the long
initial sparsification a constant-density phase while preserving the small
terminal set used by absorption.
-/

namespace Erdos207

open Finset
open scoped Classical

/-- Free vertices at the three levels: all ambient capacity at level zero,
one half at the first positive level, and none at the terminal level. -/
def hybridFreeSize (n : ℕ) (i : Fin 3) : ℕ :=
  if i = 0 then n else if i = 1 then n / 2 else 0

lemma hybridFreeSize_zero (n : ℕ) : hybridFreeSize n 0 = n := by
  simp [hybridFreeSize]

lemma hybridFreeSize_one (n : ℕ) : hybridFreeSize n 1 = n / 2 := by
  simp [hybridFreeSize]

lemma hybridFreeSize_last (n : ℕ) :
    hybridFreeSize n (Fin.last 2) = 0 := by
  simp [hybridFreeSize]

lemma hybridFreeSize_antitone (n : ℕ) : Antitone (hybridFreeSize n) := by
  intro i j hij
  by_cases hi0 : i = 0
  · subst i
    simp only [hybridFreeSize_zero]
    unfold hybridFreeSize
    split_ifs
    · exact le_rfl
    · exact Nat.div_le_self _ _
    · exact Nat.zero_le _
  by_cases hj1 : j = 1
  · have hi1 : i = 1 := by
      apply Fin.ext
      have hiPos : 0 < i.val := Nat.pos_of_ne_zero (by
        intro h
        apply hi0
        apply Fin.ext
        simpa using h)
      have hjval : j.val = 1 := congrArg Fin.val hj1
      omega
    subst i
    subst j
    exact le_rfl
  have hj0 : j ≠ 0 := by
    intro hj
    subst j
    have hiv : i.val = 0 := by
      have hle : i.val ≤ (0 : Fin 3).val := hij
      simp only [Fin.val_zero] at hle
      omega
    apply hi0
    apply Fin.ext
    simpa using hiv
  simp [hybridFreeSize, hj0, hj1]

end Erdos207
