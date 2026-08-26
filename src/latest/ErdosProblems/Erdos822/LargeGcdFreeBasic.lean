/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos822.OddCofactorLayers

/-!
# The elementary growing-cutoff B4 filter

This file contains only the filter and its immediate arithmetic consequence.
The heavier collision and squarefree interfaces live in `LargeGcdFreeFilter`.
-/

namespace Erdos822

/-- Odd raw cofactors for which no prime strictly above `y` divides both
the cofactor and its totient. -/
noncomputable def largeGcdFreeOddCofactors
    (N y : ℕ) : Finset ℕ := by
  classical
  exact (oddRawCofactors N).filter fun m =>
    ∀ p : ℕ, p.Prime → y < p →
      ¬ (p ∣ m ∧ p ∣ Nat.totient m)

@[simp]
theorem mem_largeGcdFreeOddCofactors_iff
    {N y m : ℕ} :
    m ∈ largeGcdFreeOddCofactors N y ↔
      m ∈ oddRawCofactors N ∧
        ∀ p : ℕ, p.Prime → y < p →
          ¬ (p ∣ m ∧ p ∣ Nat.totient m) := by
  simp [largeGcdFreeOddCofactors]

theorem largeGcdFreeOddCofactors_subset_oddRaw
    (N y : ℕ) :
    largeGcdFreeOddCofactors N y ⊆ oddRawCofactors N := by
  intro m hm
  exact (mem_largeGcdFreeOddCofactors_iff.mp hm).1

theorem largeGcdFreeOddCofactors_pos {N y m : ℕ}
    (hm : m ∈ largeGcdFreeOddCofactors N y) : 0 < m :=
  oddRawCofactors_pos (largeGcdFreeOddCofactors_subset_oddRaw N y hm)

/-- If a large prime divides the shifted coefficient of a B4 cofactor, it
cannot divide the cofactor itself. -/
theorem not_dvd_of_dvd_shiftedTotient_of_largeGcdFree
    {N y p m : ℕ}
    (hm : m ∈ largeGcdFreeOddCofactors N y)
    (hp : p.Prime) (hyp : y < p)
    (hshift : p ∣ shiftedTotient m) :
    ¬ p ∣ m := by
  intro hpm
  have hphi : p ∣ Nat.totient m := by
    apply (Nat.dvd_add_iff_right hpm).mpr
    simpa [shiftedTotient] using hshift
  exact (mem_largeGcdFreeOddCofactors_iff.mp hm).2
    p hp hyp ⟨hpm, hphi⟩

end Erdos822
