/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos781

def IsDescendingWave {k n : ℕ} (x : Fin k → Fin n) : Prop :=
  StrictMono x ∧
    ∀ i : ℕ, ∀ hi : i + 2 < k,
      (x ⟨i, by omega⟩).val + (x ⟨i + 2, hi⟩).val ≤
        2 * (x ⟨i + 1, by omega⟩).val

def Monochromatic {k n : ℕ} (c : Fin n → Bool) (x : Fin k → Fin n) : Prop :=
  ∃ colour, ∀ i, c (x i) = colour

def ForcesDescending (k n : ℕ) : Prop :=
  ∀ c : Fin n → Bool, ∃ x : Fin k → Fin n,
    IsDescendingWave x ∧ Monochromatic c x

noncomputable def waveRamsey (k : ℕ) : ℕ :=
  sInf {n : ℕ | ForcesDescending k n}

theorem erdos_781 :
    (∀ k : ℕ, 2 ^ 50 ≤ k →
      k ^ 3 ≤ 2 ^ 48 * waveRamsey k ∧
        waveRamsey k ≤ 8 * k ^ 3 + 1) ∧
    ¬ (∀ k : ℕ, waveRamsey k = k ^ 2 - k + 1) := by
  sorry

end Erdos781
