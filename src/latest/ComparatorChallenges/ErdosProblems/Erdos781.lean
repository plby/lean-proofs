/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open scoped BigOperators

noncomputable section

namespace Erdos781

open scoped Classical in
def IsDescendingWave {k n : ℕ} (x : Fin k → Fin n) : Prop :=
  StrictMono x ∧
    ∀ i : ℕ, ∀ hi : i + 2 < k,
      (x ⟨i, by omega⟩).val + (x ⟨i + 2, hi⟩).val ≤
        2 * (x ⟨i + 1, by omega⟩).val

end Erdos781

namespace Erdos781

open scoped Classical in
def Monochromatic {k n : ℕ} (c : Fin n → Bool) (x : Fin k → Fin n) : Prop :=
  ∃ colour, ∀ i, c (x i) = colour

end Erdos781

namespace Erdos781

open scoped Classical in
def ForcesDescending (k n : ℕ) : Prop :=
  ∀ c : Fin n → Bool, ∃ x : Fin k → Fin n,
    IsDescendingWave x ∧ Monochromatic c x

end Erdos781

namespace Erdos781

open scoped Classical in
noncomputable def waveRamsey (k : ℕ) : ℕ :=
  sInf {n : ℕ | ForcesDescending k n}

end Erdos781

namespace Erdos781

open scoped Classical in
theorem erdos_781 :
    (∀ k : ℕ, 2 ^ 50 ≤ k →
      k ^ 3 ≤ 2 ^ 48 * waveRamsey k ∧
        waveRamsey k ≤ 8 * k ^ 3 + 1) ∧
    ¬ (∀ k : ℕ, waveRamsey k = k ^ 2 - k + 1) := by
  sorry

end Erdos781

end
