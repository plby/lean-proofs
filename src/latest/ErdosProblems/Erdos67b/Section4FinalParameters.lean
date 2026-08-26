import ErdosProblems.Erdos67b.Section4ParameterHierarchy

/-! # Enlarging the separation exponent after the BCC choices -/

namespace Erdos67b

noncomputable section

def Section4BCCParameters.withLargerD {A : ℕ} {B : ℝ}
    (P : Section4BCCParameters A B) (D : ℕ) (hD : P.D ≤ D) :
    Section4BCCParameters A B :=
  { P with
    D := D
    D_pos := P.D_pos.trans_le hD
    taylorScale_le := P.taylorScale_le.trans hD }

theorem exists_section4BCCParameters_with_large_separation
    (A : ℕ) (B : ℝ) (hA : 2 ≤ A) (hB : 0 ≤ B) {c : ℝ} (hc : 0 < c) :
    ∃ P : Section4BCCParameters A B, 16 * (P.H : ℝ) ≤ c * P.D := by
  obtain ⟨P⟩ := exists_section4BCCParameters A B hA hB
  let D := max P.D ⌈16 * (P.H : ℝ) / c⌉₊
  refine ⟨P.withLargerD D (le_max_left _ _), ?_⟩
  change 16 * (P.H : ℝ) ≤ c * D
  have hDnat : ⌈16 * (P.H : ℝ) / c⌉₊ ≤ D := le_max_right _ _
  have hceil : 16 * (P.H : ℝ) / c ≤ (D : ℝ) :=
    (Nat.le_ceil _).trans (Nat.cast_le.2 hDnat)
  have hh := (div_le_iff₀ hc).1 hceil
  simpa only [mul_comm c] using hh

end

end Erdos67b
