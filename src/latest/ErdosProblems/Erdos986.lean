/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 986.
https://www.erdosproblems.com/forum/thread/986

Informal authors:
- D. Bradač

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos986.md
-/
import ErdosProblems.Erdos920.Construction

/-!
# Erdős Problem 986

For every fixed `s ≥ 3`, the off-diagonal Ramsey number satisfies

`R(s,k) ≫ k^(s-1) / (log k)^c`

for some positive constant `c = c(s)`.  Bradač's construction proves the
stronger explicit exponent `c = 2s - 4`.
-/

open Real Filter

syntax (name := answerSyntax986) "answer(" term ")" : term
macro_rules
  | `(answer($t)) => `($t)

/-- `g ≫ h` means that `h` is big-O of `g` at infinity. -/
notation:50 g " ≫ " h => Asymptotics.IsBigO Filter.atTop h g

namespace Erdos986

/-- The exact asymptotic statement of Erdős Problem 986.

The logarithmic exponent is natural-valued, as in the analogous formal
statement of Erdős Problem 920.  This loses no content: Bradač supplies the
explicit positive integer exponent `2 * s - 4`. -/
def Problem986 : Prop :=
  ∀ s : ℕ, 3 ≤ s → ∃ c : ℕ, 0 < c ∧
    (fun k : ℕ ↦ (Ramsey.ramseyNumber s k : ℝ)) ≫
      (fun k : ℕ ↦
        (k : ℝ) ^ (s - 1) / Real.log (k : ℝ) ^ c)

/-- Bradač's stronger explicit lower bound, converted from an eventual
pointwise inequality to Mathlib's reverse big-O relation. -/
theorem bradac_ramsey_lower_bound_isBigO (s : ℕ) (hs : 3 ≤ s) :
    (fun k : ℕ ↦ (Ramsey.ramseyNumber s k : ℝ)) ≫
      (fun k : ℕ ↦
        (k : ℝ) ^ (s - 1) /
          Real.log (k : ℝ) ^ (2 * s - 4)) := by
  obtain ⟨A, hA, hbound⟩ :=
    Erdos920.RamseyPackaging.bradac_ramsey_lower_bound_eventually_of_package
      s hs (Erdos920.Construction.dStarFamily (s - 2) (by omega))
  refine Asymptotics.IsBigO.of_bound A⁻¹ ?_
  filter_upwards [hbound, eventually_ge_atTop (2 : ℕ)] with k hk hk2
  have hlog : 0 < Real.log (k : ℝ) :=
    Real.log_pos (by exact_mod_cast hk2)
  have hscale_nonneg :
      0 ≤ (k : ℝ) ^ (s - 1) /
        Real.log (k : ℝ) ^ (2 * s - 4) :=
    div_nonneg (pow_nonneg (Nat.cast_nonneg k) _)
      (pow_nonneg hlog.le _)
  have hramsey_nonneg :
      0 ≤ (Ramsey.ramseyNumber s k : ℝ) :=
    Nat.cast_nonneg _
  rw [Real.norm_eq_abs, abs_of_nonneg hscale_nonneg,
    Real.norm_eq_abs, abs_of_nonneg hramsey_nonneg]
  have hscaled :
      A * ((k : ℝ) ^ (s - 1) /
        Real.log (k : ℝ) ^ (2 * s - 4)) ≤
          (Ramsey.ramseyNumber s k : ℝ) := by
    simpa [mul_div_assoc] using hk
  calc
    (k : ℝ) ^ (s - 1) /
          Real.log (k : ℝ) ^ (2 * s - 4) =
        A⁻¹ * (A * ((k : ℝ) ^ (s - 1) /
          Real.log (k : ℝ) ^ (2 * s - 4))) := by
            field_simp [hA.ne']
    _ ≤ A⁻¹ * (Ramsey.ramseyNumber s k : ℝ) :=
      mul_le_mul_of_nonneg_left hscaled (inv_nonneg.mpr hA.le)

/-- The direct affirmative resolution of Problem 986. -/
theorem problem986 : Problem986 := by
  intro s hs
  refine ⟨2 * s - 4, by omega, ?_⟩
  exact bradac_ramsey_lower_bound_isBigO s hs

/-- Erdős Problem 986 has a positive answer. -/
theorem erdos_986 : answer(True) ↔ Problem986 := by
  constructor
  · intro _
    exact problem986
  · intro _
    trivial

end Erdos986

#print axioms Erdos986.erdos_986
