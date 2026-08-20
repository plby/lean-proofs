/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos957.Charge

/-!
# Erdős Problem 957: asymptotic packaging

This module turns the finite linear-error resolution into the literal
uniform epsilon and filter formulations of the coefficient `9 / 8 + o(1)`.
-/

namespace Erdos957

/-- The precise finite resolution proved by Dumitrescu: the product has a
uniform error bounded linearly in the number of points. -/
def HasLinearErrorBound : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ (A : Finset Point) (d₁ dₖ : ℝ),
      IsMinimumDistance A d₁ →
      IsMaximumDistance A dₖ →
      (multiplicity A d₁ : ℝ) * multiplicity A dₖ ≤
        (9 / 8 : ℝ) * (A.card : ℝ) ^ 2 + C * A.card

/-- The literal epsilon-eventual meaning of the upper bound with asymptotic
coefficient `9 / 8 + o(1)`. -/
def HasNineEighthsAsymptoticBound : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ N : ℕ, ∀ (A : Finset Point) (d₁ dₖ : ℝ),
      N ≤ A.card →
      IsMinimumDistance A d₁ →
      IsMaximumDistance A dₖ →
      (multiplicity A d₁ : ℝ) * multiplicity A dₖ ≤
        ((9 / 8 : ℝ) + ε) * (A.card : ℝ) ^ 2

/-- The same asymptotic assertion, expressed literally as an eventual
statement on the filter `atTop` of cardinalities. -/
def HasNineEighthsFilterBound : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∀ᶠ n : ℕ in Filter.atTop,
      ∀ (A : Finset Point) (d₁ dₖ : ℝ),
        A.card = n →
        IsMinimumDistance A d₁ →
        IsMaximumDistance A dₖ →
        (multiplicity A d₁ : ℝ) * multiplicity A dₖ ≤
          ((9 / 8 : ℝ) + ε) * (n : ℝ) ^ 2

/-- A uniform `O(n)` additive error is `o(n²)`, in the exact epsilon form
needed for Problem 957. -/
theorem linearErrorBound_implies_nineEighthsAsymptoticBound
    (h : HasLinearErrorBound) : HasNineEighthsAsymptoticBound := by
  rcases h with ⟨C, hC, h⟩
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt (C / ε)
  refine ⟨N, ?_⟩
  intro A d₁ dₖ hcard hmin hmax
  have hbase := h A d₁ dₖ hmin hmax
  have hNcard : (N : ℝ) ≤ (A.card : ℝ) := by exact_mod_cast hcard
  have hCdiv : C / ε ≤ (A.card : ℝ) := le_trans (le_of_lt hN) hNcard
  have hCle : C ≤ ε * (A.card : ℝ) := by
    calc
      C = ε * (C / ε) := by field_simp [ne_of_gt hε]
      _ ≤ ε * (A.card : ℝ) := mul_le_mul_of_nonneg_left hCdiv hε.le
  have hcard_nonneg : (0 : ℝ) ≤ A.card := by positivity
  have hlinear : C * (A.card : ℝ) ≤ ε * (A.card : ℝ) ^ 2 := by
    calc
      C * (A.card : ℝ) ≤ (ε * (A.card : ℝ)) * (A.card : ℝ) :=
        mul_le_mul_of_nonneg_right hCle hcard_nonneg
      _ = ε * (A.card : ℝ) ^ 2 := by ring
  calc
    (multiplicity A d₁ : ℝ) * multiplicity A dₖ
        ≤ (9 / 8 : ℝ) * (A.card : ℝ) ^ 2 + C * A.card := hbase
    _ ≤ (9 / 8 : ℝ) * (A.card : ℝ) ^ 2 + ε * (A.card : ℝ) ^ 2 :=
      add_le_add le_rfl hlinear
    _ = ((9 / 8 : ℝ) + ε) * (A.card : ℝ) ^ 2 := by ring

/-- The threshold and filter formulations of the asymptotic upper bound are
equivalent. -/
theorem nineEighthsAsymptoticBound_iff_filterBound :
    HasNineEighthsAsymptoticBound ↔ HasNineEighthsFilterBound := by
  constructor
  · intro h ε hε
    obtain ⟨N, hN⟩ := h ε hε
    filter_upwards [Filter.eventually_ge_atTop N] with n hn
    intro A d₁ dₖ hcard hmin hmax
    subst n
    exact hN A d₁ dₖ hn hmin hmax
  · intro h ε hε
    have heventual := h ε hε
    rw [Filter.eventually_atTop] at heventual
    obtain ⟨N, hN⟩ := heventual
    refine ⟨N, ?_⟩
    intro A d₁ dₖ hcard hmin hmax
    exact hN A.card hcard A d₁ dₖ rfl hmin hmax

/-- Direct filter-form corollary of the finite linear-error estimate. -/
theorem linearErrorBound_implies_nineEighthsFilterBound
    (h : HasLinearErrorBound) : HasNineEighthsFilterBound :=
  nineEighthsAsymptoticBound_iff_filterBound.mp
    (linearErrorBound_implies_nineEighthsAsymptoticBound h)



end Erdos957

