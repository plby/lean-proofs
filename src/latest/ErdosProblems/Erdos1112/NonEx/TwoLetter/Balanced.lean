/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Copyright 2026 Johan Land.
Licensed under the Apache License, Version 2.0; see LICENSE and NOTICE.
Modified for this repository and Lean/Mathlib 4.33.0. -/
/-
Erdős Problem 1112.
Informal proof: Johan Land, using Claude Fable 5 and Claude Opus 4.8.
Formal proof: Johan Land, using Claude Fable 5 and Claude Opus 4.8.
GPT-5.5 and Gemini 3.1 supplied advice and adversarial review.
Source: https://www.erdosproblems.com/1112#post-7375
https://github.com/beetree/math_erdos_1112/tree/63ed94d3e802782aeb521095c17d6109a2dc57b5
Original Lean version: 4.27.0.
Original Mathlib commit: a3a10db0e9d66acbebf76c5e6a135066525ac900.
-/
/-
The Morse–Hedlund classification of balanced one-sided binary words.
Design: slope via sSup, rational ⇒ ultimately periodic, irrational ⇒
threshold separation ⇒ exact tail mechanicity.

`balanced_classification` is assembled here from the staged lemmas in
`MH/Slope.lean`, `MH/RationalCase.lean`, `MH/IrrationalCase.lean`. The
density-free route (threshold separation via discrepancy-oscillation
iteration; no density, equidistribution, or three-distance) is in
`MH/IrrationalCase.lean`.
-/
import ErdosProblems.Erdos1112.NonEx.TwoLetter.MH.RationalCase
import ErdosProblems.Erdos1112.NonEx.TwoLetter.MH.IrrationalCase

namespace Erdos1112
namespace Proof

/-- Balancedness of the counting function: any two equal-length windows
carry 1-counts differing by at most 1. -/
def BalancedQ (h : ℕ → Bool) : Prop :=
  ∀ i j n : ℕ, (qCount h (i + n) - qCount h i : ℤ) -
    (qCount h (j + n) - qCount h j : ℤ) ≤ 1

/-- Eventual periodicity of a word. -/
def EventuallyPeriodicW (h : ℕ → Bool) : Prop :=
  ∃ p, 0 < p ∧ ∃ T, ∀ n, T ≤ n → h (n + p) = h n

/-- **Morse–Hedlund (one-sided, minimized form)**: a balanced binary word is
ultimately periodic, or some tail of its counting function is exactly
mechanical with irrational slope: `q(T+n) − q(T) = ⌊n·α + β⌋` for all `n`. -/
theorem balanced_classification (h : ℕ → Bool) (bal : BalancedQ h) :
    EventuallyPeriodicW h ∨
      ∃ (α β : ℝ) (T : ℕ), Irrational α ∧ α ∈ Set.Ioo (0 : ℝ) 1 ∧
        ∀ n : ℕ, (qCount h (T + n) : ℤ) - qCount h T = ⌊(n : ℝ) * α + β⌋ := by
  have hbal : MH.BalancedHyp h := bal
  set α := MH.slope h with hα_def
  -- the uniform discrepancy bound |q n − n·α| ≤ 1 (n = 0 gives 0)
  have hD : ∀ n : ℕ, |MH.disc h α n| ≤ 1 := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [MH.disc, MH.qCount_zero]
    · have h1 := MH.le_slope (h := h) n hn
      have h2 := MH.slope_le (h := h) (hbal := hbal) n hn
      rw [MH.disc, abs_le]
      constructor <;> linarith
  by_cases hirr : Irrational α
  · -- irrational slope: mechanical tail
    right
    obtain ⟨β, T, hmech⟩ := MH.mechanical_tail h hbal hirr hD
    refine ⟨α, β, T, hirr, ⟨?_, ?_⟩, hmech⟩
    · -- 0 < α : slope_nonneg plus irrationality excludes 0
      rcases eq_or_lt_of_le (MH.slope_nonneg (h := h)) with h0 | h0
      · exact absurd h0.symm (by simpa using hirr.ne_int 0)
      · exact h0
    · -- α < 1 : slope_le_one plus irrationality excludes 1
      rcases eq_or_lt_of_le (MH.slope_le_one (h := h)) with h1 | h1
      · exact absurd h1 (by simpa using hirr.ne_int 1)
      · exact h1
  · -- rational slope: eventually periodic
    left
    obtain ⟨r, hr⟩ : α ∈ Set.range ((↑) : ℚ → ℝ) := not_not.mp hirr
    -- clear denominators: |r.den · q n − r.num · n| ≤ r.den
    have hden : ((r.den : ℝ)) * α = (r.num : ℝ) := by
      rw [← hr, Rat.cast_def]
      field_simp
    have hE : ∀ n : ℕ, |(r.den : ℤ) * qCount h n - r.num * n| ≤ r.den := by
      intro n
      have hDn := hD n
      rw [MH.disc] at hDn
      have hpos : (0 : ℝ) < (r.den : ℝ) := by exact_mod_cast r.pos
      have key : |((r.den : ℝ)) * qCount h n - (r.num : ℝ) * n| ≤ (r.den : ℝ) := by
        have expand : ((r.den : ℝ)) * qCount h n - (r.num : ℝ) * n =
            (r.den : ℝ) * ((qCount h n : ℝ) - n * α) := by
          rw [mul_sub]
          have hswap : (r.den : ℝ) * ((n : ℝ) * α) = (n : ℝ) * ((r.den : ℝ) * α) := by
            ring
          rw [hswap, hden]
          ring
        calc |((r.den : ℝ)) * qCount h n - (r.num : ℝ) * n|
            = (r.den : ℝ) * |(qCount h n : ℝ) - n * α| := by
              rw [expand, abs_mul, abs_of_pos hpos]
          _ ≤ (r.den : ℝ) * 1 := mul_le_mul_of_nonneg_left hDn hpos.le
          _ = (r.den : ℝ) := mul_one _
      exact_mod_cast (by push_cast; exact key :
        |((r.den : ℤ) : ℝ) * qCount h n - (r.num : ℝ) * n| ≤ ((r.den : ℤ) : ℝ))
    exact MH.eventuallyPeriodic_of_rational h hbal r.num r.den r.pos hE

/-- Balancedness follows from `W₂ ≤ 1` everywhere (paper 2.8(b) derivation). -/
theorem balancedQ_of_no_widthTwo (h : ℕ → Bool)
    (hno : ∀ σ, ¬ WidthTwoAt h σ) : BalancedQ h := by
  intro i j n
  by_contra hcon
  push Not at hcon
  -- a violation exhibits two pairs on the antidiagonal σ = i + j + n
  refine hno (i + (j + n)) ⟨i, j + n, i + n, j, rfl, by omega, ?_⟩
  omega

end Proof
end Erdos1112
