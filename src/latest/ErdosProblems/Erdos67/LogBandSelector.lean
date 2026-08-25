import ErdosProblems.Erdos67.LogBandCoverage

/-!
# Selecting a fixed logarithmic height band

For a fixed maximal derivative depth, all but the separated second-derivative
region fall into one of finitely many ordinary-Weyl bands.  The only boundary
case is just below `a = X^2`: failure of the second-derivative separation
forces enough lower height there to make the `r = 2` raw step scale at most
`X^(3/4)`.
-/

open Filter

namespace Erdos67.LogBandSelector

noncomputable section

open Erdos67.LogWeylParameters
open Erdos67.LogBandCoverage

/-- Eventually, failure of the separated `r=1` inequality forces the raw
third-derivative step scale into the controlled-Weyl translation window. -/
theorem exists_rawStepScale_two_threshold (H : ℕ) (hH : 0 < H) :
    ∃ X₀ : ℕ, ∀ X ≥ X₀, ∀ a U : ℝ,
      0 < a → (X : ℝ) ≤ U → U ≤ a →
      ¬8 * (H : ℝ) * a ≤ U ^ 2 →
      rawStepScale 2 X a ≤ (X : ℝ) ^ (3 / 4 : ℝ) := by
  have ht : Tendsto (fun X : ℕ ↦ (X : ℝ) ^ (1 / 4 : ℝ))
      atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).comp
      tendsto_natCast_atTop_atTop
  obtain ⟨X₁, hX₁⟩ := eventually_atTop.1
    ((tendsto_atTop.1 ht) (8 * H : ℝ))
  refine ⟨max 1 X₁, ?_⟩
  intro X hX a U ha hXU _hUa hfail
  have hXone : 1 ≤ X := (Nat.le_max_left 1 X₁).trans hX
  have hroot : (8 : ℝ) * H ≤ (X : ℝ) ^ (1 / 4 : ℝ) :=
    hX₁ X ((Nat.le_max_right 1 X₁).trans hX)
  exact (secondDerivative_or_rawStepScale_two hXone ha hXU hroot).resolve_left hfail

/-- Fixed finite-depth band selector.  The quantifier order is the one used
in the little-o proof: `R` and the second-derivative parameter `H` are fixed
before the scale tends to infinity. -/
theorem exists_fixedDepth_selector_threshold
    (R H : ℕ) (hR : 2 ≤ R) (hH : 0 < H) :
    ∃ X₀ : ℕ, ∀ X ≥ X₀, ∀ a U : ℝ,
      0 < a → (X : ℝ) ≤ U → U ≤ 2 * X → U ≤ a →
      a < (X : ℝ) ^ (R + 1) →
      (8 * (H : ℝ) * a ≤ U ^ 2 ∨
        ∃ r ∈ Finset.Icc 2 R,
          ((X : ℝ) ^ r ≤ a ∨
            rawStepScale r X a ≤ (X : ℝ) ^ (3 / 4 : ℝ)) ∧
          a < (X : ℝ) ^ (r + 1)) := by
  obtain ⟨X₀, hX₀⟩ := exists_rawStepScale_two_threshold H hH
  refine ⟨X₀, ?_⟩
  intro X hX a U ha hXU hUX hUa hupper
  by_cases hsecond : 8 * (H : ℝ) * a ≤ U ^ 2
  · exact Or.inl hsecond
  right
  have hraw2 : rawStepScale 2 X a ≤ (X : ℝ) ^ (3 / 4 : ℝ) :=
    hX₀ X hX a U ha hXU hUa hsecond
  induction R, hR using Nat.le_induction with
  | base =>
      refine ⟨2, Finset.mem_Icc.2 ⟨le_rfl, le_rfl⟩, ?_, ?_⟩
      · exact Or.inr hraw2
      · simpa using hupper
  | succ R hR ih =>
      by_cases hold : a < (X : ℝ) ^ (R + 1)
      · obtain ⟨r, hrmem, hrband, hrupper⟩ := ih hold
        exact ⟨r, Finset.mem_Icc.2
          ⟨(Finset.mem_Icc.mp hrmem).1,
            (Finset.mem_Icc.mp hrmem).2.trans (Nat.le_succ R)⟩,
          hrband, hrupper⟩
      · refine ⟨R + 1, Finset.mem_Icc.2 ⟨by omega, le_rfl⟩, ?_, ?_⟩
        · exact Or.inl (le_of_not_gt hold)
        · simpa [Nat.add_assoc] using hupper

/-- Canonical growing-lag version of the selector.  This is the form in
which the separated `r=1` estimate itself already has a coefficient tending
to zero. -/
theorem eventually_fixedDepth_selector
    (R : ℕ) (hR : 2 ≤ R) :
    ∀ᶠ X : ℕ in atTop, ∀ {a U : ℝ},
      0 < a → (X : ℝ) ≤ U → U ≤ 2 * X → U ≤ a →
      a < (X : ℝ) ^ (R + 1) →
      (8 * (rOneLagBudget X : ℝ) * a ≤ U ^ 2 ∨
        ∃ r ∈ Finset.Icc 2 R,
          ((X : ℝ) ^ r ≤ a ∨
            rawStepScale r X a ≤ (X : ℝ) ^ (3 / 4 : ℝ)) ∧
          a < (X : ℝ) ^ (r + 1)) := by
  filter_upwards [eventually_secondDerivative_or_rawStepScale_two] with X hcover
  intro a U ha hXU hUX hUa hupper
  rcases hcover ha hXU with hsecond | hraw2
  · exact Or.inl hsecond
  right
  induction R, hR using Nat.le_induction with
  | base =>
      refine ⟨2, Finset.mem_Icc.2 ⟨le_rfl, le_rfl⟩, ?_, ?_⟩
      · exact Or.inr hraw2
      · simpa using hupper
  | succ R hR ih =>
      by_cases hold : a < (X : ℝ) ^ (R + 1)
      · obtain ⟨r, hrmem, hrband, hrupper⟩ := ih hold
        exact ⟨r, Finset.mem_Icc.2
          ⟨(Finset.mem_Icc.mp hrmem).1,
            (Finset.mem_Icc.mp hrmem).2.trans (Nat.le_succ R)⟩,
          hrband, hrupper⟩
      · refine ⟨R + 1, Finset.mem_Icc.2 ⟨by omega, le_rfl⟩, ?_, ?_⟩
        · exact Or.inl (le_of_not_gt hold)
        · simpa [Nat.add_assoc] using hupper

end

end Erdos67.LogBandSelector
