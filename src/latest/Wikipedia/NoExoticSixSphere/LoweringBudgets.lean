import Wikipedia.NoExoticSixSphere.CompactLoweringCover

/-!
# Simultaneous energy budgets for a finite lowering sequence

The bandwidth is chosen after the common movement window. The per-step energy
allowance is then chosen after the bandwidth and the number of steps.
-/

namespace NoExoticSixSphere.FiniteControlledLowering

theorem exists_lowering_budgets (n : ℕ) (k : Fin n → ℝ)
    (floor level cap ζ b : ℝ) (hfloor : floor < level) (hcap : level < cap)
    (hζ : 0 < ζ) (hb : 0 < b) (hk : ∀ i, k i < level) :
    ∃ a > 0, ∃ ξ > 0,
      floor < level - a ∧ level + a < cap ∧ a ≤ b ∧ ξ ≤ ζ ∧
      (level + a / 4) - (level - a) + 2 * (n : ℝ) * ξ ≤ 2 * ζ ∧
      (level - a) + (n : ℝ) * ξ ≤ level - a / 2 ∧
      ∀ i, k i + (n : ℝ) * ξ ≤ level - a / 2 := by
  classical
  obtain ⟨d, hd, hdk⟩ := exists_pos_le_finset Finset.univ (fun i ↦ (level - k i) / 4)
    (fun i _ ↦ by have := hk i; positivity)
  let a := min b (min ((level - floor) / 2)
    (min ((cap - level) / 2) (min (ζ / 2) d)))
  have ha : 0 < a := by dsimp [a]; positivity
  have hab : a ≤ b := min_le_left _ _
  have hafloor : a ≤ (level - floor) / 2 :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hacap : a ≤ (cap - level) / 2 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have haζ : a ≤ ζ / 2 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _)))
  have had : a ≤ d :=
    (min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_right _ _)))
  let ξ := min ζ (a / (16 * ((n : ℝ) + 1)))
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hden : 0 < 16 * ((n : ℝ) + 1) := by positivity
  have hξ : 0 < ξ := lt_min hζ (div_pos ha hden)
  have hξζ : ξ ≤ ζ := min_le_left _ _
  have hξa : ξ * (16 * ((n : ℝ) + 1)) ≤ a :=
    (le_div_iff₀ hden).mp (min_le_right _ _)
  have htotal : (n : ℝ) * ξ ≤ a / 8 := by nlinarith
  refine ⟨a, ha, ξ, hξ, by linarith, by linarith, hab, hξζ,
    by nlinarith, by linarith, ?_⟩
  intro i
  have hki := hdk i (Finset.mem_univ i)
  linarith

end NoExoticSixSphere.FiniteControlledLowering
