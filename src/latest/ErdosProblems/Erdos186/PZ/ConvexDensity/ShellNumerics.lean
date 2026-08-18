/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.ConvexDensity.InitialRegularization
import ErdosProblems.Erdos186.PZ.ConvexDensity.UnitGraphGrid

/-!
# Arithmetic of the two relative dyadic shells

The occupancy selected in the second grid is an *absolute* natural number.
The parameter called `K` in Pham--Zakharov is that occupancy divided by the
average cap occupancy, equivalently `Kabs * m^n / capCard`.  Recording this
normalization explicitly is what makes the low- and high-branch formulae in
`BranchNumerics` match the labelled finite-grid construction.
-/

open Set
open scoped BigOperators

namespace Erdos186.PZ.ConvexDensity

set_option autoImplicit false
noncomputable section

/-- The relative second-grid occupancy used in the numerical branch split. -/
def relativeGraphOccupancy (n m capCard Kabs : ℕ) : ℝ :=
  (Kabs : ℝ) * (m : ℝ) ^ n / (capCard : ℝ)

theorem relativeGraphOccupancy_pos {n m capCard Kabs : ℕ}
    (hm : 0 < m) (hcap : 0 < capCard) (hK : 0 < Kabs) :
    0 < relativeGraphOccupancy n m capCard Kabs := by
  simp only [relativeGraphOccupancy]
  positivity

/-- A family of disjoint assignment fibres, each heavier than `delta`, has
fewer than `1 / delta` labels. -/
theorem heavy_cell_card_lt_inv
    {α ι : Type*} [DecidableEq α] [DecidableEq ι]
    (points : Finset α) (cells : Finset ι) (cell : α → ι)
    {J : Finset ι} {delta : ℝ}
    (hdelta : 0 < delta) (hpoints : points.Nonempty)
    (hJcells : J ⊆ cells)
    (hmaps : ∀ x ∈ points, cell x ∈ cells)
    (hheavy : ∀ k ∈ J,
      delta * (points.card : ℝ) < DyadicCells.occupancy points cell k) :
    (J.card : ℝ) < 1 / delta := by
  obtain rfl | ⟨k₀, hk₀⟩ := J.eq_empty_or_nonempty
  · simp only [Finset.card_empty, Nat.cast_zero]
    positivity
  have hsumAll := DyadicCells.sum_occupancy_eq_card points cells cell hmaps
  have hsumSub :
      (∑ k ∈ J, DyadicCells.occupancy points cell k) ≤ points.card := by
    rw [← hsumAll]
    exact Finset.sum_le_sum_of_subset_of_nonneg hJcells (by simp)
  have hsumHeavy :
      (J.card : ℝ) * (delta * (points.card : ℝ)) <
        ∑ k ∈ J, (DyadicCells.occupancy points cell k : ℝ) := by
    rw [Finset.card_eq_sum_ones, Nat.cast_sum]
    simp only [Nat.cast_one]
    rw [Finset.sum_mul]
    exact Finset.sum_lt_sum
      (fun k hk ↦ by simpa only [one_mul] using (hheavy k hk).le)
      ⟨k₀, hk₀, by simpa only [one_mul] using hheavy k₀ hk₀⟩
  have hpointsPos : (0 : ℝ) < points.card := by
    exact_mod_cast Finset.card_pos.mpr hpoints
  have hsumCast :
      (∑ k ∈ J, (DyadicCells.occupancy points cell k : ℝ)) ≤
        (points.card : ℝ) := by exact_mod_cast hsumSub
  rw [lt_div_iff₀ hdelta]
  nlinarith

/-- The explicit dyadic level count dominates `1 / delta`. -/
theorem inv_lt_two_pow_dyadicLevelCount {delta : ℝ}
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1) :
    1 / delta < (2 : ℝ) ^ (dyadicLevelCount delta + 1 : ℕ) := by
  let x : ℝ := Real.logb 2 (1 / delta)
  have hinvOne : 1 ≤ 1 / delta := by
    rw [le_div_iff₀ hdelta]
    linarith
  have hx : 0 ≤ x := Real.logb_nonneg (by norm_num) hinvOne
  have hceil : x ≤ (Nat.ceil x : ℝ) := Nat.le_ceil x
  have hpow : 1 / delta ≤ (2 : ℝ) ^ (Nat.ceil x : ℕ) := by
    have hp := Real.rpow_le_rpow_of_exponent_le
      (by norm_num : (1 : ℝ) ≤ 2) hceil
    rw [Real.rpow_natCast] at hp
    have hlogb : (2 : ℝ) ^ x = 1 / delta := by
      dsimp only [x]
      exact Real.rpow_logb (by norm_num) (by norm_num) (by positivity)
    simpa only [hlogb] using hp
  have hlevel : dyadicLevelCount delta + 1 = Nat.ceil x + 2 := by
    rfl
  rw [hlevel, pow_add]
  calc
    1 / delta ≤ (2 : ℝ) ^ Nat.ceil x := hpow
    _ < (2 : ℝ) ^ Nat.ceil x * (2 : ℝ) ^ 2 := by
      have hp : (0 : ℝ) < (2 : ℝ) ^ Nat.ceil x := by positivity
      norm_num

theorem card_lt_two_pow_dyadicLevelCount
    {card : ℕ} {delta : ℝ}
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (hcard : (card : ℝ) < 1 / delta) :
    card < 2 ^ (dyadicLevelCount delta + 1) := by
  have h := hcard.trans (inv_lt_two_pow_dyadicLevelCount hdelta hdeltaOne)
  exact_mod_cast h

/-- The first shell's mass estimate and pointwise upper occupancy imply its
basic uniform-mass inequality. -/
theorem first_shell_uniform_mass
    {N L shellWeight M labels : ℕ}
    (hmass : N ≤ 2 * (L * shellWeight))
    (hupper : shellWeight ≤ 2 * M * labels) :
    N ≤ 4 * L * M * labels := by
  calc
    N ≤ 2 * (L * shellWeight) := hmass
    _ ≤ 2 * (L * (2 * M * labels)) := by
      exact Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left L hupper)
    _ = 4 * L * M * labels := by ring

/-- The identical estimate for the occupied second-grid shell. -/
theorem second_shell_uniform_mass
    {capCard L shellWeight Kabs cells : ℕ}
    (hmass : capCard ≤ L * shellWeight)
    (hupper : shellWeight ≤ 2 * Kabs * cells) :
    capCard ≤ 2 * L * Kabs * cells := by
  calc
    capCard ≤ L * shellWeight := hmass
    _ ≤ L * (2 * Kabs * cells) := Nat.mul_le_mul_left L hupper
    _ = 2 * L * Kabs * cells := by ring

/-- Combining the first shell with a cap fraction gives the labelled-point
capture estimate in the form used by `capturedFraction`. -/
theorem capturedFraction_le_selected_mass
    {n m N L M labels capCard Kabs : ℕ} {c q : ℝ}
    (hN : 0 < N) (hL : 0 < L) (hm : 0 < m)
    (hlabels : 0 < labels) (hcapCard : 0 < capCard) (hK : 0 < Kabs)
    (hc : 0 ≤ c) (hq : 0 ≤ q)
    (hfirst : N ≤ 4 * L * M * labels)
    (hcap : c * q ^ n * (labels : ℝ) ≤ (capCard : ℝ)) :
    (c / 4) * q ^ n * relativeGraphOccupancy n m capCard Kabs /
          ((m : ℝ) ^ n * (L : ℝ)) * (N : ℝ) ≤
      (Kabs * M : ℕ) := by
  have hNR : (N : ℝ) ≤ 4 * (L : ℝ) * M * labels := by exact_mod_cast hfirst
  have hcapR : 0 < (capCard : ℝ) := by exact_mod_cast hcapCard
  have hmR : 0 < (m : ℝ) ^ n := by positivity
  have hLR : 0 < (L : ℝ) := by exact_mod_cast hL
  have hlabelsR : 0 < (labels : ℝ) := by exact_mod_cast hlabels
  have hKR : 0 ≤ (Kabs : ℝ) := by positivity
  rw [relativeGraphOccupancy]
  push_cast
  field_simp
  nlinarith [mul_nonneg hc (Real.rpow_nonneg hq n),
    mul_nonneg hKR (show (0 : ℝ) ≤ M by positivity)]

/-- The second-shell mass inequality converts the Lemma 2 denominator
`cells` into the normalized relative occupancy. -/
theorem inv_cells_le_relativeGraphOccupancy
    {n m capCard Kabs L cells : ℕ}
    (hm : 0 < m) (hcap : 0 < capCard) (hK : 0 < Kabs)
    (hL : 0 < L) (hcells : 0 < cells)
    (hmass : capCard ≤ 2 * L * Kabs * cells) :
    (1 : ℝ) / (cells : ℝ) ≤
      2 * (L : ℝ) * relativeGraphOccupancy n m capCard Kabs /
        (m : ℝ) ^ n := by
  have hmassR : (capCard : ℝ) ≤
      2 * (L : ℝ) * Kabs * cells := by exact_mod_cast hmass
  have hcapR : 0 < (capCard : ℝ) := by exact_mod_cast hcap
  have hcellsR : 0 < (cells : ℝ) := by exact_mod_cast hcells
  have hmR : 0 < (m : ℝ) ^ n := by positivity
  rw [relativeGraphOccupancy]
  field_simp
  nlinarith

end
end Erdos186.PZ.ConvexDensity
