import ErdosProblems.Erdos747.CoordinateNumericalBounds

open Filter Real
open scoped BigOperators Topology

namespace Erdos747

noncomputable section

def coordinateExceptionFraction (a : ℝ) : ℝ := coordinatePairFraction a / 1000

lemma coordinateExceptionFraction_pos (a : ℝ) (ha : 0 < a) :
    0 < coordinateExceptionFraction a := div_pos (coordinatePairFraction_pos a ha) (by norm_num)

lemma coordinateExceptionFraction_lt (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) :
    coordinateExceptionFraction a < 1 / 1000 :=
  div_lt_div_of_pos_right (coordinatePairFraction_lt_one a ha ha1) (by norm_num)

lemma coordinate_vertex_exception_budget (n : ℕ) (hn : 16 ≤ n) :
    2 * (coordinateVertexAllowance n + coordinateVertexAllowance n) + 12 ≤ n := by
  unfold coordinateVertexAllowance
  omega

lemma coordinateVertexAllowance_lower (n : ℕ) (hn : 16 ≤ n) :
    (n : ℝ) / 32 ≤ coordinateVertexAllowance n := by
  have hnat : n ≤ 32 * (n / 16) := by omega
  have hR : (n : ℝ) ≤ 32 * (coordinateVertexAllowance n : ℝ) := by exact_mod_cast hnat
  linarith only [hR]

lemma maximum_domination_fraction_lower (n : ℕ) (hn : 2 ≤ n) :
    (1 / 1000 : ℝ) ≤ (((n / 2 : ℕ) : ℝ)^3 / (allEdges n).card) := by
  have hK : (0 : ℝ) < (allEdges n).card := by
    rw [card_allEdges]
    exact_mod_cast Nat.choose_pos (show 3 ≤ 3 * n by omega)
  have hhalf : (n : ℝ) / 3 ≤ ((n / 2 : ℕ) : ℝ) := by
    have hnat : n ≤ 3 * (n / 2) := by omega
    have hR : (n : ℝ) ≤ 3 * ((n / 2 : ℕ) : ℝ) := by exact_mod_cast hnat
    linarith only [hR]
  have hcube : ((n : ℝ) / 3)^3 ≤ ((n / 2 : ℕ) : ℝ)^3 := by gcongr
  have hupper := card_allEdges_le_nine_halves_cube n
  apply (le_div_iff₀ hK).mpr
  have hn3 : 0 ≤ (n : ℝ)^3 := by positivity
  nlinarith only [hcube, hupper, hn3]

lemma coordinate_residual_exception_budget (n : ℕ) (a : ℝ)
    (hn : 32 ≤ n) (ha : 0 < a)
    (hlarge : 100 ≤ coordinatePairFraction a * (n : ℝ)^3) :
    3 * coordinateResidualAllowance n (coordinateExceptionFraction a) ≤
      coordinateVertexAllowance n * (coordinatePairCutoff n a + 1) := by
  let q := coordinatePairFraction a
  have hq : 0 < q := coordinatePairFraction_pos a ha
  have hqdiv : 0 ≤ q / 1000 := div_nonneg hq.le (by norm_num)
  have hK : ((allEdges (n - 1)).card : ℝ) ≤ (9 / 2 : ℝ) * n^3 := by
    apply (card_allEdges_le_nine_halves_cube (n - 1)).trans
    gcongr
    exact_mod_cast Nat.sub_le n 1
  have hB : (coordinateResidualAllowance n (coordinateExceptionFraction a) : ℝ) ≤
      (q / 1000) * ((allEdges (n - 1)).card : ℝ) + 1 :=
    (Nat.ceil_lt_add_one (mul_nonneg
      (coordinateExceptionFraction_pos a ha).le (Nat.cast_nonneg _))).le
  have hBupper : (coordinateResidualAllowance n (coordinateExceptionFraction a) : ℝ) ≤
      (q / 1000) * ((9 / 2 : ℝ) * n^3) + 1 := by
    exact hB.trans (add_le_add (mul_le_mul_of_nonneg_left hK hqdiv) le_rfl)
  have he := coordinateVertexAllowance_lower n (by omega)
  have hQ : q * coordinatePairPopulation n ≤ ((coordinatePairCutoff n a + 1 : ℕ) : ℝ) := by
    rw [Nat.cast_add, Nat.cast_one]
    exact (Nat.lt_floor_add_one (q * coordinatePairPopulation n)).le
  have hS := coordinatePairPopulation_ge_two_sq n (by omega)
  have hQlower : q * (2 * (n : ℝ)^2) ≤ ((coordinatePairCutoff n a + 1 : ℕ) : ℝ) :=
    (mul_le_mul_of_nonneg_left hS hq.le).trans hQ
  have hprod : (n : ℝ) / 32 * (q * (2 * (n : ℝ)^2)) ≤
      (coordinateVertexAllowance n : ℝ) * ((coordinatePairCutoff n a + 1 : ℕ) : ℝ) :=
    mul_le_mul he hQlower (by positivity) (by positivity)
  have hbound : (3 : ℝ) * coordinateResidualAllowance n (coordinateExceptionFraction a) ≤
      (coordinateVertexAllowance n : ℝ) * ((coordinatePairCutoff n a + 1 : ℕ) : ℝ) := by
    change 100 ≤ q * (n : ℝ)^3 at hlarge
    nlinarith only [hBupper, hprod, hlarge]
  exact_mod_cast hbound

lemma eventually_coordinate_exception_budgets (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) :
    ∀ᶠ n in atTop,
      3 * coordinateResidualAllowance n (coordinateExceptionFraction a) ≤
        coordinateVertexAllowance n * (coordinatePairCutoff n a + 1) ∧
      2 * (coordinateVertexAllowance n + coordinateVertexAllowance n) + 12 ≤ n ∧
      (1 / 1000 : ℝ) ≤ (((n / 2 : ℕ) : ℝ)^3 / (allEdges n).card) := by
  have hpow : Tendsto (fun n : ℕ ↦ (n : ℝ)^3) atTop atTop :=
    (tendsto_pow_atTop (by norm_num : (3 : ℕ) ≠ 0)).comp tendsto_natCast_atTop_atTop
  have hlarge := (hpow.const_mul_atTop (coordinatePairFraction_pos a ha)).eventually_ge_atTop 100
  filter_upwards [hlarge, eventually_ge_atTop 32] with n hlargeN hn
  exact ⟨coordinate_residual_exception_budget n a hn ha hlargeN,
    coordinate_vertex_exception_budget n (by omega), maximum_domination_fraction_lower n (by omega)⟩

end

end Erdos747
