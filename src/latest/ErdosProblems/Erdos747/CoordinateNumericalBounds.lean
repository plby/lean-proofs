import ErdosProblems.Erdos747.AggregatePolynomialSpread
import ErdosProblems.Erdos747.CoordinateTailSharp

open Filter Real
open scoped BigOperators Topology

namespace Erdos747

noncomputable section

def coordinateDegreeFloor (n M : ℕ) (a : ℝ) : ℕ := ⌊a * ((M : ℝ) / n) / 2⌋₊

def coordinateTailFloor (n M : ℕ) (a : ℝ) : ℕ := ⌊a * ((M : ℝ) / n) / 4⌋₊

def coordinateDegreeCeil (n M : ℕ) : ℕ := ⌈32 * ((M : ℝ) / n)⌉₊

def coordinatePairPopulation (n : ℕ) : ℕ := (3 * n - 4).choose 2

def coordinatePairFraction (a : ℝ) : ℝ := a / (264 * Real.exp 1) * Real.exp (-128 / a)

def coordinatePairCutoff (n : ℕ) (a : ℝ) : ℕ := ⌊coordinatePairFraction a * coordinatePairPopulation n⌋₊

def coordinateVertexAllowance (n : ℕ) : ℕ := n / 16

def coordinateResidualAllowance (n : ℕ) (zeta : ℝ) : ℕ := ⌈zeta * (allEdges (n - 1)).card⌉₊

lemma coordinatePairFraction_pos (a : ℝ) (ha : 0 < a) : 0 < coordinatePairFraction a := by
  unfold coordinatePairFraction
  positivity

lemma coordinatePairFraction_lt_one (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) :
    coordinatePairFraction a < 1 := by
  have he : Real.exp (-128 / a) ≤ 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (div_nonpos_of_nonpos_of_nonneg (by norm_num) ha.le)
  have he1 : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
  have hden : 0 < 264 * Real.exp 1 := by positivity
  have hquot : a / (264 * Real.exp 1) < 1 := by
    apply (div_lt_one hden).mpr
    linarith only [ha1, he1]
  have hquot0 : 0 ≤ a / (264 * Real.exp 1) := by positivity
  exact (mul_le_of_le_one_right hquot0 he).trans_lt hquot

lemma coordinate_degree_rounding_bounds (n M : ℕ) (a : ℝ)
    (ha : 0 < a) (hlarge : 8 ≤ a * ((M : ℝ) / n)) :
    coordinateTailFloor n M a < coordinateDegreeFloor n M a ∧
      a * ((M : ℝ) / n) / 8 ≤
        ((coordinateDegreeFloor n M a - coordinateTailFloor n M a : ℕ) : ℝ) ∧
      (coordinateDegreeFloor n M a : ℝ) ≤ a * ((M : ℝ) / n) / 2 ∧
      a * ((M : ℝ) / n) / 4 ≤ ((coordinateTailFloor n M a + 1 : ℕ) : ℝ) := by
  have hmu : 0 ≤ (M : ℝ) / n := by positivity
  have hdlo : a * ((M : ℝ) / n) / 2 < (coordinateDegreeFloor n M a : ℝ) + 1 := Nat.lt_floor_add_one _
  have hdhi : (coordinateDegreeFloor n M a : ℝ) ≤ a * ((M : ℝ) / n) / 2 := Nat.floor_le (by positivity)
  have hbhi : (coordinateTailFloor n M a : ℝ) ≤ a * ((M : ℝ) / n) / 4 := Nat.floor_le (by positivity)
  have hblo : a * ((M : ℝ) / n) / 4 < (coordinateTailFloor n M a : ℝ) + 1 := Nat.lt_floor_add_one _
  have hgap : (coordinateTailFloor n M a : ℝ) < coordinateDegreeFloor n M a := by
    linarith only [hdlo, hbhi, hlarge]
  have hbd : coordinateTailFloor n M a < coordinateDegreeFloor n M a := by exact_mod_cast hgap
  refine ⟨hbd, ?_, hdhi, ?_⟩
  · rw [Nat.cast_sub hbd.le]
    linarith only [hdlo, hbhi, hlarge]
  · simpa only [Nat.cast_add, Nat.cast_one] using hblo.le

lemma coordinateDegreeCeil_le (n M : ℕ) (hmean : 1 ≤ (M : ℝ) / n) :
    (coordinateDegreeCeil n M : ℝ) ≤ 33 * ((M : ℝ) / n) := by
  have hceil : (coordinateDegreeCeil n M : ℝ) < 32 * ((M : ℝ) / n) + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  linarith only [hceil, hmean]

lemma card_allEdges_le_nine_halves_cube (n : ℕ) :
    ((allEdges n).card : ℝ) ≤ (9 / 2 : ℝ) * n^3 := by
  rw [card_allEdges]
  have h := Nat.choose_le_pow_div (α := ℝ) 3 (3 * n)
  norm_num only [Nat.cast_mul, Nat.cast_ofNat, Nat.factorial_succ, Nat.factorial_zero] at h
  nlinarith only [h]

lemma coordinatePairPopulation_ge_two_sq (n : ℕ) (hn : 5 ≤ n) :
    (2 : ℝ) * n^2 ≤ coordinatePairPopulation n := by
  have h := Nat.pow_le_choose (α := ℝ) 2 (3 * n - 4)
  norm_num only [Nat.factorial_succ, Nat.factorial_zero, Nat.cast_ofNat] at h
  have hsub : 3 * n - 4 + 1 - 2 = 3 * n - 5 := by omega
  rw [hsub, Nat.cast_sub (by omega : 5 ≤ 3 * n), Nat.cast_mul, Nat.cast_ofNat] at h
  have hnR : (5 : ℝ) ≤ n := by exact_mod_cast hn
  have hlin : 2 * (n : ℝ) ≤ 3 * n - 5 := by linarith only [hnR]
  have hs : (2 * (n : ℝ))^2 ≤ (3 * n - 5)^2 :=
    (sq_le_sq₀ (by positivity) (by linarith only [hnR])).mpr hlin
  change (2 : ℝ) * n^2 ≤ ((3 * n - 4).choose 2 : ℝ)
  nlinarith only [h, hs]

lemma coordinateTailFloor_succ_le_population (n M : ℕ) (a : ℝ)
    (hn : 5 ≤ n) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hM : M ≤ (allEdges n).card) :
    coordinateTailFloor n M a + 1 ≤ coordinatePairPopulation n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn5 : (5 : ℝ) ≤ n := by exact_mod_cast hn
  have hmean : (M : ℝ) / n ≤ (9 / 2 : ℝ) * n^2 := by
    apply (div_le_iff₀ hnR).mpr
    have hMR : (M : ℝ) ≤ (allEdges n).card := by exact_mod_cast hM
    nlinarith only [hMR.trans (card_allEdges_le_nine_halves_cube n)]
  have hb : (coordinateTailFloor n M a : ℝ) ≤ a * ((M : ℝ) / n) / 4 := Nat.floor_le (by positivity)
  have haMu := mul_le_mul_of_nonneg_right ha1 (show 0 ≤ (M : ℝ) / n by positivity)
  have hS := coordinatePairPopulation_ge_two_sq n hn
  have hbound : (coordinateTailFloor n M a : ℝ) + 1 ≤ coordinatePairPopulation n := by
    nlinarith only [hb, haMu, hmean, hS, hn5, sq_nonneg ((n : ℝ) - 5)]
  exact_mod_cast hbound

end

end Erdos747
