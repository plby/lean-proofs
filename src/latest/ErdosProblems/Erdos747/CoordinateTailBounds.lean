import ErdosProblems.Erdos747.CoordinateNumericalBounds

open Filter Real
open scoped BigOperators Topology

namespace Erdos747

noncomputable section

attribute [local instance] Classical.propDecidable

lemma coordinate_tail_base_le_exp (a mu : ℝ) (Q D S b : ℕ)
    (ha : 0 < a) (hmu : 0 ≤ mu) (hS : 0 < S)
    (hQ : (Q : ℝ) ≤ coordinatePairFraction a * S)
    (hD : (D : ℝ) ≤ 33 * mu) (hb : a * mu / 4 ≤ ((b + 1 : ℕ) : ℝ)) :
    Real.exp 1 * Q * D / ((S : ℝ) * ((b + 1 : ℕ) : ℝ)) ≤ Real.exp (-128 / a) := by
  have hSR : (0 : ℝ) < S := by exact_mod_cast hS
  have hbR : (0 : ℝ) < ((b + 1 : ℕ) : ℝ) := by positivity
  have hQratio : (Q : ℝ) / S ≤ coordinatePairFraction a := (div_le_iff₀ hSR).mpr hQ
  have hDratio : (D : ℝ) / ((b + 1 : ℕ) : ℝ) ≤ 132 / a := by
    apply (div_le_div_iff₀ hbR ha).mpr
    have h := mul_le_mul_of_nonneg_left hD ha.le
    nlinarith only [h, hb]
  calc
    _ = Real.exp 1 * ((Q : ℝ) / S) * ((D : ℝ) / ((b + 1 : ℕ) : ℝ)) := by ring
    _ ≤ Real.exp 1 * coordinatePairFraction a * (132 / a) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left hQratio (Real.exp_pos _).le
      · exact hDratio
      · positivity
      · exact mul_nonneg (Real.exp_pos _).le (coordinatePairFraction_pos a ha).le
    _ = (1 / 2 : ℝ) * Real.exp (-128 / a) := by
      unfold coordinatePairFraction
      field_simp
      ring
    _ ≤ _ := by linarith only [Real.exp_pos (-128 / a)]

lemma coordinate_tail_pow_le_exp (a mu : ℝ) (Q D S b : ℕ)
    (ha : 0 < a) (hmu : 0 ≤ mu) (hS : 0 < S)
    (hQ : (Q : ℝ) ≤ coordinatePairFraction a * S)
    (hD : (D : ℝ) ≤ 33 * mu) (hb : a * mu / 4 ≤ ((b + 1 : ℕ) : ℝ)) :
    (Real.exp 1 * Q * D / ((S : ℝ) * ((b + 1 : ℕ) : ℝ)))^(b + 1) ≤ Real.exp (-32 * mu) := by
  have hbase := coordinate_tail_base_le_exp a mu Q D S b ha hmu hS hQ hD hb
  have hscaled := mul_le_mul_of_nonneg_left hb (show 0 ≤ 128 / a by positivity)
  have heq : (128 / a) * (a * mu / 4) = 32 * mu := by field_simp; ring
  rw [heq] at hscaled
  calc
    _ ≤ (Real.exp (-128 / a))^(b + 1) := by gcongr
    _ = Real.exp (((b + 1 : ℕ) : ℝ) * (-128 / a)) := (Real.exp_nat_mul _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr (by
      calc
        _ = -((128 / a) * ((b + 1 : ℕ) : ℝ)) := by ring
        _ ≤ -(32 * mu) := neg_le_neg hscaled
        _ = _ := by ring)

lemma coordinate_parameter_tail_pow_le_exp (n M : ℕ) (a : ℝ)
    (hn : 5 ≤ n) (ha : 0 < a) (hmean : 1 ≤ (M : ℝ) / n)
    (hlarge : 8 ≤ a * ((M : ℝ) / n)) :
    (Real.exp 1 * coordinatePairCutoff n a * coordinateDegreeCeil n M /
      ((coordinatePairPopulation n : ℝ) * ((coordinateTailFloor n M a + 1 : ℕ) : ℝ)))^
        (coordinateTailFloor n M a + 1) ≤ Real.exp (-32 * ((M : ℝ) / n)) := by
  have hSpos : 0 < coordinatePairPopulation n := by
    have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hp : (0 : ℝ) < coordinatePairPopulation n :=
      (show (0 : ℝ) < 2 * (n : ℝ)^2 by positivity).trans_le (coordinatePairPopulation_ge_two_sq n hn)
    exact_mod_cast hp
  exact coordinate_tail_pow_le_exp a ((M : ℝ) / n)
    (coordinatePairCutoff n a) (coordinateDegreeCeil n M) (coordinatePairPopulation n)
    (coordinateTailFloor n M a) ha (by positivity) hSpos
    (Nat.floor_le (mul_nonneg (coordinatePairFraction_pos a ha).le (Nat.cast_nonneg _)))
    (coordinateDegreeCeil_le n M hmean) (coordinate_degree_rounding_bounds n M a ha hlarge).2.2.2

lemma coordinate_parameter_failure_probability_le (n M : ℕ) (a c : ℝ)
    (hn : 5 ≤ n) (ha : 0 < a) (ha1 : a ≤ 1) (hM : M ≤ (allEdges n).card)
    (hmean : 1 ≤ (M : ℝ) / n) (hlarge : 8 ≤ a * ((M : ℝ) / n)) :
    finsetProbability (sample n M)
        (SomeAdaptiveCoordinateTailFailure n c (coordinateDegreeFloor n M a)
          (coordinateDegreeCeil n M) (coordinatePairCutoff n a) (coordinateTailFloor n M a)
          (coordinateVertexAllowance n)) ≤
      (3 : ℝ) * (allEdges n).card * ((3 * n : ℕ) : ℝ) * Real.exp (-32 * ((M : ℝ) / n)) := by
  have hround := coordinate_degree_rounding_bounds n M a ha hlarge
  have hpop := coordinateTailFloor_succ_le_population n M a hn ha.le ha1 hM
  have hraw := someAdaptiveCoordinateTailFailure_probability_le_exp
    (c := c) (D := coordinateDegreeCeil n M) (Q := coordinatePairCutoff n a)
    (e₁ := coordinateVertexAllowance n) hM hround.1 hpop
  have hpow := coordinate_parameter_tail_pow_le_exp n M a hn ha hmean hlarge
  apply hraw.trans
  norm_num only [Nat.cast_mul, Nat.cast_ofNat]
  have hfrac : ((3 * n : ℕ) : ℝ) *
      (Real.exp 1 * coordinatePairCutoff n a * coordinateDegreeCeil n M /
        ((coordinatePairPopulation n : ℝ) * ((coordinateTailFloor n M a + 1 : ℕ) : ℝ)))^
        (coordinateTailFloor n M a + 1) / ((coordinateVertexAllowance n + 1 : ℕ) : ℝ) ≤
      ((3 * n : ℕ) : ℝ) * Real.exp (-32 * ((M : ℝ) / n)) := by
    calc
      _ ≤ ((3 * n : ℕ) : ℝ) *
          (Real.exp 1 * coordinatePairCutoff n a * coordinateDegreeCeil n M /
            ((coordinatePairPopulation n : ℝ) * ((coordinateTailFloor n M a + 1 : ℕ) : ℝ)))^
            (coordinateTailFloor n M a + 1) :=
        div_le_self (by positivity) (by exact_mod_cast (show 1 ≤ coordinateVertexAllowance n + 1 by omega))
      _ ≤ _ := mul_le_mul_of_nonneg_left hpow (by positivity)
  convert mul_le_mul_of_nonneg_left hfrac (show (0 : ℝ) ≤ 3 * (allEdges n).card by positivity) using 1 <;>
    norm_num only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one, coordinatePairPopulation] <;> ring

end

end Erdos747
