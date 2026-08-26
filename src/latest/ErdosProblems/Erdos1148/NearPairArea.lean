import ErdosProblems.Erdos1148.PairOrbitArea

/-!
# The unnormalized cubic bound in flow parameters

Summing the close-flow parameter areas for mixed coefficients in their
actual entrywise-closeness range gives `Cε*d^(1+ε)*η^3`.
The conversion to closed-geodesic measures and volume normalization remain
separate from this estimate.
-/

namespace Erdos1148.DukeArithmetic

lemma log_four_mul_le_rpow {d ε : ℝ} (hd : 1 ≤ d) (hε : 0 < ε) :
    Real.log (4 * d) ≤ (Real.log 4 + ε⁻¹) * d ^ ε := by
  have hd0 : 0 < d := lt_of_lt_of_le zero_lt_one hd
  have hpow := Real.one_le_rpow hd hε.le
  have hlog := Real.log_le_rpow_div hd0.le hε
  have h4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  rw [Real.log_mul (by norm_num) hd0.ne']
  rw [div_eq_mul_inv] at hlog
  nlinarith

theorem exists_sum_near_pairOrbitParameterArea_le {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ (d : ℕ) (hd : 0 < (d : ℤ)) (η : ℝ),
      0 < η → η ≤ 1 / 2 →
      (∑ ℓ ∈ noncentralMultiples (2 * d) ⌊4 * (d : ℝ) * η ^ 2⌋ 1,
        pairOrbitParameterArea hd ℓ η) ≤ ENNReal.ofReal (K * (d : ℝ) ^ (1 + ε) * η ^ 3) := by
  classical
  let a := ε / 2
  have ha : 0 < a := by dsimp [a]; positivity
  obtain ⟨C, hC, harea⟩ := exists_sum_pairOrbitParameterArea_le ha
  let B := Real.log 4 + a⁻¹
  have hB : 0 < B := by
    have h4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    dsimp [B]
    positivity
  refine ⟨4 * C * B, by positivity, ?_⟩
  intro d hd η hη0 hη
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hd1 : (1 : ℝ) ≤ d := by
    exact_mod_cast (show 1 ≤ d by exact_mod_cast hd)
  let L : ℤ := ⌊4 * (d : ℝ) * η ^ 2⌋
  have hL : 0 ≤ L ∧ L ≤ d := by
    simpa only [L, Int.cast_natCast] using close_pairing_cutoff_bounds hd hη0.le hη
  have hfloor : (L : ℝ) ≤ 4 * (d : ℝ) * η ^ 2 := Int.floor_le _
  have hlog : Real.log (4 * (d : ℝ)) ≤ B * (d : ℝ) ^ a :=
    log_four_mul_le_rpow hd1 ha
  have hlog0 : 0 ≤ Real.log (4 * (d : ℝ)) := by
    apply Real.log_nonneg
    linarith
  have hpow : (d : ℝ) * ((d : ℝ) ^ a * (d : ℝ) ^ a) = (d : ℝ) ^ (1 + ε) := by
    rw [← Real.rpow_add hdR]
    have haa : a + a = ε := by dsimp [a]; ring
    rw [haa, Real.rpow_add hdR, Real.rpow_one]
  apply (harea d L hd η hL.1 hL.2 hη0 hη).trans
  apply ENNReal.ofReal_le_ofReal
  calc
    C * (L : ℝ) * η * (d : ℝ) ^ a * Real.log (4 * (d : ℝ)) ≤
        C * (4 * (d : ℝ) * η ^ 2) * η * (d : ℝ) ^ a * Real.log (4 * (d : ℝ)) := by
      gcongr
    _ ≤ C * (4 * (d : ℝ) * η ^ 2) * η * (d : ℝ) ^ a * (B * (d : ℝ) ^ a) := by
      gcongr
    _ = (4 * C * B) * ((d : ℝ) * ((d : ℝ) ^ a * (d : ℝ) ^ a)) * η ^ 3 := by ring
    _ = (4 * C * B) * (d : ℝ) ^ (1 + ε) * η ^ 3 := by rw [hpow]

end Erdos1148.DukeArithmetic
