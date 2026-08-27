import ErdosProblems.Erdos4.FGKMTPowerLevelEnvelope

/-! Exponential savings for the complete finite distribution envelope. -/

namespace Erdos4.FGKMT

open Filter BoundedGaps.Maynard

noncomputable def averagedErrorEnvelope (C c L : ℝ) (x Q R : ℕ) : ℝ :=
  (Q : ℝ) * Real.log ((Q * x : ℕ) : ℝ) ^ 2 +
    4 * (R : ℝ) * (1 + Real.log (Q : ℝ)) *
      (C * ((x : ℝ) * Real.exp (-c * Real.sqrt (Real.log (x : ℝ))))) +
    L * vaughanPrimitiveMeanAbelEnvelope x (R : ℝ) Q *
      vaughanPrimitiveMeanEquationOneTwoLogPower x

theorem eventually_averagedErrorEnvelope_decay {C c a L : ℝ}
    (hC : 0 ≤ C) (hL : 0 ≤ L) (ha : 0 < a) (hca : 4 * a ≤ c) :
    ∀ᶠ x : ℕ in atTop, ∀ R Q : ℕ, 1 ≤ R → R ≤ Q →
      (Q : ℝ) ≤ vaughanCubeRoot x →
      Real.exp (a * Real.sqrt (Real.log (x : ℝ))) / 2 ≤ (R : ℝ) →
      (R : ℝ) ≤ Real.exp (a * Real.sqrt (Real.log (x : ℝ))) →
      averagedErrorEnvelope C c L x Q R ≤
        (4 + 4 * C + 62 * L) *
          ((x : ℝ) * Real.exp (-(a / 2) * Real.sqrt (Real.log (x : ℝ)))) := by
  have hpow4 := eventually_rpow_sqrtLog_pow_le_decay
    (α := (1 / 3 : ℝ)) (β := 1) (c := a / 2) (by norm_num) 4
  have hpow9 := eventually_rpow_sqrtLog_pow_le_decay
    (α := (5 / 6 : ℝ)) (β := 1) (c := a / 2) (by norm_num) 9
  have hpow11 := eventually_rpow_sqrtLog_pow_le_decay
    (α := (5 / 6 : ℝ)) (β := 1) (c := a / 2) (by norm_num) 11
  have hpoly2 := eventually_const_mul_sqrtLog_pow_le_exp 2 2 ha
  have hpoly9 := eventually_sqrtLog_pow_le_exp 9 (by positivity : 0 < a / 2)
  have hlog := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
    (eventually_ge_atTop (1 : ℝ))
  filter_upwards [hpow4, hpow9, hpow11, hpoly2, hpoly9, hlog, eventually_ge_atTop 1]
    with x hpow4 hpow9 hpow11 hpoly2 hpoly9 hlog hx
  change 1 ≤ Real.log (x : ℝ) at hlog
  intro R Q hR hRQ hQ hRlo hRhi
  let u := Real.sqrt (Real.log (x : ℝ))
  let S := (x : ℝ) * Real.exp (-(a / 2) * u)
  have hu : 0 ≤ u := Real.sqrt_nonneg _
  have husq : u ^ 2 = Real.log (x : ℝ) := Real.sq_sqrt (by linarith)
  have hxpos : (0 : ℝ) < x := by exact_mod_cast hx
  have hRpos : (0 : ℝ) < R := by exact_mod_cast hR
  have hQ1 : 1 ≤ Q := hR.trans hRQ
  have hQpos : (0 : ℝ) < Q := by exact_mod_cast hQ1
  have hS0 : 0 ≤ S := by dsimp [S]; positivity
  have hP4 : (x : ℝ) ^ (1 / 3 : ℝ) * u ^ 4 ≤ S := by
    simpa only [Real.rpow_one] using hpow4
  have hP9 : (x : ℝ) ^ (5 / 6 : ℝ) * u ^ 9 ≤ S := by
    simpa only [Real.rpow_one] using hpow9
  have hP11 : (x : ℝ) ^ (5 / 6 : ℝ) * u ^ 11 ≤ S := by
    simpa only [Real.rpow_one] using hpow11
  have hboundary : (Q : ℝ) * Real.log ((Q * x : ℕ) : ℝ) ^ 2 ≤ 4 * S := by
    apply (progression_boundary_power_level hx hQ1 hQ).trans
    have hh := mul_le_mul_of_nonneg_left hP4 (by norm_num : (0 : ℝ) ≤ 4)
    simpa only [mul_assoc] using hh
  have hlogQ : Real.log (Q : ℝ) ≤ Real.log (x : ℝ) :=
    Real.log_le_log hQpos (hQ.trans (cubeRoot_le_self hx))
  have hfactor : 1 + Real.log (Q : ℝ) ≤ Real.exp (a * u) := by
    have htwo : 1 + Real.log (Q : ℝ) ≤ 2 * u ^ 2 := by rw [husq]; linarith
    exact htwo.trans hpoly2
  have hsmall : 4 * (R : ℝ) * (1 + Real.log (Q : ℝ)) *
      (C * ((x : ℝ) * Real.exp (-c * u))) ≤ 4 * C * S := by
    have hprod : (R : ℝ) * (1 + Real.log (Q : ℝ)) ≤ Real.exp (a * u) * Real.exp (a * u) :=
      mul_le_mul hRhi hfactor (by linarith [Real.log_natCast_nonneg Q]) (Real.exp_pos _).le
    have hdecay : Real.exp (a * u) * Real.exp (a * u) * Real.exp (-c * u) ≤
        Real.exp (-(a / 2) * u) := by
      rw [← Real.exp_add, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hh := mul_le_mul_of_nonneg_right hca hu
      nlinarith [mul_nonneg ha.le hu]
    calc
      _ = (4 * C * (x : ℝ)) * (((R : ℝ) * (1 + Real.log (Q : ℝ))) * Real.exp (-c * u)) := by ring
      _ ≤ (4 * C * (x : ℝ)) * ((Real.exp (a * u) * Real.exp (a * u)) * Real.exp (-c * u)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hprod (Real.exp_pos _).le) (by positivity)
      _ ≤ (4 * C * (x : ℝ)) * Real.exp (-(a / 2) * u) :=
        mul_le_mul_of_nonneg_left hdecay (by positivity)
      _ = _ := by dsimp [S]; ring
  have hreciprocal : 4 * (x : ℝ) / (R : ℝ) ≤ 8 * (x : ℝ) * Real.exp (-a * u) := by
    calc
      _ ≤ 4 * (x : ℝ) / (Real.exp (a * u) / 2) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hRlo
      _ = _ := by rw [show -a * u = -(a * u) by ring, Real.exp_neg]; ring
  have hfirst : (4 * (x : ℝ) / (R : ℝ)) * u ^ 9 ≤ 8 * S := by
    calc
      _ ≤ (8 * (x : ℝ) * Real.exp (-a * u)) * u ^ 9 :=
        mul_le_mul_of_nonneg_right hreciprocal (pow_nonneg hu _)
      _ = (8 * (x : ℝ)) * (Real.exp (-a * u) * u ^ 9) := by ring
      _ ≤ (8 * (x : ℝ)) * (Real.exp (-a * u) * Real.exp ((a / 2) * u)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hpoly9 (Real.exp_pos _).le) (by positivity)
      _ = 8 * S := by
        rw [← Real.exp_add]
        have he : -a * u + (a / 2) * u = -(a / 2) * u := by ring
        rw [he]
        dsimp [S]
        ring
  have hrest : (27 * (x : ℝ) ^ (5 / 6 : ℝ) * (1 + Real.log (x : ℝ))) * u ^ 9 ≤ 54 * S := by
    calc
      _ = 27 * ((x : ℝ) ^ (5 / 6 : ℝ) * u ^ 9 + (x : ℝ) ^ (5 / 6 : ℝ) * u ^ 11) := by
        rw [← husq]
        ring
      _ ≤ _ := (mul_le_mul_of_nonneg_left (add_le_add hP9 hP11)
        (by norm_num : (0 : ℝ) ≤ 27)).trans_eq (by ring)
  have hlarge : vaughanPrimitiveMeanAbelEnvelope x (R : ℝ) Q *
      vaughanPrimitiveMeanEquationOneTwoLogPower x ≤ 62 * S := by
    rw [meanLogPower_eq_ninth_sqrtLog]
    have hh := mul_le_mul_of_nonneg_right
      (vaughanEnvelope_power_level (R := (R : ℝ)) (Q := (Q : ℝ)) hx
        (by exact_mod_cast hR) (by exact_mod_cast hRQ) hQ) (pow_nonneg hu 9)
    change vaughanPrimitiveMeanAbelEnvelope x (R : ℝ) Q * u ^ 9 ≤ _
    nlinarith
  have hweighted := mul_le_mul_of_nonneg_left hlarge hL
  unfold averagedErrorEnvelope
  change _ ≤ (4 + 4 * C + 62 * L) * S
  nlinarith

end Erdos4.FGKMT
