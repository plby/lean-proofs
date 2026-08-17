import ErdosProblems.Erdos54.RoughNumbers

/-!
# Integral parameters for the cyclic growth estimate

This file isolates the rounding and large-scale estimates used when CFP's
cyclic subset-sum argument is applied with a sample of length
`ceil (6 * log x)`.  The secondary and reciprocal scales are natural-number
quantities, so the finite counting argument does not have to manipulate real
quotients.
-/

open Filter

namespace Erdos54

/-- The rounded logarithmic scale used in the bad-step argument. -/
noncomputable def cyclicLogScale (x : ℕ) : ℕ :=
  Nat.ceil (Real.log (x : ℝ))

/-- A binary logarithm controlling the medium-growth phase. -/
noncomputable def cyclicSecondaryScale (x : ℕ) : ℕ :=
  roughMertensConstant * (Nat.log 2 (cyclicLogScale x) + 1)

/-- The reciprocal growth scale used for the almost-period threshold. -/
noncomputable def cyclicReciprocalScale (x : ℕ) : ℕ :=
  cyclicLogScale x / (8 * cyclicSecondaryScale x)

/-- The ordered sample length in CFP Lemma 3.1. -/
noncomputable def cyclicTupleLength (x : ℕ) : ℕ :=
  Nat.ceil (6 * Real.log (x : ℝ))

@[simp] theorem cyclicSecondaryScale_pos (x : ℕ) :
    0 < cyclicSecondaryScale x := by
  exact Nat.mul_pos roughMertensConstant_pos (by omega)

theorem cyclicLogScale_pos {x : ℕ} (hx : 2 ≤ x) :
    0 < cyclicLogScale x := by
  apply Nat.ceil_pos.mpr
  exact Real.log_pos (by exact_mod_cast hx)

theorem cyclicLogScale_le_three_pow {x : ℕ} (hx : 1 ≤ x) :
    x ≤ 3 ^ cyclicLogScale x := by
  have hxpos : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
  have hlog : Real.log (x : ℝ) ≤ cyclicLogScale x := Nat.le_ceil _
  have hexp : (x : ℝ) ≤ Real.exp (cyclicLogScale x : ℝ) := by
    rw [← Real.exp_log hxpos]
    exact Real.exp_le_exp.mpr hlog
  have hpow : Real.exp (cyclicLogScale x : ℝ) ≤
      (3 : ℝ) ^ cyclicLogScale x := by
    rw [← Real.exp_one_pow]
    gcongr
    exact Real.exp_one_lt_three.le
  exact_mod_cast hexp.trans hpow

theorem cyclicLogScale_le_two_pow_secondary (x : ℕ) :
    cyclicLogScale x ≤ 2 ^ cyclicSecondaryScale x := by
  have hK : 1 ≤ roughMertensConstant := roughMertensConstant_pos
  have hexp : Nat.log 2 (cyclicLogScale x) + 1 ≤
      cyclicSecondaryScale x := by
    simp only [cyclicSecondaryScale]
    nlinarith
  exact (Nat.lt_pow_succ_log_self Nat.one_lt_two (cyclicLogScale x)).le.trans
    (Nat.pow_le_pow_right (by norm_num) hexp)

theorem cyclicTupleLength_le_six_mul_scale {x : ℕ} (hx : 1 ≤ x) :
    cyclicTupleLength x ≤ 6 * cyclicLogScale x := by
  apply Nat.ceil_le.mpr
  have hlog : Real.log (x : ℝ) ≤ cyclicLogScale x := Nat.le_ceil _
  exact_mod_cast (mul_le_mul_of_nonneg_left hlog (by norm_num : (0 : ℝ) ≤ 6))

theorem five_mul_scale_le_cyclicTupleLength {x : ℕ} (hx : 1 ≤ x)
    (hu : 5 ≤ cyclicLogScale x) :
    5 * cyclicLogScale x ≤ cyclicTupleLength x := by
  have hlog0 : 0 ≤ Real.log (x : ℝ) := Real.log_nonneg (by exact_mod_cast hx)
  have hu_lt : (cyclicLogScale x : ℝ) < Real.log (x : ℝ) + 1 :=
    Nat.ceil_lt_add_one hlog0
  have huR : (5 : ℝ) ≤ cyclicLogScale x := by exact_mod_cast hu
  change 5 * cyclicLogScale x ≤ Nat.ceil (6 * Real.log (x : ℝ))
  rw [show 5 * cyclicLogScale x = (5 * cyclicLogScale x - 1) + 1 by omega,
    Nat.add_one_le_ceil_iff]
  rw [Nat.cast_sub (by omega)]
  push_cast
  nlinarith

/-! ## Explicit natural-number domination estimates -/

private theorem thirtytwo_mul_succ_le_two_pow {s : ℕ} (hs : 64 ≤ s) :
    32 * (s + 1) ≤ 2 ^ s := by
  induction s, hs using Nat.le_induction with
  | base => norm_num
  | succ s hs ih =>
      calc
        32 * (s + 1 + 1) ≤ 2 * (32 * (s + 1)) := by omega
        _ ≤ 2 * 2 ^ s := Nat.mul_le_mul_left 2 ih
        _ = 2 ^ (s + 1) := by ring

private theorem fourth_power_step {t : ℕ} (ht : 64 ≤ t) :
    (t + 2) ^ 4 ≤ 2 * (t + 1) ^ 4 := by
  have hlin : 64 * (t + 2) ≤ 65 * (t + 1) := by omega
  have hp := pow_le_pow_left' hlin 4
  rw [mul_pow, mul_pow] at hp
  have hc : 65 ^ 4 ≤ 2 * 64 ^ 4 := by norm_num
  have hscaled : 64 ^ 4 * (t + 2) ^ 4 ≤
      64 ^ 4 * (2 * (t + 1) ^ 4) := by
    calc
      64 ^ 4 * (t + 2) ^ 4 ≤ 65 ^ 4 * (t + 1) ^ 4 := hp
      _ ≤ (2 * 64 ^ 4) * (t + 1) ^ 4 :=
        Nat.mul_le_mul_right ((t + 1) ^ 4) hc
      _ = 64 ^ 4 * (2 * (t + 1) ^ 4) := by ring
  exact Nat.le_of_mul_le_mul_left hscaled (by positivity)

private theorem thirtyfour_pow_mul_fourth_le_two_pow {s : ℕ} (hs : 64 ≤ s) :
    2 ^ 34 * (s + 1) ^ 4 ≤ 2 ^ s := by
  induction s, hs using Nat.le_induction with
  | base => norm_num
  | succ s hs ih =>
      calc
        2 ^ 34 * (s + 1 + 1) ^ 4 ≤
            2 ^ 34 * (2 * (s + 1) ^ 4) :=
          Nat.mul_le_mul_left _ (fourth_power_step hs)
        _ = 2 * (2 ^ 34 * (s + 1) ^ 4) := by ring
        _ ≤ 2 * 2 ^ s := Nat.mul_le_mul_left 2 ih
        _ = 2 ^ (s + 1) := by ring

private theorem scaled_log_domination {K t : ℕ}
    (ht : max 136 (8 * K) ≤ t) :
    16 * (K * (t + 1)) ≤ 2 ^ t ∧
      2 ^ 30 * (K * (t + 1)) ^ 4 ≤ 2 ^ t := by
  let s := t / 2
  have h136 : 136 ≤ t := (Nat.le_max_left _ _).trans ht
  have h8K : 8 * K ≤ t := (Nat.le_max_right _ _).trans ht
  have hs : 64 ≤ s := by
    dsimp [s]
    omega
  have hsplit : s + (t - s) = t := by
    dsimp [s]
    omega
  have hsplit' : t - s + s = t := by omega
  have htadd : t + 1 ≤ 2 * (s + 1) := by
    dsimp [s]
    omega
  have hsdouble : 2 * s ≤ t := by
    dsimp [s]
    omega
  have htdouble : t ≤ 2 * s + 1 := by
    dsimp [s]
    omega
  have h4Kcomp : 4 * K ≤ t - s := by
    apply Nat.le_sub_of_add_le
    omega
  have hK : K ≤ 2 ^ K := K.lt_two_pow_self.le
  have hKexp : K ≤ 2 ^ (t - s) := by
    apply hK.trans
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hKfour : K ^ 4 ≤ 2 ^ (t - s) := by
    calc
      K ^ 4 ≤ (2 ^ K) ^ 4 := pow_le_pow_left' hK 4
      _ = 2 ^ (4 * K) := by rw [← pow_mul, Nat.mul_comm]
      _ ≤ 2 ^ (t - s) := by
        exact Nat.pow_le_pow_right (by norm_num) h4Kcomp
  constructor
  · calc
      16 * (K * (t + 1)) ≤ K * (32 * (s + 1)) := by
        nlinarith
      _ ≤ 2 ^ (t - s) * 2 ^ s :=
        Nat.mul_le_mul hKexp (thirtytwo_mul_succ_le_two_pow hs)
      _ = 2 ^ t := by rw [← pow_add, hsplit']
  · have htadd4 := pow_le_pow_left' htadd 4
    calc
      2 ^ 30 * (K * (t + 1)) ^ 4 ≤
          K ^ 4 * (2 ^ 34 * (s + 1) ^ 4) := by
        rw [mul_pow]
        calc
          2 ^ 30 * (K ^ 4 * (t + 1) ^ 4) ≤
              2 ^ 30 * (K ^ 4 * (2 * (s + 1)) ^ 4) := by gcongr
          _ = K ^ 4 * (2 ^ 34 * (s + 1) ^ 4) := by ring
      _ ≤ 2 ^ (t - s) * 2 ^ s :=
        Nat.mul_le_mul hKfour (thirtyfour_pow_mul_fourth_le_two_pow hs)
      _ = 2 ^ t := by rw [← pow_add, hsplit']

theorem cyclic_scales_large_of_two_pow_le {x : ℕ}
    (hlarge : 2 ^ max 136 (8 * roughMertensConstant) ≤ cyclicLogScale x) :
    16 * cyclicSecondaryScale x ≤ cyclicLogScale x ∧
      2 ^ 30 * cyclicSecondaryScale x ^ 4 ≤ cyclicLogScale x := by
  let u := cyclicLogScale x
  let t := Nat.log 2 u
  have hu0 : u ≠ 0 := by
    have hp : 0 < 2 ^ max 136 (8 * roughMertensConstant) := by positivity
    omega
  have ht : max 136 (8 * roughMertensConstant) ≤ t := by
    exact Nat.le_log_of_pow_le Nat.one_lt_two hlarge
  have htpow : 2 ^ t ≤ u := Nat.pow_log_le_self 2 hu0
  exact ⟨by
      simpa [cyclicSecondaryScale, u, t] using
        (scaled_log_domination ht).1.trans htpow,
    by
      simpa [cyclicSecondaryScale, u, t] using
        (scaled_log_domination ht).2.trans htpow⟩

/-! ## Division and cutoff bookkeeping -/

theorem cyclicReciprocalScale_bounds {x : ℕ}
    (hlarge : 16 * cyclicSecondaryScale x ≤ cyclicLogScale x) :
    2 ≤ cyclicReciprocalScale x ∧
      cyclicReciprocalScale x ≤ cyclicLogScale x ∧
      cyclicReciprocalScale x * cyclicSecondaryScale x ≤ cyclicLogScale x ∧
      cyclicLogScale x ≤
        16 * cyclicSecondaryScale x * cyclicReciprocalScale x := by
  let u := cyclicLogScale x
  let v := cyclicSecondaryScale x
  let R := cyclicReciprocalScale x
  have hv : 0 < v := cyclicSecondaryScale_pos x
  have hd : 0 < 8 * v := by positivity
  have hR : R = u / (8 * v) := rfl
  have hRtwo : 2 ≤ R := by
    rw [hR]
    apply (Nat.le_div_iff_mul_le hd).2
    calc
      2 * (8 * v) = 16 * v := by ring
      _ ≤ u := by simpa [u, v] using hlarge
  have hdivmul : (u / (8 * v)) * (8 * v) ≤ u := Nat.div_mul_le_self _ _
  have hRv : R * v ≤ u := by
    rw [hR]
    calc
      (u / (8 * v)) * v ≤ (u / (8 * v)) * (8 * v) := by gcongr; omega
      _ ≤ u := hdivmul
  have hRle : R ≤ u := by
    rw [hR]
    exact Nat.div_le_self _ _
  have hrem : u % (8 * v) + (8 * v) * (u / (8 * v)) = u :=
    Nat.mod_add_div u (8 * v)
  have hrem_lt : u % (8 * v) < 8 * v := Nat.mod_lt _ hd
  have hule : u ≤ 16 * v * R := by
    rw [hR]
    have hone : 1 ≤ u / (8 * v) := by omega
    nlinarith [Nat.mul_le_mul_left (8 * v) hone]
  exact ⟨hRtwo, hRle, hRv, by simpa [u, v, R] using hule⟩

theorem cyclicReciprocalScale_le_roughCutoff {x : ℕ} (hx : 2 ≤ x)
    (hlarge : 2 ^ 64 ≤ cyclicLogScale x) :
    cyclicReciprocalScale x ≤ roughCutoff x := by
  let u := cyclicLogScale x
  let v := cyclicSecondaryScale x
  let R := cyclicReciprocalScale x
  have hv : 0 < v := cyclicSecondaryScale_pos x
  have hd : 0 < 8 * v := by positivity
  have hmul : (8 * v) * R ≤ u := by
    simpa [R, u, v, cyclicReciprocalScale, Nat.mul_comm] using
      (Nat.div_mul_le_self u (8 * v))
  have h8R : 8 * R ≤ u := by
    calc
      8 * R ≤ (8 * v) * R := by gcongr; omega
      _ ≤ u := hmul
  have hlog0 : 0 ≤ Real.log (x : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ x by omega))
  have hu_lt : (u : ℝ) < Real.log (x : ℝ) + 1 :=
    Nat.ceil_lt_add_one hlog0
  have huR : (2 ^ 64 : ℕ) ≤ u := hlarge
  have hlogone : (1 : ℝ) ≤ Real.log (x : ℝ) := by
    have : (2 ^ 64 : ℝ) ≤ u := by exact_mod_cast huR
    nlinarith
  apply Nat.le_floor
  change (R : ℝ) ≤ Real.log (x : ℝ) / 2
  have h8RR : (8 : ℝ) * R ≤ u := by exact_mod_cast h8R
  nlinarith

/-! ## Converting the rough-number density estimate -/

theorem roughNumbers_card_parameter_lower {x : ℕ} (hx : 2 ≤ x)
    (hloglog : 0 < Real.log (Real.log (x : ℝ)))
    (hrough : (x : ℝ) /
        (2 * roughMertensConstant * Real.log (Real.log (x : ℝ))) ≤
      (roughNumbers x).card) :
    x ≤ 16 * cyclicSecondaryScale x * (roughNumbers x).card := by
  let u := cyclicLogScale x
  let v := cyclicSecondaryScale x
  let t := Nat.log 2 u + 1
  let K := roughMertensConstant
  have hu : 0 < u := cyclicLogScale_pos hx
  have hv : 0 < v := cyclicSecondaryScale_pos x
  have hK : 0 < K := roughMertensConstant_pos
  have hlog_le_u : Real.log (x : ℝ) ≤ (u : ℝ) := Nat.le_ceil _
  have hlogxpos : 0 < Real.log (x : ℝ) := Real.log_pos (by exact_mod_cast hx)
  have hloglog_le_logu : Real.log (Real.log (x : ℝ)) ≤ Real.log (u : ℝ) :=
    Real.log_le_log hlogxpos hlog_le_u
  have hu_lt : u < 2 ^ t := by
    simpa [u, t] using
      Nat.lt_pow_succ_log_self Nat.one_lt_two u
  have hlogu_lt : Real.log (u : ℝ) < (t : ℝ) := by
    have hcast : (u : ℝ) < ((2 : ℕ) ^ t : ℕ) := by exact_mod_cast hu_lt
    have h := Real.log_lt_log (by exact_mod_cast hu) hcast
    rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow] at h
    have hlog2 : Real.log (2 : ℝ) ≤ 1 := by
      nlinarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
    have htR : (0 : ℝ) ≤ t := by positivity
    nlinarith
  have hloglog_le_t : Real.log (Real.log (x : ℝ)) ≤ (t : ℝ) :=
    hloglog_le_logu.trans hlogu_lt.le
  have hden_le :
      2 * (K : ℝ) * Real.log (Real.log (x : ℝ)) ≤ (16 * v : ℕ) := by
    have hKt : (2 : ℝ) * K * Real.log (Real.log (x : ℝ)) ≤
        2 * K * t := by
      exact mul_le_mul_of_nonneg_left hloglog_le_t (by positivity)
    have hvKt : v = K * t := by
      simp [v, K, t, u, cyclicSecondaryScale]
    calc
      2 * (K : ℝ) * Real.log (Real.log (x : ℝ)) ≤
          2 * K * t := hKt
      _ ≤ 16 * (K * t : ℕ) := by
        push_cast
        nlinarith [mul_nonneg (show (0 : ℝ) ≤ K by positivity)
          (show (0 : ℝ) ≤ t by positivity)]
      _ = (16 * v : ℕ) := by norm_cast
  have hdenpos :
      0 < 2 * (K : ℝ) * Real.log (Real.log (x : ℝ)) := by positivity
  have hxreal : (x : ℝ) ≤
      (16 * v * (roughNumbers x).card : ℕ) := by
    push_cast
    calc
      (x : ℝ) ≤ (roughNumbers x).card *
          (2 * K * Real.log (Real.log (x : ℝ))) :=
        (div_le_iff₀ hdenpos).mp hrough
      _ ≤ (roughNumbers x).card * (16 * v) := by
        have hden_le' : 2 * (K : ℝ) * Real.log (Real.log (x : ℝ)) ≤
            16 * (v : ℝ) := by exact_mod_cast hden_le
        exact mul_le_mul_of_nonneg_left hden_le' (by positivity)
      _ = 16 * v * (roughNumbers x).card := by ring
  exact_mod_cast hxreal

/-! ## The eventual bundle consumed by the finite cyclic theorem -/

/-- All rounded, density, and reciprocal-scale inequalities required by the
finite cyclic-growth and tail-counting arguments. -/
structure CyclicGrowthParameterBounds (x : ℕ) : Prop where
  two_le_x : 2 ≤ x
  logScale_pos : 0 < cyclicLogScale x
  secondaryScale_pos : 0 < cyclicSecondaryScale x
  reciprocalScale_two_le : 2 ≤ cyclicReciprocalScale x
  reciprocalScale_le_logScale : cyclicReciprocalScale x ≤ cyclicLogScale x
  reciprocalScale_le_cutoff : cyclicReciprocalScale x ≤ roughCutoff x
  scale_le_three_pow : x ≤ 3 ^ cyclicLogScale x
  scale_le_two_pow_secondary : cyclicLogScale x ≤ 2 ^ cyclicSecondaryScale x
  reciprocal_mul_secondary_le :
    cyclicReciprocalScale x * cyclicSecondaryScale x ≤ cyclicLogScale x
  five_scale_le_tupleLength : 5 * cyclicLogScale x ≤ cyclicTupleLength x
  tupleLength_le_six_scale : cyclicTupleLength x ≤ 6 * cyclicLogScale x
  scale_le_sixteen_mul : cyclicLogScale x ≤
    16 * cyclicSecondaryScale x * cyclicReciprocalScale x
  rough_card_lower : x ≤
    16 * cyclicSecondaryScale x * (roughNumbers x).card
  secondary_fourth_le :
    2 ^ 30 * cyclicSecondaryScale x ^ 4 ≤ cyclicLogScale x

theorem tendsto_cyclicLogScale :
    Tendsto cyclicLogScale atTop atTop := by
  change Tendsto
    ((fun r : ℝ ↦ Nat.ceil r) ∘ (fun x : ℕ ↦ Real.log (x : ℝ))) atTop atTop
  exact tendsto_nat_ceil_atTop.comp tendsto_log_coe_at_top

theorem eventually_cyclicGrowthParameterBounds :
    ∀ᶠ x : ℕ in atTop, CyclicGrowthParameterBounds x := by
  filter_upwards [eventually_ge_atTop 2,
    tendsto_cyclicLogScale.eventually
      (eventually_ge_atTop (2 ^ max 136 (8 * roughMertensConstant))),
    eventually_roughNumbers_card_lower,
    (Real.tendsto_log_atTop.comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).eventually
        (eventually_gt_atTop (0 : ℝ))]
      with x hx hlarge hrough hloglog
  have hscales := cyclic_scales_large_of_two_pow_le hlarge
  have h64 : 2 ^ 64 ≤ cyclicLogScale x := by
    apply (Nat.pow_le_pow_right (by norm_num)
      (show 64 ≤ max 136 (8 * roughMertensConstant) by omega)).trans
    exact hlarge
  have hrecip := cyclicReciprocalScale_bounds hscales.1
  refine
    { two_le_x := hx
      logScale_pos := cyclicLogScale_pos hx
      secondaryScale_pos := cyclicSecondaryScale_pos x
      reciprocalScale_two_le := hrecip.1
      reciprocalScale_le_logScale := hrecip.2.1
      reciprocalScale_le_cutoff :=
        cyclicReciprocalScale_le_roughCutoff hx h64
      scale_le_three_pow := cyclicLogScale_le_three_pow (by omega)
      scale_le_two_pow_secondary := cyclicLogScale_le_two_pow_secondary x
      reciprocal_mul_secondary_le := hrecip.2.2.1
      five_scale_le_tupleLength :=
        five_mul_scale_le_cyclicTupleLength (by omega) (by omega)
      tupleLength_le_six_scale := cyclicTupleLength_le_six_mul_scale (by omega)
      scale_le_sixteen_mul := hrecip.2.2.2
      rough_card_lower := roughNumbers_card_parameter_lower hx hloglog hrough
      secondary_fourth_le := hscales.2 }

/-! ## Collision supply for the robust-block sampling -/

private theorem cube_step {u : ℕ} (hu : 64 ≤ u) :
    (u + 1) ^ 3 ≤ 2 * u ^ 3 := by
  have hlin : 64 * (u + 1) ≤ 65 * u := by omega
  have hp := pow_le_pow_left' hlin 3
  rw [mul_pow, mul_pow] at hp
  have hc : 65 ^ 3 ≤ 2 * 64 ^ 3 := by norm_num
  have hscaled : 64 ^ 3 * (u + 1) ^ 3 ≤
      64 ^ 3 * (2 * u ^ 3) := by
    calc
      64 ^ 3 * (u + 1) ^ 3 ≤ 65 ^ 3 * u ^ 3 := hp
      _ ≤ (2 * 64 ^ 3) * u ^ 3 := Nat.mul_le_mul_right _ hc
      _ = 64 ^ 3 * (2 * u ^ 3) := by ring
  exact Nat.le_of_mul_le_mul_left hscaled (by positivity)

private theorem two_pow_mul_cube_le_two_pow {u : ℕ} (hu : 64 ≤ u) :
    2 ^ 32 * u ^ 3 ≤ 2 ^ u := by
  induction u, hu using Nat.le_induction with
  | base => norm_num
  | succ u hu ih =>
      calc
        2 ^ 32 * (u + 1) ^ 3 ≤ 2 ^ 32 * (2 * u ^ 3) :=
          Nat.mul_le_mul_left _ (cube_step hu)
        _ = 2 * (2 ^ 32 * u ^ 3) := by ring
        _ ≤ 2 * 2 ^ u := Nat.mul_le_mul_left 2 ih
        _ = 2 ^ (u + 1) := by ring

private theorem two_pow_pred_logScale_lt {x : ℕ} (hx : 2 ≤ x) :
    2 ^ (cyclicLogScale x - 1) < x := by
  let u := cyclicLogScale x
  have hu : 0 < u := cyclicLogScale_pos hx
  have hlog0 : 0 ≤ Real.log (x : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ x by omega))
  have hu_lt : (u : ℝ) < Real.log (x : ℝ) + 1 :=
    Nat.ceil_lt_add_one hlog0
  have hpredlog : ((u - 1 : ℕ) : ℝ) < Real.log (x : ℝ) := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    nlinarith
  have hpowexp : ((2 ^ (u - 1) : ℕ) : ℝ) ≤ Real.exp (u - 1 : ℕ) := by
    push_cast
    rw [← Real.exp_one_pow]
    gcongr
    exact Real.exp_one_gt_two.le
  have hexplog : Real.exp (u - 1 : ℕ) < (x : ℝ) := by
    have hxpos : (0 : ℝ) < x := by
      exact_mod_cast (show 0 < x by omega)
    calc
      Real.exp (u - 1 : ℕ) < Real.exp (Real.log (x : ℝ)) :=
        Real.exp_lt_exp.mpr hpredlog
      _ = x := Real.exp_log hxpos
  exact_mod_cast hpowexp.trans_lt hexplog

theorem cyclic_collision_supply_of_bounds {x : ℕ}
    (h : CyclicGrowthParameterBounds x)
    (hlarge : 64 ≤ cyclicLogScale x) :
    2 * (1280 * cyclicTupleLength x) ^ 2 < (roughNumbers x).card := by
  let u := cyclicLogScale x
  let v := cyclicSecondaryScale x
  let q := cyclicTupleLength x
  let M := (roughNumbers x).card
  let T := 2 * (1280 * q) ^ 2
  have hu : 0 < u := h.logScale_pos
  have hvle : v ≤ u := by
    have hv : 1 ≤ v := h.secondaryScale_pos
    have hvfour : v ≤ v ^ 4 := by
      simpa only [pow_one] using
        (pow_le_pow_right' hv (show 1 ≤ 4 by omega))
    calc
      v ≤ v ^ 4 := hvfour
      _ ≤ 2 ^ 30 * v ^ 4 := by
        have hcoef : 1 ≤ 2 ^ 30 := by norm_num
        nlinarith
      _ ≤ u := by simpa [u, v] using h.secondary_fourth_le
  have hq : q ≤ 6 * u := h.tupleLength_le_six_scale
  have hT : T ≤ 2 ^ 27 * u ^ 2 := by
    have hmul : 1280 * q ≤ 7680 * u := by
      calc
        1280 * q ≤ 1280 * (6 * u) := Nat.mul_le_mul_left 1280 hq
        _ = 7680 * u := by ring
    have hsq := pow_le_pow_left' hmul 2
    dsimp [T]
    calc
      2 * (1280 * q) ^ 2 ≤ 2 * (7680 * u) ^ 2 := Nat.mul_le_mul_left 2 hsq
      _ ≤ 2 ^ 27 * u ^ 2 := by
        rw [mul_pow]
        have : 2 * 7680 ^ 2 ≤ 2 ^ 27 := by norm_num
        calc
          2 * (7680 ^ 2 * u ^ 2) = (2 * 7680 ^ 2) * u ^ 2 := by ring
          _ ≤ 2 ^ 27 * u ^ 2 := Nat.mul_le_mul_right (u ^ 2) this
  have hpoly : 16 * v * T ≤ 2 ^ 31 * u ^ 3 := by
    calc
      16 * v * T ≤ 16 * u * (2 ^ 27 * u ^ 2) := by gcongr
      _ = 2 ^ 31 * u ^ 3 := by ring
  have hpow := two_pow_mul_cube_le_two_pow hlarge
  have hpred : 2 ^ 31 * u ^ 3 ≤ 2 ^ (u - 1) := by
    have huone : 1 ≤ u := hu
    have hpow_eq : 2 ^ u = 2 * 2 ^ (u - 1) := by
      calc
        2 ^ u = 2 ^ ((u - 1) + 1) := by congr 2 <;> omega
        _ = 2 * 2 ^ (u - 1) := by rw [pow_succ]; ring
    have hscaled : 2 * (2 ^ 31 * u ^ 3) ≤ 2 * 2 ^ (u - 1) := by
      calc
        2 * (2 ^ 31 * u ^ 3) = 2 ^ 32 * u ^ 3 := by ring
        _ ≤ 2 ^ u := hpow
        _ = 2 * 2 ^ (u - 1) := hpow_eq
    exact Nat.le_of_mul_le_mul_left hscaled (by omega)
  have hfactorT : 16 * v * T < x :=
    (hpoly.trans hpred).trans_lt (by
      simpa [u] using two_pow_pred_logScale_lt h.two_le_x)
  have hTM : T < M := by
    by_contra hnot
    have hMT : M ≤ T := Nat.le_of_not_gt hnot
    have hfac : 16 * v * M ≤ 16 * v * T := Nat.mul_le_mul_left _ hMT
    have hxM : x ≤ 16 * v * M := by simpa [v, M] using h.rough_card_lower
    omega
  simpa [T, M] using hTM

theorem eventually_cyclic_collision_supply :
    ∀ᶠ x : ℕ in atTop,
      2 * (1280 * cyclicTupleLength x) ^ 2 < (roughNumbers x).card := by
  filter_upwards [eventually_cyclicGrowthParameterBounds,
    tendsto_cyclicLogScale.eventually (eventually_ge_atTop 64)] with x h hlarge
  exact cyclic_collision_supply_of_bounds h hlarge

/-- The fixed small-prime obstruction used after modular growth is absent at
all sufficiently large scales. -/
theorem eventually_seventeen_le_roughCutoff :
    ∀ᶠ x : ℕ in atTop, 17 ≤ roughCutoff x := by
  filter_upwards
    [tendsto_log_coe_at_top.eventually (eventually_ge_atTop (34 : ℝ))]
      with x hx
  apply Nat.le_floor
  dsimp [roughCutoff]
  linarith

end Erdos54
