/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos285.Analytic
import ErdosProblems.Erdos285.Proposition6Asymptotic

/-!
# Erdős 285: exact-cardinality scale selection

This file isolates the ``last scale below the requested cardinality'' argument.
No monotonicity of the source count is assumed.  The only local input is an
upper bound for a positive one-step jump.  This is useful for converting a
density theorem for a finite source block into an exact-cardinality theorem.

The final section also records the slowly varying surplus parameter used in
the alternative variable-endpoint implementation of Proposition 4.
-/

namespace Erdos285.LastCrossing

open Filter Finset Real Asymptotics
open scoped Topology

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ## The last admissible scale -/

/-- Scales no larger than `M t` whose source count has not yet exceeded `t`. -/
def admissibleScales (s M : ℕ → ℕ) (t : ℕ) : Finset ℕ :=
  (range (M t + 1)).filter fun x ↦ s x ≤ t

lemma zero_mem_admissibleScales {s M : ℕ → ℕ} (hs0 : s 0 = 0) (t : ℕ) :
    0 ∈ admissibleScales s M t := by
  simp [admissibleScales, hs0]

/-- The largest admissible scale.  The harmless value `0` is used only when
    the admissible set is empty; all applications have `s 0 = 0`. -/
def lastBelow (s M : ℕ → ℕ) (t : ℕ) : ℕ :=
  if h : (admissibleScales s M t).Nonempty then
    (admissibleScales s M t).max' h
  else 0

lemma lastBelow_mem {s M : ℕ → ℕ} (hs0 : s 0 = 0) (t : ℕ) :
    lastBelow s M t ∈ admissibleScales s M t := by
  rw [lastBelow]
  split_ifs with h
  · exact Finset.max'_mem _ h
  · exact (h ⟨0, zero_mem_admissibleScales hs0 t⟩).elim

lemma lastBelow_le_cap {s M : ℕ → ℕ} (hs0 : s 0 = 0) (t : ℕ) :
    lastBelow s M t ≤ M t := by
  have h := lastBelow_mem (s := s) (M := M) hs0 t
  simp only [admissibleScales, mem_filter, mem_range] at h
  omega

lemma sourceCount_lastBelow_le {s M : ℕ → ℕ} (hs0 : s 0 = 0) (t : ℕ) :
    s (lastBelow s M t) ≤ t := by
  have h := lastBelow_mem (s := s) (M := M) hs0 t
  exact (by simpa [admissibleScales] using h :
    lastBelow s M t ≤ M t ∧ s (lastBelow s M t) ≤ t).2

/-- Maximality, phrased without a monotonicity assumption on `s`. -/
lemma le_lastBelow_of_le_cap_of_sourceCount_le {s M : ℕ → ℕ}
    {t y : ℕ} (hyM : y ≤ M t) (hys : s y ≤ t) :
    y ≤ lastBelow s M t := by
  have hy : y ∈ admissibleScales s M t := by
    simp only [admissibleScales, mem_filter, mem_range]
    exact ⟨by omega, hys⟩
  rw [lastBelow]
  split_ifs with h
  · exact Finset.le_max' _ _ hy
  · exact (h ⟨y, hy⟩).elim

lemma lastBelow_lt_cap_of_sourceCount_cap_gt {s M : ℕ → ℕ}
    (hs0 : s 0 = 0) {t : ℕ} (hcap : t < s (M t)) :
    lastBelow s M t < M t := by
  have hle := lastBelow_le_cap (s := s) (M := M) hs0 t
  exact hle.lt_of_ne fun h ↦ by
    have hsle := sourceCount_lastBelow_le (s := s) (M := M) hs0 t
    rw [h] at hsle
    exact (not_lt_of_ge hsle) hcap

lemma sourceCount_succ_lastBelow_gt {s M : ℕ → ℕ}
    (hs0 : s 0 = 0) {t : ℕ} (hcap : t < s (M t)) :
    t < s (lastBelow s M t + 1) := by
  have hlt := lastBelow_lt_cap_of_sourceCount_cap_gt (s := s) (M := M) hs0 hcap
  by_contra h
  have hs : s (lastBelow s M t + 1) ≤ t := Nat.le_of_not_gt h
  have hmax := le_lastBelow_of_le_cap_of_sourceCount_le (s := s) (M := M)
    (show lastBelow s M t + 1 ≤ M t by omega) hs
  omega

/-- A one-step upper-jump estimate bounds the exact-cardinality deficit at
the last admissible scale. -/
lemma deficit_lastBelow_le_jump {s M J : ℕ → ℕ}
    (hs0 : s 0 = 0)
    (hjump : ∀ x, s (x + 1) ≤ s x + J x)
    {t : ℕ} (hcap : t < s (M t)) :
    t - s (lastBelow s M t) ≤ J (lastBelow s M t) := by
  have hcross := sourceCount_succ_lastBelow_gt (s := s) (M := M) hs0 hcap
  have hj := hjump (lastBelow s M t)
  omega

/-! ## Asymptotic inversion -/

lemma cap_tendsto_atTop_of_ratio
    {M : ℕ → ℕ} {c : ℝ} (hc : 0 < c)
    (hM : Tendsto (fun t : ℕ ↦ (M t : ℝ) / (t : ℝ)) atTop (nhds c)) :
    Tendsto M atTop atTop := by
  have hprod : Tendsto
      (fun t : ℕ ↦ (t : ℝ) * ((M t : ℝ) / (t : ℝ))) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_mul_pos hc hM
  have hcast : Tendsto (fun t : ℕ ↦ (M t : ℝ)) atTop atTop := by
    apply hprod.congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with t ht
    field_simp
  exact tendsto_natCast_atTop_iff.mp hcast

lemma lastBelow_tendsto_atTop {s M : ℕ → ℕ}
    (_hs0 : s 0 = 0) (hM : Tendsto M atTop atTop) :
    Tendsto (lastBelow s M) atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro y
  obtain ⟨a, ha⟩ := (tendsto_atTop_atTop.mp hM) y
  refine ⟨max a (s y), fun t ht ↦ ?_⟩
  apply le_lastBelow_of_le_cap_of_sourceCount_le
  · exact ha t (le_trans (le_max_left _ _) ht)
  · exact le_trans (le_max_right _ _) ht

lemma eventually_deficit_lastBelow_le_jump {s M J : ℕ → ℕ}
    (hs0 : s 0 = 0) (hM : Tendsto M atTop atTop)
    (hcross : ∀ᶠ t in atTop, t < s (M t))
    (hjump : ∀ᶠ x in atTop, s (x + 1) ≤ s x + J x) :
    ∀ᶠ t in atTop, t - s (lastBelow s M t) ≤ J (lastBelow s M t) := by
  have hxtop := lastBelow_tendsto_atTop (s := s) (M := M) hs0 hM
  have hjumpx : ∀ᶠ t in atTop,
      s (lastBelow s M t + 1) ≤
        s (lastBelow s M t) + J (lastBelow s M t) := hxtop.eventually hjump
  filter_upwards [hcross, hjumpx] with t hcap hj
  have hnext := sourceCount_succ_lastBelow_gt (s := s) (M := M) hs0 hcap
  omega

/-! A canonical cap when no explicit quantitative cap is convenient. -/

/-- The least scale at which `s` exceeds `t`. -/
def firstAbove (s : ℕ → ℕ) (hunbounded : ∀ t, ∃ x, t < s x) (t : ℕ) : ℕ :=
  Nat.find (hunbounded t)

lemma firstAbove_spec {s : ℕ → ℕ} {hunbounded : ∀ t, ∃ x, t < s x} (t : ℕ) :
    t < s (firstAbove s hunbounded t) :=
  Nat.find_spec (hunbounded t)

/-- The first crossing escapes every finite prefix. -/
lemma firstAbove_tendsto_atTop {s : ℕ → ℕ} (hunbounded : ∀ t, ∃ x, t < s x) :
    Tendsto (firstAbove s hunbounded) atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro y
  let B : ℕ := ∑ i ∈ range (y + 1), s i
  refine ⟨B, fun t ht ↦ ?_⟩
  by_contra hnot
  have hMle : firstAbove s hunbounded t ≤ y := Nat.le_of_not_ge hnot
  have hmem : firstAbove s hunbounded t ∈ range (y + 1) := by simpa using hMle
  have hsingle : s (firstAbove s hunbounded t) ≤ B := by
    dsimp [B]
    exact Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) hmem
  have hcross := firstAbove_spec (s := s) (hunbounded := hunbounded) t
  omega

/-- Generic nonmonotone inversion theorem with an arbitrary cap tending to
infinity.  The crossing is kept explicit because this is the most convenient
finite interface for applications. -/
theorem lastBelow_ratio_tendsto_of_cap_tendsto
    {s M J : ℕ → ℕ} {d : ℝ}
    (hs0 : s 0 = 0) (hd : 0 < d) (hMtop : Tendsto M atTop atTop)
    (hs : Tendsto (fun x : ℕ ↦ (s x : ℝ) / (x : ℝ)) atTop (nhds d))
    (hcross : ∀ᶠ t in atTop, t < s (M t))
    (hjump : ∀ᶠ x in atTop, s (x + 1) ≤ s x + J x)
    (hJ : (fun x : ℕ ↦ (J x : ℝ)) =o[atTop] (fun x : ℕ ↦ (x : ℝ))) :
    Tendsto (fun t : ℕ ↦ (lastBelow s M t : ℝ) / (t : ℝ))
      atTop (nhds d⁻¹) := by
  have hxtop : Tendsto (lastBelow s M) atTop atTop := lastBelow_tendsto_atTop hs0 hMtop
  have hsx : Tendsto
      (fun t : ℕ ↦ (s (lastBelow s M t) : ℝ) / (lastBelow s M t : ℝ))
      atTop (nhds d) := hs.comp hxtop
  have hJratio : Tendsto (fun x : ℕ ↦ (J x : ℝ) / (x : ℝ))
      atTop (nhds 0) := hJ.tendsto_div_nhds_zero
  have hJx := hJratio.comp hxtop
  have hsum : Tendsto
      (fun t : ℕ ↦
        (s (lastBelow s M t) : ℝ) / (lastBelow s M t : ℝ) +
          (J (lastBelow s M t) : ℝ) / (lastBelow s M t : ℝ))
      atTop (nhds d) := by simpa using hsx.add hJx
  have hlower := hsum.inv₀ hd.ne'
  have hupper := hsx.inv₀ hd.ne'
  have hjumpx : ∀ᶠ t in atTop,
      s (lastBelow s M t + 1) ≤
        s (lastBelow s M t) + J (lastBelow s M t) := hxtop.eventually hjump
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hupper
  · filter_upwards [hcross, hxtop.eventually (eventually_ge_atTop 1),
      eventually_ge_atTop 1, hjumpx] with t hcap hx ht hj
    have hstep := sourceCount_succ_lastBelow_gt (s := s) (M := M) hs0 hcap
    have hxR : (0 : ℝ) < lastBelow s M t := by exact_mod_cast hx
    have htR : (0 : ℝ) < t := by exact_mod_cast ht
    have hreal : (t : ℝ) < (s (lastBelow s M t) : ℝ) + J (lastBelow s M t) := by
      exact_mod_cast hstep.trans_le hj
    rw [show (s (lastBelow s M t) : ℝ) / (lastBelow s M t : ℝ) +
        (J (lastBelow s M t) : ℝ) / (lastBelow s M t : ℝ) =
        ((s (lastBelow s M t) : ℝ) + J (lastBelow s M t)) /
          (lastBelow s M t : ℝ) by ring, inv_div]
    exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) htR hreal.le
  · filter_upwards [hxtop.eventually (eventually_ge_atTop 1),
      eventually_ge_atTop 1, hsx.eventually (Ioi_mem_nhds (show d / 2 < d by linarith))]
      with t hx ht hspos
    have hsle := sourceCount_lastBelow_le (s := s) (M := M) hs0 t
    have hxR : (0 : ℝ) < lastBelow s M t := by exact_mod_cast hx
    have htR : (0 : ℝ) < t := by exact_mod_cast ht
    have hsR : (0 : ℝ) < s (lastBelow s M t) := by
      have hratioPos : 0 < (s (lastBelow s M t) : ℝ) /
          (lastBelow s M t : ℝ) := (show 0 < d / 2 by positivity).trans hspos
      rcases div_pos_iff.mp hratioPos with h | h
      · exact h.1
      · exact (not_lt_of_ge hxR.le h.2).elim
    rw [inv_div]
    exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) hsR (by exact_mod_cast hsle)

/-- Ratio-form wrapper for an explicitly scaled cap. -/
theorem lastBelow_ratio_tendsto
    {s M J : ℕ → ℕ} {d c : ℝ}
    (hs0 : s 0 = 0) (hd : 0 < d) (hc : 0 < c)
    (hs : Tendsto (fun x : ℕ ↦ (s x : ℝ) / (x : ℝ)) atTop (nhds d))
    (hM : Tendsto (fun t : ℕ ↦ (M t : ℝ) / (t : ℝ)) atTop (nhds c))
    (hcross : ∀ᶠ t in atTop, t < s (M t))
    (hjump : ∀ᶠ x in atTop, s (x + 1) ≤ s x + J x)
    (hJ : (fun x : ℕ ↦ (J x : ℝ)) =o[atTop] (fun x : ℕ ↦ (x : ℝ))) :
    Tendsto (fun t : ℕ ↦ (lastBelow s M t : ℝ) / (t : ℝ))
      atTop (nhds d⁻¹) :=
  lastBelow_ratio_tendsto_of_cap_tendsto hs0 hd
    (cap_tendsto_atTop_of_ratio hc hM) hs hcross hjump hJ

/-- The common formulation in which the cap has a limiting coefficient
strictly larger than the inverse density. -/
theorem lastBelow_ratio_tendsto_of_inv_lt_cap
    {s M J : ℕ → ℕ} {d c : ℝ}
    (hs0 : s 0 = 0) (hd : 0 < d) (hc : d⁻¹ < c)
    (hs : Tendsto (fun x : ℕ ↦ (s x : ℝ) / (x : ℝ)) atTop (nhds d))
    (hM : Tendsto (fun t : ℕ ↦ (M t : ℝ) / (t : ℝ)) atTop (nhds c))
    (hcross : ∀ᶠ t in atTop, t < s (M t))
    (hjump : ∀ᶠ x in atTop, s (x + 1) ≤ s x + J x)
    (hJ : (fun x : ℕ ↦ (J x : ℝ)) =o[atTop] (fun x : ℕ ↦ (x : ℝ))) :
    Tendsto (fun t : ℕ ↦ (lastBelow s M t : ℝ) / (t : ℝ))
      atTop (nhds d⁻¹) :=
  lastBelow_ratio_tendsto hs0 hd ((inv_pos.mpr hd).trans hc) hs hM hcross hjump hJ

/-! ## A slowly varying surplus parameter -/

/-- `1/sqrt(log(t+3))`, shifted so it is positive for every natural input. -/
def surplusDelta (t : ℕ) : ℝ :=
  (Real.log ((t : ℝ) + 3)) ^ (-(1 / 2 : ℝ))

lemma surplusDelta_pos (t : ℕ) : 0 < surplusDelta t := by
  apply Real.rpow_pos_of_pos
  apply Real.log_pos
  have ht : (0 : ℝ) ≤ t := Nat.cast_nonneg t
  linarith

lemma surplusDelta_tendsto_zero : Tendsto surplusDelta atTop (nhds 0) := by
  exact (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp
    (Real.tendsto_log_atTop.comp
      (tendsto_atTop_add_const_right atTop 3 tendsto_natCast_atTop_atTop))

/-- The moving lower endpoint `exp(-1) + delta(t)`. -/
def surplusAlpha (t : ℕ) : ℝ := Real.exp (-1) + surplusDelta t

lemma surplusAlpha_tendsto : Tendsto surplusAlpha atTop (nhds (Real.exp (-1))) := by
  change Tendsto (fun t : ℕ ↦ Real.exp (-1) + surplusDelta t) atTop
    (nhds (Real.exp (-1)))
  simpa using tendsto_const_nhds.add surplusDelta_tendsto_zero

/-- The explicit enlarged endpoint proposed for the source block. -/
def surplusCutoff (t : ℕ) : ℕ :=
  ⌈(Analytic.densityConstant +
      2 * Analytic.densityConstant ^ 2 * surplusDelta t) * (t : ℝ)⌉₊

lemma surplusCutoff_ratio_tendsto :
    Tendsto (fun t : ℕ ↦ (surplusCutoff t : ℝ) / (t : ℝ)) atTop
      (nhds Analytic.densityConstant) := by
  let coefficient : ℕ → ℝ := fun t ↦ Analytic.densityConstant +
    2 * Analytic.densityConstant ^ 2 * surplusDelta t
  have hcoefficient : Tendsto coefficient atTop (nhds Analytic.densityConstant) := by
    simpa [coefficient] using tendsto_const_nhds.add
      (surplusDelta_tendsto_zero.const_mul (2 * Analytic.densityConstant ^ 2))
  have hinv : Tendsto (fun t : ℕ ↦ (t : ℝ)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hupper : Tendsto (fun t : ℕ ↦ coefficient t + (t : ℝ)⁻¹) atTop
      (nhds Analytic.densityConstant) := by simpa using hcoefficient.add hinv
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hcoefficient hupper
  · filter_upwards [eventually_ge_atTop 1] with t ht
    have htR : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
    have hscale0 : 0 ≤ coefficient t * (t : ℝ) := by
      have hc : 0 ≤ coefficient t := by
        dsimp [coefficient]
        exact add_nonneg Analytic.densityConstant_pos.le
          (mul_nonneg (by positivity) (surplusDelta_pos t).le)
      positivity
    rw [surplusCutoff, show Analytic.densityConstant +
        2 * Analytic.densityConstant ^ 2 * surplusDelta t = coefficient t by rfl]
    exact (le_div_iff₀ htR).2 (by
      simpa [mul_comm] using (Nat.le_ceil (coefficient t * (t : ℝ))))
  · filter_upwards [eventually_ge_atTop 1] with t ht
    have htR : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
    have hc : 0 ≤ coefficient t := by
      dsimp [coefficient]
      exact add_nonneg Analytic.densityConstant_pos.le
        (mul_nonneg (by positivity) (surplusDelta_pos t).le)
    have hscale0 : 0 ≤ coefficient t * (t : ℝ) := mul_nonneg hc htR.le
    rw [surplusCutoff, show Analytic.densityConstant +
        2 * Analytic.densityConstant ^ 2 * surplusDelta t = coefficient t by rfl]
    rw [div_le_iff₀ htR]
    have hceil := Nat.ceil_lt_add_one hscale0
    calc
      (⌈coefficient t * (t : ℝ)⌉₊ : ℝ) ≤ coefficient t * (t : ℝ) + 1 := hceil.le
      _ = (coefficient t + (t : ℝ)⁻¹) * (t : ℝ) := by
        field_simp

lemma surplusCutoff_tendsto_atTop : Tendsto surplusCutoff atTop atTop :=
  cap_tendsto_atTop_of_ratio Analytic.densityConstant_pos surplusCutoff_ratio_tendsto

/-! ## One-step control for the logarithmic smoothness cutoff -/

/-- The real scale before rounding in `mainCutoffNat`. -/
def mainCutoffScale (x : ℕ) : ℝ :=
  (x : ℝ) / Real.log (x : ℝ) ^ 30

@[simp] lemma mainCutoffNat_eq_floor_scale (x : ℕ) :
    mainCutoffNat x = ⌊mainCutoffScale x⌋₊ := rfl

/-- Although no global monotonicity is needed, the logarithmic cutoff can
increase by at most one in one step once `log x > 1`. -/
theorem eventually_mainCutoffNat_succ_le :
    ∀ᶠ x : ℕ in atTop, mainCutoffNat (x + 1) ≤ mainCutoffNat x + 1 := by
  filter_upwards [tendsto_log_coe_at_top.eventually (eventually_gt_atTop (1 : ℝ))]
    with x hlog
  have hxR : (0 : ℝ) < x := by
    have hx0 : (0 : ℝ) ≤ x := Nat.cast_nonneg x
    exact zero_lt_one.trans ((Real.log_pos_iff hx0).mp (zero_lt_one.trans hlog))
  have hxsuccR : (0 : ℝ) < (x + 1 : ℕ) := by positivity
  have hlogmono : Real.log (x : ℝ) ≤ Real.log (x + 1 : ℕ) := by
    exact Real.strictMonoOn_log.monotoneOn
      (Set.mem_Ioi.mpr hxR) (Set.mem_Ioi.mpr hxsuccR) (by exact_mod_cast Nat.le_succ x)
  have hpowpos : 0 < Real.log (x : ℝ) ^ 30 := pow_pos (zero_lt_one.trans hlog) _
  have hpowle : Real.log (x : ℝ) ^ 30 ≤ Real.log (x + 1 : ℕ) ^ 30 := by
    exact pow_le_pow_left₀ (zero_lt_one.trans hlog).le hlogmono _
  have hscaleStep : mainCutoffScale (x + 1) < mainCutoffScale x + 1 := by
    calc
      mainCutoffScale (x + 1) ≤ (x + 1 : ℕ) / Real.log (x : ℝ) ^ 30 := by
        dsimp [mainCutoffScale]
        exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) hpowpos hpowle
      _ = mainCutoffScale x + (Real.log (x : ℝ) ^ 30)⁻¹ := by
        dsimp [mainCutoffScale]
        push_cast
        field_simp
      _ < mainCutoffScale x + 1 := by
        gcongr
        exact inv_lt_one_of_one_lt₀ (one_lt_pow₀ hlog (by norm_num))
  rw [mainCutoffNat_eq_floor_scale, mainCutoffNat_eq_floor_scale]
  apply Nat.lt_succ_iff.mp
  have hscale0 : 0 ≤ mainCutoffScale (x + 1) := by
    exact div_nonneg (Nat.cast_nonneg _)
      (pow_nonneg ((zero_lt_one.trans hlog).le.trans hlogmono) _)
  rw [Nat.floor_lt hscale0]
  calc
    mainCutoffScale (x + 1) < mainCutoffScale x + 1 := hscaleStep
    _ < ((⌊mainCutoffScale x⌋₊ + 1 + 1 : ℕ) : ℝ) := by
      push_cast
      linarith [Nat.lt_floor_add_one (mainCutoffScale x)]

/-- A convenient global majorant for the one-step score jump.  The quotient
is the number of multiples of the sole newly allowed cutoff value; the
constant covers the moving endpoints, the new right endpoint, and the
two-term prime-power correction. -/
def logarithmicStepJump (x : ℕ) : ℕ :=
  5 + x / (mainCutoffNat x + 1)

lemma logarithmicStepJump_isLittleO :
    (fun x : ℕ ↦ (logarithmicStepJump x : ℝ))
      =o[atTop] (fun x : ℕ ↦ (x : ℝ)) := by
  have hQtop : Tendsto (fun x : ℕ ↦ mainCutoffNat x + 1) atTop atTop := by
    rw [tendsto_atTop_atTop]
    intro b
    obtain ⟨a, ha⟩ := (tendsto_atTop_atTop.mp mainCutoffNat_spec.2.1) b
    exact ⟨a, fun x hx ↦ (ha x hx).trans (Nat.le_add_right _ _)⟩
  have hinv : Tendsto (fun x : ℕ ↦ ((mainCutoffNat x + 1 : ℕ) : ℝ)⁻¹)
      atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp hQtop)
  have hconst : Tendsto (fun x : ℕ ↦ (5 : ℝ) / (x : ℝ)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hupper := hconst.add hinv
  have hratio : Tendsto
      (fun x : ℕ ↦ (logarithmicStepJump x : ℝ) / (x : ℝ)) atTop (nhds 0) := by
    apply squeeze_zero' (g := fun x : ℕ ↦
      (5 : ℝ) / (x : ℝ) + ((mainCutoffNat x + 1 : ℕ) : ℝ)⁻¹)
    · filter_upwards [eventually_ge_atTop 1] with x hx
      positivity
    · filter_upwards [eventually_ge_atTop 1] with x hx
      have hxR : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
      have hdiv : ((x / (mainCutoffNat x + 1) : ℕ) : ℝ) ≤
          (x : ℝ) / (mainCutoffNat x + 1 : ℕ) := Nat.cast_div_le
      rw [logarithmicStepJump, Nat.cast_add]
      calc
        ((5 : ℝ) + (x / (mainCutoffNat x + 1) : ℕ)) / (x : ℝ) ≤
            ((5 : ℝ) + (x : ℝ) / (mainCutoffNat x + 1 : ℕ)) /
              (x : ℝ) := div_le_div_of_nonneg_right (by linarith) hxR.le
        _ = (5 : ℝ) / (x : ℝ) +
            ((mainCutoffNat x + 1 : ℕ) : ℝ)⁻¹ := by
          have hq : ((mainCutoffNat x + 1 : ℕ) : ℝ) ≠ 0 := by positivity
          field_simp
    · simpa using hupper
  exact (Asymptotics.isLittleO_iff_tendsto' (by
    filter_upwards [eventually_ge_atTop 1] with x hx
    intro hzero
    exact ((show (x : ℝ) ≠ 0 by exact_mod_cast (show x ≠ 0 by omega)) hzero).elim)).2
      hratio

/-- The one-step jump is eventually much smaller than the deletion budget.
This is the quantitative comparison needed before applying the five-prime
reservoir capacity theorem. -/
theorem eventually_logarithmicStepJump_le_deletionBudget :
    ∀ᶠ x : ℕ in atTop, logarithmicStepJump x ≤ proposition6DeletionBudget x := by
  have hscale7 : Tendsto
      (fun x : ℕ ↦ (x : ℝ) / Real.log (x : ℝ) ^ 7) atTop atTop := by
    have h := (UnitFractions.tendsto_mul_add_div_pow_log_at_top
      (1 : ℝ) 0 7 zero_lt_one).comp tendsto_natCast_atTop_atTop
    simpa [Function.comp_def] using h
  have hscale37 : Tendsto
      (fun x : ℕ ↦ (x : ℝ) / Real.log (x : ℝ) ^ 37) atTop atTop := by
    have h := (UnitFractions.tendsto_mul_add_div_pow_log_at_top
      (1 : ℝ) 0 37 zero_lt_one).comp tendsto_natCast_atTop_atTop
    simpa [Function.comp_def] using h
  have hQratio := RoughCounts.logPowerCutoff_ratio_tendsto_one 30
  filter_upwards [tendsto_log_coe_at_top.eventually (eventually_gt_atTop (1 : ℝ)),
    hscale7.eventually (eventually_ge_atTop (1 : ℝ)),
    hscale37.eventually (eventually_ge_atTop (1 : ℝ)),
    hQratio.eventually (Ioi_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1))]
      with x hlog h7 h37 hQratioHalf
  have hxR : (0 : ℝ) < x := by
    have hx0 : (0 : ℝ) ≤ x := Nat.cast_nonneg x
    exact zero_lt_one.trans ((Real.log_pos_iff hx0).mp (zero_lt_one.trans hlog))
  have hlogpos : 0 < Real.log (x : ℝ) := zero_lt_one.trans hlog
  have hpow7 : 0 < Real.log (x : ℝ) ^ 7 := pow_pos hlogpos _
  have hpow30 : 0 < Real.log (x : ℝ) ^ 30 := pow_pos hlogpos _
  have hscalePos : 0 < (x : ℝ) / Real.log (x : ℝ) ^ 30 :=
    div_pos hxR hpow30
  have hQlower : (x : ℝ) / (2 * Real.log (x : ℝ) ^ 30) ≤
      (mainCutoffNat x : ℝ) := by
    have hhalf : (1 / 2 : ℝ) *
        ((x : ℝ) / Real.log (x : ℝ) ^ 30) < mainCutoffNat x := by
      change (1 / 2 : ℝ) < (mainCutoffNat x : ℝ) /
        ((x : ℝ) / Real.log (x : ℝ) ^ 30) at hQratioHalf
      rwa [lt_div_iff₀ hscalePos] at hQratioHalf
    calc
      (x : ℝ) / (2 * Real.log (x : ℝ) ^ 30) =
          (1 / 2 : ℝ) * ((x : ℝ) / Real.log (x : ℝ) ^ 30) := by ring
      _ ≤ (mainCutoffNat x : ℝ) := hhalf.le
  have hquotient : ((x / (mainCutoffNat x + 1) : ℕ) : ℝ) ≤
      2 * Real.log (x : ℝ) ^ 30 := by
    have hcastDiv : ((x / (mainCutoffNat x + 1) : ℕ) : ℝ) ≤
        (x : ℝ) / (mainCutoffNat x + 1 : ℕ) := Nat.cast_div_le
    have hden : (x : ℝ) / (2 * Real.log (x : ℝ) ^ 30) ≤
        (mainCutoffNat x + 1 : ℕ) := hQlower.trans (by norm_num)
    calc
      ((x / (mainCutoffNat x + 1) : ℕ) : ℝ) ≤
          (x : ℝ) / (mainCutoffNat x + 1 : ℕ) := hcastDiv
      _ ≤ (x : ℝ) / ((x : ℝ) / (2 * Real.log (x : ℝ) ^ 30)) := by
        exact div_le_div_of_nonneg_left hxR.le (div_pos hxR (mul_pos (by norm_num) hpow30)) hden
      _ = 2 * Real.log (x : ℝ) ^ 30 := by field_simp
  have hlog37le : Real.log (x : ℝ) ^ 37 ≤ (x : ℝ) := by
    rw [le_div_iff₀ (pow_pos hlogpos 37)] at h37
    simpa using h37
  have hlog30le : Real.log (x : ℝ) ^ 30 ≤
      (x : ℝ) / Real.log (x : ℝ) ^ 7 := by
    rw [le_div_iff₀ hpow7]
    rw [← pow_add]
    norm_num
    exact hlog37le
  have hjumpCast : (logarithmicStepJump x : ℝ) ≤
      1000 * (x : ℝ) / Real.log (x : ℝ) ^ 7 := by
    rw [logarithmicStepJump, Nat.cast_add]
    calc
      (5 : ℝ) + (x / (mainCutoffNat x + 1) : ℕ) ≤
          5 + 2 * Real.log (x : ℝ) ^ 30 := by linarith
      _ ≤ 5 * ((x : ℝ) / Real.log (x : ℝ) ^ 7) +
          2 * ((x : ℝ) / Real.log (x : ℝ) ^ 7) := by nlinarith
      _ ≤ 1000 * (x : ℝ) / Real.log (x : ℝ) ^ 7 := by
        have hsnonneg : 0 ≤ (x : ℝ) / Real.log (x : ℝ) ^ 7 := by positivity
        rw [show 1000 * (x : ℝ) / Real.log (x : ℝ) ^ 7 =
          1000 * ((x : ℝ) / Real.log (x : ℝ) ^ 7) by ring]
        nlinarith
  have hceil : 1000 * (x : ℝ) / Real.log (x : ℝ) ^ 7 ≤
      (proposition6DeletionBudget x : ℝ) := by
    exact Nat.le_ceil _
  exact_mod_cast hjumpCast.trans hceil

end

end Erdos285.LastCrossing

#print axioms Erdos285.LastCrossing.lastBelow_ratio_tendsto
#print axioms Erdos285.LastCrossing.surplusCutoff_ratio_tendsto
