/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos305.SmoothInterval
import ErdosProblems.Erdos285.Lemma16

/-!
# The polylogarithmic scale for Erdős 305

The ambient denominator scale is
`log b * exp (sqrt (log (log b)))`.  Eventually this is exactly
`(log b) ^ (1 + delta b)`, where `delta b = 1 / sqrt (log (log b))`.
The subexponential extra factor is large enough to absorb the fixed
`log(N)^30` loss in the smooth cutoff.
-/

open Filter Real
open scoped Topology

namespace Erdos305.Scale

noncomputable section

def u (b : ℕ) : ℝ := Real.log (Real.log (b : ℝ))

def delta (b : ℕ) : ℝ := (Real.sqrt (u b))⁻¹

def realScale (b : ℕ) : ℝ :=
  Real.log (b : ℝ) * Real.exp (Real.sqrt (u b))

def cutoff (b : ℕ) : ℕ := ⌈realScale b⌉₊

lemma u_tendsto_atTop : Tendsto u atTop atTop := by
  exact Real.tendsto_log_atTop.comp
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)

lemma sqrt_u_tendsto_atTop :
    Tendsto (fun b : ℕ ↦ Real.sqrt (u b)) atTop atTop :=
  Real.tendsto_sqrt_atTop.comp u_tendsto_atTop

lemma delta_tendsto_zero : Tendsto delta atTop (𝓝 0) := by
  exact sqrt_u_tendsto_atTop.inv_tendsto_atTop

lemma realScale_tendsto_atTop : Tendsto realScale atTop atTop := by
  have hlog : Tendsto (fun b : ℕ ↦ Real.log (b : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hexp : Tendsto (fun b : ℕ ↦ Real.exp (Real.sqrt (u b))) atTop atTop :=
    Real.tendsto_exp_atTop.comp sqrt_u_tendsto_atTop
  exact hlog.atTop_mul_atTop₀ hexp

lemma cutoff_tendsto_atTop : Tendsto cutoff atTop atTop :=
  tendsto_nat_ceil_atTop.comp realScale_tendsto_atTop

lemma eventually_realScale_eq_rpow :
    ∀ᶠ b : ℕ in atTop,
      realScale b = Real.log (b : ℝ) ^ (1 + delta b) := by
  filter_upwards [u_tendsto_atTop.eventually (eventually_gt_atTop 0),
    eventually_gt_atTop 1] with b hu hb
  have hlogb : 0 < Real.log (b : ℝ) := Real.log_pos (by exact_mod_cast hb)
  have hsqrt : 0 < Real.sqrt (u b) := Real.sqrt_pos.2 hu
  have hsquare : Real.sqrt (u b) * Real.sqrt (u b) = u b := by
    nlinarith [Real.sq_sqrt hu.le]
  rw [realScale, Real.rpow_def_of_pos hlogb, delta]
  have harg : u b * (1 + (Real.sqrt (u b))⁻¹) =
      u b + Real.sqrt (u b) := by
    field_simp [hsqrt.ne']
    nlinarith
  rw [show Real.log (Real.log (b : ℝ)) = u b by rfl, harg,
    Real.exp_add]
  have heu : Real.exp (u b) = Real.log (b : ℝ) := by
    rw [u, Real.exp_log hlogb]
  rw [heu]

lemma eventually_cutoff_le_two_realScale :
    ∀ᶠ b : ℕ in atTop, (cutoff b : ℝ) ≤ 2 * realScale b := by
  filter_upwards [realScale_tendsto_atTop.eventually (eventually_ge_atTop 1)]
      with b hs
  have hceil := Nat.ceil_lt_add_one (show 0 ≤ realScale b by positivity)
  dsimp [cutoff]
  linarith

lemma eventually_log_cutoff_le_three_u :
    ∀ᶠ b : ℕ in atTop,
      Real.log (cutoff b : ℝ) ≤ 3 * u b := by
  filter_upwards [eventually_cutoff_le_two_realScale,
    u_tendsto_atTop.eventually (eventually_ge_atTop 1),
    eventually_gt_atTop 1] with b hcut hu hb
  have hlogb : 0 < Real.log (b : ℝ) := Real.log_pos (by exact_mod_cast hb)
  have hsqrt0 : 0 ≤ Real.sqrt (u b) := Real.sqrt_nonneg _
  have hsqrtLe : Real.sqrt (u b) ≤ u b := by
    nlinarith [Real.sq_sqrt (show 0 ≤ u b by linarith), Real.sqrt_nonneg (u b)]
  have hscalePos : 0 < realScale b := by
    exact mul_pos hlogb (Real.exp_pos _)
  have hcutPos : 0 < (cutoff b : ℝ) := by
    exact hscalePos.trans_le (by
      dsimp [cutoff]
      exact Nat.le_ceil (realScale b))
  have htwoScalePos : 0 < 2 * realScale b := mul_pos zero_lt_two hscalePos
  have hlogMono := Real.log_le_log hcutPos hcut
  calc
    Real.log (cutoff b : ℝ) ≤ Real.log (2 * realScale b) := hlogMono
    _ = Real.log 2 + u b + Real.sqrt (u b) := by
      rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hscalePos.ne', realScale,
        Real.log_mul hlogb.ne' (Real.exp_pos _).ne', Real.log_exp]
      simp only [u]
      ring
    _ ≤ 3 * u b := by
      have hlog2 : Real.log 2 < 1 := Real.log_two_lt_d9.trans (by norm_num)
      linarith

/-- The main smoothness cutoff at `cutoff b` dominates any fixed multiple of
`log b`. -/
lemma eventually_mul_log_le_mainCutoff (A : ℝ) (_hA : 0 < A) :
    ∀ᶠ b : ℕ in atTop,
      A * Real.log (b : ℝ) ≤
        Erdos285.proposition6MainCutoff (cutoff b) := by
  have hdom : Tendsto
      (fun b : ℕ ↦ Real.exp (Real.sqrt (u b)) /
        Real.sqrt (u b) ^ (60 : ℕ)) atTop atTop :=
    (Real.tendsto_exp_div_pow_atTop 60).comp sqrt_u_tendsto_atTop
  filter_upwards [eventually_log_cutoff_le_three_u,
    u_tendsto_atTop.eventually (eventually_ge_atTop 1),
    hdom.eventually (eventually_ge_atTop (A * 3 ^ (30 : ℕ))),
    eventually_gt_atTop 1] with b hlogCut hu hdomB hb
  have hlogb : 0 < Real.log (b : ℝ) := Real.log_pos (by exact_mod_cast hb)
  have hu0 : 0 ≤ u b := by linarith
  have hv : 0 < Real.sqrt (u b) := Real.sqrt_pos.2 (by linarith)
  have hcutCast : realScale b ≤ (cutoff b : ℝ) := by
    dsimp [cutoff]
    exact Nat.le_ceil _
  have hcutPos : 0 < (cutoff b : ℝ) :=
    (mul_pos hlogb (Real.exp_pos _)).trans_le hcutCast
  have hlogCutPos : 0 < Real.log (cutoff b : ℝ) := by
    have hscaleOne : 1 < realScale b := by
      have hexpOne : 1 < Real.exp (Real.sqrt (u b)) :=
        Real.one_lt_exp_iff.mpr hv
      have hlogbOne : 1 ≤ Real.log (b : ℝ) := by
        have hub : u b ≥ 1 := hu
        rw [u] at hub
        have := Real.exp_le_exp.mpr hub
        rw [Real.exp_log hlogb] at this
        linarith [Real.exp_one_gt_d9]
      exact lt_of_lt_of_le hexpOne
        (le_mul_of_one_le_left (Real.exp_pos _).le hlogbOne)
    exact Real.log_pos (hscaleOne.trans_le hcutCast)
  have hpowLog : Real.log (cutoff b : ℝ) ^ (30 : ℕ) ≤
      (3 * u b) ^ (30 : ℕ) := by
    gcongr
  have hsquare : Real.sqrt (u b) ^ 2 = u b := Real.sq_sqrt hu0
  have hratio : A ≤ Real.exp (Real.sqrt (u b)) / (3 * u b) ^ (30 : ℕ) := by
    have hpowRewrite : (3 * u b) ^ (30 : ℕ) =
        3 ^ (30 : ℕ) * Real.sqrt (u b) ^ (60 : ℕ) := by
      rw [mul_pow]
      have : u b ^ (30 : ℕ) = Real.sqrt (u b) ^ (60 : ℕ) := by
        calc
          u b ^ (30 : ℕ) = (Real.sqrt (u b) ^ 2) ^ (30 : ℕ) := by rw [hsquare]
          _ = Real.sqrt (u b) ^ (60 : ℕ) := by ring
      rw [this]
    rw [hpowRewrite]
    have hthree : 0 < (3 : ℝ) ^ (30 : ℕ) := by positivity
    have hvpow : 0 < Real.sqrt (u b) ^ (60 : ℕ) := pow_pos hv _
    calc
      A ≤ (Real.exp (Real.sqrt (u b)) / Real.sqrt (u b) ^ (60 : ℕ)) /
          3 ^ (30 : ℕ) := by
        exact (le_div_iff₀ hthree).2 (by simpa [mul_comm] using hdomB)
      _ = Real.exp (Real.sqrt (u b)) /
          (3 ^ (30 : ℕ) * Real.sqrt (u b) ^ (60 : ℕ)) := by
        field_simp
  rw [Erdos285.proposition6MainCutoff]
  have hden : 0 < Real.log (cutoff b : ℝ) ^ (30 : ℕ) := pow_pos hlogCutPos _
  have hden' : 0 < (3 * u b) ^ (30 : ℕ) := by positivity
  calc
    A * Real.log (b : ℝ) ≤
        Real.log (b : ℝ) *
          (Real.exp (Real.sqrt (u b)) / (3 * u b) ^ (30 : ℕ)) := by
      simpa [mul_comm] using mul_le_mul_of_nonneg_left hratio hlogb.le
    _ = realScale b / (3 * u b) ^ (30 : ℕ) := by
      rw [realScale]
      ring
    _ ≤ (cutoff b : ℝ) / (3 * u b) ^ (30 : ℕ) := by
      exact div_le_div_of_nonneg_right hcutCast hden'.le
    _ ≤ (cutoff b : ℝ) / Real.log (cutoff b : ℝ) ^ (30 : ℕ) := by
      exact div_le_div_of_nonneg_left hcutPos.le hden hpowLog

lemma eventually_mul_log_le_mainCutoffNat (A : ℝ) (hA : 0 < A) :
    ∀ᶠ b : ℕ in atTop,
      A * Real.log (b : ℝ) ≤
        (Erdos285.mainCutoffNat (cutoff b) : ℝ) := by
  filter_upwards [eventually_mul_log_le_mainCutoff (2 * A) (mul_pos zero_lt_two hA),
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop (1 / A))] with b hcut hlog
  have hAlog : 1 ≤ A * Real.log (b : ℝ) := by
    have := mul_le_mul_of_nonneg_left hlog hA.le
    simpa [hA.ne'] using this
  have hfloor := Nat.lt_floor_add_one
    (Erdos285.proposition6MainCutoff (cutoff b))
  rw [← Erdos285.mainCutoffNat_eq] at hfloor
  have hfloor' : Erdos285.proposition6MainCutoff (cutoff b) - 1 <
      (Erdos285.mainCutoffNat (cutoff b) : ℝ) := by linarith
  linarith

lemma mainCutoffNat_cutoff_tendsto_atTop :
    Tendsto (fun b : ℕ ↦ Erdos285.mainCutoffNat (cutoff b)) atTop atTop := by
  have hlog : Tendsto (fun b : ℕ ↦ Real.log (b : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlower := eventually_mul_log_le_mainCutoffNat 1 (by norm_num)
  have hlog1 : Tendsto (fun b : ℕ ↦ (1 : ℝ) * Real.log (b : ℝ)) atTop atTop := by
    simpa using hlog
  have hreal : Tendsto
      (fun b : ℕ ↦ (Erdos285.mainCutoffNat (cutoff b) : ℝ)) atTop atTop :=
    tendsto_atTop_mono' atTop hlower hlog1
  exact tendsto_natCast_atTop_iff.mp hreal

/-- The smooth modulus `lcm(1,...,mainCutoffNat (cutoff b))` eventually
dominates `6b`. -/
lemma eventually_six_mul_lt_initialLcm :
    ∀ᶠ b : ℕ in atTop,
      6 * b < Erdos285.PrimePowers.initialLcm
        (Erdos285.mainCutoffNat (cutoff b)) := by
  let c : ℝ := Real.log 2 / 2
  have hc : c < Real.log 2 := by
    dsimp [c]
    exact half_lt_self (Real.log_pos one_lt_two)
  have hpsi := (tendsto_natCast_atTop_atTop.comp
    mainCutoffNat_cutoff_tendsto_atTop).eventually
      (chebyshev_lower_explicit hc)
  have hS := eventually_mul_log_le_mainCutoffNat
    (4 / Real.log 2) (div_pos (by norm_num) (Real.log_pos one_lt_two))
  filter_upwards [hpsi, hS, eventually_ge_atTop 7] with b hpsiB hSB hb
  let S := Erdos285.mainCutoffNat (cutoff b)
  let Q := Erdos285.PrimePowers.initialLcm S
  have hlogb : 0 < Real.log (b : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < b by omega))
  have hQpos : (0 : ℝ) < Q := by
    exact_mod_cast (Nat.pos_of_ne_zero (by simp [Q, Erdos285.PrimePowers.initialLcm]))
  have hlogQ : Real.log (Q : ℝ) = chebyshev_second (S : ℝ) := by
    change Real.log (Nat.lcmUpto S : ℝ) = Chebyshev.psi (S : ℝ)
    exact (Chebyshev.psi_eq_log_lcmUpto S).symm
  have htwoLog : 2 * Real.log (b : ℝ) ≤ Real.log (Q : ℝ) := by
    rw [hlogQ]
    have hcS : 2 * Real.log (b : ℝ) ≤ c * (S : ℝ) := by
      dsimp [c]
      have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
      calc
        2 * Real.log (b : ℝ) =
            (Real.log 2 / 2) * ((4 / Real.log 2) * Real.log (b : ℝ)) := by
          field_simp [hlog2.ne']
          ring
        _ ≤ (Real.log 2 / 2) * (S : ℝ) := by
          exact mul_le_mul_of_nonneg_left (by simpa [S] using hSB)
            (div_nonneg (Real.log_nonneg one_le_two) zero_le_two)
    exact hcS.trans hpsiB
  have hsq : (b : ℝ) ^ 2 ≤ Q := by
    have hexp := Real.exp_le_exp.mpr htwoLog
    rw [Real.exp_log hQpos] at hexp
    have hbpos : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by omega)
    rw [show 2 * Real.log (b : ℝ) =
      Real.log (b : ℝ) + Real.log (b : ℝ) by ring,
      Real.exp_add, Real.exp_log hbpos] at hexp
    simpa [pow_two] using hexp
  have hsix : (6 * b : ℕ) < b ^ 2 := by
    nlinarith
  exact lt_of_lt_of_le hsix (by exact_mod_cast hsq)

/-- The ambient scale is `b^o(1)`; this elementary square bound is used to
make the small-numerator prime interval uniformly long. -/
lemma eventually_mul_cutoff_sq_lt (A : ℝ) (hA : 0 < A) :
    ∀ᶠ b : ℕ in atTop, A * (cutoff b : ℝ) ^ 2 < b := by
  have ht : Tendsto (fun b : ℕ ↦ Real.log (b : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hdom := (Real.tendsto_exp_div_pow_atTop 4).comp ht
  filter_upwards [eventually_cutoff_le_two_realScale,
    u_tendsto_atTop.eventually (eventually_ge_atTop 1),
    hdom.eventually (eventually_gt_atTop (4 * A)),
    eventually_gt_atTop 1] with b hcut hu hdomB hb
  have hlogb : 0 < Real.log (b : ℝ) := Real.log_pos (by exact_mod_cast hb)
  have hsqrtLe : Real.sqrt (u b) ≤ u b := by
    nlinarith [Real.sq_sqrt (show 0 ≤ u b by linarith), Real.sqrt_nonneg (u b)]
  have hexpLe : Real.exp (Real.sqrt (u b)) ≤ Real.log (b : ℝ) := by
    have := Real.exp_le_exp.mpr hsqrtLe
    rw [u, Real.exp_log hlogb] at this
    exact this
  have hscaleLe : realScale b ≤ Real.log (b : ℝ) ^ 2 := by
    rw [realScale, pow_two]
    exact mul_le_mul_of_nonneg_left hexpLe hlogb.le
  have hcutLe : (cutoff b : ℝ) ≤ 2 * Real.log (b : ℝ) ^ 2 :=
    hcut.trans (mul_le_mul_of_nonneg_left hscaleLe zero_le_two)
  have hcutSq : (cutoff b : ℝ) ^ 2 ≤ 4 * Real.log (b : ℝ) ^ 4 := by
    nlinarith [sq_nonneg ((cutoff b : ℝ) - 2 * Real.log (b : ℝ) ^ 2)]
  have hmain : 4 * A * Real.log (b : ℝ) ^ 4 < (b : ℝ) := by
    have hmainExp : 4 * A * Real.log (b : ℝ) ^ 4 <
        Real.exp (Real.log (b : ℝ)) :=
      (lt_div_iff₀ (pow_pos hlogb 4)).1 (by
      simpa [mul_assoc] using hdomB)
    rwa [Real.exp_log (by positivity)] at hmainExp
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hcutSq hA.le) (by
    simpa [mul_assoc, mul_left_comm, mul_comm] using hmain)

end

end Erdos305.Scale
