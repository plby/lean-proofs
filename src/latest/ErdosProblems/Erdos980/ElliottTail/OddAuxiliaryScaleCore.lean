import ErdosProblems.Erdos980.ElliottTail.OddMediumParameters

/-!
# Subpower scale of the odd auxiliary modulus

The inert tensor uses `4 * clog₂ (t + 1)` auxiliary coordinates.  Although
the corresponding modulus is not bounded by a fixed power of `t`, its
logarithm is `O(log (t + 1)²)`.  Uniformly for
`t ≤ smoothParameterY x`, this is `o(log x)`, so the full modulus is bounded
by every fixed positive power of `x`.

This core module proves the real subpower estimate without importing the
concrete norm-sieve endpoint layer.
-/

open Filter
open scoped NumberField Topology

namespace Erdos980.ElliottTail.OddAuxiliaryScale

open OddMediumParameters

noncomputable section

/-- A real logarithmic upper bound for the strengthened tensor depth. -/
theorem oddTensorDepth_cast_le_eight_mul_log_add_one (t : ℕ) :
    (oddTensorDepth t : ℝ) ≤
      8 * (Real.log ((t + 1 : ℕ) : ℝ) + 1) := by
  have hclog :
      Nat.clog 2 (t + 1) ≤ Nat.log 2 (t + 1) + 1 :=
    Nat.clog_le_of_le_pow
      (le_of_lt (Nat.lt_pow_succ_log_self (by norm_num) (t + 1)))
  have hnatLog :
      (Nat.log 2 (t + 1) : ℝ) ≤
        Real.log ((t + 1 : ℕ) : ℝ) / Real.log 2 := by
    simpa [Real.logb] using Real.natLog_le_logb (t + 1) 2
  have hlogTwoPos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogTwoHalf : (1 / 2 : ℝ) < Real.log 2 := by
    linarith [Real.log_two_gt_d9]
  have hlogNonneg : 0 ≤ Real.log ((t + 1 : ℕ) : ℝ) := by
    apply Real.log_nonneg
    exact_mod_cast (show 1 ≤ t + 1 by omega)
  have hdiv :
      Real.log ((t + 1 : ℕ) : ℝ) / Real.log 2 ≤
        2 * Real.log ((t + 1 : ℕ) : ℝ) := by
    rw [div_le_iff₀ hlogTwoPos]
    nlinarith
  calc
    (oddTensorDepth t : ℝ) = 4 * (Nat.clog 2 (t + 1) : ℝ) := by
      simp [oddTensorDepth]
    _ ≤ 4 * ((Nat.log 2 (t + 1) : ℝ) + 1) := by
      gcongr
      exact_mod_cast hclog
    _ ≤ 4 *
        (Real.log ((t + 1 : ℕ) : ℝ) / Real.log 2 + 1) := by
      gcongr
    _ ≤ 4 * (2 * Real.log ((t + 1 : ℕ) : ℝ) + 1) := by
      gcongr
    _ ≤ 8 * (Real.log ((t + 1 : ℕ) : ℝ) + 1) := by
      nlinarith

/-- Before substituting the smooth cutoff, the auxiliary modulus is bounded
by an exponential of a squared logarithm. -/
theorem auxiliaryModulus_cast_le_exp_log_sq (t : ℕ) :
    (((t + 1) ^ oddTensorDepth t : ℕ) : ℝ) ≤
      Real.exp (8 * (Real.log ((t + 1 : ℕ) : ℝ) + 1) ^ 2) := by
  let n : ℕ := t + 1
  have hnpos : (0 : ℝ) < (n : ℝ) := by positivity
  have hlogNonneg : 0 ≤ Real.log (n : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by simp [n]))
  have hdepth : (oddTensorDepth t : ℝ) ≤
      8 * (Real.log (n : ℝ) + 1) := by
    simpa [n] using oddTensorDepth_cast_le_eight_mul_log_add_one t
  have hexponent :
      Real.log (n : ℝ) * (oddTensorDepth t : ℝ) ≤
        8 * (Real.log (n : ℝ) + 1) ^ 2 := by
    calc
      Real.log (n : ℝ) * (oddTensorDepth t : ℝ) ≤
          Real.log (n : ℝ) * (8 * (Real.log (n : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left hdepth hlogNonneg
      _ ≤ 8 * (Real.log (n : ℝ) + 1) ^ 2 := by nlinarith
  calc
    (((t + 1) ^ oddTensorDepth t : ℕ) : ℝ) =
        (n : ℝ) ^ oddTensorDepth t := by simp [n]
    _ = (n : ℝ) ^ (oddTensorDepth t : ℝ) :=
      (Real.rpow_natCast _ _).symm
    _ = Real.exp (Real.log (n : ℝ) * (oddTensorDepth t : ℝ)) := by
      rw [Real.rpow_def_of_pos hnpos]
    _ ≤ Real.exp (8 * (Real.log (n : ℝ) + 1) ^ 2) :=
      Real.exp_le_exp.mpr hexponent
    _ = Real.exp
        (8 * (Real.log ((t + 1 : ℕ) : ℝ) + 1) ^ 2) := by simp [n]

/-- Uniform subpower bound for every layer below the smoothness cutoff. -/
theorem eventually_uniform_auxiliaryModulus_le_rpow
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ x : ℕ in atTop, ∀ t : ℕ, t ≤ smoothParameterY x →
      (((t + 1) ^ oddTensorDepth t : ℕ) : ℝ) ≤ (x : ℝ) ^ δ := by
  have hlogTop :
      Tendsto (fun x : ℕ ↦ Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlogLarge :
      ∀ᶠ x : ℕ in atTop, (2 : ℝ) ≤ Real.log (x : ℝ) :=
    hlogTop.eventually (eventually_ge_atTop 2)
  have hconstant : (0 : ℝ) < δ / 9800 := div_pos hδ (by norm_num)
  have hlogLogSmall :
      ∀ᶠ x : ℕ in atTop,
        ‖Real.log (Real.log (x : ℝ)) ^ 2‖ ≤
          (δ / 9800) * ‖Real.log (x : ℝ)‖ :=
    ((Real.isLittleO_pow_log_id_atTop (n := 2)).comp_tendsto hlogTop).bound
      hconstant
  filter_upwards
      [hlogLogSmall, hlogLarge,
        eventually_smoothParameterY_add_one_sq_le_log_pow,
        eventually_ge_atTop 1]
      with x hsmall hLlarge hcut hx
  intro t ht
  let L : ℝ := Real.log (x : ℝ)
  let n : ℕ := t + 1
  have hxpos : (0 : ℝ) < (x : ℝ) := by exact_mod_cast (show 0 < x by omega)
  have hLpos : 0 < L := lt_of_lt_of_le (by norm_num) hLlarge
  have hlogLNonneg : 0 ≤ Real.log L :=
    Real.log_nonneg (by linarith [hLlarge])
  have hsmall' : Real.log L ^ 2 ≤ (δ / 9800) * L := by
    simpa only [L, Real.norm_eq_abs,
      abs_of_nonneg (sq_nonneg (Real.log (Real.log (x : ℝ)))),
      abs_of_pos (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) hLlarge)]
      using hsmall
  have hpowRewrite : L ^ (64 : ℕ) = (L ^ (32 : ℕ)) ^ 2 := by ring
  have hcut' : (((smoothParameterY x + 1 : ℕ) : ℝ) ^ 2) ≤
      4 * (L ^ (32 : ℕ)) ^ 2 := by
    simpa only [L, hpowRewrite] using hcut
  have hYle : ((smoothParameterY x + 1 : ℕ) : ℝ) ≤
      2 * L ^ (32 : ℕ) := by
    have hYnonneg : 0 ≤ ((smoothParameterY x + 1 : ℕ) : ℝ) := by positivity
    have hpowNonneg : 0 ≤ L ^ (32 : ℕ) := pow_nonneg hLpos.le _
    nlinarith [sq_nonneg
      (((smoothParameterY x + 1 : ℕ) : ℝ) + 2 * L ^ (32 : ℕ))]
  have hnY : n ≤ smoothParameterY x + 1 := by
    dsimp [n]
    omega
  have hnle : (n : ℝ) ≤ 2 * L ^ (32 : ℕ) := by
    have hnYR : (n : ℝ) ≤ (smoothParameterY x + 1 : ℕ) := by
      exact_mod_cast hnY
    exact hnYR.trans hYle
  have hnpos : (0 : ℝ) < (n : ℝ) := by positivity
  have hlogTwoLeLogL : Real.log 2 ≤ Real.log L := by
    exact Real.log_le_log (by norm_num) hLlarge
  have hlogn : Real.log (n : ℝ) ≤ 33 * Real.log L := by
    calc
      Real.log (n : ℝ) ≤ Real.log (2 * L ^ (32 : ℕ)) :=
        Real.log_le_log hnpos hnle
      _ = Real.log 2 + 32 * Real.log L := by
        rw [Real.log_mul (by norm_num) (pow_ne_zero _ hLpos.ne'), Real.log_pow]
        norm_num
      _ ≤ 33 * Real.log L := by linarith
  have honeLe : (1 : ℝ) ≤ 2 * Real.log L := by
    linarith [Real.log_two_gt_d9, hlogTwoLeLogL]
  have hlognAdd : Real.log (n : ℝ) + 1 ≤ 35 * Real.log L := by
    linarith
  have hcost :
      8 * (Real.log (n : ℝ) + 1) ^ 2 ≤ δ * L := by
    calc
      8 * (Real.log (n : ℝ) + 1) ^ 2 ≤
          8 * (35 * Real.log L) ^ 2 := by
        gcongr
      _ = 9800 * Real.log L ^ 2 := by ring
      _ ≤ 9800 * ((δ / 9800) * L) := by gcongr
      _ = δ * L := by ring
  calc
    (((t + 1) ^ oddTensorDepth t : ℕ) : ℝ) ≤
        Real.exp (8 * (Real.log ((t + 1 : ℕ) : ℝ) + 1) ^ 2) :=
      auxiliaryModulus_cast_le_exp_log_sq t
    _ = Real.exp (8 * (Real.log (n : ℝ) + 1) ^ 2) := by simp [n]
    _ ≤ Real.exp (δ * L) := Real.exp_le_exp.mpr hcost
    _ = (x : ℝ) ^ δ := by
      rw [Real.rpow_def_of_pos hxpos]
      congr 1
      simp only [L]
      ring


end

end Erdos980.ElliottTail.OddAuxiliaryScale
