import ErdosProblems.Erdos888.Asymptotic

/-!
# Dyadic transport for Erdős Problem 888

This file packages the elementary rounding step which lets later estimates be
proved only when the ambient parameter is a power of two.  We deliberately
round *up*: `dyadicCeil n` is `2 ^ (Nat.log 2 n + 1)`.  At powers of two this
is the following power rather than the same power, but in exchange its two
basic inequalities have particularly short proofs and it always lies in
`[n, 2n]` when `n` is positive.
-/

open Filter
open scoped Topology

namespace Erdos888

/-- An exponent whose corresponding power of two is strictly above `n`. -/
def dyadicCeilExponent (n : ℕ) : ℕ := Nat.log 2 n + 1

/-- A power of two in `(n, 2n]` for positive `n`. -/
def dyadicCeil (n : ℕ) : ℕ := 2 ^ dyadicCeilExponent n

/-- The exponent of the largest power of two not exceeding a positive `n`. -/
def dyadicFloorExponent (n : ℕ) : ℕ := Nat.log 2 n

/-- The largest power of two not exceeding a positive `n`. -/
def dyadicFloor (n : ℕ) : ℕ := 2 ^ dyadicFloorExponent n

/-- The dyadic ceiling really is a power of two. -/
theorem dyadicCeil_eq_two_pow (n : ℕ) :
    dyadicCeil n = 2 ^ dyadicCeilExponent n := rfl

/-- Our chosen dyadic ceiling lies (strictly) above its input. -/
theorem lt_dyadicCeil (n : ℕ) : n < dyadicCeil n := by
  simpa [dyadicCeil, dyadicCeilExponent, Nat.succ_eq_add_one] using
    (Nat.lt_pow_succ_log_self (by norm_num : 1 < (2 : ℕ)) n)

/-- Weak form of `lt_dyadicCeil`, convenient for monotonicity arguments. -/
theorem le_dyadicCeil (n : ℕ) : n ≤ dyadicCeil n :=
  (lt_dyadicCeil n).le

/-- For positive input the chosen power of two is at most twice the input. -/
theorem dyadicCeil_le_two_mul {n : ℕ} (hn : n ≠ 0) :
    dyadicCeil n ≤ 2 * n := by
  calc
    dyadicCeil n = 2 ^ Nat.log 2 n * 2 := by
      simp [dyadicCeil, dyadicCeilExponent, pow_succ]
    _ ≤ n * 2 := Nat.mul_le_mul_right 2 (Nat.pow_log_le_self 2 hn)
    _ = 2 * n := Nat.mul_comm _ _

/-- The dyadic floor is below a positive input. -/
theorem dyadicFloor_le {n : ℕ} (hn : n ≠ 0) : dyadicFloor n ≤ n := by
  exact Nat.pow_log_le_self 2 hn

/-- Every input is strictly below twice its dyadic floor. -/
theorem lt_two_mul_dyadicFloor (n : ℕ) : n < 2 * dyadicFloor n := by
  simpa [dyadicFloor, dyadicFloorExponent, pow_succ, Nat.mul_comm] using
    (Nat.lt_pow_succ_log_self (by norm_num : 1 < (2 : ℕ)) n)

/-- The dyadic floor exponent tends to infinity. -/
theorem dyadicFloorExponent_tendsto_atTop :
    Tendsto dyadicFloorExponent atTop atTop := by
  refine tendsto_atTop.2 fun j ↦ ?_
  filter_upwards [eventually_ge_atTop (2 ^ j)] with n hn
  exact Nat.le_log_of_pow_le (by norm_num : 1 < (2 : ℕ)) hn

/-- Consequently the dyadic floors themselves tend to infinity. -/
theorem dyadicFloor_tendsto_atTop : Tendsto dyadicFloor atTop atTop := by
  exact (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : 1 < (2 : ℕ))).comp
    dyadicFloorExponent_tendsto_atTop

/-- The dyadic ceiling exponent tends to infinity. -/
theorem dyadicCeilExponent_tendsto_atTop :
    Tendsto dyadicCeilExponent atTop atTop := by
  refine tendsto_atTop.2 fun j ↦ ?_
  filter_upwards [eventually_ge_atTop (2 ^ j)] with n hn
  exact (Nat.le_log_of_pow_le (by norm_num : 1 < (2 : ℕ)) hn).trans
    (Nat.le_add_right _ _)

/-- Consequently the dyadic ceilings themselves tend to infinity. -/
theorem dyadicCeil_tendsto_atTop : Tendsto dyadicCeil atTop atTop := by
  exact (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : 1 < (2 : ℕ))).comp
    dyadicCeilExponent_tendsto_atTop

/-! ## Stability of the comparison scale on a factor-two interval -/

/-- A pointwise analytic comparison used in the eventual dyadic estimate.

The last hypothesis is automatic for all sufficiently large `n`; keeping it
explicit makes the algebraic content of the lemma reusable. -/
theorem scale_le_four_mul_scale_of_mem_doubling_interval {n m : ℕ}
    (hn : 2 ≤ n) (hnm : n ≤ m) (hmn : m ≤ 2 * n)
    (hloglog : Real.log 2 ≤ Real.log (Real.log n)) :
    scale m ≤ 4 * scale n := by
  have hnRpos : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hn)
  have hmRpos : (0 : ℝ) < m := hnRpos.trans_le (by exact_mod_cast hnm)
  have hnlog : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hnloglog : 0 < Real.log (Real.log n) := hlog2.trans_le hloglog
  have hlogn_le_logm : Real.log (n : ℝ) ≤ Real.log (m : ℝ) :=
    Real.log_le_log hnRpos (by exact_mod_cast hnm)
  have hlogm_pos : 0 < Real.log (m : ℝ) := hnlog.trans_le hlogn_le_logm
  have hm_le_n_sq : m ≤ n ^ 2 := by
    calc
      m ≤ 2 * n := hmn
      _ = n * 2 := Nat.mul_comm _ _
      _ ≤ n * n := Nat.mul_le_mul_left n hn
      _ = n ^ 2 := by ring
  have hlogm_le_two_log_n : Real.log (m : ℝ) ≤ 2 * Real.log (n : ℝ) := by
    calc
      Real.log (m : ℝ) ≤ Real.log ((n : ℝ) ^ 2) :=
        Real.log_le_log hmRpos (by exact_mod_cast hm_le_n_sq)
      _ = 2 * Real.log (n : ℝ) := by rw [Real.log_pow]; norm_num
  have hloglogm_le_two_loglogn :
      Real.log (Real.log m) ≤ 2 * Real.log (Real.log n) := by
    calc
      Real.log (Real.log m) ≤ Real.log (2 * Real.log n) :=
        Real.log_le_log hlogm_pos hlogm_le_two_log_n
      _ = Real.log 2 + Real.log (Real.log n) := by
        rw [Real.log_mul (by norm_num) hnlog.ne']
      _ ≤ 2 * Real.log (Real.log n) := by linarith
  have hloglogm_nonneg : 0 ≤ Real.log (Real.log m) := by
    have hllmono : Real.log (Real.log n) ≤ Real.log (Real.log m) :=
      Real.log_le_log hnlog hlogn_le_logm
    exact hnloglog.le.trans hllmono
  have hnum_nonneg : 0 ≤ (m : ℝ) * Real.log (Real.log m) :=
    mul_nonneg (Nat.cast_nonneg _) hloglogm_nonneg
  have hfirst :
      (m : ℝ) * Real.log (Real.log m) / Real.log m ≤
        (m : ℝ) * Real.log (Real.log m) / Real.log n :=
    div_le_div_of_nonneg_left hnum_nonneg hnlog hlogn_le_logm
  have hcast_m : (m : ℝ) ≤ 2 * (n : ℝ) := by exact_mod_cast hmn
  have hnum_le :
      (m : ℝ) * Real.log (Real.log m) ≤
        (2 * (n : ℝ)) * (2 * Real.log (Real.log n)) :=
    mul_le_mul hcast_m hloglogm_le_two_loglogn hloglogm_nonneg
      (by positivity)
  calc
    scale m ≤ (m : ℝ) * Real.log (Real.log m) / Real.log n := hfirst
    _ ≤ (2 * (n : ℝ)) * (2 * Real.log (Real.log n)) / Real.log n :=
      div_le_div_of_nonneg_right hnum_le hnlog.le
    _ = 4 * scale n := by
      unfold scale
      ring

/-- Uniformly for `n ≤ m ≤ 2n`, the scale at `m` is eventually at most
four times the scale at `n`. -/
theorem eventually_scale_le_four_mul_scale_on_doubling_interval :
    ∀ᶠ n : ℕ in atTop, ∀ m : ℕ, n ≤ m → m ≤ 2 * n →
      scale m ≤ 4 * scale n := by
  have hloglog : ∀ᶠ n : ℕ in atTop,
      Real.log (2 : ℝ) ≤ Real.log (Real.log n) :=
    (Real.tendsto_log_atTop.comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).eventually_ge_atTop _
  filter_upwards [eventually_ge_atTop (2 : ℕ), hloglog] with n hn hll
  intro m hnm hmn
  exact scale_le_four_mul_scale_of_mem_doubling_interval hn hnm hmn hll

/-- The scale evaluated at the next dyadic point is eventually within a
factor four of the original scale. -/
theorem eventually_scale_dyadicCeil_le :
    ∀ᶠ n : ℕ in atTop, scale (dyadicCeil n) ≤ 4 * scale n := by
  filter_upwards [eventually_scale_le_four_mul_scale_on_doubling_interval,
    eventually_ge_atTop (1 : ℕ)] with n hscale hn
  exact hscale _ (le_dyadicCeil n) (dyadicCeil_le_two_mul (by omega))

/-- At the other end of a factor-two interval, the scale at `n` is
eventually within a factor four of the scale at its dyadic floor. -/
theorem eventually_scale_le_four_mul_scale_dyadicFloor :
    ∀ᶠ n : ℕ in atTop, scale n ≤ 4 * scale (dyadicFloor n) := by
  have hscaleAtFloor : ∀ᶠ n : ℕ in atTop,
      ∀ m : ℕ, dyadicFloor n ≤ m → m ≤ 2 * dyadicFloor n →
        scale m ≤ 4 * scale (dyadicFloor n) :=
    dyadicFloor_tendsto_atTop.eventually
      eventually_scale_le_four_mul_scale_on_doubling_interval
  filter_upwards [hscaleAtFloor, eventually_ge_atTop (1 : ℕ)]
    with n hscale hn
  exact hscale _ (dyadicFloor_le (by omega)) (lt_two_mul_dyadicFloor n).le

/-- Composition with the dyadic ceiling preserves the `scale` upper order. -/
theorem scale_comp_dyadicCeil_isBigO_scale :
    (fun n : ℕ ↦ scale (dyadicCeil n)) =O[atTop] scale := by
  apply isBigO_of_eventually_nonneg_le (C := 4) (by norm_num)
  · exact (dyadicCeil_tendsto_atTop.eventually eventually_scale_pos).mono
      fun _ h ↦ h.le
  · exact eventually_scale_pos.mono fun _ h ↦ h.le
  · exact eventually_scale_dyadicCeil_le

/-! ## Transporting bounds from powers of two -/

/-- A monotone real-valued counting function which satisfies an eventual
dyadic upper bound satisfies the corresponding bound at every sufficiently
large integer. -/
theorem eventually_le_of_monotone_dyadic_bound {f : ℕ → ℝ} {C : ℝ}
    (hf : Monotone f) (hC : 0 ≤ C)
    (hdyadic : ∀ᶠ j : ℕ in atTop, f (2 ^ j) ≤ C * scale (2 ^ j)) :
    ∀ᶠ n : ℕ in atTop, f n ≤ (4 * C) * scale n := by
  have hpulled : ∀ᶠ n : ℕ in atTop,
      f (2 ^ dyadicCeilExponent n) ≤
        C * scale (2 ^ dyadicCeilExponent n) :=
    dyadicCeilExponent_tendsto_atTop.eventually hdyadic
  filter_upwards [hpulled, eventually_scale_dyadicCeil_le] with n hbound hscale
  calc
    f n ≤ f (dyadicCeil n) := hf (le_dyadicCeil n)
    _ ≤ C * scale (dyadicCeil n) := by simpa [dyadicCeil] using hbound
    _ ≤ C * (4 * scale n) := mul_le_mul_of_nonneg_left hscale hC
    _ = (4 * C) * scale n := by ring

/-- Big-O form of `eventually_le_of_monotone_dyadic_bound`. -/
theorem isBigO_of_monotone_dyadic_bound {f : ℕ → ℝ} {C : ℝ}
    (hf : Monotone f) (hC : 0 < C)
    (hf_nonneg : ∀ᶠ n : ℕ in atTop, 0 ≤ f n)
    (hdyadic : ∀ᶠ j : ℕ in atTop, f (2 ^ j) ≤ C * scale (2 ^ j)) :
    f =O[atTop] scale := by
  apply isBigO_of_eventually_nonneg_le (C := 4 * C) (mul_pos (by norm_num) hC)
    hf_nonneg (eventually_scale_pos.mono fun _ h ↦ h.le)
  exact eventually_le_of_monotone_dyadic_bound hf hC.le hdyadic

/-- Natural-valued counting-function form of the dyadic big-O transfer. -/
theorem natCast_isBigO_of_monotone_dyadic_bound {f : ℕ → ℕ} {C : ℝ}
    (hf : Monotone f) (hC : 0 < C)
    (hdyadic : ∀ᶠ j : ℕ in atTop,
      (f (2 ^ j) : ℝ) ≤ C * scale (2 ^ j)) :
    (fun n : ℕ ↦ (f n : ℝ)) =O[atTop] scale := by
  apply isBigO_of_monotone_dyadic_bound (fun _ _ h ↦ by exact_mod_cast hf h)
    hC (Eventually.of_forall fun _ ↦ Nat.cast_nonneg _) hdyadic

/-- Lower-bound analogue of `eventually_le_of_monotone_dyadic_bound`: a
dyadic lower estimate for a monotone function transports to all large
integers, losing only a factor four in the constant. -/
theorem eventually_le_monotone_of_dyadic_lower_bound {f : ℕ → ℝ} {C : ℝ}
    (hf : Monotone f) (hC : 0 ≤ C)
    (hdyadic : ∀ᶠ j : ℕ in atTop, C * scale (2 ^ j) ≤ f (2 ^ j)) :
    ∀ᶠ n : ℕ in atTop, (C / 4) * scale n ≤ f n := by
  have hpulled : ∀ᶠ n : ℕ in atTop,
      C * scale (2 ^ dyadicFloorExponent n) ≤
        f (2 ^ dyadicFloorExponent n) :=
    dyadicFloorExponent_tendsto_atTop.eventually hdyadic
  filter_upwards [hpulled, eventually_scale_le_four_mul_scale_dyadicFloor,
    eventually_ge_atTop (1 : ℕ)] with n hbound hscale hn
  calc
    (C / 4) * scale n ≤ (C / 4) * (4 * scale (dyadicFloor n)) :=
      mul_le_mul_of_nonneg_left hscale (div_nonneg hC (by norm_num))
    _ = C * scale (dyadicFloor n) := by ring
    _ ≤ f (dyadicFloor n) := by simpa [dyadicFloor] using hbound
    _ ≤ f n := hf (dyadicFloor_le (by omega))

/-- Big-O formulation of a transported positive dyadic lower bound. -/
theorem scale_isBigO_of_monotone_dyadic_lower_bound {f : ℕ → ℝ} {C : ℝ}
    (hf : Monotone f) (hC : 0 < C)
    (hf_nonneg : ∀ᶠ n : ℕ in atTop, 0 ≤ f n)
    (hdyadic : ∀ᶠ j : ℕ in atTop, C * scale (2 ^ j) ≤ f (2 ^ j)) :
    scale =O[atTop] f := by
  apply isBigO_of_eventually_nonneg_le (C := 4 / C) (div_pos (by norm_num) hC)
    (eventually_scale_pos.mono fun _ h ↦ h.le) hf_nonneg
  filter_upwards [eventually_le_monotone_of_dyadic_lower_bound hf hC.le hdyadic]
    with n hlower
  calc
    scale n = (4 / C) * ((C / 4) * scale n) := by field_simp
    _ ≤ (4 / C) * f n :=
      mul_le_mul_of_nonneg_left hlower (div_nonneg (by norm_num) hC.le)

/-- Natural-valued counting-function form of the dyadic lower transfer. -/
theorem scale_isBigO_natCast_of_monotone_dyadic_lower_bound {f : ℕ → ℕ}
    {C : ℝ} (hf : Monotone f) (hC : 0 < C)
    (hdyadic : ∀ᶠ j : ℕ in atTop,
      C * scale (2 ^ j) ≤ (f (2 ^ j) : ℝ)) :
    scale =O[atTop] (fun n : ℕ ↦ (f n : ℝ)) := by
  apply scale_isBigO_of_monotone_dyadic_lower_bound
    (fun _ _ h ↦ by exact_mod_cast hf h) hC
    (Eventually.of_forall fun _ ↦ Nat.cast_nonneg _) hdyadic

end Erdos888
