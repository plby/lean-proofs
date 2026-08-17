import Mathlib

open Filter
open scoped Topology

namespace Erdos543

/-- The real-valued main term occurring in the proposed bound. -/
noncomputable def cutoffArgument (g : ℕ → ℝ) (N : ℕ) : ℝ :=
  Real.log (N : ℝ) / Real.log 2 + g N

/-- The integer cutoff obtained by taking the natural ceiling. -/
noncomputable def cutoffSize (g : ℕ → ℝ) (N : ℕ) : ℕ :=
  Nat.ceil (cutoffArgument g N)

/-- The occupancy parameter `(2^k - 1) / N` attached to the cutoff. -/
noncomputable def collisionParameter (g : ℕ → ℝ) (N : ℕ) : ℝ :=
  ((2 : ℝ) ^ cutoffSize g N - 1) / (N : ℝ)

lemma tendsto_log_nat_atTop :
    Tendsto (fun N : ℕ ↦ Real.log (N : ℝ)) atTop atTop := by
  exact Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

lemma tendsto_log_log_nat_atTop :
    Tendsto (fun N : ℕ ↦ Real.log (Real.log (N : ℝ))) atTop atTop := by
  exact Real.tendsto_log_atTop.comp tendsto_log_nat_atTop

/-- The explicit quotient formulation of `g = o(log log)` implies the
Mathlib `IsLittleO` formulation. -/
lemma isLittleO_loglog_of_tendsto_div {g : ℕ → ℝ}
    (hg : Tendsto (fun N ↦ g N / Real.log (Real.log (N : ℝ))) atTop (𝓝 0)) :
    g =o[atTop] (fun N : ℕ ↦ Real.log (Real.log (N : ℝ))) := by
  rw [Asymptotics.isLittleO_iff_tendsto']
  · exact hg
  · filter_upwards [tendsto_log_log_nat_atTop.eventually (eventually_gt_atTop 0)]
      with N hN
    exact fun hzero ↦ (hN.ne' hzero).elim

/-- `log log N = o(log N)` along the natural numbers. -/
lemma isLittleO_loglog_log_nat :
    (fun N : ℕ ↦ Real.log (Real.log (N : ℝ))) =o[atTop]
      (fun N : ℕ ↦ Real.log (N : ℝ)) := by
  simpa [Function.comp_def] using
    Real.isLittleO_log_id_atTop.comp_tendsto tendsto_log_nat_atTop

/-- A proposed `o(log log N)` error is in particular `o(log N)`. -/
lemma isLittleO_log_of_tendsto_div {g : ℕ → ℝ}
    (hg : Tendsto (fun N ↦ g N / Real.log (Real.log (N : ℝ))) atTop (𝓝 0)) :
    g =o[atTop] (fun N : ℕ ↦ Real.log (N : ℝ)) :=
  (isLittleO_loglog_of_tendsto_div hg).trans isLittleO_loglog_log_nat

/-- The quotient hypothesis gives its usual eventual epsilon inequality. -/
lemma eventually_abs_le_mul_loglog {g : ℕ → ℝ}
    (hg : Tendsto (fun N ↦ g N / Real.log (Real.log (N : ℝ))) atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      |g N| ≤ ε * Real.log (Real.log (N : ℝ)) := by
  have hb := (isLittleO_loglog_of_tendsto_div hg).bound hε
  filter_upwards [hb,
    tendsto_log_log_nat_atTop.eventually (eventually_ge_atTop 0)] with N hN hlog
  simpa only [Real.norm_eq_abs, Real.norm_of_nonneg hlog] using hN

/-- The rounded cutoff is `O(log N)`. -/
lemma cutoffSize_isBigO_log {g : ℕ → ℝ}
    (hg : Tendsto (fun N ↦ g N / Real.log (Real.log (N : ℝ))) atTop (𝓝 0)) :
    (fun N : ℕ ↦ (cutoffSize g N : ℝ)) =O[atTop]
      (fun N : ℕ ↦ Real.log (N : ℝ)) := by
  have hbase : (fun N : ℕ ↦ Real.log (N : ℝ) / Real.log 2) =O[atTop]
      (fun N : ℕ ↦ Real.log (N : ℝ)) := by
    simpa only [div_eq_mul_inv, mul_comm] using
      Asymptotics.isBigO_const_mul_self (Real.log 2)⁻¹
        (fun N : ℕ ↦ Real.log (N : ℝ)) atTop
  have hraw : (fun N : ℕ ↦ cutoffArgument g N) =O[atTop]
      (fun N : ℕ ↦ Real.log (N : ℝ)) := by
    simpa only [cutoffArgument] using hbase.add (isLittleO_log_of_tendsto_div hg).isBigO
  rcases Asymptotics.isBigO_iff.mp hraw with ⟨c, hc⟩
  refine Asymptotics.IsBigO.of_bound (c + 1) ?_
  filter_upwards [hc, tendsto_log_nat_atTop.eventually (eventually_ge_atTop 1)]
      with N hrawN hlog
  have hceil : (cutoffSize g N : ℝ) ≤ |cutoffArgument g N| + 1 := by
    by_cases harg : 0 ≤ cutoffArgument g N
    · exact (Nat.ceil_lt_add_one harg).le.trans
        (add_le_add_left (le_abs_self (cutoffArgument g N)) 1)
    · have hz : cutoffSize g N = 0 := by
        rw [cutoffSize, Nat.ceil_eq_zero]
        exact le_of_not_ge harg
      rw [hz, Nat.cast_zero]
      positivity
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _), Real.norm_of_nonneg (by linarith :
    0 ≤ Real.log (N : ℝ))]
  calc
    (cutoffSize g N : ℝ) ≤ |cutoffArgument g N| + 1 := hceil
    _ ≤ c * Real.log (N : ℝ) + 1 := by
      simpa only [Real.norm_eq_abs, Real.norm_of_nonneg (by linarith :
        0 ≤ Real.log (N : ℝ))] using add_le_add_left hrawN 1
    _ ≤ (c + 1) * Real.log (N : ℝ) := by nlinarith

/-- A smaller real power is little-oh of a larger one at infinity. -/
lemma isLittleO_rpow_rpow_atTop {a b : ℝ} (hab : a < b) :
    (fun x : ℝ ↦ x ^ a) =o[atTop] (fun x : ℝ ↦ x ^ b) := by
  rw [Asymptotics.isLittleO_iff_tendsto']
  · refine (tendsto_rpow_neg_atTop (sub_pos.mpr hab)).congr' ?_
    filter_upwards [eventually_gt_atTop 0] with x hx
    rw [← Real.rpow_sub hx]
    congr 2
    ring
  · filter_upwards [eventually_gt_atTop 0] with x hx
    intro hzero
    exact ((Real.rpow_pos_of_pos hx b).ne' hzero).elim

/-- The preceding real-power comparison, restricted to `log N`. -/
lemma isLittleO_log_rpow_log_rpow_nat {a b : ℝ} (hab : a < b) :
    (fun N : ℕ ↦ Real.log (N : ℝ) ^ a) =o[atTop]
      (fun N : ℕ ↦ Real.log (N : ℝ) ^ b) := by
  simpa [Function.comp_def] using
    (isLittleO_rpow_rpow_atTop hab).comp_tendsto tendsto_log_nat_atTop

/-- The unrounded main term is eventually positive.  Thus the natural
ceiling agrees with the ordinary upward rounding in the asymptotic range. -/
lemma eventually_cutoffArgument_pos {g : ℕ → ℝ}
    (hg : Tendsto (fun N ↦ g N / Real.log (Real.log (N : ℝ))) atTop (𝓝 0)) :
    ∀ᶠ N : ℕ in atTop, 0 < cutoffArgument g N := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hcoeff : 0 < (1 : ℝ) / (2 * Real.log 2) := by positivity
  have hb := (isLittleO_log_of_tendsto_div hg).bound hcoeff
  filter_upwards [hb, tendsto_log_nat_atTop.eventually (eventually_gt_atTop 0)]
      with N hN hlog
  rw [Real.norm_eq_abs, Real.norm_of_nonneg hlog.le] at hN
  have heq : Real.log (N : ℝ) / Real.log 2 =
      2 * ((1 / (2 * Real.log 2)) * Real.log (N : ℝ)) := by
    field_simp
  have htermpos : 0 < (1 / (2 * Real.log 2)) * Real.log (N : ℝ) :=
    mul_pos hcoeff hlog
  rw [cutoffArgument, heq]
  linarith [neg_abs_le (g N)]

/-- Quantitative consequence of the ceiling estimate: for every positive
`ε`, eventually `2^k/N ≤ 2 (log N)^ε`. -/
lemma eventually_pow_cutoff_div_le_log_rpow {g : ℕ → ℝ}
    (hg : Tendsto (fun N ↦ g N / Real.log (Real.log (N : ℝ))) atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      (2 : ℝ) ^ cutoffSize g N / (N : ℝ) ≤
        2 * Real.log (N : ℝ) ^ ε := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hcoeff : 0 < ε / Real.log 2 := div_pos hε hlog2
  filter_upwards [eventually_abs_le_mul_loglog hg hcoeff,
      eventually_cutoffArgument_pos hg,
      tendsto_log_nat_atTop.eventually (eventually_gt_atTop 0),
      eventually_gt_atTop (0 : ℕ)] with N hgN harg hlog hN
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
  have hceil : (cutoffSize g N : ℝ) < cutoffArgument g N + 1 := by
    exact Nat.ceil_lt_add_one harg.le
  have hgmul : g N * Real.log 2 ≤
      ε * Real.log (Real.log (N : ℝ)) := by
    calc
      g N * Real.log 2 ≤ |g N| * Real.log 2 :=
        mul_le_mul_of_nonneg_right (le_abs_self (g N)) hlog2.le
      _ ≤ (ε / Real.log 2 * Real.log (Real.log (N : ℝ))) * Real.log 2 :=
        mul_le_mul_of_nonneg_right hgN hlog2.le
      _ = ε * Real.log (Real.log (N : ℝ)) := by field_simp
  have hexponent : (cutoffSize g N : ℝ) * Real.log 2 - Real.log (N : ℝ) ≤
      ε * Real.log (Real.log (N : ℝ)) + Real.log 2 := by
    have hm := mul_lt_mul_of_pos_right hceil hlog2
    rw [cutoffArgument] at hm
    have hcancel : Real.log (N : ℝ) / Real.log 2 * Real.log 2 =
        Real.log (N : ℝ) := by field_simp
    rw [add_mul, add_mul, hcancel, one_mul] at hm
    nlinarith
  calc
    (2 : ℝ) ^ cutoffSize g N / (N : ℝ) =
        Real.exp ((cutoffSize g N : ℝ) * Real.log 2) /
          Real.exp (Real.log (N : ℝ)) := by
      rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2),
        Real.exp_log hNreal]
    _ = Real.exp ((cutoffSize g N : ℝ) * Real.log 2 - Real.log (N : ℝ)) := by
      rw [Real.exp_sub]
    _ ≤ Real.exp (ε * Real.log (Real.log (N : ℝ)) + Real.log 2) := by
      exact Real.exp_le_exp.mpr hexponent
    _ = 2 * Real.log (N : ℝ) ^ ε := by
      rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2),
        Real.rpow_def_of_pos hlog]
      rw [show ε * Real.log (Real.log (N : ℝ)) =
        Real.log (Real.log (N : ℝ)) * ε by ring]
      ring

/-- The collision parameter is nonnegative, including at `N = 0` under
Lean's totalized division. -/
lemma collisionParameter_nonneg (g : ℕ → ℝ) (N : ℕ) :
    0 ≤ collisionParameter g N := by
  rw [collisionParameter]
  have hp : (1 : ℝ) ≤ (2 : ℝ) ^ cutoffSize g N := by
    exact one_le_pow₀ (by norm_num)
  exact div_nonneg (sub_nonneg.mpr hp) (Nat.cast_nonneg N)

/-- The same quantitative upper bound holds for `(2^k-1)/N`. -/
lemma eventually_collisionParameter_le_log_rpow {g : ℕ → ℝ}
    (hg : Tendsto (fun N ↦ g N / Real.log (Real.log (N : ℝ))) atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      collisionParameter g N ≤ 2 * Real.log (N : ℝ) ^ ε := by
  filter_upwards [eventually_pow_cutoff_div_le_log_rpow hg hε]
      with N hN
  apply le_trans _ hN
  rw [collisionParameter]
  exact div_le_div_of_nonneg_right (sub_le_self _ zero_le_one) (Nat.cast_nonneg N)

/-- For every positive exponent, the collision parameter is
`O((log N)^ε)`. -/
lemma collisionParameter_isBigO_log_rpow {g : ℕ → ℝ}
    (hg : Tendsto (fun N ↦ g N / Real.log (Real.log (N : ℝ))) atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    (collisionParameter g) =O[atTop]
      (fun N : ℕ ↦ Real.log (N : ℝ) ^ ε) := by
  refine Asymptotics.IsBigO.of_bound 2 ?_
  filter_upwards [eventually_collisionParameter_le_log_rpow hg hε,
      tendsto_log_nat_atTop.eventually (eventually_ge_atTop 0)] with N hN hlog
  rw [Real.norm_of_nonneg (collisionParameter_nonneg g N),
    Real.norm_of_nonneg (Real.rpow_nonneg hlog _)]
  exact hN

/-- In particular, the collision parameter is `o(log N)`. -/
lemma collisionParameter_isLittleO_log {g : ℕ → ℝ}
    (hg : Tendsto (fun N ↦ g N / Real.log (Real.log (N : ℝ))) atTop (𝓝 0)) :
    (collisionParameter g) =o[atTop]
      (fun N : ℕ ↦ Real.log (N : ℝ)) := by
  have h := (collisionParameter_isBigO_log_rpow hg
      (ε := (1 : ℝ) / 2) (by norm_num)).trans_isLittleO
    (isLittleO_log_rpow_log_rpow_nat
      (a := (1 : ℝ) / 2) (b := 1) (by norm_num))
  simpa only [Real.rpow_one] using h

/-- The stronger power saving used in the probabilistic estimates:
`λ = o((log N)^(1/3))`. -/
lemma collisionParameter_isLittleO_log_rpow_one_third {g : ℕ → ℝ}
    (hg : Tendsto (fun N ↦ g N / Real.log (Real.log (N : ℝ))) atTop (𝓝 0)) :
    (collisionParameter g) =o[atTop]
      (fun N : ℕ ↦ Real.log (N : ℝ) ^ ((1 : ℝ) / 3)) := by
  exact (collisionParameter_isBigO_log_rpow hg
      (ε := (1 : ℝ) / 6) (by norm_num)).trans_isLittleO
    (isLittleO_log_rpow_log_rpow_nat
      (a := (1 : ℝ) / 6) (b := (1 : ℝ) / 3) (by norm_num))

/-- A logarithmic formulation of `exp λ = N^o(1)`. -/
lemma exp_collisionParameter_log_ratio_tendsto_zero {g : ℕ → ℝ}
    (hg : Tendsto (fun N ↦ g N / Real.log (Real.log (N : ℝ))) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ ↦
      Real.log (Real.exp (collisionParameter g N)) / Real.log (N : ℝ))
      atTop (𝓝 0) := by
  have hratio : Tendsto
      (fun N : ℕ ↦ collisionParameter g N / Real.log (N : ℝ))
      atTop (𝓝 0) := by
    rw [← Asymptotics.isLittleO_iff_tendsto']
    · exact collisionParameter_isLittleO_log hg
    · filter_upwards [tendsto_log_nat_atTop.eventually (eventually_gt_atTop 0)]
        with N hN
      exact fun hzero ↦ (hN.ne' hzero).elim
  simpa only [Real.log_exp] using hratio

/-- A direct eventual-power version of `exp λ = N^o(1)`: every fixed
positive power of `N` eventually dominates `exp λ`. -/
lemma eventually_exp_collisionParameter_le_rpow {g : ℕ → ℝ}
    (hg : Tendsto (fun N ↦ g N / Real.log (Real.log (N : ℝ))) atTop (𝓝 0))
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in atTop,
      Real.exp (collisionParameter g N) ≤ (N : ℝ) ^ δ := by
  have hb := (collisionParameter_isLittleO_log hg).bound hδ
  filter_upwards [hb, tendsto_log_nat_atTop.eventually (eventually_gt_atTop 0),
      eventually_gt_atTop (0 : ℕ)] with N hN hlog hNnat
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hNnat
  rw [Real.norm_of_nonneg (collisionParameter_nonneg g N),
    Real.norm_of_nonneg hlog.le] at hN
  calc
    Real.exp (collisionParameter g N) ≤
        Real.exp (δ * Real.log (N : ℝ)) := Real.exp_le_exp.mpr hN
    _ = (N : ℝ) ^ δ := by
      rw [Real.rpow_def_of_pos hNreal]
      congr 1
      ring

/-- The cutoff estimate remains valid after restriction to any unbounded
natural-number sequence (in particular, an increasing enumeration of the
primes). -/
lemma cutoffSize_comp_isBigO_log {g : ℕ → ℝ}
    (hg : Tendsto (fun N ↦ g N / Real.log (Real.log (N : ℝ))) atTop (𝓝 0))
    {u : ℕ → ℕ} (hu : Tendsto u atTop atTop) :
    (fun n : ℕ ↦ (cutoffSize g (u n) : ℝ)) =O[atTop]
      (fun n : ℕ ↦ Real.log (u n : ℝ)) := by
  simpa [Function.comp_def] using (cutoffSize_isBigO_log hg).comp_tendsto hu

/-- The `o((log N)^(1/3))` estimate also restricts to every unbounded
sequence, hence to the primes used in the cyclic obstruction. -/
lemma collisionParameter_comp_isLittleO_log_rpow_one_third {g : ℕ → ℝ}
    (hg : Tendsto (fun N ↦ g N / Real.log (Real.log (N : ℝ))) atTop (𝓝 0))
    {u : ℕ → ℕ} (hu : Tendsto u atTop atTop) :
    (fun n : ℕ ↦ collisionParameter g (u n)) =o[atTop]
      (fun n : ℕ ↦ Real.log (u n : ℝ) ^ ((1 : ℝ) / 3)) := by
  simpa [Function.comp_def] using
    (collisionParameter_isLittleO_log_rpow_one_third hg).comp_tendsto hu

end Erdos543
