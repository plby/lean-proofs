import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Normed.Algebra.Exponential

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open Finset Real

namespace CofiniteDerivatives

/-- The coefficient `sqrt ((n + m)!) / m! * r^m` for the case `beta = 1 / 2`. -/
noncomputable def saddleCoeff (n m : ℕ) (r : ℝ) : ℝ :=
  √(Nat.factorial (n + m) : ℝ) / (Nat.factorial m : ℝ) * r ^ m

/-- `saddleCoeff` after removing the common factor `sqrt (n!)`. -/
noncomputable def normalizedSaddleCoeff (n m : ℕ) (r : ℝ) : ℝ :=
  √((n + 1).ascFactorial m : ℝ) / (Nat.factorial m : ℝ) * r ^ m

/-- The sum of the normalized saddle coefficients. -/
noncomputable def normalizedSaddleSeries (n : ℕ) (r : ℝ) : ℝ :=
  ∑' m : ℕ, normalizedSaddleCoeff n m r

/-- The full series of coefficients `sqrt ((n + m)!) / m! * r^m`. -/
noncomputable def saddleSeries (n : ℕ) (r : ℝ) : ℝ :=
  ∑' m : ℕ, saddleCoeff n m r

theorem saddleCoeff_eq_sqrt_factorial_mul_normalized (n m : ℕ) (r : ℝ) :
    saddleCoeff n m r = √(Nat.factorial n : ℝ) * normalizedSaddleCoeff n m r := by
  have hsqrt :
      √(Nat.factorial (n + m) : ℝ) =
        √(Nat.factorial n : ℝ) * √((n + 1).ascFactorial m : ℝ) := by
    rw [← Real.sqrt_mul (by positivity), ← Nat.cast_mul,
      Nat.factorial_mul_ascFactorial]
  rw [saddleCoeff, normalizedSaddleCoeff, hsqrt]
  ring

theorem saddleSeries_eq_sqrt_factorial_mul_normalized (n : ℕ) (r : ℝ) :
  saddleSeries n r = √(Nat.factorial n : ℝ) * normalizedSaddleSeries n r := by
  rw [saddleSeries, normalizedSaddleSeries, ← tsum_mul_left]
  exact tsum_congr fun m ↦ saddleCoeff_eq_sqrt_factorial_mul_normalized n m r

private theorem sqrt_pow_of_nonneg (x : ℝ) (hx : 0 ≤ x) :
    ∀ m : ℕ, √(x ^ m) = √x ^ m
  | 0 => by simp
  | m + 1 => by
      rw [pow_succ, Real.sqrt_mul (pow_nonneg hx m), sqrt_pow_of_nonneg x hx m,
        pow_succ]

/-- Each normalized coefficient dominates the corresponding Poisson term with parameter
`r * sqrt n`. -/
theorem poissonTerm_le_normalizedSaddleCoeff (n m : ℕ) {r : ℝ} (hr : 0 ≤ r) :
  (r * √(n : ℝ)) ^ m / (Nat.factorial m : ℝ) ≤ normalizedSaddleCoeff n m r := by
  have hnat : n ^ m ≤ (n + 1).ascFactorial m :=
    (Nat.pow_le_pow_left (Nat.le_succ n) m).trans
      (Nat.pow_succ_le_ascFactorial (n + 1) m)
  have hcast : (n : ℝ) ^ m ≤ ((n + 1).ascFactorial m : ℝ) := by
    exact_mod_cast hnat
  have hsqrt : √((n : ℝ) ^ m) ≤ √((n + 1).ascFactorial m : ℝ) :=
    Real.sqrt_le_sqrt hcast
  calc
    (r * √(n : ℝ)) ^ m / (Nat.factorial m : ℝ) =
        r ^ m * √((n : ℝ) ^ m) / (Nat.factorial m : ℝ) := by
      rw [mul_pow, sqrt_pow_of_nonneg (n : ℝ) (by positivity)]
    _ ≤ r ^ m * √((n + 1).ascFactorial m : ℝ) / (Nat.factorial m : ℝ) := by
      gcongr
    _ = normalizedSaddleCoeff n m r := by
      rw [normalizedSaddleCoeff]
      ring

/-- A coarse global upper Stirling bound, with the correct logarithmic error. -/
theorem log_factorial_le_coarse_stirling {m : ℕ} (hm : m ≠ 0) :
  Real.log (Nat.factorial m : ℝ) ≤
      (m : ℝ) * Real.log m - m + Real.log m / 2 + 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := Nat.exists_eq_succ_of_ne_zero hm
  have hseq : Real.log (Stirling.stirlingSeq (k + 1)) ≤
      Real.log (Stirling.stirlingSeq 1) :=
    Stirling.log_stirlingSeq'_antitone (Nat.zero_le k)
  rw [Stirling.log_stirlingSeq_formula, Stirling.stirlingSeq_one] at hseq
  have hlog_mul : Real.log (2 * (k + 1 : ℝ)) =
      Real.log 2 + Real.log (k + 1 : ℝ) := by
    rw [Real.log_mul] <;> positivity
  have hlog_inner : Real.log ((k + 1 : ℝ) / Real.exp 1) =
      Real.log (k + 1 : ℝ) - 1 := by
    rw [Real.log_div, Real.log_exp] <;> positivity
  have hlog_rhs : Real.log (Real.exp 1 / √2) = 1 - Real.log 2 / 2 := by
    rw [Real.log_div, Real.log_exp, Real.log_sqrt] <;> positivity
  push_cast at hseq ⊢
  rw [hlog_mul, hlog_inner, hlog_rhs] at hseq
  ring_nf at hseq ⊢
  linarith

/-- Binomial form of the normalized coefficient. -/
theorem normalizedSaddleCoeff_eq_sqrt_choose_div (n m : ℕ) (r : ℝ) :
    normalizedSaddleCoeff n m r =
  √(((n + m).choose n : ℝ) / (Nat.factorial m : ℝ)) * r ^ m := by
  rw [normalizedSaddleCoeff, Nat.ascFactorial_eq_factorial_mul_choose,
    Nat.cast_mul, Real.sqrt_mul (by positivity), ← Nat.choose_symm_add,
    Real.sqrt_div (by positivity)]
  have hsqrt : 0 < √(Nat.factorial m : ℝ) := by positivity
  field_simp
  rw [Real.sq_sqrt (by positivity)]
  ring

/-- At `m = floor (r * sqrt n)`, the logarithm of the normalized coefficient has leading term
`r * sqrt n`, with an explicit logarithmic loss. The hypotheses hold eventually when `r` ranges
in a fixed compact subset of `(0, ∞)`. -/
theorem log_normalizedSaddleCoeff_floor_lower (n : ℕ) {r : ℝ} (hr : 0 ≤ r)
    (hx : 1 ≤ r * √(n : ℝ)) (hrn : r ≤ √(n : ℝ)) :
    r * √(n : ℝ) - 2 - Real.log n / 2 ≤
      Real.log (normalizedSaddleCoeff n ⌊r * √(n : ℝ)⌋₊ r) := by
  let x : ℝ := r * √(n : ℝ)
  let m : ℕ := ⌊x⌋₊
  have hx_pos : 0 < x := zero_lt_one.trans_le hx
  have hm_pos : 0 < m := (Nat.floor_pos).2 hx
  have hm_ne : m ≠ 0 := hm_pos.ne'
  have hm_le_x : (m : ℝ) ≤ x := Nat.floor_le hx_pos.le
  have hx_sub_one_lt_m : x - 1 < (m : ℝ) := Nat.sub_one_lt_floor x
  have hx_le_n : x ≤ (n : ℝ) := by
    calc
      x = r * √(n : ℝ) := rfl
      _ ≤ √(n : ℝ) * √(n : ℝ) := by gcongr
      _ = n := Real.mul_self_sqrt (by positivity)
  have hm_le_n : (m : ℝ) ≤ (n : ℝ) := hm_le_x.trans hx_le_n
  have hlog_m_le_x : Real.log m ≤ Real.log x :=
    Real.log_le_log (by positivity) hm_le_x
  have hlog_m_le_n : Real.log m ≤ Real.log n :=
    Real.log_le_log (by positivity) hm_le_n
  have hmul_log : (m : ℝ) * Real.log m ≤ (m : ℝ) * Real.log x := by
    gcongr
  have hfactorial := log_factorial_le_coarse_stirling hm_ne
  have hcoeff := poissonTerm_le_normalizedSaddleCoeff n m hr
  have hpoisson_pos : 0 < x ^ m / (Nat.factorial m : ℝ) := by positivity
  have hlog_coeff := Real.log_le_log hpoisson_pos (by simpa [x, m] using! hcoeff)
  rw [Real.log_div (pow_ne_zero _ hx_pos.ne') (by positivity), Real.log_pow] at hlog_coeff
  dsimp only [x, m] at hlog_coeff ⊢
  linarith

/-- Cauchy--Schwarz majorant for the full normalized series. The first square-root factor is a
negative-binomial series and the second is an exponential series. -/
theorem normalizedSaddleSeries_summable_and_le_cauchySchwarz (n : ℕ) {r t : ℝ}
    (hr : 0 ≤ r) (ht : 0 < t) (ht1 : t < 1) :
    Summable (fun m : ℕ ↦ normalizedSaddleCoeff n m r) ∧
      normalizedSaddleSeries n r ≤
        √((1 / (1 - t)) ^ (n + 1)) * √(Real.exp (r ^ 2 / t)) := by
  let A : ℕ → ℝ := fun m ↦ ((n + m).choose n : ℝ) * t ^ m
  let B : ℕ → ℝ := fun m ↦ (r ^ 2 / t) ^ m / (Nat.factorial m : ℝ)
  let f : ℕ → ℝ := fun m ↦ √(A m)
  let g : ℕ → ℝ := fun m ↦ √(B m)
  have hA_nonneg (m : ℕ) : 0 ≤ A m := by
    dsimp only [A]
    positivity
  have hB_nonneg (m : ℕ) : 0 ≤ B m := by
    dsimp only [B]
    positivity
  have ht_norm : ‖t‖ < 1 := by simpa [Real.norm_eq_abs, abs_of_pos ht] using! ht1
  have hA_sum : HasSum A ((1 / (1 - t)) ^ (n + 1)) := by
    simpa only [A, Nat.add_comm, one_div, inv_pow] using!
      (hasSum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℝ) n ht_norm)
  have hB_sum : HasSum B (Real.exp (r ^ 2 / t)) := by
    rw [Real.exp_eq_exp_ℝ]
    simpa only [B] using! (NormedSpace.expSeries_div_hasSum_exp (r ^ 2 / t : ℝ))
  have hf_sq (m : ℕ) : f m ^ (2 : ℝ) = A m := by
    rw [Real.rpow_two]
    exact Real.sq_sqrt (hA_nonneg m)
  have hg_sq (m : ℕ) : g m ^ (2 : ℝ) = B m := by
    rw [Real.rpow_two]
    exact Real.sq_sqrt (hB_nonneg m)
  have hf_sum : Summable (fun m ↦ f m ^ (2 : ℝ)) :=
    hA_sum.summable.congr fun m ↦ (hf_sq m).symm
  have hg_sum : Summable (fun m ↦ g m ^ (2 : ℝ)) :=
    hB_sum.summable.congr fun m ↦ (hg_sq m).symm
  have hcoeff (m : ℕ) : normalizedSaddleCoeff n m r = f m * g m := by
    have hleft : 0 ≤ normalizedSaddleCoeff n m r := by
      rw [normalizedSaddleCoeff]
      positivity
    have hright : 0 ≤ f m * g m := by
      dsimp only [f, g]
      positivity
    have hsquare : (normalizedSaddleCoeff n m r) ^ 2 = (f m * g m) ^ 2 := by
      rw [normalizedSaddleCoeff_eq_sqrt_choose_div, mul_pow,
        Real.sq_sqrt (div_nonneg (by positivity) (by positivity)), mul_pow]
      change (((n + m).choose n : ℝ) / (Nat.factorial m : ℝ)) * (r ^ m) ^ 2 =
        (√(A m)) ^ 2 * (√(B m)) ^ 2
      rw [Real.sq_sqrt (hA_nonneg m), Real.sq_sqrt (hB_nonneg m)]
      dsimp only [A, B]
      rw [div_pow]
      field_simp [ht.ne', pow_ne_zero m ht.ne']
      simp only [← pow_mul, Nat.mul_comm]
    nlinarith
  have hf_tsum : ∑' m, f m ^ (2 : ℝ) = (1 / (1 - t)) ^ (n + 1) :=
    (tsum_congr hf_sq).trans hA_sum.tsum_eq
  have hg_tsum : ∑' m, g m ^ (2 : ℝ) = Real.exp (r ^ 2 / t) :=
    (tsum_congr hg_sq).trans hB_sum.tsum_eq
  have hcs := Real.summable_and_inner_le_Lp_mul_Lq_tsum_of_nonneg
    (p := (2 : ℝ)) (q := (2 : ℝ)) Real.HolderConjugate.two_two
    (fun m ↦ Real.sqrt_nonneg (A m)) (fun m ↦ Real.sqrt_nonneg (B m)) hf_sum hg_sum
  constructor
  · exact hcs.1.congr fun m ↦ (hcoeff m).symm
  · calc
      normalizedSaddleSeries n r = ∑' m, f m * g m := by
        rw [normalizedSaddleSeries]
        exact tsum_congr hcoeff
      _ ≤ (∑' m, f m ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) *
          (∑' m, g m ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) := hcs.2
      _ = √((1 / (1 - t)) ^ (n + 1)) * √(Real.exp (r ^ 2 / t)) := by
        rw [hf_tsum, hg_tsum]
        simp only [Real.sqrt_eq_rpow]

/-- Explicit saddle upper bound. On `0 ≤ r ≤ R`, its correction is at most
`(R + R^2) / 2`, uniformly in `n`. -/
theorem normalizedSaddleSeries_le_exp (n : ℕ) {r : ℝ} (hn : n ≠ 0) (hr : 0 ≤ r) :
    normalizedSaddleSeries n r ≤
      Real.exp (r * √(n : ℝ) + (r + r ^ 2) / 2) := by
  obtain rfl | hr := hr.eq_or_lt
  · rw [normalizedSaddleSeries, tsum_eq_single 0]
    · simp [normalizedSaddleCoeff]
    · intro m hm
      simp [normalizedSaddleCoeff, hm]
  let s : ℝ := √(n : ℝ)
  let u : ℝ := r / s
  let t : ℝ := r / (r + s)
  have hs : 0 < s := by
    dsimp only [s]
    positivity
  have hs_one : 1 ≤ s := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt (by exact_mod_cast Nat.one_le_iff_ne_zero.2 hn)
  have hu : 0 < u := div_pos hr hs
  have ht : 0 < t := div_pos hr (add_pos hr hs)
  have ht1 : t < 1 := by
    rw [div_lt_one (add_pos hr hs)]
    linarith
  have hone : 1 / (1 - t) = 1 + u := by
    dsimp only [t, u]
    field_simp [hs.ne', hr.ne']
    ring
  have htwo : r ^ 2 / t = r * (r + s) := by
    dsimp only [t]
    field_simp [hr.ne', (add_pos hr hs).ne']
  have hseries :=
    (normalizedSaddleSeries_summable_and_le_cauchySchwarz n hr.le ht ht1).2
  rw [hone, htwo] at hseries
  refine hseries.trans ?_
  have hbase_pos : 0 < (1 + u) ^ (n + 1) := by positivity
  have hprod_pos :
      0 < √((1 + u) ^ (n + 1)) * √(Real.exp (r * (r + s))) := by
    positivity
  apply (Real.log_le_iff_le_exp hprod_pos).1
  have hlogu : Real.log (1 + u) ≤ u := by
    simpa using! Real.log_le_sub_one_of_pos (show 0 < 1 + u by positivity)
  have hs_sq : s ^ 2 = (n : ℝ) := by
    dsimp only [s]
    exact Real.sq_sqrt (by positivity)
  have hnu : ((n : ℝ) + 1) * u = r * s + u := by
    dsimp only [u]
    field_simp [hs.ne']
    nlinarith
  have hu_le_r : u ≤ r := by
    dsimp only [u]
    rw [div_le_iff₀ hs]
    nlinarith
  rw [Real.log_mul (by positivity) (by positivity), Real.log_sqrt hbase_pos.le,
    Real.log_pow, Real.log_sqrt (Real.exp_pos _).le, Real.log_exp]
  push_cast
  have hfirst : ((n : ℝ) + 1) * Real.log (1 + u) / 2 ≤
      r * s / 2 + r / 2 := by
    calc
      ((n : ℝ) + 1) * Real.log (1 + u) / 2 ≤
          ((n : ℝ) + 1) * u / 2 := by gcongr
      _ ≤ r * s / 2 + r / 2 := by linarith
  dsimp only [s] at hfirst ⊢
  nlinarith

theorem normalizedSaddleSeries_summable (n : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    Summable (fun m : ℕ ↦ normalizedSaddleCoeff n m r) :=
  (normalizedSaddleSeries_summable_and_le_cauchySchwarz n hr (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : (1 : ℝ) / 2 < 1)).1

theorem normalizedSaddleSeries_pos (n : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    0 < normalizedSaddleSeries n r := by
  have hsum := normalizedSaddleSeries_summable n hr
  have hle : normalizedSaddleCoeff n 0 r ≤ normalizedSaddleSeries n r := by
    rw [normalizedSaddleSeries]
    simpa using! hsum.sum_le_tsum ({0} : Finset ℕ) (fun m _ ↦ by
      rw [normalizedSaddleCoeff]
      positivity)
  have hzero : normalizedSaddleCoeff n 0 r = 1 := by
    rw [normalizedSaddleCoeff]
    simp
  rw [hzero] at hle
  exact zero_lt_one.trans_le hle

/-- The requested floor-witness lower bound in terms of the original coefficient. Equivalently,
after subtracting `log (n!) / 2`, the lower bound is `r * sqrt n - O(log n)`. -/
theorem log_saddleCoeff_floor_lower (n : ℕ) {r : ℝ} (hr : 0 ≤ r)
    (hx : 1 ≤ r * √(n : ℝ)) (hrn : r ≤ √(n : ℝ)) :
    Real.log (Nat.factorial n : ℝ) / 2 + r * √(n : ℝ) - 2 - Real.log n / 2 ≤
      Real.log (saddleCoeff n ⌊r * √(n : ℝ)⌋₊ r) := by
  have hr_pos : 0 < r := hr.lt_of_ne fun h ↦ by
    subst r
    norm_num at hx
  have hnormalized := log_normalizedSaddleCoeff_floor_lower n hr hx hrn
  rw [saddleCoeff_eq_sqrt_factorial_mul_normalized,
    Real.log_mul (by positivity) (by
      rw [normalizedSaddleCoeff]
      positivity), Real.log_sqrt (by positivity)]
  linarith

/-- Logarithmic upper saddle estimate for the normalized full series. -/
theorem log_normalizedSaddleSeries_le (n : ℕ) {r : ℝ} (hn : n ≠ 0) (hr : 0 ≤ r) :
    Real.log (normalizedSaddleSeries n r) ≤
      r * √(n : ℝ) + (r + r ^ 2) / 2 := by
  have hpos := normalizedSaddleSeries_pos n hr
  have hlog := Real.log_le_log hpos (normalizedSaddleSeries_le_exp n hn hr)
  simpa using! hlog

/-- Logarithmic upper saddle estimate for the original full series. -/
theorem log_saddleSeries_le (n : ℕ) {r : ℝ} (hn : n ≠ 0) (hr : 0 ≤ r) :
    Real.log (saddleSeries n r) ≤
  Real.log (Nat.factorial n : ℝ) / 2 + r * √(n : ℝ) + (r + r ^ 2) / 2 := by
  rw [saddleSeries_eq_sqrt_factorial_mul_normalized,
    Real.log_mul (by positivity) (normalizedSaddleSeries_pos n hr).ne',
    Real.log_sqrt (by positivity)]
  linarith [log_normalizedSaddleSeries_le n hn hr]

/-- Uniform version of the upper estimate on a fixed compact interval `0 ≤ r ≤ R`. -/
theorem log_saddleSeries_le_on_compact (n : ℕ) {r R : ℝ} (hn : n ≠ 0)
    (hr : 0 ≤ r) (hrR : r ≤ R) :
    Real.log (saddleSeries n r) ≤
  Real.log (Nat.factorial n : ℝ) / 2 + r * √(n : ℝ) + (R + R ^ 2) / 2 := by
  have hR : 0 ≤ R := hr.trans hrR
  have hcorrection : r + r ^ 2 ≤ R + R ^ 2 := by
    nlinarith [sq_nonneg (R - r)]
  linarith [log_saddleSeries_le n hn hr]

end CofiniteDerivatives
