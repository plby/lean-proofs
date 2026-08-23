/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos1166.Erdos1166Core

/-!
# The deterministic time change in HLOZ Appendix A

This file isolates the elementary interpolation surrounding the two genuine
probability estimates in Appendix A of Hao--Li--Okada--Zheng.  In particular,
all definitions of the auxiliary scales and all logarithmic/exponent
comparisons are internal; the disk-exit local-time estimate and the exit-time
tail are parameters of the final probability theorem.
-/

namespace Erdos1166.HLOZAppendixA

open Filter MeasureTheory Set
open scoped ENNReal Topology NNReal

/-- The disk scale `K_j = 16 e^j j^9` used in HLOZ Appendix A. -/
noncomputable def K (j : ℕ) : ℝ :=
  16 * Real.exp (j : ℝ) * (j : ℝ) ^ 9

/-- The deterministic time scale associated with `K j`. -/
noncomputable def J (ε : ℝ) (j : ℕ) : ℝ :=
  (K j * Real.exp (Real.log (K j) ^ (3 / 5 + ε : ℝ))) ^ 2

/-- A natural time at or above the real time scale `J ε j`. -/
noncomputable def Jnat (ε : ℝ) (j : ℕ) : ℕ :=
  ⌈J ε j⌉₊

/-- The disk-exit threshold appearing in (A.1). -/
noncomputable def diskThreshold (ε : ℝ) (j : ℕ) : ℝ :=
  4 / Real.pi * Real.log (K j) ^ 2 -
    Real.log (K j) ^ (8 / 5 + 2 * ε : ℝ)

/-- The lower threshold at natural time `n`. -/
noncomputable def naturalThreshold (ε : ℝ) (n : ℝ) : ℝ :=
  1 / Real.pi * Real.log n ^ 2 -
    Real.log n ^ (8 / 5 + 3 * ε : ℝ)

noncomputable def logProfile (p : ℝ) (t : ℝ) : ℝ :=
  1 / Real.pi * t ^ 2 - t ^ p

/-- For every exponent strictly between one and two, the logarithmic profile
`π⁻¹t²-tᵖ` is monotone once `t` is large. -/
lemma eventually_monotoneOn_logProfile {p : ℝ} (hp1 : 1 < p) (hp2 : p < 2) :
    ∃ T : ℝ, MonotoneOn (logProfile p) (Ici T) := by
  have hd : 0 < 2 - p := sub_pos.mpr hp2
  have hevPow : ∀ᶠ t : ℝ in atTop,
      Real.pi * p / 2 ≤ t ^ (2 - p) :=
    (tendsto_rpow_atTop hd) (Filter.eventually_ge_atTop (Real.pi * p / 2))
  have hevOne : ∀ᶠ t : ℝ in atTop, 1 ≤ t := Filter.eventually_ge_atTop 1
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp (hevPow.and hevOne)
  refine ⟨T, monotoneOn_of_deriv_nonneg (convex_Ici T)
    (by
      unfold logProfile
      exact ((continuous_const.mul (continuous_id.pow 2)).sub
        (continuous_id.rpow_const
          (fun _ => Or.inr (by linarith : 0 ≤ p)))).continuousOn)
    ?_ ?_⟩
  · intro x hx
    have hxT : T < x := by simpa only [interior_Ici, mem_Ioi] using hx
    have hx1 : 1 ≤ x := (hT x hxT.le).2
    have hxpos : 0 < x := zero_lt_one.trans_le hx1
    unfold logProfile
    exact (((differentiableAt_id.pow 2).const_mul (1 / Real.pi)).sub
      (Real.hasDerivAt_rpow_const (x := x) (p := p)
        (Or.inl hxpos.ne')).differentiableAt).differentiableWithinAt
  · intro x hx
    have hxT : T < x := by simpa only [interior_Ici, mem_Ioi] using hx
    have hxData := hT x hxT.le
    have hx1 : 1 ≤ x := hxData.2
    have hxpos : 0 < x := zero_lt_one.trans_le hx1
    have hz0 : 0 ≤ x ^ (p - 1) := Real.rpow_nonneg hxpos.le _
    have hfactor : x = x ^ (p - 1) * x ^ (2 - p) := by
      calc
        x = x ^ (1 : ℝ) := (Real.rpow_one x).symm
        _ = x ^ ((p - 1) + (2 - p)) := by congr 1 <;> ring
        _ = x ^ (p - 1) * x ^ (2 - p) := Real.rpow_add hxpos _ _
    have hpre : (Real.pi * p / 2) * x ^ (p - 1) ≤ x := by
      calc
        (Real.pi * p / 2) * x ^ (p - 1) ≤
            x ^ (p - 1) * x ^ (2 - p) := by
          simpa [mul_comm] using mul_le_mul_of_nonneg_left hxData.1 hz0
        _ = x := hfactor.symm
    have hderiv : p * x ^ (p - 1) ≤ 2 / Real.pi * x := by
      rw [show 2 / Real.pi * x = (2 * x) / Real.pi by ring,
        le_div_iff₀ Real.pi_pos]
      nlinarith
    have hsq := ((hasDerivAt_id x).pow 2).const_mul (1 / Real.pi)
    have hrpow := Real.hasDerivAt_rpow_const (x := x) (p := p) (Or.inl hxpos.ne')
    have heq := (hsq.sub hrpow).deriv
    have hfun :
        (fun y : ℝ => 1 / Real.pi * (id ^ 2) y) - (fun y : ℝ => y ^ p) =
          logProfile p := by
      funext y
      rfl
    rw [hfun] at heq
    have heq' : deriv (logProfile p) x =
        2 / Real.pi * x - p * x ^ (p - 1) := by
      norm_num [id_eq] at heq
      convert heq using 1 <;> ring
    rw [heq']
    exact sub_nonneg.mpr hderiv

lemma K_pos {j : ℕ} (hj : 1 ≤ j) : 0 < K j := by
  unfold K
  positivity

lemma log_K {j : ℕ} (hj : 1 ≤ j) :
    Real.log (K j) = Real.log 16 + j + 9 * Real.log j := by
  have hjR : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
  rw [K, Real.log_mul
    (mul_ne_zero (by norm_num : (16 : ℝ) ≠ 0) (Real.exp_ne_zero _))
    (pow_ne_zero _ hjR.ne'),
    Real.log_mul (by norm_num : (16 : ℝ) ≠ 0) (Real.exp_ne_zero _),
    Real.log_exp, Real.log_pow]
  norm_num

lemma one_le_log_K {j : ℕ} (hj : 1 ≤ j) : 1 ≤ Real.log (K j) := by
  rw [log_K hj]
  have hlog16 : 1 < Real.log 16 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num)]
    exact Real.exp_one_lt_d9.trans (by norm_num)
  have hlogj : 0 ≤ Real.log (j : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hj)
  linarith

lemma nat_le_log_K {j : ℕ} (hj : 1 ≤ j) : (j : ℝ) ≤ Real.log (K j) := by
  rw [log_K hj]
  have hlog16 : 0 ≤ Real.log 16 := Real.log_nonneg (by norm_num)
  have hlogj : 0 ≤ Real.log (j : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hj)
  linarith

lemma log_K_succ_le_two_mul {j : ℕ} (hj : 10 ≤ j) :
    Real.log (K (j + 1)) ≤ 2 * Real.log (K j) := by
  have hj1 : 1 ≤ j := by omega
  have hjs1 : 1 ≤ j + 1 := by omega
  rw [log_K hj1, log_K hjs1]
  have hjR : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
  have hsucc_le : ((j + 1 : ℕ) : ℝ) ≤ 2 * (j : ℝ) := by
    exact_mod_cast (show j + 1 ≤ 2 * j by omega)
  have hlog_succ : Real.log ((j + 1 : ℕ) : ℝ) ≤
      Real.log (2 * (j : ℝ)) :=
    Real.strictMonoOn_log.monotoneOn
      (by simp only [Set.mem_Ioi]; positivity)
      (by simp only [Set.mem_Ioi]; positivity) hsucc_le
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hjR.ne'] at hlog_succ
  have hlogtwo : Real.log 2 ≤ 1 := by
    convert Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2) using 1 <;>
      norm_num
  have hj10 : (10 : ℝ) ≤ j := by exact_mod_cast hj
  have hlog16 : 0 ≤ Real.log 16 := Real.log_nonneg (by norm_num)
  have hlogj : 0 ≤ Real.log (j : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hj1)
  norm_num [Nat.cast_add, Nat.cast_one] at hlog_succ ⊢
  linarith

lemma log_K_le_log_K_succ {j : ℕ} (hj : 1 ≤ j) :
    Real.log (K j) ≤ Real.log (K (j + 1)) := by
  rw [log_K hj, log_K (by omega : 1 ≤ j + 1)]
  have hjR : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
  have hcast : (j : ℝ) ≤ (j + 1 : ℕ) := by exact_mod_cast Nat.le_succ j
  have hlog : Real.log (j : ℝ) ≤ Real.log ((j + 1 : ℕ) : ℝ) :=
    Real.strictMonoOn_log.monotoneOn
      (by simp only [Set.mem_Ioi]; positivity)
      (by simp only [Set.mem_Ioi]; positivity) hcast
  norm_num [Nat.cast_add, Nat.cast_one] at hlog ⊢
  linarith

lemma log_K_mono {i j : ℕ} (hi : 1 ≤ i) (hij : i ≤ j) :
    Real.log (K i) ≤ Real.log (K j) := by
  have hj : 1 ≤ j := hi.trans hij
  rw [log_K hi, log_K hj]
  have hiR : (0 : ℝ) < i := by exact_mod_cast (show 0 < i by omega)
  have hijR : (i : ℝ) ≤ j := by exact_mod_cast hij
  have hlog : Real.log (i : ℝ) ≤ Real.log (j : ℝ) :=
    Real.strictMonoOn_log.monotoneOn
      (by simp only [Set.mem_Ioi]; positivity)
      (by simp only [Set.mem_Ioi]; positivity) hijR
  have hijCast : (i : ℝ) ≤ j := by exact_mod_cast hij
  linarith

lemma K_mono {i j : ℕ} (hi : 1 ≤ i) (hij : i ≤ j) : K i ≤ K j := by
  calc
    K i = Real.exp (Real.log (K i)) := (Real.exp_log (K_pos hi)).symm
    _ ≤ Real.exp (Real.log (K j)) := Real.exp_le_exp.mpr (log_K_mono hi hij)
    _ = K j := Real.exp_log (K_pos (hi.trans hij))

lemma J_mono {ε : ℝ} (hε : 0 < ε) {i j : ℕ} (hi : 1 ≤ i) (hij : i ≤ j) :
    J ε i ≤ J ε j := by
  have hj : 1 ≤ j := hi.trans hij
  have hK := K_mono hi hij
  have hlog := log_K_mono hi hij
  have hpow : Real.log (K i) ^ (3 / 5 + ε : ℝ) ≤
      Real.log (K j) ^ (3 / 5 + ε : ℝ) :=
    Real.rpow_le_rpow (zero_le_one.trans (one_le_log_K hi)) hlog (by positivity)
  have hexp := Real.exp_le_exp.mpr hpow
  have hprod :
      K i * Real.exp (Real.log (K i) ^ (3 / 5 + ε : ℝ)) ≤
        K j * Real.exp (Real.log (K j) ^ (3 / 5 + ε : ℝ)) :=
    mul_le_mul hK hexp (Real.exp_pos _).le (K_pos hj).le
  unfold J
  exact pow_le_pow_left₀ (mul_pos (K_pos hi) (Real.exp_pos _)).le hprod 2

lemma Jnat_mono {ε : ℝ} (hε : 0 < ε) {i j : ℕ} (hi : 1 ≤ i) (hij : i ≤ j) :
    Jnat ε i ≤ Jnat ε j := by
  exact Nat.ceil_mono (J_mono hε hi hij)

lemma log_K_succ_le_add_ten {j : ℕ} (hj : 1 ≤ j) :
    Real.log (K (j + 1)) ≤ Real.log (K j) + 10 := by
  rw [log_K hj, log_K (by omega : 1 ≤ j + 1)]
  have hjR : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
  have hsucc_le : ((j + 1 : ℕ) : ℝ) ≤ 2 * (j : ℝ) := by
    exact_mod_cast (show j + 1 ≤ 2 * j by omega)
  have hlog_succ : Real.log ((j + 1 : ℕ) : ℝ) ≤
      Real.log (2 * (j : ℝ)) :=
    Real.strictMonoOn_log.monotoneOn
      (by simp only [Set.mem_Ioi]; positivity)
      (by simp only [Set.mem_Ioi]; positivity) hsucc_le
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hjR.ne'] at hlog_succ
  have hlogtwo : Real.log 2 ≤ 1 := by
    convert Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2) using 1 <;>
      norm_num
  norm_num [Nat.cast_add, Nat.cast_one] at hlog_succ ⊢
  linarith

lemma log_J {ε : ℝ} {j : ℕ} (hj : 1 ≤ j) :
    Real.log (J ε j) =
      2 * (Real.log (K j) + Real.log (K j) ^ (3 / 5 + ε : ℝ)) := by
  have hK : 0 < K j := K_pos hj
  have hexp : 0 < Real.exp (Real.log (K j) ^ (3 / 5 + ε : ℝ)) := Real.exp_pos _
  rw [J, Real.log_pow, Real.log_mul hK.ne' hexp.ne', Real.log_exp]
  norm_num

lemma log_J_succ_bounds {ε : ℝ} (hε : 0 < ε) (hεsmall : ε ≤ 2 / 5)
    {j : ℕ} (hj : 1 ≤ j) :
    2 * Real.log (K j) ≤ Real.log (J ε (j + 1)) ∧
      Real.log (J ε (j + 1)) ≤
        2 * Real.log (K j) +
          42 * Real.log (K j) ^ (3 / 5 + ε : ℝ) := by
  let L : ℝ := Real.log (K j)
  let L' : ℝ := Real.log (K (j + 1))
  let q : ℝ := 3 / 5 + ε
  have hL : 1 ≤ L := one_le_log_K hj
  have hL0 : 0 ≤ L := zero_le_one.trans hL
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hL' : 1 ≤ L' := one_le_log_K (by omega)
  have hLL' : L ≤ L' := log_K_le_log_K_succ hj
  have hL'upper : L' ≤ L + 10 := log_K_succ_le_add_ten hj
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hq1 : q ≤ 1 := by dsimp [q]; linarith
  have hL'eleven : L' ≤ 11 * L := by nlinarith
  have hpowBase : L' ^ q ≤ (11 * L) ^ q :=
    Real.rpow_le_rpow (zero_le_one.trans hL') hL'eleven hq0
  have helevenPow : (11 : ℝ) ^ q ≤ 11 := by
    simpa only [Real.rpow_one] using
      (Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ 11 by norm_num) hq1)
  have hpowUpper : L' ^ q ≤ 11 * L ^ q := by
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 11) hL0] at hpowBase
    exact hpowBase.trans (mul_le_mul_of_nonneg_right helevenPow
      (Real.rpow_nonneg hL0 q))
  have honePow : 1 ≤ L ^ q := Real.one_le_rpow hL hq0
  rw [log_J (ε := ε) (j := j + 1) (by omega)]
  change 2 * L ≤ 2 * (L' + L' ^ q) ∧
    2 * (L' + L' ^ q) ≤ 2 * L + 42 * L ^ q
  constructor
  · have hpow0 : 0 ≤ L' ^ q := Real.rpow_nonneg (zero_le_one.trans hL') q
    nlinarith
  · nlinarith

/-- The numerical absorption behind the replacement of the disk threshold by
the natural-time threshold.  The deliberately generous constant `1933`
keeps the argument elementary. -/
lemma threshold_absorption {ε L R : ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 2 / 5) (hL : 1 ≤ L)
    (hRlower : 2 * L ≤ R)
    (hRupper : R ≤ 2 * L + 42 * L ^ (3 / 5 + ε : ℝ))
    (hlarge : 1933 ≤ L ^ ε) :
    1 / Real.pi * R ^ 2 - R ^ (8 / 5 + 3 * ε : ℝ) ≤
      4 / Real.pi * L ^ 2 - L ^ (8 / 5 + 2 * ε : ℝ) := by
  have hL0 : 0 ≤ L := zero_le_one.trans hL
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hq0 : 0 ≤ 3 / 5 + ε := by positivity
  have hq1 : 3 / 5 + ε ≤ 1 := by linarith
  let a : ℝ := L ^ (3 / 5 + ε : ℝ)
  have ha0 : 0 ≤ a := Real.rpow_nonneg hL0 _
  have haL : a ≤ L := by
    dsimp [a]
    simpa only [Real.rpow_one] using
      (Real.rpow_le_rpow_of_exponent_le hL hq1)
  have hLa : L * a = L ^ (8 / 5 + ε : ℝ) := by
    calc
      L * a = L ^ (1 : ℝ) * L ^ (3 / 5 + ε : ℝ) := by simp [a]
      _ = L ^ ((1 : ℝ) + (3 / 5 + ε)) :=
        (Real.rpow_add hLp 1 (3 / 5 + ε)).symm
      _ = L ^ (8 / 5 + ε : ℝ) := by congr 1 <;> ring
  have hR0 : 0 ≤ R := hRlower.trans' (mul_nonneg (by norm_num) hL0)
  have hupper0 : 0 ≤ 2 * L + 42 * a := by positivity
  have hsqmono : R ^ 2 ≤ (2 * L + 42 * a) ^ 2 := by
    have hprod : 0 ≤ (2 * L + 42 * a - R) * (2 * L + 42 * a + R) :=
      mul_nonneg (sub_nonneg.mpr hRupper) (add_nonneg hupper0 hR0)
    nlinarith
  have haa : a ^ 2 ≤ L * a := by
    nlinarith [mul_nonneg ha0 (sub_nonneg.mpr haL)]
  have hR2 : R ^ 2 ≤ 4 * L ^ 2 +
      1932 * L ^ (8 / 5 + ε : ℝ) := by
    rw [← hLa]
    nlinarith
  have hpi : (1 : ℝ) ≤ Real.pi := by
    nlinarith [Real.one_le_pi_div_two]
  have hdiv := div_le_div_of_nonneg_right hR2 Real.pi_pos.le
  have hextra0 : 0 ≤ 1932 * L ^ (8 / 5 + ε : ℝ) := by positivity
  have hextradiv :
      (1932 * L ^ (8 / 5 + ε : ℝ)) / Real.pi ≤
        1932 * L ^ (8 / 5 + ε : ℝ) :=
    div_le_self hextra0 hpi
  have hR2div : R ^ 2 / Real.pi ≤
      4 * L ^ 2 / Real.pi + 1932 * L ^ (8 / 5 + ε : ℝ) := by
    rw [add_div] at hdiv
    exact hdiv.trans (add_le_add le_rfl hextradiv)
  have hLR : L ≤ R := by linarith
  have hp0 : 0 ≤ 8 / 5 + 3 * ε := by positivity
  have hpowerLower : L ^ (8 / 5 + 3 * ε : ℝ) ≤
      R ^ (8 / 5 + 3 * ε : ℝ) :=
    Real.rpow_le_rpow hL0 hLR hp0
  have hexponents : 8 / 5 + ε ≤ 8 / 5 + 2 * ε := by linarith
  have hsmallPower : L ^ (8 / 5 + ε : ℝ) ≤
      L ^ (8 / 5 + 2 * ε : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hL hexponents
  have hcorrection :
      1932 * L ^ (8 / 5 + ε : ℝ) + L ^ (8 / 5 + 2 * ε : ℝ) ≤
        L ^ (8 / 5 + 3 * ε : ℝ) := by
    calc
      1932 * L ^ (8 / 5 + ε : ℝ) + L ^ (8 / 5 + 2 * ε : ℝ) ≤
          1933 * L ^ (8 / 5 + 2 * ε : ℝ) := by nlinarith
      _ ≤ L ^ (8 / 5 + 2 * ε : ℝ) * L ^ ε :=
        by simpa [mul_comm] using
          (mul_le_mul_of_nonneg_right hlarge
            (Real.rpow_nonneg hL0 (8 / 5 + 2 * ε : ℝ)))
      _ = L ^ (8 / 5 + 3 * ε : ℝ) := by
        rw [← Real.rpow_add hLp]
        congr 1 <;> ring
  rw [show 1 / Real.pi * R ^ 2 = R ^ 2 / Real.pi by ring,
    show 4 / Real.pi * L ^ 2 = 4 * L ^ 2 / Real.pi by ring]
  linarith

lemma naturalThreshold_J_succ_le_diskThreshold
    {ε : ℝ} (hε : 0 < ε) (hεsmall : ε ≤ 2 / 5)
    {j : ℕ} (hj : 1 ≤ j)
    (hlarge : 1933 ≤ Real.log (K j) ^ ε) :
    naturalThreshold ε (J ε (j + 1)) ≤ diskThreshold ε j := by
  rw [naturalThreshold, diskThreshold]
  exact threshold_absorption hε hεsmall (one_le_log_K hj)
    (log_J_succ_bounds hε hεsmall hj).1
    (log_J_succ_bounds hε hεsmall hj).2 hlarge

lemma eventually_large_log_K_rpow {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ j : ℕ in atTop, 1933 ≤ Real.log (K j) ^ ε := by
  have ht : Tendsto (fun j : ℕ => (j : ℝ) ^ ε) atTop atTop :=
    (tendsto_rpow_atTop hε).comp tendsto_natCast_atTop_atTop
  have hlargeNat : ∀ᶠ j : ℕ in atTop, (1933 : ℝ) ≤ (j : ℝ) ^ ε :=
    ht (Filter.eventually_ge_atTop (1933 : ℝ))
  filter_upwards [Filter.eventually_ge_atTop 1, hlargeNat] with j hj hjlarge
  have hbase : (j : ℝ) ≤ Real.log (K j) := nat_le_log_K hj
  exact hjlarge.trans (Real.rpow_le_rpow (by positivity) hbase hε.le)

lemma eventually_nat_rpow_ge {δ : ℝ} (hδ : 0 < δ) (C : ℝ) :
    ∀ᶠ j : ℕ in atTop, C ≤ (j : ℝ) ^ δ := by
  exact ((tendsto_rpow_atTop hδ).comp
    tendsto_natCast_atTop_atTop) (Filter.eventually_ge_atTop C)

/-- The exponent gap used after subtracting the exit-time tail. -/
lemma eventually_exp_exit_error_add_lt_disk_probability
    {ε c : ℝ} (hε : 0 < ε) (hc : 0 < c) :
    ∀ᶠ j : ℕ in atTop,
      Real.exp (-((j : ℝ) ^ (3 / 5 + ε / 2 : ℝ))) +
          Real.exp (-(c * (j : ℝ) ^ (3 / 5 + ε : ℝ))) <
        Real.exp (-((j : ℝ) ^ (3 / 5 + ε / 3 : ℝ))) := by
  have hd : 0 < ε / 6 := by positivity
  have hb : 0 < 2 * ε / 3 := by positivity
  have ha : 0 < 3 / 5 + ε / 3 := by positivity
  filter_upwards [Filter.eventually_ge_atTop 1,
    eventually_nat_rpow_ge hd 2,
    eventually_nat_rpow_ge hb (2 / c),
    eventually_nat_rpow_ge ha (Real.log 4)] with j hj hjd hjb hjA
  let x : ℝ := j
  let A : ℝ := x ^ (3 / 5 + ε / 3 : ℝ)
  have hx : 0 < x := by
    dsimp [x]
    exact_mod_cast (show 0 < j by omega)
  have hA0 : 0 < A := by dsimp [A]; positivity
  have hdEq : x ^ (3 / 5 + ε / 2 : ℝ) = A * x ^ (ε / 6) := by
    change x ^ (3 / 5 + ε / 2 : ℝ) =
      x ^ (3 / 5 + ε / 3 : ℝ) * x ^ (ε / 6)
    rw [← Real.rpow_add hx]
    congr 1 <;> ring
  have hbEq : c * x ^ (3 / 5 + ε : ℝ) =
      A * (c * x ^ (2 * ε / 3)) := by
    change c * x ^ (3 / 5 + ε : ℝ) =
      x ^ (3 / 5 + ε / 3 : ℝ) * (c * x ^ (2 * ε / 3))
    calc
      c * x ^ (3 / 5 + ε : ℝ) =
          c * (x ^ (3 / 5 + ε / 3 : ℝ) * x ^ (2 * ε / 3)) := by
        rw [← Real.rpow_add hx]
        congr 2 <;> ring
      _ = x ^ (3 / 5 + ε / 3 : ℝ) * (c * x ^ (2 * ε / 3)) := by ring
  have hjb' : 2 ≤ c * x ^ (2 * ε / 3) := by
    have := (mul_le_mul_of_nonneg_left hjb hc.le)
    field_simp [hc.ne'] at this
    simpa [x] using this
  have hlog4pos : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hexpneglog4 : Real.exp (-Real.log 4) = (1 : ℝ) / 4 := by
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 4)]
    norm_num
  have hDlarge : A + Real.log 4 ≤ x ^ (3 / 5 + ε / 2 : ℝ) := by
    rw [hdEq]
    have hjd' : (2 : ℝ) ≤ x ^ (ε / 6) := by simpa [x] using hjd
    nlinarith
  have hBlarge : A + Real.log 4 ≤ c * x ^ (3 / 5 + ε : ℝ) := by
    rw [hbEq]
    nlinarith
  have hquarter (Y : ℝ) (hY : A + Real.log 4 ≤ Y) :
      Real.exp (-Y) ≤ Real.exp (-A) / 4 := by
    calc
      Real.exp (-Y) ≤ Real.exp (-(A + Real.log 4)) :=
        Real.exp_le_exp.mpr (neg_le_neg hY)
      _ = Real.exp (-A) / 4 := by
        rw [neg_add, Real.exp_add, hexpneglog4]
        ring
  have hfirst := hquarter _ hDlarge
  have hsecond := hquarter _ hBlarge
  change Real.exp (-(x ^ (3 / 5 + ε / 2 : ℝ))) +
      Real.exp (-(c * x ^ (3 / 5 + ε : ℝ))) < Real.exp (-A)
  have hexpA : 0 < Real.exp (-A) := Real.exp_pos _
  nlinarith

lemma eventually_ennreal_exp_exit_error_add_lt_disk_probability
    {ε c : ℝ} (hε : 0 < ε) (hc : 0 < c) :
    ∀ᶠ j : ℕ in atTop,
      ENNReal.ofReal (Real.exp (-((j : ℝ) ^ (3 / 5 + ε / 2 : ℝ)))) +
          ENNReal.ofReal (Real.exp (-(c * (j : ℝ) ^ (3 / 5 + ε : ℝ)))) <
        ENNReal.ofReal (Real.exp (-((j : ℝ) ^ (3 / 5 + ε / 3 : ℝ)))) := by
  filter_upwards [eventually_exp_exit_error_add_lt_disk_probability hε hc] with j hj
  rw [← ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le,
    ENNReal.ofReal_lt_ofReal_iff (Real.exp_pos _)]
  exact hj

lemma exp_neg_log_J_rpow_le_exp_neg_nat_rpow
    {ε : ℝ} (hε : 0 < ε) {j : ℕ} (hj : 1 ≤ j) :
    Real.exp (-(Real.log (J ε j) ^ (3 / 5 + ε / 2 : ℝ))) ≤
      Real.exp (-((j : ℝ) ^ (3 / 5 + ε / 2 : ℝ))) := by
  have hlogJ : (j : ℝ) ≤ Real.log (J ε j) := by
    rw [log_J (ε := ε) hj]
    have hjK : (j : ℝ) ≤ Real.log (K j) := nat_le_log_K hj
    have hpow0 : 0 ≤ Real.log (K j) ^ (3 / 5 + ε : ℝ) :=
      Real.rpow_nonneg (zero_le_one.trans (one_le_log_K hj)) _
    linarith
  have hpow : (j : ℝ) ^ (3 / 5 + ε / 2 : ℝ) ≤
      Real.log (J ε j) ^ (3 / 5 + ε / 2 : ℝ) :=
    Real.rpow_le_rpow (by positivity) hlogJ (by positivity)
  exact Real.exp_le_exp.mpr (neg_le_neg hpow)

lemma nat_le_log_J {ε : ℝ} {j : ℕ} (hj : 1 ≤ j) :
    (j : ℝ) ≤ Real.log (J ε j) := by
  rw [log_J (ε := ε) hj]
  have hjK : (j : ℝ) ≤ Real.log (K j) := nat_le_log_K hj
  have hpow0 : 0 ≤ Real.log (K j) ^ (3 / 5 + ε : ℝ) :=
    Real.rpow_nonneg (zero_le_one.trans (one_le_log_K hj)) _
  linarith

lemma eventually_naturalThreshold_J_succ_le_diskThreshold
    {ε : ℝ} (hε : 0 < ε) (hεsmall : ε ≤ 2 / 5) :
    ∀ᶠ j : ℕ in atTop,
      naturalThreshold ε (J ε (j + 1)) ≤ diskThreshold ε j := by
  filter_upwards [Filter.eventually_ge_atTop 1,
    eventually_large_log_K_rpow hε] with j hj hlarge
  exact naturalThreshold_J_succ_le_diskThreshold hε hεsmall hj hlarge

lemma J_pos {ε : ℝ} {j : ℕ} (hj : 1 ≤ j) : 0 < J ε j := by
  unfold J
  exact sq_pos_of_pos (mul_pos (K_pos hj) (Real.exp_pos _))

lemma J_le_Jnat {ε : ℝ} (j : ℕ) : J ε j ≤ Jnat ε j := by
  exact Nat.le_ceil _

lemma nat_le_J {ε : ℝ} {j : ℕ} (hj : 1 ≤ j) : (j : ℝ) ≤ J ε j := by
  have hj0 : (0 : ℝ) ≤ j := by positivity
  have hjpow : (j : ℝ) ≤ (j : ℝ) ^ 9 := by
    have hjR : (1 : ℝ) ≤ j := by exact_mod_cast hj
    simpa using pow_le_pow_right₀ hjR (show 1 ≤ 9 by norm_num)
  have hexpj : (1 : ℝ) ≤ Real.exp (j : ℝ) := Real.one_le_exp hj0
  have hKj : (j : ℝ) ≤ K j := by
    rw [K]
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ 16 * Real.exp j by positivity)
      (sub_nonneg.mpr hjpow)]
  have hlogK0 : 0 ≤ Real.log (K j) := zero_le_one.trans (one_le_log_K hj)
  have hexp : 1 ≤ Real.exp (Real.log (K j) ^ (3 / 5 + ε : ℝ)) :=
    Real.one_le_exp (Real.rpow_nonneg hlogK0 _)
  have hjR1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hK1 : 1 ≤ K j := hjR1.trans hKj
  unfold J
  have hmul : K j ≤ K j * Real.exp (Real.log (K j) ^ (3 / 5 + ε : ℝ)) :=
    (le_mul_iff_one_le_right (K_pos hj)).2 hexp
  nlinarith [mul_self_le_mul_self (zero_le_one.trans hK1) hmul]

lemma nat_le_Jnat {ε : ℝ} {j : ℕ} (hj : 1 ≤ j) : j ≤ Jnat ε j := by
  exact_mod_cast (nat_le_J hj).trans (J_le_Jnat (ε := ε) j)

lemma tendsto_Jnat_atTop (ε : ℝ) : Tendsto (Jnat ε) atTop atTop := by
  apply Filter.tendsto_atTop.mpr
  intro N
  filter_upwards [Filter.eventually_ge_atTop (max 1 N)] with j hj
  exact (le_trans (le_max_right 1 N) hj).trans
    (nat_le_Jnat (le_trans (le_max_left 1 N) hj))

lemma exists_scale_index {ε : ℝ} {n : ℕ} (hn : Jnat ε 1 ≤ n) :
    ∃ j : ℕ, 1 ≤ j ∧ Jnat ε j ≤ n ∧ n < Jnat ε (j + 1) := by
  have hex : ∃ k : ℕ, n < Jnat ε (k + 1) := by
    have ht : Tendsto (fun k : ℕ => Jnat ε (k + 1)) atTop atTop := by
      simpa [Nat.add_comm] using
        ((Filter.tendsto_add_atTop_iff_nat 1).2 (tendsto_Jnat_atTop ε))
    have hev : ∀ᶠ k : ℕ in atTop, n < Jnat ε (k + 1) :=
      ht (Filter.eventually_gt_atTop n)
    exact Filter.Eventually.exists hev
  let k := Nat.find hex
  have hkUpper : n < Jnat ε (k + 1) := Nat.find_spec hex
  have hkpos : 0 < k := by
    by_contra hk
    have hk0 : k = 0 := Nat.eq_zero_of_not_pos hk
    have hkUpper0 : n < Jnat ε 1 := by simpa [hk0] using hkUpper
    exact (not_lt_of_ge hn) hkUpper0
  have hkLower : Jnat ε k ≤ n := by
    have hnot := Nat.find_min hex (by omega : k - 1 < k)
    have hkEq : (k - 1) + 1 = k := by omega
    rw [hkEq] at hnot
    omega
  exact ⟨k, hkpos, hkLower, hkUpper⟩

/-! ## The probability subtraction at the disk-exit time -/

lemma measure_gt_of_subset_union {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {A B C : Set Ω} {p q r : ℝ≥0∞}
    (hsub : A ⊆ B ∪ C) (hA : p < μ A) (hC : μ C ≤ q)
    (hpqr : r + q < p) : r < μ B := by
  by_contra h
  have hB : μ B ≤ r := le_of_not_gt h
  have hmeasure : μ A ≤ μ B + μ C :=
    (measure_mono hsub).trans (measure_union_le B C)
  exact (not_lt_of_ge (hmeasure.trans (add_le_add hB hC))) (hpqr.trans hA)

def diskGood {Ω : Type*} (M : Ω → ℕ → ℕ) (τ : ℕ → Ω → ℕ)
    (ε : ℝ) (j : ℕ) : Set Ω :=
  {ω | diskThreshold ε j ≤ (M ω (τ j ω) : ℝ)}

def exitBad {Ω : Type*} (τ : ℕ → Ω → ℕ) (ε : ℝ) (j : ℕ) : Set Ω :=
  {ω | Jnat ε j ≤ τ j ω}

def scaleGood {Ω : Type*} (M : Ω → ℕ → ℕ) (ε : ℝ) (j : ℕ) : Set Ω :=
  {ω | naturalThreshold ε (J ε (j + 1)) ≤ (M ω (Jnat ε j) : ℝ)}

def naturalGood {Ω : Type*} (M : Ω → ℕ → ℕ) (ε : ℝ) (n : ℕ) : Set Ω :=
  {ω | naturalThreshold ε n ≤ (M ω n : ℝ)}

lemma diskGood_subset_scaleGood_union_exitBad
    {Ω : Type*} (M : Ω → ℕ → ℕ) (τ : ℕ → Ω → ℕ)
    (hmono : ∀ ω, Monotone (M ω)) {ε : ℝ} {j : ℕ}
    (hthreshold : naturalThreshold ε (J ε (j + 1)) ≤ diskThreshold ε j) :
    diskGood M τ ε j ⊆ scaleGood M ε j ∪ exitBad τ ε j := by
  intro ω hω
  by_cases hexit : ω ∈ exitBad τ ε j
  · exact Set.mem_union_right _ hexit
  · apply Set.mem_union_left
    have htime : τ j ω ≤ Jnat ε j := by
      have : ¬Jnat ε j ≤ τ j ω := by simpa [exitBad] using hexit
      omega
    have hM : (M ω (τ j ω) : ℝ) ≤ M ω (Jnat ε j) := by
      exact_mod_cast hmono ω htime
    change naturalThreshold ε (J ε (j + 1)) ≤ (M ω (Jnat ε j) : ℝ)
    have hdisk : diskThreshold ε j ≤ (M ω (τ j ω) : ℝ) := by
      simpa [diskGood] using hω
    exact hthreshold.trans (hdisk.trans hM)

lemma scaleGood_measure_gt
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (M : Ω → ℕ → ℕ) (τ : ℕ → Ω → ℕ)
    (hmono : ∀ ω, Monotone (M ω)) {ε : ℝ} {j : ℕ}
    {p q r : ℝ≥0∞}
    (hthreshold : naturalThreshold ε (J ε (j + 1)) ≤ diskThreshold ε j)
    (hdisk : p < μ (diskGood M τ ε j))
    (hexit : μ (exitBad τ ε j) ≤ q) (hpqr : r + q < p) :
    r < μ (scaleGood M ε j) := by
  exact measure_gt_of_subset_union μ
    (diskGood_subset_scaleGood_union_exitBad M τ hmono hthreshold)
    hdisk hexit hpqr

lemma scaleGood_subset_naturalGood_of_bracket
    {Ω : Type*} (M : Ω → ℕ → ℕ) (hmono : ∀ ω, Monotone (M ω))
    {ε T : ℝ} {j n : ℕ}
    (hprofile : MonotoneOn (logProfile (8 / 5 + 3 * ε)) (Ici T))
    (hj : 1 ≤ j) (hT : T ≤ Real.log (J ε j))
    (hlower : Jnat ε j ≤ n) (hupper : n < Jnat ε (j + 1)) :
    scaleGood M ε j ⊆ naturalGood M ε n := by
  have hJjn : J ε j ≤ (n : ℝ) :=
    (J_le_Jnat (ε := ε) j).trans (by exact_mod_cast hlower)
  have hnpos : (0 : ℝ) < n := (J_pos (ε := ε) hj).trans_le hJjn
  have hlogLower : Real.log (J ε j) ≤ Real.log (n : ℝ) :=
    Real.strictMonoOn_log.monotoneOn
      (by simp only [Set.mem_Ioi]; exact J_pos hj)
      (by simp only [Set.mem_Ioi]; exact hnpos) hJjn
  have hnJnext : (n : ℝ) < J ε (j + 1) := by
    exact Nat.lt_ceil.mp (by simpa [Jnat] using hupper)
  have hlogUpper : Real.log (n : ℝ) ≤ Real.log (J ε (j + 1)) :=
    (Real.strictMonoOn_log.monotoneOn
      (by simp only [Set.mem_Ioi]; exact hnpos)
      (by simp only [Set.mem_Ioi]; exact J_pos (by omega)) hnJnext.le)
  have hthreshold : naturalThreshold ε n ≤
      naturalThreshold ε (J ε (j + 1)) := by
    change logProfile (8 / 5 + 3 * ε) (Real.log (n : ℝ)) ≤
      logProfile (8 / 5 + 3 * ε) (Real.log (J ε (j + 1)))
    exact hprofile (hT.trans hlogLower) (hT.trans (hlogLower.trans hlogUpper)) hlogUpper
  intro ω hω
  change naturalThreshold ε n ≤ (M ω n : ℝ)
  have hscale : naturalThreshold ε (J ε (j + 1)) ≤
      (M ω (Jnat ε j) : ℝ) := by simpa [scaleGood] using hω
  have hM : (M ω (Jnat ε j) : ℝ) ≤ M ω n := by
    exact_mod_cast hmono ω hlower
  exact hthreshold.trans (hscale.trans hM)

/-- Appendix A's first time change.  The only probabilistic hypotheses are
(A.1) and the exit-time tail; threshold replacement, subtraction of the tail,
and exponent weakening are proved above. -/
theorem scale_probability_of_disk_and_exit
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (M : Ω → ℕ → ℕ) (τ : ℕ → Ω → ℕ)
    (hmono : ∀ ω, Monotone (M ω))
    {ε c : ℝ} (hε : 0 < ε) (hεsmall : ε ≤ 2 / 5) (hc : 0 < c)
    (hdisk : ∀ᶠ j : ℕ in atTop,
      ENNReal.ofReal (Real.exp (-((j : ℝ) ^ (3 / 5 + ε / 3 : ℝ)))) <
        μ (diskGood M τ ε j))
    (hexit : ∀ᶠ j : ℕ in atTop,
      μ (exitBad τ ε j) ≤
        ENNReal.ofReal (Real.exp (-(c * (j : ℝ) ^ (3 / 5 + ε : ℝ))))) :
    ∀ᶠ j : ℕ in atTop,
      ENNReal.ofReal
          (Real.exp (-(Real.log (J ε j) ^ (3 / 5 + ε / 2 : ℝ)))) <
        μ (scaleGood M ε j) := by
  filter_upwards [Filter.eventually_ge_atTop 1,
    eventually_naturalThreshold_J_succ_le_diskThreshold hε hεsmall,
    eventually_ennreal_exp_exit_error_add_lt_disk_probability hε hc,
    hdisk, hexit] with j hj hthreshold harith hdiskj hexitj
  have hscale :
      ENNReal.ofReal (Real.exp (-((j : ℝ) ^ (3 / 5 + ε / 2 : ℝ)))) <
        μ (scaleGood M ε j) :=
    scaleGood_measure_gt μ M τ hmono hthreshold hdiskj hexitj harith
  have hweakenReal := exp_neg_log_J_rpow_le_exp_neg_nat_rpow hε hj
  have hweaken :
      ENNReal.ofReal
          (Real.exp (-(Real.log (J ε j) ^ (3 / 5 + ε / 2 : ℝ)))) ≤
        ENNReal.ofReal (Real.exp (-((j : ℝ) ^ (3 / 5 + ε / 2 : ℝ)))) :=
    ENNReal.ofReal_le_ofReal hweakenReal
  exact hweaken.trans_lt hscale

/-- Monotonic interpolation from the sparse `J_j` scales to every sufficiently
large natural time. -/
theorem natural_time_probability_of_scale_probability
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (M : Ω → ℕ → ℕ) (hmono : ∀ ω, Monotone (M ω))
    {ε : ℝ} (hε : 0 < ε) (hεsmall : ε < 2 / 15)
    (hscale : ∀ᶠ j : ℕ in atTop,
      ENNReal.ofReal
          (Real.exp (-(Real.log (J ε j) ^ (3 / 5 + ε / 2 : ℝ)))) <
        μ (scaleGood M ε j)) :
    ∀ᶠ n : ℕ in atTop,
      ENNReal.ofReal
          (Real.exp (-(Real.log (n : ℝ) ^ (3 / 5 + ε / 2 : ℝ)))) <
        μ (naturalGood M ε n) := by
  have hp1 : 1 < 8 / 5 + 3 * ε := by linarith
  have hp2 : 8 / 5 + 3 * ε < 2 := by linarith
  obtain ⟨T, hprofile⟩ := eventually_monotoneOn_logProfile hp1 hp2
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hscale
  let N₀ : ℕ := max 1 (max N ⌈T⌉₊)
  have hN₀1 : 1 ≤ N₀ := le_max_left _ _
  have hNN₀ : N ≤ N₀ := (le_max_left N ⌈T⌉₊).trans (le_max_right 1 _)
  have hceilN₀ : ⌈T⌉₊ ≤ N₀ :=
    (le_max_right N ⌈T⌉₊).trans (le_max_right 1 _)
  have hTN₀ : T ≤ (N₀ : ℝ) :=
    (Nat.le_ceil T).trans (by exact_mod_cast hceilN₀)
  have hJone : Jnat ε 1 ≤ Jnat ε N₀ := Jnat_mono hε (by norm_num) hN₀1
  filter_upwards [Filter.eventually_ge_atTop (Jnat ε N₀)] with n hn
  obtain ⟨j, hj1, hjlower, hjupper⟩ :=
    exists_scale_index (hJone.trans hn)
  have hN₀j : N₀ ≤ j := by
    by_contra h
    have hsucc : j + 1 ≤ N₀ := by omega
    have hJmono : Jnat ε (j + 1) ≤ Jnat ε N₀ :=
      Jnat_mono hε (by omega) hsucc
    omega
  have hNj : N ≤ j := hNN₀.trans hN₀j
  have hTj : T ≤ Real.log (J ε j) :=
    hTN₀.trans ((by exact_mod_cast hN₀j : (N₀ : ℝ) ≤ j).trans
      (nat_le_log_J hj1))
  have hsub : scaleGood M ε j ⊆ naturalGood M ε n :=
    scaleGood_subset_naturalGood_of_bracket M hmono hprofile hj1 hTj hjlower hjupper
  have hJjn : J ε j ≤ (n : ℝ) :=
    (J_le_Jnat (ε := ε) j).trans (by exact_mod_cast hjlower)
  have hnpos : (0 : ℝ) < n := (J_pos (ε := ε) hj1).trans_le hJjn
  have hlog : Real.log (J ε j) ≤ Real.log (n : ℝ) :=
    Real.strictMonoOn_log.monotoneOn
      (by simp only [Set.mem_Ioi]; exact J_pos hj1)
      (by simp only [Set.mem_Ioi]; exact hnpos) hJjn
  have hlog0 : 0 ≤ Real.log (J ε j) :=
    (by positivity : (0 : ℝ) ≤ j).trans (nat_le_log_J hj1)
  have hpow : Real.log (J ε j) ^ (3 / 5 + ε / 2 : ℝ) ≤
      Real.log (n : ℝ) ^ (3 / 5 + ε / 2 : ℝ) :=
    Real.rpow_le_rpow hlog0 hlog (by positivity)
  have hprobReal :
      Real.exp (-(Real.log (n : ℝ) ^ (3 / 5 + ε / 2 : ℝ))) ≤
        Real.exp (-(Real.log (J ε j) ^ (3 / 5 + ε / 2 : ℝ))) :=
    Real.exp_le_exp.mpr (neg_le_neg hpow)
  exact (ENNReal.ofReal_le_ofReal hprobReal).trans_lt
    ((hN j hNj).trans_le (measure_mono hsub))

/-- The complete sparse-scale-to-natural-time consequence of the two source
estimates.  This is the displayed interpolation inequality in Appendix A. -/
theorem natural_time_probability_of_disk_and_exit
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (M : Ω → ℕ → ℕ) (τ : ℕ → Ω → ℕ)
    (hmono : ∀ ω, Monotone (M ω))
    {ε c : ℝ} (hε : 0 < ε) (hεsmall : ε < 2 / 15) (hc : 0 < c)
    (hdisk : ∀ᶠ j : ℕ in atTop,
      ENNReal.ofReal (Real.exp (-((j : ℝ) ^ (3 / 5 + ε / 3 : ℝ)))) <
        μ (diskGood M τ ε j))
    (hexit : ∀ᶠ j : ℕ in atTop,
      μ (exitBad τ ε j) ≤
        ENNReal.ofReal (Real.exp (-(c * (j : ℝ) ^ (3 / 5 + ε : ℝ))))) :
    ∀ᶠ n : ℕ in atTop,
      ENNReal.ofReal
          (Real.exp (-(Real.log (n : ℝ) ^ (3 / 5 + ε / 2 : ℝ)))) <
        μ (naturalGood M ε n) := by
  apply natural_time_probability_of_scale_probability μ M hmono hε hεsmall
  exact scale_probability_of_disk_and_exit μ M τ hmono hε
    (by linarith) hc hdisk hexit

/-! ## Independent deterministic blocks

The amplification at the end of Appendix A uses deterministic consecutive
blocks of increments.  We record the construction on the increment space,
including the pathwise fact that a maximal local time inside a translated
block is bounded by the maximal local time of the complete walk. -/

/-- Extend a finite block by an arbitrary fixed direction.  Only times at
most the block length are ever used below, so the value after the block is
irrelevant. -/
def extendBlock {m : ℕ} (v : Fin m → Direction) (i : ℕ) : Direction :=
  if hi : i < m then v ⟨i, hi⟩ else 0

/-- The walk based on a finite block, started from the origin. -/
def finiteBlockWalk {m : ℕ} (v : Fin m → Direction) : ℕ → Site :=
  simpleRandomWalk (extendBlock v)

/-- The maximal local time made by a finite block. -/
def finiteBlockMax {m : ℕ} (v : Fin m → Direction) : ℕ :=
  maxLocalTime (finiteBlockWalk v) m

lemma extendBlock_iidBlock {m k i : ℕ} (ω : ℕ → Direction) (hi : i < m) :
    extendBlock (ProbabilityTheory.iidBlock (X := Direction) k m ω) i =
      ω (k + i) := by
  simp [extendBlock, ProbabilityTheory.iidBlock, hi]

lemma finiteBlockWalk_iidBlock {m k t : ℕ} (ω : ℕ → Direction) (ht : t ≤ m) :
    finiteBlockWalk (ProbabilityTheory.iidBlock (X := Direction) k m ω) t =
      simpleRandomWalk ω (k + t) - simpleRandomWalk ω k := by
  unfold finiteBlockWalk simpleRandomWalk
  rw [Finset.sum_range_add]
  simp only [add_sub_cancel_left]
  apply Finset.sum_congr rfl
  intro i hi
  rw [extendBlock_iidBlock]
  exact (Finset.mem_range.mp hi).trans_le ht

lemma localTime_congr_on_horizon {s t : ℕ → Site} {n : ℕ}
    (h : ∀ i ≤ n, s i = t i) (x : Site) :
    localTime s n x = localTime t n x := by
  unfold localTime
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_range]
  by_cases hi : i < n + 1
  · rw [h i (by omega)]
  · simp [hi]

lemma maxLocalTime_congr_on_horizon {s t : ℕ → Site} {n : ℕ}
    (h : ∀ i ≤ n, s i = t i) : maxLocalTime s n = maxLocalTime t n := by
  unfold maxLocalTime
  apply Finset.sup_congr rfl
  intro i hi
  rw [localTime_congr_on_horizon h, h i (by
    simp only [Finset.mem_range] at hi
    omega)]

lemma localTime_translate (s : ℕ → Site) (n : ℕ) (a x : Site) :
    localTime (fun i ↦ a + s i) n (a + x) = localTime s n x := by
  unfold localTime
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨hi, heq⟩
    exact ⟨hi, add_left_cancel heq⟩
  · rintro ⟨hi, heq⟩
    exact ⟨hi, congrArg (a + ·) heq⟩

lemma maxLocalTime_translate (s : ℕ → Site) (n : ℕ) (a : Site) :
    maxLocalTime (fun i ↦ a + s i) n = maxLocalTime s n := by
  unfold maxLocalTime
  apply Finset.sup_congr rfl
  intro i _
  exact localTime_translate s n a (s i)

/-- Every visit made inside a deterministic increment block is a visit of
the full walk, translated by its position at the start of the block. -/
lemma finiteBlockMax_le_full
    {m k n : ℕ} (ω : ℕ → Direction) (hkmn : k + m ≤ n) :
    finiteBlockMax (ProbabilityTheory.iidBlock (X := Direction) k m ω) ≤
      maxLocalTime (simpleRandomWalk ω) n := by
  let a : Site := simpleRandomWalk ω k
  let b : ℕ → Site := finiteBlockWalk
    (ProbabilityTheory.iidBlock (X := Direction) k m ω)
  have hpath : ∀ t ≤ m, simpleRandomWalk ω (k + t) = a + b t := by
    intro t ht
    dsimp [a, b]
    rw [finiteBlockWalk_iidBlock ω ht]
    abel
  unfold finiteBlockMax maxLocalTime
  rw [Finset.sup_le_iff]
  intro t ht
  have htm : t ≤ m := by
    simp only [Finset.mem_range] at ht
    omega
  have hvisit : a + b t ∈ visitedSites (simpleRandomWalk ω) n := by
    apply Finset.mem_image.mpr
    refine ⟨k + t, ?_, hpath t htm⟩
    simp only [Finset.mem_range]
    omega
  have hlocal : localTime b m (b t) ≤
      localTime (simpleRandomWalk ω) n (a + b t) := by
    unfold localTime
    apply Finset.card_le_card_of_injOn (fun u ↦ k + u)
    · intro u hu
      change u ∈ (Finset.range (m + 1)).filter (fun j ↦ b j = b t) at hu
      change k + u ∈ (Finset.range (n + 1)).filter
        (fun j ↦ simpleRandomWalk ω j = a + b t)
      rw [Finset.mem_filter] at hu ⊢
      have hum : u ≤ m := by
        simp only [Finset.mem_range] at hu
        omega
      refine ⟨?_, ?_⟩
      · simp only [Finset.mem_range]
        omega
      · rw [hpath u hum, hu.2]
    · intro u hu v hv huv
      exact Nat.add_left_cancel huv
  exact hlocal.trans (localTime_le_maxLocalTime hvisit)

lemma measurable_finiteBlockMax (m : ℕ) :
    Measurable (finiteBlockMax (m := m)) := by
  exact measurable_of_countable _

/-- Failure of a fixed threshold inside one finite increment block. -/
def finiteBlockFail (m : ℕ) (u : ℝ) : Set (Fin m → Direction) :=
  {v | (finiteBlockMax v : ℝ) < u}

lemma measurableSet_finiteBlockFail (m : ℕ) (u : ℝ) :
    MeasurableSet (finiteBlockFail m u) := by
  exact MeasurableSet.of_discrete

/-- The event that each of the first `q` blocks of length `m` fails. -/
def allBlocksFail (m : ℕ) (u : ℝ) : ℕ → Set (ℕ → Direction)
  | 0 => Set.univ
  | q + 1 => allBlocksFail m u q ∩
      ProbabilityTheory.iidBlock (X := Direction) (q * m) m ⁻¹'
        finiteBlockFail m u

lemma iidHistory_mono {i j : ℕ} (hij : i ≤ j) :
    ProbabilityTheory.iidHistory (X := Direction) i ≤
      ProbabilityTheory.iidHistory (X := Direction) j := by
  refine iSup_le fun k ↦ iSup_le fun hki ↦ ?_
  exact le_iSup_of_le k (le_iSup_of_le (hki.trans_le hij) le_rfl)

lemma measurable_iidBlock_history_end (k m : ℕ) :
    Measurable[ProbabilityTheory.iidHistory (X := Direction) (k + m)]
      (ProbabilityTheory.iidBlock (X := Direction) k m) := by
  let _ : MeasurableSpace (ℕ → Direction) :=
    ProbabilityTheory.iidHistory (X := Direction) (k + m)
  apply measurable_pi_lambda
  intro i
  apply measurable_iff_comap_le.mpr
  exact le_iSup_of_le (k + (i : ℕ))
    (le_iSup_of_le (by have := i.isLt; omega) le_rfl)

lemma measurableSet_allBlocksFail_history (m : ℕ) (u : ℝ) (q : ℕ) :
    MeasurableSet[ProbabilityTheory.iidHistory (X := Direction) (q * m)]
      (allBlocksFail m u q) := by
  induction q with
  | zero => simp [allBlocksFail]
  | succ q ih =>
      rw [Nat.succ_mul]
      apply MeasurableSet.inter
      · exact (Measurable.mono measurable_id
          (iidHistory_mono (Nat.le_add_right (q * m) m)) le_rfl) ih
      · exact (measurable_iidBlock_history_end (q * m) m)
          (measurableSet_finiteBlockFail m u)

lemma measure_allBlocksFail (m : ℕ) (u : ℝ) (q : ℕ) :
    incrementLaw (allBlocksFail m u q) =
      (Measure.infinitePi (fun _ : Fin m ↦ directionLaw)
        (finiteBlockFail m u)) ^ q := by
  induction q with
  | zero => simp [allBlocksFail]
  | succ q ih =>
      change (Measure.infinitePi fun _ : ℕ ↦ directionLaw)
          (allBlocksFail m u (q + 1)) = _
      rw [allBlocksFail,
        ProbabilityTheory.measure_inter_iidBlock_eq_mul directionLaw
          (q * m) m (measurableSet_allBlocksFail_history m u q)
          (measurableSet_finiteBlockFail m u)]
      change incrementLaw (allBlocksFail m u q) * _ = _
      rw [ih, pow_succ]

lemma global_failure_subset_allBlocksFail
    {m q n : ℕ} {u : ℝ} (hqm : q * m ≤ n) :
    {ω : ℕ → Direction | (maxLocalTime (simpleRandomWalk ω) n : ℝ) < u} ⊆
      allBlocksFail m u q := by
  intro ω hω
  induction q with
  | zero => simp [allBlocksFail]
  | succ q ih =>
      rw [allBlocksFail]
      constructor
      · apply ih
        rw [Nat.succ_mul] at hqm
        omega
      · change (finiteBlockMax
          (ProbabilityTheory.iidBlock (X := Direction) (q * m) m ω) : ℝ) < u
        have hle : q * m + m ≤ n := by simpa [Nat.succ_mul] using hqm
        exact (Nat.cast_le.mpr (finiteBlockMax_le_full ω hle)).trans_lt hω

lemma finiteBlockMax_iidBlock_zero (m : ℕ) (ω : ℕ → Direction) :
    finiteBlockMax (ProbabilityTheory.iidBlock (X := Direction) 0 m ω) =
      maxLocalTime (simpleRandomWalk ω) m := by
  apply maxLocalTime_congr_on_horizon
  intro t ht
  rw [finiteBlockWalk_iidBlock ω ht]
  simp [simpleRandomWalk]

lemma finiteBlockFail_measure (m : ℕ) (u : ℝ) :
    (Measure.infinitePi (fun _ : Fin m ↦ directionLaw))
        (finiteBlockFail m u) =
      incrementLaw
        {ω : ℕ → Direction |
          (maxLocalTime (simpleRandomWalk ω) m : ℝ) < u} := by
  have hmap := congrArg
    (fun ν : Measure (Fin m → Direction) ↦ ν (finiteBlockFail m u))
    (ProbabilityTheory.iidBlock_map directionLaw 0 m)
  rw [Measure.map_apply
    (ProbabilityTheory.measurable_iidBlock (X := Direction) 0 m)
    (measurableSet_finiteBlockFail m u)] at hmap
  change incrementLaw
      (ProbabilityTheory.iidBlock (X := Direction) 0 m ⁻¹'
        finiteBlockFail m u) = _ at hmap
  rw [← hmap]
  congr 1
  ext ω
  simp only [Set.mem_preimage, finiteBlockFail, Set.mem_setOf_eq]
  rw [finiteBlockMax_iidBlock_zero]

lemma measurableSet_walk_max_lt (m : ℕ) (u : ℝ) :
    MeasurableSet
      {ω : ℕ → Direction |
        (maxLocalTime (simpleRandomWalk ω) m : ℝ) < u} := by
  exact measurableSet_lt
    ((measurable_of_countable (fun x : ℕ ↦ (x : ℝ))).comp
      ((measurable_maxLocalTime_eval m).comp measurable_simpleRandomWalk))
    measurable_const

/-- If one length-`m` block has success probability at least `p`, then `q`
independent blocks make the global failure probability at most `exp (-pq)`.
The integer condition `q*m ≤ n` is the precise no-overrun condition. -/
theorem iid_block_amplification
    {m q n : ℕ} {u p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hqm : q * m ≤ n)
    (hsingle : ENNReal.ofReal p <
      incrementLaw
        {ω : ℕ → Direction |
          u ≤ (maxLocalTime (simpleRandomWalk ω) m : ℝ)}) :
    incrementLaw
        {ω : ℕ → Direction |
          (maxLocalTime (simpleRandomWalk ω) n : ℝ) < u} ≤
      ENNReal.ofReal (Real.exp (-(p * q))) := by
  let F : Set (ℕ → Direction) :=
    {ω | (maxLocalTime (simpleRandomWalk ω) m : ℝ) < u}
  let S : Set (ℕ → Direction) :=
    {ω | u ≤ (maxLocalTime (simpleRandomWalk ω) m : ℝ)}
  have hcompl : F = Sᶜ := by
    ext ω
    simp [F, S]
  have hSmeas : MeasurableSet S := by
    exact measurableSet_le measurable_const
      ((measurable_of_countable (fun x : ℕ ↦ (x : ℝ))).comp
        ((measurable_maxLocalTime_eval m).comp measurable_simpleRandomWalk))
  have hFmeasure : incrementLaw F ≤ ENNReal.ofReal (1 - p) := by
    rw [hcompl, measure_compl hSmeas (measure_ne_top _ _), measure_univ,
      ← ENNReal.ofReal_one, ENNReal.ofReal_sub 1 hp0]
    exact tsub_le_tsub_left hsingle.le _
  have hglobal : incrementLaw
        {ω : ℕ → Direction |
          (maxLocalTime (simpleRandomWalk ω) n : ℝ) < u} ≤
      incrementLaw (allBlocksFail m u q) :=
    measure_mono (global_failure_subset_allBlocksFail hqm)
  have honep : 0 ≤ 1 - p := sub_nonneg.mpr hp1
  have hpow : (1 - p) ^ q ≤ Real.exp (-(p * q)) := by
    calc
      (1 - p) ^ q ≤ (Real.exp (-p)) ^ q :=
        pow_le_pow_left₀ honep (Real.one_sub_le_exp_neg p) q
      _ = Real.exp (-(p * q)) := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
  calc
    incrementLaw
        {ω : ℕ → Direction |
          (maxLocalTime (simpleRandomWalk ω) n : ℝ) < u} ≤
        incrementLaw (allBlocksFail m u q) := hglobal
    _ = (Measure.infinitePi (fun _ : Fin m ↦ directionLaw)
          (finiteBlockFail m u)) ^ q := measure_allBlocksFail m u q
    _ = (incrementLaw F) ^ q := by rw [finiteBlockFail_measure]
    _ ≤ (ENNReal.ofReal (1 - p)) ^ q := pow_le_pow_left' hFmeasure q
    _ = ENNReal.ofReal ((1 - p) ^ q) := (ENNReal.ofReal_pow honep q).symm
    _ ≤ ENNReal.ofReal (Real.exp (-(p * q))) := ENNReal.ofReal_le_ofReal hpow

/-! ## The Appendix A block scales -/

/-- Number of independent blocks used at time `n`. -/
noncomputable def blockCount (ε : ℝ) (n : ℕ) : ℕ :=
  ⌊Real.exp (Real.log (n : ℝ) ^ (3 / 5 + 2 * ε : ℝ))⌋₊

/-- Integer length of each block. -/
noncomputable def blockLength (ε : ℝ) (n : ℕ) : ℕ :=
  ⌊(n : ℝ) /
    Real.exp (Real.log (n : ℝ) ^ (3 / 5 + 2 * ε : ℝ))⌋₊

/-- The threshold after the second (block) time change. -/
noncomputable def amplifiedThreshold (ε : ℝ) (n : ℕ) : ℝ :=
  1 / Real.pi * Real.log (n : ℝ) ^ 2 -
    Real.log (n : ℝ) ^ (8 / 5 + 4 * ε : ℝ)

lemma blockCount_mul_blockLength_le (ε : ℝ) (n : ℕ) :
    blockCount ε n * blockLength ε n ≤ n := by
  let A := Real.log (n : ℝ) ^ (3 / 5 + 2 * ε : ℝ)
  have hq : (blockCount ε n : ℝ) ≤ Real.exp A := by
    exact Nat.floor_le (Real.exp_pos A).le
  have hm : (blockLength ε n : ℝ) ≤ (n : ℝ) / Real.exp A := by
    exact Nat.floor_le (div_nonneg (by positivity) (Real.exp_pos A).le)
  have hexp : 0 < Real.exp A := Real.exp_pos A
  have hprod : (blockCount ε n : ℝ) * blockLength ε n ≤ n := by
    calc
      (blockCount ε n : ℝ) * blockLength ε n ≤
          Real.exp A * ((n : ℝ) / Real.exp A) :=
        mul_le_mul hq hm (by positivity) (Real.exp_pos A).le
      _ = n := by field_simp
  exact_mod_cast hprod

lemma eventually_log_nat_rpow_ge {δ : ℝ} (hδ : 0 < δ) (C : ℝ) :
    ∀ᶠ n : ℕ in atTop, C ≤ Real.log (n : ℝ) ^ δ := by
  have ht : Tendsto (fun n : ℕ ↦ Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  exact ((tendsto_rpow_atTop hδ).comp ht) (Filter.eventually_ge_atTop C)

/-- Pure exponent arithmetic used to absorb the loss caused by shortening a
block. -/
lemma short_threshold_comparison
    {ε L B : ℝ} (hε : 0 < ε) (hεsmall : ε ≤ 1 / 5)
    (hL : 4 ≤ L) (hB0 : 0 ≤ B) (hBL : B ≤ L)
    (hgap : L - B ≤ 2 * L ^ (3 / 5 + 2 * ε : ℝ))
    (hlarge : 5 ≤ L ^ ε) :
    1 / Real.pi * L ^ 2 - L ^ (8 / 5 + 4 * ε : ℝ) ≤
      1 / Real.pi * B ^ 2 - B ^ (8 / 5 + 3 * ε : ℝ) := by
  let a : ℝ := 3 / 5 + 2 * ε
  let p : ℝ := 8 / 5 + 3 * ε
  have hL0 : 0 ≤ L := by linarith
  have hLp : 0 < L := by linarith
  have ha0 : 0 ≤ a := by dsimp [a]; positivity
  have hp0 : 0 ≤ p := by dsimp [p]; positivity
  have hBpow : B ^ p ≤ L ^ p := Real.rpow_le_rpow hB0 hBL hp0
  have hsqgap : L ^ 2 - B ^ 2 ≤ 4 * L * L ^ a := by
    have hsum : L + B ≤ 2 * L := by linarith
    have hdiff0 : 0 ≤ L - B := sub_nonneg.mpr hBL
    have hfac : L ^ 2 - B ^ 2 = (L - B) * (L + B) := by ring
    rw [hfac]
    calc
      (L - B) * (L + B) ≤ (2 * L ^ a) * (2 * L) :=
        mul_le_mul hgap hsum (by positivity) (by positivity)
      _ = 4 * L * L ^ a := by ring
  have hpi : 1 ≤ Real.pi := by nlinarith [Real.one_le_pi_div_two]
  have hquad : 1 / Real.pi * (L ^ 2 - B ^ 2) ≤ 4 * L * L ^ a := by
    have hcoeff : 1 / Real.pi ≤ 1 := (div_le_one Real.pi_pos).2 hpi
    have hdiff : 0 ≤ L ^ 2 - B ^ 2 := by
      rw [show L ^ 2 - B ^ 2 = (L - B) * (L + B) by ring]
      exact mul_nonneg (sub_nonneg.mpr hBL) (add_nonneg hL0 hB0)
    calc
      1 / Real.pi * (L ^ 2 - B ^ 2) ≤ 1 * (L ^ 2 - B ^ 2) := by
        exact mul_le_mul_of_nonneg_right hcoeff hdiff
      _ ≤ 4 * L * L ^ a := by simpa using hsqgap
  have hLa : L * L ^ a = L ^ (8 / 5 + 2 * ε : ℝ) := by
    calc
      L * L ^ a = L ^ (1 : ℝ) * L ^ a := by rw [Real.rpow_one]
      _ = L ^ ((1 : ℝ) + a) := (Real.rpow_add hLp 1 a).symm
      _ = L ^ (8 / 5 + 2 * ε : ℝ) := by congr 1 <;> dsimp [a] <;> ring
  have hexp_le : 8 / 5 + 2 * ε ≤ p := by dsimp [p]; linarith
  have hsmall : L ^ (8 / 5 + 2 * ε : ℝ) ≤ L ^ p :=
    Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ L) hexp_le
  have hfactor : L ^ (8 / 5 + 4 * ε : ℝ) = L ^ p * L ^ ε := by
    rw [← Real.rpow_add hLp]
    congr 1
    dsimp [p]
    ring
  have hcorr : 4 * L * L ^ a + B ^ p ≤
      L ^ (8 / 5 + 4 * ε : ℝ) := by
    rw [show 4 * L * L ^ a = 4 * (L * L ^ a) by ring, hLa, hfactor]
    have hpnonneg : 0 ≤ L ^ p := Real.rpow_nonneg hL0 _
    have hfour : 4 * L ^ p + B ^ p ≤ 5 * L ^ p := by nlinarith
    calc
      4 * L ^ (8 / 5 + 2 * ε : ℝ) + B ^ p ≤
          4 * L ^ p + B ^ p := by gcongr
      _ ≤ 5 * L ^ p := hfour
      _ ≤ L ^ p * L ^ ε := by
        simpa [mul_comm] using mul_le_mul_of_nonneg_right hlarge hpnonneg
  change 1 / Real.pi * L ^ 2 - L ^ (8 / 5 + 4 * ε : ℝ) ≤
    1 / Real.pi * B ^ 2 - B ^ p
  have hquad' : 1 / Real.pi * L ^ 2 - 1 / Real.pi * B ^ 2 ≤
      4 * L * L ^ a := by
    convert hquad using 1 <;> ring
  linarith

/-- All deterministic estimates for the floored block length and count. -/
lemma block_scale_bounds_of_large
    {ε : ℝ} (hε : 0 < ε) (hεsmall : ε ≤ 1 / 5) {n : ℕ}
    (hL : 4 ≤ Real.log (n : ℝ))
    (hdelta : 4 ≤ Real.log (n : ℝ) ^ (2 / 5 - 2 * ε : ℝ))
    (heps : 5 ≤ Real.log (n : ℝ) ^ ε) :
    let m := blockLength ε n
    let q := blockCount ε n
    let p := Real.exp (-(Real.log (n : ℝ) ^ (3 / 5 + ε : ℝ)))
    0 < m ∧
      amplifiedThreshold ε n ≤ naturalThreshold ε m ∧
      p ≤ Real.exp
        (-(Real.log (m : ℝ) ^ (3 / 5 + ε / 2 : ℝ))) ∧
      Real.exp (Real.log (n : ℝ) ^ (3 / 5 : ℝ)) ≤ p * q := by
  dsimp only
  let L : ℝ := Real.log (n : ℝ)
  let a : ℝ := 3 / 5 + 2 * ε
  let A : ℝ := L ^ a
  let x : ℝ := (n : ℝ) / Real.exp A
  let m : ℕ := blockLength ε n
  let q : ℕ := blockCount ε n
  have hL0 : 0 ≤ L := by dsimp [L]; linarith
  have hLp : 0 < L := by dsimp [L]; linarith
  have hnpos : (0 : ℝ) < n := by
    have hnNat : 0 < n := by
      by_contra hn
      have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
      simp [hn0] at hL
      norm_num at hL
    exact_mod_cast hnNat
  have ha0 : 0 ≤ a := by dsimp [a]; positivity
  have hdelta0 : 0 < 2 / 5 - 2 * ε := by
    have hnonneg : 0 ≤ 2 / 5 - 2 * ε := by linarith
    apply lt_of_le_of_ne hnonneg
    intro heq
    rw [← heq, Real.rpow_zero] at hdelta
    norm_num at hdelta
  have hA0 : 0 ≤ A := Real.rpow_nonneg hL0 _
  have hA1 : 1 ≤ A := Real.one_le_rpow (by dsimp [L]; linarith) ha0
  have hprod : A * L ^ (2 / 5 - 2 * ε : ℝ) = L := by
    dsimp [A, a]
    rw [← Real.rpow_add hLp]
    convert Real.rpow_one L using 2 <;> ring
  have hAle : 4 * A ≤ L := by
    rw [← hprod]
    simpa [mul_comm, L] using mul_le_mul_of_nonneg_left hdelta hA0
  have hlog2 : Real.log 2 ≤ 1 :=
    Real.log_two_lt_d9.le.trans (by norm_num)
  have hLAlog : Real.log 2 ≤ L - A := by nlinarith
  have hxEq : x = Real.exp (L - A) := by
    dsimp [x, L]
    rw [Real.exp_sub, Real.exp_log hnpos]
  have hx2 : 2 ≤ x := by
    rw [hxEq]
    calc
      2 = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
      _ ≤ Real.exp (L - A) := Real.exp_le_exp.mpr hLAlog
  have hmFloor : x < (m : ℝ) + 1 := by
    simpa [m, blockLength, x, A, a, L] using Nat.lt_floor_add_one x
  have hxm : x / 2 ≤ (m : ℝ) := by nlinarith
  have hmposR : (0 : ℝ) < m := (by positivity : 0 < x / 2).trans_le hxm
  have hmpos : 0 < m := by exact_mod_cast hmposR
  have hmUpper : (m : ℝ) ≤ x := by
    dsimp [m, blockLength, x, A, a, L]
    exact Nat.floor_le (by positivity)
  have hxle : x ≤ (n : ℝ) := by
    dsimp [x]
    have heone : 1 ≤ Real.exp A := Real.one_le_exp hA0
    exact div_le_self (by positivity) heone
  let B : ℝ := Real.log (m : ℝ)
  have hB0 : 0 ≤ B := Real.log_nonneg (by exact_mod_cast hmpos)
  have hBL : B ≤ L := by
    dsimp [B, L]
    exact Real.strictMonoOn_log.monotoneOn
      (by simp only [Set.mem_Ioi]; exact hmposR)
      (by simp only [Set.mem_Ioi]; exact hnpos)
      (hmUpper.trans hxle)
  have hlogLower : L - A - Real.log 2 ≤ B := by
    have hxhalf : 0 < x / 2 := by positivity
    have hlogmono : Real.log (x / 2) ≤ Real.log (m : ℝ) :=
      Real.strictMonoOn_log.monotoneOn
        (by simp only [Set.mem_Ioi]; exact hxhalf)
        (by simp only [Set.mem_Ioi]; exact hmposR) hxm
    rw [hxEq, Real.log_div (Real.exp_ne_zero _) (by norm_num),
      Real.log_exp] at hlogmono
    exact hlogmono
  have hgap : L - B ≤ 2 * A := by
    have : L - B ≤ A + Real.log 2 := by linarith
    nlinarith
  have hthreshold : amplifiedThreshold ε n ≤ naturalThreshold ε m := by
    unfold amplifiedThreshold naturalThreshold
    change 1 / Real.pi * L ^ 2 - L ^ (8 / 5 + 4 * ε : ℝ) ≤
      1 / Real.pi * B ^ 2 - B ^ (8 / 5 + 3 * ε : ℝ)
    exact short_threshold_comparison hε hεsmall
      (by dsimp [L]; exact hL) hB0 hBL (by simpa [A, a] using hgap)
      (by dsimp [L]; exact heps)
  have hprobPow : B ^ (3 / 5 + ε / 2 : ℝ) ≤
      L ^ (3 / 5 + ε : ℝ) := by
    calc
      B ^ (3 / 5 + ε / 2 : ℝ) ≤ L ^ (3 / 5 + ε / 2 : ℝ) :=
        Real.rpow_le_rpow hB0 hBL (by positivity)
      _ ≤ L ^ (3 / 5 + ε : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ L) (by linarith)
  have hprob : Real.exp (-(L ^ (3 / 5 + ε : ℝ))) ≤
      Real.exp (-(B ^ (3 / 5 + ε / 2 : ℝ))) :=
    Real.exp_le_exp.mpr (neg_le_neg hprobPow)
  have hqFloor : Real.exp A < (q : ℝ) + 1 := by
    simpa [q, blockCount, A, a, L] using Nat.lt_floor_add_one (Real.exp A)
  have hqHalf : Real.exp A / 2 ≤ (q : ℝ) := by
    have he2 : 2 ≤ Real.exp A := by
      calc
        2 ≤ Real.exp 1 := Real.exp_one_gt_d9.le.trans' (by norm_num)
        _ ≤ Real.exp A := Real.exp_le_exp.mpr hA1
    nlinarith
  have hbasepow : L ^ (3 / 5 : ℝ) ≤
      L ^ (3 / 5 + ε : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ L) (by linarith)
  have hAfac : A = L ^ (3 / 5 + ε : ℝ) * L ^ ε := by
    dsimp [A, a]
    rw [← Real.rpow_add hLp]
    congr 1
    ring
  have hdiff : L ^ (3 / 5 : ℝ) + Real.log 2 ≤
      A - L ^ (3 / 5 + ε : ℝ) := by
    rw [hAfac]
    have hs0 : 0 ≤ L ^ (3 / 5 + ε : ℝ) := Real.rpow_nonneg hL0 _
    have hs1 : 1 ≤ L ^ (3 / 5 + ε : ℝ) :=
      Real.one_le_rpow (by linarith : 1 ≤ L) (by positivity)
    have hmul : 5 * L ^ (3 / 5 + ε : ℝ) ≤
        L ^ (3 / 5 + ε : ℝ) * L ^ ε := by
      simpa [mul_comm] using mul_le_mul_of_nonneg_left heps hs0
    linarith
  have hampExp : Real.exp (L ^ (3 / 5 : ℝ)) ≤
      Real.exp (-(L ^ (3 / 5 + ε : ℝ))) * (Real.exp A / 2) := by
    rw [show Real.exp (-(L ^ (3 / 5 + ε : ℝ))) *
        (Real.exp A / 2) = Real.exp
          (A - L ^ (3 / 5 + ε : ℝ) - Real.log 2) by
      rw [Real.exp_sub, Real.exp_sub, Real.exp_log (by norm_num), Real.exp_neg]
      ring]
    exact Real.exp_le_exp.mpr (by linarith)
  have hamp : Real.exp (L ^ (3 / 5 : ℝ)) ≤
      Real.exp (-(L ^ (3 / 5 + ε : ℝ))) * (q : ℝ) :=
    hampExp.trans (mul_le_mul_of_nonneg_left hqHalf (Real.exp_pos _).le)
  refine ⟨hmpos, hthreshold, ?_, ?_⟩
  · simpa [L, B, m] using hprob
  · simpa [L, q] using hamp

lemma blockLength_ge_of_large
    {ε : ℝ} {n N : ℕ}
    (hL : 1 ≤ Real.log (n : ℝ))
    (hdelta : 4 ≤ Real.log (n : ℝ) ^ (2 / 5 - 2 * ε : ℝ))
    (hhalf : (2 * N : ℝ) ≤ Real.exp (Real.log (n : ℝ) / 2)) :
    N ≤ blockLength ε n := by
  by_cases hN : N = 0
  · simp [hN]
  let L : ℝ := Real.log (n : ℝ)
  let a : ℝ := 3 / 5 + 2 * ε
  let A : ℝ := L ^ a
  let x : ℝ := (n : ℝ) / Real.exp A
  have hLp : 0 < L := by dsimp [L]; linarith
  have hnpos : (0 : ℝ) < n := by
    have hnNat : 0 < n := by
      by_contra hn
      have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
      simp [hn0] at hL
      norm_num at hL
    exact_mod_cast hnNat
  have hA0 : 0 ≤ A := Real.rpow_nonneg hLp.le _
  have hprod : A * L ^ (2 / 5 - 2 * ε : ℝ) = L := by
    dsimp [A, a]
    rw [← Real.rpow_add hLp]
    convert Real.rpow_one L using 2 <;> ring
  have hAle : 4 * A ≤ L := by
    rw [← hprod]
    simpa [mul_comm, L] using mul_le_mul_of_nonneg_left hdelta hA0
  have hxEq : x = Real.exp (L - A) := by
    dsimp [x, L]
    rw [Real.exp_sub, Real.exp_log hnpos]
  have hxlarge : (2 * N : ℝ) ≤ x := by
    rw [hxEq]
    exact hhalf.trans (Real.exp_le_exp.mpr (by linarith))
  have hfloor : x < (blockLength ε n : ℝ) + 1 := by
    simpa [blockLength, x, A, a, L] using Nat.lt_floor_add_one x
  have hNposR : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hN
  exact_mod_cast (show (N : ℝ) ≤ blockLength ε n by nlinarith)

lemma tendsto_blockLength_atTop
    {ε : ℝ} (hεsmall : ε < 1 / 5) :
    Tendsto (blockLength ε) atTop atTop := by
  apply Filter.tendsto_atTop.mpr
  intro N
  have hδ : 0 < 2 / 5 - 2 * ε := by linarith
  have hlog : Tendsto (fun n : ℕ ↦ Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hhalfTop : Tendsto
      (fun n : ℕ ↦ Real.exp (Real.log (n : ℝ) / 2)) atTop atTop := by
    apply Real.tendsto_exp_atTop.comp
    have hmul : Tendsto
        (fun n : ℕ ↦ (1 / 2 : ℝ) * Real.log (n : ℝ)) atTop atTop :=
      hlog.const_mul_atTop (by norm_num)
    simpa [div_eq_mul_inv, mul_comm] using hmul
  filter_upwards [hlog (Filter.eventually_ge_atTop 1),
    eventually_log_nat_rpow_ge hδ 4,
    hhalfTop (Filter.eventually_ge_atTop (2 * N : ℝ))] with n hL hδn hhalf
  exact blockLength_ge_of_large hL hδn hhalf

lemma eventually_block_scale_bounds
    {ε : ℝ} (hε : 0 < ε) (hεsmall : ε < 1 / 5) :
    ∀ᶠ n : ℕ in atTop,
      let m := blockLength ε n
      let q := blockCount ε n
      let p := Real.exp (-(Real.log (n : ℝ) ^ (3 / 5 + ε : ℝ)))
      0 < m ∧
        amplifiedThreshold ε n ≤ naturalThreshold ε m ∧
        p ≤ Real.exp
          (-(Real.log (m : ℝ) ^ (3 / 5 + ε / 2 : ℝ))) ∧
        Real.exp (Real.log (n : ℝ) ^ (3 / 5 : ℝ)) ≤ p * q := by
  have hδ : 0 < 2 / 5 - 2 * ε := by linarith
  filter_upwards [
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
      (Filter.eventually_ge_atTop 4),
    eventually_log_nat_rpow_ge hδ 4,
    eventually_log_nat_rpow_ge hε 5] with n hL hδn heps
  exact block_scale_bounds_of_large hε hεsmall.le hL hδn heps

/-- The second time change in Appendix A.  An eventual one-block lower bound
at every natural time amplifies, using genuine integer independent blocks, to
the double-exponential lower-deviation bound under the canonical path law. -/
theorem eventually_amplified_lower_deviation_of_natural_time
    {ε : ℝ} (hε : 0 < ε) (hεsmall : ε < 2 / 15)
    (hnatural : ∀ᶠ m : ℕ in atTop,
      ENNReal.ofReal
          (Real.exp (-(Real.log (m : ℝ) ^ (3 / 5 + ε / 2 : ℝ)))) <
        incrementLaw
          (naturalGood
            (fun ω n ↦ maxLocalTime (simpleRandomWalk ω) n) ε m)) :
    ∀ᶠ n : ℕ in atTop,
      simpleRandomWalkLaw
          {s | (maxLocalTime s n : ℝ) < amplifiedThreshold ε n} ≤
        ENNReal.ofReal
          (Real.exp
            (-Real.exp (Real.log (n : ℝ) ^ (3 / 5 : ℝ)))) := by
  have hεfifth : ε < 1 / 5 := by linarith
  have hnaturalBlock : ∀ᶠ n : ℕ in atTop,
      ENNReal.ofReal
          (Real.exp (-(Real.log (blockLength ε n : ℝ) ^
            (3 / 5 + ε / 2 : ℝ)))) <
        incrementLaw
          (naturalGood
            (fun ω k ↦ maxLocalTime (simpleRandomWalk ω) k) ε
            (blockLength ε n)) :=
    (tendsto_blockLength_atTop hεfifth).eventually hnatural
  filter_upwards [eventually_block_scale_bounds hε hεfifth,
    hnaturalBlock,
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
      (Filter.eventually_ge_atTop 0)] with n hscale hnat hlog0
  let m : ℕ := blockLength ε n
  let q : ℕ := blockCount ε n
  let p : ℝ := Real.exp (-(Real.log (n : ℝ) ^ (3 / 5 + ε : ℝ)))
  let u : ℝ := amplifiedThreshold ε n
  have hmpos : 0 < m := by simpa [m, q, p] using hscale.1
  have hthreshold : u ≤ naturalThreshold ε m := by
    simpa [m, q, p, u] using hscale.2.1
  have hpweaken : p ≤ Real.exp
      (-(Real.log (m : ℝ) ^ (3 / 5 + ε / 2 : ℝ))) := by
    simpa [m, q, p] using hscale.2.2.1
  have hpq : Real.exp (Real.log (n : ℝ) ^ (3 / 5 : ℝ)) ≤ p * q := by
    simpa [m, q, p] using hscale.2.2.2
  have hsub : naturalGood
      (fun ω k ↦ maxLocalTime (simpleRandomWalk ω) k) ε m ⊆
      {ω : ℕ → Direction |
        u ≤ (maxLocalTime (simpleRandomWalk ω) m : ℝ)} := by
    intro ω hω
    change naturalThreshold ε m ≤
      (maxLocalTime (simpleRandomWalk ω) m : ℝ) at hω
    exact hthreshold.trans hω
  have hsingle : ENNReal.ofReal p <
      incrementLaw
        {ω : ℕ → Direction |
          u ≤ (maxLocalTime (simpleRandomWalk ω) m : ℝ)} :=
    (ENNReal.ofReal_le_ofReal hpweaken).trans_lt
      (hnat.trans_le (measure_mono hsub))
  have hp0 : 0 ≤ p := (Real.exp_pos _).le
  have hp1 : p ≤ 1 := by
    dsimp [p]
    rw [← Real.exp_zero]
    apply Real.exp_le_exp.mpr
    exact neg_nonpos.mpr (Real.rpow_nonneg hlog0 _)
  have hamp := iid_block_amplification hp0 hp1
    (blockCount_mul_blockLength_le ε n) hsingle
  have hexp : Real.exp (-(p * (q : ℝ))) ≤
      Real.exp
        (-Real.exp (Real.log (n : ℝ) ^ (3 / 5 : ℝ))) :=
    Real.exp_le_exp.mpr (neg_le_neg hpq)
  have hinc : incrementLaw
      {ω : ℕ → Direction |
        (maxLocalTime (simpleRandomWalk ω) n : ℝ) < u} ≤
      ENNReal.ofReal
        (Real.exp
          (-Real.exp (Real.log (n : ℝ) ^ (3 / 5 : ℝ)))) :=
    hamp.trans (ENNReal.ofReal_le_ofReal hexp)
  have hmeas : MeasurableSet
      {s : ℕ → Site | (maxLocalTime s n : ℝ) < u} := by
    exact measurableSet_lt
      ((measurable_of_countable (fun x : ℕ ↦ (x : ℝ))).comp
        (measurable_maxLocalTime_eval n)) measurable_const
  rw [simpleRandomWalkLaw,
    Measure.map_apply measurable_simpleRandomWalk hmeas]
  simpa [u] using hinc

/-- Appendix A through the IID amplification step.  The only probabilistic
premises are precisely the disk-exit lower bound (A.1) and the exit-time tail;
all time changes, floors, threshold comparisons, and independent-block
amplification are proved in this file. -/
theorem eventually_prop13_lower_deviation_of_disk_and_exit
    (τ : ℕ → (ℕ → Direction) → ℕ)
    {ε c : ℝ} (hε : 0 < ε) (hεsmall : ε < 2 / 15) (hc : 0 < c)
    (hdisk : ∀ᶠ j : ℕ in atTop,
      ENNReal.ofReal (Real.exp (-((j : ℝ) ^ (3 / 5 + ε / 3 : ℝ)))) <
        incrementLaw
          (diskGood
            (fun ω n ↦ maxLocalTime (simpleRandomWalk ω) n) τ ε j))
    (hexit : ∀ᶠ j : ℕ in atTop,
      incrementLaw (exitBad τ ε j) ≤
        ENNReal.ofReal
          (Real.exp (-(c * (j : ℝ) ^ (3 / 5 + ε : ℝ))))) :
    ∀ᶠ n : ℕ in atTop,
      simpleRandomWalkLaw
          {s | (maxLocalTime s n : ℝ) <
            1 / Real.pi * Real.log (n : ℝ) ^ 2 -
              Real.log (n : ℝ) ^ (8 / 5 + 4 * ε : ℝ)} ≤
        ENNReal.ofReal
          (Real.exp
            (-Real.exp (Real.log (n : ℝ) ^ (3 / 5 : ℝ)))) := by
  have hmono : ∀ ω : ℕ → Direction,
      Monotone (fun n ↦ maxLocalTime (simpleRandomWalk ω) n) := by
    intro ω i j hij
    exact maxLocalTime_mono hij
  have hnatural := natural_time_probability_of_disk_and_exit
    incrementLaw
    (fun ω n ↦ maxLocalTime (simpleRandomWalk ω) n) τ hmono
    hε hεsmall hc hdisk hexit
  simpa [amplifiedThreshold] using
    (eventually_amplified_lower_deviation_of_natural_time
      hε hεsmall hnatural)

/-- A finite initial segment can be absorbed into the multiplicative constant
in Proposition 1.3. -/
lemma exists_global_constant_of_eventually_double_exp_bound
    (a : ℕ → ℝ≥0∞) (ha : ∀ n, a n ≤ 1)
    (hev : ∀ᶠ n : ℕ in atTop,
      a n ≤ ENNReal.ofReal
        (Real.exp
          (-Real.exp (Real.log (n : ℝ) ^ (3 / 5 : ℝ))))) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ,
      a n ≤ ENNReal.ofReal
        (C * Real.exp
          (-Real.exp (Real.log (n : ℝ) ^ (3 / 5 : ℝ)))) := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hev
  let N₀ : ℕ := max 1 N
  let R : ℕ → ℝ := fun n ↦
    Real.exp (Real.log (n : ℝ) ^ (3 / 5 : ℝ))
  let C : ℝ := Real.exp (R N₀)
  have hC : 0 < C := Real.exp_pos _
  have hCone : 1 ≤ C := Real.one_le_exp (Real.exp_pos _).le
  refine ⟨C, hC, fun n ↦ ?_⟩
  by_cases hn : N₀ ≤ n
  · have hbase := hN n ((le_max_right 1 N).trans hn)
    have hrpos : 0 ≤ Real.exp (-R n) := (Real.exp_pos _).le
    have hreal : Real.exp (-R n) ≤ C * Real.exp (-R n) := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hCone hrpos
    exact hbase.trans (ENNReal.ofReal_le_ofReal (by simpa [R] using hreal))
  · have hnlt : n < N₀ := Nat.lt_of_not_ge hn
    have hN₀pos : 0 < N₀ := lt_of_lt_of_le Nat.zero_lt_one (le_max_left 1 N)
    have hlog0 : 0 ≤ Real.log (n : ℝ) := by
      by_cases hn0 : n = 0
      · simp [hn0]
      · exact Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn0)
    have hlogN0 : 0 ≤ Real.log (N₀ : ℝ) :=
      Real.log_nonneg (by exact_mod_cast hN₀pos)
    have hlogle : Real.log (n : ℝ) ≤ Real.log (N₀ : ℝ) := by
      by_cases hn0 : n = 0
      · simp [hn0, hlogN0]
      · exact Real.strictMonoOn_log.monotoneOn
          (by simp only [Set.mem_Ioi]; exact_mod_cast Nat.pos_of_ne_zero hn0)
          (by simp only [Set.mem_Ioi]; exact_mod_cast hN₀pos)
          (by exact_mod_cast hnlt.le)
    have hpow : Real.log (n : ℝ) ^ (3 / 5 : ℝ) ≤
        Real.log (N₀ : ℝ) ^ (3 / 5 : ℝ) :=
      Real.rpow_le_rpow hlog0 hlogle (by norm_num)
    have hR : R n ≤ R N₀ := Real.exp_le_exp.mpr hpow
    have hone : 1 ≤ C * Real.exp (-R n) := by
      change 1 ≤ Real.exp (R N₀) * Real.exp (-R n)
      rw [← Real.exp_add, ← Real.exp_zero]
      exact Real.exp_le_exp.mpr (by linarith)
    calc
      a n ≤ 1 := ha n
      _ = ENNReal.ofReal 1 := ENNReal.ofReal_one.symm
      _ ≤ ENNReal.ofReal (C * Real.exp (-R n)) := ENNReal.ofReal_le_ofReal hone
      _ = ENNReal.ofReal
          (C * Real.exp
            (-Real.exp (Real.log (n : ℝ) ^ (3 / 5 : ℝ)))) := by rfl

/-- Full pointwise Proposition 1.3 (with `δ = 4ε`) from the two Appendix A
source estimates.  Unlike the eventual form, this includes the harmless
finite-range constant `C`. -/
theorem prop13_lower_deviation_of_disk_and_exit
    (τ : ℕ → (ℕ → Direction) → ℕ)
    {ε c : ℝ} (hε : 0 < ε) (hεsmall : ε < 2 / 15) (hc : 0 < c)
    (hdisk : ∀ᶠ j : ℕ in atTop,
      ENNReal.ofReal (Real.exp (-((j : ℝ) ^ (3 / 5 + ε / 3 : ℝ)))) <
        incrementLaw
          (diskGood
            (fun ω n ↦ maxLocalTime (simpleRandomWalk ω) n) τ ε j))
    (hexit : ∀ᶠ j : ℕ in atTop,
      incrementLaw (exitBad τ ε j) ≤
        ENNReal.ofReal
          (Real.exp (-(c * (j : ℝ) ^ (3 / 5 + ε : ℝ))))) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ,
      simpleRandomWalkLaw
          {s | (maxLocalTime s n : ℝ) <
            1 / Real.pi * Real.log (n : ℝ) ^ 2 -
              Real.log (n : ℝ) ^ (8 / 5 + 4 * ε : ℝ)} ≤
        ENNReal.ofReal
          (C * Real.exp
            (-Real.exp (Real.log (n : ℝ) ^ (3 / 5 : ℝ)))) := by
  let a : ℕ → ℝ≥0∞ := fun n ↦
    simpleRandomWalkLaw
      {s | (maxLocalTime s n : ℝ) <
        1 / Real.pi * Real.log (n : ℝ) ^ 2 -
          Real.log (n : ℝ) ^ (8 / 5 + 4 * ε : ℝ)}
  have ha : ∀ n, a n ≤ 1 := fun n ↦ by
    change simpleRandomWalkLaw
      {s : ℕ → Site | (maxLocalTime s n : ℝ) <
        1 / Real.pi * Real.log (n : ℝ) ^ 2 -
          Real.log (n : ℝ) ^ (8 / 5 + 4 * ε : ℝ)} ≤ 1
    calc
      simpleRandomWalkLaw
          {s : ℕ → Site | (maxLocalTime s n : ℝ) <
            1 / Real.pi * Real.log (n : ℝ) ^ 2 -
              Real.log (n : ℝ) ^ (8 / 5 + 4 * ε : ℝ)} ≤
          simpleRandomWalkLaw Set.univ := measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
  have hev : ∀ᶠ n : ℕ in atTop,
      a n ≤ ENNReal.ofReal
        (Real.exp
          (-Real.exp (Real.log (n : ℝ) ^ (3 / 5 : ℝ)))) := by
    simpa [a] using eventually_prop13_lower_deviation_of_disk_and_exit
      τ hε hεsmall hc hdisk hexit
  simpa [a] using exists_global_constant_of_eventually_double_exp_bound a ha hev

end Erdos1166.HLOZAppendixA
