import ErdosProblems.Erdos1149.AnalyticParameters

/-!
# Numerical parameters for Weyl differencing of a logarithmic phase

On a dyadic block of length `N`, suppose that the height `T` lies between
`N^r` and `N^(r+1)`.  We use `s = r+1` Weyl steps.  The derivative of order
`s+1` has size comparable to `T * s! / N^(s+1)`.  The step size below
normalizes its upper bound, while the (much smaller) shift-count exponent
leaves room for both a Kusmin--Landau terminal saving and the boundary loss.

This file contains only the numerical argument.  The derivative identities
and the verification of the terminal increment condition belong in the
logarithmic-phase file which consumes these parameters.
-/

namespace Erdos67.LogWeylParameters

noncomputable section

open Erdos1149 Filter

/-- Number of controlled Weyl steps used at logarithmic height
`N^r <= T < N^(r+1)`. -/
def depth (r : ℕ) : ℕ := r + 1

/-- Growth exponent of the number of translates. -/
def shiftExponent (r : ℕ) : ℝ :=
  1 / (8 * depth r)

/-- Rounded number of translates. -/
def shiftCount (r N : ℕ) : ℕ :=
  ⌈(N : ℝ) ^ shiftExponent r⌉₊

/-- The unrounded common step scale. -/
def rawStepScale (r N : ℕ) (T : ℝ) : ℝ :=
  (((N : ℝ) ^ (depth r + 1) /
      (4 * T * ((depth r).factorial : ℝ))) ^
    (((depth r : ℕ) : ℝ)⁻¹))

/-- Rounded common spacing between translates. -/
def stepSize (r N : ℕ) (T : ℝ) : ℕ :=
  ⌊rawStepScale r N T / (2 * shiftCount r N)⌋₊

/-- Lower terminal increment scale. -/
def terminalLambda (r N : ℕ) : ℝ :=
  1 / ((12 : ℝ) ^ (depth r + 1) * (shiftCount r N : ℝ) ^ depth r)

/-- Fixed terminal constant after replacing the rounded shift count by its
upper power bound. -/
def terminalConstant (r : ℕ) : ℝ :=
  (12 : ℝ) ^ (depth r + 1) * (2 : ℝ) ^ depth r

/-- Power saving produced by the finite controlled-Weyl envelope. -/
def savingExponent (r : ℕ) : ℝ :=
  shiftExponent r / (2 : ℝ) ^ depth r

/-- A single eventual inequality which ensures that the rounded step size
is at least one, uniformly for every `T < N^(r+1)`. -/
def IsLargeLogWeylScale (r N : ℕ) : Prop :=
  8 * (N : ℝ) ^ shiftExponent r ≤
    ((N : ℝ) / (4 * ((depth r).factorial : ℝ))) ^
      (((depth r : ℕ) : ℝ)⁻¹)

/-- In the overlap with the second-derivative band, depth two already has a
sublinear raw translation scale.  The exponent `7/4` is slightly weaker
than the `15/8` cutoff used by the global decomposition. -/
theorem rawStepScale_two_le_of_rpow_lower
    {N : ℕ} {T : ℝ} (hN : 1 ≤ N) (hT : 0 < T)
    (hlower : (N : ℝ) ^ (7 / 4 : ℝ) ≤ T) :
    rawStepScale 2 N T ≤ (N : ℝ) ^ (3 / 4 : ℝ) := by
  have hNRpos : (0 : ℝ) < N := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  have hNR0 : (0 : ℝ) ≤ N := hNRpos.le
  have hpowSplit : (N : ℝ) ^ (4 : ℕ) =
      (N : ℝ) ^ (9 / 4 : ℝ) * (N : ℝ) ^ (7 / 4 : ℝ) := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_add hNRpos]
    norm_num
  have hratio : (N : ℝ) ^ (4 : ℕ) / T ≤
      (N : ℝ) ^ (9 / 4 : ℝ) := by
    apply (div_le_iff₀ hT).2
    rw [hpowSplit]
    exact mul_le_mul_of_nonneg_left hlower (Real.rpow_nonneg hNR0 _)
  have hbase : (N : ℝ) ^ (4 : ℕ) /
        (4 * T * (Nat.factorial 3 : ℝ)) ≤
      (N : ℝ) ^ (9 / 4 : ℝ) := by
    calc
      (N : ℝ) ^ (4 : ℕ) /
          (4 * T * (Nat.factorial 3 : ℝ)) ≤
          (N : ℝ) ^ (4 : ℕ) / T := by
        apply div_le_div_of_nonneg_left (by positivity) hT
        norm_num
        nlinarith
      _ ≤ (N : ℝ) ^ (9 / 4 : ℝ) := hratio
  unfold rawStepScale depth
  norm_num only [Nat.factorial, Nat.cast_ofNat, Nat.reduceAdd]
  calc
    ((N : ℝ) ^ 4 / (4 * T * 6)) ^ (1 / 3 : ℝ) ≤
        ((N : ℝ) ^ (9 / 4 : ℝ)) ^ (1 / 3 : ℝ) := by
      exact Real.rpow_le_rpow (by positivity) hbase (by positivity)
    _ = (N : ℝ) ^ (3 / 4 : ℝ) := by
      rw [← Real.rpow_mul hNR0]
      congr 1
      norm_num

lemma depth_pos (r : ℕ) : 0 < depth r := by
  simp [depth]

lemma shiftExponent_pos (r : ℕ) : 0 < shiftExponent r := by
  unfold shiftExponent
  have hs : (0 : ℝ) < depth r := by exact_mod_cast depth_pos r
  exact one_div_pos.mpr (mul_pos (by norm_num) hs)

lemma savingExponent_pos (r : ℕ) : 0 < savingExponent r := by
  unfold savingExponent
  exact div_pos (shiftExponent_pos r) (by positivity)

lemma shiftCount_pos {r N : ℕ} (hN : 1 ≤ N) : 0 < shiftCount r N := by
  unfold shiftCount
  apply Erdos1149.AnalyticParameters.natCeil_pos
  exact Real.rpow_pos_of_pos (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)) _

lemma shiftCount_lower (r N : ℕ) :
    (N : ℝ) ^ shiftExponent r ≤ shiftCount r N := by
  unfold shiftCount
  exact Nat.le_ceil _

lemma shiftCount_upper {r N : ℕ} (hN : 1 ≤ N) :
    (shiftCount r N : ℝ) ≤ 2 * (N : ℝ) ^ shiftExponent r := by
  unfold shiftCount
  apply Erdos1149.AnalyticParameters.natCeil_le_two_mul
  exact Real.one_le_rpow (by exact_mod_cast hN) (shiftExponent_pos r).le

/-! ## The rounded logarithmic-phase parameters -/

/-- All numerical inequalities needed by the derivative test and by the
controlled-Weyl envelope.  The analytic consumer uses the two derivative
factors in the middle with the dyadic bounds on `[N,3N]`. -/
theorem parameters_of_lower_or_rawStepScale_le
    {r N : ℕ} {T : ℝ}
    (hr : 2 ≤ r) (hN : 1 ≤ N) (hT : 0 < T)
    (hboundaryInput : (N : ℝ) ^ r ≤ T ∨
      rawStepScale r N T ≤ (N : ℝ) ^ (3 / 4 : ℝ))
    (hTupper : T < (N : ℝ) ^ (r + 1))
    (hlarge : IsLargeLogWeylScale r N) :
    let s := depth r
    let K := shiftCount r N
    let d := stepSize r N T
    let lam := terminalLambda r N
    0 < K ∧ 0 < d ∧
      (K : ℝ) ^ s * (d : ℝ) ^ s *
          (T * (s.factorial : ℝ) *
            (N : ℝ) ^ (-((s + 1 : ℕ) : ℤ))) ≤ 1 / 2 ∧
      lam ≤ (d : ℝ) ^ s *
          (T * (s.factorial : ℝ) *
            (3 * (N : ℝ)) ^ (-((s + 1 : ℕ) : ℤ))) ∧
      0 < lam ∧ lam ≤ 1 / 2 ∧
      (N : ℝ) ^ shiftExponent r ≤ K ∧
      (K : ℝ) * d ≤ (N : ℝ) ^ (3 / 4 : ℝ) ∧
      1 / lam ≤ terminalConstant r * (N : ℝ) ^ (1 / 8 : ℝ) := by
  let s := depth r
  let K := shiftCount r N
  let D := rawStepScale r N T
  let d := stepSize r N T
  let lam := terminalLambda r N
  let Y : ℝ := (N : ℝ) ^ (s + 1) /
    (4 * T * (s.factorial : ℝ))
  let z : ℝ := D / (2 * K)
  have hs : s = r + 1 := rfl
  have hspos : 0 < s := by simp [s, depth]
  have hsne : s ≠ 0 := Nat.ne_of_gt hspos
  have hs3 : 3 ≤ s := by omega
  have hNR : 1 ≤ (N : ℝ) := by exact_mod_cast hN
  have hNpos : 0 < (N : ℝ) := zero_lt_one.trans_le hNR
  have hFpos : (0 : ℝ) < s.factorial := by positivity
  have hKpos : 0 < K := by
    dsimp only [K]
    exact shiftCount_pos hN
  have hKRpos : (0 : ℝ) < K := by exact_mod_cast hKpos
  have hYpos : 0 < Y := by
    dsimp only [Y]
    positivity
  have hDdef : D = Y ^ ((s : ℝ)⁻¹) := by rfl
  have hDpos : 0 < D := by
    rw [hDdef]
    exact Real.rpow_pos_of_pos hYpos _
  have hDpow : D ^ s = Y := by
    rw [hDdef]
    exact Real.rpow_inv_natCast_pow hYpos.le hsne
  have hTupper' : T ≤ (N : ℝ) ^ s := by
    rw [hs]
    exact hTupper.le
  have hbaseY :
      (N : ℝ) / (4 * (s.factorial : ℝ)) ≤ Y := by
    dsimp only [Y]
    have hNT : (N : ℝ) * T ≤ (N : ℝ) ^ (s + 1) := by
      calc
        (N : ℝ) * T ≤ (N : ℝ) * (N : ℝ) ^ s := by gcongr
        _ = (N : ℝ) ^ (s + 1) := by rw [pow_succ]; ring
    rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < 4 * s.factorial)
      (by positivity : (0 : ℝ) < 4 * T * s.factorial)]
    nlinarith
  have hbase0 : 0 ≤ (N : ℝ) / (4 * (s.factorial : ℝ)) := by positivity
  have hbaseRoot :
      ((N : ℝ) / (4 * (s.factorial : ℝ))) ^ ((s : ℝ)⁻¹) ≤ D := by
    rw [hDdef]
    exact Real.rpow_le_rpow hbase0 hbaseY (by positivity)
  have hKupper : (K : ℝ) ≤ 2 * (N : ℝ) ^ shiftExponent r := by
    dsimp only [K]
    exact shiftCount_upper hN
  have hfourK : (4 : ℝ) * K ≤ D := by
    calc
      (4 : ℝ) * K ≤ 8 * (N : ℝ) ^ shiftExponent r := by nlinarith
      _ ≤ ((N : ℝ) / (4 * ((depth r).factorial : ℝ))) ^
          (((depth r : ℕ) : ℝ)⁻¹) := hlarge
      _ = ((N : ℝ) / (4 * (s.factorial : ℝ))) ^ ((s : ℝ)⁻¹) := rfl
      _ ≤ D := hbaseRoot
  have hz2 : 2 ≤ z := by
    dsimp only [z]
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * (K : ℝ))).2
    nlinarith
  have hdDef : d = ⌊z⌋₊ := by rfl
  have hdpow := Erdos1149.AnalyticParameters.natFloor_pow_bounds hz2 s
  rw [← hdDef] at hdpow
  have hdpos : 0 < d := by
    rw [hdDef]
    exact Erdos1149.AnalyticParameters.natFloor_pos hz2
  have hzpos : 0 < z := lt_of_lt_of_le (by norm_num) hz2
  have hupperIdentity :
      (K : ℝ) ^ s * z ^ s *
          (T * (s.factorial : ℝ) *
            (N : ℝ) ^ (-((s + 1 : ℕ) : ℤ))) =
        1 / ((4 : ℝ) * 2 ^ s) := by
    have hpowN : (N : ℝ) ^ (-((s + 1 : ℕ) : ℤ)) =
        ((N : ℝ) ^ (s + 1))⁻¹ := by
      simp only [zpow_neg, zpow_natCast]
    rw [hpowN]
    dsimp only [z]
    rw [div_pow, hDpow]
    dsimp only [Y]
    field_simp
    ring
  have hupper :
      (K : ℝ) ^ s * (d : ℝ) ^ s *
          (T * (s.factorial : ℝ) *
            (N : ℝ) ^ (-((s + 1 : ℕ) : ℤ))) ≤ 1 / 2 := by
    have hfactor0 : 0 ≤
        T * (s.factorial : ℝ) *
          (N : ℝ) ^ (-((s + 1 : ℕ) : ℤ)) := by positivity
    calc
      (K : ℝ) ^ s * (d : ℝ) ^ s *
          (T * (s.factorial : ℝ) *
            (N : ℝ) ^ (-((s + 1 : ℕ) : ℤ))) ≤
          (K : ℝ) ^ s * z ^ s *
            (T * (s.factorial : ℝ) *
              (N : ℝ) ^ (-((s + 1 : ℕ) : ℤ))) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hdpow.2 (by positivity)) hfactor0
      _ = 1 / ((4 : ℝ) * 2 ^ s) := hupperIdentity
      _ ≤ 1 / 2 := by
        have hpow1 : (1 : ℝ) ≤ 2 ^ s := one_le_pow₀ (by norm_num)
        have hden : (2 : ℝ) ≤ 4 * 2 ^ s := by nlinarith
        exact one_div_le_one_div_of_le (by norm_num) hden
  have hlowerIdentity :
      (z / 2) ^ s *
          (T * (s.factorial : ℝ) *
            (3 * (N : ℝ)) ^ (-((s + 1 : ℕ) : ℤ))) =
        1 / ((12 : ℝ) ^ (s + 1) * (K : ℝ) ^ s) := by
    have hpow3N : (3 * (N : ℝ)) ^ (-((s + 1 : ℕ) : ℤ)) =
        ((3 * (N : ℝ)) ^ (s + 1))⁻¹ := by
      simp only [zpow_neg, zpow_natCast]
    have h12pow : (12 : ℝ) ^ (s + 1) =
        4 ^ (s + 1) * 3 ^ (s + 1) := by
      rw [← mul_pow]
      norm_num
    rw [hpow3N]
    rw [h12pow]
    dsimp only [z]
    rw [div_div, div_pow, hDpow]
    dsimp only [Y]
    field_simp
    ring
  have hlower : lam ≤ (d : ℝ) ^ s *
      (T * (s.factorial : ℝ) *
        (3 * (N : ℝ)) ^ (-((s + 1 : ℕ) : ℤ))) := by
    have hfactor0 : 0 ≤
        T * (s.factorial : ℝ) *
          (3 * (N : ℝ)) ^ (-((s + 1 : ℕ) : ℤ)) := by positivity
    calc
      lam = 1 / ((12 : ℝ) ^ (s + 1) * (K : ℝ) ^ s) := rfl
      _ = (z / 2) ^ s *
          (T * (s.factorial : ℝ) *
            (3 * (N : ℝ)) ^ (-((s + 1 : ℕ) : ℤ))) :=
        hlowerIdentity.symm
      _ ≤ (d : ℝ) ^ s *
          (T * (s.factorial : ℝ) *
            (3 * (N : ℝ)) ^ (-((s + 1 : ℕ) : ℤ))) := by
        exact mul_le_mul_of_nonneg_right hdpow.1 hfactor0
  have hlampos : 0 < lam := by
    dsimp only [lam, terminalLambda]
    positivity
  have hlamhalf : lam ≤ 1 / 2 := by
    dsimp only [lam, terminalLambda]
    have hden : (2 : ℝ) ≤
        (12 : ℝ) ^ (depth r + 1) * (shiftCount r N : ℝ) ^ depth r := by
      have hpow12 : (12 : ℝ) ≤ 12 ^ (depth r + 1) := by
        rw [pow_succ]
        have hone : (1 : ℝ) ≤ 12 ^ depth r := one_le_pow₀ (by norm_num)
        nlinarith
      have hKone : (1 : ℝ) ≤ shiftCount r N := by exact_mod_cast hKpos
      have hKpow : (1 : ℝ) ≤ (shiftCount r N : ℝ) ^ depth r :=
        one_le_pow₀ hKone
      nlinarith
    exact one_div_le_one_div_of_le (by norm_num) hden
  have hKlower : (N : ℝ) ^ shiftExponent r ≤ K := by
    dsimp only [K]
    exact shiftCount_lower r N
  have hDbound : D ≤ (N : ℝ) ^ (3 / 4 : ℝ) := by
    rcases hboundaryInput with hTlower | hDraw
    · have hYupper : Y ≤ (N : ℝ) ^ 2 := by
        have hTlower' : (N : ℝ) ^ (s - 1) ≤ T := by
          rw [hs]
          simpa using hTlower
        have hdenLower : (N : ℝ) ^ (s - 1) ≤
            4 * T * (s.factorial : ℝ) := by
          have hfacOne : (1 : ℝ) ≤ 4 * (s.factorial : ℝ) := by
            have hsFac : (1 : ℝ) ≤ s.factorial := by
              exact_mod_cast (Nat.factorial_pos s)
            linarith
          calc
            (N : ℝ) ^ (s - 1) ≤ T := hTlower'
            _ = T * 1 := by ring
            _ ≤ T * (4 * (s.factorial : ℝ)) :=
              mul_le_mul_of_nonneg_left hfacOne hT.le
            _ = 4 * T * (s.factorial : ℝ) := by ring
        dsimp only [Y]
        apply (div_le_iff₀ (by positivity : (0 : ℝ) < 4 * T * s.factorial)).2
        have hpowSplit : (N : ℝ) ^ (s + 1) =
            (N : ℝ) ^ 2 * (N : ℝ) ^ (s - 1) := by
          rw [show s + 1 = 2 + (s - 1) by omega, pow_add]
        rw [hpowSplit]
        exact mul_le_mul_of_nonneg_left hdenLower (by positivity)
      have hDupper : D ≤ (N : ℝ) ^ (2 / (s : ℝ)) := by
        rw [hDdef]
        calc
          Y ^ ((s : ℝ)⁻¹) ≤ ((N : ℝ) ^ 2) ^ ((s : ℝ)⁻¹) := by
            exact Real.rpow_le_rpow hYpos.le hYupper (by positivity)
          _ = (N : ℝ) ^ (2 / (s : ℝ)) := by
            rw [← Real.rpow_natCast]
            rw [← Real.rpow_mul hNpos.le]
            congr 1
      have hexp : 2 / (s : ℝ) ≤ (3 / 4 : ℝ) := by
        have hsR : (3 : ℝ) ≤ s := by exact_mod_cast hs3
        calc
          2 / (s : ℝ) ≤ 2 / 3 :=
            div_le_div_of_nonneg_left (by norm_num) (by norm_num) hsR
          _ ≤ 3 / 4 := by norm_num
      exact hDupper.trans (Real.rpow_le_rpow_of_exponent_le hNR hexp)
    · exact hDraw
  have hboundary : (K : ℝ) * d ≤ (N : ℝ) ^ (3 / 4 : ℝ) := by
    calc
      (K : ℝ) * d ≤ (K : ℝ) * z := by
        gcongr
        exact (Erdos1149.AnalyticParameters.natFloor_le hzpos.le)
      _ = D / 2 := by
        dsimp only [z]
        field_simp
      _ ≤ D := by linarith
      _ ≤ (N : ℝ) ^ (3 / 4 : ℝ) := hDbound
  have hshiftPow : ((N : ℝ) ^ shiftExponent r) ^ s =
      (N : ℝ) ^ (1 / 8 : ℝ) := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul hNpos.le]
    congr 1
    dsimp only [shiftExponent]
    have hsR : (s : ℝ) ≠ 0 := by exact_mod_cast hsne
    change 1 / (8 * (depth r : ℝ)) * (s : ℝ) = 1 / 8
    rw [show s = depth r by rfl]
    have hdepthR : (depth r : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.ne_of_gt (depth_pos r))
    field_simp [hdepthR]
  have hterminal : 1 / lam ≤
      terminalConstant r * (N : ℝ) ^ (1 / 8 : ℝ) := by
    have hKpow : (K : ℝ) ^ s ≤
        (2 * (N : ℝ) ^ shiftExponent r) ^ s :=
      pow_le_pow_left₀ hKRpos.le hKupper s
    have hlamInv : 1 / lam = (12 : ℝ) ^ (s + 1) * (K : ℝ) ^ s := by
      dsimp only [lam, terminalLambda]
      rw [one_div_div]
      simp only [s, K]
      ring
    rw [hlamInv]
    calc
      (12 : ℝ) ^ (s + 1) * (K : ℝ) ^ s ≤
          (12 : ℝ) ^ (s + 1) *
            (2 * (N : ℝ) ^ shiftExponent r) ^ s := by gcongr
      _ = terminalConstant r * (N : ℝ) ^ (1 / 8 : ℝ) := by
        rw [mul_pow, hshiftPow]
        simp only [terminalConstant, s]
        ring
  exact ⟨hKpos, hdpos, hupper, hlower, hlampos, hlamhalf,
    hKlower, hboundary, hterminal⟩

/-- Original height-band wrapper: the standard lower bound on `T` implies
the required sublinear raw translation scale. -/
theorem parameters
    {r N : ℕ} {T : ℝ}
    (hr : 2 ≤ r) (hN : 1 ≤ N) (hT : 0 < T)
    (hTlower : (N : ℝ) ^ r ≤ T)
    (hTupper : T < (N : ℝ) ^ (r + 1))
    (hlarge : IsLargeLogWeylScale r N) :
    let s := depth r
    let K := shiftCount r N
    let d := stepSize r N T
    let lam := terminalLambda r N
    0 < K ∧ 0 < d ∧
      (K : ℝ) ^ s * (d : ℝ) ^ s *
          (T * (s.factorial : ℝ) *
            (N : ℝ) ^ (-((s + 1 : ℕ) : ℤ))) ≤ 1 / 2 ∧
      lam ≤ (d : ℝ) ^ s *
          (T * (s.factorial : ℝ) *
            (3 * (N : ℝ)) ^ (-((s + 1 : ℕ) : ℤ))) ∧
      0 < lam ∧ lam ≤ 1 / 2 ∧
      (N : ℝ) ^ shiftExponent r ≤ K ∧
      (K : ℝ) * d ≤ (N : ℝ) ^ (3 / 4 : ℝ) ∧
      1 / lam ≤ terminalConstant r * (N : ℝ) ^ (1 / 8 : ℝ) := by
  exact parameters_of_lower_or_rawStepScale_le hr hN hT (Or.inl hTlower)
    hTupper hlarge

/-- Variant for overlap bands: instead of `N^r ≤ T`, it is enough to
verify directly that the unrounded common step scale is sublinear. -/
theorem parameters_of_rawStepScale_le
    {r N : ℕ} {T : ℝ}
    (hr : 2 ≤ r) (hN : 1 ≤ N) (hT : 0 < T)
    (hDraw : rawStepScale r N T ≤ (N : ℝ) ^ (3 / 4 : ℝ))
    (hTupper : T < (N : ℝ) ^ (r + 1))
    (hlarge : IsLargeLogWeylScale r N) :
    let s := depth r
    let K := shiftCount r N
    let d := stepSize r N T
    let lam := terminalLambda r N
    0 < K ∧ 0 < d ∧
      (K : ℝ) ^ s * (d : ℝ) ^ s *
          (T * (s.factorial : ℝ) *
            (N : ℝ) ^ (-((s + 1 : ℕ) : ℤ))) ≤ 1 / 2 ∧
      lam ≤ (d : ℝ) ^ s *
          (T * (s.factorial : ℝ) *
            (3 * (N : ℝ)) ^ (-((s + 1 : ℕ) : ℤ))) ∧
      0 < lam ∧ lam ≤ 1 / 2 ∧
      (N : ℝ) ^ shiftExponent r ≤ K ∧
      (K : ℝ) * d ≤ (N : ℝ) ^ (3 / 4 : ℝ) ∧
      1 / lam ≤ terminalConstant r * (N : ℝ) ^ (1 / 8 : ℝ) := by
  exact parameters_of_lower_or_rawStepScale_le hr hN hT (Or.inr hDraw)
    hTupper hlarge

/-! ## Closing the numerical controlled-Weyl envelope -/

/-- The rounded parameters give an explicit power saving in the exact
finite-history envelope.  This is the numerical conclusion used after the
logarithmic derivative tower has supplied every terminal increment
condition. -/
theorem finiteHistoryEnvelope_le_of_lower_or_rawStepScale_le
    {r N P : ℕ} {T : ℝ}
    (hr : 2 ≤ r) (hN : 1 ≤ N) (hP : P ≤ N) (hT : 0 < T)
    (hboundaryInput : (N : ℝ) ^ r ≤ T ∨
      rawStepScale r N T ≤ (N : ℝ) ^ (3 / 4 : ℝ))
    (hTupper : T < (N : ℝ) ^ (r + 1))
    (hlarge : IsLargeLogWeylScale r N) :
    Erdos1149.RestrictedWeyl.finiteHistoryEnvelope P
        (1 / terminalLambda r N)
        (List.replicate (depth r)
          { shiftCount := shiftCount r N
            stepSize := stepSize r N T
            shiftCount_pos := shiftCount_pos hN }) ≤
      Erdos1149.AnalyticParameters.envelopeConstant
          10 (terminalConstant r) (depth r) *
        (N : ℝ) ^ (1 - savingExponent r) := by
  have hp := parameters_of_lower_or_rawStepScale_le hr hN hT hboundaryInput
    hTupper hlarge
  dsimp only at hp
  have hsExp : shiftExponent r ≤ 1 / 8 := by
    unfold shiftExponent
    have hsOne : (1 : ℝ) ≤ depth r := by
      exact_mod_cast (depth_pos r)
    have hden : (8 : ℝ) ≤ 8 * depth r := by nlinarith
    exact one_div_le_one_div_of_le (by norm_num) hden
  have hκθ : shiftExponent r ≤ (7 / 8 : ℝ) := by
    linarith
  have hκδ : shiftExponent r ≤ 2 * (1 / 4 : ℝ) := by
    linarith
  have htermC : 0 ≤ terminalConstant r := by
    unfold terminalConstant
    positivity
  have hKd : (shiftCount r N : ℝ) * stepSize r N T ≤
      (1 : ℝ) * (N : ℝ) ^ (1 - (1 / 4 : ℝ)) := by
    have hb := hp.2.2.2.2.2.2.2.1
    calc
      (shiftCount r N : ℝ) * stepSize r N T ≤
          (N : ℝ) ^ (3 / 4 : ℝ) := hb
      _ = (1 : ℝ) * (N : ℝ) ^ (1 - (1 / 4 : ℝ)) := by norm_num
  have hterminal0 : 0 ≤ 1 / terminalLambda r N :=
    (one_div_pos.mpr hp.2.2.2.2.1).le
  have hmain :=
    Erdos1149.AnalyticParameters.finiteHistoryEnvelope_replicate_le_rpow
      N P (shiftCount r N) (stepSize r N T) (depth r)
      (shiftExponent r) (1 / 4 : ℝ) (7 / 8 : ℝ)
      1 (terminalConstant r) (1 / terminalLambda r N)
      hN hP hp.1 (shiftExponent_pos r) (by norm_num) htermC
      hκθ hκδ hp.2.2.2.2.2.2.1 hKd
      hterminal0 (by
        have ht := hp.2.2.2.2.2.2.2.2
        calc
          1 / terminalLambda r N ≤
              terminalConstant r * (N : ℝ) ^ (1 / 8 : ℝ) := ht
          _ = terminalConstant r * (N : ℝ) ^ (1 - (7 / 8 : ℝ)) := by norm_num)
  norm_num only [one_pow, mul_one] at hmain
  simpa [savingExponent] using hmain

theorem finiteHistoryEnvelope_le
    {r N P : ℕ} {T : ℝ}
    (hr : 2 ≤ r) (hN : 1 ≤ N) (hP : P ≤ N) (hT : 0 < T)
    (hTlower : (N : ℝ) ^ r ≤ T)
    (hTupper : T < (N : ℝ) ^ (r + 1))
    (hlarge : IsLargeLogWeylScale r N) :
    Erdos1149.RestrictedWeyl.finiteHistoryEnvelope P
        (1 / terminalLambda r N)
        (List.replicate (depth r)
          { shiftCount := shiftCount r N
            stepSize := stepSize r N T
            shiftCount_pos := shiftCount_pos hN }) ≤
      Erdos1149.AnalyticParameters.envelopeConstant
          10 (terminalConstant r) (depth r) *
        (N : ℝ) ^ (1 - savingExponent r) := by
  exact finiteHistoryEnvelope_le_of_lower_or_rawStepScale_le
    hr hN hP hT (Or.inl hTlower) hTupper hlarge

theorem finiteHistoryEnvelope_le_of_rawStepScale_le
    {r N P : ℕ} {T : ℝ}
    (hr : 2 ≤ r) (hN : 1 ≤ N) (hP : P ≤ N) (hT : 0 < T)
    (hDraw : rawStepScale r N T ≤ (N : ℝ) ^ (3 / 4 : ℝ))
    (hTupper : T < (N : ℝ) ^ (r + 1))
    (hlarge : IsLargeLogWeylScale r N) :
    Erdos1149.RestrictedWeyl.finiteHistoryEnvelope P
        (1 / terminalLambda r N)
        (List.replicate (depth r)
          { shiftCount := shiftCount r N
            stepSize := stepSize r N T
            shiftCount_pos := shiftCount_pos hN }) ≤
      Erdos1149.AnalyticParameters.envelopeConstant
          10 (terminalConstant r) (depth r) *
        (N : ℝ) ^ (1 - savingExponent r) := by
  exact finiteHistoryEnvelope_le_of_lower_or_rawStepScale_le
    hr hN hP hT (Or.inr hDraw) hTupper hlarge

/-- For every fixed differencing depth, the rounded scale condition used by
`parameters` holds at all sufficiently large natural scales. -/
theorem eventually_isLargeLogWeylScale (r : ℕ) :
    ∀ᶠ N : ℕ in atTop, IsLargeLogWeylScale r N := by
  let s : ℝ := depth r
  let e : ℝ := shiftExponent r
  let d : ℝ := (s : ℝ)⁻¹ - e
  let C : ℝ := 4 * ((depth r).factorial : ℝ)
  have hs : 0 < s := by
    dsimp only [s]
    exact_mod_cast depth_pos r
  have hC : 0 < C := by dsimp only [C]; positivity
  have he : e = 1 / (8 * s) := rfl
  have hd : d = 7 / (8 * s) := by
    dsimp only [d]
    rw [he]
    field_simp
    ring
  have hdpos : 0 < d := by rw [hd]; positivity
  have htend : Tendsto (fun N : ℕ ↦ (N : ℝ) ^ d) atTop atTop :=
    (tendsto_rpow_atTop hdpos).comp tendsto_natCast_atTop_atTop
  have hevent : ∀ᶠ N : ℕ in atTop,
      8 * C ^ (s : ℝ)⁻¹ ≤ (N : ℝ) ^ d :=
    htend.eventually (eventually_ge_atTop (8 * C ^ (s : ℝ)⁻¹))
  filter_upwards [hevent, eventually_ge_atTop 1] with N hN hNone
  unfold IsLargeLogWeylScale
  have hNR : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hCrpow : 0 < C ^ (s : ℝ)⁻¹ := Real.rpow_pos_of_pos hC _
  have hmul := mul_le_mul_of_nonneg_right hN
    (Real.rpow_nonneg hNR.le e)
  have hpow : (N : ℝ) ^ d * (N : ℝ) ^ e =
      (N : ℝ) ^ (s : ℝ)⁻¹ := by
    rw [← Real.rpow_add hNR]
    congr 1
    dsimp only [d]
    ring
  have hmain :
      8 * (N : ℝ) ^ e ≤
        (N : ℝ) ^ (s : ℝ)⁻¹ / C ^ (s : ℝ)⁻¹ := by
    rw [le_div_iff₀ hCrpow]
    rw [← hpow]
    nlinarith [Real.rpow_nonneg hNR.le e]
  rw [show shiftExponent r = e by rfl]
  rw [show (4 * ((depth r).factorial : ℝ)) = C by rfl]
  rw [Real.div_rpow hNR.le hC.le]
  exact hmain

end

end Erdos67.LogWeylParameters
