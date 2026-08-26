import ErdosProblems.Erdos1002.NearResonantPartialCarrierBlock

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Explicit denominator parameters for the nonzero near carriers

The low shifted-carrier estimate must stop at least a logarithmic distance
`L^(1/3)` below the natural denominator cutoff.  We use the slightly larger
explicit distance `2 * sqrt L`; this still has square `O(L)`, as required by
the high-block energy estimate.  The file proves the resulting dyadic cutoff
inequality, all adjacent endpoint identities, and the final partial-block
containment.
-/

open Filter MeasureTheory Set Finset
open scoped BigOperators ENNReal Real Topology

namespace Erdos1002

noncomputable section

def nearCarrierGapWidth (L : ℝ) : ℕ :=
  ⌈2 * Real.sqrt L⌉₊

def nearCarrierLogExponent (N : ℕ) : ℕ :=
  Nat.log 2 N

def nearCarrierLowBlockCount (N : ℕ) (L : ℝ) : ℕ :=
  nearCarrierLogExponent N - nearCarrierGapWidth L - 1

def nearCarrierHighStart (N : ℕ) (L : ℝ) : ℕ :=
  nearCarrierLowBlockCount N L + 2

def nearCarrierNonzeroEnergyConstant : ℝ :=
  8 * (2 * nearGevreyProfileConstant) ^ 2 * 32

def nearCarrierBinaryLogLinearConstant : ℝ :=
  1 / Real.log 2 + 1

theorem nearCarrierNonzeroEnergyConstant_nonneg :
    0 ≤ nearCarrierNonzeroEnergyConstant := by
  unfold nearCarrierNonzeroEnergyConstant
  positivity

theorem nearCarrierBinaryLogLinearConstant_pos :
    0 < nearCarrierBinaryLogLinearConstant := by
  unfold nearCarrierBinaryLogLinearConstant
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  positivity

theorem nearCarrierGapWidth_cast_le_three_sqrt
    (L : ℝ) (hL : 1 ≤ L) :
    (nearCarrierGapWidth L : ℝ) ≤ 3 * Real.sqrt L := by
  have hceil : (nearCarrierGapWidth L : ℝ) <
      2 * Real.sqrt L + 1 := by
    unfold nearCarrierGapWidth
    exact Nat.ceil_lt_add_one (by positivity)
  have hsqrt : 1 ≤ Real.sqrt L := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt hL
  linarith

theorem nearCarrierGapWidth_cast_sq_le_nine_mul
    (L : ℝ) (hL : 1 ≤ L) :
    (nearCarrierGapWidth L : ℝ) ^ 2 ≤ 9 * L := by
  have hgap := nearCarrierGapWidth_cast_le_three_sqrt L hL
  have hsq := pow_le_pow_left₀ (by positivity : 0 ≤ (nearCarrierGapWidth L : ℝ))
    hgap 2
  rw [mul_pow, show (3 : ℝ) ^ 2 = 9 by norm_num, Real.sq_sqrt (by linarith)] at hsq
  exact hsq

theorem nearCarrierHighCommonEnergyBound_toReal
    (a : ℝ) (H : ℕ) (ha : 0 < a) :
    (nearCarrierHighCommonEnergyBound a H).toReal =
      (H : ℝ) ^ 2 * (nearCarrierNonzeroEnergyConstant / a) := by
  have hprofile : 0 ≤
      8 * ((2 * nearGevreyProfileConstant) ^ 2 * (32 / a)) := by
    positivity
  simp only [nearCarrierHighCommonEnergyBound, ENNReal.toReal_mul,
    ENNReal.toReal_pow, ENNReal.toReal_natCast,
    ENNReal.toReal_ofReal hprofile]
  unfold nearCarrierNonzeroEnergyConstant
  field_simp

theorem nearCarrierPartialCommonEnergyBound_eq
    (a : ℝ) (ha : 0 < a) :
    nearCarrierPartialCommonEnergyBound a =
      nearCarrierNonzeroEnergyConstant / a := by
  unfold nearCarrierPartialCommonEnergyBound nearCarrierNonzeroEnergyConstant
  field_simp

theorem nearCarrierHighCommonEnergyBound_scaled_le
    (A L : ℝ) (hA : 0 < A) (hL : 1 ≤ L) :
    (nearCarrierHighCommonEnergyBound (A / L)
        (nearCarrierGapWidth L)).toReal / L ^ 2 ≤
      9 * nearCarrierNonzeroEnergyConstant / A := by
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  rw [nearCarrierHighCommonEnergyBound_toReal (A / L)
    (nearCarrierGapWidth L) (div_pos hA hLpos)]
  have hgap := nearCarrierGapWidth_cast_sq_le_nine_mul L hL
  have hC := nearCarrierNonzeroEnergyConstant_nonneg
  apply (div_le_iff₀ (sq_pos_of_pos hLpos)).2
  calc
    (nearCarrierGapWidth L : ℝ) ^ 2 *
        (nearCarrierNonzeroEnergyConstant / (A / L)) ≤
      (9 * L) * (nearCarrierNonzeroEnergyConstant / (A / L)) := by
        gcongr
    _ = (9 * nearCarrierNonzeroEnergyConstant / A) * L ^ 2 := by
      field_simp [hA.ne', hLpos.ne']

theorem nearCarrierPartialCommonEnergyBound_scaled_le
    (A L : ℝ) (hA : 0 < A) (hL : 1 ≤ L) :
    nearCarrierPartialCommonEnergyBound (A / L) / L ^ 2 ≤
      nearCarrierNonzeroEnergyConstant / A := by
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  rw [nearCarrierPartialCommonEnergyBound_eq (A / L) (div_pos hA hLpos)]
  have hC := nearCarrierNonzeroEnergyConstant_nonneg
  apply (div_le_iff₀ (sq_pos_of_pos hLpos)).2
  calc
    nearCarrierNonzeroEnergyConstant / (A / L) ≤
        (nearCarrierNonzeroEnergyConstant / A) * L ^ 2 := by
      field_simp [hA.ne', hLpos.ne']
      nlinarith

theorem nearCarrierLowBlockCount_cast_le_linear
    (N : ℕ) (L : ℝ) (hN : 1 ≤ N) (hL : 1 ≤ L)
    (hNL : Real.exp L = (N : ℝ)) :
    (nearCarrierLowBlockCount N L : ℝ) ≤
      nearCarrierBinaryLogLinearConstant * L := by
  have hNat : nearCarrierLowBlockCount N L ≤ Nat.clog 2 N := by
    calc
      nearCarrierLowBlockCount N L ≤ nearCarrierLogExponent N := by
        unfold nearCarrierLowBlockCount
        exact (Nat.sub_le _ _).trans (Nat.sub_le _ _)
      _ = Nat.log 2 N := rfl
      _ ≤ Nat.clog 2 N := Nat.log_le_clog 2 N
  have hcast : (nearCarrierLowBlockCount N L : ℝ) ≤
      (Nat.clog 2 N : ℝ) := by exact_mod_cast hNat
  have hclog := nat_clog_two_cast_le_log_div_add_one N hN
  have hlogN : Real.log (N : ℝ) = L := by
    rw [← hNL, Real.log_exp]
  rw [hlogN] at hclog
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  calc
    (nearCarrierLowBlockCount N L : ℝ) ≤ (Nat.clog 2 N : ℝ) := hcast
    _ ≤ L / Real.log 2 + 1 := hclog
    _ ≤ nearCarrierBinaryLogLinearConstant * L := by
      unfold nearCarrierBinaryLogLinearConstant
      have hLnonneg : 0 ≤ L := zero_le_one.trans hL
      field_simp [hlogTwo.ne']
      nlinarith

theorem nearCarrierLowCommonEnergyBound_toReal
    (A L : ℝ) (M : ℕ) (hA : 0 < A) (hL : 0 < L) :
    (nearCarrierLowCommonEnergyBound A L M).toReal =
      2 * (4 * (M : ℝ) *
          (nearCarrierNonzeroEnergyConstant / (A / L)) +
        (M : ℝ) ^ 2 * Real.exp (-(5 / 2 : ℝ) * L)) := by
  have hprofile : 0 ≤
      8 * ((2 * nearGevreyProfileConstant) ^ 2 * (32 / (A / L))) := by
    positivity
  have hexp : 0 ≤ Real.exp (-(5 / 2 : ℝ) * L) := Real.exp_pos _ |>.le
  unfold nearCarrierLowCommonEnergyBound
  rw [ENNReal.toReal_mul]
  rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_natCast, ENNReal.toReal_ofReal hprofile,
    ENNReal.toReal_ofReal hexp, ENNReal.toReal_ofNat]
  unfold nearCarrierNonzeroEnergyConstant
  field_simp [hA.ne', hL.ne']

theorem nearCarrierLowCommonEnergyBound_scaled_le
    (A L : ℝ) (N : ℕ) (hA : 0 < A) (hL : 1 ≤ L)
    (hN : 1 ≤ N) (hNL : Real.exp L = (N : ℝ)) :
    (nearCarrierLowCommonEnergyBound A L
        (nearCarrierLowBlockCount N L)).toReal / L ^ 2 ≤
      8 * nearCarrierBinaryLogLinearConstant *
          nearCarrierNonzeroEnergyConstant / A +
        2 * nearCarrierBinaryLogLinearConstant ^ 2 *
          Real.exp (-(5 / 2 : ℝ) * L) := by
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  let M : ℕ := nearCarrierLowBlockCount N L
  let D : ℝ := nearCarrierBinaryLogLinearConstant
  let C : ℝ := nearCarrierNonzeroEnergyConstant
  have hM : (M : ℝ) ≤ D * L := by
    simpa only [M, D] using!
      nearCarrierLowBlockCount_cast_le_linear N L hN hL hNL
  have hMnonneg : 0 ≤ (M : ℝ) := by positivity
  have hDLnonneg : 0 ≤ D * L := by
    dsimp [D]
    exact mul_nonneg (nearCarrierBinaryLogLinearConstant_pos.le) hLpos.le
  have hMsq : (M : ℝ) ^ 2 ≤ (D * L) ^ 2 :=
    pow_le_pow_left₀ hMnonneg hM 2
  have hC : 0 ≤ C := by
    dsimp [C]
    exact nearCarrierNonzeroEnergyConstant_nonneg
  have hscale : 0 ≤ C / (A / L) := by positivity
  have hexp : 0 ≤ Real.exp (-(5 / 2 : ℝ) * L) := Real.exp_pos _ |>.le
  rw [nearCarrierLowCommonEnergyBound_toReal A L M hA hLpos]
  calc
    2 * (4 * (M : ℝ) * (C / (A / L)) +
          (M : ℝ) ^ 2 * Real.exp (-(5 / 2 : ℝ) * L)) / L ^ 2 ≤
        2 * (4 * (D * L) * (C / (A / L)) +
          (D * L) ^ 2 * Real.exp (-(5 / 2 : ℝ) * L)) / L ^ 2 := by
      gcongr
    _ = 8 * D * C / A +
        2 * D ^ 2 * Real.exp (-(5 / 2 : ℝ) * L) := by
      field_simp [hA.ne', hLpos.ne']
      ring

private theorem sqrt_div_le_sqrt_of_div_sq_le
    {B C L : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C) (hL : 0 < L)
    (h : B / L ^ 2 ≤ C) :
    Real.sqrt B / L ≤ Real.sqrt C := by
  apply (sq_le_sq₀ (div_nonneg (Real.sqrt_nonneg B) hL.le)
    (Real.sqrt_nonneg C)).mp
  rw [div_pow, Real.sq_sqrt hB, Real.sq_sqrt hC]
  exact h

/-- The chosen ceiling `ceil(2 sqrt L)` supplies at least the (smaller)
exponential `L^(1/3)` frequency gap required by the Gevrey leakage estimate. -/
theorem exp_rpow_one_third_le_two_pow_nearCarrierGapWidth
    (L : ℝ) (hL : 1 ≤ L) :
    Real.exp (L ^ (1 / 3 : ℝ)) ≤
      ((2 ^ nearCarrierGapWidth L : ℕ) : ℝ) := by
  let x : ℝ := L ^ (1 / 3 : ℝ)
  let T : ℕ := nearCarrierGapWidth L
  have hx : 0 ≤ x := by
    dsimp [x]
    exact Real.rpow_nonneg (zero_le_one.trans hL) _
  have hxSqrt : x ≤ Real.sqrt L := by
    dsimp [x]
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hL (by norm_num)
  have hceil : 2 * Real.sqrt L ≤ (T : ℝ) := by
    dsimp [T, nearCarrierGapWidth]
    exact Nat.le_ceil _
  have hlog : (1 / 2 : ℝ) ≤ Real.log 2 := by
    exact (by norm_num : (1 / 2 : ℝ) < 0.6931471803).le.trans
      Real.log_two_gt_d9.le
  have hmul : x ≤ (T : ℝ) * Real.log 2 := by
    calc
      x ≤ Real.sqrt L := hxSqrt
      _ = (2 * Real.sqrt L) * (1 / 2 : ℝ) := by ring
      _ ≤ (T : ℝ) * Real.log 2 :=
        mul_le_mul hceil hlog (by positivity) (by positivity)
  calc
    Real.exp (L ^ (1 / 3 : ℝ)) = Real.exp x := by rfl
    _ ≤ Real.exp ((T : ℝ) * Real.log 2) := Real.exp_le_exp.mpr hmul
    _ = ((2 : ℝ) ^ T) := by
      rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    _ = ((2 ^ nearCarrierGapWidth L : ℕ) : ℝ) := by
      norm_num [T]

theorem pow_nearCarrierLogExponent_le
    (N : ℕ) (hN : 0 < N) :
    2 ^ nearCarrierLogExponent N ≤ N := by
  exact Nat.pow_log_le_self 2 hN.ne'

theorem lt_pow_nearCarrierLogExponent_add_one
    (N : ℕ) (hN : 0 < N) :
    N < 2 ^ (nearCarrierLogExponent N + 1) := by
  unfold nearCarrierLogExponent
  exact (Nat.log_lt_iff_lt_pow (by norm_num) hN.ne').mp
    (Nat.lt_succ_self (Nat.log 2 N))

/-- Once `L=log N` is large, the square-root-width gap fits strictly below
the largest binary exponent of `N`. -/
theorem nearCarrierGapWidth_add_one_le_logExponent
    (N : ℕ) (L : ℝ) (hN : 0 < N) (hL : 16 ≤ L)
    (hNL : Real.exp L = (N : ℝ)) :
    nearCarrierGapWidth L + 1 ≤ nearCarrierLogExponent N := by
  let T : ℕ := nearCarrierGapWidth L
  let R : ℕ := nearCarrierLogExponent N
  have hLpos : 0 < L := lt_of_lt_of_le (by norm_num) hL
  have hsqrt : Real.sqrt L ≤ L / 4 := by
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    · nlinarith
  have hceil : (T : ℝ) < 2 * Real.sqrt L + 1 := by
    dsimp [T, nearCarrierGapWidth]
    exact Nat.ceil_lt_add_one (by positivity)
  have hTbelow : ((T + 1 : ℕ) : ℝ) < L - 1 := by
    norm_num at hceil ⊢
    calc
      (T : ℝ) + 1 < 2 * Real.sqrt L + 2 := by linarith
      _ ≤ L / 2 + 2 := by linarith
      _ ≤ L - 1 := by linarith
  have hNupper : N ≤ 2 ^ (R + 1) := by
    dsimp [R]
    exact (lt_pow_nearCarrierLogExponent_add_one N hN).le
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
  have hpowReal : 0 < ((2 : ℝ) ^ (R + 1)) := by positivity
  have hlogMono : Real.log (N : ℝ) ≤
      Real.log ((2 : ℝ) ^ (R + 1)) := by
    exact Real.log_le_log hNreal (by exact_mod_cast hNupper)
  have hlogN : Real.log (N : ℝ) = L := by
    rw [← hNL, Real.log_exp]
  have hlogTwoUpper : Real.log 2 ≤ 1 :=
    Real.log_two_lt_d9.le.trans (by norm_num)
  rw [hlogN, Real.log_pow] at hlogMono
  have hLle : L ≤ (R : ℝ) + 1 := by
    calc
      L ≤ ((R + 1 : ℕ) : ℝ) * Real.log 2 := by
        simpa only [Nat.cast_add, Nat.cast_one] using! hlogMono
      _ ≤ ((R + 1 : ℕ) : ℝ) * 1 := by
        exact mul_le_mul_of_nonneg_left hlogTwoUpper (by positivity)
      _ = (R : ℝ) + 1 := by norm_num
  have hTRreal : ((T + 1 : ℕ) : ℝ) < (R : ℝ) :=
    hTbelow.trans_le (by linarith)
  exact_mod_cast hTRreal.le

theorem eventually_nearCarrierGapWidth_add_one_le_logExponent :
    ∀ᶠ N : ℕ in atTop,
      nearCarrierGapWidth (Real.log (N : ℝ)) + 1 ≤
        nearCarrierLogExponent N := by
  have hlog : Tendsto (fun N : ℕ ↦ Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlarge : ∀ᶠ N : ℕ in atTop, 16 ≤ Real.log (N : ℝ) :=
    hlog.eventually (eventually_ge_atTop 16)
  filter_upwards [hlarge, eventually_ge_atTop 1] with N hL hN
  exact nearCarrierGapWidth_add_one_le_logExponent
    N (Real.log (N : ℝ)) (by omega) hL (by
      rw [Real.exp_log]
      positivity)

/-- Every low dyadic block selected by the explicit square-root gap lies below
the carrier-separation cutoff `N exp(-L^(1/3))`. -/
theorem nearCarrierLowBlock_cutoff
    (N : ℕ) (L : ℝ) (hN : 0 < N) (hL : 1 ≤ L)
    (hroom : nearCarrierGapWidth L + 1 ≤ nearCarrierLogExponent N) :
    ∀ s ∈ nearCarrierDyadicExponents (nearCarrierLowBlockCount N L),
      (2 ^ s : ℕ) / (N : ℝ) ≤
        Real.exp (-L ^ (1 / 3 : ℝ)) := by
  intro s hs
  let T : ℕ := nearCarrierGapWidth L
  let R : ℕ := nearCarrierLogExponent N
  let M : ℕ := nearCarrierLowBlockCount N L
  have hTR : T ≤ R := by
    dsimp [T, R]
    omega
  have hM : M + 1 = R - T := by
    dsimp [M, nearCarrierLowBlockCount, T, R]
    omega
  have hsle : s ≤ R - T := by
    have hs' := (Finset.mem_Ico.mp hs).2
    rw [← hM]
    omega
  have hpowS : (2 ^ s : ℕ) ≤ 2 ^ (R - T) :=
    Nat.pow_le_pow_right (by omega) hsle
  have hpowProduct : 2 ^ (R - T) * 2 ^ T = (2 ^ R : ℕ) := by
    rw [← pow_add]
    congr 1
    omega
  have hpowR : 2 ^ R ≤ N := by
    dsimp [R]
    exact pow_nearCarrierLogExponent_le N hN
  have hgap : Real.exp (L ^ (1 / 3 : ℝ)) ≤ (2 ^ T : ℕ) := by
    simpa only [T, Nat.cast_pow, Nat.cast_ofNat] using!
      exp_rpow_one_third_le_two_pow_nearCarrierGapWidth L hL
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
  have hexp : 0 < Real.exp (L ^ (1 / 3 : ℝ)) := Real.exp_pos _
  rw [Real.exp_neg, inv_eq_one_div]
  rw [div_le_div_iff₀ hNreal hexp]
  norm_num
  calc
    (2 : ℝ) ^ s * Real.exp (L ^ (1 / 3 : ℝ)) ≤
        (2 : ℝ) ^ (R - T) * (2 : ℝ) ^ T := by
      exact mul_le_mul (by exact_mod_cast hpowS) (by simpa using! hgap)
        (Real.exp_pos _).le (by positivity)
    _ = (2 : ℝ) ^ R := by exact_mod_cast hpowProduct
    _ ≤ (N : ℝ) := by exact_mod_cast hpowR

/-- The low range ends exactly where the short high range begins. -/
theorem nearCarrier_low_high_boundary
    (N : ℕ) (L : ℝ) :
    2 ^ (nearCarrierLowBlockCount N L + 1) =
      (2 ^ nearCarrierHighStart N L) / 2 := by
  have hstart : nearCarrierHighStart N L =
      nearCarrierLowBlockCount N L + 1 + 1 := by
    simp [nearCarrierHighStart]
  rw [hstart, pow_succ]
  omega

/-- The short high range has exactly `nearCarrierGapWidth L` blocks and
ends at the largest power of two not exceeding `N`. -/
theorem nearCarrier_high_endpoint
    (N : ℕ) (L : ℝ)
    (hroom : nearCarrierGapWidth L + 1 ≤ nearCarrierLogExponent N) :
    (2 ^ (nearCarrierHighStart N L + nearCarrierGapWidth L)) / 2 =
      2 ^ nearCarrierLogExponent N := by
  have hexponent :
      nearCarrierHighStart N L + nearCarrierGapWidth L =
        nearCarrierLogExponent N + 1 := by
    unfold nearCarrierHighStart nearCarrierLowBlockCount
    omega
  rw [hexponent, pow_succ]
  omega

/-- The remaining literal interval `(2^R,N]` is contained in the final
dyadic block `(2^R,2^(R+1)]`. -/
theorem nearCarrier_terminal_partial_block_parameters
    (N : ℕ) (hN : 4 ≤ N) :
    let R := nearCarrierLogExponent N
    let P := 2 ^ (R + 1)
    P / 2 = 2 ^ R ∧ 4 ≤ P ∧ N ≤ P := by
  dsimp
  constructor
  · rw [pow_succ]
    omega
  constructor
  · have hRpos : 1 ≤ nearCarrierLogExponent N := by
      unfold nearCarrierLogExponent
      exact (Nat.le_log_iff_pow_le (by norm_num) (by omega)).2 (by omega)
    have hp := Nat.pow_le_pow_right (by omega : 0 < 2)
      (show 2 ≤ nearCarrierLogExponent N + 1 by omega)
    norm_num at hp
    exact hp
  · exact (lt_pow_nearCarrierLogExponent_add_one N (by omega)).le

/-! ## Exact three-range Hilbert-space decomposition -/

/-- With the explicit low/high/terminal split, the complete nonzero-carrier
series over the literal denominator range `2 < p ≤ N` is summable in
circle `L²`.  This statement is kept separate from the subsequent `tsum`
identity because Fourier uniqueness for the literal smooth shot needs the
summability proof itself, not merely an equality between already formed
`tsum`s. -/
theorem eventually_summable_smoothNearNonzeroCarrierL2Term_full
    (A ε : ℝ) (hA : 0 < A) (hε : 0 < ε) (hεhalf : ε < 1 / 2) :
    ∀ᶠ L : ℝ in atTop, ∀ (N : ℕ)
      (ha : 0 < A / L) (haε : A / L ≤ ε / 4),
      4 ≤ N → Real.exp L = (N : ℝ) → 1 ≤ L →
      nearCarrierGapWidth L + 1 ≤ nearCarrierLogExponent N →
      Summable
        (smoothNearNonzeroCarrierL2Term N (A / L) ε 2 N ha haε) := by
  filter_upwards [
      eventually_summable_smoothNearNonzeroCarrierL2Term_low
        A ε hA hε hεhalf] with L hlowEventually
  intro N ha haε hN hNL hL hroom
  let M : ℕ := nearCarrierLowBlockCount N L
  let S : ℕ := nearCarrierHighStart N L
  let H : ℕ := nearCarrierGapWidth L
  let R : ℕ := nearCarrierLogExponent N
  let Q₁ : ℕ := 2 ^ (M + 1)
  let Q₂ : ℕ := 2 ^ R
  have hNpos : 0 < N := by omega
  have hcut := nearCarrierLowBlock_cutoff N L hNpos hL hroom
  have hlow : Summable
      (smoothNearNonzeroCarrierL2Term N (A / L) ε 2 Q₁ ha haε) := by
    simpa only [M, Q₁] using!
      hlowEventually N M ha haε hNpos hNL hcut
  have hS : 2 ≤ S := by
    dsimp [S, nearCarrierHighStart]
    omega
  have hboundary : (2 ^ S) / 2 = Q₁ := by
    dsimp [S, Q₁, M]
    exact (nearCarrier_low_high_boundary N L).symm
  have hendpoint : (2 ^ (S + H)) / 2 = Q₂ := by
    dsimp [S, H, Q₂, R]
    exact nearCarrier_high_endpoint N L hroom
  have hhigh : Summable
      (smoothNearNonzeroCarrierL2Term N (A / L) ε Q₁ Q₂ ha haε) := by
    have hh := summable_smoothNearNonzeroCarrierL2Term_high
      N S H (A / L) ε hS ha hε haε hεhalf
    simpa only [hboundary, hendpoint] using! hh
  obtain ⟨hPdiv, hPfour, hNP⟩ :=
    nearCarrier_terminal_partial_block_parameters N hN
  have hpartial : Summable
      (smoothNearNonzeroCarrierL2Term N (A / L) ε Q₂ N ha haε) := by
    apply summable_smoothNearNonzeroCarrierL2Term_partial
      N (2 ^ (R + 1)) Q₂ N (A / L) ε
      (by simpa only [R] using! hPfour)
      (by simpa only [R, Q₂] using! hPdiv.le)
      (by simpa only [R] using! hNP)
      ha hε haε hεhalf
  have hQ₂N : Q₂ ≤ N := by
    dsimp [Q₂, R]
    exact pow_nearCarrierLogExponent_le N hNpos
  have hQ₁Q₂ : Q₁ ≤ Q₂ := by
    have hExp : M + 1 ≤ R := by
      dsimp [M, R, nearCarrierLowBlockCount]
      omega
    exact Nat.pow_le_pow_right (by omega) hExp
  have htwoQ₁ : 2 ≤ Q₁ := by
    have hExp : 1 ≤ M + 1 := by omega
    dsimp [Q₁]
    exact Nat.pow_le_pow_right (by omega : 0 < 2) hExp
  have hhighPartial : Summable
      (smoothNearNonzeroCarrierL2Term N (A / L) ε Q₁ N ha haε) := by
    exact (hhigh.add hpartial).congr fun ell ↦
      (smoothNearNonzeroCarrierL2Term_split
        N (A / L) ε Q₁ Q₂ N ha haε hQ₁Q₂ hQ₂N ell).symm
  exact (hlow.add hhighPartial).congr fun ell ↦
    (smoothNearNonzeroCarrierL2Term_split
      N (A / L) ε 2 Q₁ N ha haε htwoQ₁
        (hQ₁Q₂.trans hQ₂N) ell).symm

/-- For the explicit parameters, the complete nonzero-carrier tail is the
sum of the low separated range, the short high range, and the literal final
partial dyadic block.  All three infinite carrier series are proved
summable before the `tsum` is rearranged. -/
theorem eventually_smoothNearInfiniteNonzeroCarrierL2_eq_three_ranges
    (A ε : ℝ) (hA : 0 < A) (hε : 0 < ε) (hεhalf : ε < 1 / 2) :
    ∀ᶠ L : ℝ in atTop, ∀ (N : ℕ)
      (ha : 0 < A / L) (haε : A / L ≤ ε / 4),
      4 ≤ N → Real.exp L = (N : ℝ) → 1 ≤ L →
      nearCarrierGapWidth L + 1 ≤ nearCarrierLogExponent N →
      smoothNearInfiniteNonzeroCarrierL2 N (A / L) ε 2 N ha haε =
        smoothNearInfiniteNonzeroCarrierL2 N (A / L) ε 2
            (2 ^ (nearCarrierLowBlockCount N L + 1)) ha haε +
          (smoothNearInfiniteNonzeroCarrierL2 N (A / L) ε
              (2 ^ (nearCarrierLowBlockCount N L + 1))
              (2 ^ nearCarrierLogExponent N) ha haε +
            smoothNearInfiniteNonzeroCarrierL2 N (A / L) ε
              (2 ^ nearCarrierLogExponent N) N ha haε) := by
  filter_upwards [
      eventually_summable_smoothNearNonzeroCarrierL2Term_low
        A ε hA hε hεhalf] with L hlowEventually
  intro N ha haε hN hNL hL hroom
  let M : ℕ := nearCarrierLowBlockCount N L
  let S : ℕ := nearCarrierHighStart N L
  let H : ℕ := nearCarrierGapWidth L
  let R : ℕ := nearCarrierLogExponent N
  let Q₁ : ℕ := 2 ^ (M + 1)
  let Q₂ : ℕ := 2 ^ R
  have hNpos : 0 < N := by omega
  have hcut := nearCarrierLowBlock_cutoff N L hNpos hL hroom
  have hlow : Summable
      (smoothNearNonzeroCarrierL2Term N (A / L) ε 2 Q₁ ha haε) := by
    simpa only [M, Q₁] using!
      hlowEventually N M ha haε hNpos hNL hcut
  have hS : 2 ≤ S := by
    dsimp [S, nearCarrierHighStart]
    omega
  have hboundary : (2 ^ S) / 2 = Q₁ := by
    dsimp [S, Q₁, M]
    exact (nearCarrier_low_high_boundary N L).symm
  have hendpoint : (2 ^ (S + H)) / 2 = Q₂ := by
    dsimp [S, H, Q₂, R]
    exact nearCarrier_high_endpoint N L hroom
  have hhigh : Summable
      (smoothNearNonzeroCarrierL2Term N (A / L) ε Q₁ Q₂ ha haε) := by
    have hh := summable_smoothNearNonzeroCarrierL2Term_high
      N S H (A / L) ε hS ha hε haε hεhalf
    simpa only [hboundary, hendpoint] using! hh
  obtain ⟨hPdiv, hPfour, hNP⟩ := nearCarrier_terminal_partial_block_parameters N hN
  have hpartial : Summable
      (smoothNearNonzeroCarrierL2Term N (A / L) ε Q₂ N ha haε) := by
    apply summable_smoothNearNonzeroCarrierL2Term_partial
      N (2 ^ (R + 1)) Q₂ N (A / L) ε
      (by simpa only [R] using! hPfour)
      (by simpa only [R, Q₂] using! hPdiv.le)
      (by simpa only [R] using! hNP)
      ha hε haε hεhalf
  have hQ₂N : Q₂ ≤ N := by
    dsimp [Q₂, R]
    exact pow_nearCarrierLogExponent_le N hNpos
  have hQ₁Q₂ : Q₁ ≤ Q₂ := by
    have hExp : M + 1 ≤ R := by
      dsimp [M, R, nearCarrierLowBlockCount]
      omega
    exact Nat.pow_le_pow_right (by omega) hExp
  have htwoQ₁ : 2 ≤ Q₁ := by
    have hExp : 1 ≤ M + 1 := by omega
    dsimp [Q₁]
    exact Nat.pow_le_pow_right (by omega : 0 < 2) hExp
  have hhighPartial : Summable
      (smoothNearNonzeroCarrierL2Term N (A / L) ε Q₁ N ha haε) := by
    have hadd := hhigh.add hpartial
    exact hadd.congr fun ell ↦
      (smoothNearNonzeroCarrierL2Term_split
        N (A / L) ε Q₁ Q₂ N ha haε hQ₁Q₂ hQ₂N ell).symm
  have hrightSplit := smoothNearInfiniteNonzeroCarrierL2_split
    N (A / L) ε Q₁ Q₂ N ha haε hQ₁Q₂ hQ₂N hhigh hpartial
  have hfullSplit := smoothNearInfiniteNonzeroCarrierL2_split
    N (A / L) ε 2 Q₁ N ha haε htwoQ₁
      (hQ₁Q₂.trans hQ₂N) hlow hhighPartial
  dsimp only [Q₁, Q₂, M, R] at hfullSplit hrightSplit ⊢
  rw [hfullSplit, hrightSplit]

/-- Quantitative norm bound for the complete nonzero-carrier tail with all
three explicit denominator ranges displayed. -/
theorem eventually_norm_smoothNearInfiniteNonzeroCarrierL2_le_three_ranges
    (A ε : ℝ) (hA : 0 < A) (hε : 0 < ε) (hεhalf : ε < 1 / 2) :
    ∀ᶠ L : ℝ in atTop, ∀ (N : ℕ)
      (ha : 0 < A / L) (haε : A / L ≤ ε / 4),
      4 ≤ N → Real.exp L = (N : ℝ) → 1 ≤ L →
      nearCarrierGapWidth L + 1 ≤ nearCarrierLogExponent N →
      ‖smoothNearInfiniteNonzeroCarrierL2 N (A / L) ε 2 N ha haε‖ ≤
        windowCarrierMassConstant *
            Real.sqrt (nearCarrierLowCommonEnergyBound A L
              (nearCarrierLowBlockCount N L)).toReal +
          (windowCarrierMassConstant *
              Real.sqrt (nearCarrierHighCommonEnergyBound (A / L)
                (nearCarrierGapWidth L)).toReal +
            windowCarrierMassConstant *
              Real.sqrt (nearCarrierPartialCommonEnergyBound (A / L))) := by
  filter_upwards [
      eventually_smoothNearInfiniteNonzeroCarrierL2_eq_three_ranges
        A ε hA hε hεhalf,
      eventually_norm_smoothNearInfiniteNonzeroCarrierL2_low_le
        A ε hA hε hεhalf] with L hsplit hlow
  intro N ha haε hN hNL hL hroom
  let M : ℕ := nearCarrierLowBlockCount N L
  let S : ℕ := nearCarrierHighStart N L
  let H : ℕ := nearCarrierGapWidth L
  let R : ℕ := nearCarrierLogExponent N
  let Q₁ : ℕ := 2 ^ (M + 1)
  let Q₂ : ℕ := 2 ^ R
  have hNpos : 0 < N := by omega
  have hcut := nearCarrierLowBlock_cutoff N L hNpos hL hroom
  have hlowBound :
      ‖smoothNearInfiniteNonzeroCarrierL2 N (A / L) ε 2 Q₁ ha haε‖ ≤
        windowCarrierMassConstant *
          Real.sqrt (nearCarrierLowCommonEnergyBound A L M).toReal := by
    simpa only [M, Q₁] using! hlow N M ha haε hNpos hNL hcut
  have hS : 2 ≤ S := by
    dsimp [S, nearCarrierHighStart]
    omega
  have hboundary : (2 ^ S) / 2 = Q₁ := by
    dsimp [S, Q₁, M]
    exact (nearCarrier_low_high_boundary N L).symm
  have hendpoint : (2 ^ (S + H)) / 2 = Q₂ := by
    dsimp [S, H, Q₂, R]
    exact nearCarrier_high_endpoint N L hroom
  have hhighBound :
      ‖smoothNearInfiniteNonzeroCarrierL2
          N (A / L) ε Q₁ Q₂ ha haε‖ ≤
        windowCarrierMassConstant *
          Real.sqrt (nearCarrierHighCommonEnergyBound (A / L) H).toReal := by
    have hh := norm_smoothNearInfiniteNonzeroCarrierL2_high_le
      N S H (A / L) ε hS ha hε haε hεhalf
    simpa only [hboundary, hendpoint] using! hh
  obtain ⟨hPdiv, hPfour, hNP⟩ := nearCarrier_terminal_partial_block_parameters N hN
  have hpartialBound :
      ‖smoothNearInfiniteNonzeroCarrierL2
          N (A / L) ε Q₂ N ha haε‖ ≤
        windowCarrierMassConstant *
          Real.sqrt (nearCarrierPartialCommonEnergyBound (A / L)) := by
    apply norm_smoothNearInfiniteNonzeroCarrierL2_partial_le
      N (2 ^ (R + 1)) Q₂ N (A / L) ε
      (by simpa only [R] using! hPfour)
      (by simpa only [R, Q₂] using! hPdiv.le)
      (by simpa only [R] using! hNP)
      ha hε haε hεhalf
  have hsplit' := hsplit N ha haε hN hNL hL hroom
  rw [hsplit']
  exact (norm_add_le _ _).trans <| add_le_add hlowBound <|
    (norm_add_le _ _).trans (add_le_add hhighBound hpartialBound)

/-- The complete nonzero-carrier tail divided by `L` has an explicit
`O(A⁻¹/²)` bound, plus one exponentially vanishing leakage term. -/
theorem eventually_norm_smoothNearInfiniteNonzeroCarrierL2_div_log_le
    (A ε : ℝ) (hA : 0 < A) (hε : 0 < ε) (hεhalf : ε < 1 / 2) :
    ∀ᶠ L : ℝ in atTop, ∀ (N : ℕ)
      (ha : 0 < A / L) (haε : A / L ≤ ε / 4),
      4 ≤ N → Real.exp L = (N : ℝ) → 1 ≤ L →
      nearCarrierGapWidth L + 1 ≤ nearCarrierLogExponent N →
      ‖smoothNearInfiniteNonzeroCarrierL2 N (A / L) ε 2 N ha haε‖ / L ≤
        windowCarrierMassConstant * Real.sqrt
            (8 * nearCarrierBinaryLogLinearConstant *
                nearCarrierNonzeroEnergyConstant / A +
              2 * nearCarrierBinaryLogLinearConstant ^ 2 *
                Real.exp (-(5 / 2 : ℝ) * L)) +
          (windowCarrierMassConstant * Real.sqrt
              (9 * nearCarrierNonzeroEnergyConstant / A) +
            windowCarrierMassConstant * Real.sqrt
              (nearCarrierNonzeroEnergyConstant / A)) := by
  filter_upwards [
      eventually_norm_smoothNearInfiniteNonzeroCarrierL2_le_three_ranges
        A ε hA hε hεhalf] with L hnorm
  intro N ha haε hN hNL hL hroom
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  let B₁ : ℝ := (nearCarrierLowCommonEnergyBound A L
    (nearCarrierLowBlockCount N L)).toReal
  let B₂ : ℝ := (nearCarrierHighCommonEnergyBound (A / L)
    (nearCarrierGapWidth L)).toReal
  let B₃ : ℝ := nearCarrierPartialCommonEnergyBound (A / L)
  let C₁ : ℝ := 8 * nearCarrierBinaryLogLinearConstant *
      nearCarrierNonzeroEnergyConstant / A +
    2 * nearCarrierBinaryLogLinearConstant ^ 2 *
      Real.exp (-(5 / 2 : ℝ) * L)
  let C₂ : ℝ := 9 * nearCarrierNonzeroEnergyConstant / A
  let C₃ : ℝ := nearCarrierNonzeroEnergyConstant / A
  have hB₁ : 0 ≤ B₁ := ENNReal.toReal_nonneg
  have hB₂ : 0 ≤ B₂ := ENNReal.toReal_nonneg
  have hB₃ : 0 ≤ B₃ := by
    dsimp [B₃]
    exact nearCarrierPartialCommonEnergyBound_nonneg (A / L) ha
  have hC₁ : 0 ≤ C₁ := by
    dsimp [C₁]
    have hD := nearCarrierBinaryLogLinearConstant_pos.le
    have hC := nearCarrierNonzeroEnergyConstant_nonneg
    positivity
  have hC₂ : 0 ≤ C₂ := by
    dsimp [C₂]
    exact div_nonneg
      (mul_nonneg (by norm_num) nearCarrierNonzeroEnergyConstant_nonneg) hA.le
  have hC₃ : 0 ≤ C₃ := by
    dsimp [C₃]
    exact div_nonneg nearCarrierNonzeroEnergyConstant_nonneg hA.le
  have hscale₁ : B₁ / L ^ 2 ≤ C₁ := by
    dsimp [B₁, C₁]
    exact nearCarrierLowCommonEnergyBound_scaled_le A L N hA hL (by omega) hNL
  have hscale₂ : B₂ / L ^ 2 ≤ C₂ := by
    dsimp [B₂, C₂]
    exact nearCarrierHighCommonEnergyBound_scaled_le A L hA hL
  have hscale₃ : B₃ / L ^ 2 ≤ C₃ := by
    dsimp [B₃, C₃]
    exact nearCarrierPartialCommonEnergyBound_scaled_le A L hA hL
  have hsqrt₁ : Real.sqrt B₁ / L ≤ Real.sqrt C₁ :=
    sqrt_div_le_sqrt_of_div_sq_le hB₁ hC₁ hLpos hscale₁
  have hsqrt₂ : Real.sqrt B₂ / L ≤ Real.sqrt C₂ :=
    sqrt_div_le_sqrt_of_div_sq_le hB₂ hC₂ hLpos hscale₂
  have hsqrt₃ : Real.sqrt B₃ / L ≤ Real.sqrt C₃ :=
    sqrt_div_le_sqrt_of_div_sq_le hB₃ hC₃ hLpos hscale₃
  have hraw := hnorm N ha haε hN hNL hL hroom
  have hrawB :
      ‖smoothNearInfiniteNonzeroCarrierL2 N (A / L) ε 2 N ha haε‖ ≤
        windowCarrierMassConstant * Real.sqrt B₁ +
          (windowCarrierMassConstant * Real.sqrt B₂ +
            windowCarrierMassConstant * Real.sqrt B₃) := by
    simpa only [B₁, B₂, B₃] using! hraw
  have hW : 0 ≤ windowCarrierMassConstant :=
    windowCarrierMassConstant_nonneg
  calc
    ‖smoothNearInfiniteNonzeroCarrierL2 N (A / L) ε 2 N ha haε‖ / L ≤
        (windowCarrierMassConstant * Real.sqrt B₁ +
          (windowCarrierMassConstant * Real.sqrt B₂ +
            windowCarrierMassConstant * Real.sqrt B₃)) / L :=
      div_le_div_of_nonneg_right hrawB hLpos.le
    _ = windowCarrierMassConstant * (Real.sqrt B₁ / L) +
        (windowCarrierMassConstant * (Real.sqrt B₂ / L) +
          windowCarrierMassConstant * (Real.sqrt B₃ / L)) := by ring
    _ ≤ windowCarrierMassConstant * Real.sqrt C₁ +
        (windowCarrierMassConstant * Real.sqrt C₂ +
          windowCarrierMassConstant * Real.sqrt C₃) := by
      gcongr
    _ = windowCarrierMassConstant * Real.sqrt
            (8 * nearCarrierBinaryLogLinearConstant *
                nearCarrierNonzeroEnergyConstant / A +
              2 * nearCarrierBinaryLogLinearConstant ^ 2 *
                Real.exp (-(5 / 2 : ℝ) * L)) +
          (windowCarrierMassConstant * Real.sqrt
              (9 * nearCarrierNonzeroEnergyConstant / A) +
            windowCarrierMassConstant * Real.sqrt
              (nearCarrierNonzeroEnergyConstant / A)) := by
      rfl

end

end Erdos1002
