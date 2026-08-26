import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import ErdosProblems.Erdos1002.NearResonantCarrierSeries
import ErdosProblems.Erdos1002.NearResonantUnconditionalBridge
import ErdosProblems.Erdos1002.RealFourierConjugacy

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Global frequency assembly for the zero Bernoulli carrier

The nonzero carriers are separated by their large modulation.  The zero
carrier instead uses the natural multiplier scale `n ≈ p²/a`.  This file
starts the global assembly by summing every complete denominator shell below
that scale with its retained localized variation factor.
-/

open Filter MeasureTheory Set Finset
open scoped BigOperators ComplexConjugate ENNReal Real

namespace Erdos1002

noncomputable section

def nearZeroLowDyadicExponents (R : ℕ) : Finset ℕ :=
  Finset.Ico 1 (R + 1)

def nearZeroLowDyadicVector
    (a ε : ℝ) (K R : ℕ) : NearDyadicEuclidean K :=
  ∑ r ∈ nearZeroLowDyadicExponents R,
    finiteNearRamanujanMultiplierVector
      a ε K (2 ^ r + 1) (2 * 2 ^ r)

private theorem sum_pow_two_nearZeroLowDyadicExponents_le (R : ℕ) :
    (∑ r ∈ nearZeroLowDyadicExponents R, (2 : ℝ) ^ r) ≤
      (2 : ℝ) ^ (R + 1) := by
  unfold nearZeroLowDyadicExponents
  rw [Finset.sum_Ico_eq_sub (fun r : ℕ ↦ (2 : ℝ) ^ r)
    (by omega : 1 ≤ R + 1)]
  rw [geom_sum_eq (by norm_num : (2 : ℝ) ≠ 1),
    geom_sum_eq (by norm_num : (2 : ℝ) ≠ 1)]
  norm_num
  linarith

/-- Scalar normalization used at the principal denominator scale: if
`q² ≤ ax`, then the low-shell factor `q/(a√x)` is at most `a⁻¹/²`.
-/
theorem div_mul_sqrt_le_inv_sqrt_of_sq_le
    (a x q : ℝ) (ha : 0 < a) (hx : 0 < x) (hq : 0 ≤ q)
    (hsq : q ^ 2 ≤ a * x) :
    q / (a * Real.sqrt x) ≤ 1 / Real.sqrt a := by
  have hsqrta : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
  have hsqrtx : 0 < Real.sqrt x := Real.sqrt_pos.2 hx
  have hroot : q ≤ Real.sqrt a * Real.sqrt x := by
    rw [← sq_le_sq₀ hq (mul_nonneg hsqrta.le hsqrtx.le)]
    rw [mul_pow, Real.sq_sqrt ha.le, Real.sq_sqrt hx.le]
    exact hsq
  apply (div_le_iff₀ (mul_pos ha hsqrtx)).2
  calc
    q ≤ Real.sqrt a * Real.sqrt x := hroot
    _ = (1 / Real.sqrt a) * (a * Real.sqrt x) := by
      field_simp [hsqrta.ne']
      rw [Real.sq_sqrt ha.le]

/-- Complementary scalar normalization: if `ax ≤ (2q)²`, then the
tail factor `√x/q` is at most `2a⁻¹/²`.
-/
theorem sqrt_div_le_two_inv_sqrt_of_le_sq
    (a x q : ℝ) (ha : 0 < a) (hx : 0 < x) (hq : 0 < q)
    (hsq : a * x ≤ (2 * q) ^ 2) :
    Real.sqrt x / q ≤ 2 / Real.sqrt a := by
  have hsqrta : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
  have hsqrtx : 0 < Real.sqrt x := Real.sqrt_pos.2 hx
  have hroot : Real.sqrt a * Real.sqrt x ≤ 2 * q := by
    rw [← sq_le_sq₀ (mul_nonneg hsqrta.le hsqrtx.le) (by positivity)]
    rw [mul_pow, Real.sq_sqrt ha.le, Real.sq_sqrt hx.le]
    exact hsq
  apply (div_le_iff₀ hq).2
  calc
    Real.sqrt x ≤ 2 * q / Real.sqrt a := by
      apply (le_div_iff₀ hsqrta).2
      simpa only [mul_comm] using! hroot
    _ = (2 / Real.sqrt a) * q := by ring

/-- A principal dyadic denominator endpoint always exists once `aK ≥ 16`.
The returned exponent has exactly the two bracketing inequalities consumed
by the normalized zero-carrier block estimate. -/
theorem exists_nearZeroPrincipalExponent
    (a : ℝ) (K : ℕ) (ha : 0 < a) (hK : 0 < K)
    (hlarge : 16 ≤ a * (K : ℝ)) :
    ∃ R : ℕ,
      ((2 ^ (R + 1) : ℕ) : ℝ) ^ 2 ≤ a * (K : ℝ) ∧
        a * (K : ℝ) ≤
          (2 * ((2 ^ (R + 1) : ℕ) : ℝ)) ^ 2 := by
  have hprod : 0 < a * (K : ℝ) := by positivity
  have hsqrtFour : (4 : ℝ) ≤ Real.sqrt (a * (K : ℝ)) := by
    rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 4)]
    apply Real.sqrt_le_sqrt
    norm_num
    exact hlarge
  obtain ⟨n, hnlow, hnhigh⟩ :=
    exists_nat_pow_near
      (show (1 : ℝ) ≤ Real.sqrt (a * (K : ℝ)) by linarith)
      (show (1 : ℝ) < 2 by norm_num)
  have hnTwo : 2 ≤ n := by
    by_contra hn
    have hnle : n ≤ 1 := by omega
    rw [Real.sqrt_mul ha.le] at hsqrtFour
    interval_cases n <;> norm_num at hnhigh <;> linarith
  refine ⟨n - 1, ?_, ?_⟩
  · have hindex : n - 1 + 1 = n := by omega
    rw [hindex]
    norm_num only [Nat.cast_pow, Nat.cast_ofNat]
    have hsq := (sq_le_sq₀ (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ n)
      (Real.sqrt_nonneg _)).2 hnlow
    rwa [Real.sq_sqrt hprod.le] at hsq
  · have hindex : n - 1 + 1 = n := by omega
    rw [hindex]
    have hupper : Real.sqrt (a * (K : ℝ)) ≤
        2 * (((2 ^ n : ℕ) : ℝ)) := by
      calc
        Real.sqrt (a * (K : ℝ)) ≤ (2 : ℝ) ^ (n + 1) := hnhigh.le
        _ = 2 * (((2 ^ n : ℕ) : ℝ)) := by
          push_cast
          rw [pow_succ]
          ring
    rw [← Real.sq_sqrt hprod.le]
    exact (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).2 hupper

/-- The canonical integer ceiling `sqrt K + 1` straddles `sqrt K` with the
exact inequalities required by the unconditional Ramanujan tail theorem.
-/
theorem nearZeroNatSqrtCeiling_spec (K : ℕ) (hK : 0 < K) :
    2 ≤ Nat.sqrt K + 1 ∧
      (Nat.sqrt K + 1 - 1) ^ 2 ≤ K ∧
      K ≤ (Nat.sqrt K + 1) ^ 2 := by
  have hsqrtPos : 0 < Nat.sqrt K := Nat.sqrt_pos.2 hK
  constructor
  · omega
  constructor
  · simpa using! Nat.sqrt_le' K
  · exact (Nat.lt_succ_sqrt' K).le

/-- Because `a ≤ ε/4 < 1/8`, a principal denominator endpoint lying
below `sqrt(aK)` is strictly below the integer square-root boundary.  This
discharges the nontrivial separation hypothesis in the cross-boundary tail.
-/
theorem nearZeroPrincipalEndpoint_lt_natSqrt
    (a ε : ℝ) (K R : ℕ)
    (haε : a ≤ ε / 4) (hεhalf : ε < 1 / 2) (hK : 0 < K)
    (hband : ((2 ^ (R + 1) : ℕ) : ℝ) ^ 2 ≤ a * (K : ℝ)) :
    2 ^ (R + 1) < Nat.sqrt K := by
  let Q : ℕ := 2 ^ (R + 1)
  have hKR : 0 < (K : ℝ) := by exact_mod_cast hK
  have haEighth : a < (1 : ℝ) / 8 := by linarith
  have haK : a * (K : ℝ) < (K : ℝ) / 8 := by
    nlinarith
  have hQsq : ((Q : ℝ) ^ 2) < (K : ℝ) / 8 := by
    have hbandQ : (Q : ℝ) ^ 2 ≤ a * (K : ℝ) := by
      simpa only [Q] using! hband
    exact hbandQ.trans_lt haK
  have hQone : (1 : ℝ) ≤ (Q : ℝ) := by
    exact_mod_cast (show 1 ≤ Q by
      dsimp [Q]
      exact Nat.one_le_two_pow)
  have hsuccSqReal : (((Q + 1) ^ 2 : ℕ) : ℝ) ≤ (K : ℝ) := by
    push_cast
    nlinarith [sq_nonneg ((Q : ℝ) - 1)]
  have hsuccSq : (Q + 1) ^ 2 ≤ K := by exact_mod_cast hsuccSqReal
  have hle : Q + 1 ≤ Nat.sqrt K := Nat.le_sqrt'.2 hsuccSq
  dsimp [Q] at hle ⊢
  omega

/-- Complete low-denominator shell aggregation on one positive-frequency
block.  The hypothesis says that the last dyadic endpoint is still below
the principal scale `sqrt(aK)`. -/
theorem norm_nearZeroLowDyadicVector_le
    (a ε : ℝ) (K R : ℕ)
    (ha : 0 < a) (hε : 0 < ε) (haε : a ≤ ε / 4)
    (hεhalf : ε < 1 / 2) (hK : 0 < K)
    (hband : ((2 ^ (R + 1) : ℕ) : ℝ) ^ 2 ≤ a * (K : ℝ)) :
    ‖nearZeroLowDyadicVector a ε K R‖ ≤
      192 * Real.sqrt 42 * Real.pi * nearProfileDecayConstant *
        ((2 ^ (R + 1) : ℕ) : ℝ) /
          (a * Real.sqrt (K : ℝ)) := by
  let C : ℝ := 192 * Real.sqrt 42 * Real.pi * nearProfileDecayConstant
  have haOne : a ≤ 1 := by linarith
  have hKR : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
  have hden : 0 < a * Real.sqrt (K : ℝ) :=
    mul_pos ha (Real.sqrt_pos.2 hKR)
  have hshell (r : ℕ) (hr : r ∈ nearZeroLowDyadicExponents R) :
      ‖finiteNearRamanujanMultiplierVector
          a ε K (2 ^ r + 1) (2 * 2 ^ r)‖ ≤
        C * ((2 : ℝ) ^ r) / (a * Real.sqrt (K : ℝ)) := by
    have hrBounds := Finset.mem_Ico.mp hr
    have hpow : 2 ^ r ≤ 2 ^ (R + 1) :=
      Nat.pow_le_pow_right (by omega : 0 < 2) hrBounds.2.le
    have hpowSq : ((2 ^ r : ℕ) : ℝ) ^ 2 ≤
        ((2 ^ (R + 1) : ℕ) : ℝ) ^ 2 := by
      gcongr
    have hQKReal : ((2 ^ r : ℕ) : ℝ) ^ 2 ≤ (K : ℝ) := by
      calc
        ((2 ^ r : ℕ) : ℝ) ^ 2 ≤
            ((2 ^ (R + 1) : ℕ) : ℝ) ^ 2 := hpowSq
        _ ≤ a * (K : ℝ) := hband
        _ ≤ (K : ℝ) := by
          nlinarith
    have hQK : (2 ^ r) ^ 2 ≤ K := by exact_mod_cast hQKReal
    simpa only [C, Nat.cast_pow, Nat.cast_ofNat] using!
      norm_finiteNearRamanujanMultiplierVector_dyadic_le_lowDenominator_normalized
        a ε K (2 ^ r) ha hε haε hK (by positivity) hQK
  calc
    ‖nearZeroLowDyadicVector a ε K R‖ ≤
        ∑ r ∈ nearZeroLowDyadicExponents R,
          ‖finiteNearRamanujanMultiplierVector
            a ε K (2 ^ r + 1) (2 * 2 ^ r)‖ := by
      unfold nearZeroLowDyadicVector
      exact norm_sum_le _ _
    _ ≤ ∑ r ∈ nearZeroLowDyadicExponents R,
        C * ((2 : ℝ) ^ r) / (a * Real.sqrt (K : ℝ)) := by
      apply Finset.sum_le_sum
      intro r hr
      exact hshell r hr
    _ = C * (∑ r ∈ nearZeroLowDyadicExponents R, (2 : ℝ) ^ r) /
        (a * Real.sqrt (K : ℝ)) := by
      rw [Finset.mul_sum]
      simp only [div_eq_mul_inv]
      rw [Finset.sum_mul]
    _ ≤ C * ((2 : ℝ) ^ (R + 1)) /
        (a * Real.sqrt (K : ℝ)) := by
      have hC : 0 ≤ C := by
        dsimp [C]
        exact mul_nonneg
          (mul_nonneg
            (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
            Real.pi_nonneg)
          nearProfileDecayConstant_nonneg
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left
          (sum_pow_two_nearZeroLowDyadicExponents_le R) hC) hden.le
    _ = 192 * Real.sqrt 42 * Real.pi * nearProfileDecayConstant *
        ((2 ^ (R + 1) : ℕ) : ℝ) /
          (a * Real.sqrt (K : ℝ)) := by
      dsimp [C]
      push_cast
      rfl

/-- A possibly incomplete final denominator shell below the principal
scale.  This is the endpoint-flexible version needed for an arbitrary
natural cutoff `U`, rather than only a power of two. -/
theorem norm_finiteNearRamanujanMultiplierVector_partialDyadic_le_lowDenominator
    (a ε : ℝ) (K Q U : ℕ)
    (ha : 0 < a) (hε : 0 < ε) (haε : a ≤ ε / 4)
    (hK : 0 < K) (hQ : 0 < Q) (hQU : Q < U)
    (hU2Q : U ≤ 2 * Q) (hQK : Q ^ 2 ≤ K) :
    ‖finiteNearRamanujanMultiplierVector a ε K (Q + 1) U‖ ≤
      192 * Real.sqrt 42 * Real.pi * nearProfileDecayConstant * (Q : ℝ) /
        (a * Real.sqrt (K : ℝ)) := by
  have hstart : Q + 1 ≤ U := by omega
  have hraw := norm_euclidean_vector_sum_coordinateMul_le
    (nearRamanujanVectorTerm K)
    (fun p ↦ nearJDyadicMultiplierVector a ε K (p : ℝ))
    hstart (Real.sqrt (42 * (K : ℝ) / (Q : ℝ) ^ 2))
    (fun R hR ↦
      norm_euclideanIntervalPartialSum_nearRamanujan_dyadic_le_lowRange
        K Q R hQ hQK (by
          exact Finset.mem_Icc.mpr ⟨( Finset.mem_Icc.mp hR).1,
            (Finset.mem_Icc.mp hR).2.trans hU2Q⟩))
  rw [show
      (∑ n ∈ Finset.Icc (Q + 1) U,
        euclideanCoordinateMul (nearRamanujanVectorTerm K n)
          (nearJDyadicMultiplierVector a ε K (n : ℝ))) =
        finiteNearRamanujanMultiplierVector a ε K (Q + 1) U by rfl] at hraw
  have hvar :=
    nearJDyadicMultiplierVector_terminal_add_variation_le_lowDenominator
      a ε K (Q + 1) U ha hε haε hK (by omega) hstart
  have hfirst := hraw.trans (mul_le_mul_of_nonneg_left hvar
    (Real.sqrt_nonneg _))
  have hUReal : (U : ℝ) ≤ 2 * (Q : ℝ) := by exact_mod_cast hU2Q
  have hUsq : (U : ℝ) ^ 2 ≤ (2 * (Q : ℝ)) ^ 2 := by gcongr
  have hconst : 0 ≤ 48 * Real.pi * nearProfileDecayConstant := by
    exact mul_nonneg
      (mul_nonneg (by norm_num) Real.pi_nonneg)
      nearProfileDecayConstant_nonneg
  have hden : 0 < a * (K : ℝ) := by positivity
  have hreplace :
      48 * Real.pi * nearProfileDecayConstant * (U : ℝ) ^ 2 /
          (a * (K : ℝ)) ≤
        48 * Real.pi * nearProfileDecayConstant * (2 * (Q : ℝ)) ^ 2 /
          (a * (K : ℝ)) := by
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hUsq hconst) hden.le
  have hQR : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQ
  have hKR : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
  have hsqrtK : 0 < Real.sqrt (K : ℝ) := Real.sqrt_pos.2 hKR
  have hKsqrt : (K : ℝ) = Real.sqrt (K : ℝ) ^ 2 :=
    (Real.sq_sqrt hKR.le).symm
  calc
    ‖finiteNearRamanujanMultiplierVector a ε K (Q + 1) U‖ ≤
      Real.sqrt (42 * (K : ℝ) / (Q : ℝ) ^ 2) *
        (48 * Real.pi * nearProfileDecayConstant * (U : ℝ) ^ 2 /
          (a * (K : ℝ))) := hfirst
    _ ≤ Real.sqrt (42 * (K : ℝ) / (Q : ℝ) ^ 2) *
        (48 * Real.pi * nearProfileDecayConstant * (2 * (Q : ℝ)) ^ 2 /
          (a * (K : ℝ))) :=
      mul_le_mul_of_nonneg_left hreplace (Real.sqrt_nonneg _)
    _ = 192 * Real.sqrt 42 * Real.pi * nearProfileDecayConstant * (Q : ℝ) /
        (a * Real.sqrt (K : ℝ)) := by
      rw [hKsqrt, Real.sqrt_div (by positivity),
        Real.sqrt_mul (by norm_num), Real.sqrt_sq (Real.sqrt_nonneg _),
        Real.sqrt_sq (by positivity)]
      field_simp [hQR.ne', hsqrtK.ne', ha.ne']
      ring

/-- The complete low shells are not merely an estimate: together they are
exactly the single denominator interval `2 < p ≤ 2^(R+1)`.  Recording this
identity prevents a hidden endpoint loss when the shell bounds are assembled.
-/
theorem nearZeroLowDyadicVector_eq_interval
    (a ε : ℝ) (K R : ℕ) :
    nearZeroLowDyadicVector a ε K R =
      finiteNearRamanujanMultiplierVector a ε K 3 (2 ^ (R + 1)) := by
  induction R with
  | zero =>
      simp [nearZeroLowDyadicVector, nearZeroLowDyadicExponents,
        finiteNearRamanujanMultiplierVector]
  | succ R ih =>
      let f : ℕ → NearDyadicEuclidean K := fun p ↦
        euclideanCoordinateMul (nearRamanujanVectorTerm K p)
          (nearJDyadicMultiplierVector a ε K (p : ℝ))
      have hstep :
          nearZeroLowDyadicVector a ε K (R + 1) =
            nearZeroLowDyadicVector a ε K R +
              finiteNearRamanujanMultiplierVector a ε K
                (2 ^ (R + 1) + 1) (2 ^ (R + 2)) := by
        unfold nearZeroLowDyadicVector nearZeroLowDyadicExponents
        rw [Finset.sum_Ico_succ_top (by omega : 1 ≤ R + 1)]
        congr 2
        simp only [pow_succ]
        ring
      rw [hstep, ih]
      rw [finiteNearRamanujanMultiplierVector_eq_sum_Ioc a ε K 2,
        finiteNearRamanujanMultiplierVector_eq_sum_Ioc a ε K (2 ^ (R + 1)),
        finiteNearRamanujanMultiplierVector_eq_sum_Ioc a ε K 2]
      have htwo : 2 ≤ 2 ^ (R + 1) := by
        have hone : 1 ≤ 2 ^ R := Nat.one_le_two_pow
        rw [pow_succ]
        nlinarith
      exact Finset.sum_Ioc_consecutive f htwo
        (Nat.pow_le_pow_right (by omega : 0 < 2) (by omega))

/-- Arbitrary-cutoff low-denominator estimate.  A floor dyadic logarithm
splits `2 < p ≤ U` into complete geometric shells and at most one partial
shell, so no power-of-two assumption on the natural cutoff is made. -/
theorem norm_finiteNearRamanujanMultiplierVector_three_le_lowDenominator
    (a ε : ℝ) (K U : ℕ)
    (ha : 0 < a) (hε : 0 < ε) (haε : a ≤ ε / 4)
    (hεhalf : ε < 1 / 2) (hK : 0 < K) (hU : 2 ≤ U)
    (hscale : ((U : ℝ) ^ 2) ≤ a * (K : ℝ)) :
    ‖finiteNearRamanujanMultiplierVector a ε K 3 U‖ ≤
      384 * Real.sqrt 42 * Real.pi * nearProfileDecayConstant * (U : ℝ) /
        (a * Real.sqrt (K : ℝ)) := by
  let m : ℕ := Nat.log 2 U
  let Q : ℕ := 2 ^ m
  have hUne : U ≠ 0 := by omega
  have hm : 1 ≤ m := by
    dsimp [m]
    exact Nat.log_pos Nat.one_lt_two hU
  have hQpos : 0 < Q := by
    dsimp [Q]
    positivity
  have hQtwo : 2 ≤ Q := by
    dsimp [Q]
    exact Nat.pow_le_pow_right (by omega : 0 < 2) hm
  have hQU : Q ≤ U := by
    dsimp [Q, m]
    exact Nat.pow_log_le_self 2 hUne
  have hU2Q : U ≤ 2 * Q := by
    have hlt := Nat.lt_pow_succ_log_self Nat.one_lt_two U
    dsimp [Q, m]
    rw [pow_succ] at hlt
    omega
  have hQscale : ((Q : ℝ) ^ 2) ≤ a * (K : ℝ) := by
    have hcast : (Q : ℝ) ≤ (U : ℝ) := by exact_mod_cast hQU
    exact (sq_le_sq₀ (by positivity) (by positivity)).2 hcast |>.trans hscale
  have hQKReal : (Q : ℝ) ^ 2 ≤ (K : ℝ) := by
    calc
      (Q : ℝ) ^ 2 ≤ a * (K : ℝ) := hQscale
      _ ≤ (K : ℝ) := by
        have haOne : a ≤ 1 := by linarith
        nlinarith [show (0 : ℝ) ≤ (K : ℝ) by positivity]
  have hQK : Q ^ 2 ≤ K := by exact_mod_cast hQKReal
  have hRindex : m - 1 + 1 = m := by omega
  have hlow :
      ‖finiteNearRamanujanMultiplierVector a ε K 3 Q‖ ≤
        192 * Real.sqrt 42 * Real.pi * nearProfileDecayConstant * (Q : ℝ) /
          (a * Real.sqrt (K : ℝ)) := by
    have hlow' := norm_nearZeroLowDyadicVector_le
      a ε K (m - 1) ha hε haε hεhalf hK (by
        simpa only [hRindex, Q] using! hQscale)
    rw [nearZeroLowDyadicVector_eq_interval, hRindex] at hlow'
    simpa only [Q] using! hlow'
  have hconst : 0 ≤
      192 * Real.sqrt 42 * Real.pi * nearProfileDecayConstant := by
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
        Real.pi_nonneg)
      nearProfileDecayConstant_nonneg
  have hden : 0 < a * Real.sqrt (K : ℝ) := by positivity
  have hreplace :
      192 * Real.sqrt 42 * Real.pi * nearProfileDecayConstant * (Q : ℝ) /
          (a * Real.sqrt (K : ℝ)) ≤
        192 * Real.sqrt 42 * Real.pi * nearProfileDecayConstant * (U : ℝ) /
          (a * Real.sqrt (K : ℝ)) := by
    apply div_le_div_of_nonneg_right _ hden.le
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hQU) hconst
  by_cases hEq : Q = U
  · rw [← hEq]
    exact hlow.trans <| calc
      192 * Real.sqrt 42 * Real.pi * nearProfileDecayConstant * (Q : ℝ) /
          (a * Real.sqrt (K : ℝ)) ≤
        2 * (192 * Real.sqrt 42 * Real.pi * nearProfileDecayConstant * (Q : ℝ) /
          (a * Real.sqrt (K : ℝ))) := by
            have hnonneg : 0 ≤
                192 * Real.sqrt 42 * Real.pi * nearProfileDecayConstant * (Q : ℝ) /
                  (a * Real.sqrt (K : ℝ)) := by positivity
            linarith
      _ = 384 * Real.sqrt 42 * Real.pi * nearProfileDecayConstant * (Q : ℝ) /
          (a * Real.sqrt (K : ℝ)) := by ring
  · have hQltU : Q < U := hQU.lt_of_ne hEq
    have hpartial :=
      norm_finiteNearRamanujanMultiplierVector_partialDyadic_le_lowDenominator
        a ε K Q U ha hε haε hK hQpos hQltU hU2Q hQK
    have hsplit :
        finiteNearRamanujanMultiplierVector a ε K 3 U =
          finiteNearRamanujanMultiplierVector a ε K 3 Q +
            finiteNearRamanujanMultiplierVector a ε K (Q + 1) U := by
      let f : ℕ → NearDyadicEuclidean K := fun p ↦
        euclideanCoordinateMul (nearRamanujanVectorTerm K p)
          (nearJDyadicMultiplierVector a ε K (p : ℝ))
      rw [finiteNearRamanujanMultiplierVector_eq_sum_Ioc a ε K 2,
        finiteNearRamanujanMultiplierVector_eq_sum_Ioc a ε K 2,
        finiteNearRamanujanMultiplierVector_eq_sum_Ioc a ε K Q]
      exact (Finset.sum_Ioc_consecutive f hQtwo hQU).symm
    rw [hsplit]
    calc
      ‖finiteNearRamanujanMultiplierVector a ε K 3 Q +
          finiteNearRamanujanMultiplierVector a ε K (Q + 1) U‖ ≤
        ‖finiteNearRamanujanMultiplierVector a ε K 3 Q‖ +
          ‖finiteNearRamanujanMultiplierVector a ε K (Q + 1) U‖ :=
        norm_add_le _ _
      _ ≤
        192 * Real.sqrt 42 * Real.pi * nearProfileDecayConstant * (Q : ℝ) /
            (a * Real.sqrt (K : ℝ)) +
          192 * Real.sqrt 42 * Real.pi * nearProfileDecayConstant * (Q : ℝ) /
            (a * Real.sqrt (K : ℝ)) := add_le_add hlow hpartial
      _ ≤
        2 * (192 * Real.sqrt 42 * Real.pi * nearProfileDecayConstant * (U : ℝ) /
          (a * Real.sqrt (K : ℝ))) := by linarith
      _ = 384 * Real.sqrt 42 * Real.pi * nearProfileDecayConstant * (U : ℝ) /
          (a * Real.sqrt (K : ℝ)) := by ring

/-- Physical-space form of the arbitrary-cutoff low-denominator estimate.
This supplies the geometrically decaying high-frequency tail once
`U² ≤ aK`. -/
theorem norm_smoothNearPrimitivePoleTailDyadicProjection_two_le_highFrequency
    (a ε : ℝ) (K U : ℕ)
    (ha : 0 < a) (hε : 0 < ε) (haε : a ≤ ε / 4)
    (hεhalf : ε < 1 / 2) (hK : 0 < K) (hU : 2 ≤ U)
    (hscale : ((U : ℝ) ^ 2) ≤ a * (K : ℝ)) :
    ‖smoothNearPrimitivePoleTailDyadicProjection a ε K 2 U ha haε‖ ≤
      384 * Real.sqrt 42 * Real.pi * nearProfileDecayConstant * (U : ℝ) /
        (a * Real.sqrt (K : ℝ)) := by
  rw [norm_smoothNearPrimitivePoleTailDyadicProjection_eq_vector
    a ε K 2 U (by norm_num) ha hε haε hεhalf.le]
  exact norm_finiteNearRamanujanMultiplierVector_three_le_lowDenominator
    a ε K U ha hε haε hεhalf hK hU hscale

/-- Elementary inverse-geometric tail on a finite dyadic exponent range. -/
private theorem sum_inv_pow_two_Ico_le (S H : ℕ) :
    (∑ s ∈ Finset.Ico S H, 1 / (2 : ℝ) ^ s) ≤
      2 / (2 : ℝ) ^ S := by
  have h := geom_sum_Ico_le_of_lt_one
    (m := S) (n := H) (x := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
  calc
    (∑ s ∈ Finset.Ico S H, 1 / (2 : ℝ) ^ s) =
        ∑ s ∈ Finset.Ico S H, (1 / 2 : ℝ) ^ s := by
      apply Finset.sum_congr rfl
      intro s _hs
      simp only [one_div]
      exact (inv_pow (2 : ℝ) s).symm
    _ ≤ (1 / 2 : ℝ) ^ S / (1 - (1 / 2 : ℝ)) := h
    _ = 2 / (2 : ℝ) ^ S := by
      rw [one_div, inv_pow]
      field_simp
      ring

/-- The complete high-frequency square tail over any finite consecutive
dyadic range is `O(1/a)`, uniformly in its upper endpoint. -/
theorem sum_sq_norm_smoothNearPrimitivePoleTailDyadicProjection_high_le
    (a ε : ℝ) (U S H : ℕ)
    (ha : 0 < a) (hε : 0 < ε) (haε : a ≤ ε / 4)
    (hεhalf : ε < 1 / 2) (hU : 2 ≤ U)
    (hscale : ((U : ℝ) ^ 2) ≤ a * ((2 ^ S : ℕ) : ℝ)) :
    ∑ s ∈ Finset.Ico S H,
        ‖smoothNearPrimitivePoleTailDyadicProjection
          a ε (2 ^ s) 2 U ha haε‖ ^ 2 ≤
      2 * (384 * Real.sqrt 42 * Real.pi * nearProfileDecayConstant) ^ 2 / a := by
  let C : ℝ := 384 * Real.sqrt 42 * Real.pi * nearProfileDecayConstant
  have hC : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) Real.pi_nonneg)
      nearProfileDecayConstant_nonneg
  have hsumBlocks :
      ∑ s ∈ Finset.Ico S H,
          ‖smoothNearPrimitivePoleTailDyadicProjection
            a ε (2 ^ s) 2 U ha haε‖ ^ 2 ≤
        C ^ 2 * (U : ℝ) ^ 2 / a ^ 2 *
          ∑ s ∈ Finset.Ico S H, 1 / (2 : ℝ) ^ s := by
    calc
      ∑ s ∈ Finset.Ico S H,
          ‖smoothNearPrimitivePoleTailDyadicProjection
            a ε (2 ^ s) 2 U ha haε‖ ^ 2 ≤
        ∑ s ∈ Finset.Ico S H,
          C ^ 2 * (U : ℝ) ^ 2 / a ^ 2 * (1 / (2 : ℝ) ^ s) := by
        apply Finset.sum_le_sum
        intro s hs
        have hsBounds := Finset.mem_Ico.mp hs
        have hscaleS : a * ((2 ^ S : ℕ) : ℝ) ≤
            a * ((2 ^ s : ℕ) : ℝ) := by
          apply mul_le_mul_of_nonneg_left _ ha.le
          exact_mod_cast Nat.pow_le_pow_right (by omega : 0 < 2) hsBounds.1
        have hscaleS' : (U : ℝ) ^ 2 ≤
            a * ((2 ^ s : ℕ) : ℝ) := hscale.trans hscaleS
        have hnorm :=
          norm_smoothNearPrimitivePoleTailDyadicProjection_two_le_highFrequency
            a ε (2 ^ s) U ha hε haε hεhalf (by positivity) hU hscaleS'
        have hsq := (sq_le_sq₀ (norm_nonneg _)
          (div_nonneg (mul_nonneg hC (by positivity)) (by positivity))).2 hnorm
        calc
          ‖smoothNearPrimitivePoleTailDyadicProjection
              a ε (2 ^ s) 2 U ha haε‖ ^ 2 ≤
            (C * (U : ℝ) / (a * Real.sqrt ((2 ^ s : ℕ) : ℝ))) ^ 2 := by
              simpa only [C] using! hsq
          _ = C ^ 2 * (U : ℝ) ^ 2 / a ^ 2 * (1 / (2 : ℝ) ^ s) := by
            simp only [div_pow, mul_pow]
            rw [Real.sq_sqrt (by positivity)]
            norm_num only [Nat.cast_pow, Nat.cast_ofNat]
            field_simp [ha.ne']
      _ = C ^ 2 * (U : ℝ) ^ 2 / a ^ 2 *
          ∑ s ∈ Finset.Ico S H, 1 / (2 : ℝ) ^ s := by
        rw [Finset.mul_sum]
  have hpowPos : 0 < (2 : ℝ) ^ S := by positivity
  have hscaleReal : (U : ℝ) ^ 2 ≤ a * (2 : ℝ) ^ S := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using! hscale
  have hratio : (U : ℝ) ^ 2 / (a * (2 : ℝ) ^ S) ≤ 1 := by
    apply (div_le_one₀ (mul_pos ha hpowPos)).2
    exact hscaleReal
  have hfactor : 0 ≤ 2 * C ^ 2 / a := by positivity
  calc
    ∑ s ∈ Finset.Ico S H,
        ‖smoothNearPrimitivePoleTailDyadicProjection
          a ε (2 ^ s) 2 U ha haε‖ ^ 2 ≤
      C ^ 2 * (U : ℝ) ^ 2 / a ^ 2 *
        ∑ s ∈ Finset.Ico S H, 1 / (2 : ℝ) ^ s := hsumBlocks
    _ ≤ C ^ 2 * (U : ℝ) ^ 2 / a ^ 2 *
        (2 / (2 : ℝ) ^ S) := by
      gcongr
      exact sum_inv_pow_two_Ico_le S H
    _ ≤ 2 * C ^ 2 / a := by
      calc
        C ^ 2 * (U : ℝ) ^ 2 / a ^ 2 * (2 / (2 : ℝ) ^ S) =
            (2 * C ^ 2 / a) *
              ((U : ℝ) ^ 2 / (a * (2 : ℝ) ^ S)) := by
          field_simp [ha.ne', hpowPos.ne']
        _ ≤ (2 * C ^ 2 / a) * 1 :=
          mul_le_mul_of_nonneg_left hratio hfactor
        _ = 2 * C ^ 2 / a := by ring
    _ = 2 * (384 * Real.sqrt 42 * Real.pi * nearProfileDecayConstant) ^ 2 / a := by
      rfl

/-! ## Zero and negative frequencies -/

/-- The cutoff profile is complex-valued only for Fourier convenience; its
pointwise values are real. -/
theorem nearRho_star (a ε x : ℝ) :
    starRingEnd ℂ (nearRho a ε x) = nearRho a ε x := by
  simp [nearRho, scaledNearProfile, nearBaseProfile]

/-- The smooth zero-carrier pole is pointwise real-valued. -/
theorem smoothNearPrimitivePoleTail_star
    (a ε : ℝ) (Q U : ℕ) (alpha : ℝ) :
    starRingEnd ℂ (smoothNearPrimitivePoleTail a ε Q U alpha) =
      smoothNearPrimitivePoleTail a ε Q U alpha := by
  simp [smoothNearPrimitivePoleTail, smoothNearPrimitivePoleSum,
    nearPoleCell, nearW, nearRho_star]

/-- The canonical circle representative is pointwise real-valued. -/
theorem smoothNearPrimitivePoleTailCircle_star
    (a ε : ℝ) (Q U : ℕ) (x : AddCircle (1 : ℝ)) :
    starRingEnd ℂ (smoothNearPrimitivePoleTailCircle a ε Q U x) =
      smoothNearPrimitivePoleTailCircle a ε Q U x := by
  unfold smoothNearPrimitivePoleTailCircle
  have hcomp :
      AddCircle.liftIoc (1 : ℝ) 0
          ((starRingEnd ℂ) ∘ smoothNearPrimitivePoleTail a ε Q U) x =
        starRingEnd ℂ
          (AddCircle.liftIoc (1 : ℝ) 0
            (smoothNearPrimitivePoleTail a ε Q U) x) :=
    AddCircle.liftIoc_comp_apply
  rw [← hcomp]
  congr 1
  funext alpha
  exact smoothNearPrimitivePoleTail_star a ε Q U alpha

/-- Exact conjugacy of negative and positive Fourier coefficients for the
finite smooth zero carrier. -/
theorem fourierCoeff_smoothNearPrimitivePoleTailL2_neg
    (a ε : ℝ) (Q U : ℕ) (ha : 0 < a) (haε : a ≤ ε / 4)
    (n : ℤ) :
    fourierCoeff
        (smoothNearPrimitivePoleTailL2 a ε Q U ha haε :
          AddCircle (1 : ℝ) → ℂ) (-n) =
      starRingEnd ℂ
        (fourierCoeff
          (smoothNearPrimitivePoleTailL2 a ε Q U ha haε :
            AddCircle (1 : ℝ) → ℂ) n) := by
  apply fourierCoeff_neg_eq_conj_of_ae_real
  filter_upwards [smoothNearPrimitivePoleTailL2_coe_ae
    a ε Q U ha haε] with x hx
  rw [hx]
  exact smoothNearPrimitivePoleTailCircle_star a ε Q U x

/-- The zero Fourier coefficient vanishes exactly because `J_a(0)=0`. -/
theorem fourierCoeff_smoothNearPrimitivePoleTailL2_zero
    (a ε : ℝ) (Q U : ℕ)
    (hQ : 0 < Q) (ha : 0 < a) (hε : 0 < ε)
    (haε : a ≤ ε / 4) (hεhalf : ε ≤ 1 / 2) :
    fourierCoeff
        (smoothNearPrimitivePoleTailL2 a ε Q U ha haε :
          AddCircle (1 : ℝ) → ℂ) 0 = 0 := by
  rw [show (0 : ℤ) = ((0 : ℕ) : ℤ) by norm_num,
    fourierCoeff_smoothNearPrimitivePoleTailL2_nat,
    unitFourierCoefficient_smoothNearPrimitivePoleTail_eq
      a ε Q U 0 hQ ha hε haε hεhalf]
  simp [nearJ_zero]

/-- Direct positive-block Parseval identity, stated before any Ramanujan
coefficient replacement. -/
theorem norm_sq_smoothNearPrimitivePoleTailDyadicProjection_eq_sum
    (a ε : ℝ) (K Q U : ℕ) (ha : 0 < a) (haε : a ≤ ε / 4) :
    ‖smoothNearPrimitivePoleTailDyadicProjection a ε K Q U ha haε‖ ^ 2 =
      ∑ n ∈ Finset.Ioc K (2 * K),
        ‖fourierCoeff
          (smoothNearPrimitivePoleTailL2 a ε Q U ha haε :
            AddCircle (1 : ℝ) → ℂ) (n : ℤ)‖ ^ 2 := by
  unfold smoothNearPrimitivePoleTailDyadicProjection
  simpa using!
    (orthonormal_fourier.orthogonalFamily.norm_sum
      (fun n : ℤ ↦ fourierCoeff
        (smoothNearPrimitivePoleTailL2 a ε Q U ha haε :
          AddCircle (1 : ℝ) → ℂ) n)
      ((Finset.Ioc K (2 * K)).map
        ⟨(fun n : ℕ ↦ (n : ℤ)), fun _ _ h ↦ Int.ofNat_inj.mp h⟩))

/-- The dyadic blocks `K=1,2,4,…,2^(H-1)` partition exactly the positive
integer frequencies `1<n≤2^H`; every endpoint occurs once. -/
theorem sum_sq_norm_smoothNearPrimitivePoleTailDyadicProjection_range_eq
    (a ε : ℝ) (Q U H : ℕ) (ha : 0 < a) (haε : a ≤ ε / 4) :
    ∑ s ∈ Finset.range H,
        ‖smoothNearPrimitivePoleTailDyadicProjection
          a ε (2 ^ s) Q U ha haε‖ ^ 2 =
      ∑ n ∈ Finset.Ioc (1 : ℕ) (2 ^ H),
        ‖fourierCoeff
          (smoothNearPrimitivePoleTailL2 a ε Q U ha haε :
            AddCircle (1 : ℝ) → ℂ) (n : ℤ)‖ ^ 2 := by
  induction H with
  | zero => simp
  | succ H ih =>
      rw [Finset.sum_range_succ, ih,
        norm_sq_smoothNearPrimitivePoleTailDyadicProjection_eq_sum]
      have hpow : 2 * 2 ^ H = 2 ^ (H + 1) := by
        rw [pow_succ]
        ring
      rw [hpow]
      exact Finset.sum_Ioc_consecutive
        (fun n : ℕ ↦
          ‖fourierCoeff
            (smoothNearPrimitivePoleTailL2 a ε Q U ha haε :
              AddCircle (1 : ℝ) → ℂ) (n : ℤ)‖ ^ 2)
        Nat.one_le_two_pow
        (Nat.pow_le_pow_right (by omega : 0 < 2) (Nat.le_succ H))

/-- Exact cut of the denominator interval at `Q`.  This is the endpoint
identity used when the low geometric shells are joined to the elementary
square-root tail. -/
theorem finiteNearRamanujanMultiplierVector_split_at
    (a ε : ℝ) (K Q U : ℕ) (hQ : 2 ≤ Q) (hQU : Q ≤ U) :
    finiteNearRamanujanMultiplierVector a ε K 3 U =
      finiteNearRamanujanMultiplierVector a ε K 3 Q +
        finiteNearRamanujanMultiplierVector a ε K (Q + 1) U := by
  let f : ℕ → NearDyadicEuclidean K := fun p ↦
    euclideanCoordinateMul (nearRamanujanVectorTerm K p)
      (nearJDyadicMultiplierVector a ε K (p : ℝ))
  rw [finiteNearRamanujanMultiplierVector_eq_sum_Ioc a ε K 2,
    finiteNearRamanujanMultiplierVector_eq_sum_Ioc a ε K 2,
    finiteNearRamanujanMultiplierVector_eq_sum_Ioc a ε K Q]
  exact (Finset.sum_Ioc_consecutive f hQ hQU).symm

/-- One complete zero-carrier frequency block, with every denominator up to
`U`, obtained by joining the exact low-shell aggregation to the unconditional
tail across `sqrt K`.  All endpoint and scale hypotheses are explicit.
-/
theorem norm_finiteNearRamanujanMultiplierVector_le_lowShells_add_tail
    (a ε : ℝ) (K R P U : ℕ)
    (ha : 0 < a) (hε : 0 < ε) (haε : a ≤ ε / 4)
    (hεhalf : ε < 1 / 2) (hK : 0 < K)
    (hband : ((2 ^ (R + 1) : ℕ) : ℝ) ^ 2 ≤ a * (K : ℝ))
    (hP : 2 ≤ P) (hQP : 2 ^ (R + 1) < P - 1)
    (hPm1K : (P - 1) ^ 2 ≤ K) (hKP : K ≤ P ^ 2)
    (hPU : P < U) :
    ‖finiteNearRamanujanMultiplierVector a ε K 3 U‖ ≤
      192 * Real.sqrt 42 * Real.pi * nearProfileDecayConstant *
          ((2 ^ (R + 1) : ℕ) : ℝ) /
            (a * Real.sqrt (K : ℝ)) +
        (2 * Real.sqrt 42 * Real.sqrt (K : ℝ) /
            ((2 ^ (R + 1) : ℕ) : ℝ)) *
            (64 * Real.pi * nearProfileDecayConstant) +
        (16 * Real.sqrt 54 + 64 * Real.sqrt 42) * Real.pi *
            nearProfileDecayConstant * (ε / 2 + a) *
            (K : ℝ) / (P : ℝ) ^ 2 := by
  let Q : ℕ := 2 ^ (R + 1)
  have hQpos : 0 < Q := by
    dsimp [Q]
    positivity
  have hQU : Q ≤ U := by
    exact hQP.le.trans ((Nat.sub_le P 1).trans hPU.le)
  have hsplit := finiteNearRamanujanMultiplierVector_split_at
    a ε K Q U (by
      dsimp [Q]
      have hone : 1 ≤ 2 ^ R := Nat.one_le_two_pow
      rw [pow_succ]
      nlinarith) hQU
  have hlow :
      ‖finiteNearRamanujanMultiplierVector a ε K 3 Q‖ ≤
        192 * Real.sqrt 42 * Real.pi * nearProfileDecayConstant *
          (Q : ℝ) / (a * Real.sqrt (K : ℝ)) := by
    rw [← nearZeroLowDyadicVector_eq_interval a ε K R]
    simpa only [Q] using! norm_nearZeroLowDyadicVector_le
      a ε K R ha hε haε hεhalf hK hband
  have htail :=
    norm_finiteNearRamanujanMultiplierVector_tail_le_unconditional
      a ε K Q P U ha hε haε hK hQpos hP hQP hPm1K hKP hPU
  rw [hsplit]
  calc
    ‖finiteNearRamanujanMultiplierVector a ε K 3 Q +
        finiteNearRamanujanMultiplierVector a ε K (Q + 1) U‖ ≤
        ‖finiteNearRamanujanMultiplierVector a ε K 3 Q‖ +
          ‖finiteNearRamanujanMultiplierVector a ε K (Q + 1) U‖ :=
      norm_add_le _ _
    _ ≤
        192 * Real.sqrt 42 * Real.pi * nearProfileDecayConstant *
            (Q : ℝ) / (a * Real.sqrt (K : ℝ)) +
          ((2 * Real.sqrt 42 * Real.sqrt (K : ℝ) / (Q : ℝ)) *
              (64 * Real.pi * nearProfileDecayConstant) +
            (16 * Real.sqrt 54 + 64 * Real.sqrt 42) * Real.pi *
              nearProfileDecayConstant * (ε / 2 + a) *
              (K : ℝ) / (P : ℝ) ^ 2) := add_le_add hlow htail
    _ =
        192 * Real.sqrt 42 * Real.pi * nearProfileDecayConstant *
            ((2 ^ (R + 1) : ℕ) : ℝ) /
              (a * Real.sqrt (K : ℝ)) +
          (2 * Real.sqrt 42 * Real.sqrt (K : ℝ) /
              ((2 ^ (R + 1) : ℕ) : ℝ)) *
              (64 * Real.pi * nearProfileDecayConstant) +
          (16 * Real.sqrt 54 + 64 * Real.sqrt 42) * Real.pi *
              nearProfileDecayConstant * (ε / 2 + a) *
              (K : ℝ) / (P : ℝ) ^ 2 := by
        dsimp [Q]
        ring

/-- Physical-space version of the preceding full-denominator block bound.
The left side is the genuine positive-frequency Fourier projection of the
smooth near pole over `2 < p ≤ U`; no formal coefficient surrogate remains.
-/
theorem norm_smoothNearPrimitivePoleTailDyadicProjection_two_le_lowShells_add_tail
    (a ε : ℝ) (K R P U : ℕ)
    (ha : 0 < a) (hε : 0 < ε) (haε : a ≤ ε / 4)
    (hεhalf : ε < 1 / 2) (hK : 0 < K)
    (hband : ((2 ^ (R + 1) : ℕ) : ℝ) ^ 2 ≤ a * (K : ℝ))
    (hP : 2 ≤ P) (hQP : 2 ^ (R + 1) < P - 1)
    (hPm1K : (P - 1) ^ 2 ≤ K) (hKP : K ≤ P ^ 2)
    (hPU : P < U) :
    ‖smoothNearPrimitivePoleTailDyadicProjection a ε K 2 U ha haε‖ ≤
      192 * Real.sqrt 42 * Real.pi * nearProfileDecayConstant *
          ((2 ^ (R + 1) : ℕ) : ℝ) /
            (a * Real.sqrt (K : ℝ)) +
        (2 * Real.sqrt 42 * Real.sqrt (K : ℝ) /
            ((2 ^ (R + 1) : ℕ) : ℝ)) *
            (64 * Real.pi * nearProfileDecayConstant) +
        (16 * Real.sqrt 54 + 64 * Real.sqrt 42) * Real.pi *
            nearProfileDecayConstant * (ε / 2 + a) *
            (K : ℝ) / (P : ℝ) ^ 2 := by
  rw [norm_smoothNearPrimitivePoleTailDyadicProjection_eq_vector
    a ε K 2 U (by norm_num) ha hε haε hεhalf.le]
  exact norm_finiteNearRamanujanMultiplierVector_le_lowShells_add_tail
    a ε K R P U ha hε haε hεhalf hK hband hP hQP hPm1K hKP hPU

/-- Scale-normalized form of the physical block estimate.  The additional
hypothesis says that the selected dyadic endpoint is maximal up to one
doubling, so both the low and tail pieces are `O(a⁻¹/²)` uniformly in the
frequency block `K`.
-/
theorem norm_smoothNearPrimitivePoleTailDyadicProjection_two_le_principalScale
    (a ε : ℝ) (K R P U : ℕ)
    (ha : 0 < a) (hε : 0 < ε) (haε : a ≤ ε / 4)
    (hεhalf : ε < 1 / 2) (hK : 0 < K)
    (hband : ((2 ^ (R + 1) : ℕ) : ℝ) ^ 2 ≤ a * (K : ℝ))
    (hnext : a * (K : ℝ) ≤
      (2 * ((2 ^ (R + 1) : ℕ) : ℝ)) ^ 2)
    (hP : 2 ≤ P) (hQP : 2 ^ (R + 1) < P - 1)
    (hPm1K : (P - 1) ^ 2 ≤ K) (hKP : K ≤ P ^ 2)
    (hPU : P < U) :
    ‖smoothNearPrimitivePoleTailDyadicProjection a ε K 2 U ha haε‖ ≤
      192 * Real.sqrt 42 * Real.pi * nearProfileDecayConstant /
          Real.sqrt a +
        (4 * Real.sqrt 42 / Real.sqrt a) *
          (64 * Real.pi * nearProfileDecayConstant) +
        (16 * Real.sqrt 54 + 64 * Real.sqrt 42) * Real.pi *
          nearProfileDecayConstant * (ε / 2 + a) *
          (K : ℝ) / (P : ℝ) ^ 2 := by
  let Qr : ℝ := ((2 ^ (R + 1) : ℕ) : ℝ)
  have hKR : 0 < (K : ℝ) := by exact_mod_cast hK
  have hQr : 0 < Qr := by
    dsimp [Qr]
    positivity
  have hlowScalar :
      Qr / (a * Real.sqrt (K : ℝ)) ≤ 1 / Real.sqrt a :=
    div_mul_sqrt_le_inv_sqrt_of_sq_le a (K : ℝ) Qr
      ha hKR hQr.le (by simpa only [Qr] using! hband)
  have htailScalar :
      Real.sqrt (K : ℝ) / Qr ≤ 2 / Real.sqrt a :=
    sqrt_div_le_two_inv_sqrt_of_le_sq a (K : ℝ) Qr
      ha hKR hQr (by simpa only [Qr] using! hnext)
  have hprofile : 0 ≤ nearProfileDecayConstant :=
    nearProfileDecayConstant_nonneg
  have hlow :
      192 * Real.sqrt 42 * Real.pi * nearProfileDecayConstant * Qr /
          (a * Real.sqrt (K : ℝ)) ≤
        192 * Real.sqrt 42 * Real.pi * nearProfileDecayConstant /
          Real.sqrt a := by
    calc
      192 * Real.sqrt 42 * Real.pi * nearProfileDecayConstant * Qr /
          (a * Real.sqrt (K : ℝ)) =
        (192 * Real.sqrt 42 * Real.pi * nearProfileDecayConstant) *
          (Qr / (a * Real.sqrt (K : ℝ))) := by ring
      _ ≤ (192 * Real.sqrt 42 * Real.pi * nearProfileDecayConstant) *
          (1 / Real.sqrt a) := by
        exact mul_le_mul_of_nonneg_left hlowScalar (by positivity)
      _ = 192 * Real.sqrt 42 * Real.pi * nearProfileDecayConstant /
          Real.sqrt a := by ring
  have htail :
      (2 * Real.sqrt 42 * Real.sqrt (K : ℝ) / Qr) *
          (64 * Real.pi * nearProfileDecayConstant) ≤
        (4 * Real.sqrt 42 / Real.sqrt a) *
          (64 * Real.pi * nearProfileDecayConstant) := by
    calc
      (2 * Real.sqrt 42 * Real.sqrt (K : ℝ) / Qr) *
          (64 * Real.pi * nearProfileDecayConstant) =
        ((2 * Real.sqrt 42) * (Real.sqrt (K : ℝ) / Qr)) *
          (64 * Real.pi * nearProfileDecayConstant) := by ring
      _ ≤ ((2 * Real.sqrt 42) * (2 / Real.sqrt a)) *
          (64 * Real.pi * nearProfileDecayConstant) := by
        gcongr
      _ = (4 * Real.sqrt 42 / Real.sqrt a) *
          (64 * Real.pi * nearProfileDecayConstant) := by ring
  have hraw :=
    norm_smoothNearPrimitivePoleTailDyadicProjection_two_le_lowShells_add_tail
      a ε K R P U ha hε haε hεhalf hK hband hP hQP hPm1K hKP hPU
  dsimp [Qr] at hlow htail
  exact hraw.trans (add_le_add (add_le_add hlow htail) le_rfl)

/-- A fixed explicit constant for the zero-carrier principal-scale block.
-/
def nearZeroPrincipalScaleConstant : ℝ :=
  192 * Real.sqrt 42 * Real.pi * nearProfileDecayConstant +
    4 * Real.sqrt 42 * (64 * Real.pi * nearProfileDecayConstant) +
    (16 * Real.sqrt 54 + 64 * Real.sqrt 42) * Real.pi *
      nearProfileDecayConstant

theorem nearZeroPrincipalScaleConstant_nonneg :
    0 ≤ nearZeroPrincipalScaleConstant := by
  unfold nearZeroPrincipalScaleConstant
  have hprofile : 0 ≤ nearProfileDecayConstant :=
    nearProfileDecayConstant_nonneg
  have hpi : 0 ≤ Real.pi := Real.pi_nonneg
  have hs42 : 0 ≤ Real.sqrt 42 := Real.sqrt_nonneg _
  have hs54 : 0 ≤ Real.sqrt 54 := Real.sqrt_nonneg _
  positivity

/-- Explicit constant for the initial positive-frequency blocks, where the
principal denominator scale is below the first nontrivial dyadic shell. -/
def nearZeroInitialFrequencyConstant : ℝ :=
  Real.sqrt 42 * (64 * Real.pi * nearProfileDecayConstant) +
    (16 * Real.sqrt 54 + 64 * Real.sqrt 42) * Real.pi *
      nearProfileDecayConstant

theorem nearZeroInitialFrequencyConstant_nonneg :
    0 ≤ nearZeroInitialFrequencyConstant := by
  unfold nearZeroInitialFrequencyConstant
  have hprofile : 0 ≤ nearProfileDecayConstant :=
    nearProfileDecayConstant_nonneg
  have hpi : 0 ≤ Real.pi := Real.pi_nonneg
  have hs42 : 0 ≤ Real.sqrt 42 := Real.sqrt_nonneg _
  have hs54 : 0 ≤ Real.sqrt 54 := Real.sqrt_nonneg _
  positivity

/-- Crude but summable estimate for the initial dyadic frequency blocks.
It grows only like `√K`, so its squared norms form a geometric series up to
the principal threshold `K ≈ 1/a`.
-/
theorem norm_smoothNearPrimitivePoleTailDyadicProjection_two_le_initial
    (a ε : ℝ) (K U : ℕ)
    (ha : 0 < a) (hε : 0 < ε) (haε : a ≤ ε / 4)
    (hεhalf : ε < 1 / 2) (hK : 9 ≤ K)
    (hU : Nat.sqrt K + 1 < U) :
    ‖smoothNearPrimitivePoleTailDyadicProjection a ε K 2 U ha haε‖ ≤
      nearZeroInitialFrequencyConstant * Real.sqrt (K : ℝ) := by
  have hKpos : 0 < K := by omega
  obtain ⟨hP, hPm1K, hKP⟩ := nearZeroNatSqrtCeiling_spec K hKpos
  have hsqrtThree : 3 ≤ Nat.sqrt K := by
    apply Nat.le_sqrt'.2
    norm_num
    exact hK
  have hQP : 2 < Nat.sqrt K + 1 - 1 := by omega
  have hraw := norm_smoothNearPrimitivePoleTailDyadicProjection_le_unconditional
    a ε K 2 (Nat.sqrt K + 1) U ha hε haε hεhalf.le
      hKpos (by norm_num) hP hQP hPm1K hKP hU
  have hscale0 : 0 ≤ ε / 2 + a := by positivity
  have hscale1 : ε / 2 + a ≤ 1 := by linarith
  have hPpos : 0 < ((Nat.sqrt K + 1 : ℕ) : ℝ) ^ 2 := by positivity
  have hratio : (K : ℝ) / ((Nat.sqrt K + 1 : ℕ) : ℝ) ^ 2 ≤ 1 := by
    apply (div_le_one₀ hPpos).2
    exact_mod_cast hKP
  let D : ℝ := (16 * Real.sqrt 54 + 64 * Real.sqrt 42) * Real.pi *
    nearProfileDecayConstant
  have hD : 0 ≤ D := by
    dsimp [D]
    exact mul_nonneg
      (mul_nonneg
        (add_nonneg
          (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
          (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)))
        Real.pi_nonneg)
      nearProfileDecayConstant_nonneg
  have hthird :
      D * (ε / 2 + a) * (K : ℝ) /
          ((Nat.sqrt K + 1 : ℕ) : ℝ) ^ 2 ≤ D := by
    calc
      D * (ε / 2 + a) * (K : ℝ) /
          ((Nat.sqrt K + 1 : ℕ) : ℝ) ^ 2 =
        (D * (ε / 2 + a)) *
          ((K : ℝ) / ((Nat.sqrt K + 1 : ℕ) : ℝ) ^ 2) := by ring
      _ ≤ (D * 1) * 1 := by gcongr
      _ = D := by ring
  have hsqrtOne : (1 : ℝ) ≤ Real.sqrt (K : ℝ) := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt (by exact_mod_cast (show 1 ≤ K by omega))
  have hthirdSqrt :
      D * (ε / 2 + a) * (K : ℝ) /
          ((Nat.sqrt K + 1 : ℕ) : ℝ) ^ 2 ≤
        D * Real.sqrt (K : ℝ) :=
    hthird.trans (by
      simpa only [mul_one] using! mul_le_mul_of_nonneg_left hsqrtOne hD)
  calc
    ‖smoothNearPrimitivePoleTailDyadicProjection a ε K 2 U ha haε‖ ≤
        (2 * Real.sqrt 42 * Real.sqrt (K : ℝ) / (2 : ℝ)) *
            (64 * Real.pi * nearProfileDecayConstant) +
          D * (ε / 2 + a) * (K : ℝ) /
            ((Nat.sqrt K + 1 : ℕ) : ℝ) ^ 2 := by
      simpa only [D, Nat.cast_ofNat] using! hraw
    _ ≤
        (2 * Real.sqrt 42 * Real.sqrt (K : ℝ) / (2 : ℝ)) *
            (64 * Real.pi * nearProfileDecayConstant) +
          D * Real.sqrt (K : ℝ) := add_le_add le_rfl hthirdSqrt
    _ = nearZeroInitialFrequencyConstant * Real.sqrt (K : ℝ) := by
      unfold nearZeroInitialFrequencyConstant
      dsimp [D]
      ring

private theorem sum_pow_two_Ico_four_le (M : ℕ) (hM : 4 ≤ M + 1) :
    (∑ s ∈ Finset.Ico 4 (M + 1), (2 : ℝ) ^ s) ≤
      (2 : ℝ) ^ (M + 1) := by
  rw [Finset.sum_Ico_eq_sub (fun s : ℕ ↦ (2 : ℝ) ^ s) hM]
  rw [geom_sum_eq (by norm_num : (2 : ℝ) ≠ 1),
    geom_sum_eq (by norm_num : (2 : ℝ) ≠ 1)]
  norm_num
  linarith

/-- The entire initial-frequency square sum is `O(1/a)`, with no logarithmic
loss: the crude `O(√K)` block bound is summed geometrically.
-/
theorem sum_sq_norm_smoothNearPrimitivePoleTailDyadicProjection_initial_le
    (a ε : ℝ) (U M : ℕ)
    (ha : 0 < a) (hε : 0 < ε) (haε : a ≤ ε / 4)
    (hεhalf : ε < 1 / 2) (hM : 4 ≤ M)
    (htop : a * ((2 ^ M : ℕ) : ℝ) ≤ 16)
    (hU : ∀ s ∈ Finset.Ico 4 (M + 1),
      Nat.sqrt (2 ^ s) + 1 < U) :
    ∑ s ∈ Finset.Ico 4 (M + 1),
        ‖smoothNearPrimitivePoleTailDyadicProjection
          a ε (2 ^ s) 2 U ha haε‖ ^ 2 ≤
      32 * nearZeroInitialFrequencyConstant ^ 2 / a := by
  have hC : 0 ≤ nearZeroInitialFrequencyConstant :=
    nearZeroInitialFrequencyConstant_nonneg
  have hsumBlocks :
      ∑ s ∈ Finset.Ico 4 (M + 1),
          ‖smoothNearPrimitivePoleTailDyadicProjection
            a ε (2 ^ s) 2 U ha haε‖ ^ 2 ≤
        nearZeroInitialFrequencyConstant ^ 2 *
          ∑ s ∈ Finset.Ico 4 (M + 1), (2 : ℝ) ^ s := by
    calc
      ∑ s ∈ Finset.Ico 4 (M + 1),
          ‖smoothNearPrimitivePoleTailDyadicProjection
            a ε (2 ^ s) 2 U ha haε‖ ^ 2 ≤
        ∑ s ∈ Finset.Ico 4 (M + 1),
          nearZeroInitialFrequencyConstant ^ 2 * (2 : ℝ) ^ s := by
        apply Finset.sum_le_sum
        intro s hs
        have hsBounds := Finset.mem_Ico.mp hs
        have hKnine : 9 ≤ 2 ^ s := by
          have : 4 ≤ s := hsBounds.1
          calc
            9 ≤ 2 ^ 4 := by norm_num
            _ ≤ 2 ^ s := Nat.pow_le_pow_right (by omega) this
        have hnorm :=
          norm_smoothNearPrimitivePoleTailDyadicProjection_two_le_initial
            a ε (2 ^ s) U ha hε haε hεhalf hKnine (hU s hs)
        have hsq := (sq_le_sq₀ (norm_nonneg _)
          (mul_nonneg hC (Real.sqrt_nonneg _))).2 hnorm
        calc
          ‖smoothNearPrimitivePoleTailDyadicProjection
              a ε (2 ^ s) 2 U ha haε‖ ^ 2 ≤
            (nearZeroInitialFrequencyConstant *
              Real.sqrt ((2 ^ s : ℕ) : ℝ)) ^ 2 := hsq
          _ = nearZeroInitialFrequencyConstant ^ 2 * (2 : ℝ) ^ s := by
            rw [mul_pow, Real.sq_sqrt (by positivity)]
            norm_cast
      _ = nearZeroInitialFrequencyConstant ^ 2 *
          ∑ s ∈ Finset.Ico 4 (M + 1), (2 : ℝ) ^ s := by
        rw [Finset.mul_sum]
  have hpow : (2 : ℝ) ^ (M + 1) ≤ 32 / a := by
    apply (le_div_iff₀ ha).2
    have htop' : a * (2 : ℝ) ^ M ≤ 16 := by
      simpa only [Nat.cast_pow, Nat.cast_ofNat] using! htop
    rw [pow_succ]
    nlinarith
  calc
    ∑ s ∈ Finset.Ico 4 (M + 1),
        ‖smoothNearPrimitivePoleTailDyadicProjection
          a ε (2 ^ s) 2 U ha haε‖ ^ 2 ≤
      nearZeroInitialFrequencyConstant ^ 2 *
        ∑ s ∈ Finset.Ico 4 (M + 1), (2 : ℝ) ^ s := hsumBlocks
    _ ≤ nearZeroInitialFrequencyConstant ^ 2 * (2 : ℝ) ^ (M + 1) := by
      gcongr
      exact sum_pow_two_Ico_four_le M (by omega)
    _ ≤ nearZeroInitialFrequencyConstant ^ 2 * (32 / a) := by gcongr
    _ = 32 * nearZeroInitialFrequencyConstant ^ 2 / a := by ring

/-- Uniform one-block zero-carrier estimate in its square-summable form.
Under the principal-scale bracketing hypotheses, the block norm is at most
an absolute explicit constant times `a⁻¹/²`.
-/
theorem norm_smoothNearPrimitivePoleTailDyadicProjection_two_le_le_invSqrt
    (a ε : ℝ) (K R P U : ℕ)
    (ha : 0 < a) (hε : 0 < ε) (haε : a ≤ ε / 4)
    (hεhalf : ε < 1 / 2) (hK : 0 < K)
    (hband : ((2 ^ (R + 1) : ℕ) : ℝ) ^ 2 ≤ a * (K : ℝ))
    (hnext : a * (K : ℝ) ≤
      (2 * ((2 ^ (R + 1) : ℕ) : ℝ)) ^ 2)
    (hP : 2 ≤ P) (hQP : 2 ^ (R + 1) < P - 1)
    (hPm1K : (P - 1) ^ 2 ≤ K) (hKP : K ≤ P ^ 2)
    (hPU : P < U) :
    ‖smoothNearPrimitivePoleTailDyadicProjection a ε K 2 U ha haε‖ ≤
      nearZeroPrincipalScaleConstant / Real.sqrt a := by
  have hsqrta : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
  have hscale0 : 0 ≤ ε / 2 + a := by positivity
  have hscale1 : ε / 2 + a ≤ 1 := by linarith
  have hPpos : 0 < (P : ℝ) ^ 2 := by positivity
  have hratio : (K : ℝ) / (P : ℝ) ^ 2 ≤ 1 := by
    apply (div_le_one₀ hPpos).2
    exact_mod_cast hKP
  let D : ℝ := (16 * Real.sqrt 54 + 64 * Real.sqrt 42) * Real.pi *
    nearProfileDecayConstant
  have hD : 0 ≤ D := by
    dsimp [D]
    exact mul_nonneg
      (mul_nonneg
        (add_nonneg
          (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
          (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)))
        Real.pi_nonneg)
      nearProfileDecayConstant_nonneg
  have hthird :
      D * (ε / 2 + a) * (K : ℝ) / (P : ℝ) ^ 2 ≤ D := by
    calc
      D * (ε / 2 + a) * (K : ℝ) / (P : ℝ) ^ 2 =
          (D * (ε / 2 + a)) * ((K : ℝ) / (P : ℝ) ^ 2) := by ring
      _ ≤ (D * 1) * 1 := by gcongr
      _ = D := by ring
  have haOne : a ≤ 1 := by linarith
  have hsqrtOne : Real.sqrt a ≤ 1 := Real.sqrt_le_one.2 haOne
  have hthirdDiv :
      D * (ε / 2 + a) * (K : ℝ) / (P : ℝ) ^ 2 ≤
        D / Real.sqrt a := by
    refine hthird.trans ?_
    apply (le_div_iff₀ hsqrta).2
    exact mul_le_of_le_one_right hD hsqrtOne
  have hraw :=
    norm_smoothNearPrimitivePoleTailDyadicProjection_two_le_principalScale
      a ε K R P U ha hε haε hεhalf hK hband hnext
        hP hQP hPm1K hKP hPU
  calc
    ‖smoothNearPrimitivePoleTailDyadicProjection a ε K 2 U ha haε‖ ≤
        192 * Real.sqrt 42 * Real.pi * nearProfileDecayConstant /
            Real.sqrt a +
          (4 * Real.sqrt 42 / Real.sqrt a) *
            (64 * Real.pi * nearProfileDecayConstant) +
          D * (ε / 2 + a) * (K : ℝ) / (P : ℝ) ^ 2 := by
      simpa only [D] using! hraw
    _ ≤
        192 * Real.sqrt 42 * Real.pi * nearProfileDecayConstant /
            Real.sqrt a +
          (4 * Real.sqrt 42 / Real.sqrt a) *
            (64 * Real.pi * nearProfileDecayConstant) +
          D / Real.sqrt a := add_le_add le_rfl hthirdDiv
    _ = nearZeroPrincipalScaleConstant / Real.sqrt a := by
      unfold nearZeroPrincipalScaleConstant
      dsimp [D]
      field_simp [hsqrta.ne']

/-- Parameter-eliminated principal-block estimate.  The dyadic denominator
endpoint and the integer square-root ceiling are constructed internally;
the only scale assumptions left are `aK ≥ 16` and that the natural
denominator cutoff lies beyond `sqrt K + 1`.
-/
theorem norm_smoothNearPrimitivePoleTailDyadicProjection_two_le_of_large
    (a ε : ℝ) (K U : ℕ)
    (ha : 0 < a) (hε : 0 < ε) (haε : a ≤ ε / 4)
    (hεhalf : ε < 1 / 2) (hK : 0 < K)
    (hlarge : 16 ≤ a * (K : ℝ))
    (hU : Nat.sqrt K + 1 < U) :
    ‖smoothNearPrimitivePoleTailDyadicProjection a ε K 2 U ha haε‖ ≤
      nearZeroPrincipalScaleConstant / Real.sqrt a := by
  obtain ⟨R, hband, hnext⟩ :=
    exists_nearZeroPrincipalExponent a K ha hK hlarge
  obtain ⟨hP, hPm1K, hKP⟩ := nearZeroNatSqrtCeiling_spec K hK
  have hQP : 2 ^ (R + 1) < Nat.sqrt K + 1 - 1 := by
    simpa using! nearZeroPrincipalEndpoint_lt_natSqrt
      a ε K R haε hεhalf hK hband
  exact norm_smoothNearPrimitivePoleTailDyadicProjection_two_le_le_invSqrt
    a ε K R (Nat.sqrt K + 1) U ha hε haε hεhalf hK
      hband hnext hP hQP hPm1K hKP hU

/-- The square-function estimate over an arbitrary finite family of positive
dyadic frequency blocks.  The hypotheses expose the chosen principal
denominator endpoint and square-root ceiling for every block; no selection
function is hidden. -/
theorem sum_sq_norm_smoothNearPrimitivePoleTailDyadicProjection_le
    (a ε : ℝ) (U : ℕ) (S : Finset ℕ) (R P : ℕ → ℕ)
    (ha : 0 < a) (hε : 0 < ε) (haε : a ≤ ε / 4)
    (hεhalf : ε < 1 / 2)
    (hband : ∀ s ∈ S,
      ((2 ^ (R s + 1) : ℕ) : ℝ) ^ 2 ≤ a * ((2 ^ s : ℕ) : ℝ))
    (hnext : ∀ s ∈ S, a * ((2 ^ s : ℕ) : ℝ) ≤
      (2 * ((2 ^ (R s + 1) : ℕ) : ℝ)) ^ 2)
    (hP : ∀ s ∈ S, 2 ≤ P s)
    (hQP : ∀ s ∈ S, 2 ^ (R s + 1) < P s - 1)
    (hPm1K : ∀ s ∈ S, (P s - 1) ^ 2 ≤ 2 ^ s)
    (hKP : ∀ s ∈ S, 2 ^ s ≤ (P s) ^ 2)
    (hPU : ∀ s ∈ S, P s < U) :
    ∑ s ∈ S,
        ‖smoothNearPrimitivePoleTailDyadicProjection
          a ε (2 ^ s) 2 U ha haε‖ ^ 2 ≤
      (S.card : ℝ) * nearZeroPrincipalScaleConstant ^ 2 / a := by
  have hsqrta : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
  have hconstant : 0 ≤ nearZeroPrincipalScaleConstant :=
    nearZeroPrincipalScaleConstant_nonneg
  calc
    ∑ s ∈ S,
        ‖smoothNearPrimitivePoleTailDyadicProjection
          a ε (2 ^ s) 2 U ha haε‖ ^ 2 ≤
      ∑ _s ∈ S,
        (nearZeroPrincipalScaleConstant / Real.sqrt a) ^ 2 := by
      apply Finset.sum_le_sum
      intro s hs
      have hnorm :=
        norm_smoothNearPrimitivePoleTailDyadicProjection_two_le_le_invSqrt
          a ε (2 ^ s) (R s) (P s) U ha hε haε hεhalf
            (by positivity) (hband s hs) (hnext s hs) (hP s hs)
            (hQP s hs) (hPm1K s hs) (hKP s hs) (hPU s hs)
      exact (sq_le_sq₀ (norm_nonneg _)
        (div_nonneg hconstant hsqrta.le)).2 hnorm
    _ = (S.card : ℝ) * nearZeroPrincipalScaleConstant ^ 2 / a := by
      rw [Finset.sum_const, nsmul_eq_mul]
      rw [div_pow, Real.sq_sqrt ha.le]
      ring

/-- Fully parameter-eliminated square-function bound on every finite family
of principal positive-frequency blocks. -/
theorem sum_sq_norm_smoothNearPrimitivePoleTailDyadicProjection_le_of_large
    (a ε : ℝ) (U : ℕ) (S : Finset ℕ)
    (ha : 0 < a) (hε : 0 < ε) (haε : a ≤ ε / 4)
    (hεhalf : ε < 1 / 2)
    (hlarge : ∀ s ∈ S, 16 ≤ a * ((2 ^ s : ℕ) : ℝ))
    (hU : ∀ s ∈ S, Nat.sqrt (2 ^ s) + 1 < U) :
    ∑ s ∈ S,
        ‖smoothNearPrimitivePoleTailDyadicProjection
          a ε (2 ^ s) 2 U ha haε‖ ^ 2 ≤
      (S.card : ℝ) * nearZeroPrincipalScaleConstant ^ 2 / a := by
  have hsqrta : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
  have hconstant : 0 ≤ nearZeroPrincipalScaleConstant :=
    nearZeroPrincipalScaleConstant_nonneg
  calc
    ∑ s ∈ S,
        ‖smoothNearPrimitivePoleTailDyadicProjection
          a ε (2 ^ s) 2 U ha haε‖ ^ 2 ≤
      ∑ _s ∈ S,
        (nearZeroPrincipalScaleConstant / Real.sqrt a) ^ 2 := by
      apply Finset.sum_le_sum
      intro s hs
      have hnorm :=
        norm_smoothNearPrimitivePoleTailDyadicProjection_two_le_of_large
          a ε (2 ^ s) U ha hε haε hεhalf (by positivity)
            (hlarge s hs) (hU s hs)
      exact (sq_le_sq₀ (norm_nonneg _)
        (div_nonneg hconstant hsqrta.le)).2 hnorm
    _ = (S.card : ℝ) * nearZeroPrincipalScaleConstant ^ 2 / a := by
      rw [Finset.sum_const, nsmul_eq_mul, div_pow, Real.sq_sqrt ha.le]
      ring

/-! ## The four fixed initial dyadic blocks -/

def nearZeroTinyFrequencyConstant : ℝ :=
  (16 * Real.sqrt 54 + 64 * Real.sqrt 42) * Real.pi *
    nearProfileDecayConstant

theorem nearZeroTinyFrequencyConstant_nonneg :
    0 ≤ nearZeroTinyFrequencyConstant := by
  unfold nearZeroTinyFrequencyConstant
  exact mul_nonneg
    (mul_nonneg
      (add_nonneg
        (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
        (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)))
      Real.pi_nonneg)
    nearProfileDecayConstant_nonneg

/-- Uniform bound for `K≤8`, obtained from the singleton `p=3` and the
geometrically summable high-denominator tail. -/
theorem norm_smoothNearPrimitivePoleTailDyadicProjection_two_le_tiny
    (a ε : ℝ) (K U : ℕ)
    (ha : 0 < a) (hε : 0 < ε) (haε : a ≤ ε / 4)
    (hεhalf : ε < 1 / 2) (hK : 0 < K) (hK8 : K ≤ 8) (hU : 4 ≤ U) :
    ‖smoothNearPrimitivePoleTailDyadicProjection a ε K 2 U ha haε‖ ≤
      nearZeroTinyFrequencyConstant := by
  have hK9 : K ≤ 3 ^ 2 := by norm_num; omega
  have hsingle :=
    norm_finiteNearRamanujanMultiplierVector_singleton_le_highRange
      a ε K 3 ha hε haε (by norm_num) hK9
  have htail :=
    norm_finiteNearRamanujanMultiplierVector_tail_le_highRange
      a ε K 3 U ha hε haε hK (by norm_num) hK9 (by omega)
  have hsplit := finiteNearRamanujanMultiplierVector_split_at
    a ε K 3 U (by norm_num) (by omega)
  have hscale0 : 0 ≤ ε / 2 + a := by positivity
  have hscale1 : ε / 2 + a ≤ 1 := by linarith
  have hratio : (K : ℝ) / (3 : ℝ) ^ 2 ≤ 1 := by
    apply (div_le_one₀ (by norm_num)).2
    exact_mod_cast hK9
  have hD : 0 ≤ nearZeroTinyFrequencyConstant :=
    nearZeroTinyFrequencyConstant_nonneg
  rw [norm_smoothNearPrimitivePoleTailDyadicProjection_eq_vector
    a ε K 2 U (by norm_num) ha hε haε hεhalf.le, hsplit]
  calc
    ‖finiteNearRamanujanMultiplierVector a ε K 3 3 +
        finiteNearRamanujanMultiplierVector a ε K 4 U‖ ≤
      ‖finiteNearRamanujanMultiplierVector a ε K 3 3‖ +
        ‖finiteNearRamanujanMultiplierVector a ε K 4 U‖ := norm_add_le _ _
    _ ≤
      (16 * Real.sqrt 54 * Real.pi * nearProfileDecayConstant *
          (ε / 2 + a)) * (K : ℝ) / (3 : ℝ) ^ 2 +
        (64 * Real.sqrt 42 * Real.pi * nearProfileDecayConstant *
          (ε / 2 + a)) * (K : ℝ) / (3 : ℝ) ^ 2 :=
      add_le_add hsingle htail
    _ = nearZeroTinyFrequencyConstant * (ε / 2 + a) *
        ((K : ℝ) / (3 : ℝ) ^ 2) := by
      unfold nearZeroTinyFrequencyConstant
      ring
    _ ≤ nearZeroTinyFrequencyConstant * 1 * 1 := by gcongr
    _ = nearZeroTinyFrequencyConstant := by ring

/-- Combined square bound for `K=1,2,4,8`. -/
theorem sum_sq_norm_smoothNearPrimitivePoleTailDyadicProjection_range_four_le
    (a ε : ℝ) (U : ℕ)
    (ha : 0 < a) (hε : 0 < ε) (haε : a ≤ ε / 4)
    (hεhalf : ε < 1 / 2) (hU : 4 ≤ U) :
    ∑ s ∈ Finset.range 4,
        ‖smoothNearPrimitivePoleTailDyadicProjection
          a ε (2 ^ s) 2 U ha haε‖ ^ 2 ≤
      4 * nearZeroTinyFrequencyConstant ^ 2 := by
  have hC : 0 ≤ nearZeroTinyFrequencyConstant :=
    nearZeroTinyFrequencyConstant_nonneg
  calc
    ∑ s ∈ Finset.range 4,
        ‖smoothNearPrimitivePoleTailDyadicProjection
          a ε (2 ^ s) 2 U ha haε‖ ^ 2 ≤
      ∑ _s ∈ Finset.range 4, nearZeroTinyFrequencyConstant ^ 2 := by
        apply Finset.sum_le_sum
        intro s hs
        have hslt : s < 4 := Finset.mem_range.mp hs
        have hK8 : 2 ^ s ≤ 8 := by
          calc
            2 ^ s ≤ 2 ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
            _ = 8 := by norm_num
        have hnorm :=
          norm_smoothNearPrimitivePoleTailDyadicProjection_two_le_tiny
            a ε (2 ^ s) U ha hε haε hεhalf (by positivity) hK8 hU
        exact (sq_le_sq₀ (norm_nonneg _) hC).2 hnorm
    _ = 4 * nearZeroTinyFrequencyConstant ^ 2 := by simp

/-- Complete finite positive-frequency square-function estimate, with the
four tiny blocks, the initial geometric range, the principal range, and the
high geometric tail displayed separately. -/
theorem sum_sq_norm_smoothNearPrimitivePoleTailDyadicProjection_range_le
    (a ε : ℝ) (U M S H : ℕ)
    (ha : 0 < a) (hε : 0 < ε) (haε : a ≤ ε / 4)
    (hεhalf : ε < 1 / 2) (hUfour : 4 ≤ U)
    (hM : 4 ≤ M) (hMS : M + 1 ≤ S) (hSH : S ≤ H)
    (hinitialTop : a * ((2 ^ M : ℕ) : ℝ) ≤ 16)
    (hprincipalBase : 16 ≤ a * ((2 ^ (M + 1) : ℕ) : ℝ))
    (hinitialU : ∀ s ∈ Finset.Ico 4 (M + 1),
      Nat.sqrt (2 ^ s) + 1 < U)
    (hprincipalU : ∀ s ∈ Finset.Ico (M + 1) S,
      Nat.sqrt (2 ^ s) + 1 < U)
    (hhigh : ((U : ℝ) ^ 2) ≤ a * ((2 ^ S : ℕ) : ℝ)) :
    ∑ s ∈ Finset.range H,
        ‖smoothNearPrimitivePoleTailDyadicProjection
          a ε (2 ^ s) 2 U ha haε‖ ^ 2 ≤
      4 * nearZeroTinyFrequencyConstant ^ 2 +
        32 * nearZeroInitialFrequencyConstant ^ 2 / a +
        ((Finset.Ico (M + 1) S).card : ℝ) *
          nearZeroPrincipalScaleConstant ^ 2 / a +
        2 * (384 * Real.sqrt 42 * Real.pi * nearProfileDecayConstant) ^ 2 / a := by
  let f : ℕ → ℝ := fun s ↦
    ‖smoothNearPrimitivePoleTailDyadicProjection
      a ε (2 ^ s) 2 U ha haε‖ ^ 2
  have hfourM : 4 ≤ M + 1 := by omega
  have hfourS : 4 ≤ S := hfourM.trans hMS
  have hfourH : 4 ≤ H := hfourS.trans hSH
  have hsplit :
      ∑ s ∈ Finset.range H, f s =
        (∑ s ∈ Finset.range 4, f s) +
          (∑ s ∈ Finset.Ico 4 (M + 1), f s) +
          (∑ s ∈ Finset.Ico (M + 1) S, f s) +
          (∑ s ∈ Finset.Ico S H, f s) := by
    rw [← Finset.sum_range_add_sum_Ico f hfourH,
      ← Finset.sum_Ico_consecutive f hfourM (hMS.trans hSH),
      ← Finset.sum_Ico_consecutive f hMS hSH]
    ring
  have htiny :
      ∑ s ∈ Finset.range 4, f s ≤
        4 * nearZeroTinyFrequencyConstant ^ 2 := by
    simpa only [f] using!
      sum_sq_norm_smoothNearPrimitivePoleTailDyadicProjection_range_four_le
        a ε U ha hε haε hεhalf hUfour
  have hinitial :
      ∑ s ∈ Finset.Ico 4 (M + 1), f s ≤
        32 * nearZeroInitialFrequencyConstant ^ 2 / a := by
    apply sum_sq_norm_smoothNearPrimitivePoleTailDyadicProjection_initial_le
      a ε U M ha hε haε hεhalf hM hinitialTop
    exact hinitialU
  have hprincipalLarge : ∀ s ∈ Finset.Ico (M + 1) S,
      16 ≤ a * ((2 ^ s : ℕ) : ℝ) := by
    intro s hs
    have hsLower := (Finset.mem_Ico.mp hs).1
    have hpow : ((2 ^ (M + 1) : ℕ) : ℝ) ≤ ((2 ^ s : ℕ) : ℝ) := by
      exact_mod_cast Nat.pow_le_pow_right (by omega : 0 < 2) hsLower
    exact hprincipalBase.trans
      (mul_le_mul_of_nonneg_left hpow ha.le)
  have hprincipal :
      ∑ s ∈ Finset.Ico (M + 1) S, f s ≤
        ((Finset.Ico (M + 1) S).card : ℝ) *
          nearZeroPrincipalScaleConstant ^ 2 / a := by
    simpa only [f] using!
      sum_sq_norm_smoothNearPrimitivePoleTailDyadicProjection_le_of_large
        a ε U (Finset.Ico (M + 1) S) ha hε haε hεhalf
          hprincipalLarge hprincipalU
  have hhighBound :
      ∑ s ∈ Finset.Ico S H, f s ≤
        2 * (384 * Real.sqrt 42 * Real.pi * nearProfileDecayConstant) ^ 2 / a := by
    simpa only [f] using!
      sum_sq_norm_smoothNearPrimitivePoleTailDyadicProjection_high_le
        a ε U S H ha hε haε hεhalf (by omega) hhigh
  rw [hsplit]
  exact add_le_add (add_le_add (add_le_add htiny hinitial) hprincipal) hhighBound

/-- The same complete estimate written directly as a partial sum of the
actual positive Fourier coefficients of the smooth zero carrier. -/
theorem sum_norm_sq_fourierCoeff_smoothNearPrimitivePoleTailL2_positive_le
    (a ε : ℝ) (U M S H : ℕ)
    (ha : 0 < a) (hε : 0 < ε) (haε : a ≤ ε / 4)
    (hεhalf : ε < 1 / 2) (hUfour : 4 ≤ U)
    (hM : 4 ≤ M) (hMS : M + 1 ≤ S) (hSH : S ≤ H)
    (hinitialTop : a * ((2 ^ M : ℕ) : ℝ) ≤ 16)
    (hprincipalBase : 16 ≤ a * ((2 ^ (M + 1) : ℕ) : ℝ))
    (hinitialU : ∀ s ∈ Finset.Ico 4 (M + 1),
      Nat.sqrt (2 ^ s) + 1 < U)
    (hprincipalU : ∀ s ∈ Finset.Ico (M + 1) S,
      Nat.sqrt (2 ^ s) + 1 < U)
    (hhigh : ((U : ℝ) ^ 2) ≤ a * ((2 ^ S : ℕ) : ℝ)) :
    ∑ n ∈ Finset.Ioc (1 : ℕ) (2 ^ H),
        ‖fourierCoeff
          (smoothNearPrimitivePoleTailL2 a ε 2 U ha haε :
            AddCircle (1 : ℝ) → ℂ) (n : ℤ)‖ ^ 2 ≤
      4 * nearZeroTinyFrequencyConstant ^ 2 +
        32 * nearZeroInitialFrequencyConstant ^ 2 / a +
        ((Finset.Ico (M + 1) S).card : ℝ) *
          nearZeroPrincipalScaleConstant ^ 2 / a +
        2 * (384 * Real.sqrt 42 * Real.pi * nearProfileDecayConstant) ^ 2 / a := by
  rw [← sum_sq_norm_smoothNearPrimitivePoleTailDyadicProjection_range_eq
    a ε 2 U H ha haε]
  exact sum_sq_norm_smoothNearPrimitivePoleTailDyadicProjection_range_le
    a ε U M S H ha hε haε hεhalf hUfour hM hMS hSH
      hinitialTop hprincipalBase hinitialU hprincipalU hhigh

/-! ## The single positive frequency omitted by the dyadic partition -/

def nearZeroFrequencyOnePSeries : ℝ :=
  ∑' p : ℕ, 1 / (p : ℝ) ^ 3

theorem nearZeroFrequencyOnePSeries_nonneg :
    0 ≤ nearZeroFrequencyOnePSeries := by
  unfold nearZeroFrequencyOnePSeries
  exact tsum_nonneg fun _ ↦ by positivity

def nearZeroFrequencyOneConstant : ℝ :=
  8 * Real.pi * nearProfileDecayConstant * nearZeroFrequencyOnePSeries

theorem nearZeroFrequencyOneConstant_nonneg :
    0 ≤ nearZeroFrequencyOneConstant := by
  unfold nearZeroFrequencyOneConstant
  exact mul_nonneg
    (mul_nonneg (mul_nonneg (by norm_num) Real.pi_nonneg)
      nearProfileDecayConstant_nonneg)
    nearZeroFrequencyOnePSeries_nonneg

private theorem norm_nearZero_frequency_one_term_le
    (a ε : ℝ) (p : ℕ)
    (ha : 0 < a) (hε : 0 < ε) (haε : a ≤ ε / 4)
    (hp : 0 < p) :
    ‖((p : ℂ) ^ 2)⁻¹ *
        ramanujanSum p (1 : ℤ) *
          nearJ a ε ((1 : ℝ) / (p : ℝ) ^ 2)‖ ≤
      (8 * Real.pi * nearProfileDecayConstant * (ε / 2 + a)) *
        (1 / (p : ℝ) ^ 3) := by
  let C : ℝ := 8 * Real.pi * nearProfileDecayConstant * (ε / 2 + a)
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp
  have hC : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (by norm_num) Real.pi_nonneg)
        nearProfileDecayConstant_nonneg)
      (by positivity)
  have hRam := norm_ramanujanSum_le_totient p (1 : ℤ)
  have htot : (Nat.totient p : ℝ) ≤ (p : ℝ) := by
    exact_mod_cast Nat.totient_le p
  have hJ := norm_nearJ_le_linear a ε ((1 : ℝ) / (p : ℝ) ^ 2)
    ha hε haε
  have htpos : 0 ≤ (1 : ℝ) / (p : ℝ) ^ 2 := by positivity
  rw [abs_of_nonneg htpos] at hJ
  have hinvCast : ((p : ℂ) ^ 2)⁻¹ =
      ((1 / (p : ℝ) ^ 2 : ℝ) : ℂ) := by
    rw [one_div, Complex.ofReal_inv]
    push_cast
    rfl
  calc
    ‖((p : ℂ) ^ 2)⁻¹ *
        ramanujanSum p (1 : ℤ) *
          nearJ a ε ((1 : ℝ) / (p : ℝ) ^ 2)‖ =
      (1 / (p : ℝ) ^ 2) * ‖ramanujanSum p (1 : ℤ)‖ *
        ‖nearJ a ε ((1 : ℝ) / (p : ℝ) ^ 2)‖ := by
      rw [hinvCast, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by positivity)]
    _ ≤ (1 / (p : ℝ) ^ 2) * (p : ℝ) *
        (C * ((1 : ℝ) / (p : ℝ) ^ 2)) := by
      gcongr
      exact hRam.trans htot
    _ = C * (1 / (p : ℝ) ^ 3) := by
      field_simp [hpR.ne']
    _ = (8 * Real.pi * nearProfileDecayConstant * (ε / 2 + a)) *
        (1 / (p : ℝ) ^ 3) := by rfl

/-- Uniform bound for the omitted coefficient `n=1`. -/
theorem norm_fourierCoeff_smoothNearPrimitivePoleTailL2_one_le
    (a ε : ℝ) (U : ℕ)
    (ha : 0 < a) (hε : 0 < ε) (haε : a ≤ ε / 4)
    (hεhalf : ε < 1 / 2) :
    ‖fourierCoeff
        (smoothNearPrimitivePoleTailL2 a ε 2 U ha haε :
          AddCircle (1 : ℝ) → ℂ) (1 : ℤ)‖ ≤
      nearZeroFrequencyOneConstant := by
  have hformula := fourierCoeff_smoothNearPrimitivePoleTailL2_nat
    a ε 2 U 1 ha haε
  change ‖fourierCoeff
      (smoothNearPrimitivePoleTailL2 a ε 2 U ha haε :
        AddCircle (1 : ℝ) → ℂ) ((1 : ℕ) : ℤ)‖ ≤ _
  rw [hformula, unitFourierCoefficient_smoothNearPrimitivePoleTail_eq
    a ε 2 U 1 (by norm_num) ha hε haε hεhalf.le]
  norm_num
  let g : ℕ → ℂ := fun p ↦
    ((((p : ℂ) ^ 2)⁻¹) * ramanujanSum p (1 : ℤ) *
      nearJ a ε (((p : ℝ) ^ 2)⁻¹))
  change ‖∑ p ∈ Finset.Ioc 2 U, g p‖ ≤ _
  calc
    _ ≤
      ∑ p ∈ Finset.Ioc 2 U,
        ‖g p‖ := norm_sum_le _ _
    _ ≤ ∑ p ∈ Finset.Ioc 2 U,
        (8 * Real.pi * nearProfileDecayConstant * (ε / 2 + a)) *
          (1 / (p : ℝ) ^ 3) := by
      apply Finset.sum_le_sum
      intro p hp
      simpa only [g, one_div] using! norm_nearZero_frequency_one_term_le
        a ε p ha hε haε (by
          have hpBounds := Finset.mem_Ioc.mp hp
          omega)
    _ = (8 * Real.pi * nearProfileDecayConstant * (ε / 2 + a)) *
        ∑ p ∈ Finset.Ioc 2 U, 1 / (p : ℝ) ^ 3 := by
      rw [Finset.mul_sum]
    _ ≤ (8 * Real.pi * nearProfileDecayConstant * (ε / 2 + a)) *
        nearZeroFrequencyOnePSeries := by
      apply mul_le_mul_of_nonneg_left _ (by
        exact mul_nonneg
          (mul_nonneg
            (mul_nonneg (by norm_num) Real.pi_nonneg)
            nearProfileDecayConstant_nonneg)
          (by positivity))
      unfold nearZeroFrequencyOnePSeries
      exact (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 3)).sum_le_tsum
        (Finset.Ioc 2 U) (fun _ _ ↦ by positivity)
    _ ≤ (8 * Real.pi * nearProfileDecayConstant * 1) *
        nearZeroFrequencyOnePSeries := by
      have hscale : ε / 2 + a ≤ 1 := by linarith
      apply mul_le_mul_of_nonneg_right _ nearZeroFrequencyOnePSeries_nonneg
      exact mul_le_mul_of_nonneg_left hscale (by
        exact mul_nonneg
          (mul_nonneg (by norm_num) Real.pi_nonneg)
          nearProfileDecayConstant_nonneg)
    _ = nearZeroFrequencyOneConstant := by
      unfold nearZeroFrequencyOneConstant
      ring

/-! ## Passage from finite dyadic ranges to the complete coefficient energy -/

/-- The finite positive-frequency bounds are uniform in the terminal dyadic
exponent.  Consequently they control the entire series of nonnegative
Fourier frequencies.  The zero coefficient vanishes, while the one
coefficient is inserted separately because the dyadic partition starts at
frequency two. -/
theorem tsum_norm_sq_fourierCoeff_smoothNearPrimitivePoleTailL2_nat_le
    (a ε : ℝ) (U M S : ℕ)
    (ha : 0 < a) (hε : 0 < ε) (haε : a ≤ ε / 4)
    (hεhalf : ε < 1 / 2) (hUfour : 4 ≤ U)
    (hM : 4 ≤ M) (hMS : M + 1 ≤ S)
    (hinitialTop : a * ((2 ^ M : ℕ) : ℝ) ≤ 16)
    (hprincipalBase : 16 ≤ a * ((2 ^ (M + 1) : ℕ) : ℝ))
    (hinitialU : ∀ s ∈ Finset.Ico 4 (M + 1),
      Nat.sqrt (2 ^ s) + 1 < U)
    (hprincipalU : ∀ s ∈ Finset.Ico (M + 1) S,
      Nat.sqrt (2 ^ s) + 1 < U)
    (hhigh : ((U : ℝ) ^ 2) ≤ a * ((2 ^ S : ℕ) : ℝ)) :
    ∑' n : ℕ,
        ‖fourierCoeff
          (smoothNearPrimitivePoleTailL2 a ε 2 U ha haε :
            AddCircle (1 : ℝ) → ℂ) (n : ℤ)‖ ^ 2 ≤
      nearZeroFrequencyOneConstant ^ 2 +
        (4 * nearZeroTinyFrequencyConstant ^ 2 +
          32 * nearZeroInitialFrequencyConstant ^ 2 / a +
          ((Finset.Ico (M + 1) S).card : ℝ) *
            nearZeroPrincipalScaleConstant ^ 2 / a +
          2 * (384 * Real.sqrt 42 * Real.pi * nearProfileDecayConstant) ^ 2 / a) := by
  let f : ℕ → ℝ := fun n ↦
    ‖fourierCoeff
      (smoothNearPrimitivePoleTailL2 a ε 2 U ha haε :
        AddCircle (1 : ℝ) → ℂ) (n : ℤ)‖ ^ 2
  let B : ℝ :=
    4 * nearZeroTinyFrequencyConstant ^ 2 +
      32 * nearZeroInitialFrequencyConstant ^ 2 / a +
      ((Finset.Ico (M + 1) S).card : ℝ) *
        nearZeroPrincipalScaleConstant ^ 2 / a +
      2 * (384 * Real.sqrt 42 * Real.pi * nearProfileDecayConstant) ^ 2 / a
  have hpowSelf : ∀ k : ℕ, k ≤ 2 ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        rw [pow_succ]
        have hone : 1 ≤ 2 ^ k := Nat.one_le_two_pow
        omega
  have hfzero : f 0 = 0 := by
    dsimp [f]
    rw [fourierCoeff_smoothNearPrimitivePoleTailL2_zero
      a ε 2 U (by norm_num) ha hε haε hεhalf.le]
    norm_num
  have hfone : f 1 ≤ nearZeroFrequencyOneConstant ^ 2 := by
    dsimp [f]
    exact (sq_le_sq₀ (norm_nonneg _) nearZeroFrequencyOneConstant_nonneg).2
      (norm_fourierCoeff_smoothNearPrimitivePoleTailL2_one_le
        a ε U ha hε haε hεhalf)
  apply Real.tsum_le_of_sum_range_le (fun n ↦ sq_nonneg _)
  intro k
  let H : ℕ := max S k
  let T : Finset ℕ :=
    insert 0 (insert 1 (Finset.Ioc (1 : ℕ) (2 ^ H)))
  have hSH : S ≤ H := by
    dsimp [H]
    exact le_max_left _ _
  have hkH : k ≤ H := by
    dsimp [H]
    exact le_max_right _ _
  have hkPow : k ≤ 2 ^ H := hkH.trans (hpowSelf H)
  have hsubset : Finset.range k ⊆ T := by
    intro n hn
    have hnk : n < k := Finset.mem_range.mp hn
    have hnPow : n ≤ 2 ^ H := (Nat.le_of_lt hnk).trans hkPow
    simp only [T, Finset.mem_insert, Finset.mem_Ioc]
    omega
  have hfinite :
      ∑ n ∈ Finset.Ioc (1 : ℕ) (2 ^ H), f n ≤ B := by
    dsimp only [f, B]
    exact
      sum_norm_sq_fourierCoeff_smoothNearPrimitivePoleTailL2_positive_le
        a ε U M S H ha hε haε hεhalf hUfour hM hMS hSH
          hinitialTop hprincipalBase hinitialU hprincipalU hhigh
  calc
    ∑ n ∈ Finset.range k, f n ≤ ∑ n ∈ T, f n := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
      intro n _hn _hnot
      exact sq_nonneg _
    _ = f 0 + f 1 + ∑ n ∈ Finset.Ioc (1 : ℕ) (2 ^ H), f n := by
      simp [T, add_assoc]
    _ ≤ nearZeroFrequencyOneConstant ^ 2 + B := by
      rw [hfzero, zero_add]
      exact add_le_add hfone hfinite
    _ = nearZeroFrequencyOneConstant ^ 2 +
        (4 * nearZeroTinyFrequencyConstant ^ 2 +
          32 * nearZeroInitialFrequencyConstant ^ 2 / a +
          ((Finset.Ico (M + 1) S).card : ℝ) *
            nearZeroPrincipalScaleConstant ^ 2 / a +
          2 * (384 * Real.sqrt 42 * Real.pi * nearProfileDecayConstant) ^ 2 / a) := by
      rfl

/-- By reality of the carrier, the negative-frequency energy is an exact
copy of the positive-frequency energy.  This is the complete Parseval-side
bound over all integer frequencies. -/
theorem tsum_norm_sq_fourierCoeff_smoothNearPrimitivePoleTailL2_int_le
    (a ε : ℝ) (U M S : ℕ)
    (ha : 0 < a) (hε : 0 < ε) (haε : a ≤ ε / 4)
    (hεhalf : ε < 1 / 2) (hUfour : 4 ≤ U)
    (hM : 4 ≤ M) (hMS : M + 1 ≤ S)
    (hinitialTop : a * ((2 ^ M : ℕ) : ℝ) ≤ 16)
    (hprincipalBase : 16 ≤ a * ((2 ^ (M + 1) : ℕ) : ℝ))
    (hinitialU : ∀ s ∈ Finset.Ico 4 (M + 1),
      Nat.sqrt (2 ^ s) + 1 < U)
    (hprincipalU : ∀ s ∈ Finset.Ico (M + 1) S,
      Nat.sqrt (2 ^ s) + 1 < U)
    (hhigh : ((U : ℝ) ^ 2) ≤ a * ((2 ^ S : ℕ) : ℝ)) :
    ∑' z : ℤ,
        ‖fourierCoeff
          (smoothNearPrimitivePoleTailL2 a ε 2 U ha haε :
            AddCircle (1 : ℝ) → ℂ) z‖ ^ 2 ≤
      2 * (nearZeroFrequencyOneConstant ^ 2 +
        (4 * nearZeroTinyFrequencyConstant ^ 2 +
          32 * nearZeroInitialFrequencyConstant ^ 2 / a +
          ((Finset.Ico (M + 1) S).card : ℝ) *
            nearZeroPrincipalScaleConstant ^ 2 / a +
          2 * (384 * Real.sqrt 42 * Real.pi * nearProfileDecayConstant) ^ 2 / a)) := by
  let F := smoothNearPrimitivePoleTailL2 a ε 2 U ha haε
  let f : ℤ → ℝ := fun z ↦
    ‖fourierCoeff (F : AddCircle (1 : ℝ) → ℂ) z‖ ^ 2
  have hs : Summable f := by
    exact (hasSum_sq_fourierCoeff F).summable
  have heven : f.Even := by
    intro z
    dsimp [f, F]
    rw [fourierCoeff_smoothNearPrimitivePoleTailL2_neg,
      starRingEnd_apply, norm_star]
  have hfzero : f 0 = 0 := by
    dsimp [f, F]
    rw [fourierCoeff_smoothNearPrimitivePoleTailL2_zero
      a ε 2 U (by norm_num) ha hε haε hεhalf.le]
    norm_num
  have hsnat : Summable (fun n : ℕ ↦ f (n : ℤ)) :=
    hs.comp_injective Nat.cast_injective
  have hpnat :
      (∑' n : ℕ+, f (n : ℤ)) = ∑' n : ℕ, f (n : ℤ) := by
    have h := tsum_zero_pnat_eq_tsum_nat hsnat
    have hfzeroCast : f ((0 : ℕ) : ℤ) = 0 := by simpa using! hfzero
    rw [hfzeroCast, zero_add] at h
    exact h
  have hnat :
      (∑' n : ℕ, f (n : ℤ)) ≤
        nearZeroFrequencyOneConstant ^ 2 +
          (4 * nearZeroTinyFrequencyConstant ^ 2 +
            32 * nearZeroInitialFrequencyConstant ^ 2 / a +
            ((Finset.Ico (M + 1) S).card : ℝ) *
              nearZeroPrincipalScaleConstant ^ 2 / a +
            2 * (384 * Real.sqrt 42 * Real.pi * nearProfileDecayConstant) ^ 2 / a) := by
    simpa only [f, F] using!
      tsum_norm_sq_fourierCoeff_smoothNearPrimitivePoleTailL2_nat_le
        a ε U M S ha hε haε hεhalf hUfour hM hMS
          hinitialTop hprincipalBase hinitialU hprincipalU hhigh
  change (∑' z : ℤ, f z) ≤ _
  rw [tsum_int_eq_zero_add_two_mul_tsum_pnat heven hs]
  simp only [hfzero, zero_add, nsmul_eq_mul, hpnat]
  exact mul_le_mul_of_nonneg_left hnat (by norm_num)

/-- Physical `L²` form of the complete zero-carrier estimate.  No
frequency truncation remains: Parseval identifies the left side with the
full integer coefficient energy bounded above. -/
theorem norm_sq_smoothNearPrimitivePoleTailL2_le
    (a ε : ℝ) (U M S : ℕ)
    (ha : 0 < a) (hε : 0 < ε) (haε : a ≤ ε / 4)
    (hεhalf : ε < 1 / 2) (hUfour : 4 ≤ U)
    (hM : 4 ≤ M) (hMS : M + 1 ≤ S)
    (hinitialTop : a * ((2 ^ M : ℕ) : ℝ) ≤ 16)
    (hprincipalBase : 16 ≤ a * ((2 ^ (M + 1) : ℕ) : ℝ))
    (hinitialU : ∀ s ∈ Finset.Ico 4 (M + 1),
      Nat.sqrt (2 ^ s) + 1 < U)
    (hprincipalU : ∀ s ∈ Finset.Ico (M + 1) S,
      Nat.sqrt (2 ^ s) + 1 < U)
    (hhigh : ((U : ℝ) ^ 2) ≤ a * ((2 ^ S : ℕ) : ℝ)) :
    ‖smoothNearPrimitivePoleTailL2 a ε 2 U ha haε‖ ^ 2 ≤
      2 * (nearZeroFrequencyOneConstant ^ 2 +
        (4 * nearZeroTinyFrequencyConstant ^ 2 +
          32 * nearZeroInitialFrequencyConstant ^ 2 / a +
          ((Finset.Ico (M + 1) S).card : ℝ) *
            nearZeroPrincipalScaleConstant ^ 2 / a +
          2 * (384 * Real.sqrt 42 * Real.pi * nearProfileDecayConstant) ^ 2 / a)) := by
  let F : UnitCircleL2 := smoothNearPrimitivePoleTailL2 a ε 2 U ha haε
  have hparseval := tsum_sq_fourierCoeff F
  have hinner := congrArg RCLike.re
    (@L2.inner_def (AddCircle (1 : ℝ)) ℂ ℂ _ _ _ _ _ F F)
  rw [← integral_re] at hinner
  · simp only [← norm_sq_eq_re_inner] at hinner
    calc
      ‖smoothNearPrimitivePoleTailL2 a ε 2 U ha haε‖ ^ 2 =
          ∫ x : AddCircle (1 : ℝ),
            ‖(F : AddCircle (1 : ℝ) → ℂ) x‖ ^ 2
              ∂AddCircle.haarAddCircle := by simpa only [F] using! hinner
      _ = ∑' z : ℤ,
          ‖fourierCoeff (F : AddCircle (1 : ℝ) → ℂ) z‖ ^ 2 := hparseval.symm
      _ ≤ 2 * (nearZeroFrequencyOneConstant ^ 2 +
          (4 * nearZeroTinyFrequencyConstant ^ 2 +
            32 * nearZeroInitialFrequencyConstant ^ 2 / a +
            ((Finset.Ico (M + 1) S).card : ℝ) *
              nearZeroPrincipalScaleConstant ^ 2 / a +
            2 * (384 * Real.sqrt 42 * Real.pi * nearProfileDecayConstant) ^ 2 / a)) := by
        simpa only [F] using!
          tsum_norm_sq_fourierCoeff_smoothNearPrimitivePoleTailL2_int_le
            a ε U M S ha hε haε hεhalf hUfour hM hMS
              hinitialTop hprincipalBase hinitialU hprincipalU hhigh
  · exact L2.integrable_inner F F

end

end Erdos1002
