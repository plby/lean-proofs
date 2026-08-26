import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import ErdosProblems.Erdos1002.NearResonantZeroCarrierIntermediate

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Global parameter split for the smooth zero carrier

The lower principal estimate requires its square-root denominator ceiling to
lie below `U`, whereas the high-frequency estimate starts only once
`U² ≤ aK`.  These conditions leave the genuine intermediate range
`U² ≤ K < U²/a`.  This file inserts the endpoint-tail estimate from
`NearResonantZeroCarrierIntermediate` and then performs the complete
five-piece frequency split, with every cutoff hypothesis exposed.
-/

open Filter MeasureTheory Set Finset
open scoped BigOperators ComplexConjugate ENNReal Real

namespace Erdos1002

noncomputable section

/-! ## Closing the single square-root boundary block -/

/-- If the integer ceiling of `sqrt K` is exactly the denominator cutoff
`U`, the low-range endpoint estimate stops at `U-1` and the remaining
singleton `p=U` is treated explicitly.  This is the boundary case omitted
by the strict hypothesis `sqrt K + 1 < U`. -/
theorem norm_smoothNearPrimitivePoleTailDyadicProjection_two_le_sqrtBoundary
    (a ε : ℝ) (K U : ℕ)
    (ha : 0 < a) (hε : 0 < ε) (haε : a ≤ ε / 4)
    (hεhalf : ε < 1 / 2) (hK : 0 < K)
    (hlarge : 16 ≤ a * (K : ℝ))
    (hboundary : Nat.sqrt K + 1 = U) :
    ‖smoothNearPrimitivePoleTailDyadicProjection a ε K 2 U ha haε‖ ≤
      nearZeroPrincipalScaleConstant / Real.sqrt a := by
  obtain ⟨R, hband, hnext⟩ :=
    exists_nearZeroPrincipalExponent a K ha hK hlarge
  let P : ℕ := Nat.sqrt K + 1
  let Q : ℕ := 2 ^ (R + 1)
  obtain ⟨hP, hPm1K, hKP⟩ := nearZeroNatSqrtCeiling_spec K hK
  have hQP : Q < P - 1 := by
    dsimp [Q, P]
    simpa using! nearZeroPrincipalEndpoint_lt_natSqrt
      a ε K R haε hεhalf hK hband
  have hQtwo : 2 ≤ Q := by
    dsimp [Q]
    have hone : 1 ≤ 2 ^ R := Nat.one_le_two_pow
    rw [pow_succ]
    omega
  have hQleP : Q ≤ P := hQP.le.trans (Nat.sub_le P 1)
  have hsplit₁ := finiteNearRamanujanMultiplierVector_split_at
    a ε K Q P hQtwo hQleP
  have hPm1succ : P - 1 + 1 = P := by omega
  have hsplit₂ :
      finiteNearRamanujanMultiplierVector a ε K (Q + 1) P =
        finiteNearRamanujanMultiplierVector a ε K (Q + 1) (P - 1) +
          finiteNearRamanujanMultiplierVector a ε K P P := by
    rw [finiteNearRamanujanMultiplierVector_eq_sum_Ioc a ε K Q P,
      finiteNearRamanujanMultiplierVector_eq_sum_Ioc a ε K Q (P - 1)]
    rw [show finiteNearRamanujanMultiplierVector a ε K P P =
        ∑ p ∈ Finset.Ioc (P - 1) P,
          euclideanCoordinateMul (nearRamanujanVectorTerm K p)
            (nearJDyadicMultiplierVector a ε K (p : ℝ)) by
      simpa only [hPm1succ] using!
        finiteNearRamanujanMultiplierVector_eq_sum_Ioc
          a ε K (P - 1) P]
    exact (Finset.sum_Ioc_consecutive
      (fun p : ℕ ↦ euclideanCoordinateMul (nearRamanujanVectorTerm K p)
        (nearJDyadicMultiplierVector a ε K (p : ℝ)))
      hQP.le (Nat.sub_le P 1)).symm
  have hlow :
      ‖finiteNearRamanujanMultiplierVector a ε K 3 Q‖ ≤
        192 * Real.sqrt 42 * Real.pi * nearProfileDecayConstant * (Q : ℝ) /
          (a * Real.sqrt (K : ℝ)) := by
    rw [← nearZeroLowDyadicVector_eq_interval a ε K R]
    simpa only [Q] using! norm_nearZeroLowDyadicVector_le
      a ε K R ha hε haε hεhalf hK hband
  have htail := norm_finiteNearRamanujanMultiplierVector_tail_le_lowRange
    a ε K Q (P - 1) ha hε haε hK (by positivity) hQP hPm1K
  have hsingle :=
    norm_finiteNearRamanujanMultiplierVector_singleton_le_highRange
      a ε K P ha hε haε hP hKP
  have hvector :
      ‖finiteNearRamanujanMultiplierVector a ε K 3 P‖ ≤
        192 * Real.sqrt 42 * Real.pi * nearProfileDecayConstant * (Q : ℝ) /
            (a * Real.sqrt (K : ℝ)) +
          (2 * Real.sqrt 42 * Real.sqrt (K : ℝ) / (Q : ℝ)) *
            (64 * Real.pi * nearProfileDecayConstant) +
          (16 * Real.sqrt 54 * Real.pi * nearProfileDecayConstant *
            (ε / 2 + a)) * (K : ℝ) / (P : ℝ) ^ 2 := by
    rw [hsplit₁, hsplit₂]
    calc
      ‖finiteNearRamanujanMultiplierVector a ε K 3 Q +
          (finiteNearRamanujanMultiplierVector a ε K (Q + 1) (P - 1) +
            finiteNearRamanujanMultiplierVector a ε K P P)‖ ≤
        ‖finiteNearRamanujanMultiplierVector a ε K 3 Q‖ +
          ‖finiteNearRamanujanMultiplierVector a ε K (Q + 1) (P - 1) +
            finiteNearRamanujanMultiplierVector a ε K P P‖ := norm_add_le _ _
      _ ≤ ‖finiteNearRamanujanMultiplierVector a ε K 3 Q‖ +
          (‖finiteNearRamanujanMultiplierVector a ε K (Q + 1) (P - 1)‖ +
            ‖finiteNearRamanujanMultiplierVector a ε K P P‖) :=
        add_le_add le_rfl (norm_add_le _ _)
      _ ≤
          192 * Real.sqrt 42 * Real.pi * nearProfileDecayConstant * (Q : ℝ) /
              (a * Real.sqrt (K : ℝ)) +
            ((2 * Real.sqrt 42 * Real.sqrt (K : ℝ) / (Q : ℝ)) *
                (64 * Real.pi * nearProfileDecayConstant) +
              (16 * Real.sqrt 54 * Real.pi * nearProfileDecayConstant *
                (ε / 2 + a)) * (K : ℝ) / (P : ℝ) ^ 2) :=
        add_le_add hlow (add_le_add htail hsingle)
      _ =
          192 * Real.sqrt 42 * Real.pi * nearProfileDecayConstant * (Q : ℝ) /
              (a * Real.sqrt (K : ℝ)) +
            (2 * Real.sqrt 42 * Real.sqrt (K : ℝ) / (Q : ℝ)) *
              (64 * Real.pi * nearProfileDecayConstant) +
            (16 * Real.sqrt 54 * Real.pi * nearProfileDecayConstant *
              (ε / 2 + a)) * (K : ℝ) / (P : ℝ) ^ 2 := by ring
  have hphysical :
      ‖smoothNearPrimitivePoleTailDyadicProjection a ε K 2 U ha haε‖ =
        ‖finiteNearRamanujanMultiplierVector a ε K 3 P‖ := by
    rw [norm_smoothNearPrimitivePoleTailDyadicProjection_eq_vector
      a ε K 2 U (by norm_num) ha hε haε hεhalf.le]
    simp only [P, hboundary]
  let Qr : ℝ := (Q : ℝ)
  have hKR : 0 < (K : ℝ) := by exact_mod_cast hK
  have hQr : 0 < Qr := by dsimp [Qr, Q]; positivity
  have hlowScalar :
      Qr / (a * Real.sqrt (K : ℝ)) ≤ 1 / Real.sqrt a :=
    div_mul_sqrt_le_inv_sqrt_of_sq_le a (K : ℝ) Qr
      ha hKR hQr.le (by simpa only [Qr, Q] using! hband)
  have htailScalar :
      Real.sqrt (K : ℝ) / Qr ≤ 2 / Real.sqrt a :=
    sqrt_div_le_two_inv_sqrt_of_le_sq a (K : ℝ) Qr
      ha hKR hQr (by simpa only [Qr, Q] using! hnext)
  let D₀ : ℝ := 16 * Real.sqrt 54 * Real.pi * nearProfileDecayConstant
  let D : ℝ := (16 * Real.sqrt 54 + 64 * Real.sqrt 42) * Real.pi *
    nearProfileDecayConstant
  have hprofile : 0 ≤ nearProfileDecayConstant :=
    nearProfileDecayConstant_nonneg
  have hD₀ : 0 ≤ D₀ := by
    dsimp [D₀]
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
        Real.pi_nonneg) hprofile
  have hD : 0 ≤ D := by
    dsimp [D]
    exact mul_nonneg
      (mul_nonneg
        (add_nonneg
          (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
          (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)))
        Real.pi_nonneg) hprofile
  have hscale : ε / 2 + a ≤ 1 := by linarith
  have hPpos : 0 < (P : ℝ) ^ 2 := by positivity
  have hratio : (K : ℝ) / (P : ℝ) ^ 2 ≤ 1 := by
    apply (div_le_one₀ hPpos).2
    exact_mod_cast hKP
  have hsingleNorm :
      D₀ * (ε / 2 + a) * (K : ℝ) / (P : ℝ) ^ 2 ≤ D₀ := by
    calc
      D₀ * (ε / 2 + a) * (K : ℝ) / (P : ℝ) ^ 2 =
          (D₀ * (ε / 2 + a)) * ((K : ℝ) / (P : ℝ) ^ 2) := by ring
      _ ≤ (D₀ * 1) * 1 := by gcongr
      _ = D₀ := by ring
  have hD₀D : D₀ ≤ D := by
    dsimp [D₀, D]
    have hnonneg : 0 ≤
        64 * Real.sqrt 42 * Real.pi * nearProfileDecayConstant := by
      exact mul_nonneg
        (mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
          Real.pi_nonneg) hprofile
    nlinarith
  have haOne : a ≤ 1 := by linarith
  have hsqrta : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
  have hsqrtOne : Real.sqrt a ≤ 1 := Real.sqrt_le_one.2 haOne
  have hDdiv : D₀ ≤ D / Real.sqrt a := by
    refine hD₀D.trans ?_
    apply (le_div_iff₀ hsqrta).2
    exact mul_le_of_le_one_right hD hsqrtOne
  rw [hphysical]
  calc
    ‖finiteNearRamanujanMultiplierVector a ε K 3 P‖ ≤
        192 * Real.sqrt 42 * Real.pi * nearProfileDecayConstant * (Q : ℝ) /
            (a * Real.sqrt (K : ℝ)) +
          (2 * Real.sqrt 42 * Real.sqrt (K : ℝ) / (Q : ℝ)) *
            (64 * Real.pi * nearProfileDecayConstant) +
          D₀ * (ε / 2 + a) * (K : ℝ) / (P : ℝ) ^ 2 := by
      simpa only [D₀] using! hvector
    _ ≤ 192 * Real.sqrt 42 * Real.pi * nearProfileDecayConstant /
          Real.sqrt a +
        (4 * Real.sqrt 42 / Real.sqrt a) *
          (64 * Real.pi * nearProfileDecayConstant) + D / Real.sqrt a := by
      have hlowNorm :
          192 * Real.sqrt 42 * Real.pi * nearProfileDecayConstant * (Q : ℝ) /
              (a * Real.sqrt (K : ℝ)) ≤
            192 * Real.sqrt 42 * Real.pi * nearProfileDecayConstant /
              Real.sqrt a := by
        have hlowConstant :
            0 ≤ 192 * Real.sqrt 42 * Real.pi * nearProfileDecayConstant := by
          exact mul_nonneg
            (mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
              Real.pi_nonneg) hprofile
        calc
          192 * Real.sqrt 42 * Real.pi * nearProfileDecayConstant * (Q : ℝ) /
              (a * Real.sqrt (K : ℝ)) =
            (192 * Real.sqrt 42 * Real.pi * nearProfileDecayConstant) *
              (Qr / (a * Real.sqrt (K : ℝ))) := by
                dsimp [Qr]
                ring
          _ ≤ (192 * Real.sqrt 42 * Real.pi * nearProfileDecayConstant) *
              (1 / Real.sqrt a) :=
            mul_le_mul_of_nonneg_left hlowScalar hlowConstant
          _ = 192 * Real.sqrt 42 * Real.pi * nearProfileDecayConstant /
              Real.sqrt a := by ring
      have htailNorm :
          (2 * Real.sqrt 42 * Real.sqrt (K : ℝ) / (Q : ℝ)) *
              (64 * Real.pi * nearProfileDecayConstant) ≤
            (4 * Real.sqrt 42 / Real.sqrt a) *
              (64 * Real.pi * nearProfileDecayConstant) := by
        have h64 : 0 ≤ 64 * Real.pi * nearProfileDecayConstant := by
          exact mul_nonneg (mul_nonneg (by norm_num) Real.pi_nonneg) hprofile
        calc
          (2 * Real.sqrt 42 * Real.sqrt (K : ℝ) / (Q : ℝ)) *
              (64 * Real.pi * nearProfileDecayConstant) =
            ((2 * Real.sqrt 42) * (Real.sqrt (K : ℝ) / Qr)) *
              (64 * Real.pi * nearProfileDecayConstant) := by
                dsimp [Qr]
                ring
          _ ≤ ((2 * Real.sqrt 42) * (2 / Real.sqrt a)) *
              (64 * Real.pi * nearProfileDecayConstant) := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left htailScalar
                (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))) h64
          _ = (4 * Real.sqrt 42 / Real.sqrt a) *
              (64 * Real.pi * nearProfileDecayConstant) := by ring
      exact add_le_add (add_le_add hlowNorm htailNorm)
        (hsingleNorm.trans hDdiv)
    _ = nearZeroPrincipalScaleConstant / Real.sqrt a := by
      unfold nearZeroPrincipalScaleConstant
      dsimp [D]
      field_simp [hsqrta.ne']

/-- Every block below `U²` is covered: normally the square-root ceiling is
strictly below `U`; equality is the boundary lemma above. -/
theorem norm_smoothNearPrimitivePoleTailDyadicProjection_two_le_lower_of_large
    (a ε : ℝ) (K U : ℕ)
    (ha : 0 < a) (hε : 0 < ε) (haε : a ≤ ε / 4)
    (hεhalf : ε < 1 / 2) (hK : 0 < K)
    (hlarge : 16 ≤ a * (K : ℝ)) (hKU : K < U ^ 2) :
    ‖smoothNearPrimitivePoleTailDyadicProjection a ε K 2 U ha haε‖ ≤
      nearZeroPrincipalScaleConstant / Real.sqrt a := by
  have hsqrtLt : Nat.sqrt K < U := by
    exact Nat.sqrt_lt'.2 hKU
  by_cases hstrict : Nat.sqrt K + 1 < U
  · exact norm_smoothNearPrimitivePoleTailDyadicProjection_two_le_of_large
      a ε K U ha hε haε hεhalf hK hlarge hstrict
  · have heq : Nat.sqrt K + 1 = U := by omega
    exact norm_smoothNearPrimitivePoleTailDyadicProjection_two_le_sqrtBoundary
      a ε K U ha hε haε hεhalf hK hlarge heq

/-- Square-sum of every lower-principal block under the natural scale
condition `K < U²`.  The square-root boundary is included. -/
theorem sum_sq_norm_smoothNearPrimitivePoleTailDyadicProjection_lower_le
    (a ε : ℝ) (U : ℕ) (I : Finset ℕ)
    (ha : 0 < a) (hε : 0 < ε) (haε : a ≤ ε / 4)
    (hεhalf : ε < 1 / 2)
    (hlarge : ∀ s ∈ I, 16 ≤ a * ((2 ^ s : ℕ) : ℝ))
    (hupper : ∀ s ∈ I, 2 ^ s < U ^ 2) :
    ∑ s ∈ I,
        ‖smoothNearPrimitivePoleTailDyadicProjection
          a ε (2 ^ s) 2 U ha haε‖ ^ 2 ≤
      (I.card : ℝ) * nearZeroPrincipalScaleConstant ^ 2 / a := by
  have hsqrta : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
  have hconstant : 0 ≤ nearZeroPrincipalScaleConstant :=
    nearZeroPrincipalScaleConstant_nonneg
  calc
    ∑ s ∈ I,
        ‖smoothNearPrimitivePoleTailDyadicProjection
          a ε (2 ^ s) 2 U ha haε‖ ^ 2 ≤
      ∑ _s ∈ I,
        (nearZeroPrincipalScaleConstant / Real.sqrt a) ^ 2 := by
      apply Finset.sum_le_sum
      intro s hs
      have hnorm :=
        norm_smoothNearPrimitivePoleTailDyadicProjection_two_le_lower_of_large
          a ε (2 ^ s) U ha hε haε hεhalf (by positivity)
            (hlarge s hs) (hupper s hs)
      exact (sq_le_sq₀ (norm_nonneg _)
        (div_nonneg hconstant hsqrta.le)).2 hnorm
    _ = (I.card : ℝ) * nearZeroPrincipalScaleConstant ^ 2 / a := by
      rw [Finset.sum_const, nsmul_eq_mul, div_pow, Real.sq_sqrt ha.le]
      ring

/-- Square-sum of all intermediate blocks.  The strict upper scale
`aK < U²` forces every selected principal denominator endpoint to be
strictly below `U`; this supplies the endpoint premise of the one-block
intermediate estimate rather than hiding it in a choice function. -/
theorem sum_sq_norm_smoothNearPrimitivePoleTailDyadicProjection_intermediate_le
    (a ε : ℝ) (U : ℕ) (I : Finset ℕ)
    (ha : 0 < a) (hε : 0 < ε) (haε : a ≤ ε / 4)
    (hεhalf : ε < 1 / 2)
    (hlarge : ∀ s ∈ I, 16 ≤ a * ((2 ^ s : ℕ) : ℝ))
    (hlower : ∀ s ∈ I, U ^ 2 ≤ 2 ^ s)
    (hupper : ∀ s ∈ I,
      a * ((2 ^ s : ℕ) : ℝ) < ((U : ℝ) ^ 2)) :
    ∑ s ∈ I,
        ‖smoothNearPrimitivePoleTailDyadicProjection
          a ε (2 ^ s) 2 U ha haε‖ ^ 2 ≤
      (I.card : ℝ) * nearZeroPrincipalScaleConstant ^ 2 / a := by
  have hsqrta : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
  have hconstant : 0 ≤ nearZeroPrincipalScaleConstant :=
    nearZeroPrincipalScaleConstant_nonneg
  calc
    ∑ s ∈ I,
        ‖smoothNearPrimitivePoleTailDyadicProjection
          a ε (2 ^ s) 2 U ha haε‖ ^ 2 ≤
      ∑ _s ∈ I,
        (nearZeroPrincipalScaleConstant / Real.sqrt a) ^ 2 := by
      apply Finset.sum_le_sum
      intro s hs
      have hnorm :=
        norm_smoothNearPrimitivePoleTailDyadicProjection_two_le_intermediate_of_large
          a ε (2 ^ s) U ha hε haε hεhalf (by positivity)
            (hlarge s hs) (hlower s hs) (by
              intro R hband
              let q : ℕ := 2 ^ (R + 1)
              have hq0 : 0 ≤ (q : ℝ) := by positivity
              have hU0 : 0 ≤ (U : ℝ) := by positivity
              have hband' : (q : ℝ) ^ 2 ≤
                  a * ((2 ^ s : ℕ) : ℝ) := by
                simpa only [q] using! hband
              have hsq : (q : ℝ) ^ 2 < (U : ℝ) ^ 2 := by
                exact hband'.trans_lt (hupper s hs)
              have hqUReal : (q : ℝ) < (U : ℝ) := by nlinarith
              exact_mod_cast hqUReal)
      exact (sq_le_sq₀ (norm_nonneg _)
        (div_nonneg hconstant hsqrta.le)).2 hnorm
    _ = (I.card : ℝ) * nearZeroPrincipalScaleConstant ^ 2 / a := by
      rw [Finset.sum_const, nsmul_eq_mul, div_pow, Real.sq_sqrt ha.le]
      ring

/-! ## Explicit dyadic cutoffs -/

/-- Simultaneous construction of the three dyadic frequency cutoffs.

* `M+1` is the first exponent with `16 ≤ a 2^s`;
* `T = clog₂(U²)` is the first exponent with `U² ≤ 2^s`;
* `S` is the first exponent with `U² ≤ a 2^s`.

Minimality supplies all strict inequalities on the preceding blocks.  More
importantly, `S ≤ (M+1)+T`, so the total number of principal and
intermediate blocks is at most `T ≤ 2 clog₂ U`; the dependence on `a`
cancels rather than producing a spurious logarithmic loss. -/
theorem exists_nearZeroFrequencySplit
    (a : ℝ) (U : ℕ) (ha : 0 < a) (haHalf : a ≤ 1 / 2)
    (hUfour : 4 ≤ U)
    (hroom : 16 < a * (((U - 1 : ℕ) : ℝ) ^ 2)) :
    ∃ M T S : ℕ,
      4 ≤ M ∧ M + 1 ≤ T ∧ T ≤ S ∧
      a * ((2 ^ M : ℕ) : ℝ) ≤ 16 ∧
      16 ≤ a * ((2 ^ (M + 1) : ℕ) : ℝ) ∧
      (∀ s ∈ Finset.Ico 4 (M + 1), Nat.sqrt (2 ^ s) + 1 < U) ∧
      (∀ s ∈ Finset.Ico (M + 1) T, 2 ^ s < U ^ 2) ∧
      (∀ s ∈ Finset.Ico T S, U ^ 2 ≤ 2 ^ s) ∧
      (∀ s ∈ Finset.Ico T S,
        a * ((2 ^ s : ℕ) : ℝ) < ((U : ℝ) ^ 2)) ∧
      ((U : ℝ) ^ 2) ≤ a * ((2 ^ S : ℕ) : ℝ) ∧
      Finset.card (Finset.Ico (M + 1) T) +
        Finset.card (Finset.Ico T S) ≤ 2 * Nat.clog 2 U := by
  have hexStart : ∃ n : ℕ, 16 ≤ a * ((2 ^ n : ℕ) : ℝ) := by
    rcases pow_unbounded_of_one_lt (16 / a) (by norm_num : (1 : ℝ) < 2) with
      ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have hmul := (div_lt_iff₀ ha).mp hn
    norm_num at hmul ⊢
    simpa only [Nat.cast_pow, Nat.cast_ofNat, mul_comm] using! hmul.le
  let n₀ : ℕ := Nat.find hexStart
  have hn₀spec : 16 ≤ a * ((2 ^ n₀ : ℕ) : ℝ) := by
    dsimp [n₀]
    exact Nat.find_spec hexStart
  have hn₀min : ∀ s < n₀, a * ((2 ^ s : ℕ) : ℝ) < 16 := by
    intro s hs
    exact lt_of_not_ge (Nat.find_min hexStart hs)
  have hn₀four : 4 < n₀ := by
    by_contra hnot
    have hnle : n₀ ≤ 4 := Nat.le_of_not_gt hnot
    have hpowNat : 2 ^ n₀ ≤ 16 := by
      calc
        2 ^ n₀ ≤ 2 ^ 4 := Nat.pow_le_pow_right (by omega) hnle
        _ = 16 := by norm_num
    have hpowReal : (((2 ^ n₀ : ℕ) : ℝ)) ≤ 16 := by exact_mod_cast hpowNat
    have hprod : a * ((2 ^ n₀ : ℕ) : ℝ) ≤ 8 := by nlinarith
    linarith
  let M : ℕ := n₀ - 1
  have hMn₀ : M + 1 = n₀ := by dsimp [M]; omega
  have hMfour : 4 ≤ M := by dsimp [M]; omega
  have hMtop : a * ((2 ^ M : ℕ) : ℝ) ≤ 16 :=
    (hn₀min M (by dsimp [M]; omega)).le
  have hMbase : 16 ≤ a * ((2 ^ (M + 1) : ℕ) : ℝ) := by
    simpa only [hMn₀] using! hn₀spec
  let T : ℕ := Nat.clog 2 (U ^ 2)
  have hUT : U ^ 2 ≤ 2 ^ T := by
    dsimp [T]
    exact Nat.le_pow_clog (by omega) (U ^ 2)
  have hbelowT : ∀ s < T, 2 ^ s < U ^ 2 := by
    intro s hs
    dsimp [T] at hs
    exact (Nat.lt_clog_iff_pow_lt (by omega)).mp hs
  have hn₀T : n₀ ≤ T := by
    apply Nat.find_min' hexStart
    have hUsub : U - 1 ≤ U := Nat.sub_le U 1
    have hsqSubNat : (U - 1) ^ 2 ≤ U ^ 2 := Nat.pow_le_pow_left hUsub 2
    have hsqSub : ((((U - 1) ^ 2 : ℕ) : ℝ)) ≤ ((U ^ 2 : ℕ) : ℝ) := by
      exact_mod_cast hsqSubNat
    have hUTReal : (((U ^ 2 : ℕ) : ℝ)) ≤ (((2 ^ T : ℕ) : ℝ)) := by
      exact_mod_cast hUT
    have h16T : 16 ≤ a * (((2 ^ T : ℕ) : ℝ)) := by
      have hsubToT : (((U - 1 : ℕ) : ℝ) ^ 2) ≤
          (((2 ^ T : ℕ) : ℝ)) := by
        calc
          ((U - 1 : ℕ) : ℝ) ^ 2 = ((((U - 1) ^ 2 : ℕ) : ℝ)) := by
            norm_num
          _ ≤ ((U ^ 2 : ℕ) : ℝ) := hsqSub
          _ ≤ ((2 ^ T : ℕ) : ℝ) := hUTReal
      exact hroom.le.trans (mul_le_mul_of_nonneg_left hsubToT ha.le)
    exact h16T
  have hMT : M + 1 ≤ T := by simpa only [hMn₀] using! hn₀T
  have hexHigh : ∃ n : ℕ,
      ((U : ℝ) ^ 2) ≤ a * ((2 ^ n : ℕ) : ℝ) := by
    rcases pow_unbounded_of_one_lt (((U : ℝ) ^ 2) / a)
        (by norm_num : (1 : ℝ) < 2) with ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have hmul := (div_lt_iff₀ ha).mp hn
    simpa only [Nat.cast_pow, Nat.cast_ofNat, mul_comm] using! hmul.le
  let S : ℕ := Nat.find hexHigh
  have hSspec : ((U : ℝ) ^ 2) ≤ a * ((2 ^ S : ℕ) : ℝ) := by
    dsimp [S]
    exact Nat.find_spec hexHigh
  have hSmin : ∀ s < S,
      a * ((2 ^ s : ℕ) : ℝ) < ((U : ℝ) ^ 2) := by
    intro s hs
    exact lt_of_not_ge (Nat.find_min hexHigh hs)
  have haOne : a ≤ 1 := haHalf.trans (by norm_num)
  have hTS : T ≤ S := by
    by_contra hnot
    have hST : S < T := Nat.lt_of_not_ge hnot
    have hpowNat := hbelowT S hST
    have hpowReal : (((2 ^ S : ℕ) : ℝ)) < ((U : ℝ) ^ 2) := by
      exact_mod_cast hpowNat
    have hprod : a * ((2 ^ S : ℕ) : ℝ) ≤ ((2 ^ S : ℕ) : ℝ) := by
      exact mul_le_of_le_one_left (by positivity) haOne
    linarith
  have hSn₀T : S ≤ n₀ + T := by
    apply Nat.find_min' hexHigh
    have hUTReal : ((U : ℝ) ^ 2) ≤ ((2 ^ T : ℕ) : ℝ) := by
      exact_mod_cast hUT
    calc
      (U : ℝ) ^ 2 ≤ 16 * (U : ℝ) ^ 2 := by nlinarith [sq_nonneg (U : ℝ)]
      _ ≤ (a * ((2 ^ n₀ : ℕ) : ℝ)) *
          ((2 ^ T : ℕ) : ℝ) := by
        exact mul_le_mul hn₀spec hUTReal (sq_nonneg _) (by positivity)
      _ = a * ((2 ^ (n₀ + T) : ℕ) : ℝ) := by
        rw [pow_add]
        push_cast
        ring
  have hinitialU : ∀ s ∈ Finset.Ico 4 (M + 1),
      Nat.sqrt (2 ^ s) + 1 < U := by
    intro s hs
    have hsn₀ : s < n₀ := by simpa only [hMn₀] using! (Finset.mem_Ico.mp hs).2
    have hprodLt := (hn₀min s hsn₀).trans hroom
    have hpowReal : (((2 ^ s : ℕ) : ℝ)) < (((U - 1 : ℕ) : ℝ) ^ 2) := by
      nlinarith
    have hpowNat : 2 ^ s < (U - 1) ^ 2 := by exact_mod_cast hpowReal
    have hsqrt : Nat.sqrt (2 ^ s) < U - 1 := Nat.sqrt_lt'.2 hpowNat
    omega
  have hlower : ∀ s ∈ Finset.Ico (M + 1) T, 2 ^ s < U ^ 2 := by
    intro s hs
    exact hbelowT s (Finset.mem_Ico.mp hs).2
  have hinterLower : ∀ s ∈ Finset.Ico T S, U ^ 2 ≤ 2 ^ s := by
    intro s hs
    exact (Nat.clog_le_iff_le_pow (by omega)).mp (by
      simpa only [T] using! (Finset.mem_Ico.mp hs).1)
  have hinterUpper : ∀ s ∈ Finset.Ico T S,
      a * ((2 ^ s : ℕ) : ℝ) < ((U : ℝ) ^ 2) := by
    intro s hs
    exact hSmin s (Finset.mem_Ico.mp hs).2
  have hTlog : T ≤ 2 * Nat.clog 2 U := by
    let c : ℕ := Nat.clog 2 U
    have hUc : U ≤ 2 ^ c := by
      dsimp [c]
      exact Nat.le_pow_clog (by omega) U
    have hsq : U ^ 2 ≤ 2 ^ (2 * c) := by
      calc
        U ^ 2 ≤ (2 ^ c) ^ 2 := Nat.pow_le_pow_left hUc 2
        _ = 2 ^ (2 * c) := by rw [← pow_mul]; congr 1; omega
    dsimp [T, c]
    exact Nat.clog_le_of_le_pow hsq
  have hcard :
      Finset.card (Finset.Ico (M + 1) T) +
          Finset.card (Finset.Ico T S) ≤ 2 * Nat.clog 2 U := by
    simp only [Nat.card_Ico]
    have hSn : S ≤ (M + 1) + T := by simpa only [hMn₀] using! hSn₀T
    omega
  exact ⟨M, T, S, hMfour, hMT, hTS, hMtop, hMbase,
    hinitialU, hlower, hinterLower, hinterUpper, hSspec, hcard⟩

/-- Complete finite positive-frequency square-function estimate with the
previously missing intermediate interval shown as its own summand. -/
theorem sum_sq_norm_smoothNearPrimitivePoleTailDyadicProjection_range_le_split
    (a ε : ℝ) (U M T S H : ℕ)
    (ha : 0 < a) (hε : 0 < ε) (haε : a ≤ ε / 4)
    (hεhalf : ε < 1 / 2) (hUfour : 4 ≤ U)
    (hM : 4 ≤ M) (hMT : M + 1 ≤ T) (hTS : T ≤ S) (hSH : S ≤ H)
    (hinitialTop : a * ((2 ^ M : ℕ) : ℝ) ≤ 16)
    (hprincipalBase : 16 ≤ a * ((2 ^ (M + 1) : ℕ) : ℝ))
    (hinitialU : ∀ s ∈ Finset.Ico 4 (M + 1),
      Nat.sqrt (2 ^ s) + 1 < U)
    (hprincipalUpper : ∀ s ∈ Finset.Ico (M + 1) T,
      2 ^ s < U ^ 2)
    (hinterLower : ∀ s ∈ Finset.Ico T S, U ^ 2 ≤ 2 ^ s)
    (hinterUpper : ∀ s ∈ Finset.Ico T S,
      a * ((2 ^ s : ℕ) : ℝ) < ((U : ℝ) ^ 2))
    (hhigh : ((U : ℝ) ^ 2) ≤ a * ((2 ^ S : ℕ) : ℝ)) :
    ∑ s ∈ Finset.range H,
        ‖smoothNearPrimitivePoleTailDyadicProjection
          a ε (2 ^ s) 2 U ha haε‖ ^ 2 ≤
      4 * nearZeroTinyFrequencyConstant ^ 2 +
        32 * nearZeroInitialFrequencyConstant ^ 2 / a +
        ((Finset.Ico (M + 1) T).card : ℝ) *
          nearZeroPrincipalScaleConstant ^ 2 / a +
        ((Finset.Ico T S).card : ℝ) *
          nearZeroPrincipalScaleConstant ^ 2 / a +
        2 * (384 * Real.sqrt 42 * Real.pi * nearProfileDecayConstant) ^ 2 / a := by
  let f : ℕ → ℝ := fun s ↦
    ‖smoothNearPrimitivePoleTailDyadicProjection
      a ε (2 ^ s) 2 U ha haε‖ ^ 2
  have hfourM : 4 ≤ M + 1 := by omega
  have hfourT : 4 ≤ T := hfourM.trans hMT
  have hfourS : 4 ≤ S := hfourT.trans hTS
  have hfourH : 4 ≤ H := hfourS.trans hSH
  have hsplit :
      ∑ s ∈ Finset.range H, f s =
        (∑ s ∈ Finset.range 4, f s) +
          (∑ s ∈ Finset.Ico 4 (M + 1), f s) +
          (∑ s ∈ Finset.Ico (M + 1) T, f s) +
          (∑ s ∈ Finset.Ico T S, f s) +
          (∑ s ∈ Finset.Ico S H, f s) := by
    rw [← Finset.sum_range_add_sum_Ico f hfourH,
      ← Finset.sum_Ico_consecutive f hfourM
        (hMT.trans (hTS.trans hSH)),
      ← Finset.sum_Ico_consecutive f hMT (hTS.trans hSH),
      ← Finset.sum_Ico_consecutive f hTS hSH]
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
    simpa only [f] using!
      sum_sq_norm_smoothNearPrimitivePoleTailDyadicProjection_initial_le
        a ε U M ha hε haε hεhalf hM hinitialTop hinitialU
  have hlarge : ∀ s ∈ Finset.Ico (M + 1) S,
      16 ≤ a * ((2 ^ s : ℕ) : ℝ) := by
    intro s hs
    have hsLower := (Finset.mem_Ico.mp hs).1
    have hpow : ((2 ^ (M + 1) : ℕ) : ℝ) ≤ ((2 ^ s : ℕ) : ℝ) := by
      exact_mod_cast Nat.pow_le_pow_right (by omega : 0 < 2) hsLower
    exact hprincipalBase.trans (mul_le_mul_of_nonneg_left hpow ha.le)
  have hprincipal :
      ∑ s ∈ Finset.Ico (M + 1) T, f s ≤
        ((Finset.Ico (M + 1) T).card : ℝ) *
          nearZeroPrincipalScaleConstant ^ 2 / a := by
    simpa only [f] using!
      sum_sq_norm_smoothNearPrimitivePoleTailDyadicProjection_lower_le
        a ε U (Finset.Ico (M + 1) T) ha hε haε hεhalf
          (fun s hs ↦ hlarge s (Finset.mem_Ico.mpr
            ⟨(Finset.mem_Ico.mp hs).1, (Finset.mem_Ico.mp hs).2.trans_le hTS⟩))
          hprincipalUpper
  have hintermediate :
      ∑ s ∈ Finset.Ico T S, f s ≤
        ((Finset.Ico T S).card : ℝ) *
          nearZeroPrincipalScaleConstant ^ 2 / a := by
    simpa only [f] using!
      sum_sq_norm_smoothNearPrimitivePoleTailDyadicProjection_intermediate_le
        a ε U (Finset.Ico T S) ha hε haε hεhalf
          (fun s hs ↦ hlarge s (Finset.mem_Ico.mpr
            ⟨hMT.trans (Finset.mem_Ico.mp hs).1, Finset.mem_Ico.mp hs |>.2⟩))
          hinterLower hinterUpper
  have hhighBound :
      ∑ s ∈ Finset.Ico S H, f s ≤
        2 * (384 * Real.sqrt 42 * Real.pi * nearProfileDecayConstant) ^ 2 / a := by
    simpa only [f] using!
      sum_sq_norm_smoothNearPrimitivePoleTailDyadicProjection_high_le
        a ε U S H ha hε haε hεhalf (by omega) hhigh
  rw [hsplit]
  exact add_le_add
    (add_le_add (add_le_add (add_le_add htiny hinitial) hprincipal)
      hintermediate) hhighBound

/-- The preceding complete split written as an actual positive Fourier
coefficient partial sum. -/
theorem sum_norm_sq_fourierCoeff_smoothNearPrimitivePoleTailL2_positive_le_split
    (a ε : ℝ) (U M T S H : ℕ)
    (ha : 0 < a) (hε : 0 < ε) (haε : a ≤ ε / 4)
    (hεhalf : ε < 1 / 2) (hUfour : 4 ≤ U)
    (hM : 4 ≤ M) (hMT : M + 1 ≤ T) (hTS : T ≤ S) (hSH : S ≤ H)
    (hinitialTop : a * ((2 ^ M : ℕ) : ℝ) ≤ 16)
    (hprincipalBase : 16 ≤ a * ((2 ^ (M + 1) : ℕ) : ℝ))
    (hinitialU : ∀ s ∈ Finset.Ico 4 (M + 1),
      Nat.sqrt (2 ^ s) + 1 < U)
    (hprincipalUpper : ∀ s ∈ Finset.Ico (M + 1) T,
      2 ^ s < U ^ 2)
    (hinterLower : ∀ s ∈ Finset.Ico T S, U ^ 2 ≤ 2 ^ s)
    (hinterUpper : ∀ s ∈ Finset.Ico T S,
      a * ((2 ^ s : ℕ) : ℝ) < ((U : ℝ) ^ 2))
    (hhigh : ((U : ℝ) ^ 2) ≤ a * ((2 ^ S : ℕ) : ℝ)) :
    ∑ n ∈ Finset.Ioc (1 : ℕ) (2 ^ H),
        ‖fourierCoeff
          (smoothNearPrimitivePoleTailL2 a ε 2 U ha haε :
            AddCircle (1 : ℝ) → ℂ) (n : ℤ)‖ ^ 2 ≤
      4 * nearZeroTinyFrequencyConstant ^ 2 +
        32 * nearZeroInitialFrequencyConstant ^ 2 / a +
        ((Finset.Ico (M + 1) T).card : ℝ) *
          nearZeroPrincipalScaleConstant ^ 2 / a +
        ((Finset.Ico T S).card : ℝ) *
          nearZeroPrincipalScaleConstant ^ 2 / a +
        2 * (384 * Real.sqrt 42 * Real.pi * nearProfileDecayConstant) ^ 2 / a := by
  rw [← sum_sq_norm_smoothNearPrimitivePoleTailDyadicProjection_range_eq
    a ε 2 U H ha haε]
  exact
    sum_sq_norm_smoothNearPrimitivePoleTailDyadicProjection_range_le_split
      a ε U M T S H ha hε haε hεhalf hUfour hM hMT hTS hSH
        hinitialTop hprincipalBase hinitialU hprincipalUpper
        hinterLower hinterUpper hhigh

/-! ## Removal of the terminal Fourier cutoff -/

private theorem tsum_nat_le_of_dyadic_positive_partials
    (f : ℕ → ℝ) (C₀ C : ℝ) (S : ℕ)
    (hf : ∀ n, 0 ≤ f n) (hf₀ : f 0 = 0) (hf₁ : f 1 ≤ C₀)
    (hpartial : ∀ H, S ≤ H →
      ∑ n ∈ Finset.Ioc (1 : ℕ) (2 ^ H), f n ≤ C) :
    ∑' n : ℕ, f n ≤ C₀ + C := by
  have hpowSelf : ∀ k : ℕ, k ≤ 2 ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        rw [pow_succ]
        have hone : 1 ≤ 2 ^ k := Nat.one_le_two_pow
        omega
  apply Real.tsum_le_of_sum_range_le hf
  intro k
  let H : ℕ := max S k
  let E : Finset ℕ :=
    insert 0 (insert 1 (Finset.Ioc (1 : ℕ) (2 ^ H)))
  have hSH : S ≤ H := by
    dsimp [H]
    exact le_max_left _ _
  have hkH : k ≤ H := by
    dsimp [H]
    exact le_max_right _ _
  have hkPow : k ≤ 2 ^ H := hkH.trans (hpowSelf H)
  have hsubset : Finset.range k ⊆ E := by
    intro n hn
    have hnk : n < k := Finset.mem_range.mp hn
    have hnPow : n ≤ 2 ^ H := (Nat.le_of_lt hnk).trans hkPow
    simp only [E, Finset.mem_insert, Finset.mem_Ioc]
    omega
  calc
    ∑ n ∈ Finset.range k, f n ≤ ∑ n ∈ E, f n := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
      intro n _hn _hnot
      exact hf n
    _ = f 0 + f 1 + ∑ n ∈ Finset.Ioc (1 : ℕ) (2 ^ H), f n := by
      simp [E, add_assoc]
    _ ≤ C₀ + C := by
      rw [hf₀, zero_add]
      exact add_le_add hf₁ (hpartial H hSH)

/-- Complete nonnegative-frequency energy for the valid lower/intermediate/
high split. -/
theorem tsum_norm_sq_fourierCoeff_smoothNearPrimitivePoleTailL2_nat_le_split
    (a ε : ℝ) (U M T S : ℕ)
    (ha : 0 < a) (hε : 0 < ε) (haε : a ≤ ε / 4)
    (hεhalf : ε < 1 / 2) (hUfour : 4 ≤ U)
    (hM : 4 ≤ M) (hMT : M + 1 ≤ T) (hTS : T ≤ S)
    (hinitialTop : a * ((2 ^ M : ℕ) : ℝ) ≤ 16)
    (hprincipalBase : 16 ≤ a * ((2 ^ (M + 1) : ℕ) : ℝ))
    (hinitialU : ∀ s ∈ Finset.Ico 4 (M + 1),
      Nat.sqrt (2 ^ s) + 1 < U)
    (hprincipalUpper : ∀ s ∈ Finset.Ico (M + 1) T,
      2 ^ s < U ^ 2)
    (hinterLower : ∀ s ∈ Finset.Ico T S, U ^ 2 ≤ 2 ^ s)
    (hinterUpper : ∀ s ∈ Finset.Ico T S,
      a * ((2 ^ s : ℕ) : ℝ) < ((U : ℝ) ^ 2))
    (hhigh : ((U : ℝ) ^ 2) ≤ a * ((2 ^ S : ℕ) : ℝ)) :
    ∑' n : ℕ,
        ‖fourierCoeff
          (smoothNearPrimitivePoleTailL2 a ε 2 U ha haε :
            AddCircle (1 : ℝ) → ℂ) (n : ℤ)‖ ^ 2 ≤
      nearZeroFrequencyOneConstant ^ 2 +
        (4 * nearZeroTinyFrequencyConstant ^ 2 +
          32 * nearZeroInitialFrequencyConstant ^ 2 / a +
          ((Finset.Ico (M + 1) T).card : ℝ) *
            nearZeroPrincipalScaleConstant ^ 2 / a +
          ((Finset.Ico T S).card : ℝ) *
            nearZeroPrincipalScaleConstant ^ 2 / a +
          2 * (384 * Real.sqrt 42 * Real.pi * nearProfileDecayConstant) ^ 2 / a) := by
  let f : ℕ → ℝ := fun n ↦
    ‖fourierCoeff
      (smoothNearPrimitivePoleTailL2 a ε 2 U ha haε :
        AddCircle (1 : ℝ) → ℂ) (n : ℤ)‖ ^ 2
  let C : ℝ :=
    4 * nearZeroTinyFrequencyConstant ^ 2 +
      32 * nearZeroInitialFrequencyConstant ^ 2 / a +
      ((Finset.Ico (M + 1) T).card : ℝ) *
        nearZeroPrincipalScaleConstant ^ 2 / a +
      ((Finset.Ico T S).card : ℝ) *
        nearZeroPrincipalScaleConstant ^ 2 / a +
      2 * (384 * Real.sqrt 42 * Real.pi * nearProfileDecayConstant) ^ 2 / a
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
  apply tsum_nat_le_of_dyadic_positive_partials f
    (nearZeroFrequencyOneConstant ^ 2) C S (fun n ↦ sq_nonneg _)
      hfzero hfone
  intro H hSH
  dsimp only [f, C]
  exact
    sum_norm_sq_fourierCoeff_smoothNearPrimitivePoleTailL2_positive_le_split
      a ε U M T S H ha hε haε hεhalf hUfour hM hMT hTS hSH
        hinitialTop hprincipalBase hinitialU hprincipalUpper
        hinterLower hinterUpper hhigh

private theorem tsum_int_le_two_mul_tsum_nat_of_even_zero
    (f : ℤ → ℝ) (C : ℝ)
    (hs : Summable f) (heven : f.Even) (hfzero : f 0 = 0)
    (hnat : (∑' n : ℕ, f (n : ℤ)) ≤ C) :
    (∑' z : ℤ, f z) ≤ 2 * C := by
  have hsnat : Summable (fun n : ℕ ↦ f (n : ℤ)) :=
    hs.comp_injective Nat.cast_injective
  have hpnat :
      (∑' n : ℕ+, f (n : ℤ)) = ∑' n : ℕ, f (n : ℤ) := by
    have h := tsum_zero_pnat_eq_tsum_nat hsnat
    have hfzeroCast : f ((0 : ℕ) : ℤ) = 0 := by simpa using! hfzero
    rw [hfzeroCast, zero_add] at h
    exact h
  rw [tsum_int_eq_zero_add_two_mul_tsum_pnat heven hs]
  simp only [hfzero, zero_add, nsmul_eq_mul, hpnat]
  exact mul_le_mul_of_nonneg_left hnat (by norm_num)

/-- Complete integer coefficient energy after inserting the intermediate
frequency range. -/
theorem tsum_norm_sq_fourierCoeff_smoothNearPrimitivePoleTailL2_int_le_split
    (a ε : ℝ) (U M T S : ℕ)
    (ha : 0 < a) (hε : 0 < ε) (haε : a ≤ ε / 4)
    (hεhalf : ε < 1 / 2) (hUfour : 4 ≤ U)
    (hM : 4 ≤ M) (hMT : M + 1 ≤ T) (hTS : T ≤ S)
    (hinitialTop : a * ((2 ^ M : ℕ) : ℝ) ≤ 16)
    (hprincipalBase : 16 ≤ a * ((2 ^ (M + 1) : ℕ) : ℝ))
    (hinitialU : ∀ s ∈ Finset.Ico 4 (M + 1),
      Nat.sqrt (2 ^ s) + 1 < U)
    (hprincipalUpper : ∀ s ∈ Finset.Ico (M + 1) T,
      2 ^ s < U ^ 2)
    (hinterLower : ∀ s ∈ Finset.Ico T S, U ^ 2 ≤ 2 ^ s)
    (hinterUpper : ∀ s ∈ Finset.Ico T S,
      a * ((2 ^ s : ℕ) : ℝ) < ((U : ℝ) ^ 2))
    (hhigh : ((U : ℝ) ^ 2) ≤ a * ((2 ^ S : ℕ) : ℝ)) :
    ∑' z : ℤ,
        ‖fourierCoeff
          (smoothNearPrimitivePoleTailL2 a ε 2 U ha haε :
            AddCircle (1 : ℝ) → ℂ) z‖ ^ 2 ≤
      2 * (nearZeroFrequencyOneConstant ^ 2 +
        (4 * nearZeroTinyFrequencyConstant ^ 2 +
          32 * nearZeroInitialFrequencyConstant ^ 2 / a +
          ((Finset.Ico (M + 1) T).card : ℝ) *
            nearZeroPrincipalScaleConstant ^ 2 / a +
          ((Finset.Ico T S).card : ℝ) *
            nearZeroPrincipalScaleConstant ^ 2 / a +
          2 * (384 * Real.sqrt 42 * Real.pi * nearProfileDecayConstant) ^ 2 / a)) := by
  let F := smoothNearPrimitivePoleTailL2 a ε 2 U ha haε
  let f : ℤ → ℝ := fun z ↦
    ‖fourierCoeff (F : AddCircle (1 : ℝ) → ℂ) z‖ ^ 2
  have hs : Summable f := (hasSum_sq_fourierCoeff F).summable
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
  apply tsum_int_le_two_mul_tsum_nat_of_even_zero f _ hs heven hfzero
  simpa only [f, F] using!
    tsum_norm_sq_fourierCoeff_smoothNearPrimitivePoleTailL2_nat_le_split
      a ε U M T S ha hε haε hεhalf hUfour hM hMT hTS
        hinitialTop hprincipalBase hinitialU hprincipalUpper
        hinterLower hinterUpper hhigh

/-- Physical `L²` estimate with no frequency truncation and no gap between
the principal and high-frequency regimes. -/
theorem norm_sq_smoothNearPrimitivePoleTailL2_le_split
    (a ε : ℝ) (U M T S : ℕ)
    (ha : 0 < a) (hε : 0 < ε) (haε : a ≤ ε / 4)
    (hεhalf : ε < 1 / 2) (hUfour : 4 ≤ U)
    (hM : 4 ≤ M) (hMT : M + 1 ≤ T) (hTS : T ≤ S)
    (hinitialTop : a * ((2 ^ M : ℕ) : ℝ) ≤ 16)
    (hprincipalBase : 16 ≤ a * ((2 ^ (M + 1) : ℕ) : ℝ))
    (hinitialU : ∀ s ∈ Finset.Ico 4 (M + 1),
      Nat.sqrt (2 ^ s) + 1 < U)
    (hprincipalUpper : ∀ s ∈ Finset.Ico (M + 1) T,
      2 ^ s < U ^ 2)
    (hinterLower : ∀ s ∈ Finset.Ico T S, U ^ 2 ≤ 2 ^ s)
    (hinterUpper : ∀ s ∈ Finset.Ico T S,
      a * ((2 ^ s : ℕ) : ℝ) < ((U : ℝ) ^ 2))
    (hhigh : ((U : ℝ) ^ 2) ≤ a * ((2 ^ S : ℕ) : ℝ)) :
    ‖smoothNearPrimitivePoleTailL2 a ε 2 U ha haε‖ ^ 2 ≤
      2 * (nearZeroFrequencyOneConstant ^ 2 +
        (4 * nearZeroTinyFrequencyConstant ^ 2 +
          32 * nearZeroInitialFrequencyConstant ^ 2 / a +
          ((Finset.Ico (M + 1) T).card : ℝ) *
            nearZeroPrincipalScaleConstant ^ 2 / a +
          ((Finset.Ico T S).card : ℝ) *
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
            ((Finset.Ico (M + 1) T).card : ℝ) *
              nearZeroPrincipalScaleConstant ^ 2 / a +
            ((Finset.Ico T S).card : ℝ) *
              nearZeroPrincipalScaleConstant ^ 2 / a +
            2 * (384 * Real.sqrt 42 * Real.pi * nearProfileDecayConstant) ^ 2 / a)) := by
        simpa only [F] using!
          tsum_norm_sq_fourierCoeff_smoothNearPrimitivePoleTailL2_int_le_split
            a ε U M T S ha hε haε hεhalf hUfour hM hMT hTS
              hinitialTop hprincipalBase hinitialU hprincipalUpper
              hinterLower hinterUpper hhigh
  · exact L2.integrable_inner F F

/-- Fully parameter-eliminated zero-carrier estimate.  The only scale
assumption is the eventual room condition `16 < a (U-1)²`.  All three
frequency cutoffs are selected internally, and their combined cardinality
is bounded by `2 clog₂ U`. -/
theorem norm_sq_smoothNearPrimitivePoleTailL2_le_explicit
    (a ε : ℝ) (U : ℕ)
    (ha : 0 < a) (hε : 0 < ε) (haε : a ≤ ε / 4)
    (hεhalf : ε < 1 / 2) (hUfour : 4 ≤ U)
    (hroom : 16 < a * (((U - 1 : ℕ) : ℝ) ^ 2)) :
    ‖smoothNearPrimitivePoleTailL2 a ε 2 U ha haε‖ ^ 2 ≤
      2 * (nearZeroFrequencyOneConstant ^ 2 +
        (4 * nearZeroTinyFrequencyConstant ^ 2 +
          32 * nearZeroInitialFrequencyConstant ^ 2 / a +
          ((2 * Nat.clog 2 U : ℕ) : ℝ) *
            nearZeroPrincipalScaleConstant ^ 2 / a +
          2 * (384 * Real.sqrt 42 * Real.pi * nearProfileDecayConstant) ^ 2 / a)) := by
  have haHalf : a ≤ 1 / 2 := by linarith
  obtain ⟨M, T, S, hM, hMT, hTS, hinitialTop, hprincipalBase,
      hinitialU, hlower, hinterLower, hinterUpper, hhigh, hcard⟩ :=
    exists_nearZeroFrequencySplit a U ha haHalf hUfour hroom
  have hraw := norm_sq_smoothNearPrimitivePoleTailL2_le_split
    a ε U M T S ha hε haε hεhalf hUfour hM hMT hTS
      hinitialTop hprincipalBase hinitialU hlower hinterLower hinterUpper hhigh
  have hcardReal :
      ((Finset.card (Finset.Ico (M + 1) T) +
          Finset.card (Finset.Ico T S) : ℕ) : ℝ) ≤
        ((2 * Nat.clog 2 U : ℕ) : ℝ) := by
    exact_mod_cast hcard
  have hfactor : 0 ≤ nearZeroPrincipalScaleConstant ^ 2 / a := by positivity
  have hmerge :
      ((Finset.Ico (M + 1) T).card : ℝ) *
          nearZeroPrincipalScaleConstant ^ 2 / a +
        ((Finset.Ico T S).card : ℝ) *
          nearZeroPrincipalScaleConstant ^ 2 / a ≤
        ((2 * Nat.clog 2 U : ℕ) : ℝ) *
          nearZeroPrincipalScaleConstant ^ 2 / a := by
    calc
      ((Finset.Ico (M + 1) T).card : ℝ) *
            nearZeroPrincipalScaleConstant ^ 2 / a +
          ((Finset.Ico T S).card : ℝ) *
            nearZeroPrincipalScaleConstant ^ 2 / a =
        (((Finset.Ico (M + 1) T).card +
            (Finset.Ico T S).card : ℕ) : ℝ) *
          (nearZeroPrincipalScaleConstant ^ 2 / a) := by
            push_cast
            ring
      _ ≤ ((2 * Nat.clog 2 U : ℕ) : ℝ) *
          (nearZeroPrincipalScaleConstant ^ 2 / a) :=
        mul_le_mul_of_nonneg_right hcardReal hfactor
      _ = ((2 * Nat.clog 2 U : ℕ) : ℝ) *
          nearZeroPrincipalScaleConstant ^ 2 / a := by ring
  refine hraw.trans ?_
  have hinner :
      4 * nearZeroTinyFrequencyConstant ^ 2 +
          32 * nearZeroInitialFrequencyConstant ^ 2 / a +
          ((Finset.Ico (M + 1) T).card : ℝ) *
            nearZeroPrincipalScaleConstant ^ 2 / a +
          ((Finset.Ico T S).card : ℝ) *
            nearZeroPrincipalScaleConstant ^ 2 / a +
          2 * (384 * Real.sqrt 42 * Real.pi * nearProfileDecayConstant) ^ 2 / a ≤
        4 * nearZeroTinyFrequencyConstant ^ 2 +
          32 * nearZeroInitialFrequencyConstant ^ 2 / a +
          ((2 * Nat.clog 2 U : ℕ) : ℝ) *
            nearZeroPrincipalScaleConstant ^ 2 / a +
          2 * (384 * Real.sqrt 42 * Real.pi * nearProfileDecayConstant) ^ 2 / a := by
    linarith
  exact mul_le_mul_of_nonneg_left (add_le_add le_rfl hinner) (by norm_num)

/-! ## The manuscript scaling `a=A/L`, `U=N` -/

def nearZeroFixedEnergyConstant : ℝ :=
  nearZeroFrequencyOneConstant ^ 2 +
    4 * nearZeroTinyFrequencyConstant ^ 2

theorem nearZeroFixedEnergyConstant_nonneg :
    0 ≤ nearZeroFixedEnergyConstant := by
  unfold nearZeroFixedEnergyConstant
  positivity

def nearZeroReciprocalEnergyConstant : ℝ :=
  32 * nearZeroInitialFrequencyConstant ^ 2 +
    2 * (384 * Real.sqrt 42 * Real.pi * nearProfileDecayConstant) ^ 2

theorem nearZeroReciprocalEnergyConstant_nonneg :
    0 ≤ nearZeroReciprocalEnergyConstant := by
  unfold nearZeroReciprocalEnergyConstant
  positivity

/-- Elementary comparison between the dyadic ceiling and the natural
logarithm. -/
theorem nat_clog_two_cast_le_log_div_add_one
    (N : ℕ) (hN : 1 ≤ N) :
    (Nat.clog 2 N : ℝ) ≤
      Real.log (N : ℝ) / Real.log 2 + 1 := by
  have hNReal : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hlogN : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg hNReal
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogb : 0 ≤ Real.logb 2 (N : ℝ) := by
    unfold Real.logb
    exact div_nonneg hlogN hlogTwo.le
  have hceil := Nat.ceil_lt_add_one hlogb
  have hceilEq : ⌈Real.logb (2 : ℝ) (N : ℝ)⌉₊ = Nat.clog 2 N :=
    Real.natCeil_logb_natCast 2 N
  rw [hceilEq] at hceil
  unfold Real.logb at hceil
  exact hceil.le

/-- Quantitative zero-carrier estimate in the exact scaling of the paper.
After division by `L²`, the only nonvanishing term is an explicit constant
times `1/A`; every other displayed term tends to zero already for fixed
`A`. -/
theorem norm_sq_smoothNearPrimitivePoleTailL2_div_log_sq_le
    (A L ε : ℝ) (N : ℕ)
    (hA : 0 < A) (hL : 0 < L) (hε : 0 < ε)
    (haε : A / L ≤ ε / 4) (hεhalf : ε < 1 / 2)
    (hNfour : 4 ≤ N) (hNL : Real.exp L = (N : ℝ))
    (hroom : 16 < (A / L) * (((N - 1 : ℕ) : ℝ) ^ 2)) :
    ‖smoothNearPrimitivePoleTailL2 (A / L) ε 2 N
        (div_pos hA hL) haε‖ ^ 2 / L ^ 2 ≤
      2 * nearZeroFixedEnergyConstant / L ^ 2 +
        2 * nearZeroReciprocalEnergyConstant / (A * L) +
        4 * nearZeroPrincipalScaleConstant ^ 2 / (A * Real.log 2) +
        4 * nearZeroPrincipalScaleConstant ^ 2 / (A * L) := by
  have hraw := norm_sq_smoothNearPrimitivePoleTailL2_le_explicit
    (A / L) ε N (div_pos hA hL) hε haε hεhalf hNfour hroom
  have hlogEq : Real.log (N : ℝ) = L := by
    rw [← hNL, Real.log_exp]
  have hclog := nat_clog_two_cast_le_log_div_add_one N (by omega)
  rw [hlogEq] at hclog
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hclogNonneg : 0 ≤ (Nat.clog 2 N : ℝ) := by positivity
  have hprincipalNonneg : 0 ≤ nearZeroPrincipalScaleConstant ^ 2 := sq_nonneg _
  have hscale : 0 ≤ L / A := (div_pos hL hA).le
  have hcarrier :
      ((2 * Nat.clog 2 N : ℕ) : ℝ) *
          nearZeroPrincipalScaleConstant ^ 2 * (L / A) ≤
        (2 * (L / Real.log 2 + 1)) *
          nearZeroPrincipalScaleConstant ^ 2 * (L / A) := by
    have htwoClog :
        (((2 * Nat.clog 2 N : ℕ) : ℝ)) ≤
          2 * (L / Real.log 2 + 1) := by
      norm_num at hclog ⊢
      linarith
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right htwoClog hprincipalNonneg) hscale
  have hrawRewrite :
      2 * (nearZeroFrequencyOneConstant ^ 2 +
        (4 * nearZeroTinyFrequencyConstant ^ 2 +
          32 * nearZeroInitialFrequencyConstant ^ 2 / (A / L) +
          ((2 * Nat.clog 2 N : ℕ) : ℝ) *
            nearZeroPrincipalScaleConstant ^ 2 / (A / L) +
          2 * (384 * Real.sqrt 42 * Real.pi * nearProfileDecayConstant) ^ 2 /
            (A / L))) =
        2 * (nearZeroFixedEnergyConstant +
          nearZeroReciprocalEnergyConstant * (L / A) +
          ((2 * Nat.clog 2 N : ℕ) : ℝ) *
            nearZeroPrincipalScaleConstant ^ 2 * (L / A)) := by
    unfold nearZeroFixedEnergyConstant nearZeroReciprocalEnergyConstant
    field_simp [hA.ne', hL.ne']
    ring
  rw [hrawRewrite] at hraw
  have hraw' :
      ‖smoothNearPrimitivePoleTailL2 (A / L) ε 2 N
          (div_pos hA hL) haε‖ ^ 2 ≤
        2 * (nearZeroFixedEnergyConstant +
          nearZeroReciprocalEnergyConstant * (L / A) +
          (2 * (L / Real.log 2 + 1)) *
            nearZeroPrincipalScaleConstant ^ 2 * (L / A)) := by
    exact hraw.trans (mul_le_mul_of_nonneg_left
      (add_le_add le_rfl hcarrier) (by norm_num))
  apply (div_le_iff₀ (sq_pos_of_pos hL)).2
  calc
    ‖smoothNearPrimitivePoleTailL2 (A / L) ε 2 N
        (div_pos hA hL) haε‖ ^ 2 ≤
      2 * (nearZeroFixedEnergyConstant +
        nearZeroReciprocalEnergyConstant * (L / A) +
        (2 * (L / Real.log 2 + 1)) *
          nearZeroPrincipalScaleConstant ^ 2 * (L / A)) := hraw'
    _ = (2 * nearZeroFixedEnergyConstant / L ^ 2 +
          2 * nearZeroReciprocalEnergyConstant / (A * L) +
          4 * nearZeroPrincipalScaleConstant ^ 2 / (A * Real.log 2) +
          4 * nearZeroPrincipalScaleConstant ^ 2 / (A * L)) * L ^ 2 := by
      field_simp [hA.ne', hL.ne', hlogTwo.ne']
      ring

end

end Erdos1002
