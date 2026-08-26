import ErdosProblems.Erdos1002.NearResonantZeroCarrierGlobal

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# The zero-carrier intermediate frequency range

For frequencies `K` with `U^2 ≤ K < U^2 / a`, the square-root split used
for lower frequencies is unavailable (`sqrt K` has already passed the
denominator cutoff `U`), while the small-multiplier high-frequency estimate
has not yet started (`U^2 ≤ a K` need not hold).  This module closes that
otherwise missing range.  We stop the low-denominator Abel sum directly at
`U`; the unconditional partial-sum estimate below `sqrt K` applies because
`U^2 ≤ K`.
-/

open MeasureTheory Set Finset
open scoped BigOperators ComplexConjugate ENNReal

namespace Erdos1002

noncomputable section

/-- Join the low geometric denominator shells at the principal endpoint
`Q = 2^(R+1)` directly to the finite low-range tail ending at `U`. -/
theorem norm_finiteNearRamanujanMultiplierVector_le_lowShells_add_lowRangeTail
    (a ε : ℝ) (K R U : ℕ)
    (ha : 0 < a) (hε : 0 < ε) (haε : a ≤ ε / 4)
    (hεhalf : ε < 1 / 2) (hK : 0 < K)
    (hband : ((2 ^ (R + 1) : ℕ) : ℝ) ^ 2 ≤ a * (K : ℝ))
    (hQU : 2 ^ (R + 1) < U) (hUK : U ^ 2 ≤ K) :
    ‖finiteNearRamanujanMultiplierVector a ε K 3 U‖ ≤
      192 * Real.sqrt 42 * Real.pi * nearProfileDecayConstant *
          ((2 ^ (R + 1) : ℕ) : ℝ) /
            (a * Real.sqrt (K : ℝ)) +
        (2 * Real.sqrt 42 * Real.sqrt (K : ℝ) /
            ((2 ^ (R + 1) : ℕ) : ℝ)) *
          (64 * Real.pi * nearProfileDecayConstant) := by
  let Q : ℕ := 2 ^ (R + 1)
  have hQpos : 0 < Q := by
    dsimp [Q]
    positivity
  have hQtwo : 2 ≤ Q := by
    dsimp [Q]
    have hone : 1 ≤ 2 ^ R := Nat.one_le_two_pow
    rw [pow_succ]
    omega
  have hQU' : Q ≤ U := (by simpa only [Q] using! hQU.le)
  have hsplit := finiteNearRamanujanMultiplierVector_split_at
    a ε K Q U hQtwo hQU'
  have hlow :
      ‖finiteNearRamanujanMultiplierVector a ε K 3 Q‖ ≤
        192 * Real.sqrt 42 * Real.pi * nearProfileDecayConstant *
          (Q : ℝ) / (a * Real.sqrt (K : ℝ)) := by
    rw [← nearZeroLowDyadicVector_eq_interval a ε K R]
    simpa only [Q] using! norm_nearZeroLowDyadicVector_le
      a ε K R ha hε haε hεhalf hK hband
  have htail := norm_finiteNearRamanujanMultiplierVector_tail_le_lowRange
    a ε K Q U ha hε haε hK hQpos (by simpa only [Q] using! hQU) hUK
  rw [hsplit]
  exact (norm_add_le _ _).trans (add_le_add hlow (by
    simpa only [Q] using! htail))

/-- Physical-space version of the preceding endpoint-tail decomposition. -/
theorem norm_smoothNearPrimitivePoleTailDyadicProjection_two_le_intermediateRaw
    (a ε : ℝ) (K R U : ℕ)
    (ha : 0 < a) (hε : 0 < ε) (haε : a ≤ ε / 4)
    (hεhalf : ε < 1 / 2) (hK : 0 < K)
    (hband : ((2 ^ (R + 1) : ℕ) : ℝ) ^ 2 ≤ a * (K : ℝ))
    (hQU : 2 ^ (R + 1) < U) (hUK : U ^ 2 ≤ K) :
    ‖smoothNearPrimitivePoleTailDyadicProjection a ε K 2 U ha haε‖ ≤
      192 * Real.sqrt 42 * Real.pi * nearProfileDecayConstant *
          ((2 ^ (R + 1) : ℕ) : ℝ) /
            (a * Real.sqrt (K : ℝ)) +
        (2 * Real.sqrt 42 * Real.sqrt (K : ℝ) /
            ((2 ^ (R + 1) : ℕ) : ℝ)) *
          (64 * Real.pi * nearProfileDecayConstant) := by
  rw [norm_smoothNearPrimitivePoleTailDyadicProjection_eq_vector
    a ε K 2 U (by norm_num) ha hε haε hεhalf.le]
  exact norm_finiteNearRamanujanMultiplierVector_le_lowShells_add_lowRangeTail
    a ε K R U ha hε haε hεhalf hK hband hQU hUK

/-- The missing intermediate block has the same `O(a^{-1/2})` norm as a
principal block.  The upper bracketing inequality is essential for the
second term; no assumption that `sqrt K < U` occurs. -/
theorem norm_smoothNearPrimitivePoleTailDyadicProjection_two_le_intermediate
    (a ε : ℝ) (K R U : ℕ)
    (ha : 0 < a) (hε : 0 < ε) (haε : a ≤ ε / 4)
    (hεhalf : ε < 1 / 2) (hK : 0 < K)
    (hband : ((2 ^ (R + 1) : ℕ) : ℝ) ^ 2 ≤ a * (K : ℝ))
    (hnext : a * (K : ℝ) ≤
      (2 * ((2 ^ (R + 1) : ℕ) : ℝ)) ^ 2)
    (hQU : 2 ^ (R + 1) < U) (hUK : U ^ 2 ≤ K) :
    ‖smoothNearPrimitivePoleTailDyadicProjection a ε K 2 U ha haε‖ ≤
      nearZeroPrincipalScaleConstant / Real.sqrt a := by
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
          (1 / Real.sqrt a) :=
        mul_le_mul_of_nonneg_left hlowScalar (by positivity)
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
          (64 * Real.pi * nearProfileDecayConstant) := by gcongr
      _ = (4 * Real.sqrt 42 / Real.sqrt a) *
          (64 * Real.pi * nearProfileDecayConstant) := by ring
  have hraw :=
    norm_smoothNearPrimitivePoleTailDyadicProjection_two_le_intermediateRaw
      a ε K R U ha hε haε hεhalf hK hband hQU hUK
  have hsqrta : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
  let D : ℝ := (16 * Real.sqrt 54 + 64 * Real.sqrt 42) * Real.pi *
    nearProfileDecayConstant
  have hD : 0 ≤ D := by
    dsimp [D]
    positivity
  calc
    ‖smoothNearPrimitivePoleTailDyadicProjection a ε K 2 U ha haε‖ ≤
        192 * Real.sqrt 42 * Real.pi * nearProfileDecayConstant * Qr /
            (a * Real.sqrt (K : ℝ)) +
          (2 * Real.sqrt 42 * Real.sqrt (K : ℝ) / Qr) *
            (64 * Real.pi * nearProfileDecayConstant) := by
      simpa only [Qr] using! hraw
    _ ≤ 192 * Real.sqrt 42 * Real.pi * nearProfileDecayConstant /
          Real.sqrt a +
        (4 * Real.sqrt 42 / Real.sqrt a) *
          (64 * Real.pi * nearProfileDecayConstant) := add_le_add hlow htail
    _ ≤ 192 * Real.sqrt 42 * Real.pi * nearProfileDecayConstant /
          Real.sqrt a +
        (4 * Real.sqrt 42 / Real.sqrt a) *
          (64 * Real.pi * nearProfileDecayConstant) + D / Real.sqrt a := by
      exact le_add_of_nonneg_right (div_nonneg hD hsqrta.le)
    _ = nearZeroPrincipalScaleConstant / Real.sqrt a := by
      unfold nearZeroPrincipalScaleConstant
      dsimp [D]
      field_simp [hsqrta.ne']

/-- Parameter-eliminated intermediate-block estimate. -/
theorem norm_smoothNearPrimitivePoleTailDyadicProjection_two_le_intermediate_of_large
    (a ε : ℝ) (K U : ℕ)
    (ha : 0 < a) (hε : 0 < ε) (haε : a ≤ ε / 4)
    (hεhalf : ε < 1 / 2) (hK : 0 < K)
    (hlarge : 16 ≤ a * (K : ℝ))
    (hUK : U ^ 2 ≤ K)
    (hendpoint : ∀ R : ℕ,
      ((2 ^ (R + 1) : ℕ) : ℝ) ^ 2 ≤ a * (K : ℝ) →
        2 ^ (R + 1) < U) :
    ‖smoothNearPrimitivePoleTailDyadicProjection a ε K 2 U ha haε‖ ≤
      nearZeroPrincipalScaleConstant / Real.sqrt a := by
  obtain ⟨R, hband, hnext⟩ :=
    exists_nearZeroPrincipalExponent a K ha hK hlarge
  exact norm_smoothNearPrimitivePoleTailDyadicProjection_two_le_intermediate
    a ε K R U ha hε haε hεhalf hK hband hnext
      (hendpoint R hband) hUK

end

end Erdos1002
