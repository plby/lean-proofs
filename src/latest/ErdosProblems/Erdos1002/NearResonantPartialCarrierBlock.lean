import ErdosProblems.Erdos1002.NearResonantInfiniteCarrierBounds

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Partial terminal denominator blocks for shifted near carriers

The global dyadic split ends at the largest power of two below `N`.  This
file treats the literal remaining interval up to `N`.  The proof repeats the
reduced-rational packing argument on an arbitrary subinterval of one dyadic
block, so no artificial power-of-two endpoint is inserted into the physical
shot sum.
-/

open Filter MeasureTheory Set Finset
open scoped BigOperators ENNReal Real Topology

namespace Erdos1002

noncomputable section

/-- An arbitrary denominator subinterval inside `(P/2,P]` has at most four
simultaneously active reduced-rational cells. -/
theorem norm_sq_smoothNearPrimitivePoleCarrierTail_partial_le_four_mul_sum
    (N P Q U : ℕ) (ell : ℤ) (a ε alpha : ℝ)
    (hP : 4 ≤ P) (hQ : P / 2 ≤ Q) (hU : U ≤ P)
    (ha : 0 < a) (hε : 0 < ε) (haε : a ≤ ε / 4)
    (hεhalf : ε < 1 / 2) (halpha : alpha ∈ Ioo (0 : ℝ) 1) :
    ‖smoothNearPrimitivePoleCarrierTail N ell a ε Q U alpha‖ ^ 2 ≤
      4 * ∑ p ∈ Finset.Ioc Q U,
        ‖smoothNearPrimitivePoleCarrierTerm N ell a ε p alpha‖ ^ 2 := by
  let s := Finset.Ioc Q U
  let u := s.filter fun p ↦ smoothNearPrimitivePoleSum a ε p alpha ≠ 0
  let f : ℕ → ℂ := fun p ↦
    smoothNearPrimitivePoleCarrierTerm N ell a ε p alpha
  have hus : u ⊆ nearActiveDenominators a ε P alpha := by
    intro p hp
    have hp' := Finset.mem_filter.mp hp
    have hpBounds := Finset.mem_Ioc.mp hp'.1
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_Ioc.mpr
      exact ⟨lt_of_le_of_lt hQ hpBounds.1, hpBounds.2.trans hU⟩
    · exact hp'.2
  have hcard : u.card ≤ 4 :=
    (Finset.card_le_card hus).trans
      (card_nearActiveDenominators_le_four
        a ε alpha P hP ha hε haε hεhalf halpha)
  have hsum : (∑ p ∈ s, f p) = ∑ p ∈ u, f p := by
    dsimp [u]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro p hpMem
    by_cases hpActive : smoothNearPrimitivePoleSum a ε p alpha ≠ 0
    · simp [hpActive]
    · have hpZero : smoothNearPrimitivePoleSum a ε p alpha = 0 :=
        not_ne_iff.mp hpActive
      simp [f, smoothNearPrimitivePoleCarrierTerm, unitModulate, hpZero]
  have hnorm : ‖∑ p ∈ u, f p‖ ≤ ∑ p ∈ u, ‖f p‖ :=
    norm_sum_le _ _
  have hcs : ‖∑ p ∈ u, f p‖ ^ 2 ≤
      (u.card : ℝ) * ∑ p ∈ u, ‖f p‖ ^ 2 := by
    exact (pow_le_pow_left₀ (norm_nonneg _) hnorm 2).trans
      sq_sum_le_card_mul_sum_sq
  have hcardReal : (u.card : ℝ) ≤ 4 := by exact_mod_cast hcard
  have husTarget : u ⊆ s := Finset.filter_subset _ _
  have hsumNorm : (∑ p ∈ u, ‖f p‖ ^ 2) ≤
      ∑ p ∈ s, ‖f p‖ ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg husTarget
      (fun _p _hp _hnot ↦ sq_nonneg _)
  unfold smoothNearPrimitivePoleCarrierTail
  change ‖∑ p ∈ s, f p‖ ^ 2 ≤ 4 * ∑ p ∈ s, ‖f p‖ ^ 2
  rw [hsum]
  exact hcs.trans (mul_le_mul hcardReal hsumNorm (by positivity) (by positivity))

/-- Integrated packing estimate for a literal partial terminal block. -/
theorem integral_unit_norm_sq_smoothNearPrimitivePoleCarrierTail_partial_le
    (N P Q U : ℕ) (ell : ℤ) (a ε : ℝ)
    (hP : 4 ≤ P) (hQ : P / 2 ≤ Q) (hU : U ≤ P)
    (ha : 0 < a) (hε : 0 < ε) (haε : a ≤ ε / 4)
    (hεhalf : ε < 1 / 2) :
    (∫ alpha in (0 : ℝ)..1,
        ‖smoothNearPrimitivePoleCarrierTail N ell a ε Q U alpha‖ ^ 2) ≤
      4 * ∑ p ∈ Finset.Ioc Q U,
        ∫ alpha in (0 : ℝ)..1,
          ‖smoothNearPrimitivePoleCarrierTerm N ell a ε p alpha‖ ^ 2 := by
  let f : ℝ → ℝ := fun alpha ↦
    ‖smoothNearPrimitivePoleCarrierTail N ell a ε Q U alpha‖ ^ 2
  let g : ℝ → ℝ := fun alpha ↦
    4 * ∑ p ∈ Finset.Ioc Q U,
      ‖smoothNearPrimitivePoleCarrierTerm N ell a ε p alpha‖ ^ 2
  have hfCont : Continuous f :=
    (smoothNearPrimitivePoleCarrierTail_continuous
      N Q U ell a ε ha haε).norm.pow 2
  have hgCont : Continuous g := by
    dsimp [g]
    apply continuous_const.mul
    apply continuous_finset_sum
    intro p _hp
    exact (smoothNearPrimitivePoleCarrierTerm_continuous
      N p ell a ε ha haε).norm.pow 2
  have hpoint : f ≤ᵐ[volume.restrict (Icc (0 : ℝ) 1)] g := by
    rw [← Measure.restrict_congr_set Ioo_ae_eq_Icc]
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with alpha halpha
    exact norm_sq_smoothNearPrimitivePoleCarrierTail_partial_le_four_mul_sum
      N P Q U ell a ε alpha hP hQ hU ha hε haε hεhalf halpha
  have hmono := intervalIntegral.integral_mono_ae_restrict
    (show (0 : ℝ) ≤ 1 by norm_num)
    (hfCont.intervalIntegrable 0 1) (hgCont.intervalIntegrable 0 1) hpoint
  change (∫ alpha in (0 : ℝ)..1, f alpha) ≤ _
  calc
    (∫ alpha in (0 : ℝ)..1, f alpha) ≤
        ∫ alpha in (0 : ℝ)..1, g alpha := hmono
    _ = 4 * ∑ p ∈ Finset.Ioc Q U,
        ∫ alpha in (0 : ℝ)..1,
          ‖smoothNearPrimitivePoleCarrierTerm N ell a ε p alpha‖ ^ 2 := by
      dsimp [g]
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_finset_sum]
      intro p _hp
      exact ((smoothNearPrimitivePoleCarrierTerm_continuous
        N p ell a ε ha haε).norm.pow 2).intervalIntegrable 0 1

/-- Scalar `O(a⁻¹)` energy bound for any partial interval inside one
dyadic denominator block. -/
theorem integral_unit_norm_sq_smoothNearPrimitivePoleCarrierTail_partial_le_scalar
    (N P Q U : ℕ) (ell : ℤ) (a ε : ℝ)
    (hP : 4 ≤ P) (hQ : P / 2 ≤ Q) (hU : U ≤ P)
    (ha : 0 < a) (hε : 0 < ε) (haε : a ≤ ε / 4)
    (hεhalf : ε < 1 / 2) :
    (∫ alpha in (0 : ℝ)..1,
        ‖smoothNearPrimitivePoleCarrierTail N ell a ε Q U alpha‖ ^ 2) ≤
      8 * ‖bernoulliMarkFourierCoefficient ell‖ ^ 2 *
        ((2 * nearGevreyProfileConstant) ^ 2 * (32 / a)) := by
  let G : ℝ := (2 * nearGevreyProfileConstant) ^ 2 * (32 / a)
  have hG : 0 ≤ G := by dsimp [G]; positivity
  have hpacking :=
    integral_unit_norm_sq_smoothNearPrimitivePoleCarrierTail_partial_le
      N P Q U ell a ε hP hQ hU ha hε haε hεhalf
  have hterm : ∀ p ∈ Finset.Ioc Q U,
      (∫ alpha in (0 : ℝ)..1,
        ‖smoothNearPrimitivePoleCarrierTerm N ell a ε p alpha‖ ^ 2) ≤
      ‖bernoulliMarkFourierCoefficient ell‖ ^ 2 *
        ((Nat.totient p : ℝ) * (1 / (p : ℝ) ^ 2) * G) := by
    intro p hp
    have hpBounds := Finset.mem_Ioc.mp hp
    have hpTwo : 2 ≤ p := by
      have hhalf : 2 ≤ P / 2 :=
        (Nat.le_div_iff_mul_le (by omega : 0 < 2)).2 (by omega)
      omega
    have hmass :=
      integral_unit_norm_iteratedDeriv_smoothNearPrimitivePoleSum_sq_le_gevrey
        0 p a ε hpTwo ha hε haε hεhalf
    have hcarrier :
        (∫ alpha in (0 : ℝ)..1,
          ‖smoothNearPrimitivePoleCarrierTerm N ell a ε p alpha‖ ^ 2) =
        ‖bernoulliMarkFourierCoefficient ell‖ ^ 2 *
          (∫ alpha in (0 : ℝ)..1,
            ‖smoothNearPrimitivePoleSum a ε p alpha‖ ^ 2) := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro alpha _halpha
      exact norm_sq_smoothNearPrimitivePoleCarrierTerm N p ell a ε alpha
    rw [hcarrier]
    have hzeroDeriv : iteratedDeriv 0
        (smoothNearPrimitivePoleSum a ε p) =
        smoothNearPrimitivePoleSum a ε p := by
      simp
    rw [hzeroDeriv] at hmass
    have hmass' :
        (∫ alpha in (0 : ℝ)..1,
          ‖smoothNearPrimitivePoleSum a ε p alpha‖ ^ 2) ≤
        (Nat.totient p : ℝ) * (1 / (p : ℝ) ^ 2) * G := by
      simpa [G] using! hmass
    exact mul_le_mul_of_nonneg_left hmass' (sq_nonneg _)
  have hsubset : Finset.Ioc Q U ⊆ Finset.Ioc (P / 2) P := by
    intro p hp
    have hp' := Finset.mem_Ioc.mp hp
    exact Finset.mem_Ioc.mpr ⟨lt_of_le_of_lt hQ hp'.1, hp'.2.trans hU⟩
  have htot :
      (∑ p ∈ Finset.Ioc Q U,
        (Nat.totient p : ℝ) * (1 / (p : ℝ) ^ 2)) ≤ 2 := by
    exact (Finset.sum_le_sum_of_subset_of_nonneg hsubset
      (fun _p _hp _hnot ↦ by positivity)).trans
        (sum_totient_mul_inv_sq_Ioc_half_le_two P (by omega))
  calc
    (∫ alpha in (0 : ℝ)..1,
        ‖smoothNearPrimitivePoleCarrierTail N ell a ε Q U alpha‖ ^ 2) ≤
        4 * ∑ p ∈ Finset.Ioc Q U,
          ∫ alpha in (0 : ℝ)..1,
            ‖smoothNearPrimitivePoleCarrierTerm N ell a ε p alpha‖ ^ 2 :=
      hpacking
    _ ≤ 4 * ∑ p ∈ Finset.Ioc Q U,
        ‖bernoulliMarkFourierCoefficient ell‖ ^ 2 *
          ((Nat.totient p : ℝ) * (1 / (p : ℝ) ^ 2) * G) := by
      gcongr with p hp
      exact hterm p hp
    _ = 4 * (‖bernoulliMarkFourierCoefficient ell‖ ^ 2 * G) *
        (∑ p ∈ Finset.Ioc Q U,
          (Nat.totient p : ℝ) * (1 / (p : ℝ) ^ 2)) := by
      rw [mul_assoc]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _hp
      ring
    _ ≤ 4 * (‖bernoulliMarkFourierCoefficient ell‖ ^ 2 * G) * 2 :=
      mul_le_mul_of_nonneg_left htot (by positivity)
    _ = 8 * ‖bernoulliMarkFourierCoefficient ell‖ ^ 2 *
        ((2 * nearGevreyProfileConstant) ^ 2 * (32 / a)) := by
      dsimp [G]
      ring

def nearCarrierPartialCommonEnergyBound (a : ℝ) : ℝ :=
  8 * ((2 * nearGevreyProfileConstant) ^ 2 * (32 / a))

theorem nearCarrierPartialCommonEnergyBound_nonneg
    (a : ℝ) (ha : 0 < a) :
    0 ≤ nearCarrierPartialCommonEnergyBound a := by
  unfold nearCarrierPartialCommonEnergyBound
  positivity

/-- Real norm-squared form of the terminal partial-block estimate. -/
theorem norm_sq_smoothNearPrimitivePoleCarrierTailL2_partial_le
    (N P Q U : ℕ) (ell : ℤ) (a ε : ℝ)
    (hP : 4 ≤ P) (hQ : P / 2 ≤ Q) (hU : U ≤ P)
    (ha : 0 < a) (hε : 0 < ε) (haε : a ≤ ε / 4)
    (hεhalf : ε < 1 / 2) :
    ‖smoothNearPrimitivePoleCarrierTailL2 N ell a ε Q U ha haε‖ ^ 2 ≤
      ‖bernoulliMarkFourierCoefficient ell‖ ^ 2 *
        nearCarrierPartialCommonEnergyBound a := by
  rw [norm_sq_smoothNearPrimitivePoleCarrierTailL2]
  refine (integral_unit_norm_sq_smoothNearPrimitivePoleCarrierTail_partial_le_scalar
    N P Q U ell a ε hP hQ hU ha hε haε hεhalf).trans_eq ?_
  unfold nearCarrierPartialCommonEnergyBound
  ring

/-- The literal terminal partial block after summing all nonzero Bernoulli
carriers in circle `L²`. -/
theorem norm_smoothNearInfiniteNonzeroCarrierL2_partial_le
    (N P Q U : ℕ) (a ε : ℝ)
    (hP : 4 ≤ P) (hQ : P / 2 ≤ Q) (hU : U ≤ P)
    (ha : 0 < a) (hε : 0 < ε) (haε : a ≤ ε / 4)
    (hεhalf : ε < 1 / 2) :
    ‖smoothNearInfiniteNonzeroCarrierL2 N a ε Q U ha haε‖ ≤
      windowCarrierMassConstant *
        Real.sqrt (nearCarrierPartialCommonEnergyBound a) := by
  apply norm_smoothNearInfiniteNonzeroCarrierL2_le
    N a ε Q U ha haε
    (nearCarrierPartialCommonEnergyBound_nonneg a ha)
  intro ell
  exact norm_sq_smoothNearPrimitivePoleCarrierTailL2_partial_le
    N P Q U (ell : ℤ) a ε hP hQ hU ha hε haε hεhalf

theorem summable_smoothNearNonzeroCarrierL2Term_partial
    (N P Q U : ℕ) (a ε : ℝ)
    (hP : 4 ≤ P) (hQ : P / 2 ≤ Q) (hU : U ≤ P)
    (ha : 0 < a) (hε : 0 < ε) (haε : a ≤ ε / 4)
    (hεhalf : ε < 1 / 2) :
    Summable (smoothNearNonzeroCarrierL2Term N a ε Q U ha haε) := by
  apply summable_smoothNearNonzeroCarrierL2Term
    N a ε Q U ha haε
    (nearCarrierPartialCommonEnergyBound_nonneg a ha)
  intro ell
  exact norm_sq_smoothNearPrimitivePoleCarrierTailL2_partial_le
    N P Q U (ell : ℤ) a ε hP hQ hU ha hε haε hεhalf

end

end Erdos1002
