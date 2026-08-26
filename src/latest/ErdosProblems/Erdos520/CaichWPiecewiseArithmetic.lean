import ErdosProblems.Erdos520.CaichWPiecewise
import ErdosProblems.Erdos520.CaichWSmallPrimeGeometry
import ErdosProblems.Erdos520.CaichWScalarAlgebra
import ErdosProblems.Erdos520.CaichWPrimeSums
import ErdosProblems.Erdos520.CaichWScalar
import ErdosProblems.Erdos520.ThinScheduleChebyshev

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Filter Finset MeasureTheory Set
open scoped BigOperators ENNReal Interval Topology

namespace Erdos
namespace Problem520

/-!
# Arithmetic estimate for the floor-safe piecewise `W` budget

This file closes the many-atom estimate and then sums the two branches.  In
the many-atom range the support cardinality supplies the indispensable
factor `X^(-1/(2r))`; in the single-atom range the pointwise bound from
`CaichWPointwise` is summed using Chebyshev's prime-counting theorem.
-/

/-- Once the nominal smoothing power is at least two, its natural floor is
at least half of it. -/
theorem caichWSmoothingParameter_half_le_natCast
    {r x : ℕ} (hW : 2 ≤ caichWSmoothingParameter r x) :
    caichWSmoothingParameter r x / 2 ≤
      caichWSmoothingParameterNatCast r x := by
  have hfloor := Nat.lt_floor_add_one (caichWSmoothingParameter r x)
  have hhalf : caichWSmoothingParameter r x / 2 ≤
      caichWSmoothingParameter r x - 1 := by
    linarith
  have hlt : caichWSmoothingParameter r x / 2 <
      (Nat.floor (caichWSmoothingParameter r x) : ℝ) := by
    linarith
  have hmax : Nat.floor (caichWSmoothingParameter r x) ≤
      caichWSmoothingParameterNat r x := by
    unfold caichWSmoothingParameterNat
    exact le_max_right _ _
  unfold caichWSmoothingParameterNatCast
  exact hlt.le.trans (by exact_mod_cast hmax)

theorem two_le_caichWSmoothingParameter
    {r x : ℕ} (hlog : 2 ≤ Real.log (x : ℝ)) :
    2 ≤ caichWSmoothingParameter r x := by
  unfold caichWSmoothingParameter caichWSmoothingExponent
  have hexp : 1 ≤ 8 * r ^ 2 - 8 * r + 4 := by omega
  exact hlog.trans (le_self_pow₀ (one_le_two.trans hlog) (by omega))

/-- The exact short-section interpolation budget has the required
`1 / log(x)^2` saving in the many-atom range. -/
theorem caichWShortMomentRootBudget_le_div_sq_of_smallPrime
    {r X x p : ℕ} (hr : 1 ≤ r) (hXtwo : 2 ≤ X) (hp : 0 < p)
    (hsmall : p * (X + 1) ≤ x)
    (hlog : 2 ≤ Real.log (x : ℝ))
    (hXL : Real.log (x : ℝ) ^ caichWScalarSmoothingExponent r / 2 ≤
      (X : ℝ))
    {t : ℝ} (hpt : (p : ℝ) ≤ t)
    (htq : t ≤ (p : ℝ) * (1 + 1 / (X : ℝ))) :
    caichWShortMomentRootBudget r x p t ≤
      (caichWScalarConstant r * 2 ^ caichWCardExponent r) *
          ((x : ℝ) / (p : ℝ)) /
        Real.log (x : ℝ) ^ (2 : ℕ) := by
  let u : ℝ := (x : ℝ) / (p : ℝ)
  let L : ℝ := Real.log (x : ℝ)
  let C : ℝ := ((caichWShortSupport x p t).card : ℝ)
  let E : ℝ := caichWShortDivisorEnergy r x p t
  let C₀ : ℝ := 2 * u / (X : ℝ)
  let E₀ : ℝ := u * (2 * L) ^ (4 * r - 4)
  have hX : 0 < X := by omega
  have hXR : (0 : ℝ) < (X : ℝ) := by exact_mod_cast hX
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hx : 0 < x := by
    have : 0 < p * (X + 1) := Nat.mul_pos hp (by omega)
    omega
  have hu : 0 < u := by dsimp [u]; positivity
  have hL : 0 < L := by dsimp [L]; linarith
  have hxpLower : X + 1 ≤ x / p := by
    exact (Nat.le_div_iff_mul_le hp).2 (by
      simpa only [Nat.mul_comm] using! hsmall)
  have hxp : 3 ≤ x / p := by omega
  have hcardRaw := caichWShortSupport_card_cast_le_of_smallPrime
    hX hp hsmall hpt htq
  have hcard : C ≤ C₀ := by
    dsimp only [C, C₀, u]
    convert! hcardRaw using 1
    field_simp [hpR.ne', hXR.ne']
    <;> ring
  have henergyRaw := caichWShortDivisorEnergy_le_of_smallPrime
    hr hxp t
  have hdiv : ((x / p : ℕ) : ℝ) ≤ u := by
    dsimp only [u]
    exact Nat.cast_div_le
  have hlogFactor : 0 ≤ (2 * L) ^ (4 * r - 4) := by positivity
  have henergy : E ≤ E₀ := by
    calc
      E ≤ ((x / p : ℕ) : ℝ) *
          (2 * Real.log (x : ℝ)) ^ (4 * r - 4) := by
        simpa only [E] using! henergyRaw
      _ ≤ u * (2 * L) ^ (4 * r - 4) := by
        exact mul_le_mul_of_nonneg_right hdiv hlogFactor
      _ = E₀ := rfl
  have hE : 0 ≤ E := by
    unfold E caichWShortDivisorEnergy
    exact Finset.sum_nonneg fun n _hn ↦ by positivity
  have hpow : E ^ (2 * r - 1) ≤ E₀ ^ (2 * r - 1) :=
    pow_le_pow_left₀ hE henergy _
  have hbase :
      Real.sqrt C * Real.sqrt (E ^ (2 * r - 1)) ≤
        Real.sqrt C₀ * Real.sqrt (E₀ ^ (2 * r - 1)) := by
    exact mul_le_mul (Real.sqrt_le_sqrt hcard)
      (Real.sqrt_le_sqrt hpow) (Real.sqrt_nonneg _)
      (Real.sqrt_nonneg _)
  have hbaseNonneg :
      0 ≤ Real.sqrt C * Real.sqrt (E ^ (2 * r - 1)) := by positivity
  have hroot :
      (Real.sqrt C * Real.sqrt (E ^ (2 * r - 1))) ^
          (1 / (r : ℝ)) ≤
        (Real.sqrt C₀ * Real.sqrt (E₀ ^ (2 * r - 1))) ^
          (1 / (r : ℝ)) :=
    Real.rpow_le_rpow hbaseNonneg hbase (by positivity)
  have hscalar := caichW_raw_scalar_le_div_sq hr hu hXR hL hXL
  unfold caichWShortMomentRootBudget
  change (Real.sqrt C * Real.sqrt (E ^ (2 * r - 1))) ^
      (1 / (r : ℝ)) ≤ _
  exact hroot.trans (by
    simpa only [C₀, E₀, u, L] using! hscalar)

/-- Averaging the preceding uniform section bound over the interval of
length `p / X` leaves the same bound for one prime. -/
theorem caichWPrimeMomentRootBudget_le_div_sq_of_smallPrime
    {r X x p : ℕ} (hr : 1 ≤ r) (hXtwo : 2 ≤ X) (hp : p.Prime)
    (hsmall : p * (X + 1) ≤ x)
    (hlog : 2 ≤ Real.log (x : ℝ))
    (hXL : Real.log (x : ℝ) ^ caichWScalarSmoothingExponent r / 2 ≤
      (X : ℝ)) :
    caichWPrimeMomentRootBudget r (X : ℝ) x p ≤
      (caichWScalarConstant r * 2 ^ caichWCardExponent r) *
          ((x : ℝ) / (p : ℝ)) /
        Real.log (x : ℝ) ^ (2 : ℕ) := by
  let q : ℝ := (p : ℝ) * (1 + 1 / (X : ℝ))
  let B : ℝ :=
    (caichWScalarConstant r * 2 ^ caichWCardExponent r) *
        ((x : ℝ) / (p : ℝ)) /
      Real.log (x : ℝ) ^ (2 : ℕ)
  have hX : 0 < X := by omega
  have hXR : (0 : ℝ) < (X : ℝ) := by exact_mod_cast hX
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hpq : (p : ℝ) ≤ q := by
    dsimp only [q]
    have : 0 ≤ 1 / (X : ℝ) := by positivity
    nlinarith
  have hB : 0 ≤ B := by
    dsimp only [B]
    apply div_nonneg
    · exact mul_nonneg
        (mul_nonneg (caichWScalarConstant_pos r).le
          (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _))
        (div_nonneg (Nat.cast_nonneg x) (Nat.cast_nonneg p))
    · positivity
  have hbudgetInt : IntervalIntegrable
      (fun t ↦ caichWShortMomentRootBudget r x p t)
      volume (p : ℝ) q := by
    exact intervalIntegrable_caichWShortMomentRootBudget
      (by omega) x p (p : ℝ) q
  have hconstInt : IntervalIntegrable (fun _t : ℝ ↦ B)
      volume (p : ℝ) q := intervalIntegrable_const
  have hint :
      (∫ t in (p : ℝ)..q,
        caichWShortMomentRootBudget r x p t) ≤
      ∫ _t in (p : ℝ)..q, B := by
    apply intervalIntegral.integral_mono_on hpq hbudgetInt hconstInt
    intro t ht
    exact caichWShortMomentRootBudget_le_div_sq_of_smallPrime
      hr hXtwo hp.pos hsmall hlog hXL ht.1 ht.2
  unfold caichWPrimeMomentRootBudget
  change (X : ℝ) / (p : ℝ) *
      (∫ t in (p : ℝ)..q,
        caichWShortMomentRootBudget r x p t) ≤ B
  calc
    (X : ℝ) / (p : ℝ) *
        (∫ t in (p : ℝ)..q,
          caichWShortMomentRootBudget r x p t) ≤
      (X : ℝ) / (p : ℝ) * (∫ _t in (p : ℝ)..q, B) :=
        mul_le_mul_of_nonneg_left hint (by positivity)
    _ = B := by
      rw [intervalIntegral.integral_const]
      have hlength : q - (p : ℝ) = (p : ℝ) / (X : ℝ) := by
        dsimp only [q]
        field_simp [hXR.ne']
        ring
      rw [hlength]
      rw [div_eq_mul_inv, div_eq_mul_inv]
      calc
        (X : ℝ) * (p : ℝ)⁻¹ * ((p : ℝ) * (X : ℝ)⁻¹ * B) =
            ((p : ℝ)⁻¹ * (p : ℝ)) *
              ((X : ℝ) * (X : ℝ)⁻¹) * B := by ring
        _ = B := by
          rw [inv_mul_cancel₀ hpR.ne', mul_inv_cancel₀ hXR.ne']
          ring

/-- Specialization of the one-prime estimate to the common natural
smoothing parameter. -/
theorem caichWPrimeMomentRootBudget_le_div_sq_natSmoothing
    {r x p : ℕ} (hr : 1 ≤ r) (hp : p.Prime)
    (hsmall : p * (caichWSmoothingParameterNat r x + 1) ≤ x)
    (hlog : 2 ≤ Real.log (x : ℝ)) :
    caichWPrimeMomentRootBudget r
        (caichWSmoothingParameterNatCast r x) x p ≤
      (caichWScalarConstant r * 2 ^ caichWCardExponent r) *
          ((x : ℝ) / (p : ℝ)) /
        Real.log (x : ℝ) ^ (2 : ℕ) := by
  have hXtwo : 2 ≤ caichWSmoothingParameterNat r x :=
    by
      have hWtwo : 2 ≤ caichWSmoothingParameter r x :=
        two_le_caichWSmoothingParameter hlog
      have hfloor : 2 ≤ Nat.floor (caichWSmoothingParameter r x) :=
        Nat.le_floor hWtwo
      unfold caichWSmoothingParameterNat
      omega
  have hWtwo : 2 ≤ caichWSmoothingParameter r x :=
    two_le_caichWSmoothingParameter hlog
  have hXL :
      Real.log (x : ℝ) ^ caichWScalarSmoothingExponent r / 2 ≤
        (caichWSmoothingParameterNat r x : ℝ) := by
    simpa only [caichWSmoothingParameter,
      caichWSmoothingExponent, caichWScalarSmoothingExponent,
      caichWSmoothingParameterNatCast] using!
        (caichWSmoothingParameter_half_le_natCast hWtwo)
  simpa only [caichWSmoothingParameterNatCast] using!
    caichWPrimeMomentRootBudget_le_div_sq_of_smallPrime
      hr hXtwo hp hsmall hlog hXL

/-! ## Summing the two prime ranges -/

/-- The two branches sum to a harmonic reciprocal-prime term plus the
number of primes.  This form is uniform in the lower endpoint `a`. -/
theorem caichWPiecewiseTotalMomentRootBudget_le_harmonic_add_card
    {r x : ℕ} (hr : 1 ≤ r) (hlog : 2 ≤ Real.log (x : ℝ)) (a : ℕ) :
    caichWPiecewiseTotalMomentRootBudget r
        (caichWSmoothingParameterNat r x) x a x ≤
      ((caichWScalarConstant r * 2 ^ caichWCardExponent r) *
          (x : ℝ) / Real.log (x : ℝ) ^ (2 : ℕ)) *
          (1 + Real.log (x : ℝ)) +
        (#(freshPrimes a x) : ℝ) := by
  let X : ℕ := caichWSmoothingParameterNat r x
  let A : ℝ := caichWScalarConstant r * 2 ^ caichWCardExponent r
  let D : ℝ := A * (x : ℝ) / Real.log (x : ℝ) ^ (2 : ℕ)
  let P : Finset ℕ := freshPrimes a x
  have hA : 0 ≤ A := by
    dsimp only [A]
    exact mul_nonneg (caichWScalarConstant_pos r).le
      (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)
  have hD : 0 ≤ D := by
    dsimp only [D]
    positivity
  have hterm (p : ℕ) (hpP : p ∈ P) :
      caichWPiecewisePrimeMomentRootBudget r X x p ≤
        D * (p : ℝ)⁻¹ + 1 := by
    have hp : p.Prime := (mem_freshPrimes.mp (by simpa only [P] using! hpP)).1
    unfold caichWPiecewisePrimeMomentRootBudget
    by_cases hlarge : x < p * (X + 1)
    · rw [if_pos hlarge]
      exact le_add_of_nonneg_left
        (mul_nonneg hD (inv_nonneg.mpr (Nat.cast_nonneg p)))
    · rw [if_neg hlarge]
      have hsmall : p * (X + 1) ≤ x := le_of_not_gt hlarge
      have hraw := caichWPrimeMomentRootBudget_le_div_sq_natSmoothing
        hr hp (by simpa only [X] using! hsmall) hlog
      have heq :
          (caichWScalarConstant r * 2 ^ caichWCardExponent r) *
                ((x : ℝ) / (p : ℝ)) /
              Real.log (x : ℝ) ^ (2 : ℕ) =
            D * (p : ℝ)⁻¹ := by
        dsimp only [D, A]
        field_simp [show (p : ℝ) ≠ 0 by exact_mod_cast hp.ne_zero]
        <;> ring
      exact hraw.trans (by rw [heq]; linarith)
  unfold caichWPiecewiseTotalMomentRootBudget
  change (∑ p ∈ P, caichWPiecewisePrimeMomentRootBudget r X x p) ≤ _
  calc
    (∑ p ∈ P, caichWPiecewisePrimeMomentRootBudget r X x p) ≤
        ∑ p ∈ P, (D * (p : ℝ)⁻¹ + 1) := by
      exact Finset.sum_le_sum fun p hp ↦ hterm p hp
    _ = D * freshReciprocalSum a x + (#P : ℝ) := by
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_const, nsmul_eq_mul, mul_one,
        Nat.cast_ofNat, Nat.cast_id]
      unfold freshReciprocalSum
      rw [Finset.mul_sum]
    _ ≤ D * (1 + Real.log (x : ℝ)) + (#P : ℝ) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left
          (freshReciprocalSum_le_one_add_log a x) hD) le_rfl
    _ = ((caichWScalarConstant r * 2 ^ caichWCardExponent r) *
          (x : ℝ) / Real.log (x : ℝ) ^ (2 : ℕ)) *
          (1 + Real.log (x : ℝ)) +
        (#(freshPrimes a x) : ℝ) := rfl

/-- If a Chebyshev bound is available at `x`, the complete piecewise
budget is `O_r(x / log x)`. -/
theorem caichWPiecewiseTotalMomentRootBudget_le_mul_div_log
    {r x : ℕ} (hr : 1 ≤ r) (hlog : 2 ≤ Real.log (x : ℝ))
    {Cpi : ℝ} (hCpi : 0 ≤ Cpi) (a : ℕ)
    (hcard : (#(freshPrimes a x) : ℝ) ≤
      Cpi * (x : ℝ) / Real.log (x : ℝ)) :
    caichWPiecewiseTotalMomentRootBudget r
        (caichWSmoothingParameterNat r x) x a x ≤
      (2 * (caichWScalarConstant r * 2 ^ caichWCardExponent r) + Cpi) *
        (x : ℝ) / Real.log (x : ℝ) := by
  let A : ℝ := caichWScalarConstant r * 2 ^ caichWCardExponent r
  let D : ℝ := A * (x : ℝ) / Real.log (x : ℝ) ^ (2 : ℕ)
  let L : ℝ := Real.log (x : ℝ)
  have hA : 0 ≤ A := by
    dsimp only [A]
    exact mul_nonneg (caichWScalarConstant_pos r).le
      (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hL : 0 < L := by dsimp only [L]; linarith
  have hsmall : D * (1 + L) ≤ 2 * A * (x : ℝ) / L := by
    calc
      D * (1 + L) ≤ D * (2 * L) := by
        exact mul_le_mul_of_nonneg_left (by linarith) hD
      _ = 2 * A * (x : ℝ) / L := by
        dsimp only [D]
        field_simp [hL.ne']
        <;> ring
  have hraw :=
    caichWPiecewiseTotalMomentRootBudget_le_harmonic_add_card
      hr hlog a
  calc
    caichWPiecewiseTotalMomentRootBudget r
        (caichWSmoothingParameterNat r x) x a x ≤
      D * (1 + L) + (#(freshPrimes a x) : ℝ) := by
        simpa only [A, D, L] using! hraw
    _ ≤ (2 * A * (x : ℝ) / L) +
        (Cpi * (x : ℝ) / L) := add_le_add hsmall (by
          simpa only [L] using! hcard)
    _ = (2 * (caichWScalarConstant r *
          2 ^ caichWCardExponent r) + Cpi) *
        (x : ℝ) / Real.log (x : ℝ) := by
      dsimp only [A, L]
      ring

/-- The complete arithmetic estimate is unconditional: Chebyshev's
theorem supplies the large-prime count and the harmonic bound supplies the
small-prime reciprocal sum. -/
theorem exists_eventually_caichWPiecewiseTotalMomentRootBudget_bound
    {r : ℕ} (hr : 1 ≤ r) :
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ x : ℕ in atTop, ∀ a : ℕ,
        caichWPiecewiseTotalMomentRootBudget r
            (caichWSmoothingParameterNat r x) x a x ≤
          C * (x : ℝ) / Real.log (x : ℝ) := by
  obtain ⟨Cpi, hCpi, hcard⟩ :=
    exists_eventually_uniform_card_freshPrimes_bound
  let A : ℝ := caichWScalarConstant r * 2 ^ caichWCardExponent r
  let C : ℝ := 2 * A + Cpi
  have hA : 0 < A := by
    dsimp only [A]
    exact mul_pos (caichWScalarConstant_pos r)
      (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _)
  have hC : 0 < C := by dsimp only [C]; positivity
  have hlog : ∀ᶠ x : ℕ in atTop, 2 ≤ Real.log (x : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop (2 : ℝ))
  refine ⟨C, hC, ?_⟩
  filter_upwards [hcard, hlog] with x hcardx hlogx
  intro a
  simpa only [C, A] using!
    caichWPiecewiseTotalMomentRootBudget_le_mul_div_log
      hr hlogx hCpi.le a (hcardx a)

/-! ## Aligned specialization and unconditional failure summability -/

/-- Every selected aligned test point eventually lies beyond any fixed
natural threshold. -/
theorem eventually_le_alignedRootExpTestPoint_of_mem
    {K m : ℕ} (hK : 1 ≤ K) (N : ℕ) :
    ∀ᶠ ell : ℕ in atTop, ∀ i ∈ alignedRootExpTests K m ell,
      N ≤ alignedRootExpTestPoint m i := by
  have hout := (tendsto_alignedOuterEndpoint_atTop hK).eventually
    (eventually_ge_atTop N)
  rw [eventually_atTop] at hout
  obtain ⟨L, hL⟩ := hout
  filter_upwards [eventually_ge_atTop (L + 2)] with ell hell
  intro i hi
  have hsub : L ≤ ell - 2 := by omega
  have hinitial : N ≤ alignedThinEndpoint K ell 0 := by
    have := hL (ell - 2) hsub
    simpa only [alignedThinEndpoint, alignedThinExponent,
      ceilThinGrow_zero, alignedOuterEndpoint] using! this
  exact hinitial.trans
    (alignedThinInitial_lt_testPoint_of_mem hi).le

/-- The unconditional arithmetic estimate transported to every selected
point of all sufficiently large aligned scales. -/
theorem exists_eventually_aligned_caichWPiecewiseBudget_bound
    {r K m : ℕ} (hr : 1 ≤ r) (hK : 1 ≤ K)
    (a : ℕ → ℕ → ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ ell : ℕ in atTop, ∀ i ∈ alignedRootExpTests K m ell,
        caichWPiecewiseTotalMomentRootBudget r
            (caichWSmoothingParameterNat r
              (alignedRootExpTestPoint m i))
            (alignedRootExpTestPoint m i) (a ell i)
            (alignedRootExpTestPoint m i) ≤
          C * (alignedRootExpTestPoint m i : ℝ) /
            Real.log (alignedRootExpTestPoint m i : ℝ) := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_eventually_caichWPiecewiseTotalMomentRootBudget_bound hr
  rw [eventually_atTop] at hbound
  obtain ⟨N, hN⟩ := hbound
  refine ⟨C, hC, ?_⟩
  filter_upwards [eventually_le_alignedRootExpTestPoint_of_mem
      (m := m) hK N] with ell hell
  intro i hi
  exact hN (alignedRootExpTestPoint m i) (hell i hi) (a ell i)

/-- A pointwise piecewise-budget estimate gives the published aligned
`(C / log x)^r` moment bound for the natural-cast `W/x` variable. -/
theorem integral_caichAlignedConcreteWoverXNat_pow_le_of_budget
    {r K m : ℕ} (hr : 1 ≤ r) {a : ℕ → ℕ → ℕ}
    {C : ℝ} (hC : 0 ≤ C) {ell i : ℕ}
    (hi : i ∈ alignedRootExpTests K m ell)
    (hbudget :
      caichWPiecewiseTotalMomentRootBudget r
          (caichWSmoothingParameterNat r
            (alignedRootExpTestPoint m i))
          (alignedRootExpTestPoint m i) (a ell i)
          (alignedRootExpTestPoint m i) ≤
        C * (alignedRootExpTestPoint m i : ℝ) /
          Real.log (alignedRootExpTestPoint m i : ℝ)) :
    (∫ omega,
        caichAlignedConcreteWoverXNat r m a ell i omega ^ r ∂μ) ≤
      caichAlignedWMoment r m C ell i := by
  let x : ℕ := alignedRootExpTestPoint m i
  let X : ℕ := caichWSmoothingParameterNat r x
  have hx : 0 < x :=
    Nat.zero_lt_of_lt (one_lt_alignedRootExpTestPoint_of_mem hi)
  have hxR : (0 : ℝ) < (x : ℝ) := by exact_mod_cast hx
  have hlog : 0 < Real.log (x : ℝ) :=
    Real.log_pos (by exact_mod_cast
      (one_lt_alignedRootExpTestPoint_of_mem hi))
  have hX : 0 < X := caichWSmoothingParameterNat_pos r x
  have hbase := caichConcreteWoverX_moment_le_piecewise
    r X x (a ell i) x hr hX hx
  have hnormalized :
      caichWPiecewiseTotalMomentRootBudget r X x (a ell i) x /
          (x : ℝ) ≤
        C / Real.log (x : ℝ) := by
    rw [div_le_iff₀ hxR]
    calc
      caichWPiecewiseTotalMomentRootBudget r X x (a ell i) x ≤
          C * (x : ℝ) / Real.log (x : ℝ) := by
        simpa only [x, X] using! hbudget
      _ = (C / Real.log (x : ℝ)) * (x : ℝ) := by ring
  have htotal : 0 ≤
      caichWPiecewiseTotalMomentRootBudget r X x (a ell i) x :=
    caichWPiecewiseTotalMomentRootBudget_nonneg r hX x (a ell i) x
  have hpow := pow_le_pow_left₀ (div_nonneg htotal hxR.le)
    hnormalized r
  unfold caichAlignedConcreteWoverXNat caichAlignedWMoment
  simpa only [x, X, caichWSmoothingParameterNatCast] using!
    hbase.trans hpow

/-- Markov plus a finite union at one fixed scale, requiring moment facts
only for the test points that actually occur at that scale. -/
theorem measureReal_caichAuxiliaryComponentFailure_le_natMomentBudget_at
    (tests : ℕ → Finset ℕ)
    (value : ℕ → ℕ → Omega → ℝ)
    (moment : ℕ → ℕ → ℝ)
    (threshold : ℕ → ℝ) (q ell : ℕ)
    (hq : 0 < q)
    (hvalue : ∀ i ∈ tests ell, ∀ omega, 0 ≤ value ell i omega)
    (hthreshold : 0 < threshold ell)
    (hintegrable : ∀ i ∈ tests ell,
      Integrable (fun omega ↦ value ell i omega ^ q) μ)
    (hmoment : ∀ i ∈ tests ell,
      (∫ omega, value ell i omega ^ q ∂μ) ≤ moment ell i) :
    μ.real (caichAuxiliaryComponentFailure tests value threshold ell) ≤
      caichAuxiliaryFiniteUnionMomentBudget
        tests moment threshold q ell := by
  let point : ℕ → Set Omega := fun i ↦
    {omega | threshold ell < value ell i omega}
  have hfailure :
      caichAuxiliaryComponentFailure tests value threshold ell =
        ⋃ i ∈ tests ell, point i := by
    ext omega
    simp only [caichAuxiliaryComponentFailure,
      caichAuxiliaryComponentGoodAtScale, Set.mem_setOf_eq, not_forall,
      not_le, Set.mem_iUnion, exists_prop, point]
  rw [hfailure]
  calc
    μ.real (⋃ i ∈ tests ell, point i) ≤
        ∑ i ∈ tests ell, μ.real (point i) :=
      measureReal_biUnion_finset_le _ _
    _ ≤ ∑ i ∈ tests ell,
        moment ell i / threshold ell ^ q := by
      gcongr with i hi
      exact measureReal_lt_le_natMoment hq (hvalue i hi)
        hthreshold (hintegrable i hi) (hmoment i hi)
    _ = caichAuxiliaryFiniteUnionMomentBudget
        tests moment threshold q ell := rfl

/-- Complete unconditional `W/x` failure summability on the aligned mesh.
There is no remaining divisor-budget hypothesis: the many-atom estimate,
the single-atom repair, the harmonic sum, and Chebyshev are all instantiated
internally. -/
theorem summable_measureReal_caichAlignedConcreteWoverXNat_failure
    {r K m : ℕ} (hr : 1 ≤ r) (hK : 1 ≤ K)
    (hgap : 12 * (2 ^ K) * (2 * m + 2) ≤ r)
    (a : ℕ → ℕ → ℕ) :
    Summable fun ell ↦ μ.real
      (caichAuxiliaryComponentFailure (alignedRootExpTests K m)
        (caichAlignedConcreteWoverXNat r m a)
        (caichWAuxThreshold K) ell) := by
  obtain ⟨C, hC, hbudget⟩ :=
    exists_eventually_aligned_caichWPiecewiseBudget_bound
      hr hK a
  let tests : ℕ → Finset ℕ := alignedRootExpTests K m
  let value : ℕ → ℕ → Omega → ℝ :=
    caichAlignedConcreteWoverXNat r m a
  let moment : ℕ → ℕ → ℝ := caichAlignedWMoment r m C
  let safeMoment : ℕ → ℕ → ℝ := fun ell i ↦
    if i ∈ tests ell then moment ell i else 0
  have hscalar := caichWAlignedScalarSummability_of_largeMoment
    hK hgap hC.le
  unfold CaichWAlignedScalarSummability at hscalar
  apply hscalar.of_norm_bounded_eventually_nat
  filter_upwards [hbudget, eventually_ge_atTop (5 : ℕ)] with
      ell hbudgetEll hell
  have hmoment : ∀ i ∈ tests ell,
      (∫ omega, value ell i omega ^ r ∂μ) ≤ moment ell i := by
    intro i hi
    exact integral_caichAlignedConcreteWoverXNat_pow_le_of_budget
      hr hC.le (by simpa only [tests] using! hi)
      (hbudgetEll i (by simpa only [tests] using! hi))
  have hmeasureSafe :=
    measureReal_caichAuxiliaryComponentFailure_le_natMomentBudget_at
      tests value moment (caichAlignedWSafeThreshold K) r ell
      (by omega)
      (fun i hi omega ↦
        caichAlignedConcreteWoverXNat_nonneg
          (by simpa only [tests, value] using! hi) omega)
      (caichAlignedWSafeThreshold_pos K ell)
      (fun i hi ↦
        integrable_caichAlignedConcreteWoverXNat_pow hr
          (by simpa only [tests, value] using! hi))
      hmoment
  have hthreshold :
      caichAlignedWSafeThreshold K ell = caichWAuxThreshold K ell := by
    unfold caichAlignedWSafeThreshold
    rw [if_neg (by omega : ¬ ell < 5)]
  have hfailure :
      caichAuxiliaryComponentFailure tests value
          (caichAlignedWSafeThreshold K) ell =
        caichAuxiliaryComponentFailure tests value
          (caichWAuxThreshold K) ell := by
    unfold caichAuxiliaryComponentFailure
      caichAuxiliaryComponentGoodAtScale
    ext omega
    simp only [Set.mem_setOf_eq, not_forall, not_le]
    rw [hthreshold]
  have hmeasure :
      μ.real (caichAuxiliaryComponentFailure tests value
          (caichWAuxThreshold K) ell) ≤
        caichAuxiliaryFiniteUnionMomentBudget tests moment
          (caichAlignedWSafeThreshold K) r ell := by
    rw [← hfailure]
    exact hmeasureSafe
  have hbudgetNonneg : 0 ≤
      caichAuxiliaryFiniteUnionMomentBudget tests safeMoment
        (caichAlignedWSafeThreshold K) r ell := by
    unfold caichAuxiliaryFiniteUnionMomentBudget
    exact Finset.sum_nonneg fun i hi ↦ by
      have hi' : i ∈ tests ell := hi
      have hx : 1 < alignedRootExpTestPoint m i :=
        one_lt_alignedRootExpTestPoint_of_mem
          (by simpa only [tests] using! hi)
      have hlog : 0 < Real.log (alignedRootExpTestPoint m i : ℝ) :=
        Real.log_pos (by exact_mod_cast hx)
      unfold safeMoment moment caichAlignedWMoment
      rw [if_pos hi']
      exact div_nonneg
        (pow_nonneg (div_nonneg hC.le hlog.le) r)
        (pow_nonneg (caichAlignedWSafeThreshold_pos K ell).le r)
  have hbudgetEq :
      caichAuxiliaryFiniteUnionMomentBudget tests moment
          (caichAlignedWSafeThreshold K) r ell =
        caichAuxiliaryFiniteUnionMomentBudget tests safeMoment
          (caichAlignedWSafeThreshold K) r ell := by
    unfold caichAuxiliaryFiniteUnionMomentBudget
    apply Finset.sum_congr rfl
    intro i hi
    unfold safeMoment
    rw [if_pos hi]
  rw [Real.norm_eq_abs, abs_of_nonneg (measureReal_nonneg :
    0 ≤ μ.real (caichAuxiliaryComponentFailure tests value
      (caichWAuxThreshold K) ell))]
  simpa only [tests, value, moment, safeMoment] using!
    hmeasure.trans_eq hbudgetEq

end Problem520
end Erdos
