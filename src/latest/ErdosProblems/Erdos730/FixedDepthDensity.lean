/- leanprover/lean4:v4.33.0  mathlib db584cd6 (master, the commit the v4.33.0 tag is cut from) -/
import ErdosProblems.Erdos730.DigitBoxes
import ErdosProblems.Erdos730.FixedDepthFourier
import ErdosProblems.Erdos730.PrimeBands
import Mathlib.NumberTheory.Chebyshev

/-!
# Erdős 730: the fixed-depth analytic density passage

This file isolates equations (37)--(42) from the event-counting ledger.  We
use the relaxed full lower-half box.  At depth `r` its exact density is

`4⁻ʳ * (1 + 1 / p)^(2*r)`.

The difference from `4⁻ʳ` contributes a summable `p⁻²` error after the
per-prime `1/p` weight.  The Fourier discrepancy, terminal blocks, and the
per-prime `+1` terms are packaged as explicit analytic majorants and shown to
vanish.  Thus the majorant tends to the Mertens band mass

`4⁻ʳ * log ((r+2)/(r+1))`.

No event-density assertion is assumed in this module.  Its final comparison
theorem consumes only a separately supplied finite count inequality against
the concrete majorant.
-/

open Filter Finset
open scoped Topology Chebyshev

namespace Erdos730
namespace FixedDepthDensity

open DigitBoxes FullDensity

noncomputable section

/-! ## The exact finite band and relaxed digit density -/

/-- Primes in the real-cutoff depth-`r` band
`X^(1/(r+2)) < p ≤ X^(1/(r+1))`. -/
def fixedDepthPrimeSet (r X : ℕ) : Finset ℕ :=
  (Finset.Ioc
      ⌊fixedDepthPrimeBandLower r (X : ℝ)⌋₊
      ⌊fixedDepthPrimeBandUpper r (X : ℝ)⌋₊).filter Nat.Prime

/-- Exact density of the relaxed full `2r`-digit lower-half box. -/
def relaxedDigitDensity (r p : ℕ) : ℝ :=
  (((halfDigitCount p : ℕ) : ℝ) / (p : ℝ)) ^ (2 * r)

/-- The limiting density at fixed depth. -/
def fixedDepthBaseDensity (r : ℕ) : ℝ := (1 / 4 : ℝ) ^ r

/-- Explicit coefficient in the `O_r(1/p)` density estimate. -/
def fixedDepthDensityErrorConstant (r : ℕ) : ℝ :=
  (2 * r : ℕ) * (2 : ℝ) ^ (2 * r)

theorem relaxedDigitDensity_eq_card_ratio
    {r p : ℕ} (hp : 3 ≤ p) :
    relaxedDigitDensity r p =
      ((lowerHalfResidues p (2 * r)).card : ℝ) / (p : ℝ) ^ (2 * r) := by
  rw [lowerHalfResidues_card hp]
  simp only [relaxedDigitDensity, Nat.cast_pow]
  rw [div_pow]

lemma halfDigitCount_cast_eq {p : ℕ} (hpodd : p % 2 = 1) :
    ((halfDigitCount p : ℕ) : ℝ) = ((p : ℝ) + 1) / 2 := by
  have hpform : p = 2 * (p / 2) + 1 := by omega
  unfold halfDigitCount
  rw [hpform]
  norm_num

/-- Equation (37) for the relaxed full lower-half box. -/
theorem relaxedDigitDensity_formula
    {r p : ℕ} (hpodd : p % 2 = 1) (hp : 1 ≤ p) :
    relaxedDigitDensity r p =
      fixedDepthBaseDensity r * (1 + (p : ℝ)⁻¹) ^ (2 * r) := by
  have hpR : (p : ℝ) ≠ 0 := by positivity
  rw [relaxedDigitDensity, halfDigitCount_cast_eq hpodd,
    fixedDepthBaseDensity]
  have hratio : (((p : ℝ) + 1) / 2) / (p : ℝ) =
      (1 / 2 : ℝ) * (1 + (p : ℝ)⁻¹) := by
    field_simp
  rw [hratio, mul_pow]
  congr 1
  rw [show 2 * r = r + r by omega, pow_add]
  rw [← mul_pow]
  norm_num

lemma one_add_pow_sub_one_le
    (n : ℕ) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    (1 + x) ^ n - 1 ≤ (n : ℝ) * 2 ^ n * x := by
  induction n with
  | zero => simp
  | succ n ih =>
      have ha0 : 0 ≤ 1 + x := by linarith
      have ha1 : 1 ≤ 1 + x := by linarith
      have ha2 : 1 + x ≤ 2 := by linarith
      have hdiff0 : 0 ≤ (1 + x) ^ n - 1 := by
        exact sub_nonneg.mpr (one_le_pow₀ ha1)
      calc
        (1 + x) ^ (n + 1) - 1 =
            ((1 + x) ^ n - 1) * (1 + x) + x := by ring
        _ ≤ ((n : ℝ) * 2 ^ n * x) * 2 + x := by
          gcongr
        _ ≤ ((n + 1 : ℕ) : ℝ) * 2 ^ (n + 1) * x := by
          have hpow : (1 : ℝ) ≤ 2 ^ (n + 1) := one_le_pow₀ (by norm_num)
          have hxpow : x ≤ 2 ^ (n + 1) * x :=
            by simpa using mul_le_mul_of_nonneg_right hpow hx0
          calc
            ((n : ℝ) * 2 ^ n * x) * 2 + x =
                (n : ℝ) * 2 ^ (n + 1) * x + x := by
              rw [pow_succ]
              ring
            _ ≤ (n : ℝ) * 2 ^ (n + 1) * x + 2 ^ (n + 1) * x :=
              add_le_add_right hxpow _
            _ = ((n + 1 : ℕ) : ℝ) * 2 ^ (n + 1) * x := by
              push_cast
              ring

theorem relaxedDigitDensity_sub_base_nonneg
    {r p : ℕ} (hpodd : p % 2 = 1) (hp : 1 ≤ p) :
    0 ≤ relaxedDigitDensity r p - fixedDepthBaseDensity r := by
  rw [relaxedDigitDensity_formula hpodd hp]
  have hbase : 0 ≤ fixedDepthBaseDensity r := by
    exact pow_nonneg (by norm_num [fixedDepthBaseDensity]) _
  have hinv : 0 ≤ (p : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg p)
  have hpow : 1 ≤ (1 + (p : ℝ)⁻¹) ^ (2 * r) :=
    one_le_pow₀ (by linarith)
  nlinarith

/-- Explicit `O_r(1/p)` bound for the relaxed density. -/
theorem relaxedDigitDensity_sub_base_le
    {r p : ℕ} (hpodd : p % 2 = 1) (hp : 1 ≤ p) :
    relaxedDigitDensity r p - fixedDepthBaseDensity r ≤
      fixedDepthDensityErrorConstant r / (p : ℝ) := by
  have hpR : (0 : ℝ) < p := by positivity
  have hx0 : 0 ≤ (p : ℝ)⁻¹ := inv_nonneg.mpr hpR.le
  have hx1 : (p : ℝ)⁻¹ ≤ 1 := by
    exact (inv_le_one₀ hpR).2 (by exact_mod_cast hp)
  have hpow := one_add_pow_sub_one_le (2 * r) hx0 hx1
  have hbase0 : 0 ≤ fixedDepthBaseDensity r := by
    exact pow_nonneg (by norm_num [fixedDepthBaseDensity]) _
  have hbase1 : fixedDepthBaseDensity r ≤ 1 := by
    exact pow_le_one₀ (a := (1 / 4 : ℝ)) (by norm_num) (by norm_num)
  rw [relaxedDigitDensity_formula hpodd hp]
  calc
    fixedDepthBaseDensity r * (1 + (p : ℝ)⁻¹) ^ (2 * r) -
          fixedDepthBaseDensity r =
        fixedDepthBaseDensity r *
          ((1 + (p : ℝ)⁻¹) ^ (2 * r) - 1) := by ring
    _ ≤ fixedDepthBaseDensity r *
          (((2 * r : ℕ) : ℝ) * 2 ^ (2 * r) * (p : ℝ)⁻¹) := by
      gcongr
    _ ≤ ((2 * r : ℕ) : ℝ) * 2 ^ (2 * r) * (p : ℝ)⁻¹ := by
      have hA : 0 ≤ ((2 * r : ℕ) : ℝ) * 2 ^ (2 * r) * (p : ℝ)⁻¹ := by
        positivity
      simpa using mul_le_mul_of_nonneg_right hbase1 hA
    _ = fixedDepthDensityErrorConstant r / (p : ℝ) := by
      rw [fixedDepthDensityErrorConstant, div_eq_mul_inv]

/-- After the reciprocal-prime weight, the density correction is `O_r(p⁻²)`. -/
theorem relaxedDigitDensity_weighted_error_le
    {r p : ℕ} (hpodd : p % 2 = 1) (hp : 1 ≤ p) :
    (relaxedDigitDensity r p - fixedDepthBaseDensity r) / (p : ℝ) ≤
      fixedDepthDensityErrorConstant r / (p : ℝ) ^ 2 := by
  have hpR : (0 : ℝ) < p := by positivity
  calc
    (relaxedDigitDensity r p - fixedDepthBaseDensity r) / (p : ℝ) ≤
        (fixedDepthDensityErrorConstant r / (p : ℝ)) / (p : ℝ) :=
      div_le_div_of_nonneg_right
        (relaxedDigitDensity_sub_base_le hpodd hp) hpR.le
    _ = fixedDepthDensityErrorConstant r / (p : ℝ) ^ 2 := by ring

theorem relaxedDigitDensity_nonneg (r p : ℕ) :
    0 ≤ relaxedDigitDensity r p := by
  unfold relaxedDigitDensity
  positivity

/-- The relaxed box density is at most one; this absorbs the `+1` interval
term in equation (38) into `fixedDepthUnitError`. -/
theorem relaxedDigitDensity_le_one
    {r p : ℕ} (hp : 1 ≤ p) :
    relaxedDigitDensity r p ≤ 1 := by
  unfold relaxedDigitDensity
  apply pow_le_one₀
  · positivity
  · apply (div_le_one₀ (by positivity : (0 : ℝ) < p)).2
    exact_mod_cast halfDigitCount_le hp

/-! ## Tail domination and the exact Mertens decomposition -/

lemma sum_Ioc_eq_range_shift (f : ℕ → ℝ) (L U : ℕ) :
    (∑ n ∈ Finset.Ioc L U, f n) =
      ∑ k ∈ Finset.range (U - L), f (k + L + 1) := by
  classical
  apply Finset.sum_bij (fun n hn ↦ n - (L + 1))
  · intro n hn
    simp only [Finset.mem_range]
    simp only [Finset.mem_Ioc] at hn
    omega
  · intro a ha b hb hab
    simp only [Finset.mem_Ioc] at ha hb
    omega
  · intro k hk
    simp only [Finset.mem_range] at hk
    refine ⟨k + L + 1, ?_, ?_⟩
    · simp only [Finset.mem_Ioc]
      omega
    · omega
  · intro n hn
    simp only [Finset.mem_Ioc] at hn
    congr 1
    omega

lemma sum_Ioc_le_tail {f : ℕ → ℝ}
    (hf : ∀ n, 0 ≤ f n) (hs : Summable f) (L U : ℕ) :
    (∑ n ∈ Finset.Ioc L U, f n) ≤
      ∑' k : ℕ, f (k + L + 1) := by
  rw [sum_Ioc_eq_range_shift]
  have hshift : Summable (fun k : ℕ ↦ f (k + L + 1)) := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      ((summable_nat_add_iff (L + 1)).2 hs)
  exact hshift.sum_le_tsum (Finset.range (U - L)) (fun k _ ↦ hf _)

lemma tendsto_fixedDepthPrimeBandLowerFloor (r : ℕ) :
    Tendsto (fun X : ℕ ↦
      ⌊fixedDepthPrimeBandLower r (X : ℝ)⌋₊) atTop atTop := by
  exact tendsto_nat_floor_atTop.comp
    ((tendsto_rpow_atTop (by positivity)).comp tendsto_natCast_atTop_atTop)

lemma tendsto_fixedDepthPrimeBandUpper_nat (r : ℕ) :
    Tendsto (fun X : ℕ ↦ fixedDepthPrimeBandUpper r (X : ℝ))
      atTop atTop := by
  exact (tendsto_rpow_atTop (by positivity)).comp tendsto_natCast_atTop_atTop

/-- The reciprocal-square tail starting just above `L`. -/
def reciprocalSquareTail (L : ℕ) : ℝ :=
  ∑' k : ℕ, (((k + L + 1 : ℕ) : ℝ) ^ 2)⁻¹

lemma reciprocalSquare_summable :
    Summable (fun n : ℕ ↦ (((n : ℕ) : ℝ) ^ 2)⁻¹) :=
  Real.summable_nat_pow_inv.mpr (by omega)

theorem tendsto_reciprocalSquareTail_zero :
    Tendsto reciprocalSquareTail atTop (𝓝 0) := by
  have h := tendsto_sum_nat_add
    (f := fun n : ℕ ↦ (((n : ℕ) : ℝ) ^ 2)⁻¹)
  have h' := h.comp (tendsto_add_atTop_nat 1)
  simpa only [reciprocalSquareTail, Nat.add_assoc] using! h'

/-- The exact weighted relaxed-density correction over the depth band. -/
def fixedDepthDensityCorrection (r X : ℕ) : ℝ :=
  ∑ p ∈ fixedDepthPrimeSet r X,
    (relaxedDigitDensity r p - fixedDepthBaseDensity r) / (p : ℝ)

theorem fixedDepthDensityCorrection_nonneg
    {r X : ℕ}
    (hL : 2 ≤ ⌊fixedDepthPrimeBandLower r (X : ℝ)⌋₊) :
    0 ≤ fixedDepthDensityCorrection r X := by
  apply Finset.sum_nonneg
  intro p hp
  rw [fixedDepthPrimeSet, Finset.mem_filter, Finset.mem_Ioc] at hp
  have hp2 : p ≠ 2 := by omega
  have hpodd : p % 2 = 1 :=
    (hp.2.mod_two_eq_one_iff_ne_two).2 hp2
  exact div_nonneg (relaxedDigitDensity_sub_base_nonneg hpodd (by omega))
    (Nat.cast_nonneg p)

/-- The finite `p⁻²` density correction is bounded by a genuine summable
tail beginning at the lower band endpoint. -/
theorem fixedDepthDensityCorrection_le_tail
    {r X : ℕ}
    (hL : 2 ≤ ⌊fixedDepthPrimeBandLower r (X : ℝ)⌋₊) :
    fixedDepthDensityCorrection r X ≤
      fixedDepthDensityErrorConstant r *
        reciprocalSquareTail
          ⌊fixedDepthPrimeBandLower r (X : ℝ)⌋₊ := by
  let L := ⌊fixedDepthPrimeBandLower r (X : ℝ)⌋₊
  let U := ⌊fixedDepthPrimeBandUpper r (X : ℝ)⌋₊
  have hC : 0 ≤ fixedDepthDensityErrorConstant r := by
    unfold fixedDepthDensityErrorConstant
    positivity
  have hsquare : Summable
      (fun p : ℕ ↦ fixedDepthDensityErrorConstant r *
        (((p : ℕ) : ℝ) ^ 2)⁻¹) :=
    reciprocalSquare_summable.mul_left _
  calc
    fixedDepthDensityCorrection r X =
        ∑ p ∈ fixedDepthPrimeSet r X,
          (relaxedDigitDensity r p - fixedDepthBaseDensity r) / (p : ℝ) := rfl
    _ ≤ ∑ p ∈ fixedDepthPrimeSet r X,
          fixedDepthDensityErrorConstant r * (((p : ℕ) : ℝ) ^ 2)⁻¹ := by
      apply Finset.sum_le_sum
      intro p hp
      rw [fixedDepthPrimeSet, Finset.mem_filter, Finset.mem_Ioc] at hp
      have hp2 : p ≠ 2 := by omega
      have hpodd : p % 2 = 1 :=
        (hp.2.mod_two_eq_one_iff_ne_two).2 hp2
      simpa [div_eq_mul_inv] using
        relaxedDigitDensity_weighted_error_le (r := r) hpodd (by omega)
    _ ≤ ∑ p ∈ Finset.Ioc L U,
          fixedDepthDensityErrorConstant r * (((p : ℕ) : ℝ) ^ 2)⁻¹ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro p hp
        have hp' := hp
        rw [fixedDepthPrimeSet, Finset.mem_filter] at hp'
        simpa [L, U] using hp'.1
      · intro p _hp _hnot
        positivity
    _ ≤ ∑' k : ℕ,
          fixedDepthDensityErrorConstant r *
            ((((k + L + 1 : ℕ) : ℕ) : ℝ) ^ 2)⁻¹ :=
      sum_Ioc_le_tail (fun _ ↦ by positivity) hsquare L U
    _ = fixedDepthDensityErrorConstant r * reciprocalSquareTail L := by
      rw [reciprocalSquareTail, tsum_mul_left]
    _ = fixedDepthDensityErrorConstant r *
        reciprocalSquareTail
          ⌊fixedDepthPrimeBandLower r (X : ℝ)⌋₊ := by rfl

theorem tendsto_fixedDepthDensityCorrection_zero (r : ℕ) :
    Tendsto (fixedDepthDensityCorrection r) atTop (𝓝 0) := by
  have htail := tendsto_reciprocalSquareTail_zero.comp
    (tendsto_fixedDepthPrimeBandLowerFloor r)
  have hmajorant : Tendsto (fun X : ℕ ↦
      fixedDepthDensityErrorConstant r *
        reciprocalSquareTail
          ⌊fixedDepthPrimeBandLower r (X : ℝ)⌋₊) atTop (𝓝 0) := by
    simpa using htail.const_mul (fixedDepthDensityErrorConstant r)
  apply squeeze_zero'
  · filter_upwards
      [(tendsto_fixedDepthPrimeBandLowerFloor r).eventually_ge_atTop 2]
      with X hL
    exact fixedDepthDensityCorrection_nonneg hL
  · filter_upwards
      [(tendsto_fixedDepthPrimeBandLowerFloor r).eventually_ge_atTop 2]
      with X hL
    exact fixedDepthDensityCorrection_le_tail hL
  · exact hmajorant

theorem fixedDepthPrimeSet_reciprocalSum_eq
    {r X : ℕ} (hX : 1 ≤ X) :
    (∑ p ∈ fixedDepthPrimeSet r X, (p : ℝ)⁻¹) =
      fixedDepthReciprocalPrimeBand r (X : ℝ) := by
  let L := ⌊fixedDepthPrimeBandLower r (X : ℝ)⌋₊
  let U := ⌊fixedDepthPrimeBandUpper r (X : ℝ)⌋₊
  have hLU : L ≤ U := by
    apply Nat.floor_mono
    exact fixedDepthPrimeBandLower_le_upper r (by exact_mod_cast hX)
  have hunion :
      (Finset.Ioc 0 L).filter Nat.Prime ∪
          (Finset.Ioc L U).filter Nat.Prime =
        (Finset.Ioc 0 U).filter Nat.Prime := by
    rw [← Finset.filter_union, Finset.Ioc_union_Ioc_eq_Ioc (Nat.zero_le L) hLU]
  have hdis : Disjoint
      ((Finset.Ioc 0 L).filter Nat.Prime)
      ((Finset.Ioc L U).filter Nat.Prime) :=
    (Finset.Ioc_disjoint_Ioc_of_le (le_refl L)).mono
      (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  rw [fixedDepthReciprocalPrimeBand, reciprocalPrimeSumReal,
    reciprocalPrimeSumReal]
  change (∑ p ∈ (Finset.Ioc L U).filter Nat.Prime, (p : ℝ)⁻¹) =
    (∑ p ∈ (Finset.Ioc 0 U).filter Nat.Prime, (p : ℝ)⁻¹) -
      ∑ p ∈ (Finset.Ioc 0 L).filter Nat.Prime, (p : ℝ)⁻¹
  rw [← hunion, Finset.sum_union hdis]
  ring

/-- Exact decomposition of the relaxed prime mass into the Mertens main term
and the summable density correction. -/
theorem fixedDepthRelaxedPrimeMass_eq
    {r X : ℕ} (hX : 1 ≤ X) :
    (∑ p ∈ fixedDepthPrimeSet r X,
        relaxedDigitDensity r p / (p : ℝ)) =
      fixedDepthBaseDensity r *
          fixedDepthReciprocalPrimeBand r (X : ℝ) +
        fixedDepthDensityCorrection r X := by
  rw [← fixedDepthPrimeSet_reciprocalSum_eq hX,
    fixedDepthDensityCorrection, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _hp
  ring

theorem tendsto_fixedDepthRelaxedPrimeMass (r : ℕ) :
    Tendsto (fun X : ℕ ↦
      ∑ p ∈ fixedDepthPrimeSet r X,
        relaxedDigitDensity r p / (p : ℝ)) atTop
      (𝓝 (fixedDepthBaseDensity r * fixedDepthPrimeBandMainTerm r)) := by
  have hmain :=
    (tendsto_fixedDepthReciprocalPrimeBand_nat r).const_mul
      (fixedDepthBaseDensity r)
  have h := hmain.add (tendsto_fixedDepthDensityCorrection_zero r)
  have h' : Tendsto (fun X : ℕ ↦
      fixedDepthBaseDensity r *
          fixedDepthReciprocalPrimeBand r (X : ℝ) +
        fixedDepthDensityCorrection r X) atTop
      (𝓝 (fixedDepthBaseDensity r * fixedDepthPrimeBandMainTerm r)) := by
    simpa using h
  apply h'.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with X hX
  exact (fixedDepthRelaxedPrimeMass_eq hX).symm

/-! ## The fixed-depth Fourier discrepancy tail -/

/-- The normalized per-prime Fourier envelope.  The harmless `3 + log p`
form directly matches the interval `L¹` surface in
`Erdos730FixedDepthFourier`; it also dominates the paper's `1 + log p` form. -/
def fixedDepthFourierWeight (r p : ℕ) : ℝ :=
  (3 + Real.log p) ^ (2 * r + 1) *
    (p : ℝ) ^ (-(3 / 2 : ℝ))

/-- The finite Fourier envelope over the depth band. -/
def fixedDepthFourierBandError (r X : ℕ) : ℝ :=
  ∑ p ∈ fixedDepthPrimeSet r X, fixedDepthFourierWeight r p

/-- The explicit paper coefficient `2 C_r`, with
`C_r = (2r+3) 3^(2r)`. -/
def fixedDepthFourierErrorConstant (r : ℕ) : ℝ :=
  2 * (2 * r + 3 : ℕ) * (3 : ℝ) ^ (2 * r)

/-- Complete normalized Fourier-error majorant. -/
def fixedDepthFourierError (r X : ℕ) : ℝ :=
  fixedDepthFourierErrorConstant r * fixedDepthFourierBandError r X

/-- The exact one-block discrepancy on the right side of
`FixedDepthFourier.fixedDepth_intervalHitCount_discrepancy_le`. -/
def fixedDepthBlockDiscrepancy (r p : ℕ) : ℝ :=
  Real.sqrt (((p ^ (2 * r - 1) : ℕ) : ℝ)) *
    (((2 * r + 3 : ℕ) : ℝ) * (1 + Real.log p)) *
      (3 + Real.log p) ^ (2 * r)

theorem fixedDepthBlockDiscrepancy_nonneg (r p : ℕ) :
    0 ≤ fixedDepthBlockDiscrepancy r p := by
  unfold fixedDepthBlockDiscrepancy
  exact mul_nonneg
    (mul_nonneg (Real.sqrt_nonneg _) (mul_nonneg (by positivity) (by positivity)))
    (pow_nonneg (by positivity) _)

theorem one_le_fixedDepthBlockDiscrepancy
    {r p : ℕ} (hp : 0 < p) (hr : 1 ≤ r) :
    1 ≤ fixedDepthBlockDiscrepancy r p := by
  have hp1 : 1 ≤ p := hp
  have hpowNat : 1 ≤ p ^ (2 * r - 1) :=
    Nat.one_le_pow _ p hp
  have hpowReal : (1 : ℝ) ≤ ((p ^ (2 * r - 1) : ℕ) : ℝ) := by
    exact_mod_cast hpowNat
  have hsqrt : (1 : ℝ) ≤
      Real.sqrt (((p ^ (2 * r - 1) : ℕ) : ℝ)) := by
    exact Real.le_sqrt_of_sq_le (by simpa using hpowReal)
  have hlog : 0 ≤ Real.log (p : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hp1)
  have hcoef : (1 : ℝ) ≤ ((2 * r + 3 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 1 ≤ 2 * r + 3)
  have hlog1 : (1 : ℝ) ≤ 1 + Real.log p := by linarith
  have hlog3 : (1 : ℝ) ≤ (3 + Real.log p) ^ (2 * r) :=
    one_le_pow₀ (by linarith)
  rw [fixedDepthBlockDiscrepancy]
  calc
    (1 : ℝ) = 1 * (1 * 1) * 1 := by norm_num
    _ ≤ Real.sqrt (((p ^ (2 * r - 1) : ℕ) : ℝ)) *
        (((2 * r + 3 : ℕ) : ℝ) * (1 + Real.log p)) *
          (3 + Real.log p) ^ (2 * r) := by gcongr

/-- Exact natural-number complete-block count.  The band condition pays for
the endpoint `+1` without introducing another Fourier block. -/
theorem fixedDepthBlockCount_mul_pow_le
    {X p r : ℕ} (hp : 0 < p) (hr : 1 ≤ r)
    (hband : p ^ (r + 1) ≤ X) :
    ((X / p + 1) / p ^ r) * p ^ (r + 1) ≤ 2 * X := by
  let B := (X / p + 1) / p ^ r
  have hdiv : B * p ^ r ≤ X / p + 1 := by
    exact Nat.div_mul_le_self (X / p + 1) (p ^ r)
  have hpX : p ≤ X := by
    calc
      p = p ^ 1 := by simp
      _ ≤ p ^ (r + 1) := Nat.pow_le_pow_right hp (by omega)
      _ ≤ X := hband
  have hXp : (X / p) * p ≤ X := Nat.div_mul_le_self X p
  calc
    B * p ^ (r + 1) = (B * p ^ r) * p := by
      rw [pow_succ]
      ring
    _ ≤ (X / p + 1) * p := Nat.mul_le_mul_right p hdiv
    _ = (X / p) * p + p := by ring
    _ ≤ X + X := Nat.add_le_add hXp hpX
    _ = 2 * X := by ring

theorem fixedDepthBlockCount_normalized_le
    {X p r : ℕ} (hp : 0 < p) (hX : 0 < X) (hr : 1 ≤ r)
    (hband : p ^ (r + 1) ≤ X) :
    ((((X / p + 1) / p ^ r : ℕ) : ℝ) / (X : ℝ)) ≤
      2 / (p : ℝ) ^ (r + 1) := by
  have hnat := fixedDepthBlockCount_mul_pow_le hp hr hband
  have hreal : (((X / p + 1) / p ^ r : ℕ) : ℝ) *
      (p : ℝ) ^ (r + 1) ≤ 2 * (X : ℝ) := by
    exact_mod_cast hnat
  have hXR : (0 : ℝ) < X := by exact_mod_cast hX
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  apply (div_le_div_iff₀ hXR (pow_pos hpR (r + 1))).2
  simpa [mul_assoc, mul_left_comm, mul_comm] using hreal

lemma sqrt_prime_pow_div (p r : ℕ) (hp : 0 < p) (hr : 1 ≤ r) :
    Real.sqrt (((p ^ (2 * r - 1) : ℕ) : ℝ)) /
        (p : ℝ) ^ (r + 1) =
      (p : ℝ) ^ (-(3 / 2 : ℝ)) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hexp : (((2 * r - 1 : ℕ) : ℝ) * (1 / 2 : ℝ)) =
      (r : ℝ) - 1 / 2 := by
    rw [Nat.cast_sub (by omega : 1 ≤ 2 * r)]
    push_cast
    ring
  rw [Nat.cast_pow, Real.sqrt_eq_rpow, ← Real.rpow_natCast,
    ← Real.rpow_mul hpR.le, hexp, ← Real.rpow_natCast]
  rw [← Real.rpow_sub hpR]
  congr 1
  push_cast
  ring

/-- The chosen fixed-r Fourier coefficient dominates the exact translated
Lemma-2 discrepancy, including the factor two from the number of complete
`p^r` blocks. -/
theorem fixedDepthBlockDiscrepancy_scaled_le
    {p r : ℕ} (hp : 0 < p) (hr : 1 ≤ r) :
    (2 / (p : ℝ) ^ (r + 1)) * fixedDepthBlockDiscrepancy r p ≤
      fixedDepthFourierErrorConstant r * fixedDepthFourierWeight r p := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hlog : 0 ≤ Real.log (p : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hp)
  have hsqrt := sqrt_prime_pow_div p r hp hr
  have hz : 0 ≤ (p : ℝ) ^ (-(3 / 2 : ℝ)) :=
    Real.rpow_nonneg hpR.le _
  have hC : 0 ≤ (((2 * r + 3 : ℕ) : ℝ)) := by positivity
  calc
    (2 / (p : ℝ) ^ (r + 1)) * fixedDepthBlockDiscrepancy r p =
        2 * (Real.sqrt (((p ^ (2 * r - 1) : ℕ) : ℝ)) /
          (p : ℝ) ^ (r + 1)) *
          (((2 * r + 3 : ℕ) : ℝ)) * (1 + Real.log p) *
            (3 + Real.log p) ^ (2 * r) := by
      rw [fixedDepthBlockDiscrepancy]
      ring
    _ = 2 * (p : ℝ) ^ (-(3 / 2 : ℝ)) *
          (((2 * r + 3 : ℕ) : ℝ)) * (1 + Real.log p) *
            (3 + Real.log p) ^ (2 * r) := by rw [hsqrt]
    _ ≤ 2 * (p : ℝ) ^ (-(3 / 2 : ℝ)) *
          (((2 * r + 3 : ℕ) : ℝ)) * (3 + Real.log p) *
            (3 + Real.log p) ^ (2 * r) := by
      gcongr
      norm_num
    _ = 2 * (((2 * r + 3 : ℕ) : ℝ)) *
          ((3 + Real.log p) ^ (2 * r + 1) *
            (p : ℝ) ^ (-(3 / 2 : ℝ))) := by
      rw [pow_succ]
      ring
    _ ≤ fixedDepthFourierErrorConstant r * fixedDepthFourierWeight r p := by
      rw [fixedDepthFourierErrorConstant, fixedDepthFourierWeight]
      have hpow : (1 : ℝ) ≤ 3 ^ (2 * r) :=
        one_le_pow₀ (by norm_num)
      have hfac : 2 * (((2 * r + 3 : ℕ) : ℝ)) ≤
          2 * (((2 * r + 3 : ℕ) : ℝ)) * 3 ^ (2 * r) := by
        nlinarith [mul_nonneg hC (sub_nonneg.mpr hpow)]
      exact mul_le_mul_of_nonneg_right hfac
        (mul_nonneg (pow_nonneg (by linarith) _) hz)

/-- The same coefficient also absorbs the extra factor two introduced when a
real complete-block bound is rounded up to a natural-number bound.  The
slack is `3^(2r) ≥ 2` for every positive depth. -/
theorem fixedDepthBlockDiscrepancy_double_scaled_le
    {p r : ℕ} (hp : 0 < p) (hr : 1 ≤ r) :
    (4 / (p : ℝ) ^ (r + 1)) * fixedDepthBlockDiscrepancy r p ≤
      fixedDepthFourierErrorConstant r * fixedDepthFourierWeight r p := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hlog : 0 ≤ Real.log (p : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hp)
  have hsqrt := sqrt_prime_pow_div p r hp hr
  have hz : 0 ≤ (p : ℝ) ^ (-(3 / 2 : ℝ)) :=
    Real.rpow_nonneg hpR.le _
  have hC : 0 ≤ (((2 * r + 3 : ℕ) : ℝ)) := by positivity
  calc
    (4 / (p : ℝ) ^ (r + 1)) * fixedDepthBlockDiscrepancy r p =
        4 * (Real.sqrt (((p ^ (2 * r - 1) : ℕ) : ℝ)) /
          (p : ℝ) ^ (r + 1)) *
          (((2 * r + 3 : ℕ) : ℝ)) * (1 + Real.log p) *
            (3 + Real.log p) ^ (2 * r) := by
      rw [fixedDepthBlockDiscrepancy]
      ring
    _ = 4 * (p : ℝ) ^ (-(3 / 2 : ℝ)) *
          (((2 * r + 3 : ℕ) : ℝ)) * (1 + Real.log p) *
            (3 + Real.log p) ^ (2 * r) := by rw [hsqrt]
    _ ≤ 4 * (p : ℝ) ^ (-(3 / 2 : ℝ)) *
          (((2 * r + 3 : ℕ) : ℝ)) * (3 + Real.log p) *
            (3 + Real.log p) ^ (2 * r) := by
      gcongr
      norm_num
    _ = 4 * (((2 * r + 3 : ℕ) : ℝ)) *
          ((3 + Real.log p) ^ (2 * r + 1) *
            (p : ℝ) ^ (-(3 / 2 : ℝ))) := by
      rw [pow_succ]
      ring
    _ ≤ fixedDepthFourierErrorConstant r * fixedDepthFourierWeight r p := by
      rw [fixedDepthFourierErrorConstant, fixedDepthFourierWeight]
      have hpow : (2 : ℝ) ≤ 3 ^ (2 * r) := by
        calc
          (2 : ℝ) ≤ 3 ^ 2 := by norm_num
          _ ≤ 3 ^ (2 * r) := by
            exact pow_le_pow_right₀ (by norm_num) (by omega)
      have hfac : 4 * (((2 * r + 3 : ℕ) : ℝ)) ≤
          2 * (((2 * r + 3 : ℕ) : ℝ)) * 3 ^ (2 * r) := by
        nlinarith [mul_nonneg hC (sub_nonneg.mpr hpow)]
      exact mul_le_mul_of_nonneg_right hfac
        (mul_nonneg (pow_nonneg (by linarith) _) hz)

/-- Auditable normalized bridge for all complete blocks of one prime. -/
theorem fixedDepthCompleteBlocks_normalized_discrepancy_le
    {X p r : ℕ} (hp : 0 < p) (hX : 0 < X) (hr : 1 ≤ r)
    (hband : p ^ (r + 1) ≤ X) :
    ((((X / p + 1) / p ^ r : ℕ) : ℝ) *
        fixedDepthBlockDiscrepancy r p) / (X : ℝ) ≤
      fixedDepthFourierErrorConstant r * fixedDepthFourierWeight r p := by
  have hD := fixedDepthBlockDiscrepancy_nonneg r p
  calc
    ((((X / p + 1) / p ^ r : ℕ) : ℝ) *
          fixedDepthBlockDiscrepancy r p) / (X : ℝ) =
        ((((X / p + 1) / p ^ r : ℕ) : ℝ) / (X : ℝ)) *
          fixedDepthBlockDiscrepancy r p := by ring
    _ ≤ (2 / (p : ℝ) ^ (r + 1)) *
          fixedDepthBlockDiscrepancy r p :=
      mul_le_mul_of_nonneg_right
        (fixedDepthBlockCount_normalized_le hp hX hr hband) hD
    _ ≤ fixedDepthFourierErrorConstant r * fixedDepthFourierWeight r p :=
      fixedDepthBlockDiscrepancy_scaled_le hp hr

/-- Normalized complete-block discrepancy after the one-time ceiling loss in
`card_filter_range_cast_le_completeBlocks_add_terminal`. -/
theorem two_mul_fixedDepthCompleteBlocks_normalized_discrepancy_le
    {X p r : ℕ} (hp : 0 < p) (hX : 0 < X) (hr : 1 ≤ r)
    (hband : p ^ (r + 1) ≤ X) :
    2 * (((((X / p + 1) / p ^ r : ℕ) : ℝ) *
        fixedDepthBlockDiscrepancy r p) / (X : ℝ)) ≤
      fixedDepthFourierErrorConstant r * fixedDepthFourierWeight r p := by
  have hD := fixedDepthBlockDiscrepancy_nonneg r p
  calc
    2 * (((((X / p + 1) / p ^ r : ℕ) : ℝ) *
          fixedDepthBlockDiscrepancy r p) / (X : ℝ)) =
        (2 * ((((X / p + 1) / p ^ r : ℕ) : ℝ) / (X : ℝ))) *
          fixedDepthBlockDiscrepancy r p := by ring
    _ ≤ (4 / (p : ℝ) ^ (r + 1)) *
          fixedDepthBlockDiscrepancy r p := by
      apply mul_le_mul_of_nonneg_right _ hD
      have htwo := mul_le_mul_of_nonneg_left
        (fixedDepthBlockCount_normalized_le hp hX hr hband)
        (by norm_num : (0 : ℝ) ≤ 2)
      convert htwo using 1 <;> ring
    _ ≤ fixedDepthFourierErrorConstant r * fixedDepthFourierWeight r p :=
      fixedDepthBlockDiscrepancy_double_scaled_le hp hr

lemma eventually_three_add_log_pow_le_rpow (K : ℕ) :
    ∀ᶠ x : ℝ in atTop,
      (3 + Real.log x) ^ K ≤ x ^ (1 / 4 : ℝ) := by
  let A : ℝ := (2 : ℝ) ^ K
  have hA : 0 < A := by
    dsimp [A]
    positivity
  have hsmall :=
    (isLittleO_log_rpow_rpow_atTop (K : ℝ)
      (by norm_num : (0 : ℝ) < 1 / 4)).bound (inv_pos.mpr hA)
  filter_upwards [hsmall, Real.tendsto_log_atTop.eventually_ge_atTop 3,
      eventually_gt_atTop (0 : ℝ)] with x hx hlog hx0
  have hlog0 : 0 ≤ Real.log x := by linarith
  have hnormlog : ‖Real.log x ^ (K : ℝ)‖ = Real.log x ^ K := by
    rw [Real.rpow_natCast, Real.norm_of_nonneg (pow_nonneg hlog0 K)]
  have hnormx : ‖x ^ (1 / 4 : ℝ)‖ = x ^ (1 / 4 : ℝ) := by
    rw [Real.norm_of_nonneg (Real.rpow_nonneg hx0.le _)]
  rw [hnormlog, hnormx] at hx
  have hscaled : A * Real.log x ^ K ≤ x ^ (1 / 4 : ℝ) := by
    calc
      A * Real.log x ^ K ≤ A * (A⁻¹ * x ^ (1 / 4 : ℝ)) :=
        mul_le_mul_of_nonneg_left hx hA.le
      _ = x ^ (1 / 4 : ℝ) := by field_simp
  calc
    (3 + Real.log x) ^ K ≤ (2 * Real.log x) ^ K := by
      gcongr
      linarith
    _ = A * Real.log x ^ K := by rw [mul_pow]
    _ ≤ x ^ (1 / 4 : ℝ) := hscaled

/-- The logarithmic Fourier weight is eventually dominated by the summable
`p^(-5/4)` sequence. -/
theorem eventually_fixedDepthFourierWeight_le (r : ℕ) :
    ∀ᶠ p : ℕ in atTop,
      fixedDepthFourierWeight r p ≤ (p : ℝ) ^ (-(5 / 4 : ℝ)) := by
  have h := tendsto_natCast_atTop_atTop.eventually
    (eventually_three_add_log_pow_le_rpow (2 * r + 1))
  filter_upwards [h, eventually_gt_atTop (0 : ℕ)] with p hp hp0
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp0
  rw [fixedDepthFourierWeight]
  calc
    (3 + Real.log ↑p) ^ (2 * r + 1) * ↑p ^ (-(3 / 2 : ℝ)) ≤
        ↑p ^ (1 / 4 : ℝ) * ↑p ^ (-(3 / 2 : ℝ)) := by
      gcongr
    _ = ↑p ^ (-(5 / 4 : ℝ)) := by
      rw [← Real.rpow_add hpR]
      norm_num

lemma reciprocalFiveQuarter_summable :
    Summable (fun n : ℕ ↦ (n : ℝ) ^ (-(5 / 4 : ℝ))) :=
  Real.summable_nat_rpow.mpr (by norm_num)

/-- Tail of the summable `n^(-5/4)` comparison sequence. -/
def reciprocalFiveQuarterTail (L : ℕ) : ℝ :=
  ∑' k : ℕ, ((k + L + 1 : ℕ) : ℝ) ^ (-(5 / 4 : ℝ))

theorem tendsto_reciprocalFiveQuarterTail_zero :
    Tendsto reciprocalFiveQuarterTail atTop (𝓝 0) := by
  have h := tendsto_sum_nat_add
    (f := fun n : ℕ ↦ (n : ℝ) ^ (-(5 / 4 : ℝ)))
  have h' := h.comp (tendsto_add_atTop_nat 1)
  simpa only [reciprocalFiveQuarterTail, Nat.add_assoc] using! h'

theorem fixedDepthFourierBandError_nonneg (r X : ℕ) :
    0 ≤ fixedDepthFourierBandError r X := by
  apply Finset.sum_nonneg
  intro p _hp
  unfold fixedDepthFourierWeight
  exact mul_nonneg (pow_nonneg (by positivity) _)
    (Real.rpow_nonneg (Nat.cast_nonneg p) _)

theorem eventually_fixedDepthFourierBandError_le_tail (r : ℕ) :
    ∀ᶠ X : ℕ in atTop,
      fixedDepthFourierBandError r X ≤
        reciprocalFiveQuarterTail
          ⌊fixedDepthPrimeBandLower r (X : ℝ)⌋₊ := by
  have hweight := eventually_fixedDepthFourierWeight_le r
  rw [eventually_atTop] at hweight
  obtain ⟨N, hN⟩ := hweight
  filter_upwards
      [(tendsto_fixedDepthPrimeBandLowerFloor r).eventually_ge_atTop N]
      with X hL
  let L := ⌊fixedDepthPrimeBandLower r (X : ℝ)⌋₊
  let U := ⌊fixedDepthPrimeBandUpper r (X : ℝ)⌋₊
  calc
    fixedDepthFourierBandError r X =
        ∑ p ∈ fixedDepthPrimeSet r X, fixedDepthFourierWeight r p := rfl
    _ ≤ ∑ p ∈ fixedDepthPrimeSet r X,
          (p : ℝ) ^ (-(5 / 4 : ℝ)) := by
      apply Finset.sum_le_sum
      intro p hp
      have hp' := hp
      rw [fixedDepthPrimeSet, Finset.mem_filter, Finset.mem_Ioc] at hp'
      exact hN p (by omega)
    _ ≤ ∑ p ∈ Finset.Ioc L U,
          (p : ℝ) ^ (-(5 / 4 : ℝ)) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro p hp
        have hp' := hp
        rw [fixedDepthPrimeSet, Finset.mem_filter] at hp'
        simpa [L, U] using hp'.1
      · intro p _hp _hnot
        exact Real.rpow_nonneg (Nat.cast_nonneg p) _
    _ ≤ ∑' k : ℕ,
          ((k + L + 1 : ℕ) : ℝ) ^ (-(5 / 4 : ℝ)) :=
      sum_Ioc_le_tail
        (fun p ↦ Real.rpow_nonneg (Nat.cast_nonneg p) _)
        reciprocalFiveQuarter_summable L U
    _ = reciprocalFiveQuarterTail
        ⌊fixedDepthPrimeBandLower r (X : ℝ)⌋₊ := by rfl

/-- Equation (39): the normalized Fourier discrepancy summed over a fixed
depth band tends to zero. -/
theorem tendsto_fixedDepthFourierBandError_zero (r : ℕ) :
    Tendsto (fixedDepthFourierBandError r) atTop (𝓝 0) := by
  have htail := tendsto_reciprocalFiveQuarterTail_zero.comp
    (tendsto_fixedDepthPrimeBandLowerFloor r)
  apply squeeze_zero'
  · exact Eventually.of_forall (fixedDepthFourierBandError_nonneg r)
  · exact eventually_fixedDepthFourierBandError_le_tail r
  · exact htail

theorem tendsto_fixedDepthFourierError_zero (r : ℕ) :
    Tendsto (fixedDepthFourierError r) atTop (𝓝 0) := by
  simpa [fixedDepthFourierError] using!
    (tendsto_fixedDepthFourierBandError_zero r).const_mul
      (fixedDepthFourierErrorConstant r)

/-! ## Terminal blocks and the per-prime `+1` term -/

/-- Natural upper cutoff of the fixed-depth band. -/
def fixedDepthUpperCut (r X : ℕ) : ℕ :=
  ⌊fixedDepthPrimeBandUpper r (X : ℝ)⌋₊

theorem fixedDepthPrimeSet_card_le_upperCut (r X : ℕ) :
    (fixedDepthPrimeSet r X).card ≤ fixedDepthUpperCut r X := by
  calc
    (fixedDepthPrimeSet r X).card ≤
        (Finset.Ioc 0 (fixedDepthUpperCut r X)).card := by
      apply Finset.card_le_card
      intro p hp
      rw [fixedDepthPrimeSet, Finset.mem_filter, Finset.mem_Ioc] at hp
      rw [Finset.mem_Ioc]
      dsimp [fixedDepthUpperCut]
      omega
    _ = fixedDepthUpperCut r X := by simp

lemma card_filter_prime_Iic (n : ℕ) :
    ((Finset.Iic n).filter Nat.Prime).card = n.primeCounting := by
  simp only [Nat.primeCounting, Nat.primeCounting',
    Nat.count_eq_card_filter_range]
  congr 1
  ext p
  simp

theorem fixedDepthPrimeSet_card_le_primeCounting (r X : ℕ) :
    (fixedDepthPrimeSet r X).card ≤
      (fixedDepthUpperCut r X).primeCounting := by
  rw [← card_filter_prime_Iic]
  apply Finset.card_le_card
  intro p hp
  rw [fixedDepthPrimeSet, Finset.mem_filter, Finset.mem_Ioc] at hp
  rw [Finset.mem_filter, Finset.mem_Iic]
  exact ⟨hp.1.2, hp.2⟩

/-- The normalized sum of the terminal `p^r` blocks. -/
def fixedDepthTerminalBlockError (r X : ℕ) : ℝ :=
  (∑ p ∈ fixedDepthPrimeSet r X, (p : ℝ) ^ r) / (X : ℝ)

/-- The normalized count of one extra incomplete interval per prime. -/
def fixedDepthUnitError (r X : ℕ) : ℝ :=
  ((fixedDepthPrimeSet r X).card : ℝ) / (X : ℝ)

/-- Chebyshev majorant for the terminal-block error. -/
def fixedDepthTerminalChebyshevMajorant (r X : ℕ) : ℝ :=
  ((fixedDepthUpperCut r X).primeCounting : ℝ) /
    fixedDepthPrimeBandUpper r (X : ℝ)

theorem tendsto_fixedDepthUpper_div_self_zero
    (r : ℕ) (hr : 1 ≤ r) :
    Tendsto (fun X : ℕ ↦
      fixedDepthPrimeBandUpper r (X : ℝ) / (X : ℝ))
      atTop (𝓝 0) := by
  let b : ℝ := 1 - (((r + 1 : ℕ) : ℝ)⁻¹)
  have hb : 0 < b := by
    dsimp [b]
    apply sub_pos.mpr
    apply inv_lt_one_of_one_lt₀
    exact_mod_cast (show 1 < r + 1 by omega)
  have h := (tendsto_rpow_neg_atTop hb).comp tendsto_natCast_atTop_atTop
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with X hX
  have hXR : (0 : ℝ) < X := by exact_mod_cast hX
  change (X : ℝ) ^ (-b) =
    (X : ℝ) ^ (((r + 1 : ℕ) : ℝ)⁻¹) / X
  calc
    (X : ℝ) ^ (-b) =
        (X : ℝ) ^ ((((r + 1 : ℕ) : ℝ)⁻¹) - 1) := by
      congr 1
      dsimp [b]
      ring
    _ = (X : ℝ) ^ (((r + 1 : ℕ) : ℝ)⁻¹) / X := by
      simpa using
        Real.rpow_sub hXR (((r + 1 : ℕ) : ℝ)⁻¹) 1

theorem fixedDepthUnitError_nonneg (r X : ℕ) :
    0 ≤ fixedDepthUnitError r X := by
  unfold fixedDepthUnitError
  positivity

theorem fixedDepthUnitError_le_upper_div_self
    {r X : ℕ} (hX : 1 ≤ X) :
    fixedDepthUnitError r X ≤
      fixedDepthPrimeBandUpper r (X : ℝ) / (X : ℝ) := by
  have hXR : (0 : ℝ) < X := by positivity
  apply div_le_div_of_nonneg_right _ hXR.le
  calc
    ((fixedDepthPrimeSet r X).card : ℝ) ≤ fixedDepthUpperCut r X := by
      exact_mod_cast fixedDepthPrimeSet_card_le_upperCut r X
    _ ≤ fixedDepthPrimeBandUpper r (X : ℝ) := by
      exact Nat.floor_le (fixedDepthPrimeBandUpper_pos r (by positivity)).le

/-- The per-prime `+1` terms are `o(X)`. -/
theorem tendsto_fixedDepthUnitError_zero
    (r : ℕ) (hr : 1 ≤ r) :
    Tendsto (fixedDepthUnitError r) atTop (𝓝 0) := by
  apply squeeze_zero'
  · exact Eventually.of_forall (fixedDepthUnitError_nonneg r)
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with X hX
    exact fixedDepthUnitError_le_upper_div_self hX
  · exact tendsto_fixedDepthUpper_div_self_zero r hr

theorem fixedDepthTerminalBlockError_nonneg (r X : ℕ) :
    0 ≤ fixedDepthTerminalBlockError r X := by
  unfold fixedDepthTerminalBlockError
  positivity

/-- Exact finite form of the terminal-block estimate in equation (40). -/
theorem fixedDepthTerminalBlockError_le_Chebyshev
    {r X : ℕ} (hX : 1 ≤ X) :
    fixedDepthTerminalBlockError r X ≤
      fixedDepthTerminalChebyshevMajorant r X := by
  let u := fixedDepthPrimeBandUpper r (X : ℝ)
  let U := fixedDepthUpperCut r X
  have hXR : (0 : ℝ) < X := by positivity
  have hu0 : 0 < u := fixedDepthPrimeBandUpper_pos r hXR
  have hUu : (U : ℝ) ≤ u := by
    exact Nat.floor_le hu0.le
  have hsum :
      (∑ p ∈ fixedDepthPrimeSet r X, (p : ℝ) ^ r) ≤
        ((fixedDepthPrimeSet r X).card : ℝ) * u ^ r := by
    calc
      (∑ p ∈ fixedDepthPrimeSet r X, (p : ℝ) ^ r) ≤
          ∑ _p ∈ fixedDepthPrimeSet r X, u ^ r := by
        apply Finset.sum_le_sum
        intro p hp
        have hp' := hp
        rw [fixedDepthPrimeSet, Finset.mem_filter, Finset.mem_Ioc] at hp'
        apply pow_le_pow_left₀ (Nat.cast_nonneg p)
        exact (by exact_mod_cast hp'.1.2 : (p : ℝ) ≤ U) |>.trans hUu
      _ = ((fixedDepthPrimeSet r X).card : ℝ) * u ^ r := by simp
  have hcard : ((fixedDepthPrimeSet r X).card : ℝ) ≤
      ((fixedDepthUpperCut r X).primeCounting : ℝ) := by
    exact_mod_cast fixedDepthPrimeSet_card_le_primeCounting r X
  have hsum' :
      (∑ p ∈ fixedDepthPrimeSet r X, (p : ℝ) ^ r) ≤
        ((fixedDepthUpperCut r X).primeCounting : ℝ) * u ^ r :=
    hsum.trans (mul_le_mul_of_nonneg_right hcard (pow_nonneg hu0.le r))
  have huPow : u ^ (r + 1) = (X : ℝ) := by
    simpa [u, fixedDepthPrimeBandUpper] using
      (Real.rpow_inv_natCast_pow (x := (X : ℝ)) hXR.le
        (show r + 1 ≠ 0 by omega))
  unfold fixedDepthTerminalBlockError fixedDepthTerminalChebyshevMajorant
  change (∑ p ∈ fixedDepthPrimeSet r X, (p : ℝ) ^ r) / (X : ℝ) ≤
    ((fixedDepthUpperCut r X).primeCounting : ℝ) / u
  calc
    (∑ p ∈ fixedDepthPrimeSet r X, (p : ℝ) ^ r) / (X : ℝ) ≤
        (((fixedDepthUpperCut r X).primeCounting : ℝ) * u ^ r) /
          (X : ℝ) := div_le_div_of_nonneg_right hsum' hXR.le
    _ = ((fixedDepthUpperCut r X).primeCounting : ℝ) / u := by
      rw [← huPow, pow_succ]
      field_simp

/-- Chebyshev's upper bound implies `π(u)/u → 0` along the fixed-depth
upper cutoff. -/
theorem tendsto_fixedDepthTerminalChebyshevMajorant_zero (r : ℕ) :
    Tendsto (fixedDepthTerminalChebyshevMajorant r) atTop (𝓝 0) := by
  let C : ℝ := Real.log 4 + 1
  have hcheb :=
    Chebyshev.eventually_primeCounting_le (ε := (1 : ℝ)) one_pos
  have hcheb' :=
    (tendsto_fixedDepthPrimeBandUpper_nat r).eventually hcheb
  have hbound : ∀ᶠ X : ℕ in atTop,
      fixedDepthTerminalChebyshevMajorant r X ≤
        C / Real.log (fixedDepthPrimeBandUpper r (X : ℝ)) := by
    filter_upwards [hcheb',
      (tendsto_fixedDepthPrimeBandUpper_nat r).eventually_gt_atTop 1]
      with X hC hu
    have hu0 : 0 < fixedDepthPrimeBandUpper r (X : ℝ) :=
      zero_lt_one.trans hu
    change ((fixedDepthUpperCut r X).primeCounting : ℝ) /
      fixedDepthPrimeBandUpper r (X : ℝ) ≤ _
    have hC' : ((fixedDepthUpperCut r X).primeCounting : ℝ) ≤
        C * fixedDepthPrimeBandUpper r (X : ℝ) /
          Real.log (fixedDepthPrimeBandUpper r (X : ℝ)) := by
      simpa [fixedDepthUpperCut, C] using hC
    calc
      ((fixedDepthUpperCut r X).primeCounting : ℝ) /
          fixedDepthPrimeBandUpper r (X : ℝ) ≤
        (C * fixedDepthPrimeBandUpper r (X : ℝ) /
          Real.log (fixedDepthPrimeBandUpper r (X : ℝ))) /
          fixedDepthPrimeBandUpper r (X : ℝ) :=
        div_le_div_of_nonneg_right hC' hu0.le
      _ = C / Real.log (fixedDepthPrimeBandUpper r (X : ℝ)) := by
        field_simp
  have hright : Tendsto (fun X : ℕ ↦
      C / Real.log (fixedDepthPrimeBandUpper r (X : ℝ)))
      atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using
      ((Real.tendsto_log_atTop.comp
        (tendsto_fixedDepthPrimeBandUpper_nat r)).inv_tendsto_atTop.const_mul C)
  apply squeeze_zero'
  · exact Eventually.of_forall fun X ↦ by
      unfold fixedDepthTerminalChebyshevMajorant
      exact div_nonneg (Nat.cast_nonneg _)
        (Real.rpow_nonneg (Nat.cast_nonneg X) _)
  · exact hbound
  · exact hright

/-- Equation (40): terminal `p^r` blocks contribute `o(X)`. -/
theorem tendsto_fixedDepthTerminalBlockError_zero (r : ℕ) :
    Tendsto (fixedDepthTerminalBlockError r) atTop (𝓝 0) := by
  apply squeeze_zero'
  · exact Eventually.of_forall (fixedDepthTerminalBlockError_nonneg r)
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with X hX
    exact fixedDepthTerminalBlockError_le_Chebyshev hX
  · exact tendsto_fixedDepthTerminalChebyshevMajorant_zero r

/-! ## Combined analytic majorant and comparison interface -/

/-- Concrete normalized fixed-depth majorant corresponding to equation (38):
the relaxed box mass, the Fourier discrepancy, the terminal `p^r` blocks,
and one incomplete interval per prime. -/
def fixedDepthAnalyticMajorant (r X : ℕ) : ℝ :=
  (∑ p ∈ fixedDepthPrimeSet r X,
      relaxedDigitDensity r p / (p : ℝ)) +
    fixedDepthFourierError r X +
    fixedDepthTerminalBlockError r X +
    fixedDepthUnitError r X

/-- Equations (37)--(42): the complete fixed-depth analytic majorant tends
to `4⁻ʳ log ((r+2)/(r+1))`. -/
theorem tendsto_fixedDepthAnalyticMajorant
    (r : ℕ) (hr : 1 ≤ r) :
    Tendsto (fixedDepthAnalyticMajorant r) atTop
      (𝓝 (fixedDepthBaseDensity r * fixedDepthPrimeBandMainTerm r)) := by
  have h := (((tendsto_fixedDepthRelaxedPrimeMass r).add
    (tendsto_fixedDepthFourierError_zero r)).add
      (tendsto_fixedDepthTerminalBlockError_zero r)).add
        (tendsto_fixedDepthUnitError_zero r hr)
  simpa only [fixedDepthAnalyticMajorant, add_zero] using! h

/-- Quantified limsup form: any normalized count eventually dominated by the
concrete analytic majorant is eventually below the limiting constant plus an
arbitrary positive epsilon. -/
theorem eventually_le_limit_add_of_le_fixedDepthAnalyticMajorant
    {r : ℕ} (hr : 1 ≤ r) {f : ℕ → ℝ}
    (hdom : ∀ᶠ X : ℕ in atTop, f X ≤ fixedDepthAnalyticMajorant r X)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ X : ℕ in atTop,
      f X ≤ fixedDepthBaseDensity r * fixedDepthPrimeBandMainTerm r + ε := by
  have hupper := (tendsto_order.1
    (tendsto_fixedDepthAnalyticMajorant r hr)).2
      (fixedDepthBaseDensity r * fixedDepthPrimeBandMainTerm r + ε)
      (lt_add_of_pos_right _ hε)
  filter_upwards [hdom, hupper] with X hf hmajor
  exact hf.trans hmajor.le

/-- Literal limsup consumer.  The only non-analytic inputs are eventual
domination by the concrete majorant and the standard lower coboundedness of
the counted sequence (automatic for nonnegative normalized counts). -/
theorem limsup_le_of_le_fixedDepthAnalyticMajorant
    {r : ℕ} (hr : 1 ≤ r) {f : ℕ → ℝ}
    (hdom : ∀ᶠ X : ℕ in atTop, f X ≤ fixedDepthAnalyticMajorant r X)
    (hfCob : IsCoboundedUnder (· ≤ ·) atTop f) :
    limsup f atTop ≤
      fixedDepthBaseDensity r * fixedDepthPrimeBandMainTerm r := by
  have hlim := tendsto_fixedDepthAnalyticMajorant r hr
  calc
    limsup f atTop ≤ limsup (fixedDepthAnalyticMajorant r) atTop :=
      limsup_le_limsup hdom hfCob hlim.isBoundedUnder_le
    _ = fixedDepthBaseDensity r * fixedDepthPrimeBandMainTerm r :=
      hlim.limsup_eq

end

end FixedDepthDensity
end Erdos730
