import ErdosProblems.Erdos980.ElliottTail.OddInertFibreCover
import ErdosProblems.Erdos980.ElliottTail.OddRosserParameters

/-!
# The finite rational-prime loss in the odd norm sieve

The norm sieve omits the exceptional conductors which are themselves sieve
primes.  In each fixed correction/unit tag this loses at most the number of
rational primes below the moving endpoint.  Since the tag set is finite, the
total loss is `O(x^eta)`, and hence is absorbed by the Rosser cell envelope.
-/

open Filter
open scoped BigOperators NumberField nonZeroDivisors Topology

noncomputable section

namespace Erdos980.ElliottTail.OddFiniteLossEstimate

open NumberField
open OddInertFibreCover
open OddInertGeneratorMembership
open OddMediumParameters
open OddRosserParameters
open RayPrincipalization
open RayPrincipalizationHeight

variable (ell : ℕ) [Fact ell.Prime]
variable (K : Type*) [Field K] [NumberField K]
  [IsCyclotomicExtension {ell} ℚ K]

/-- The loss set obtained when every correction/unit tag uses its own
concrete ray modulus and the common moving norm-sieve upper endpoint. -/
def rationalExceptionalNormSieveLossTotalByTag
    (eta : ℝ)
    (f : CyclotomicRayCorrectionIndex ell K × UnitResidueImage ell K → ℕ)
    (t x : ℕ) : Finset ℕ :=
  rationalExceptionalSieveLossTotal ell K
    (fun tag ↦ normSievePrimes K (tagCorrectionIdeal ell K tag) (f tag)
      (normSieveUpper eta x)) t x

/-- Constant-ray-modulus specialization retained for consumers which use a
single auxiliary modulus in every correction/unit tag. -/
def rationalExceptionalNormSieveLossTotal
    (eta : ℝ) (f t x : ℕ) : Finset ℕ :=
  rationalExceptionalNormSieveLossTotalByTag ell K eta (fun _ ↦ f) t x

/-- A uniform envelope coefficient for all correction/unit tags. -/
def oddFiniteLossConstant : ℝ :=
  2 * ((exceptionalTagIndices ell K).card : ℝ)

theorem oddFiniteLossConstant_nonneg :
    0 ≤ oddFiniteLossConstant ell K := by
  unfold oddFiniteLossConstant
  positivity

/-- The concrete rational sieve interval contains at most `y` elements. -/
theorem normSievePrimes_card_le_upper
    (J : (Ideal (RingOfIntegers K))⁰) (f y : ℕ) :
    (normSievePrimes K J f y).card ≤ y := by
  classical
  have hsubset : normSievePrimes K J f y ⊆ Finset.Icc 1 y := by
    intro p hp
    have hp' := mem_normSievePrimes.mp hp
    exact Finset.mem_Icc.mpr ⟨hp'.2.2.pos, hp'.2.1⟩
  calc
    (normSievePrimes K J f y).card ≤ (Finset.Icc 1 y).card :=
      Finset.card_le_card hsubset
    _ ≤ y := by simp

/-- Before passing to real asymptotics, the total loss for arbitrary
tag-dependent ray moduli is bounded by the number of tags times the common
sieve endpoint. -/
theorem rationalExceptionalNormSieveLossTotalByTag_card_le
    (eta : ℝ)
    (f : CyclotomicRayCorrectionIndex ell K × UnitResidueImage ell K → ℕ)
    (t x : ℕ) :
    (rationalExceptionalNormSieveLossTotalByTag ell K eta f t x).card ≤
      (exceptionalTagIndices ell K).card * normSieveUpper eta x := by
  classical
  unfold rationalExceptionalNormSieveLossTotalByTag
  calc
    (rationalExceptionalSieveLossTotal ell K
        (fun tag ↦ normSievePrimes K (tagCorrectionIdeal ell K tag) (f tag)
          (normSieveUpper eta x)) t x).card ≤
        ∑ tag ∈ exceptionalTagIndices ell K,
          (normSievePrimes K (tagCorrectionIdeal ell K tag) (f tag)
            (normSieveUpper eta x)).card :=
      rationalExceptionalSieveLossTotal_card_le_sum ell K _ t x
    _ ≤ ∑ _tag ∈ exceptionalTagIndices ell K, normSieveUpper eta x := by
      exact Finset.sum_le_sum fun tag _ ↦
        normSievePrimes_card_le_upper K (tagCorrectionIdeal ell K tag) (f tag)
          (normSieveUpper eta x)
    _ = (exceptionalTagIndices ell K).card * normSieveUpper eta x := by
      rw [Finset.sum_const]
      simp [mul_comm]

/-- Constant-modulus form of
`rationalExceptionalNormSieveLossTotalByTag_card_le`. -/
theorem rationalExceptionalNormSieveLossTotal_card_le
    (eta : ℝ) (f t x : ℕ) :
    (rationalExceptionalNormSieveLossTotal ell K eta f t x).card ≤
      (exceptionalTagIndices ell K).card * normSieveUpper eta x := by
  simpa only [rationalExceptionalNormSieveLossTotal] using
    rationalExceptionalNormSieveLossTotalByTag_card_le ell K eta
      (fun _ ↦ f) t x

/-- Uniformly in the smoothness layer and the ray modulus, the complete
finite sieve-prime loss is eventually absorbed by one Rosser cell envelope.

The proof only needs `eta ≥ 0`; in the final application `eta` is chosen
positive and smaller than the reciprocal number-field degree. -/
theorem eventually_rationalExceptionalNormSieveLossTotalByTag_card_le_envelope
    {eta : ℝ} (heta : 0 ≤ eta) :
    ∀ᶠ x : ℕ in atTop, ∀ t : ℕ, t ≤ smoothParameterY x →
      ∀ f : CyclotomicRayCorrectionIndex ell K × UnitResidueImage ell K → ℕ,
      ((rationalExceptionalNormSieveLossTotalByTag ell K eta f t x).card : ℝ) ≤
        realRosserCellEnvelope (normSieveDegree K) (normSieveDegree K)
          eta (oddFiniteLossConstant ell K) (x : ℝ) := by
  have hlogTop :
      Tendsto (fun x : ℕ ↦ Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlogLarge : ∀ᶠ x : ℕ in atTop, (1 : ℝ) ≤ Real.log (x : ℝ) :=
    hlogTop.eventually (eventually_ge_atTop 1)
  filter_upwards [hlogLarge, eventually_ge_atTop 1] with x hlog hx
  intro t _ht f
  let tags := (exceptionalTagIndices ell K).card
  let y := normSieveUpper eta x
  have hcardNat :
      (rationalExceptionalNormSieveLossTotalByTag ell K eta f t x).card ≤
        tags * y := by
    simpa only [tags, y] using
      rationalExceptionalNormSieveLossTotalByTag_card_le ell K eta f t x
  have hcardReal :
      ((rationalExceptionalNormSieveLossTotalByTag ell K eta f t x).card : ℝ) ≤
        (tags : ℝ) * (y : ℝ) := by
    exact_mod_cast hcardNat
  have hy : (y : ℝ) ≤ 2 * (x : ℝ) ^ eta := by
    simpa only [y] using normSieveUpper_cast_le_two_mul_rpow heta hx
  have hrNat : 0 < normSieveDegree K := normSieveDegree_pos K
  have hrReal : (1 : ℝ) ≤ (normSieveDegree K : ℝ) := by
    exact_mod_cast hrNat
  have hinv : ((normSieveDegree K : ℝ))⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ hrReal
  have hexponent :
      eta ≤ 1 - ((normSieveDegree K : ℝ))⁻¹ + eta := by
    linarith
  have hxReal : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
  have hrpow :
      (x : ℝ) ^ eta ≤
        (x : ℝ) ^ (1 - ((normSieveDegree K : ℝ))⁻¹ + eta) :=
    Real.rpow_le_rpow_of_exponent_le hxReal hexponent
  have hlogpow :
      (1 : ℝ) ≤ Real.log (x : ℝ) ^ (normSieveDegree K : ℝ) :=
    Real.one_le_rpow hlog (by positivity)
  have hconstant : 0 ≤ oddFiniteLossConstant ell K :=
    oddFiniteLossConstant_nonneg ell K
  calc
    ((rationalExceptionalNormSieveLossTotalByTag ell K eta f t x).card : ℝ) ≤
        (tags : ℝ) * (y : ℝ) := hcardReal
    _ ≤ (tags : ℝ) * (2 * (x : ℝ) ^ eta) :=
      mul_le_mul_of_nonneg_left hy (by positivity)
    _ = oddFiniteLossConstant ell K * (x : ℝ) ^ eta := by
      unfold oddFiniteLossConstant
      dsimp only [tags]
      ring
    _ ≤ oddFiniteLossConstant ell K *
        (x : ℝ) ^ (1 - ((normSieveDegree K : ℝ))⁻¹ + eta) :=
      mul_le_mul_of_nonneg_left hrpow hconstant
    _ ≤ oddFiniteLossConstant ell K *
          (x : ℝ) ^ (1 - ((normSieveDegree K : ℝ))⁻¹ + eta) *
        Real.log (x : ℝ) ^ (normSieveDegree K : ℝ) := by
      exact le_mul_of_one_le_right
        (mul_nonneg hconstant (Real.rpow_nonneg (by positivity) _)) hlogpow
    _ = realRosserCellEnvelope (normSieveDegree K) (normSieveDegree K)
        eta (oddFiniteLossConstant ell K) (x : ℝ) := by
      rfl

/-- Constant-modulus form of the eventual finite-loss envelope. -/
theorem eventually_rationalExceptionalNormSieveLossTotal_card_le_envelope
    {eta : ℝ} (heta : 0 ≤ eta) :
    ∀ᶠ x : ℕ in atTop, ∀ t : ℕ, t ≤ smoothParameterY x → ∀ f : ℕ,
      ((rationalExceptionalNormSieveLossTotal ell K eta f t x).card : ℝ) ≤
        realRosserCellEnvelope (normSieveDegree K) (normSieveDegree K)
          eta (oddFiniteLossConstant ell K) (x : ℝ) := by
  filter_upwards
    [eventually_rationalExceptionalNormSieveLossTotalByTag_card_le_envelope
      ell K heta]
    with x hx
  intro t ht f
  simpa only [rationalExceptionalNormSieveLossTotal] using
    hx t ht (fun _ ↦ f)

end Erdos980.ElliottTail.OddFiniteLossEstimate
