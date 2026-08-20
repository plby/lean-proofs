import ErdosProblems.Erdos980.ElliottTail.OddInertFibreCover
import ErdosProblems.Erdos980.ElliottTail.OddRayNormRosser
import ErdosProblems.Erdos980.ElliottTail.OddRosserParameters

/-!
# Applying the norm Rosser sieve to one odd correction/unit fibre

This is the arithmetic specialization of `OddRayNormRosser`.  It constructs
the canonical fixed-ray candidate data and discharges the exact divisor-cell
identity, normalized main identity, tensor-cell cardinality, local root
bounds, ray/sieve coprimality, and the injection of surviving exceptional
conductors.  Only transparent numerical scale inequalities remain as inputs.
-/

open Filter
open MeasureTheory
open scoped BigOperators NumberField nonZeroDivisors

noncomputable section

namespace Erdos980.ElliottTail.OddInertOneCellApplication

open NumberField
open NumberField.mixedEmbedding
open IdealGeneratorCongruenceCount
open Erdos851.FiniteCombinatorialSieve
open Erdos851.BetaSieveFundamental
open Erdos387.GeneralBetaCutoff
open Erdos387.FiniteBetaSieveBridge
open RayNormPrimeSieve
open RayNormRemainder
open FixedRayCellCandidateData
open OddMediumParameters
open OddInertAuxiliaryPrimes
open OddInertTensorCells
open OddInertGeneratorMembership
open OddInertCandidateInjection
open OddInertFibreCover
open OddRayNormRosser
open OddRosserParameters
open RayPrincipalization
open RayPrincipalizationHeight

variable (ell : ℕ) [Fact ell.Prime]
variable (K : Type*) [Field K] [NumberField K]
  [IsCyclotomicExtension {ell} ℚ K]

/-- The exact tensor cell attached to a nonempty correction/unit fibre. -/
def oneTagRayAllowed
    {t x : ℕ} (Q : Finset ℕ)
    (hQ : Q ⊆ inertAuxiliaryPrimes ell t)
    (tag : CyclotomicRayCorrectionIndex ell K × UnitResidueImage ell K)
    (hcop : ∀ q ∈ Q, q.Coprime
      (Ideal.absNorm (tagCorrectionIdeal ell K tag : Ideal (𝓞 K))))
    (p₀ : ExceptionalPrime ell t x)
    (hp₀ : p₀ ∈ exceptionalGeneratorFiber ell K t x tag) :
    Finset (index K → ZMod (inertTensorModulus Q)) :=
  inertPowerClassCoordinateCell ell K Q
    (fun q hq ↦ inertAuxiliaryPrimes_prime ell (hQ hq))
    (tagCorrectionIdeal ell K tag) hcop
    (exceptionalBalancedPowerClassPattern ell K Q hQ tag hcop p₀ hp₀)

/-- The canonical norm-sieve data attached to the tensor cell of one tag. -/
def oneTagData
    {t x : ℕ} (Q : Finset ℕ) [NeZero (inertTensorModulus Q)]
    (hQ : Q ⊆ inertAuxiliaryPrimes ell t)
    (tag : CyclotomicRayCorrectionIndex ell K × UnitResidueImage ell K)
    (hcop : ∀ q ∈ Q, q.Coprime
      (Ideal.absNorm (tagCorrectionIdeal ell K tag : Ideal (𝓞 K))))
    (p₀ : ExceptionalPrime ell t x)
    (hp₀ : p₀ ∈ exceptionalGeneratorFiber ell K t x tag)
    (y : ℕ) (hx : 0 < x) :
    Data K (Candidate K (tagCorrectionIdeal ell K tag) (inertTensorModulus Q)
      (oneTagRayAllowed ell K Q hQ tag hcop p₀ hp₀)
      (exceptionalTagHeight ell K tag x)) :=
  canonicalData (K := K) (tagCorrectionIdeal ell K tag)
    (inertTensorModulus Q) (oneTagRayAllowed ell K Q hQ tag hcop p₀ hp₀)
    (exceptionalTagHeight ell K tag x) x
    (canonicalConductorNorm_le_x ell K tag (inertTensorModulus Q)
      (oneTagRayAllowed ell K Q hQ tag hcop p₀ hp₀) hx)
    (normSievePrimes K (tagCorrectionIdeal ell K tag)
      (inertTensorModulus Q) y)
    normSievePrimes_prime ell (oddTensorDepth t) (inertUnitResidueCount K Q)
    (fun p hp hd ↦ normSievePrimes_rootCount_pos
      (tagCorrectionIdeal ell K tag) (f := inertTensorModulus Q) (y := y) hp hd)
    (fun p hp hd ↦ normSievePrimes_rootCount_lt
      (tagCorrectionIdeal ell K tag) (f := inertTensorModulus Q) (y := y) hp hd)

/-- The exact ray-cell mass is bounded by the tensor density times the fixed
correction-ideal coefficient and the conductor cutoff.  This is the
normalization needed by the post-tensor norm-sieve main-term estimate. -/
theorem rayCellTotalMass_le_tensor_mul_coefficient
    {t x : ℕ} (Q : Finset ℕ) [NeZero (inertTensorModulus Q)]
    (hQ : Q ⊆ inertAuxiliaryPrimes ell t)
    (tag : CyclotomicRayCorrectionIndex ell K × UnitResidueImage ell K)
    (hcop : ∀ q ∈ Q, q.Coprime
      (Ideal.absNorm (tagCorrectionIdeal ell K tag : Ideal (𝓞 K))))
    (hx : 0 < x) :
    rayCellTotalMass (K := K) (tagCorrectionIdeal ell K tag)
      ell (oddTensorDepth t) (inertTensorModulus Q)
      (inertUnitResidueCount K Q) (exceptionalTagHeight ell K tag x) ≤
      ((ell : ℝ)⁻¹) ^ oddTensorDepth t *
        (generatorCellMainConstant K (tagCorrectionIdeal ell K tag) *
          Ideal.absNorm (tagCorrectionIdeal ell K tag : Ideal (𝓞 K))) *
        (x : ℝ) := by
  classical
  let f := inertTensorModulus Q
  let height := exceptionalTagHeight ell K tag x
  let J := tagCorrectionIdeal ell K tag
  have hf0 : f ≠ 0 := NeZero.ne _
  have hdegree : Module.finrank ℚ K = Nat.card (index K) := by
    rw [Nat.card_eq_fintype_card,
      ← Module.finrank_eq_card_basis (mixedEmbedding.stdBasis K),
      mixedEmbedding.finrank]
  have hunit : inertUnitResidueCount K Q ≤ f ^ Nat.card (index K) := by
    exact inertUnitResidueCount_le_fullCoordinateResidues ell K Q hQ J hcop
  have hdenpos : 0 < (f : ℝ) ^ Nat.card (index K) := by
    positivity
  have hunitCast : (inertUnitResidueCount K Q : ℝ) ≤
      (f : ℝ) ^ Nat.card (index K) := by
    exact_mod_cast hunit
  have hratio : (inertUnitResidueCount K Q : ℝ) /
      (f : ℝ) ^ Nat.card (index K) ≤ 1 :=
    (div_le_one hdenpos).2 hunitCast
  have hratio0 : 0 ≤ (inertUnitResidueCount K Q : ℝ) /
      (f : ℝ) ^ Nat.card (index K) := by positivity
  have hmain0 : 0 ≤ generatorCellMainConstant K J := by
    unfold generatorCellMainConstant
    exact div_nonneg measureReal_nonneg (abs_nonneg _)
  have hheight0 : 0 ≤ height ^ Nat.card (index K) :=
    pow_nonneg (exceptionalTagHeight_pos ell K tag hx).le _
  have hheightPow : height ^ Nat.card (index K) =
      ((x * Ideal.absNorm (J : Ideal (𝓞 K)) : ℕ) : ℝ) := by
    rw [← hdegree]
    exact exceptionalTagHeight_pow_finrank ell K tag hx
  change rayCellTotalMass (K := K) J ell (oddTensorDepth t) f
      (inertUnitResidueCount K Q) height ≤ _
  unfold rayCellTotalMass
  rw [show (ell : ℝ) ^ (- (oddTensorDepth t : ℤ)) =
      ((ell : ℝ)⁻¹) ^ oddTensorDepth t by
    simp only [zpow_neg, zpow_natCast, inv_pow]]
  calc
    ((ell : ℝ)⁻¹) ^ oddTensorDepth t *
          ((inertUnitResidueCount K Q : ℝ) /
            (f : ℝ) ^ Nat.card (index K)) *
          (generatorCellMainConstant K J *
            height ^ Nat.card (index K)) ≤
        ((ell : ℝ)⁻¹) ^ oddTensorDepth t * 1 *
          (generatorCellMainConstant K J *
            height ^ Nat.card (index K)) := by gcongr
    _ = ((ell : ℝ)⁻¹) ^ oddTensorDepth t *
        (generatorCellMainConstant K J *
          Ideal.absNorm (J : Ideal (𝓞 K))) * (x : ℝ) := by
      rw [hheightPow]
      push_cast
      ring

/-- The tag height dominates the pure conductor scale.  The correction
ideal contributes an integral norm at least one. -/
theorem rpow_le_exceptionalTagHeight
    (tag : CyclotomicRayCorrectionIndex ell K × UnitResidueImage ell K)
    {x : ℕ} (hx : 0 < x) :
    (x : ℝ) ^ ((Nat.card (index K) : ℝ)⁻¹) ≤
      exceptionalTagHeight ell K tag x := by
  classical
  have hdegree : Module.finrank ℚ K = Nat.card (index K) := by
    rw [Nat.card_eq_fintype_card,
      ← Module.finrank_eq_card_basis (mixedEmbedding.stdBasis K),
      mixedEmbedding.finrank]
  have hnorm : 1 ≤ Ideal.absNorm
      (tagCorrectionIdeal ell K tag : Ideal (𝓞 K)) :=
    Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
      (nonZeroDivisors.coe_ne_zero (tagCorrectionIdeal ell K tag)))
  unfold exceptionalTagHeight
  rw [hdegree]
  apply Real.rpow_le_rpow (by positivity) ?_ (by positivity)
  push_cast
  exact_mod_cast (show x ≤ x * Ideal.absNorm
    (tagCorrectionIdeal ell K tag : Ideal (𝓞 K)) by nlinarith)

/-- The codimension-one height power has the exact fixed-ideal coefficient
needed in the Rosser boundary estimate. -/
theorem exceptionalTagHeight_pow_pred_le
    (tag : CyclotomicRayCorrectionIndex ell K × UnitResidueImage ell K)
    {x : ℕ} (hx : 0 < x) :
    exceptionalTagHeight ell K tag x ^ (Nat.card (index K) - 1) ≤
      (Ideal.absNorm (tagCorrectionIdeal ell K tag : Ideal (𝓞 K)) : ℝ) *
        (x : ℝ) ^ (1 - (Nat.card (index K) : ℝ)⁻¹) := by
  classical
  let D := Nat.card (index K)
  let H := exceptionalTagHeight ell K tag x
  let N := Ideal.absNorm (tagCorrectionIdeal ell K tag : Ideal (𝓞 K))
  have hD : 0 < D := by
    exact normSieveDegree_pos K
  have hH : 0 < H := exceptionalTagHeight_pos ell K tag hx
  have hlow : (x : ℝ) ^ ((D : ℝ)⁻¹) ≤ H := by
    simpa only [D, H] using rpow_le_exceptionalTagHeight ell K tag hx
  have hpow : H ^ D = ((x * N : ℕ) : ℝ) := by
    dsimp only [H, N, D]
    have hdegree : Module.finrank ℚ K = Nat.card (index K) := by
      rw [Nat.card_eq_fintype_card,
        ← Module.finrank_eq_card_basis (mixedEmbedding.stdBasis K),
        mixedEmbedding.finrank]
    rw [← hdegree]
    exact exceptionalTagHeight_pow_finrank ell K tag hx
  have hfactor : H ^ (D - 1) * H = ((x * N : ℕ) : ℝ) := by
    rw [← hpow, ← pow_succ, Nat.sub_add_cancel hD]
  have hnonneg : 0 ≤ (N : ℝ) * (x : ℝ) ^ (1 - (D : ℝ)⁻¹) := by
    positivity
  have hmul := mul_le_mul_of_nonneg_left hlow hnonneg
  change H ^ (D - 1) ≤ (N : ℝ) * (x : ℝ) ^ (1 - (D : ℝ)⁻¹)
  have hmulAll : H ^ (D - 1) * H ≤
      ((N : ℝ) * (x : ℝ) ^ (1 - (D : ℝ)⁻¹)) * H := by
    calc
      H ^ (D - 1) * H = ((x * N : ℕ) : ℝ) := hfactor
      _ = (N : ℝ) * (x : ℝ) := by push_cast; ring
      _ = ((N : ℝ) * (x : ℝ) ^ (1 - (D : ℝ)⁻¹)) *
            (x : ℝ) ^ ((D : ℝ)⁻¹) := by
        rw [mul_assoc, ← Real.rpow_add (by positivity)]
        rw [show 1 - (D : ℝ)⁻¹ + (D : ℝ)⁻¹ = 1 by ring,
          Real.rpow_one]
      _ ≤ ((N : ℝ) * (x : ℝ) ^ (1 - (D : ℝ)⁻¹)) * H := hmul
  nlinarith

/-- Transport the numerical post-tensor main-term estimate to the literal
canonical `Data`.  The only subtlety is that the upper Rosser polynomial is
nonnegative on the selected prime list; this follows by restricting the
local density to that list and comparing with its nonnegative Euler
product. -/
theorem oneTagData_mainTerm_le_of_tensorWeighted
    {t x : ℕ} (Q : Finset ℕ) [NeZero (inertTensorModulus Q)]
    (hQ : Q ⊆ inertAuxiliaryPrimes ell t)
    (tag : CyclotomicRayCorrectionIndex ell K × UnitResidueImage ell K)
    (hcop : ∀ q ∈ Q, q.Coprime
      (Ideal.absNorm (tagCorrectionIdeal ell K tag : Ideal (𝓞 K))))
    (p₀ : ExceptionalPrime ell t x)
    (hp₀ : p₀ ∈ exceptionalGeneratorFiber ell K t x tag)
    (y S : ℕ) (hx : 0 < x) {B : ℝ}
    (hbase :
      (((ell : ℝ)⁻¹) ^ oddTensorDepth t *
          (generatorCellMainConstant K (tagCorrectionIdeal ell K tag) *
            Ideal.absNorm (tagCorrectionIdeal ell K tag : Ideal (𝓞 K))) *
          (x : ℝ)) *
        upperMainTerm (rosserStoppingPredicate (normRosserBeta K) (y ^ S))
          (coordinateNormDensity K (tagCorrectionIdeal ell K tag))
          (Erdos851.ascendingSievePrimes
            (normSieveLower K (tagCorrectionIdeal ell K tag)
              (inertTensorModulus Q)) y) ≤ B) :
    let D := oneTagData ell K Q hQ tag hcop p₀ hp₀ y hx
    D.totalMass *
        upperMainTerm (rosserStoppingPredicate (normRosserBeta K) (y ^ S))
          (fun p ↦ D.nu p) (RayNormPrimeSieve.ascendingSievePrimes D) ≤ B := by
  dsimp only
  let J := tagCorrectionIdeal ell K tag
  let f := inertTensorModulus Q
  let D := oneTagData ell K Q hQ tag hcop p₀ hp₀ y hx
  let P := Erdos851.ascendingSievePrimes (normSieveLower K J f) y
  have hP : RayNormPrimeSieve.ascendingSievePrimes D = P := by
    rfl
  have hnu : (fun p ↦ D.nu p) = coordinateNormDensity K J := by
    funext p
    rfl
  have hg0 : ∀ p, 0 ≤ coordinateNormDensity K J p :=
    coordinateNormDensity_nonneg K J
  have hg1 : ∀ p ∈ P, coordinateNormDensity K J p ≤ 1 := by
    intro p hp
    exact (coordinateNormDensity_lt_one J
      (by simpa only [normSievePrimes] using
        (Erdos851.mem_ascendingSievePrimes.mp hp))).le
  let g' : ℕ → ℝ := fun p ↦ if p ∈ P then coordinateNormDensity K J p else 0
  have hg' : ∀ p ∈ P, coordinateNormDensity K J p = g' p := by
    intro p hp
    simp only [g', hp, if_true]
  have hg0' : ∀ p, 0 ≤ g' p := by
    intro p
    dsimp only [g']
    split_ifs
    · exact hg0 p
    · exact le_rfl
  have hg1' : ∀ p, g' p ≤ 1 := by
    intro p
    dsimp only [g']
    split_ifs with hp
    · exact hg1 p hp
    · norm_num
  have heuler0 : 0 ≤ finiteEulerProduct g' P := by
    unfold finiteEulerProduct
    apply List.prod_nonneg
    intro a ha
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ha
    exact sub_nonneg.mpr (hg1' p)
  have hupper0 : 0 ≤ upperMainTerm
      (rosserStoppingPredicate (normRosserBeta K) (y ^ S))
      (coordinateNormDensity K J) P := by
    rw [Erdos851.upperMainTerm_congr_on _ _ g' P hg']
    exact heuler0.trans (euler_le_upperMainTerm _ _ hg0' hg1' P)
  have hmass := rayCellTotalMass_le_tensor_mul_coefficient
    ell K Q hQ tag hcop hx
  have hmul := mul_le_mul_of_nonneg_right hmass hupper0
  rw [hP, hnu]
  exact hmul.trans hbase

/-- Direct post-tensor form of the one-cell application.  Unlike the
logarithmic-modulus wrapper below, its main-term input has already absorbed
the tensor density and all lower-endpoint logarithms. -/
theorem exists_oneTag_surviving_card_bound_postTensor
    (hodd : Odd ell)
    (tag : CyclotomicRayCorrectionIndex ell K × UnitResidueImage ell K) :
    ∃ Cgeom : ℝ, 0 ≤ Cgeom ∧
      ∀ {t x : ℕ} (Q : Finset ℕ) [NeZero (inertTensorModulus Q)]
        (hQ : Q ⊆ inertAuxiliaryPrimes ell t)
        (hcop : ∀ q ∈ Q, q.Coprime
          (Ideal.absNorm (tagCorrectionIdeal ell K tag : Ideal (𝓞 K))))
        (hQcard : Q.card = oddTensorDepth t)
        (p₀ : ExceptionalPrime ell t x)
        (hp₀ : p₀ ∈ exceptionalGeneratorFiber ell K t x tag)
        (y S : ℕ) {eta C A E : ℝ} (hx : 1 < x),
        let f := inertTensorModulus Q
        let rayAllowed := oneTagRayAllowed ell K Q hQ tag hcop p₀ hp₀
        let height := exceptionalTagHeight ell K tag x
        let sievePrimes := normSievePrimes K (tagCorrectionIdeal ell K tag) f y
        let D := oneTagData ell K Q hQ tag hcop p₀ hp₀ y (by omega)
        normSieveLower K (tagCorrectionIdeal ell K tag) f ≤ y →
        ((f * y ^ S : ℕ) : ℝ) ≤ height →
        D.totalMass *
            upperMainTerm (rosserStoppingPredicate (normRosserBeta K) (y ^ S))
              (fun p ↦ D.nu p) (ascendingSievePrimes D) ≤
          A * ((x : ℝ) / Real.log (x : ℝ)) /
            (((t + 1 : ℕ) : ℝ) ^ 2) →
        (Cgeom * rayAllowed.card *
            (height / f) ^ (Nat.card (index K) - 1)) * (y ^ S) ≤
          C * (x : ℝ) ^
            (1 - (Nat.card (index K) : ℝ)⁻¹ + eta) →
        0 ≤ ((ascendingSievePrimes D).map
            fun p ↦ 1 + (Nat.card (index K) : ℝ) / p).prod →
        ((ascendingSievePrimes D).map
            fun p ↦ 1 + (Nat.card (index K) : ℝ) / p).prod ≤
          E * Real.log (x : ℝ) ^ (Nat.card (index K) : ℝ) →
        0 ≤ C → 0 ≤ A → 0 ≤ E →
        ((rationalSurvivingExceptionalGeneratorFiber ell K tag sievePrimes
          t x).card : ℝ) ≤
          A * ((x : ℝ) / Real.log (x : ℝ)) /
            (((t + 1 : ℕ) : ℝ) ^ 2) +
            realRosserCellEnvelope (Nat.card (index K))
              (Nat.card (index K)) eta (C * E) (x : ℝ) := by
  classical
  obtain ⟨Cgeom, hCgeom, hsift⟩ :=
    exists_fixedIdeal_oneCell_normSiftedMass_bound K
      (tagCorrectionIdeal ell K tag)
  refine ⟨Cgeom, hCgeom, ?_⟩
  intro t x Q _inst hQ hcop hQcard p₀ hp₀ y S eta C A E hx
  dsimp only
  intro hlow hheight hmainFinal hboundary hEuler0 hEuler hC hA hE
  let f := inertTensorModulus Q
  have hf0 : f ≠ 0 := NeZero.ne (inertTensorModulus Q)
  let rayAllowed := oneTagRayAllowed ell K Q hQ tag hcop p₀ hp₀
  let height := exceptionalTagHeight ell K tag x
  let sievePrimes := normSievePrimes K (tagCorrectionIdeal ell K tag) f y
  let R := canonicalGeneratorRealization (K := K)
    (tagCorrectionIdeal ell K tag) f rayAllowed height
  let D := oneTagData ell K Q hQ tag hcop p₀ hp₀ y (by omega)
  have hfprod : f.Coprime (sievePrimes.prod id) := by
    exact rayModulus_coprime_normSieveProduct
      (tagCorrectionIdeal ell K tag) hf0
  have hgood : ∀ p ∈ sievePrimes,
      p.Coprime (Ideal.absNorm
        (tagCorrectionIdeal ell K tag : Ideal (𝓞 K))) :=
    normSievePrimes_good_for_correction (tagCorrectionIdeal ell K tag) f y
  have hray : ell ^ oddTensorDepth t * rayAllowed.card =
      inertUnitResidueCount K Q := by
    dsimp only [rayAllowed]
    rw [← hQcard]
    exact ell_pow_mul_inertPowerClassCoordinateCell_card
      ell K Q hQ (tagCorrectionIdeal ell K tag) hcop _
  have hheight' : ∀ (d : ℕ) [NeZero d], d ∣ D.sievePrimes.prod id →
      d ≤ y ^ S → ((f * d : ℕ) : ℝ) ≤ height := by
    intro d _ _ hd
    exact height_condition_of_level_le hheight d hd
  have hdivisor : ∀ (d : ℕ) [NeZero d] [NeZero (f * d)]
      (hd : d ∣ D.sievePrimes.prod id),
      normDivisorMass D d =
        (allowedGeneratorResidueCellCount (tagCorrectionIdeal ell K tag)
          (f * d)
          (combinedCoordinateResidues K
            (Nat.Coprime.of_dvd_right hd hfprod) rayAllowed
            (normDivisibleResidues K d
              ((coordinateAlgebraNormResidueSystem K
                (tagCorrectionIdeal ell K tag)).normMod d))) height : ℕ) := by
    intro d _ _ hd
    let Ref := canonicalDivisorCellRefinement (K := K)
      (tagCorrectionIdeal ell K tag) f rayAllowed height R sievePrimes
      hfprod hgood
    simpa only [D, oneTagData, canonicalData, R, f, rayAllowed, height,
      sievePrimes] using
      data_normDivisorMass_eq_allowedGeneratorResidueCellCount
        (K := K) (tagCorrectionIdeal ell K tag) f rayAllowed height
        (fun k _ ↦ generatorCongruenceCell_inter_generatorNormRegion_finite
          (tagCorrectionIdeal ell K tag) f k height)
        R x (canonicalConductorNorm_le_x ell K tag f rayAllowed (by omega))
        sievePrimes normSievePrimes_prime ell (oddTensorDepth t)
        (inertUnitResidueCount K Q)
        (fun p hp hd ↦ normSievePrimes_rootCount_pos
          (tagCorrectionIdeal ell K tag) (f := f) (y := y) hp hd)
        (fun p hp hd ↦ normSievePrimes_rootCount_lt
          (tagCorrectionIdeal ell K tag) (f := f) (y := y) hp hd)
        hfprod Ref d hd
  have hmain : ∀ (d : ℕ) [NeZero d], d ∣ D.sievePrimes.prod id →
      D.nu d * D.totalMass =
        combinedRayUnitNormDensity K ell (oddTensorDepth t) f d
            (inertUnitResidueCount K Q)
            ((coordinateAlgebraNormResidueSystem K
              (tagCorrectionIdeal ell K tag)).normMod d) *
          (generatorCellMainConstant K (tagCorrectionIdeal ell K tag) *
            height ^ Nat.card (index K)) := by
    intro d _ _
    simpa only [D, oneTagData, canonicalData, R, f, rayAllowed, height,
      sievePrimes] using
      data_nu_mul_totalMass
        (K := K) (tagCorrectionIdeal ell K tag) f rayAllowed height
        (fun k _ ↦ generatorCongruenceCell_inter_generatorNormRegion_finite
          (tagCorrectionIdeal ell K tag) f k height)
        R x (canonicalConductorNorm_le_x ell K tag f rayAllowed (by omega))
        sievePrimes normSievePrimes_prime ell (oddTensorDepth t)
        (inertUnitResidueCount K Q)
        (fun p hp hd ↦ normSievePrimes_rootCount_pos
          (tagCorrectionIdeal ell K tag) (f := f) (y := y) hp hd)
        (fun p hp hd ↦ normSievePrimes_rootCount_lt
          (tagCorrectionIdeal ell K tag) (f := f) (y := y) hp hd) d
  have hfibre :
      ((rationalSurvivingExceptionalGeneratorFiber ell K tag sievePrimes
        t x).card : ℝ) ≤ normSiftedMass D := by
    rw [rationalSurvivingExceptionalGeneratorFiber_card ell K]
    exact survivingExceptionalGeneratorFiber_card_le_normSiftedMass
      ell K hodd Q hQ tag hcop p₀ hp₀ sievePrimes
      normSievePrimes_prime (oddTensorDepth t) (inertUnitResidueCount K Q)
      (fun p hp hd ↦ normSievePrimes_rootCount_pos
        (tagCorrectionIdeal ell K tag) (f := f) (y := y) hp hd)
      (fun p hp hd ↦ normSievePrimes_rootCount_lt
        (tagCorrectionIdeal ell K tag) (f := f) (y := y) hp hd) (by omega)
  have hy : 1 ≤ y := by
    have hdim := two_le_normSieveDimension K
    have hlower := two_mul_dimension_le_lower K
      (tagCorrectionIdeal ell K tag) f
    exact (show 1 ≤ normSieveLower K (tagCorrectionIdeal ell K tag) f by
      omega).trans hlow
  have hsift' := hsift D rayAllowed height (Fact.out : ell.Prime).ne_zero
    hf0 hfprod hgood hray (normRosserBeta_pos K)
    (normRosserLevel_pos (K := K) hy) hheight' hdivisor hmain
  have hx0 : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
  have hboundaryCast :
      (Cgeom * rayAllowed.card *
          (height / f) ^ (Nat.card (index K) - 1)) *
          ((y ^ S : ℕ) : ℝ) ≤
        C * (x : ℝ) ^
          (1 - (Nat.card (index K) : ℝ)⁻¹ + eta) := by
    simpa only [Nat.cast_pow] using hboundary
  have hboundaryFinal :
      (Cgeom * rayAllowed.card *
          (height / f) ^ (Nat.card (index K) - 1)) *
          ((y ^ S : ℕ) : ℝ) *
            ((ascendingSievePrimes D).map
              fun p ↦ 1 + (Nat.card (index K) : ℝ) / p).prod ≤
        realRosserCellEnvelope (Nat.card (index K))
          (Nat.card (index K)) eta (C * E) (x : ℝ) := by
    calc
      _ ≤ (C * (x : ℝ) ^
          (1 - (Nat.card (index K) : ℝ)⁻¹ + eta)) *
            (E * Real.log (x : ℝ) ^ (Nat.card (index K) : ℝ)) :=
        mul_le_mul hboundaryCast hEuler hEuler0
          (mul_nonneg hC (Real.rpow_nonneg hx0.le _))
      _ = realRosserCellEnvelope (Nat.card (index K))
          (Nat.card (index K)) eta (C * E) (x : ℝ) := by
        unfold realRosserCellEnvelope
        ring
  exact hfibre.trans <| hsift'.trans <|
    add_le_add hmainFinal hboundaryFinal

/-- One nonempty correction/unit fibre satisfies the logarithmic-modulus
Rosser estimate once the remaining numerical scale inequalities are
supplied.  All arithmetic and geometric realization hypotheses of the
generic sieve are discharged here. -/
theorem exists_oneTag_surviving_card_bound
    (hodd : Odd ell)
    (tag : CyclotomicRayCorrectionIndex ell K × UnitResidueImage ell K) :
    ∃ Cgeom : ℝ, 0 ≤ Cgeom ∧
      ∀ {t x : ℕ} (Q : Finset ℕ) [NeZero (inertTensorModulus Q)]
        (hQ : Q ⊆ inertAuxiliaryPrimes ell t)
        (hcop : ∀ q ∈ Q, q.Coprime
          (Ideal.absNorm (tagCorrectionIdeal ell K tag : Ideal (𝓞 K))))
        (hQcard : Q.card = oddTensorDepth t)
        (p₀ : ExceptionalPrime ell t x)
        (hp₀ : p₀ ∈ exceptionalGeneratorFiber ell K t x tag)
        (y S : ℕ) {eta C A : ℝ} (hx : 1 < x),
        let f := inertTensorModulus Q
        let rayAllowed := oneTagRayAllowed ell K Q hQ tag hcop p₀ hp₀
        let height := exceptionalTagHeight ell K tag x
        let sievePrimes := normSievePrimes K (tagCorrectionIdeal ell K tag) f y
        let D := oneTagData ell K Q hQ tag hcop p₀ hp₀ y (by omega)
        f ≤ (t + 1) ^ oddTensorDepth t →
        normSieveLower K (tagCorrectionIdeal ell K tag) f ≤ y →
        ((f * y ^ S : ℕ) : ℝ) ≤ height →
        D.totalMass *
            upperMainTerm (rosserStoppingPredicate (normRosserBeta K) (y ^ S))
              (fun p ↦ D.nu p) (ascendingSievePrimes D) ≤
          A * ((ell : ℝ)⁻¹) ^ oddTensorDepth t * Real.log (f : ℝ) *
            ((x : ℝ) / Real.log (x : ℝ)) →
        (Cgeom * rayAllowed.card *
            (height / f) ^ (Nat.card (index K) - 1)) * (y ^ S) ≤
          C * (x : ℝ) ^
            (1 - (Nat.card (index K) : ℝ)⁻¹ + eta) →
        0 ≤ ((ascendingSievePrimes D).map
            fun p ↦ 1 + (Nat.card (index K) : ℝ) / p).prod →
        ((ascendingSievePrimes D).map
            fun p ↦ 1 + (Nat.card (index K) : ℝ) / p).prod ≤
          Real.log (x : ℝ) ^ (Nat.card (index K) : ℝ) →
        0 ≤ C → 0 ≤ A →
        ((rationalSurvivingExceptionalGeneratorFiber ell K tag sievePrimes
          t x).card : ℝ) ≤
          (4 * A) * ((x : ℝ) / Real.log (x : ℝ)) /
              (((t + 1 : ℕ) : ℝ) ^ 2) +
            realRosserCellEnvelope (Nat.card (index K))
              (Nat.card (index K)) eta C (x : ℝ) := by
  classical
  obtain ⟨Cgeom, hCgeom, hcell⟩ :=
    exists_fixedIdeal_oneCell_exceptional_card_bound_logModulus K
      (tagCorrectionIdeal ell K tag)
  refine ⟨Cgeom, hCgeom, ?_⟩
  intro t x Q _inst hQ hcop hQcard p₀ hp₀ y S eta C A hx
  dsimp only
  intro hfmodulus hlow hheight hmainScale hboundary hEuler0 hEuler hC hA
  let f := inertTensorModulus Q
  have hf0 : f ≠ 0 := by
    exact NeZero.ne (inertTensorModulus Q)
  let rayAllowed := oneTagRayAllowed ell K Q hQ tag hcop p₀ hp₀
  let height := exceptionalTagHeight ell K tag x
  let sievePrimes := normSievePrimes K (tagCorrectionIdeal ell K tag) f y
  let R := canonicalGeneratorRealization (K := K)
    (tagCorrectionIdeal ell K tag) f rayAllowed height
  let D := oneTagData ell K Q hQ tag hcop p₀ hp₀ y (by omega)
  have hfprod : f.Coprime (sievePrimes.prod id) := by
    exact rayModulus_coprime_normSieveProduct
      (tagCorrectionIdeal ell K tag) hf0
  have hgood : ∀ p ∈ sievePrimes,
      p.Coprime (Ideal.absNorm
        (tagCorrectionIdeal ell K tag : Ideal (𝓞 K))) :=
    normSievePrimes_good_for_correction (tagCorrectionIdeal ell K tag) f y
  have hray : ell ^ oddTensorDepth t * rayAllowed.card =
      inertUnitResidueCount K Q := by
    dsimp only [rayAllowed]
    rw [← hQcard]
    exact ell_pow_mul_inertPowerClassCoordinateCell_card
      ell K Q hQ (tagCorrectionIdeal ell K tag) hcop _
  have hheight' : ∀ (d : ℕ) [NeZero d], d ∣ D.sievePrimes.prod id →
      d ≤ y ^ S → ((f * d : ℕ) : ℝ) ≤ height := by
    intro d _ _ hd
    exact height_condition_of_level_le hheight d hd
  have hdivisor : ∀ (d : ℕ) [NeZero d] [NeZero (f * d)]
      (hd : d ∣ D.sievePrimes.prod id),
      normDivisorMass D d =
        (allowedGeneratorResidueCellCount (tagCorrectionIdeal ell K tag)
          (f * d)
          (combinedCoordinateResidues K
            (Nat.Coprime.of_dvd_right hd hfprod) rayAllowed
            (normDivisibleResidues K d
              ((coordinateAlgebraNormResidueSystem K
                (tagCorrectionIdeal ell K tag)).normMod d))) height : ℕ) := by
    intro d _ _ hd
    let Ref := canonicalDivisorCellRefinement (K := K)
      (tagCorrectionIdeal ell K tag) f rayAllowed height R sievePrimes
      hfprod hgood
    simpa only [D, oneTagData, canonicalData, R, f, rayAllowed, height,
      sievePrimes] using
      data_normDivisorMass_eq_allowedGeneratorResidueCellCount
        (K := K) (tagCorrectionIdeal ell K tag) f rayAllowed height
        (fun k _ ↦ generatorCongruenceCell_inter_generatorNormRegion_finite
          (tagCorrectionIdeal ell K tag) f k height)
        R x (canonicalConductorNorm_le_x ell K tag f rayAllowed (by omega))
        sievePrimes normSievePrimes_prime ell (oddTensorDepth t)
        (inertUnitResidueCount K Q)
        (fun p hp hd ↦ normSievePrimes_rootCount_pos
          (tagCorrectionIdeal ell K tag) (f := f) (y := y) hp hd)
        (fun p hp hd ↦ normSievePrimes_rootCount_lt
          (tagCorrectionIdeal ell K tag) (f := f) (y := y) hp hd)
        hfprod Ref d hd
  have hmain : ∀ (d : ℕ) [NeZero d], d ∣ D.sievePrimes.prod id →
      D.nu d * D.totalMass =
        combinedRayUnitNormDensity K ell (oddTensorDepth t) f d
            (inertUnitResidueCount K Q)
            ((coordinateAlgebraNormResidueSystem K
              (tagCorrectionIdeal ell K tag)).normMod d) *
          (generatorCellMainConstant K (tagCorrectionIdeal ell K tag) *
            height ^ Nat.card (index K)) := by
    intro d _ _
    simpa only [D, oneTagData, canonicalData, R, f, rayAllowed, height,
      sievePrimes] using
      data_nu_mul_totalMass
        (K := K) (tagCorrectionIdeal ell K tag) f rayAllowed height
        (fun k _ ↦ generatorCongruenceCell_inter_generatorNormRegion_finite
          (tagCorrectionIdeal ell K tag) f k height)
        R x (canonicalConductorNorm_le_x ell K tag f rayAllowed (by omega))
        sievePrimes normSievePrimes_prime ell (oddTensorDepth t)
        (inertUnitResidueCount K Q)
        (fun p hp hd ↦ normSievePrimes_rootCount_pos
          (tagCorrectionIdeal ell K tag) (f := f) (y := y) hp hd)
        (fun p hp hd ↦ normSievePrimes_rootCount_lt
          (tagCorrectionIdeal ell K tag) (f := f) (y := y) hp hd) d
  have hfibre :
      ((rationalSurvivingExceptionalGeneratorFiber ell K tag sievePrimes
        t x).card : ℝ) ≤ normSiftedMass D := by
    rw [rationalSurvivingExceptionalGeneratorFiber_card ell K]
    exact survivingExceptionalGeneratorFiber_card_le_normSiftedMass
      ell K hodd Q hQ tag hcop p₀ hp₀ sievePrimes
      normSievePrimes_prime (oddTensorDepth t) (inertUnitResidueCount K Q)
      (fun p hp hd ↦ normSievePrimes_rootCount_pos
        (tagCorrectionIdeal ell K tag) (f := f) (y := y) hp hd)
      (fun p hp hd ↦ normSievePrimes_rootCount_lt
        (tagCorrectionIdeal ell K tag) (f := f) (y := y) hp hd) (by omega)
  have hy : 1 ≤ y := by
    have hdim := two_le_normSieveDimension K
    have hlower := two_mul_dimension_le_lower K
      (tagCorrectionIdeal ell K tag) f
    exact (show 1 ≤ normSieveLower K (tagCorrectionIdeal ell K tag) f by
      omega).trans hlow
  have hboundary' :
      (Cgeom * rayAllowed.card *
          (height / f) ^ (Nat.card (index K) - 1)) * (y ^ S) ≤
        C * (x : ℝ) ^
          (1 - (Nat.card (index K) : ℝ)⁻¹ + eta) := by
    simpa only [f, rayAllowed, height, Nat.cast_pow] using hboundary
  have hboundaryCast :
      (Cgeom * rayAllowed.card *
          (height / f) ^ (Nat.card (index K) - 1)) *
          ((y ^ S : ℕ) : ℝ) ≤
        C * (x : ℝ) ^
          (1 - (Nat.card (index K) : ℝ)⁻¹ + eta) := by
    simpa only [Nat.cast_pow] using hboundary'
  exact hcell (ell := ell) (j := oddTensorDepth t) (f := f)
    (unitResidueCount := inertUnitResidueCount K Q)
    (β := normRosserBeta K) (level := y ^ S) (x := x) (t := t)
    (eta := eta) (C := C) (A := A)
    D rayAllowed height (Fact.out : ell.Prime).two_le hf0 hx
    hfmodulus hfprod hgood hray rfl (normRosserBeta_pos K)
    (normRosserLevel_pos (K := K) hy) hheight' hdivisor hmain
    _ hfibre hmainScale hboundaryCast hEuler0 hEuler hC hA

end Erdos980.ElliottTail.OddInertOneCellApplication
