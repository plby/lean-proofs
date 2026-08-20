import ErdosProblems.Erdos980.ElliottTail.OddInertOneCellApplication
import ErdosProblems.Erdos980.ElliottTail.OddFilteredInertPrimes
import ErdosProblems.Erdos980.ElliottTail.OddAuxiliaryScale
import ErdosProblems.Erdos980.ElliottTail.OddFiniteLossEstimate
import ErdosProblems.Erdos980.ElliottTail.OddFiniteFibreAssembly
import ErdosProblems.Erdos980.ElliottTail.CumulativeCutoffWrapper

/-!
# The odd-prime medium estimate

This file makes the final uniform parameter choice, selects the inert
auxiliary primes separately for every correction/unit tag, applies the
fixed-ray norm Rosser sieve to every surviving tag fibre, sums the finite
cover, absorbs the sieve-prime loss and the lattice envelopes, and exports
the unconditional odd-prime endpoint.
-/

open Filter
open scoped BigOperators NumberField nonZeroDivisors Topology

noncomputable section

namespace Erdos980.ElliottTail.OddPrimeMediumApplication

open NumberField NumberField.mixedEmbedding
open Erdos851.FiniteCombinatorialSieve
open RayNormPrimeSieve
open RayNormRemainder
open OddMediumParameters
open OddRosserParameters
open OddAuxiliaryScale
open OddFilteredInertPrimes
open OddInertAuxiliaryPrimes
open OddInertTensorCells
open OddInertGeneratorMembership
open OddInertCandidateInjection
open OddInertFibreCover
open OddInertOneCellApplication
open OddFiniteLossEstimate
open OddFiniteFibreAssembly
open RayPrincipalization
open RayPrincipalizationHeight

variable (ell : ℕ) [Fact ell.Prime]
variable (K : Type*) [Field K] [NumberField K]
  [IsCyclotomicExtension {ell} ℚ K]

/-- The canonical depth-sized inert family for one correction tag. -/
def tagAuxiliaryPrimes
    (tag : CyclotomicRayCorrectionIndex ell K × UnitResidueImage ell K)
    (t : ℕ) : Finset ℕ :=
  selectedCoprimeInertAuxiliaryPrimes ell
    (tagCorrectionIdeal ell K tag : Ideal (𝓞 K)) t

/-- The scalar CRT modulus belonging to the selected tag family. -/
def tagTensorModulus
    (tag : CyclotomicRayCorrectionIndex ell K × UnitResidueImage ell K)
    (t : ℕ) : ℕ :=
  inertTensorModulus (tagAuxiliaryPrimes ell K tag t)

/-- The concrete norm-sieve interval for one tag. -/
def tagNormSievePrimes
    (eta : ℝ)
    (tag : CyclotomicRayCorrectionIndex ell K × UnitResidueImage ell K)
    (t x : ℕ) : Finset ℕ :=
  normSievePrimes K (tagCorrectionIdeal ell K tag)
    (tagTensorModulus ell K tag t) (normSieveUpper eta x)

/-- Rational exceptional conductors in one tag which survive its own norm
sieve. -/
def tagSurvivingFibre
    (eta : ℝ)
    (tag : CyclotomicRayCorrectionIndex ell K × UnitResidueImage ell K)
    (t x : ℕ) : Finset ℕ :=
  rationalSurvivingExceptionalGeneratorFiber ell K tag
    (tagNormSievePrimes ell K eta tag t x) t x

/-- The union of the tag-dependent sieve-prime losses. -/
def tagSieveLoss (eta : ℝ) (t x : ℕ) : Finset ℕ :=
  rationalExceptionalNormSieveLossTotalByTag ell K eta
    (fun tag ↦ tagTensorModulus ell K tag t) t x

theorem tagAuxiliaryPrimes_subset
    (tag : CyclotomicRayCorrectionIndex ell K × UnitResidueImage ell K)
    (t : ℕ) :
    tagAuxiliaryPrimes ell K tag t ⊆ inertAuxiliaryPrimes ell t :=
  selectedCoprimeInertAuxiliaryPrimes_subset ell
    (tagCorrectionIdeal ell K tag : Ideal (𝓞 K)) t

theorem tagAuxiliaryPrime_coprime_absNorm
    (tag : CyclotomicRayCorrectionIndex ell K × UnitResidueImage ell K)
    {t q : ℕ} (hq : q ∈ tagAuxiliaryPrimes ell K tag t) :
    q.Coprime
      (Ideal.absNorm (tagCorrectionIdeal ell K tag : Ideal (𝓞 K))) :=
  selectedCoprimeInertAuxiliaryPrimes_coprime_absNorm ell hq

theorem tagTensorModulus_ne_zero
    (tag : CyclotomicRayCorrectionIndex ell K × UnitResidueImage ell K)
    (t : ℕ) : tagTensorModulus ell K tag t ≠ 0 := by
  unfold tagTensorModulus inertTensorModulus
  apply Finset.prod_ne_zero_iff.mpr
  intro q hq
  exact (selectedCoprimeInertAuxiliaryPrimes_prime ell q.2).ne_zero

theorem tagTensorModulus_le_auxiliaryBound
    (tag : CyclotomicRayCorrectionIndex ell K × UnitResidueImage ell K)
    (t : ℕ) :
    tagTensorModulus ell K tag t ≤ (t + 1) ^ oddTensorDepth t := by
  calc
    tagTensorModulus ell K tag t ≤ oddAuxiliaryModulusBound t := by
      change (∏ q : selectedCoprimeInertAuxiliaryPrimes ell
        (tagCorrectionIdeal ell K tag : Ideal (𝓞 K)) t, q.1) ≤
          oddAuxiliaryModulusBound t
      have h := selectedCoprimeInertAuxiliaryPrimes_prod_le_modulusBound ell
        (tagCorrectionIdeal ell K tag : Ideal (𝓞 K)) t
      rw [← Finset.prod_attach] at h
      simpa only [Finset.attach_eq_univ, id_eq] using h
    _ ≤ (t + 1) ^ oddTensorDepth t := by
      unfold oddAuxiliaryModulusBound
      exact Nat.pow_le_pow_left (by omega) _

theorem eventually_tagAuxiliaryPrimes_card
    (tag : CyclotomicRayCorrectionIndex ell K × UnitResidueImage ell K) :
    ∀ᶠ t : ℕ in atTop,
      (tagAuxiliaryPrimes ell K tag t).card = oddTensorDepth t := by
  exact eventually_selectedCoprimeInertAuxiliaryPrimes_card ell
    (tagCorrectionIdeal ell K tag : Ideal (𝓞 K))
    (nonZeroDivisors.coe_ne_zero (tagCorrectionIdeal ell K tag))

theorem exceptionalPrimes_subset_tagSieveLoss_union_tagSurvivingFibres
    (eta : ℝ) (t x : ℕ) :
    exceptionalPrimes ell t x ⊆
      tagSieveLoss ell K eta t x ∪
        (exceptionalTagIndices ell K).biUnion
          (fun tag ↦ tagSurvivingFibre ell K eta tag t x) := by
  simpa only [tagSieveLoss, tagSurvivingFibre, tagNormSievePrimes,
    rationalExceptionalNormSieveLossTotalByTag] using
    exceptionalPrimes_subset_loss_union_survivingFibres ell K
      (fun tag ↦ normSievePrimes K (tagCorrectionIdeal ell K tag)
        (tagTensorModulus ell K tag t) (normSieveUpper eta x)) t x

/-- One fixed correction/unit tag has an eventual inverse-square Rosser
bound above a fixed tensor-availability threshold. -/
theorem exists_eventually_tagSurvivingFibre_bound
    (hodd : Odd ell) (hdegree : 2 ≤ normSieveDegree K)
    {eta delta : ℝ} {S W : ℕ}
    (heta : 0 < eta) (hdelta : 0 < delta) (heta1 : eta ≤ 1)
    (hgap : delta + eta * S < (normSieveDegree K : ℝ)⁻¹)
    (tag : CyclotomicRayCorrectionIndex ell K × UnitResidueImage ell K)
    (A E : ℝ) (hA : 0 ≤ A) (hE : 1 ≤ E)
    (hmain : ∀ᶠ t : ℕ in atTop, ∀ f : ℕ, f ≠ 0 →
      f ≤ (t + 1) ^ oddTensorDepth t →
      ∀ x : ℕ, 1 < x → W ≤ normSieveUpper eta x + 1 →
        normSieveLower K (tagCorrectionIdeal ell K tag) f ≤
          normSieveUpper eta x →
        (((ell : ℝ)⁻¹) ^ oddTensorDepth t *
              (generatorCellMainConstant K (tagCorrectionIdeal ell K tag) *
                Ideal.absNorm
                  (tagCorrectionIdeal ell K tag : Ideal (𝓞 K))) *
              (x : ℝ)) *
            upperMainTerm
              (rosserStoppingPredicate (normRosserBeta K)
                (normSieveUpper eta x ^ S))
              (coordinateNormDensity K (tagCorrectionIdeal ell K tag))
              (Erdos851.ascendingSievePrimes
                (normSieveLower K (tagCorrectionIdeal ell K tag) f)
                (normSieveUpper eta x)) ≤
          A * ((x : ℝ) / Real.log (x : ℝ)) /
            (((t + 1 : ℕ) : ℝ) ^ 2))
    (hEuler : ∀ (J : (Ideal (RingOfIntegers K))⁰) (f x : ℕ) (eta : ℝ),
      0 < eta → eta ≤ 1 → 1 < x →
      normSieveLower K J f ≤ normSieveUpper eta x →
      ((Erdos851.ascendingSievePrimes (normSieveLower K J f)
        (normSieveUpper eta x)).map
        (fun p : ℕ ↦ 1 + (normSieveDegree K : ℝ) / p)).prod ≤
          E * Real.log (x : ℝ) ^ normSieveDimension K) :
    ∃ T : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ x : ℕ in atTop, ∀ t : ℕ,
        T ≤ t → t ≤ smoothParameterY x →
        ((tagSurvivingFibre ell K eta tag t x).card : ℝ) ≤
          A * ((x : ℝ) / Real.log (x : ℝ)) /
              (((t + 1 : ℕ) : ℝ) ^ 2) +
            realRosserCellEnvelope (normSieveDegree K)
              (normSieveDegree K) (delta + eta * S) C (x : ℝ) := by
  classical
  obtain ⟨Cgeom, hCgeom, hcell⟩ :=
    exists_oneTag_surviving_card_bound_postTensor ell K hodd tag
  let N : ℝ := Ideal.absNorm
    (tagCorrectionIdeal ell K tag : Ideal (𝓞 K))
  let L : ℝ := (2 : ℝ) ^ S
  let C : ℝ := Cgeom * N * L * E
  have hN : 0 ≤ N := by positivity
  have hL : 0 ≤ L := by positivity
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  have htogether : ∀ᶠ t : ℕ in atTop,
      (tagAuxiliaryPrimes ell K tag t).card = oddTensorDepth t ∧
      (∀ f : ℕ, f ≠ 0 → f ≤ (t + 1) ^ oddTensorDepth t →
        ∀ x : ℕ, 1 < x → W ≤ normSieveUpper eta x + 1 →
          normSieveLower K (tagCorrectionIdeal ell K tag) f ≤
            normSieveUpper eta x →
          (((ell : ℝ)⁻¹) ^ oddTensorDepth t *
                (generatorCellMainConstant K (tagCorrectionIdeal ell K tag) *
                  Ideal.absNorm
                    (tagCorrectionIdeal ell K tag : Ideal (𝓞 K))) *
                (x : ℝ)) *
              upperMainTerm
                (rosserStoppingPredicate (normRosserBeta K)
                  (normSieveUpper eta x ^ S))
                (coordinateNormDensity K (tagCorrectionIdeal ell K tag))
                (Erdos851.ascendingSievePrimes
                  (normSieveLower K (tagCorrectionIdeal ell K tag) f)
                  (normSieveUpper eta x)) ≤
            A * ((x : ℝ) / Real.log (x : ℝ)) /
              (((t + 1 : ℕ) : ℝ) ^ 2)) :=
    (eventually_tagAuxiliaryPrimes_card ell K tag).and hmain
  obtain ⟨T, hT⟩ := (eventually_atTop.1 htogether)
  have hheightEvent := eventually_uniform_normRosser_height_condition
    (normSieveDegree_pos K) hdelta heta.le S 1 zero_lt_one hgap
  have hlevelEvent :=
    eventually_uniform_auxiliary_mul_normSieveLevel_le_rpow
      hdelta heta.le S
  have hlowerEvent :=
    eventually_normSieveLower_le_normSieveUpper_of_auxiliaryModulus K
      (tagCorrectionIdeal ell K tag) heta
  have hWEvent : ∀ᶠ x : ℕ in atTop, W ≤ normSieveUpper eta x + 1 :=
    by
      filter_upwards
          [(tendsto_normSieveUpper_atTop heta).eventually
            (eventually_ge_atTop W)] with x hx
      omega
  refine ⟨T, C, hC, ?_⟩
  filter_upwards [hheightEvent, hlevelEvent, hlowerEvent, hWEvent,
    eventually_ge_atTop 2] with x hxheight hxlevel hxlower hxW hx2
  intro t htT htY
  let Q := tagAuxiliaryPrimes ell K tag t
  let f := inertTensorModulus Q
  have hf0 : f ≠ 0 := by
    simpa only [f, Q, tagTensorModulus, tagAuxiliaryPrimes] using
      tagTensorModulus_ne_zero ell K tag t
  letI : NeZero f := ⟨hf0⟩
  have hQ : Q ⊆ inertAuxiliaryPrimes ell t :=
    tagAuxiliaryPrimes_subset ell K tag t
  have hcop : ∀ q ∈ Q, q.Coprime
      (Ideal.absNorm (tagCorrectionIdeal ell K tag : Ideal (𝓞 K))) :=
    fun q hq ↦ tagAuxiliaryPrime_coprime_absNorm ell K tag hq
  have hfmod : f ≤ (t + 1) ^ oddTensorDepth t :=
    by simpa only [f, Q, tagTensorModulus] using
      tagTensorModulus_le_auxiliaryBound ell K tag t
  have hQt := hT t htT
  have hQcard : Q.card = oddTensorDepth t := hQt.1
  let y := normSieveUpper eta x
  let sievePrimes := normSievePrimes K (tagCorrectionIdeal ell K tag) f y
  let rawFibre := survivingExceptionalGeneratorFiber ell K (t := t) (x := x)
    tag sievePrimes
  by_cases hraw : rawFibre.Nonempty
  · obtain ⟨p₀, hp₀survive⟩ := hraw
    have hp₀ : p₀ ∈ exceptionalGeneratorFiber ell K t x tag :=
      ((mem_survivingExceptionalGeneratorFiber
        (ell := ell) (K := K)).mp hp₀survive).1
    have hx : 1 < x := by omega
    have hlow : normSieveLower K (tagCorrectionIdeal ell K tag) f ≤ y :=
      hxlower t htY f hfmod
    have hheight : ((f * y ^ S : ℕ) : ℝ) ≤
        exceptionalTagHeight ell K tag x := by
      have hh := hxheight t htY f hfmod
      exact hh.trans (by
        simpa only [one_mul, normSieveDegree] using
          rpow_le_exceptionalTagHeight ell K tag (by omega))
    have hmainBase := hQt.2 f hf0 hfmod x hx hxW hlow
    have hmainFinal := oneTagData_mainTerm_le_of_tensorWeighted
      ell K Q hQ tag hcop p₀ hp₀ y S (by omega) hmainBase
    let rayAllowed := oneTagRayAllowed ell K Q hQ tag hcop p₀ hp₀
    have hrayCard : rayAllowed.card ≤ f ^ normSieveDegree K := by
      simpa only [normSieveDegree] using
        rayAllowed_card_le_fullCoordinateResidues K f rayAllowed
    have hheightPow : exceptionalTagHeight ell K tag x ^
          (normSieveDegree K - 1) ≤
        N * (x : ℝ) ^ (1 - (normSieveDegree K : ℝ)⁻¹) := by
      simpa only [normSieveDegree, N] using
        exceptionalTagHeight_pow_pred_le ell K tag (by omega)
    have hlevel : ((f * y ^ S : ℕ) : ℝ) ≤
        L * (x : ℝ) ^ (delta + eta * S) := by
      simpa only [y, f, L] using hxlevel t htY f hfmod
    have hboundary :
        (Cgeom * rayAllowed.card *
            (exceptionalTagHeight ell K tag x / f) ^
              (normSieveDegree K - 1)) * (y ^ S) ≤
          (Cgeom * N * L) *
            (x : ℝ) ^
              (1 - (normSieveDegree K : ℝ)⁻¹ + (delta + eta * S)) := by
      simpa only [Nat.cast_pow] using
        normRosser_boundary_scale_le (normSieveDegree_pos K) hf0
        (exceptionalTagHeight_pos ell K tag (by omega)).le hCgeom
        hheightPow hN hrayCard hlevel hL (by positivity)
    let D := oneTagData ell K Q hQ tag hcop p₀ hp₀ y (by omega)
    have hDprimes : RayNormPrimeSieve.ascendingSievePrimes D =
        Erdos851.ascendingSievePrimes
          (normSieveLower K (tagCorrectionIdeal ell K tag) f) y := by
      rfl
    have hEuler0 : 0 ≤
        ((RayNormPrimeSieve.ascendingSievePrimes D).map
          fun p : ℕ ↦ 1 + (Nat.card (index K) : ℝ) / (p : ℝ)).prod := by
      rw [hDprimes]
      simpa only [normSieveDegree] using
        normSieve_endpointEuler_nonneg K (tagCorrectionIdeal ell K tag) f y
    have hdim : normSieveDimension K = normSieveDegree K := by
      unfold normSieveDimension
      exact max_eq_right hdegree
    have hEulerBound :
        ((RayNormPrimeSieve.ascendingSievePrimes D).map
          fun p : ℕ ↦ 1 + (Nat.card (index K) : ℝ) / (p : ℝ)).prod ≤
            E * Real.log (x : ℝ) ^ (Nat.card (index K) : ℝ) := by
      have he := hEuler (tagCorrectionIdeal ell K tag) f x eta
        heta heta1 hx hlow
      rw [hDprimes]
      simpa only [normSieveDegree, hdim, Real.rpow_natCast] using he
    have hEuler0' : 0 ≤
        (((RayNormPrimeSieve.ascendingSievePrimes D).map
          fun p : ℕ ↦ (p : ℝ)).map
            fun p : ℝ ↦ 1 + (Nat.card (index K) : ℝ) / p).prod := by
      simpa only [List.map_map, Function.comp_def] using hEuler0
    have hEulerBound' :
        (((RayNormPrimeSieve.ascendingSievePrimes D).map
          fun p : ℕ ↦ (p : ℝ)).map
            fun p : ℝ ↦ 1 + (Nat.card (index K) : ℝ) / p).prod ≤
          E * Real.log (x : ℝ) ^ (Nat.card (index K) : ℝ) := by
      simpa only [List.map_map, Function.comp_def] using hEulerBound
    have hcastList :
        List.flatMap (fun p : ℕ ↦ [(p : ℝ)])
            (RayNormPrimeSieve.ascendingSievePrimes D) =
          (RayNormPrimeSieve.ascendingSievePrimes D).map
            (fun p : ℕ ↦ (p : ℝ)) := by
      induction RayNormPrimeSieve.ascendingSievePrimes D with
      | nil => rfl
      | cons p ps ih => simp only [List.flatMap_cons, List.singleton_append,
          List.map_cons, ih]
    have hcellBound := hcell Q hQ hcop hQcard p₀ hp₀ y S hx hlow
      hheight hmainFinal (eta := delta + eta * S)
      (C := Cgeom * N * L) (A := A) (E := E)
      (by simpa only [normSieveDegree, rayAllowed, y, f] using hboundary)
      (by
        change 0 ≤
          ((List.flatMap (fun p : ℕ ↦ [(p : ℝ)])
            (RayNormPrimeSieve.ascendingSievePrimes D)).map
              fun p : ℝ ↦ 1 + (Nat.card (index K) : ℝ) / p).prod
        rw [hcastList]
        exact hEuler0')
      (by
        change
          ((List.flatMap (fun p : ℕ ↦ [(p : ℝ)])
            (RayNormPrimeSieve.ascendingSievePrimes D)).map
              fun p : ℝ ↦ 1 + (Nat.card (index K) : ℝ) / p).prod ≤
            E * Real.log (x : ℝ) ^ (Nat.card (index K) : ℝ)
        rw [hcastList]
        exact hEulerBound')
      (by positivity) hA (zero_le_one.trans hE)
    simpa only [tagSurvivingFibre, tagNormSievePrimes, tagTensorModulus,
      f, Q, y, sievePrimes, C, mul_assoc, normSieveDegree] using hcellBound
  · have hrawEmpty : rawFibre = ∅ := Finset.not_nonempty_iff_eq_empty.mp hraw
    have hleft : (tagSurvivingFibre ell K eta tag t x).card = 0 := by
      rw [tagSurvivingFibre, tagNormSievePrimes,
        rationalSurvivingExceptionalGeneratorFiber_card]
      change rawFibre.card = 0
      simp only [hrawEmpty, Finset.card_empty]
    rw [hleft]
    have hxlog : 0 < Real.log (x : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < x by omega))
    have hscale : 0 ≤ (x : ℝ) / Real.log (x : ℝ) := by positivity
    have henv : 0 ≤ realRosserCellEnvelope (normSieveDegree K)
        (normSieveDegree K) (delta + eta * S) C (x : ℝ) := by
      unfold realRosserCellEnvelope
      positivity
    have hmain0 : 0 ≤ A * ((x : ℝ) / Real.log (x : ℝ)) /
        (((t + 1 : ℕ) : ℝ) ^ 2) := by positivity
    simpa only [Nat.cast_zero] using add_nonneg hmain0 henv

/-- Threshold-aware finite-fibre assembly.  The individual auxiliary-prime
families need only have reached their prescribed cardinality above their own
fixed threshold; summing those thresholds produces one cutoff that works for
the whole finite correction cover. -/
theorem eventually_exceptional_card_le_tagEnvelope_above
    {ι : Type*}
    (indices : Finset ι) (threshold : ι → ℕ)
    (fibre : ι → ℕ → ℕ → Finset ℕ)
    (finiteLoss : ℕ → ℕ → Finset ℕ)
    {r k : ℕ} {eta lossConstant : ℝ}
    (mainConstant errorConstant : ι → ℝ)
    (hcover : ∀ x t : ℕ,
      exceptionalPrimes ell t x ⊆
        finiteLoss t x ∪ indices.biUnion (fun i ↦ fibre i t x))
    (hloss : ∀ᶠ x : ℕ in atTop,
      ∀ t : ℕ, t ≤ smoothParameterY x →
        ((finiteLoss t x).card : ℝ) ≤
          realRosserCellEnvelope r k eta lossConstant (x : ℝ))
    (hfibre : ∀ i ∈ indices, ∀ᶠ x : ℕ in atTop,
      ∀ t : ℕ, threshold i ≤ t → t ≤ smoothParameterY x →
        ((fibre i t x).card : ℝ) ≤
          mainConstant i * ((x : ℝ) / Real.log (x : ℝ)) /
              (((t + 1 : ℕ) : ℝ) ^ 2) +
            realRosserCellEnvelope r k eta (errorConstant i) (x : ℝ)) :
    ∀ᶠ x : ℕ in atTop, ∀ t : ℕ,
      (∑ i ∈ indices, threshold i) ≤ t → t ≤ smoothParameterY x →
      ((exceptionalPrimes ell t x).card : ℝ) ≤
        finiteFibreMainConstant indices mainConstant *
              ((x : ℝ) / Real.log (x : ℝ)) /
              (((t + 1 : ℕ) : ℝ) ^ 2) +
          realRosserCellEnvelope r k eta
            (finiteFibreErrorConstantWithLoss indices errorConstant
              lossConstant) (x : ℝ) := by
  classical
  have hall := (Finset.eventually_all indices).2 hfibre
  filter_upwards [hall, hloss] with x hx hxloss
  intro t htThreshold htY
  have hcardNat :
      (exceptionalPrimes ell t x).card ≤
        (finiteLoss t x).card + ∑ i ∈ indices, (fibre i t x).card := by
    calc
      (exceptionalPrimes ell t x).card ≤
          (finiteLoss t x ∪ indices.biUnion (fun i ↦ fibre i t x)).card :=
        Finset.card_le_card (hcover x t)
      _ ≤ (finiteLoss t x).card +
          (indices.biUnion (fun i ↦ fibre i t x)).card :=
        Finset.card_union_le _ _
      _ ≤ (finiteLoss t x).card +
          ∑ i ∈ indices, (fibre i t x).card :=
        Nat.add_le_add_left Finset.card_biUnion_le _
  have hcardReal :
      ((exceptionalPrimes ell t x).card : ℝ) ≤
        ((finiteLoss t x).card : ℝ) +
          ∑ i ∈ indices, ((fibre i t x).card : ℝ) := by
    exact_mod_cast hcardNat
  have hfibreSum :
      (∑ i ∈ indices, ((fibre i t x).card : ℝ)) ≤
        ∑ i ∈ indices,
          (mainConstant i * ((x : ℝ) / Real.log (x : ℝ)) /
              (((t + 1 : ℕ) : ℝ) ^ 2) +
            realRosserCellEnvelope r k eta (errorConstant i) (x : ℝ)) := by
    apply Finset.sum_le_sum
    intro i hi
    have hti : threshold i ≤ t :=
      (Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) hi).trans htThreshold
    exact hx i hi t hti htY
  calc
    ((exceptionalPrimes ell t x).card : ℝ) ≤
        ((finiteLoss t x).card : ℝ) +
          ∑ i ∈ indices, ((fibre i t x).card : ℝ) := hcardReal
    _ ≤ realRosserCellEnvelope r k eta lossConstant (x : ℝ) +
        ∑ i ∈ indices,
          (mainConstant i * ((x : ℝ) / Real.log (x : ℝ)) /
              (((t + 1 : ℕ) : ℝ) ^ 2) +
            realRosserCellEnvelope r k eta
              (errorConstant i) (x : ℝ)) :=
      add_le_add (hxloss t htY) hfibreSum
    _ = finiteFibreMainConstant indices mainConstant *
              ((x : ℝ) / Real.log (x : ℝ)) /
              (((t + 1 : ℕ) : ℝ) ^ 2) +
          realRosserCellEnvelope r k eta
            (finiteFibreErrorConstantWithLoss indices errorConstant
              lossConstant) (x : ℝ) := by
      rw [Finset.sum_add_distrib]
      have hmainSum :
          (∑ i ∈ indices,
              mainConstant i * ((x : ℝ) / Real.log (x : ℝ)) /
                (((t + 1 : ℕ) : ℝ) ^ 2)) =
            finiteFibreMainConstant indices mainConstant *
                ((x : ℝ) / Real.log (x : ℝ)) /
                (((t + 1 : ℕ) : ℝ) ^ 2) := by
        unfold finiteFibreMainConstant
        rw [← Finset.sum_div, Finset.sum_mul]
      have herrorSum :
          (∑ i ∈ indices,
              realRosserCellEnvelope r k eta
                (errorConstant i) (x : ℝ)) =
            realRosserCellEnvelope r k eta
              (finiteFibreErrorConstant indices errorConstant) (x : ℝ) := by
        unfold finiteFibreErrorConstant realRosserCellEnvelope
        rw [Finset.sum_mul, Finset.sum_mul]
      rw [hmainSum, herrorSum]
      unfold finiteFibreErrorConstantWithLoss realRosserCellEnvelope
      ring

/-- Above a fixed tensor-availability threshold, the little-oh lattice
envelope can be paid for by one further inverse-square main-term unit. -/
theorem eventually_inverseSquare_tail_of_tagEnvelope_above
    (T r k : ℕ) {eta C A : ℝ} (hr : 0 < r)
    (heta : eta < (r : ℝ)⁻¹) (hC : 0 ≤ C)
    (hrosser : ∀ᶠ x : ℕ in atTop, ∀ t : ℕ,
      T ≤ t → t ≤ smoothParameterY x →
      ((exceptionalPrimes ell t x).card : ℝ) ≤
        A * ((x : ℝ) / Real.log (x : ℝ)) /
            (((t + 1 : ℕ) : ℝ) ^ 2) +
          realRosserCellEnvelope r k eta C (x : ℝ)) :
    ∀ᶠ x : ℕ in atTop, ∀ t : ℕ,
      T ≤ t → t ≤ smoothParameterY x →
      ((exceptionalPrimes ell t x).card : ℝ) ≤
        (x : ℝ) / Real.log (x : ℝ) *
          inverseSquareMajorant (A + 1) t := by
  have herr := rosserCellEnvelope_mul_smoothCutoff_sq_isLittleO
    (r := r) (k := k) (eta := eta) (C := C) hr heta
  have herrBound := herr.bound (show (0 : ℝ) < 1 by norm_num)
  filter_upwards [hrosser, herrBound, eventually_ge_atTop 2]
      with x hxrosser hxerr hx2
  intro t htT htY
  have hlog : 0 < Real.log (x : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < x by omega))
  have hscale : 0 ≤ (x : ℝ) / Real.log (x : ℝ) := by positivity
  have hE : 0 ≤ realRosserCellEnvelope r k eta C (x : ℝ) := by
    unfold realRosserCellEnvelope
    positivity
  have hYsq : 0 ≤ (((smoothParameterY x + 1 : ℕ) : ℝ) ^ 2) :=
    sq_nonneg _
  have hxerr' :
      realRosserCellEnvelope r k eta C (x : ℝ) *
          (((smoothParameterY x + 1 : ℕ) : ℝ) ^ 2) ≤
        (x : ℝ) / Real.log (x : ℝ) := by
    simpa only [Real.norm_eq_abs, one_mul,
      abs_of_nonneg (mul_nonneg hE hYsq), abs_of_nonneg hscale] using hxerr
  have htcast : ((t + 1 : ℕ) : ℝ) ≤
      ((smoothParameterY x + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.add_le_add_right htY 1
  have hsq : (((t + 1 : ℕ) : ℝ) ^ 2) ≤
      (((smoothParameterY x + 1 : ℕ) : ℝ) ^ 2) := by
    exact pow_le_pow_left₀ (by positivity) htcast _
  have hEscale : realRosserCellEnvelope r k eta C (x : ℝ) *
      (((t + 1 : ℕ) : ℝ) ^ 2) ≤
        (x : ℝ) / Real.log (x : ℝ) :=
    (mul_le_mul_of_nonneg_left hsq hE).trans hxerr'
  have hden : 0 < (((t + 1 : ℕ) : ℝ) ^ 2) := by positivity
  have hEdiv : realRosserCellEnvelope r k eta C (x : ℝ) ≤
      ((x : ℝ) / Real.log (x : ℝ)) /
        (((t + 1 : ℕ) : ℝ) ^ 2) :=
    (le_div_iff₀ hden).2 (by simpa [mul_comm] using hEscale)
  calc
    ((exceptionalPrimes ell t x).card : ℝ) ≤
        A * ((x : ℝ) / Real.log (x : ℝ)) /
            (((t + 1 : ℕ) : ℝ) ^ 2) +
          realRosserCellEnvelope r k eta C (x : ℝ) :=
      hxrosser t htT htY
    _ ≤ A * ((x : ℝ) / Real.log (x : ℝ)) /
            (((t + 1 : ℕ) : ℝ) ^ 2) +
          ((x : ℝ) / Real.log (x : ℝ)) /
            (((t + 1 : ℕ) : ℝ) ^ 2) := by linarith
    _ = (x : ℝ) / Real.log (x : ℝ) *
          inverseSquareMajorant (A + 1) t := by
      unfold inverseSquareMajorant
      ring

/-- The complete odd-prime arithmetic construction over an arbitrary
cyclotomic realization.  It produces precisely the eventual high-`t`
inverse-square estimate consumed by `CumulativeCutoffWrapper`. -/
theorem exists_eventually_oddPrime_tail_bound
    (hodd : Odd ell) (hell : 2 ≤ ell)
    (hdegree : 2 ≤ normSieveDegree K) :
    ∃ T : ℕ, ∃ C : ℝ,
      ∀ᶠ x : ℕ in atTop, ∀ t : ℕ,
        T ≤ t → t ≤ smoothParameterY x →
        ((exceptionalPrimes ell t x).card : ℝ) ≤
          (x : ℝ) / Real.log (x : ℝ) * inverseSquareMajorant C t := by
  classical
  obtain ⟨eta, delta, S, W, heta, hdelta, heta1, hgap, hS, huniform⟩ :=
    exists_uniform_smallEndpoint_tensorWeighted_upperMainTerm_le_inverseSquare
      K hell
  obtain ⟨E, hE, hEuler⟩ := exists_normSieve_endpointEuler_log_bound K
  let coefficient :
      CyclotomicRayCorrectionIndex ell K × UnitResidueImage ell K → ℝ :=
    fun tag ↦ generatorCellMainConstant K (tagCorrectionIdeal ell K tag) *
      Ideal.absNorm (tagCorrectionIdeal ell K tag : Ideal (𝓞 K))
  have hcoefficient : ∀ tag, 0 ≤ coefficient tag := by
    intro tag
    dsimp only [coefficient]
    exact mul_nonneg (generatorCellMainConstant_nonneg K _)
      (Nat.cast_nonneg _)
  have hmainProvider : ∀ tag, ∃ A : ℝ, 0 ≤ A ∧
      ∀ᶠ t : ℕ in atTop, ∀ f : ℕ, f ≠ 0 →
        f ≤ (t + 1) ^ oddTensorDepth t →
        ∀ x : ℕ, 1 < x → W ≤ normSieveUpper eta x + 1 →
          normSieveLower K (tagCorrectionIdeal ell K tag) f ≤
            normSieveUpper eta x →
          (((ell : ℝ)⁻¹) ^ oddTensorDepth t * coefficient tag * (x : ℝ)) *
              upperMainTerm
                (rosserStoppingPredicate (normRosserBeta K)
                  (normSieveUpper eta x ^ S))
                (coordinateNormDensity K (tagCorrectionIdeal ell K tag))
                (Erdos851.ascendingSievePrimes
                  (normSieveLower K (tagCorrectionIdeal ell K tag) f)
                  (normSieveUpper eta x)) ≤
            A * ((x : ℝ) / Real.log (x : ℝ)) /
              (((t + 1 : ℕ) : ℝ) ^ 2) := by
    intro tag
    exact huniform (tagCorrectionIdeal ell K tag) (coefficient tag)
      (hcoefficient tag)
  choose A hA hmain using hmainProvider
  have htagProvider : ∀ tag,
      ∃ T : ℕ, ∃ C : ℝ, 0 ≤ C ∧
        ∀ᶠ x : ℕ in atTop, ∀ t : ℕ,
          T ≤ t → t ≤ smoothParameterY x →
          ((tagSurvivingFibre ell K eta tag t x).card : ℝ) ≤
            A tag * ((x : ℝ) / Real.log (x : ℝ)) /
                (((t + 1 : ℕ) : ℝ) ^ 2) +
              realRosserCellEnvelope (normSieveDegree K)
                (normSieveDegree K) (delta + eta * S) C (x : ℝ) := by
    intro tag
    apply exists_eventually_tagSurvivingFibre_bound ell K hodd hdegree
      heta hdelta heta1 hgap tag (A tag) E (hA tag) hE
    · simpa only [coefficient] using hmain tag
    · exact hEuler
  choose T C hC htag using htagProvider
  let indices := exceptionalTagIndices ell K
  let exponent : ℝ := delta + eta * S
  let lossConstant := oddFiniteLossConstant ell K
  have hSone : (1 : ℝ) ≤ (S : ℝ) := by
    exact_mod_cast (show 1 ≤ S by omega)
  have hetaExponent : eta ≤ exponent := by
    dsimp only [exponent]
    have hmul : eta ≤ eta * (S : ℝ) := by
      nlinarith [mul_le_mul_of_nonneg_left hSone heta.le]
    linarith
  have hlossBase :=
    eventually_rationalExceptionalNormSieveLossTotalByTag_card_le_envelope
      ell K heta.le
  have hloss : ∀ᶠ x : ℕ in atTop,
      ∀ t : ℕ, t ≤ smoothParameterY x →
      ((tagSieveLoss ell K eta t x).card : ℝ) ≤
        realRosserCellEnvelope (normSieveDegree K) (normSieveDegree K)
          exponent lossConstant (x : ℝ) := by
    filter_upwards [hlossBase, eventually_ge_atTop 1] with x hxloss hxone
    intro t htY
    have hbase := hxloss t htY (fun tag ↦ tagTensorModulus ell K tag t)
    have hxReal : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hxone
    have hrpow :
        (x : ℝ) ^
            (1 - (normSieveDegree K : ℝ)⁻¹ + eta) ≤
          (x : ℝ) ^
            (1 - (normSieveDegree K : ℝ)⁻¹ + exponent) :=
      Real.rpow_le_rpow_of_exponent_le hxReal (by linarith)
    have hEnvelope :
        realRosserCellEnvelope (normSieveDegree K) (normSieveDegree K)
            eta lossConstant (x : ℝ) ≤
          realRosserCellEnvelope (normSieveDegree K) (normSieveDegree K)
            exponent lossConstant (x : ℝ) := by
      unfold realRosserCellEnvelope
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hrpow
          (oddFiniteLossConstant_nonneg ell K))
        (Real.rpow_nonneg (Real.log_nonneg hxReal) _)
    have hbase' :
        ((tagSieveLoss ell K eta t x).card : ℝ) ≤
          realRosserCellEnvelope (normSieveDegree K) (normSieveDegree K)
            eta lossConstant (x : ℝ) := by
      simpa only [tagSieveLoss, lossConstant] using hbase
    exact hbase'.trans hEnvelope
  have hcover : ∀ x t : ℕ,
      exceptionalPrimes ell t x ⊆
        tagSieveLoss ell K eta t x ∪
          indices.biUnion (fun tag ↦ tagSurvivingFibre ell K eta tag t x) := by
    intro x t
    simpa only [indices] using
      exceptionalPrimes_subset_tagSieveLoss_union_tagSurvivingFibres
        ell K eta t x
  have hassembled := eventually_exceptional_card_le_tagEnvelope_above
    ell indices T (fun tag t x ↦ tagSurvivingFibre ell K eta tag t x)
    (tagSieveLoss ell K eta) A C hcover hloss
    (fun tag _htag ↦ htag tag)
  have herrorNonneg :
      0 ≤ finiteFibreErrorConstantWithLoss indices C lossConstant :=
    finiteFibreErrorConstantWithLoss_nonneg indices C lossConstant
      (fun tag _ ↦ hC tag) (oddFiniteLossConstant_nonneg ell K)
  refine ⟨∑ tag ∈ indices, T tag,
    finiteFibreMainConstant indices A + 1, ?_⟩
  exact eventually_inverseSquare_tail_of_tagEnvelope_above ell
    (∑ tag ∈ indices, T tag) (normSieveDegree K) (normSieveDegree K)
    (normSieveDegree_pos K) hgap herrorNonneg hassembled

end Erdos980.ElliottTail.OddPrimeMediumApplication

namespace Erdos980.ElliottTail

open NumberField NumberField.mixedEmbedding
open OddRosserParameters

/-- Elliott's medium-prime estimate for every odd prime exponent. -/
theorem oddPrimeExponentMediumEstimate
    (ell : ℕ) (hell : ell.Prime) (hodd : Odd ell) :
    PrimeExponentMediumEstimate ell := by
  letI : Fact ell.Prime := ⟨hell⟩
  letI : NeZero ell := ⟨hell.ne_zero⟩
  letI : NeZero (ell : ℚ) := ⟨by exact_mod_cast hell.ne_zero⟩
  let K := CyclotomicField ell ℚ
  letI : IsCyclotomicExtension {ell} ℚ K :=
    CyclotomicField.isCyclotomicExtension ell ℚ
  letI : Fintype (index K) := Fintype.ofFinite _
  have hellNeTwo : ell ≠ 2 := by
    intro heq
    subst ell
    norm_num at hodd
  have hell3 : 3 ≤ ell := by
    have hell2 := hell.two_le
    omega
  have hdegree : 2 ≤ normSieveDegree K := by
    unfold normSieveDegree
    rw [Nat.card_eq_fintype_card,
      ← Module.finrank_eq_card_basis (mixedEmbedding.stdBasis K),
      mixedEmbedding.finrank]
    rw [IsCyclotomicExtension.finrank K
      (Polynomial.cyclotomic.irreducible_rat hell.pos),
      Nat.totient_prime hell]
    omega
  obtain ⟨T, C, htail⟩ :=
    OddPrimeMediumApplication.exists_eventually_oddPrime_tail_bound
      ell K hodd hell.two_le hdegree
  exact primeExponentMediumEstimate_of_eventually_tail
    ell T hell.two_le C htail

end Erdos980.ElliottTail
