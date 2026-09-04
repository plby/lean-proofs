/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.LemmaSeven

/-!
# The concrete equal-rank iteration step

This file packages the finite coordinate output of the convex-density and
discrete-John arguments into the literal `.same` `StepOutput` used by the
final iteration.  The hypotheses are precisely the four scalar estimates
which remain after the geometric construction: population retention, the
new density certificate, the structural/convex scale bounds, and the
coordinate-box volume estimate.
-/

namespace Erdos186.PZ.OneStepAssembly

open Finset
open scoped BigOperators
open FinalIteration
open FinalIteration.Partial

noncomputable section

set_option autoImplicit false

/-- In positive dimension the real exponent used by PZ Lemma 1 is the
iteration's convex-density exponent plus the chosen epsilon. -/
theorem densityExponent_eq_convexDensityExponent_add
    {d : ℕ} (hd : 1 ≤ d) (epsilon : ℝ) :
    ConvexDensity.densityExponent d epsilon =
      convexDensityExponent d + epsilon := by
  unfold ConvexDensity.densityExponent convexDensityExponent
  rw [Nat.cast_sub hd]
  norm_num

/-- A genuinely nondegenerate GAP coefficient box is a full-dimensional
compact convex body, so it is a valid reference body for PZ Lemma 1. -/
theorem isConvexBody_boxRealization_gapCoefficientBox
    {ambient d : ℕ} (P : GAP ambient d) (hwidth : ∀ i, 2 ≤ P.widths i) :
    ConvexDensity.IsConvexBody
      (boxRealization (gapCoefficientBox P)) := by
  let lower : Fin d → ℝ := fun _ ↦ 0
  let upper : Fin d → ℝ := fun i ↦ (P.widths i - 1 : ℕ)
  have hrealization :
      boxRealization (gapCoefficientBox P) =
        ConvexDensity.closedAxisBox lower upper := by
    ext x
    change x ∈ (toDiscretizationBox (gapCoefficientBox P)).realization ↔
      x ∈ ConvexDensity.closedAxisBox lower upper
    rw [BoxDiscretization.IntegerBox.mem_realization_iff,
      ConvexDensity.mem_closedAxisBox_iff]
    dsimp only [toDiscretizationBox, gapCoefficientBox]
    simp only [Pi.zero_apply, Int.cast_zero, Int.cast_sub,
      Int.cast_natCast, Int.cast_one, lower, upper]
    constructor <;> intro h i
    · have hi := h i
      change 0 ≤ x.ofLp i ∧
        x.ofLp i ≤ (P.widths i : ℝ) - 1 at hi
      change 0 ≤ x.ofLp i ∧
        x.ofLp i ≤ ((P.widths i - 1 : ℕ) : ℝ)
      rw [Nat.cast_sub (P.width_pos i)]
      simpa using hi
    · have hi := h i
      change 0 ≤ x.ofLp i ∧
        x.ofLp i ≤ ((P.widths i - 1 : ℕ) : ℝ) at hi
      change 0 ≤ x.ofLp i ∧
        x.ofLp i ≤ (P.widths i : ℝ) - 1
      rw [Nat.cast_sub (P.width_pos i)] at hi
      simpa using hi
  rw [hrealization]
  refine ⟨ConvexDensity.convex_closedAxisBox lower upper, ?_, ?_⟩
  · rw [ConvexDensity.closedAxisBox_eq_preimage_Icc]
    exact (PiLp.continuousLinearEquiv 2 ℝ
      (fun _ : Fin d ↦ ℝ)).toHomeomorph.isCompact_preimage.mpr isCompact_Icc
  · let center : ConvexDensity.EuclideanPoint d :=
      WithLp.toLp 2 (fun i ↦ ((P.widths i - 1 : ℕ) : ℝ) / 2)
    refine ⟨center, ?_⟩
    rw [ConvexDensity.closedAxisBox_eq_preimage_Icc]
    apply preimage_interior_subset_interior_preimage
      (PiLp.continuousLinearEquiv 2 ℝ
        (fun _ : Fin d ↦ ℝ)).continuous
    change (fun i ↦ ((P.widths i - 1 : ℕ) : ℝ) / 2) ∈
      interior (Set.Icc lower upper)
    rw [← Set.pi_univ_Icc, interior_pi_set Set.finite_univ]
    intro i _hi
    have hnat : 0 < P.widths i - 1 := by
      have hi := hwidth i
      omega
    have hpositive : (0 : ℝ) < (P.widths i - 1 : ℕ) := by
      exact_mod_cast hnat
    change ((P.widths i - 1 : ℕ) : ℝ) / 2 ∈
      interior (Set.Icc (lower i) (upper i))
    rw [interior_Icc]
    dsimp only [lower, upper]
    constructor <;> nlinarith

/-- Finite lattice containment in a public integer box transports to the
corresponding Euclidean realization. -/
theorem realImage_subset_boxRealization_of_subset
    {d : ℕ} {B : IntegerBox d} {A : Finset (BoxPoint d)}
    (hAB : A ⊆ B.carrier) :
    (Intersection.realImage A :
      Set (ConvexDensity.EuclideanPoint d)) ⊆ boxRealization B := by
  intro x hx
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
  change BoxDiscretization.latticeEmbed z ∈
    (toDiscretizationBox B).realization
  apply BoxDiscretization.IntegerBox.latticeEmbed_mem_realization_iff.mpr
  simpa using hAB hz

/-- Apply the now-unconditional convex-density theorem to a lattice
population and rewrite its Euclidean point count as the cardinality of the
literal lattice restriction used by the next iteration state. -/
theorem exists_convexRestriction_of_pzLemmaOne
    (hConvexDensity : ConvexDensity.PZLemmaOneStatement)
    {d : ℕ} (hd : 1 ≤ d) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ tau deltaZero : ℝ,
      0 < tau ∧ tau < 1 ∧ 0 < deltaZero ∧
      ∀ {delta : ℝ}, 0 < delta → delta < deltaZero →
        ∃ largeEnough : ℕ,
        ∀ (B : IntegerBox d) (A : Finset (BoxPoint d)),
          ConvexDensity.IsConvexBody (boxRealization B) →
          (Intersection.realImage A :
            Set (ConvexDensity.EuclideanPoint d)) ⊆ boxRealization B →
          largeEnough ≤ A.card →
          ConvexGeometry.IsDeltaConvexPosition delta
            (Intersection.realImage A) →
          ∃ eta : ℝ, eta ∈ Set.Icc delta (delta ^ tau) ∧
            ∃ Omega : Set (ConvexDensity.EuclideanPoint d),
              Convex ℝ Omega ∧ Omega ⊆ boxRealization B ∧
              ConvexDensity.relativeVolume Omega (boxRealization B) ≤
                ENNReal.ofReal eta ∧
              eta ^ (convexDensityExponent d + epsilon) * (A.card : ℝ) ≤
                ((latticeRestriction A Omega).card : ℝ) := by
  obtain ⟨tau, deltaZero, htau, htauOne, hdeltaZero, hsource⟩ :=
    hConvexDensity d hd epsilon hepsilon
  refine ⟨tau, deltaZero, htau, htauOne, hdeltaZero, ?_⟩
  intro delta hdelta hdeltaZero
  obtain ⟨largeEnough, hlarge⟩ := hsource delta hdelta hdeltaZero
  refine ⟨largeEnough, ?_⟩
  intro B A hB hAB hcard hposition
  obtain ⟨eta, heta, Omega, hOmega, hOmegaB, hrelative, hpoints⟩ :=
    hlarge (boxRealization B) (Intersection.realImage A) hB hAB
      (by simpa only [Intersection.card_realImage] using hcard) hposition
  refine ⟨eta, heta, Omega, hOmega, hOmegaB, hrelative, ?_⟩
  rw [← card_latticeRestriction A Omega,
    densityExponent_eq_convexDensityExponent_add hd epsilon] at hpoints
  simpa only [Intersection.card_realImage] using hpoints

/-- If the restricted population has two points, the active discrete-John
rank cannot be zero.  This is the small endpoint needed to turn the
rank-drop alternative into a positive-dimensional iteration state. -/
theorem CenteredDiscreteJohnCertificate.rank_pos_of_two_le_restriction_card
    {d : ℕ} {B : IntegerBox d}
    {Omega : Set (ConvexDensity.EuclideanPoint d)}
    (J : CenteredDiscreteJohnCertificate B Omega)
    {A : Finset (BoxPoint d)} (hAB : A ⊆ B.carrier)
    (htwo : 2 ≤ (latticeRestriction A Omega).card) :
    0 < J.rank := by
  by_contra hnot
  have hrank : J.rank = 0 := Nat.eq_zero_of_not_pos hnot
  have hsubset := J.centeredRestriction_subset_outer hAB
  have hcardSubset := Finset.card_le_card hsubset
  have htranslateCard :
      (PZ.translate (-J.center) (latticeRestriction A Omega)).card =
        (latticeRestriction A Omega).card :=
    PZ.card_translate _ _
  have houterCard : J.certificate.outer.carrier.card = 1 := by
    rw [GAP.card_carrier_eq_volume _ J.certificate.outer_proper,
      DiscreteJohn.Certificate.outer, DiscreteJohn.symmetricGAP_volume]
    let : IsEmpty (Fin J.rank) := ⟨fun i ↦ by
      have hi := i.isLt
      omega⟩
    simp
  rw [htranslateCard, houterCard] at hcardSubset
  omega

/-- The post-CFP intersection theorem upgrades irreducibility to convex
position of the selected coefficient core.  The contradiction is taken in
the terminal ambient coordinates, where nonaveraging is already carried by
the reduction result. -/
theorem Reduction.IrreducibleReplacementResult.identifiedCore_isDeltaConvexPosition
    {beta eta : ℝ}
    {context : Reduction.HigherDimensionalContext beta eta}
    {selector : Reduction.BoundedCFPSelector context}
    {ℓ : ℕ} {B₀ : CFP.IntegerBox ℓ}
    {A₀ : Finset (LatticePoint ℓ)}
    {hA₀ : selector.Eligible (Reduction.normalizeSet B₀ A₀)}
    {epsilon delta gamma : ℝ} {K : ℕ} {constant : ℝ}
    (R : Reduction.IrreducibleReplacementResult selector B₀ A₀ hA₀
      epsilon delta gamma K constant)
    (hd : 0 < R.ambientDimension) (rankCeiling : ℕ)
    (hrank : (selector.chosen R.points R.eligible).dimension ≤ rankCeiling)
    {C C' : ℝ} {M : ℕ} {mu : ℝ}
    (hparams : Intersection.Theorem4Parameters R.points beta C C' M
      delta gamma mu)
    (hcoreRetention : delta * (R.points.card : ℝ) ≤
      ((((selector.chosen R.points R.eligible).identifiedCore.card - 2) /
        2 : ℕ) : ℝ))
    (hpost : Intersection.ProducesTheorem4PostCFPData selector R.points
      R.eligible hd rankCeiling hrank delta gamma mu hparams
      R.selector_candidate_closed hcoreRetention) :
    ConvexGeometry.IsDeltaConvexPosition mu
      (Intersection.realImage
        (selector.chosen R.points R.eligible).identifiedCore) := by
  by_contra hfail
  exact (Intersection.theorem4_of_irreducible_of_not_isDeltaConvexPosition
    selector R.eligible hd hrank hparams R.irreducible
    R.selector_candidate_closed hcoreRetention hpost hfail) R.nonaveraging

/-- Convex density followed by the unconditional rank-sensitive discrete
John theorem.  This is the complete geometric extraction used after the
intersection argument: the returned restriction has the exact source
population bound, and its John certificate comes with both the coarse
outer-volume estimate and the lower/full-rank dichotomy. -/
theorem exists_convexJohnRestrictionData
    (hConvexDensity : ConvexDensity.PZLemmaOneStatement)
    (hJohn : PZLemmaSevenStatement)
    {d : ℕ} (hd : 1 ≤ d) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ tau deltaZero : ℝ, ∃ factorBound : ℕ, ∃ johnConstant : ℝ,
      0 < tau ∧ tau < 1 ∧ 0 < deltaZero ∧
      1 ≤ johnConstant ∧
      ∀ {delta : ℝ}, 0 < delta → delta < 1 → delta < deltaZero →
        ∃ largeEnough : ℕ,
        ∀ (B : IntegerBox d) (A : Finset (BoxPoint d)),
          ConvexDensity.IsConvexBody (boxRealization B) →
          (Intersection.realImage A :
            Set (ConvexDensity.EuclideanPoint d)) ⊆ boxRealization B →
          A.Nonempty → largeEnough ≤ A.card →
          ConvexGeometry.IsDeltaConvexPosition delta
            (Intersection.realImage A) →
          1 ≤ delta * (B.carrier.card : ℝ) →
          ∃ eta : ℝ, eta ∈ Set.Icc delta (delta ^ tau) ∧ eta ≤ 1 ∧
            ∃ Omega : Set (ConvexDensity.EuclideanPoint d),
              Convex ℝ Omega ∧ Omega ⊆ boxRealization B ∧
              ConvexDensity.relativeVolume Omega (boxRealization B) ≤
                ENNReal.ofReal eta ∧
              eta ^ (convexDensityExponent d + epsilon) * (A.card : ℝ) ≤
                ((latticeRestriction A Omega).card : ℝ) ∧
              ∃ J : CenteredDiscreteJohnCertificate B Omega,
                J.factor ≤ factorBound ∧
                (J.certificate.outer.volume : ℝ) ≤
                  johnConstant * (B.carrier.card : ℝ) ∧
                (J.rank < d ∨
                  (J.rank = d ∧
                    (J.certificate.outer.volume : ℝ) ≤
                      johnConstant * eta * (B.carrier.card : ℝ))) := by
  obtain ⟨tau, deltaZero, htau, htauOne, hdeltaZero, hconvex⟩ :=
    exists_convexRestriction_of_pzLemmaOne hConvexDensity hd hepsilon
  obtain ⟨factorBound, johnConstant, hjohnConstant, hJohnData⟩ :=
    hJohn d hd
  refine ⟨tau, deltaZero, factorBound, johnConstant, htau, htauOne,
    hdeltaZero, hjohnConstant, ?_⟩
  intro delta hdelta hdeltaOne hdeltaZero'
  obtain ⟨largeEnough, hlarge⟩ := hconvex hdelta hdeltaZero'
  refine ⟨largeEnough, ?_⟩
  intro B A hB hAB hAne hAcard hposition hdeltaBox
  obtain ⟨eta, heta, Omega, hOmega, hOmegaB, hrelative, hpopulation⟩ :=
    hlarge B A hB hAB hAcard hposition
  have hetaPos : 0 < eta := hdelta.trans_le heta.1
  have hetaOne : eta ≤ 1 := by
    exact heta.2.trans (Real.rpow_le_one hdelta.le hdeltaOne.le htau.le)
  have hrestriction : (latticeRestriction A Omega).Nonempty := by
    apply Finset.card_pos.mp
    have hleftPos : 0 <
        eta ^ (convexDensityExponent d + epsilon) * (A.card : ℝ) :=
      mul_pos (Real.rpow_pos_of_pos hetaPos _)
        (by exact_mod_cast hAne.card_pos)
    have hrightPos : 0 < ((latticeRestriction A Omega).card : ℝ) :=
      hleftPos.trans_le hpopulation
    exact_mod_cast hrightPos
  have hetaBox : 1 ≤ eta * (B.carrier.card : ℝ) := by
    calc
      1 ≤ delta * (B.carrier.card : ℝ) := hdeltaBox
      _ ≤ eta * (B.carrier.card : ℝ) :=
        mul_le_mul_of_nonneg_right heta.1 (Nat.cast_nonneg _)
  have hboxRestriction : (boxLatticePointsIn B Omega).Nonempty := by
    apply hrestriction.mono
    intro x hx
    have hx' := mem_latticeRestriction.mp hx
    have hxReal := hAB (Intersection.mem_realImage_of_mem hx'.1)
    have hxBox : x ∈ B.carrier := by
      change BoxDiscretization.latticeEmbed x ∈
        (toDiscretizationBox B).realization at hxReal
      simpa using
        (BoxDiscretization.IntegerBox.latticeEmbed_mem_realization_iff.mp
          hxReal)
    exact mem_latticeRestriction.mpr ⟨hxBox, hx'.2⟩
  obtain ⟨J, hfactor, houter, hrank⟩ :=
    hJohnData B Omega eta hB hetaPos hOmega hOmegaB hboxRestriction
      hrelative hetaBox
  exact ⟨eta, heta, hetaOne, Omega, hOmega, hOmegaB, hrelative,
    hpopulation, J, hfactor, houter, hrank⟩

/-- The exact structural population ratio carried from the terminal
replacement into a same-dimension step. -/
def replacementStructuralRatio (coreFraction : ℝ)
    {beta eta : ℝ}
    {context : Reduction.HigherDimensionalContext beta eta}
    {selector : Reduction.BoundedCFPSelector context}
    {ℓ : ℕ} {B₀ : CFP.IntegerBox ℓ}
    {A₀ : Finset (LatticePoint ℓ)}
    {hA₀ : selector.Eligible (Reduction.normalizeSet B₀ A₀)}
    {epsilon delta gamma : ℝ} {K : ℕ} {constant : ℝ}
    (R : Reduction.IrreducibleReplacementResult selector B₀ A₀ hA₀
      epsilon delta gamma K constant)
    {zeta : ℝ} (current : State zeta) : ℝ :=
  coreFraction * ((R.points.card : ℝ) / (current.points.card : ℝ))

/-- The structural ratio is positive and at most one under the source
density range `0 < delta ≤ 1`. -/
theorem replacementStructuralRatio_mem_Ioc
    {beta eta : ℝ}
    {context : Reduction.HigherDimensionalContext beta eta}
    {selector : Reduction.BoundedCFPSelector context}
    {ℓ : ℕ} {B₀ : CFP.IntegerBox ℓ}
    {A₀ : Finset (LatticePoint ℓ)}
    {hA₀ : selector.Eligible (Reduction.normalizeSet B₀ A₀)}
    {epsilon delta gamma : ℝ} {K : ℕ} {constant : ℝ}
    (R : Reduction.IrreducibleReplacementResult selector B₀ A₀ hA₀
      epsilon delta gamma K constant)
    {zeta coreFraction : ℝ} (current : State zeta)
    (hinputCard : A₀.card ≤ current.points.card)
    (hfraction : 0 < coreFraction) (hfractionOne : coreFraction ≤ 1) :
    replacementStructuralRatio coreFraction R current ∈ Set.Ioc 0 1 := by
  have hcurrentCard : (0 : ℝ) < (current.points.card : ℝ) := by
    exact_mod_cast current.points_nonempty.card_pos
  have hterminalCard : (0 : ℝ) < (R.points.card : ℝ) := by
    exact_mod_cast (selector.eligible_nonempty R.eligible).card_pos
  have hterminalCardLe : (R.points.card : ℝ) ≤
      (current.points.card : ℝ) := by
    have hterminalCardLeNat :=
      Reduction.card_le_of_coordinateReachable R.reachable
    exact_mod_cast ((show R.points.card ≤ A₀.card by
      simpa only [Reduction.card_normalizeSet] using hterminalCardLeNat).trans
        hinputCard)
  have hratioPos : 0 <
      (R.points.card : ℝ) / (current.points.card : ℝ) :=
    div_pos hterminalCard hcurrentCard
  have hratioOne :
      (R.points.card : ℝ) / (current.points.card : ℝ) ≤ 1 :=
    (div_le_one hcurrentCard).2 hterminalCardLe
  constructor
  · exact mul_pos hfraction hratioPos
  · calc
      coreFraction * ((R.points.card : ℝ) / (current.points.card : ℝ)) ≤
          1 * ((R.points.card : ℝ) / (current.points.card : ℝ)) :=
        mul_le_mul_of_nonneg_right hfractionOne hratioPos.le
      _ ≤ 1 := by simpa using hratioOne

/-- The convex-density population bound on the selected core becomes the
literal same-step retention bound after inserting the replacement ratio. -/
theorem convexPopulation_retained
    {beta eta : ℝ}
    {context : Reduction.HigherDimensionalContext beta eta}
    {selector : Reduction.BoundedCFPSelector context}
    {ℓ : ℕ} {B₀ : CFP.IntegerBox ℓ}
    {A₀ : Finset (LatticePoint ℓ)}
    {hA₀ : selector.Eligible (Reduction.normalizeSet B₀ A₀)}
    {epsilon delta gamma : ℝ} {K : ℕ} {constant : ℝ}
    (R : Reduction.IrreducibleReplacementResult selector B₀ A₀ hA₀
      epsilon delta gamma K constant)
    {zeta coreFraction : ℝ} (current : State zeta)
    (_hinputCard : A₀.card ≤ current.points.card)
    (hcoreRetention : coreFraction * (R.points.card : ℝ) ≤
      ((selector.chosen R.points R.eligible).identifiedCore.card : ℝ))
    {convexScale exponent : ℝ}
    (hscale : 0 ≤ convexScale ^ exponent)
    {Omega : Set (ConvexDensity.EuclideanPoint
      (selector.chosen R.points R.eligible).dimension)}
    (hpopulation :
      convexScale ^ exponent *
          ((selector.chosen R.points R.eligible).identifiedCore.card : ℝ) ≤
        ((latticeRestriction
          (selector.chosen R.points R.eligible).identifiedCore Omega).card : ℝ)) :
    convexScale ^ exponent * replacementStructuralRatio coreFraction R current *
        (current.points.card : ℝ) ≤
      ((latticeRestriction
        (selector.chosen R.points R.eligible).identifiedCore Omega).card : ℝ) := by
  have hcurrentCard : (0 : ℝ) < (current.points.card : ℝ) := by
    exact_mod_cast current.points_nonempty.card_pos
  calc
    convexScale ^ exponent * replacementStructuralRatio coreFraction R current *
          (current.points.card : ℝ) =
        convexScale ^ exponent * (coreFraction * (R.points.card : ℝ)) := by
      rw [replacementStructuralRatio]
      field_simp
    _ ≤ convexScale ^ exponent *
        ((selector.chosen R.points R.eligible).identifiedCore.card : ℝ) :=
      mul_le_mul_of_nonneg_left hcoreRetention hscale
    _ ≤ ((latticeRestriction
        (selector.chosen R.points R.eligible).identifiedCore Omega).card : ℝ) :=
      hpopulation

/-- The fixed loss required to express the equal-rank box estimate using the
same structural ratio as the population estimate. -/
def sameStepBoxConstant (johnConstant reductionConstant delta : ℝ)
    (K : ℕ) : ℝ :=
  johnConstant * reductionConstant * (delta⁻¹) ^ K

theorem one_le_sameStepBoxConstant
    {johnConstant reductionConstant delta : ℝ} {K : ℕ}
    (hjohn : 1 ≤ johnConstant) (hreduction : 1 ≤ reductionConstant)
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1) :
    1 ≤ sameStepBoxConstant johnConstant reductionConstant delta K := by
  have hinv : 1 ≤ delta⁻¹ := one_le_inv_iff₀.mpr ⟨hdelta, hdeltaOne⟩
  have hinvPow : 1 ≤ (delta⁻¹) ^ K := one_le_pow₀ hinv
  exact (show (1 : ℝ) = 1 * 1 * 1 by norm_num) ▸
    mul_le_mul (mul_le_mul hjohn hreduction (by norm_num) (by linarith))
      hinvPow (by norm_num) (by positivity)

/-- In the terminal equal-rank case, the full-rank John estimate and the
reduction's progression estimate give exactly the box inequality required
by a `.same` transition. -/
theorem equalRank_outerVolume_le_sameStepBox
    {beta eta zeta : ℝ}
    {context : Reduction.HigherDimensionalContext beta eta}
    {selector : Reduction.BoundedCFPSelector context}
    (current : State zeta)
    {hA : selector.Eligible
      (Reduction.normalizeSet (toCFPBox current.box) current.points)}
    {epsilon delta gamma : ℝ} {K : ℕ} {reductionConstant : ℝ}
    (R : Reduction.IrreducibleReplacementResult selector
      (toCFPBox current.box) current.points hA epsilon delta gamma K
      reductionConstant)
    (hrank : (selector.chosen R.points R.eligible).dimension =
      current.dimension)
    {convexScale johnConstant JVolume coreFraction : ℝ}
    (hscale : 0 ≤ convexScale) (hjohn : 0 ≤ johnConstant)
    (houter :
      (JVolume : ℝ) ≤ johnConstant * convexScale *
        ((selector.chosen R.points R.eligible).progression.volume : ℝ))
    (hfraction : 0 < coreFraction) :
    JVolume ≤
      sameStepBoxConstant johnConstant reductionConstant coreFraction K *
        convexScale * (replacementStructuralRatio coreFraction R current) ^ K *
          (current.box.carrier.card : ℝ) := by
  have hequal := R.equal_rank_bound hrank
  have hprefix :
      johnConstant * convexScale *
          ((selector.chosen R.points R.eligible).progression.volume : ℝ) ≤
        johnConstant * convexScale *
          (reductionConstant *
            ((R.points.card : ℝ) / (current.points.card : ℝ)) ^ K *
              (current.box.carrier.card : ℝ)) :=
    mul_le_mul_of_nonneg_left hequal (mul_nonneg hjohn hscale)
  calc
    JVolume ≤ johnConstant * convexScale *
        ((selector.chosen R.points R.eligible).progression.volume : ℝ) :=
      houter
    _ ≤ johnConstant * convexScale *
        (reductionConstant *
          ((R.points.card : ℝ) / (current.points.card : ℝ)) ^ K *
            (current.box.carrier.card : ℝ)) := hprefix
    _ = sameStepBoxConstant johnConstant reductionConstant coreFraction K *
        convexScale * (replacementStructuralRatio coreFraction R current) ^ K *
          (current.box.carrier.card : ℝ) := by
      rw [sameStepBoxConstant, replacementStructuralRatio, mul_pow]
      have hcancel : (coreFraction⁻¹) ^ K * coreFraction ^ K = (1 : ℝ) := by
        rw [← mul_pow, inv_mul_cancel₀ hfraction.ne', one_pow]
      calc
        johnConstant * convexScale *
              (reductionConstant *
                ((R.points.card : ℝ) / (current.points.card : ℝ)) ^ K *
                  (current.box.carrier.card : ℝ)) =
            johnConstant * reductionConstant * convexScale *
              ((R.points.card : ℝ) / (current.points.card : ℝ)) ^ K *
                (current.box.carrier.card : ℝ) := by ring
        _ = johnConstant * reductionConstant *
              ((coreFraction⁻¹) ^ K * coreFraction ^ K) * convexScale *
                ((R.points.card : ℝ) / (current.points.card : ℝ)) ^ K *
                  (current.box.carrier.card : ℝ) := by rw [hcancel]; ring
        _ = johnConstant * reductionConstant * (coreFraction⁻¹) ^ K *
              convexScale *
                (coreFraction ^ K *
                  ((R.points.card : ℝ) / (current.points.card : ℝ)) ^ K) *
                    (current.box.carrier.card : ℝ) := by ring

/-- A logarithmic loss budget converts the convex-scale and structural-ratio
population estimate into the uniform power retention used by controlled
traces. -/
theorem powerRetention_of_logBudget
    {rho densityExponent convexScale structuralRatio pointCard : ℝ}
    (hscale : 0 < convexScale) (hratio : 0 < structuralRatio)
    (hpoints : 0 < pointCard)
    (hbudget :
      -(densityExponent * Real.log convexScale +
          Real.log structuralRatio) ≤
        rho * Real.log pointCard) :
    pointCard ^ (1 - rho) ≤
      convexScale ^ densityExponent * structuralRatio * pointCard := by
  have hright : 0 <
      convexScale ^ densityExponent * structuralRatio * pointCard :=
    mul_pos (mul_pos (Real.rpow_pos_of_pos hscale _) hratio) hpoints
  apply (Real.log_le_log_iff (Real.rpow_pos_of_pos hpoints _) hright).mp
  rw [Real.log_rpow hpoints,
    Real.log_mul
      (mul_pos (Real.rpow_pos_of_pos hscale _) hratio).ne' hpoints.ne',
    Real.log_mul (Real.rpow_pos_of_pos hscale _).ne' hratio.ne',
    Real.log_rpow hscale]
  linarith

/-- A fixed positive lower bound for the convex scale and the source
replacement population bound make the equal-rank power-retention budget
uniform above a cardinality threshold.  The exponent ceiling is fixed
before the current state is seen; in the iteration it is supplied by the
global dimension envelope. -/
theorem exists_equalRank_powerRetentionBudget_threshold
    {epsilon delta rho exponentCeiling : ℝ}
    (hdelta : 0 < delta)
    (hepsilonRho : epsilon < rho)
    (hexponentCeiling : 0 ≤ exponentCeiling) :
    ∃ pointThreshold : ℕ, 2 ≤ pointThreshold ∧
      ∀ {beta eta zeta densityExponent convexScale : ℝ}
        {context : Reduction.HigherDimensionalContext beta eta}
        {selector : Reduction.BoundedCFPSelector context}
        (current : State zeta)
        {hA : selector.Eligible
          (Reduction.normalizeSet (toCFPBox current.box) current.points)}
        {gamma : ℝ} {K : ℕ} {constant : ℝ}
        (R : Reduction.IrreducibleReplacementResult selector
          (toCFPBox current.box) current.points hA epsilon delta gamma K
            constant),
        pointThreshold ≤ current.points.card →
        0 ≤ densityExponent → densityExponent ≤ exponentCeiling →
        delta ≤ convexScale → convexScale ≤ 1 →
        -(densityExponent * Real.log convexScale +
            Real.log (replacementStructuralRatio (1 / 2) R current)) ≤
          rho * Real.log (current.points.card : ℝ) := by
  let gap : ℝ := rho - epsilon
  have hgap : 0 < gap := sub_pos.mpr hepsilonRho
  let burden : ℝ :=
    max (-(exponentCeiling * Real.log delta + Real.log (1 / 2))) 0
  obtain ⟨pointThreshold, hthreshold⟩ :=
    exists_nat_gt (max 2 (Real.exp (burden / gap)))
  refine ⟨pointThreshold, ?_, ?_⟩
  · have htwo : (2 : ℝ) < (pointThreshold : ℝ) :=
      (le_max_left 2 (Real.exp (burden / gap))).trans_lt hthreshold
    exact_mod_cast htwo.le
  intro beta eta zeta densityExponent convexScale context selector current
    hA gamma K constant R hlarge hexponent hexponentBound hscaleLower
    hscaleUpper
  have hcardCast : (pointThreshold : ℝ) ≤
      (current.points.card : ℝ) := by exact_mod_cast hlarge
  have hexpLt : Real.exp (burden / gap) <
      (current.points.card : ℝ) :=
    ((le_max_right 2 (Real.exp (burden / gap))).trans_lt
      hthreshold).trans_le hcardCast
  have hcurrent : (0 : ℝ) < (current.points.card : ℝ) :=
    (Real.exp_pos _).trans hexpLt
  have hlogLarge : burden / gap <
      Real.log (current.points.card : ℝ) :=
    (Real.lt_log_iff_exp_lt hcurrent).2 hexpLt
  have habsorb : burden <
      gap * Real.log (current.points.card : ℝ) :=
    by simpa [mul_comm] using (div_lt_iff₀ hgap).mp hlogLarge
  have hscalePos : 0 < convexScale := hdelta.trans_le hscaleLower
  have hlogScaleNonpos : Real.log convexScale ≤ 0 :=
    Real.log_nonpos hscalePos.le hscaleUpper
  have hlogDeltaScale : Real.log delta ≤ Real.log convexScale :=
    Real.log_le_log hdelta hscaleLower
  have hscaleCost :
      exponentCeiling * Real.log delta ≤
        densityExponent * Real.log convexScale := by
    calc
      exponentCeiling * Real.log delta ≤
          exponentCeiling * Real.log convexScale :=
        mul_le_mul_of_nonneg_left hlogDeltaScale hexponentCeiling
      _ ≤ densityExponent * Real.log convexScale :=
        mul_le_mul_of_nonpos_right hexponentBound hlogScaleNonpos
  have hterminal : (0 : ℝ) < (R.points.card : ℝ) := by
    exact_mod_cast (selector.eligible_nonempty R.eligible).card_pos
  have hpopulationLog :
      (1 - epsilon) * Real.log (current.points.card : ℝ) <
        Real.log (R.points.card : ℝ) := by
    have hlog := Real.log_lt_log
      (Real.rpow_pos_of_pos hcurrent _) R.population_large
    rwa [Real.log_rpow hcurrent] at hlog
  have hhalf : (1 / 2 : ℝ) ≠ 0 := by norm_num
  have hratio :
      (R.points.card : ℝ) / (current.points.card : ℝ) ≠ 0 :=
    div_ne_zero hterminal.ne' hcurrent.ne'
  have hstructuralLog :
      Real.log (1 / 2) -
          epsilon * Real.log (current.points.card : ℝ) <
        Real.log (replacementStructuralRatio (1 / 2) R current) := by
    rw [replacementStructuralRatio, Real.log_mul hhalf hratio,
      Real.log_div hterminal.ne' hcurrent.ne']
    nlinarith
  have hcost :
      -(exponentCeiling * Real.log delta + Real.log (1 / 2)) ≤
        burden := le_max_left _ _
  dsimp only [gap] at habsorb
  nlinarith

/-- Fixed-convex-scale variant of
`exists_equalRank_powerRetentionBudget_threshold`.  The lower bound for the
convex scale is independent of the replacement density parameter; this is
the form needed when the replacement uses a slowly varying `delta`, while
convex density is invoked at one globally frozen parameter. -/
theorem exists_equalRank_powerRetentionBudget_threshold_scaleFloor
    {epsilon scaleFloor rho exponentCeiling : ℝ}
    (hscaleFloor : 0 < scaleFloor)
    (hepsilonRho : epsilon < rho)
    (hexponentCeiling : 0 ≤ exponentCeiling) :
    ∃ pointThreshold : ℕ, 2 ≤ pointThreshold ∧
      ∀ {beta eta zeta densityExponent convexScale : ℝ}
        {context : Reduction.HigherDimensionalContext beta eta}
        {selector : Reduction.BoundedCFPSelector context}
        (current : State zeta)
        {hA : selector.Eligible
          (Reduction.normalizeSet (toCFPBox current.box) current.points)}
        {delta gamma : ℝ} {K : ℕ} {constant : ℝ}
        (R : Reduction.IrreducibleReplacementResult selector
          (toCFPBox current.box) current.points hA epsilon delta gamma K
            constant),
        pointThreshold ≤ current.points.card →
        0 ≤ densityExponent → densityExponent ≤ exponentCeiling →
        scaleFloor ≤ convexScale → convexScale ≤ 1 →
        -(densityExponent * Real.log convexScale +
            Real.log (replacementStructuralRatio (1 / 2) R current)) ≤
          rho * Real.log (current.points.card : ℝ) := by
  let gap : ℝ := rho - epsilon
  have hgap : 0 < gap := sub_pos.mpr hepsilonRho
  let burden : ℝ :=
    max (-(exponentCeiling * Real.log scaleFloor + Real.log (1 / 2))) 0
  obtain ⟨pointThreshold, hthreshold⟩ :=
    exists_nat_gt (max 2 (Real.exp (burden / gap)))
  refine ⟨pointThreshold, ?_, ?_⟩
  · have htwo : (2 : ℝ) < (pointThreshold : ℝ) :=
      (le_max_left 2 (Real.exp (burden / gap))).trans_lt hthreshold
    exact_mod_cast htwo.le
  intro beta eta zeta densityExponent convexScale context selector current
    hA delta gamma K constant R hlarge hexponent hexponentBound
    hscaleLower hscaleUpper
  have hcardCast : (pointThreshold : ℝ) ≤
      (current.points.card : ℝ) := by exact_mod_cast hlarge
  have hexpLt : Real.exp (burden / gap) <
      (current.points.card : ℝ) :=
    ((le_max_right 2 (Real.exp (burden / gap))).trans_lt
      hthreshold).trans_le hcardCast
  have hcurrent : (0 : ℝ) < (current.points.card : ℝ) :=
    (Real.exp_pos _).trans hexpLt
  have hlogLarge : burden / gap <
      Real.log (current.points.card : ℝ) :=
    (Real.lt_log_iff_exp_lt hcurrent).2 hexpLt
  have habsorb : burden <
      gap * Real.log (current.points.card : ℝ) :=
    by simpa [mul_comm] using (div_lt_iff₀ hgap).mp hlogLarge
  have hscalePos : 0 < convexScale := hscaleFloor.trans_le hscaleLower
  have hlogScaleNonpos : Real.log convexScale ≤ 0 :=
    Real.log_nonpos hscalePos.le hscaleUpper
  have hlogFloorScale : Real.log scaleFloor ≤ Real.log convexScale :=
    Real.log_le_log hscaleFloor hscaleLower
  have hscaleCost :
      exponentCeiling * Real.log scaleFloor ≤
        densityExponent * Real.log convexScale := by
    calc
      exponentCeiling * Real.log scaleFloor ≤
          exponentCeiling * Real.log convexScale :=
        mul_le_mul_of_nonneg_left hlogFloorScale hexponentCeiling
      _ ≤ densityExponent * Real.log convexScale :=
        mul_le_mul_of_nonpos_right hexponentBound hlogScaleNonpos
  have hterminal : (0 : ℝ) < (R.points.card : ℝ) := by
    exact_mod_cast (selector.eligible_nonempty R.eligible).card_pos
  have hpopulationLog :
      (1 - epsilon) * Real.log (current.points.card : ℝ) <
        Real.log (R.points.card : ℝ) := by
    have hlog := Real.log_lt_log
      (Real.rpow_pos_of_pos hcurrent _) R.population_large
    rwa [Real.log_rpow hcurrent] at hlog
  have hhalf : (1 / 2 : ℝ) ≠ 0 := by norm_num
  have hratio :
      (R.points.card : ℝ) / (current.points.card : ℝ) ≠ 0 :=
    div_ne_zero hterminal.ne' hcurrent.ne'
  have hstructuralLog :
      Real.log (1 / 2) -
          epsilon * Real.log (current.points.card : ℝ) <
        Real.log (replacementStructuralRatio (1 / 2) R current) := by
    rw [replacementStructuralRatio, Real.log_mul hhalf hratio,
      Real.log_div hterminal.ne' hcurrent.ne']
    nlinarith
  have hcost :
      -(exponentCeiling * Real.log scaleFloor + Real.log (1 / 2)) ≤
        burden := le_max_left _ _
  dsimp only [gap] at habsorb
  nlinarith

/-- Dimension-bounded specialization with a convex-scale floor independent
of the replacement density parameter. -/
theorem exists_equalRank_powerRetentionBudget_threshold_boundedDimension_scaleFloor
    {zeta epsilon scaleFloor rho : ℝ} (dimensionCeiling : ℕ)
    (hdimensionCeiling : 0 < dimensionCeiling) (hzeta : 0 < zeta)
    (hscaleFloor : 0 < scaleFloor) (hepsilonRho : epsilon < rho) :
    ∃ pointThreshold : ℕ, 2 ≤ pointThreshold ∧
      ∀ {beta eta : ℝ}
        {context : Reduction.HigherDimensionalContext beta eta}
        {selector : Reduction.BoundedCFPSelector context}
        (current : State zeta)
        {hA : selector.Eligible
          (Reduction.normalizeSet (toCFPBox current.box) current.points)}
        {delta gamma : ℝ} {K : ℕ} {constant convexScale : ℝ}
        (R : Reduction.IrreducibleReplacementResult selector
          (toCFPBox current.box) current.points hA epsilon delta gamma K
            constant),
        current.dimension ≤ dimensionCeiling →
        pointThreshold ≤ current.points.card →
        scaleFloor ≤ convexScale → convexScale ≤ 1 →
        -((convexDensityExponent current.dimension + zeta / 2) *
            Real.log convexScale +
          Real.log (replacementStructuralRatio (1 / 2) R current)) ≤
          rho * Real.log (current.points.card : ℝ) := by
  have hceiling : 0 ≤ boxExponent dimensionCeiling + zeta / 2 := by
    have hbox := one_div_four_le_boxExponent hdimensionCeiling
    linarith
  obtain ⟨pointThreshold, hpointThresholdTwo, hbudget⟩ :=
    exists_equalRank_powerRetentionBudget_threshold_scaleFloor hscaleFloor
      hepsilonRho hceiling
  refine ⟨pointThreshold, hpointThresholdTwo, ?_⟩
  intro beta eta context selector current hA delta gamma K constant
    convexScale R hdimension hlarge hscaleLower hscaleUpper
  apply hbudget current R hlarge
  · have hconvexNonneg : 0 ≤ convexDensityExponent current.dimension := by
      unfold convexDensityExponent
      positivity
    linarith
  · have hcurrentPos : 1 ≤ current.dimension := current.dimension_pos
    have hconvexBox := convexDensityExponent_le_boxExponent hcurrentPos
    have hboxCeiling := boxExponent_mono hcurrentPos hdimension
    linarith
  · exact hscaleLower
  · exact hscaleUpper

/-- Dimension-bounded specialization of
`exists_equalRank_powerRetentionBudget_threshold` for the exact exponent
appearing in the source equal-rank constructor. -/
theorem exists_equalRank_powerRetentionBudget_threshold_boundedDimension
    {zeta epsilon delta rho : ℝ} (dimensionCeiling : ℕ)
    (hdimensionCeiling : 0 < dimensionCeiling) (hzeta : 0 < zeta)
    (hdelta : 0 < delta) (hepsilonRho : epsilon < rho) :
    ∃ pointThreshold : ℕ, 2 ≤ pointThreshold ∧
      ∀ {beta eta : ℝ}
        {context : Reduction.HigherDimensionalContext beta eta}
        {selector : Reduction.BoundedCFPSelector context}
        (current : State zeta)
        {hA : selector.Eligible
          (Reduction.normalizeSet (toCFPBox current.box) current.points)}
        {gamma : ℝ} {K : ℕ} {constant convexScale : ℝ}
        (R : Reduction.IrreducibleReplacementResult selector
          (toCFPBox current.box) current.points hA epsilon delta gamma K
            constant),
        current.dimension ≤ dimensionCeiling →
        pointThreshold ≤ current.points.card →
        delta ≤ convexScale → convexScale ≤ 1 →
        -((convexDensityExponent current.dimension + zeta / 2) *
            Real.log convexScale +
          Real.log (replacementStructuralRatio (1 / 2) R current)) ≤
          rho * Real.log (current.points.card : ℝ) := by
  have hceiling : 0 ≤ boxExponent dimensionCeiling + zeta / 2 := by
    have hbox := one_div_four_le_boxExponent hdimensionCeiling
    linarith
  obtain ⟨pointThreshold, hpointThresholdTwo, hbudget⟩ :=
    exists_equalRank_powerRetentionBudget_threshold hdelta hepsilonRho
      hceiling
  refine ⟨pointThreshold, hpointThresholdTwo, ?_⟩
  intro beta eta context selector current hA gamma K constant convexScale R
    hdimension hlarge hscaleLower hscaleUpper
  apply hbudget current R hlarge
  · have hconvexNonneg : 0 ≤ convexDensityExponent current.dimension := by
      unfold convexDensityExponent
      positivity
    linarith
  · have hcurrentPos : 1 ≤ current.dimension := current.dimension_pos
    have hconvexBox := convexDensityExponent_le_boxExponent hcurrentPos
    have hboxCeiling := boxExponent_mono hcurrentPos hdimension
    linarith
  · exact hscaleLower
  · exact hscaleUpper

/-- A full-rank centered discrete-John certificate for a convex restriction
constructs the genuine equal-dimension next state.  Cardinality and
nonaveraging are transported by proper GAP coordinates; all fields of the
`.same` transition are then the displayed source estimates. -/
theorem exists_sameRankStepOutput_of_centeredCertificate
    {K : ℕ} {zeta changeGain sameGain rhoChange : ℝ}
    (current : State zeta)
    {d : ℕ} (B : IntegerBox d)
    (A : Finset (BoxPoint d))
    (Omega : Set (ConvexDensity.EuclideanPoint d))
    (J : CenteredDiscreteJohnCertificate B Omega)
    (hAB : A ⊆ B.carrier)
    (hNA : IsBoxNonaveraging A)
    (hrank : J.rank = current.dimension)
    (hrestriction : (latticeRestriction A Omega).Nonempty)
    (hcardLe : (latticeRestriction A Omega).card ≤ current.points.card)
    (structuralRatio convexScale boxConstant : ℝ)
    (hstructuralRatio : 0 < structuralRatio)
    (hstructuralRatioOne : structuralRatio ≤ 1)
    (hconvexScale : 0 < convexScale)
    (hconvexScaleOne : convexScale ≤ 1)
    (hboxConstant : 1 ≤ boxConstant)
    (hsameBox : boxConstant * convexScale ≤
      convexScale ^ sameRunA current.dimension zeta)
    (hsameGain : 0 < sameGain)
    (hpopulation :
      convexScale ^
          (convexDensityExponent current.dimension + zeta / 2) *
            structuralRatio * (current.points.card : ℝ) ≤
        ((latticeRestriction A Omega).card : ℝ))
    (hdensity :
      (boxExponent J.rank + zeta + (current.excess + sameGain)) *
          Real.log (J.certificate.outer.volume : ℝ) <
        Real.log ((latticeRestriction A Omega).card : ℝ))
    (hbox : (J.certificate.outer.volume : ℝ) ≤
      boxConstant * convexScale * structuralRatio ^ K *
        (current.box.carrier.card : ℝ)) :
    Nonempty (BranchControlledStepOutput (K := K)
      (changeGain := changeGain) (sameGain := sameGain)
      (rhoChange := rhoChange)
      current) := by
  obtain ⟨B', A', hA'B', hA'NA, hA'card, hB'card⟩ :=
    J.exists_coordinateBox hAB hNA
  have hdimensionPos : 0 < J.rank := by
    rw [hrank]
    exact current.dimension_pos
  have hA'nonempty : A'.Nonempty := by
    apply Finset.card_pos.mp
    rw [hA'card]
    exact hrestriction.card_pos
  have hnextDensity :
      (boxExponent J.rank + zeta + (current.excess + sameGain)) *
          Real.log (B'.carrier.card : ℝ) < Real.log (A'.card : ℝ) := by
    rw [hB'card, hA'card]
    exact hdensity
  let next : State zeta := {
    dimension := J.rank
    dimension_pos := hdimensionPos
    zeta_pos := current.zeta_pos
    box := B'
    points := A'
    points_subset_box := hA'B'
    nonaveraging := hA'NA
    points_nonempty := hA'nonempty
    excess := current.excess + sameGain
    excess_nonneg := add_nonneg current.excess_nonneg hsameGain.le
    density_certificate := hnextDensity }
  let retention : ℝ :=
    convexScale ^
        (convexDensityExponent current.dimension + zeta / 2) *
      structuralRatio
  have hexponentNonneg :
      0 ≤ convexDensityExponent current.dimension + zeta / 2 := by
    have hconvexNonneg : 0 ≤ convexDensityExponent current.dimension := by
      unfold convexDensityExponent
      positivity
    linarith [current.zeta_pos]
  have hscalePowPos :
      0 < convexScale ^
        (convexDensityExponent current.dimension + zeta / 2) :=
    Real.rpow_pos_of_pos hconvexScale _
  have hscalePowOne :
      convexScale ^
          (convexDensityExponent current.dimension + zeta / 2) ≤ 1 :=
    Real.rpow_le_one hconvexScale.le hconvexScaleOne hexponentNonneg
  let step : StepOutput (K := K) (changeGain := changeGain)
      (sameGain := sameGain) current := {
    next := next
    points_card_le := by
      dsimp only [next]
      exact hA'card.le.trans hcardLe
    kind := DensityIteration.StepKind.same
    retention := retention
    retention_pos := by
      dsimp only [retention]
      exact mul_pos hscalePowPos hstructuralRatio
    retention_le_one := by
      dsimp only [retention]
      calc
        convexScale ^
              (convexDensityExponent current.dimension + zeta / 2) *
            structuralRatio ≤ 1 * structuralRatio :=
          mul_le_mul_of_nonneg_right hscalePowOne hstructuralRatio.le
        _ ≤ 1 := by simpa using hstructuralRatioOne
    population_retained := by
      dsimp only [retention, next]
      rw [hA'card]
      exact hpopulation
    structuralRatio := structuralRatio
    structuralRatio_pos := hstructuralRatio
    structuralRatio_le_one := hstructuralRatioOne
    convexScale := convexScale
    convexScale_pos := hconvexScale
    convexScale_le_one := hconvexScaleOne
    boxConstant := boxConstant
    one_le_boxConstant := hboxConstant
    transition := by
      dsimp only [next]
      refine ⟨hrank, le_rfl, rfl, ?_⟩
      rw [hB'card]
      exact hbox }
  refine ⟨step.withBranchControl ?_ ?_⟩
  · intro hchange
    exact (hchange rfl).elim
  · intro _hsame
    exact hsameBox

/-- The lower-rank alternative of the same discrete-John certificate gives
a genuine dimension-drop step.  Its multiplicative same-run fields are
inactive, while the retained population and new density certificate still
refer to the literal convex restriction. -/
theorem exists_johnRankDropStepOutput_of_centeredCertificate
    {K : ℕ} {zeta changeGain sameGain rhoChange : ℝ}
    (current : State zeta)
    {d : ℕ} (B : IntegerBox d)
    (A : Finset (BoxPoint d))
    (Omega : Set (ConvexDensity.EuclideanPoint d))
    (J : CenteredDiscreteJohnCertificate B Omega)
    (hAB : A ⊆ B.carrier)
    (hNA : IsBoxNonaveraging A)
    (hrank : J.rank < current.dimension)
    (hJrankPos : 0 < J.rank)
    (hrestriction : (latticeRestriction A Omega).Nonempty)
    (hcardLe : (latticeRestriction A Omega).card ≤ current.points.card)
    (hpower : (current.points.card : ℝ) ^ (1 - rhoChange) ≤
      ((latticeRestriction A Omega).card : ℝ))
    (retention : ℝ) (hretention : 0 < retention)
    (hretentionOne : retention ≤ 1)
    (hchangeGain : 0 < changeGain)
    (hpopulation : retention * (current.points.card : ℝ) ≤
      ((latticeRestriction A Omega).card : ℝ))
    (hdensity :
      (boxExponent J.rank + zeta + (current.excess + changeGain)) *
          Real.log (J.certificate.outer.volume : ℝ) <
        Real.log ((latticeRestriction A Omega).card : ℝ)) :
    Nonempty (BranchControlledStepOutput (K := K)
      (changeGain := changeGain) (sameGain := sameGain)
      (rhoChange := rhoChange)
      current) := by
  obtain ⟨B', A', hA'B', hA'NA, hA'card, hB'card⟩ :=
    J.exists_coordinateBox hAB hNA
  have hA'nonempty : A'.Nonempty := by
    apply Finset.card_pos.mp
    rw [hA'card]
    exact hrestriction.card_pos
  have hnextDensity :
      (boxExponent J.rank + zeta + (current.excess + changeGain)) *
          Real.log (B'.carrier.card : ℝ) < Real.log (A'.card : ℝ) := by
    rw [hB'card, hA'card]
    exact hdensity
  let next : State zeta := {
    dimension := J.rank
    dimension_pos := hJrankPos
    zeta_pos := current.zeta_pos
    box := B'
    points := A'
    points_subset_box := hA'B'
    nonaveraging := hA'NA
    points_nonempty := hA'nonempty
    excess := current.excess + changeGain
    excess_nonneg := add_nonneg current.excess_nonneg hchangeGain.le
    density_certificate := hnextDensity }
  let step : StepOutput (K := K) (changeGain := changeGain)
      (sameGain := sameGain) current := {
    next := next
    points_card_le := by
      dsimp only [next]
      exact hA'card.le.trans hcardLe
    kind := DensityIteration.StepKind.down
    retention := retention
    retention_pos := hretention
    retention_le_one := hretentionOne
    population_retained := by
      dsimp only [next]
      rw [hA'card]
      exact hpopulation
    structuralRatio := 1
    structuralRatio_pos := zero_lt_one
    structuralRatio_le_one := le_rfl
    convexScale := 1
    convexScale_pos := zero_lt_one
    convexScale_le_one := le_rfl
    boxConstant := 1
    one_le_boxConstant := le_rfl
    transition := by
      dsimp only [next]
      exact ⟨hrank, le_rfl⟩ }
  refine ⟨step.withBranchControl ?_ ?_⟩
  · intro _hchange
    dsimp only [step, next]
    rw [hA'card]
    exact hpower
  · intro hsame
    simp [step] at hsame

/-- All finite bookkeeping in the terminal equal-rank branch is automatic
once convex density and the full-rank John alternative provide their two
displayed analytic inequalities. -/
theorem exists_sameRankStepOutput_of_replacementJohn
    {beta eta zeta changeGain sameGain rhoChange : ℝ}
    {context : Reduction.HigherDimensionalContext beta eta}
    {selector : Reduction.BoundedCFPSelector context}
    (current : State zeta)
    {hA : selector.Eligible
      (Reduction.normalizeSet (toCFPBox current.box) current.points)}
    {epsilon delta gamma : ℝ} {K : ℕ} {reductionConstant : ℝ}
    (R : Reduction.IrreducibleReplacementResult selector
      (toCFPBox current.box) current.points hA epsilon delta gamma K
      reductionConstant)
    (hselectedRank : (selector.chosen R.points R.eligible).dimension =
      current.dimension)
    {coreFraction : ℝ}
    (hcoreRetention : coreFraction * (R.points.card : ℝ) ≤
      ((selector.chosen R.points R.eligible).identifiedCore.card : ℝ))
    (hfraction : 0 < coreFraction) (hfractionOne : coreFraction ≤ 1)
    {convexScale johnConstant : ℝ}
    (hconvexScale : 0 < convexScale) (hconvexScaleOne : convexScale ≤ 1)
    (hjohnConstant : 1 ≤ johnConstant)
    (hreductionConstant : 1 ≤ reductionConstant)
    {Omega : Set (ConvexDensity.EuclideanPoint
      (selector.chosen R.points R.eligible).dimension)}
    (J : CenteredDiscreteJohnCertificate
      (gapCoefficientBox
        (selector.chosen R.points R.eligible).progression) Omega)
    (hJohnRank : J.rank = current.dimension)
    (hsameBox :
      sameStepBoxConstant johnConstant reductionConstant coreFraction K *
          convexScale ≤
        convexScale ^ sameRunA current.dimension zeta)
    (hconvexPopulation :
      convexScale ^
          (convexDensityExponent current.dimension + zeta / 2) *
            ((selector.chosen R.points R.eligible).identifiedCore.card : ℝ) ≤
        ((latticeRestriction
          (selector.chosen R.points R.eligible).identifiedCore Omega).card : ℝ))
    (hJohnOuter :
      (J.certificate.outer.volume : ℝ) ≤
        johnConstant * convexScale *
          ((selector.chosen R.points R.eligible).progression.volume : ℝ))
    (hsameGain : 0 < sameGain)
    (hdensity :
      (boxExponent J.rank + zeta + (current.excess + sameGain)) *
          Real.log (J.certificate.outer.volume : ℝ) <
        Real.log
          ((latticeRestriction
            (selector.chosen R.points R.eligible).identifiedCore Omega).card : ℝ)) :
    Nonempty (BranchControlledStepOutput (K := K)
      (changeGain := changeGain) (sameGain := sameGain)
      (rhoChange := rhoChange)
      current) := by
  let S := selector.chosen R.points R.eligible
  have hstructural := replacementStructuralRatio_mem_Ioc R current le_rfl
    hfraction hfractionOne
  have hcore : S.identifiedCore.Nonempty :=
    by
      apply Finset.card_pos.mp
      have hterminalPos : (0 : ℝ) < (R.points.card : ℝ) := by
        exact_mod_cast (selector.eligible_nonempty R.eligible).card_pos
      have hcorePos : (0 : ℝ) < (S.identifiedCore.card : ℝ) :=
        (mul_pos hfraction hterminalPos).trans_le hcoreRetention
      exact_mod_cast hcorePos
  have hrestriction :
      (latticeRestriction S.identifiedCore Omega).Nonempty := by
    apply Finset.card_pos.mp
    have hleftPos : 0 <
        convexScale ^
            (convexDensityExponent current.dimension + zeta / 2) *
              (S.identifiedCore.card : ℝ) :=
      mul_pos (Real.rpow_pos_of_pos hconvexScale _)
        (by exact_mod_cast hcore.card_pos)
    have hrightPos : 0 <
        ((latticeRestriction S.identifiedCore Omega).card : ℝ) :=
      hleftPos.trans_le hconvexPopulation
    exact_mod_cast hrightPos
  have hcardLe : (latticeRestriction S.identifiedCore Omega).card ≤
      current.points.card := by
    exact (Finset.card_le_card
      (latticeRestriction_subset S.identifiedCore Omega)).trans
        (replacementCore_card_le_input R)
  have hpopulation :
      convexScale ^
          (convexDensityExponent current.dimension + zeta / 2) *
            replacementStructuralRatio coreFraction R current *
              (current.points.card : ℝ) ≤
        ((latticeRestriction S.identifiedCore Omega).card : ℝ) := by
    exact convexPopulation_retained R current le_rfl hcoreRetention
      (Real.rpow_nonneg hconvexScale.le _)
      (by simpa only [S] using hconvexPopulation)
  have hbox : (J.certificate.outer.volume : ℝ) ≤
      sameStepBoxConstant johnConstant reductionConstant coreFraction K *
        convexScale * (replacementStructuralRatio coreFraction R current) ^ K *
          (current.box.carrier.card : ℝ) :=
    equalRank_outerVolume_le_sameStepBox current R hselectedRank
      hconvexScale.le (zero_le_one.trans hjohnConstant) hJohnOuter hfraction
  apply exists_sameRankStepOutput_of_centeredCertificate current
    (gapCoefficientBox S.progression) S.identifiedCore Omega J
    S.identifiedCore_subset_coefficientBox
    (S.identifiedCore_nonaveraging R.nonaveraging) hJohnRank hrestriction
    hcardLe (replacementStructuralRatio coreFraction R current) convexScale
    (sameStepBoxConstant johnConstant reductionConstant coreFraction K)
    hstructural.1 hstructural.2 hconvexScale hconvexScaleOne
    (one_le_sameStepBoxConstant hjohnConstant hreductionConstant
      hfraction hfractionOne)
    hsameBox hsameGain hpopulation hdensity hbox

/-- The lower-active-rank John alternative in an otherwise equal selected
rank gives a genuine dimension drop.  Its retained population is still the
same convex-scale/replacement-ratio product as in the full-rank branch. -/
theorem exists_johnRankDropStepOutput_of_replacementJohn
    {beta eta zeta changeGain sameGain rhoChange : ℝ}
    {context : Reduction.HigherDimensionalContext beta eta}
    {selector : Reduction.BoundedCFPSelector context}
    (current : State zeta)
    {hA : selector.Eligible
      (Reduction.normalizeSet (toCFPBox current.box) current.points)}
    {epsilon delta gamma : ℝ} {K : ℕ} {reductionConstant : ℝ}
    (R : Reduction.IrreducibleReplacementResult selector
      (toCFPBox current.box) current.points hA epsilon delta gamma K
      reductionConstant)
    (hselectedRank : (selector.chosen R.points R.eligible).dimension =
      current.dimension)
    {coreFraction : ℝ}
    (hcoreRetention : coreFraction * (R.points.card : ℝ) ≤
      ((selector.chosen R.points R.eligible).identifiedCore.card : ℝ))
    (hfraction : 0 < coreFraction) (hfractionOne : coreFraction ≤ 1)
    {convexScale : ℝ}
    (hconvexScale : 0 < convexScale) (hconvexScaleOne : convexScale ≤ 1)
    {Omega : Set (ConvexDensity.EuclideanPoint
      (selector.chosen R.points R.eligible).dimension)}
    (J : CenteredDiscreteJohnCertificate
      (gapCoefficientBox
        (selector.chosen R.points R.eligible).progression) Omega)
    (hJohnRank : J.rank <
      (selector.chosen R.points R.eligible).dimension)
    (htwo : 2 ≤
      (latticeRestriction
        (selector.chosen R.points R.eligible).identifiedCore Omega).card)
    (hconvexPopulation :
      convexScale ^
          (convexDensityExponent current.dimension + zeta / 2) *
            ((selector.chosen R.points R.eligible).identifiedCore.card : ℝ) ≤
        ((latticeRestriction
          (selector.chosen R.points R.eligible).identifiedCore Omega).card : ℝ))
    (hpowerBudget :
      -((convexDensityExponent current.dimension + zeta / 2) *
          Real.log convexScale +
        Real.log (replacementStructuralRatio coreFraction R current)) ≤
        rhoChange * Real.log (current.points.card : ℝ))
    (hchangeGain : 0 < changeGain)
    (hdensity :
      (boxExponent J.rank + zeta + (current.excess + changeGain)) *
          Real.log (J.certificate.outer.volume : ℝ) <
        Real.log
          ((latticeRestriction
            (selector.chosen R.points R.eligible).identifiedCore Omega).card : ℝ)) :
    Nonempty (BranchControlledStepOutput (K := K)
      (changeGain := changeGain) (sameGain := sameGain)
      (rhoChange := rhoChange)
      current) := by
  let S := selector.chosen R.points R.eligible
  let retention : ℝ :=
      convexScale ^
        (convexDensityExponent current.dimension + zeta / 2) *
      replacementStructuralRatio coreFraction R current
  have hstructural := replacementStructuralRatio_mem_Ioc R current le_rfl
    hfraction hfractionOne
  have hexponentNonneg :
      0 ≤ convexDensityExponent current.dimension + zeta / 2 := by
    have hconvexNonneg : 0 ≤ convexDensityExponent current.dimension := by
      unfold convexDensityExponent
      positivity
    linarith [current.zeta_pos]
  have hscalePowPos :
      0 < convexScale ^
        (convexDensityExponent current.dimension + zeta / 2) :=
    Real.rpow_pos_of_pos hconvexScale _
  have hscalePowOne :
      convexScale ^
          (convexDensityExponent current.dimension + zeta / 2) ≤ 1 :=
    Real.rpow_le_one hconvexScale.le hconvexScaleOne hexponentNonneg
  have hretentionPos : 0 < retention := by
    exact mul_pos hscalePowPos hstructural.1
  have hretentionOne : retention ≤ 1 := by
    dsimp only [retention]
    calc
      convexScale ^
            (convexDensityExponent current.dimension + zeta / 2) *
          replacementStructuralRatio coreFraction R current ≤
          1 * replacementStructuralRatio coreFraction R current :=
        mul_le_mul_of_nonneg_right hscalePowOne hstructural.1.le
      _ ≤ 1 := by simpa using hstructural.2
  have hpopulation : retention * (current.points.card : ℝ) ≤
      ((latticeRestriction S.identifiedCore Omega).card : ℝ) := by
    exact convexPopulation_retained R current le_rfl hcoreRetention
      hscalePowPos.le (by simpa only [S] using hconvexPopulation)
  have hpower : (current.points.card : ℝ) ^ (1 - rhoChange) ≤
      ((latticeRestriction S.identifiedCore Omega).card : ℝ) := by
    apply (powerRetention_of_logBudget hconvexScale hstructural.1
      (by exact_mod_cast current.points_nonempty.card_pos) hpowerBudget).trans
    simpa only [retention] using hpopulation
  have hcardLe : (latticeRestriction S.identifiedCore Omega).card ≤
      current.points.card := by
    exact (Finset.card_le_card
      (latticeRestriction_subset S.identifiedCore Omega)).trans
        (replacementCore_card_le_input R)
  have hrank : J.rank < current.dimension := by
    exact hJohnRank.trans_le hselectedRank.le
  have hJrankPos : 0 < J.rank :=
    J.rank_pos_of_two_le_restriction_card
      S.identifiedCore_subset_coefficientBox htwo
  have hrestriction : (latticeRestriction S.identifiedCore Omega).Nonempty :=
    Finset.card_pos.mp ((by omega : 0 < 2).trans_le htwo)
  apply exists_johnRankDropStepOutput_of_centeredCertificate current
    (gapCoefficientBox S.progression) S.identifiedCore Omega J
    S.identifiedCore_subset_coefficientBox
    (S.identifiedCore_nonaveraging R.nonaveraging) hrank hJrankPos
    hrestriction hcardLe hpower
    retention hretentionPos hretentionOne hchangeGain hpopulation hdensity

/-- A real lower bound strictly above one forces at least two lattice points
in the convex restriction. -/
theorem two_le_latticeRestriction_of_one_lt_population
    {d : ℕ} {A : Finset (BoxPoint d)}
    {Omega : Set (ConvexDensity.EuclideanPoint d)} {population : ℝ}
    (hone : 1 < population)
    (hpopulation : population ≤ ((latticeRestriction A Omega).card : ℝ)) :
    2 ≤ (latticeRestriction A Omega).card := by
  exact_mod_cast hone.trans_le hpopulation

/-- Monotonicity of the logarithm reduces a new-state density certificate
to the scalar comparison between the accumulated population lower bound
and box upper bound.  This isolates the remaining source parameter
calculation without assuming a density certificate itself. -/
theorem densityCertificate_of_population_and_box_bounds
    {d r : ℕ} {zeta excess gain : ℝ}
    (J : GAP d r) {A : Finset (BoxPoint d)}
    {Omega : Set (ConvexDensity.EuclideanPoint d)}
    {populationBound boxBound : ℝ}
    (hnewExponent : 0 < boxExponent r + zeta + (excess + gain))
    (hpopulationPos : 0 < populationBound)
    (hpopulation : populationBound ≤
      ((latticeRestriction A Omega).card : ℝ))
    (hbox : (J.volume : ℝ) ≤ boxBound)
    (hscalar :
      (boxExponent r + zeta + (excess + gain)) * Real.log boxBound <
        Real.log populationBound) :
    (boxExponent r + zeta + (excess + gain)) *
        Real.log (J.volume : ℝ) <
      Real.log ((latticeRestriction A Omega).card : ℝ) := by
  have hJpos : (0 : ℝ) < (J.volume : ℝ) := by
    exact_mod_cast (show 0 < J.volume by
      rw [GAP.volume]
      exact Finset.prod_pos fun i _hi ↦ J.width_pos i)
  have hrestrictionPos : (0 : ℝ) <
      ((latticeRestriction A Omega).card : ℝ) :=
    hpopulationPos.trans_le hpopulation
  have hlogBox : Real.log (J.volume : ℝ) ≤ Real.log boxBound :=
    Real.log_le_log hJpos hbox
  have hlogPopulation : Real.log populationBound ≤
      Real.log ((latticeRestriction A Omega).card : ℝ) :=
    Real.log_le_log hpopulationPos hpopulation
  calc
    (boxExponent r + zeta + (excess + gain)) *
          Real.log (J.volume : ℝ) ≤
        (boxExponent r + zeta + (excess + gain)) * Real.log boxBound :=
      mul_le_mul_of_nonneg_left hlogBox hnewExponent.le
    _ < Real.log populationBound := hscalar
    _ ≤ Real.log ((latticeRestriction A Omega).card : ℝ) :=
      hlogPopulation

/-- Exact logarithmic algebra for one equal-dimension step.  The displayed
budget is the source parameter inequality: the convex scale, structural
ratio and current density together pay for the gain in the density
exponent and the fixed box constant. -/
theorem sameRank_scalar_log_comparison
    {oldExponent newExponent densityExponent boxConstant
      convexScale structuralRatio boxCard pointCard : ℝ}
    {K : ℕ}
    (hold : 0 < oldExponent) (hnew : 0 < newExponent)
    (hconstant : 0 < boxConstant) (hscale : 0 < convexScale)
    (hratio : 0 < structuralRatio) (hbox : 0 < boxCard)
    (hpoints : 0 < pointCard)
    (hcurrent : oldExponent * Real.log boxCard < Real.log pointCard)
    (hbudget :
      newExponent * Real.log boxConstant +
          (newExponent - densityExponent) * Real.log convexScale +
          (newExponent * (K : ℝ) - 1) * Real.log structuralRatio +
          (newExponent * oldExponent⁻¹ - 1) * Real.log pointCard ≤ 0) :
    newExponent * Real.log
        (boxConstant * convexScale * structuralRatio ^ K * boxCard) <
      Real.log (convexScale ^ densityExponent * structuralRatio * pointCard) := by
  have hscaleOld : 0 < newExponent * oldExponent⁻¹ :=
    mul_pos hnew (inv_pos.mpr hold)
  have hscaled := mul_lt_mul_of_pos_left hcurrent hscaleOld
  have hscaled' :
      newExponent * Real.log boxCard <
        (newExponent * oldExponent⁻¹) * Real.log pointCard := by
    calc
      newExponent * Real.log boxCard =
          (newExponent * oldExponent⁻¹) *
            (oldExponent * Real.log boxCard) := by
        field_simp
      _ < (newExponent * oldExponent⁻¹) * Real.log pointCard :=
        hscaled
  rw [Real.log_mul
      (mul_pos (mul_pos hconstant hscale) (pow_pos hratio K)).ne'
      hbox.ne',
    Real.log_mul (mul_pos hconstant hscale).ne' (pow_pos hratio K).ne',
    Real.log_mul hconstant.ne' hscale.ne', Real.log_pow,
    Real.log_mul
      (mul_pos (Real.rpow_pos_of_pos hscale _) hratio).ne' hpoints.ne',
    Real.log_mul (Real.rpow_pos_of_pos hscale _).ne' hratio.ne',
    Real.log_rpow hscale]
  nlinarith

/-- Source-facing full-rank equal-step constructor.  The sole remaining
analytic premise is the explicit logarithmic budget; the new density
certificate is derived from the actual convex-population and John-box
bounds. -/
theorem exists_sameRankStepOutput_of_replacementJohn_logBudget
    {beta eta zeta changeGain sameGain rhoChange : ℝ}
    {context : Reduction.HigherDimensionalContext beta eta}
    {selector : Reduction.BoundedCFPSelector context}
    (current : State zeta)
    {hA : selector.Eligible
      (Reduction.normalizeSet (toCFPBox current.box) current.points)}
    {epsilon delta gamma : ℝ} {K : ℕ} {reductionConstant : ℝ}
    (R : Reduction.IrreducibleReplacementResult selector
      (toCFPBox current.box) current.points hA epsilon delta gamma K
      reductionConstant)
    (hselectedRank : (selector.chosen R.points R.eligible).dimension =
      current.dimension)
    {coreFraction : ℝ}
    (hcoreRetention : coreFraction * (R.points.card : ℝ) ≤
      ((selector.chosen R.points R.eligible).identifiedCore.card : ℝ))
    (hfraction : 0 < coreFraction) (hfractionOne : coreFraction ≤ 1)
    {convexScale johnConstant : ℝ}
    (hconvexScale : 0 < convexScale) (hconvexScaleOne : convexScale ≤ 1)
    (hjohnConstant : 1 ≤ johnConstant)
    (hreductionConstant : 1 ≤ reductionConstant)
    (hsameBox :
      sameStepBoxConstant johnConstant reductionConstant coreFraction K *
          convexScale ≤
        convexScale ^ sameRunA current.dimension zeta)
    {Omega : Set (ConvexDensity.EuclideanPoint
      (selector.chosen R.points R.eligible).dimension)}
    (J : CenteredDiscreteJohnCertificate
      (gapCoefficientBox
        (selector.chosen R.points R.eligible).progression) Omega)
    (hJohnRank : J.rank = current.dimension)
    (hconvexPopulation :
      convexScale ^
          (convexDensityExponent current.dimension + zeta / 2) *
            ((selector.chosen R.points R.eligible).identifiedCore.card : ℝ) ≤
        ((latticeRestriction
          (selector.chosen R.points R.eligible).identifiedCore Omega).card : ℝ))
    (hJohnOuter :
      (J.certificate.outer.volume : ℝ) ≤
        johnConstant * convexScale *
          ((selector.chosen R.points R.eligible).progression.volume : ℝ))
    (hsameGain : 0 < sameGain)
    (hbudget :
      (boxExponent J.rank + zeta + (current.excess + sameGain)) *
          Real.log
            (sameStepBoxConstant johnConstant reductionConstant coreFraction K) +
        ((boxExponent J.rank + zeta + (current.excess + sameGain)) -
            (convexDensityExponent current.dimension + zeta / 2)) *
          Real.log convexScale +
        ((boxExponent J.rank + zeta + (current.excess + sameGain)) *
            (K : ℝ) - 1) *
          Real.log (replacementStructuralRatio coreFraction R current) +
        ((boxExponent J.rank + zeta + (current.excess + sameGain)) *
            (boxExponent current.dimension + zeta + current.excess)⁻¹ - 1) *
          Real.log (current.points.card : ℝ) ≤ 0) :
    Nonempty (BranchControlledStepOutput (K := K)
      (changeGain := changeGain) (sameGain := sameGain)
      (rhoChange := rhoChange)
      current) := by
  let S := selector.chosen R.points R.eligible
  let structuralRatio := replacementStructuralRatio coreFraction R current
  let densityExponent :=
    convexDensityExponent current.dimension + zeta / 2
  let oldExponent :=
    boxExponent current.dimension + zeta + current.excess
  let newExponent :=
    boxExponent J.rank + zeta + (current.excess + sameGain)
  let boxConstant :=
    sameStepBoxConstant johnConstant reductionConstant coreFraction K
  let populationBound :=
    convexScale ^ densityExponent * structuralRatio *
      (current.points.card : ℝ)
  let boxBound := boxConstant * convexScale * structuralRatio ^ K *
    (current.box.carrier.card : ℝ)
  have hstructural := replacementStructuralRatio_mem_Ioc R current le_rfl
    hfraction hfractionOne
  have hold : 0 < oldExponent := by
    dsimp only [oldExponent]
    have hbox := boxExponent_pos current.dimension_pos
    linarith [current.zeta_pos, current.excess_nonneg]
  have hJrankPos : 0 < J.rank :=
    hJohnRank.symm ▸ current.dimension_pos
  have hnew : 0 < newExponent := by
    dsimp only [newExponent]
    have hbox := boxExponent_pos hJrankPos
    linarith [current.zeta_pos, current.excess_nonneg, hsameGain]
  have hboxConstant : 1 ≤ boxConstant := by
    exact one_le_sameStepBoxConstant hjohnConstant hreductionConstant
      hfraction hfractionOne
  have hpoints : (0 : ℝ) < (current.points.card : ℝ) := by
    exact_mod_cast current.points_nonempty.card_pos
  have hboxCard : (0 : ℝ) < (current.box.carrier.card : ℝ) := by
    exact_mod_cast (current.points_nonempty.card_pos.trans_le
      (Finset.card_le_card current.points_subset_box))
  have hpopulation : populationBound ≤
      ((latticeRestriction S.identifiedCore Omega).card : ℝ) := by
    exact convexPopulation_retained R current le_rfl hcoreRetention
      (Real.rpow_pos_of_pos hconvexScale _).le
      (by simpa only [S, densityExponent, populationBound,
          structuralRatio] using hconvexPopulation)
  have hpopulationPos : 0 < populationBound := by
    exact mul_pos
      (mul_pos (Real.rpow_pos_of_pos hconvexScale _) hstructural.1) hpoints
  have hbox : (J.certificate.outer.volume : ℝ) ≤ boxBound := by
    exact equalRank_outerVolume_le_sameStepBox current R hselectedRank
      hconvexScale.le (zero_le_one.trans hjohnConstant) hJohnOuter hfraction
  have hscalar : newExponent * Real.log boxBound <
      Real.log populationBound := by
    exact sameRank_scalar_log_comparison hold hnew
      (zero_lt_one.trans_le hboxConstant)
      hconvexScale hstructural.1 hboxCard hpoints current.density_certificate
      (by simpa only [newExponent, oldExponent, densityExponent, boxConstant,
          structuralRatio] using hbudget)
  have hdensity :
      (boxExponent J.rank + zeta + (current.excess + sameGain)) *
          Real.log (J.certificate.outer.volume : ℝ) <
        Real.log
          ((latticeRestriction S.identifiedCore Omega).card : ℝ) := by
    exact densityCertificate_of_population_and_box_bounds
      J.certificate.outer hnew hpopulationPos hpopulation hbox
        (by simpa only [newExponent] using hscalar)
  exact exists_sameRankStepOutput_of_replacementJohn current R hselectedRank
    hcoreRetention hfraction hfractionOne hconvexScale hconvexScaleOne
    hjohnConstant hreductionConstant J hJohnRank hsameBox
    hconvexPopulation hJohnOuter
    hsameGain (by simpa only [S] using hdensity)

/-- The actual canonical reduction retains one half of its terminal
population in the selected core.  This source-facing specialization removes
the artificial free core-fraction parameter from the equal-rank step. -/
theorem exists_sameRankStepOutput_of_replacementJohn_halfCore_logBudget
    {beta eta zeta changeGain sameGain rhoChange : ℝ}
    {context : Reduction.HigherDimensionalContext beta eta}
    {selector : Reduction.BoundedCFPSelector context}
    (current : State zeta)
    {hA : selector.Eligible
      (Reduction.normalizeSet (toCFPBox current.box) current.points)}
    {epsilon delta gamma : ℝ} {K : ℕ} {reductionConstant : ℝ}
    (R : Reduction.IrreducibleReplacementResult selector
      (toCFPBox current.box) current.points hA epsilon delta gamma K
      reductionConstant)
    (hselectedRank : (selector.chosen R.points R.eligible).dimension =
      current.dimension)
    {convexScale johnConstant : ℝ}
    (hconvexScale : 0 < convexScale) (hconvexScaleOne : convexScale ≤ 1)
    (hjohnConstant : 1 ≤ johnConstant)
    (hreductionConstant : 1 ≤ reductionConstant)
    (hsameBox :
      sameStepBoxConstant johnConstant reductionConstant (1 / 2) K *
          convexScale ≤
        convexScale ^ sameRunA current.dimension zeta)
    {Omega : Set (ConvexDensity.EuclideanPoint
      (selector.chosen R.points R.eligible).dimension)}
    (J : CenteredDiscreteJohnCertificate
      (gapCoefficientBox
        (selector.chosen R.points R.eligible).progression) Omega)
    (hJohnRank : J.rank = current.dimension)
    (hconvexPopulation :
      convexScale ^
          (convexDensityExponent current.dimension + zeta / 2) *
            ((selector.chosen R.points R.eligible).identifiedCore.card : ℝ) ≤
        ((latticeRestriction
          (selector.chosen R.points R.eligible).identifiedCore Omega).card : ℝ))
    (hJohnOuter :
      (J.certificate.outer.volume : ℝ) ≤
        johnConstant * convexScale *
          ((selector.chosen R.points R.eligible).progression.volume : ℝ))
    (hsameGain : 0 < sameGain)
    (hbudget :
      (boxExponent J.rank + zeta + (current.excess + sameGain)) *
          Real.log
            (sameStepBoxConstant johnConstant reductionConstant (1 / 2) K) +
        ((boxExponent J.rank + zeta + (current.excess + sameGain)) -
            (convexDensityExponent current.dimension + zeta / 2)) *
          Real.log convexScale +
        ((boxExponent J.rank + zeta + (current.excess + sameGain)) *
            (K : ℝ) - 1) *
          Real.log (replacementStructuralRatio (1 / 2) R current) +
        ((boxExponent J.rank + zeta + (current.excess + sameGain)) *
            (boxExponent current.dimension + zeta + current.excess)⁻¹ - 1) *
          Real.log (current.points.card : ℝ) ≤ 0) :
    Nonempty (BranchControlledStepOutput (K := K)
      (changeGain := changeGain) (sameGain := sameGain)
      (rhoChange := rhoChange)
      current) := by
  apply exists_sameRankStepOutput_of_replacementJohn_logBudget current R
    hselectedRank R.core_half (by norm_num) (by norm_num)
    hconvexScale hconvexScaleOne hjohnConstant hreductionConstant hsameBox
    J hJohnRank hconvexPopulation hJohnOuter hsameGain hbudget

/-! ## The source same-rank logarithmic budget -/

/-- Numerical core of the source same-rank calculation.  The fixed John and
replacement cost is absorbed by the slowly growing quantity `-log mu`; the
frozen gain spends only a small fraction of the same budget.  The remaining
two terms have the correct sign because `K ≥ 4` and the canonical half-core
structural ratio is at most `1 / 2`. -/
theorem sameRank_halfCore_scalar_budget
    {zeta tau mu gain oldExponent newExponent densityExponent
      boxConstant convexScale structuralRatio pointCard : ℝ}
    {K : ℕ}
    (hzeta : 0 < zeta) (htau : 0 < tau)
    (hmu : 0 < mu) (hmuOne : mu < 1)
    (hgain : 0 < gain) (hgainOne : gain ≤ 1)
    (holdQuarter : (1 / 4 : ℝ) ≤ oldExponent)
    (holdOne : oldExponent < 1)
    (hnew : newExponent = oldExponent + gain)
    (hdensityGap : zeta / 2 ≤ newExponent - densityExponent)
    (hconstant : 1 ≤ boxConstant)
    (hscale : 0 < convexScale)
    (hscaleUpper : convexScale ≤ mu ^ tau)
    (hratio : 0 < structuralRatio)
    (hratioHalf : structuralRatio ≤ 1 / 2)
    (hK : 4 ≤ K)
    (hpointCard : 1 ≤ pointCard)
    (hconstantBudget :
      16 * Real.log boxConstant ≤
        zeta * tau * (-Real.log mu))
    (hgainBudget :
      gain * Real.log pointCard ≤
        zeta * tau / 16 * (-Real.log mu)) :
    newExponent * Real.log boxConstant +
        (newExponent - densityExponent) * Real.log convexScale +
        (newExponent * (K : ℝ) - 1) * Real.log structuralRatio +
        (newExponent * oldExponent⁻¹ - 1) * Real.log pointCard ≤ 0 := by
  have holdPos : 0 < oldExponent :=
    (by norm_num : (0 : ℝ) < 1 / 4).trans_le holdQuarter
  have hnewPos : 0 < newExponent := by rw [hnew]; linarith
  have hnewTwo : newExponent ≤ 2 := by rw [hnew]; linarith
  have hlogConstant : 0 ≤ Real.log boxConstant :=
    Real.log_nonneg hconstant
  have hconstantTerm :
      newExponent * Real.log boxConstant ≤
        zeta * tau / 8 * (-Real.log mu) := by
    calc
      newExponent * Real.log boxConstant ≤
          2 * Real.log boxConstant :=
        mul_le_mul_of_nonneg_right hnewTwo hlogConstant
      _ ≤ zeta * tau / 8 * (-Real.log mu) := by
        linarith
  have hmuPowPos : 0 < mu ^ tau := Real.rpow_pos_of_pos hmu _
  have hmuPowOne : mu ^ tau < 1 :=
    Real.rpow_lt_one hmu.le hmuOne htau
  have hscaleOne : convexScale ≤ 1 :=
    hscaleUpper.trans hmuPowOne.le
  have hlogScale : Real.log convexScale ≤ 0 :=
    Real.log_nonpos hscale.le hscaleOne
  have hlogScaleUpper :
      Real.log convexScale ≤ tau * Real.log mu := by
    calc
      Real.log convexScale ≤ Real.log (mu ^ tau) :=
        Real.log_le_log hscale hscaleUpper
      _ = tau * Real.log mu := by rw [Real.log_rpow hmu]
  have hscaleTerm :
      (newExponent - densityExponent) * Real.log convexScale ≤
        -(zeta * tau / 2 * (-Real.log mu)) := by
    calc
      (newExponent - densityExponent) * Real.log convexScale ≤
          (zeta / 2) * Real.log convexScale :=
        mul_le_mul_of_nonpos_right hdensityGap hlogScale
      _ ≤ (zeta / 2) * (tau * Real.log mu) :=
        mul_le_mul_of_nonneg_left hlogScaleUpper (by linarith)
      _ = -(zeta * tau / 2 * (-Real.log mu)) := by ring
  have hratioOne : structuralRatio ≤ 1 := by
    linarith
  have hlogRatio : Real.log structuralRatio ≤ 0 :=
    Real.log_nonpos hratio.le hratioOne
  have hKCast : (4 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have hnewQuarter : (1 / 4 : ℝ) ≤ newExponent := by
    rw [hnew]
    linarith
  have hcoefficient : 0 ≤ newExponent * (K : ℝ) - 1 := by
    have hnonnegNew : 0 ≤ newExponent := hnewPos.le
    have hnonnegK : (0 : ℝ) ≤ (K : ℝ) := by positivity
    have hmul := mul_le_mul hnewQuarter hKCast
      (by norm_num : (0 : ℝ) ≤ 4) hnonnegNew
    nlinarith [hmul]
  have hratioTerm :
      (newExponent * (K : ℝ) - 1) * Real.log structuralRatio ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hcoefficient hlogRatio
  have holdInverseLe : oldExponent⁻¹ ≤ 4 := by
    have honeDiv : 1 / oldExponent ≤ 4 :=
      (div_le_iff₀ holdPos).2 (by nlinarith)
    simpa only [one_div] using honeDiv
  have hlastCoefficient :
      newExponent * oldExponent⁻¹ - 1 = gain * oldExponent⁻¹ := by
    rw [hnew]
    field_simp
    <;> ring
  have hlastCoefficientLe :
      newExponent * oldExponent⁻¹ - 1 ≤ 4 * gain := by
    rw [hlastCoefficient]
    nlinarith
  have hlogPointCard : 0 ≤ Real.log pointCard :=
    Real.log_nonneg hpointCard
  have hlastTerm :
      (newExponent * oldExponent⁻¹ - 1) * Real.log pointCard ≤
        zeta * tau / 4 * (-Real.log mu) := by
    calc
      (newExponent * oldExponent⁻¹ - 1) * Real.log pointCard ≤
          (4 * gain) * Real.log pointCard :=
        mul_le_mul_of_nonneg_right hlastCoefficientLe hlogPointCard
      _ ≤ zeta * tau / 4 * (-Real.log mu) := by
        nlinarith
  have hnegLogMu : 0 ≤ -Real.log mu := by
    have := Real.log_nonpos hmu.le hmuOne.le
    linarith
  linarith [mul_nonneg (mul_nonneg hzeta.le htau.le) hnegLogMu]

/-- The canonical structural factor is at most one half: replacement never
increases population, and the selected core retains the fixed fraction
`1 / 2` of the terminal population. -/
theorem replacementStructuralRatio_half_le
    {beta eta zeta : ℝ}
    {context : Reduction.HigherDimensionalContext beta eta}
    {selector : Reduction.BoundedCFPSelector context}
    (current : State zeta)
    {hA : selector.Eligible
      (Reduction.normalizeSet (toCFPBox current.box) current.points)}
    {epsilon delta gamma : ℝ} {K : ℕ} {constant : ℝ}
    (R : Reduction.IrreducibleReplacementResult selector
      (toCFPBox current.box) current.points hA epsilon delta gamma K
      constant) :
    replacementStructuralRatio (1 / 2) R current ≤ 1 / 2 := by
  have hcurrentCard : (0 : ℝ) < (current.points.card : ℝ) := by
    exact_mod_cast current.points_nonempty.card_pos
  have hterminalCardLeNat : R.points.card ≤ current.points.card := by
    have hreachable :=
      Reduction.card_le_of_coordinateReachable R.reachable
    simpa only [Reduction.card_normalizeSet] using hreachable
  have hterminalCardLe : (R.points.card : ℝ) ≤
      (current.points.card : ℝ) := by
    exact_mod_cast hterminalCardLeNat
  have hratio :
      (R.points.card : ℝ) / (current.points.card : ℝ) ≤ 1 :=
    (div_le_one hcurrentCard).2 hterminalCardLe
  rw [replacementStructuralRatio]
  simpa using (mul_le_mul_of_nonneg_left hratio
    (by norm_num : (0 : ℝ) ≤ 1 / 2))

/-- Source-facing form of the same-rank scalar budget.  The gain is frozen
from the initial population `initialCard`; a separate slow-variation
comparison transports its `mu` cost to the current population.  The trace
invariant supplies `current.points.card ≤ initialCard`, while its square-root
lower bound is exactly what is used downstream to establish
`hmuComparison`. -/
theorem sameRank_halfCore_logBudget_of_frozenGain
    {beta eta zeta sameGain kappa tau : ℝ}
    {context : Reduction.HigherDimensionalContext beta eta}
    {selector : Reduction.BoundedCFPSelector context}
    (current : State zeta)
    {hA : selector.Eligible
      (Reduction.normalizeSet (toCFPBox current.box) current.points)}
    {epsilon delta gamma : ℝ} {K : ℕ} {reductionConstant : ℝ}
    (R : Reduction.IrreducibleReplacementResult selector
      (toCFPBox current.box) current.points hA epsilon delta gamma K
      reductionConstant)
    {johnConstant convexScale : ℝ}
    {Omega : Set (ConvexDensity.EuclideanPoint
      (selector.chosen R.points R.eligible).dimension)}
    (J : CenteredDiscreteJohnCertificate
      (gapCoefficientBox
        (selector.chosen R.points R.eligible).progression) Omega)
    (hJohnRank : J.rank = current.dimension)
    {initialCard : ℕ}
    (htau : 0 < tau)
    (hK : 4 ≤ K)
    (hjohnConstant : 1 ≤ johnConstant)
    (hreductionConstant : 1 ≤ reductionConstant)
    (hconvexScale : 0 < convexScale)
    (hconvexScaleUpper : convexScale ≤ mu kappa current.points.card ^ tau)
    (hmuCurrent : mu kappa current.points.card ∈ Set.Ioo 0 1)
    (_hmuInitial : mu kappa initialCard ∈ Set.Ioo 0 1)
    (hinitialTwo : 2 ≤ initialCard)
    (hcurrentLe : current.points.card ≤ initialCard)
    (hmuComparison :
      -Real.log (mu kappa initialCard) ≤
        2 * (-Real.log (mu kappa current.points.card)))
    (hsameGain : 0 < sameGain)
    (hsameGainUpper :
      sameGain ≤ min 1
        (zeta * tau / 32 * (-Real.log (mu kappa initialCard)) /
          Real.log (initialCard : ℝ)))
    (hconstantBudget :
      16 * Real.log
          (sameStepBoxConstant johnConstant reductionConstant (1 / 2) K) ≤
        zeta * tau * (-Real.log (mu kappa current.points.card))) :
    (boxExponent J.rank + zeta + (current.excess + sameGain)) *
          Real.log
            (sameStepBoxConstant johnConstant reductionConstant (1 / 2) K) +
        ((boxExponent J.rank + zeta + (current.excess + sameGain)) -
            (convexDensityExponent current.dimension + zeta / 2)) *
          Real.log convexScale +
        ((boxExponent J.rank + zeta + (current.excess + sameGain)) *
            (K : ℝ) - 1) *
          Real.log (replacementStructuralRatio (1 / 2) R current) +
        ((boxExponent J.rank + zeta + (current.excess + sameGain)) *
            (boxExponent current.dimension + zeta + current.excess)⁻¹ - 1) *
          Real.log (current.points.card : ℝ) ≤ 0 := by
  have hcurrentTwo : 2 ≤ current.points.card :=
    State.two_le_points_card current
  have hcurrentReal : (1 : ℝ) ≤ (current.points.card : ℝ) := by
    exact_mod_cast (show 1 ≤ current.points.card by omega)
  have hinitialReal : (1 : ℝ) < (initialCard : ℝ) := by
    exact_mod_cast hinitialTwo
  have hlogInitialPos : 0 < Real.log (initialCard : ℝ) :=
    Real.log_pos hinitialReal
  have hcurrentCastLe : (current.points.card : ℝ) ≤
      (initialCard : ℝ) := by exact_mod_cast hcurrentLe
  have hlogCurrentLe :
      Real.log (current.points.card : ℝ) ≤
        Real.log (initialCard : ℝ) := by
    exact Real.log_le_log
      (by exact_mod_cast current.points_nonempty.card_pos) hcurrentCastLe
  have hgainOne : sameGain ≤ 1 :=
    hsameGainUpper.trans (min_le_left _ _)
  have hgainCap :
      sameGain ≤
        zeta * tau / 32 * (-Real.log (mu kappa initialCard)) /
          Real.log (initialCard : ℝ) :=
    hsameGainUpper.trans (min_le_right _ _)
  have hgainInitial :
      sameGain * Real.log (initialCard : ℝ) ≤
        zeta * tau / 32 * (-Real.log (mu kappa initialCard)) := by
    calc
      sameGain * Real.log (initialCard : ℝ) ≤
          (zeta * tau / 32 * (-Real.log (mu kappa initialCard)) /
            Real.log (initialCard : ℝ)) *
              Real.log (initialCard : ℝ) :=
        mul_le_mul_of_nonneg_right hgainCap hlogInitialPos.le
      _ = zeta * tau / 32 * (-Real.log (mu kappa initialCard)) := by
        field_simp
  have hgainCurrent :
      sameGain * Real.log (current.points.card : ℝ) ≤
        zeta * tau / 16 *
          (-Real.log (mu kappa current.points.card)) := by
    calc
      sameGain * Real.log (current.points.card : ℝ) ≤
          sameGain * Real.log (initialCard : ℝ) :=
        mul_le_mul_of_nonneg_left hlogCurrentLe hsameGain.le
      _ ≤ zeta * tau / 32 * (-Real.log (mu kappa initialCard)) :=
        hgainInitial
      _ ≤ zeta * tau / 32 *
          (2 * (-Real.log (mu kappa current.points.card))) := by
        exact mul_le_mul_of_nonneg_left hmuComparison
          (div_nonneg (mul_nonneg current.zeta_pos.le htau.le) (by norm_num))
      _ = zeta * tau / 16 *
          (-Real.log (mu kappa current.points.card)) := by ring
  have hstructural := replacementStructuralRatio_mem_Ioc R current le_rfl
    (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : (1 / 2 : ℝ) ≤ 1)
  have hdensityGap :
      zeta / 2 ≤
        (boxExponent J.rank + zeta + (current.excess + sameGain)) -
          (convexDensityExponent current.dimension + zeta / 2) := by
    have hconvex :=
      convexDensityExponent_le_boxExponent current.dimension_pos
    rw [hJohnRank]
    linarith [current.excess_nonneg, hsameGain]
  apply sameRank_halfCore_scalar_budget current.zeta_pos htau
    hmuCurrent.1 hmuCurrent.2 hsameGain hgainOne
    (by
      have hbox := one_div_four_le_boxExponent current.dimension_pos
      linarith [current.zeta_pos, current.excess_nonneg])
    current.totalExponent_lt_one
    (by rw [hJohnRank]; ring)
    hdensityGap
    (one_le_sameStepBoxConstant hjohnConstant hreductionConstant
      (by norm_num) (by norm_num))
    hconvexScale hconvexScaleUpper hstructural.1
    (replacementStructuralRatio_half_le current R) hK hcurrentReal
    hconstantBudget hgainCurrent

/-- Frozen-parameter variant used by the final package construction.  The
source values `delta₀`, `gamma₀`, and `mu₀` are chosen after the initial
counterexample is fixed and then remain unchanged throughout the trace. -/
theorem sameRank_halfCore_logBudget_of_frozenParameters
    {beta eta zeta sameGain tau mu₀ : ℝ}
    {context : Reduction.HigherDimensionalContext beta eta}
    {selector : Reduction.BoundedCFPSelector context}
    (current : State zeta)
    {hA : selector.Eligible
      (Reduction.normalizeSet (toCFPBox current.box) current.points)}
    {epsilon delta gamma : ℝ} {K : ℕ} {reductionConstant : ℝ}
    (R : Reduction.IrreducibleReplacementResult selector
      (toCFPBox current.box) current.points hA epsilon delta gamma K
      reductionConstant)
    {johnConstant convexScale : ℝ}
    {Omega : Set (ConvexDensity.EuclideanPoint
      (selector.chosen R.points R.eligible).dimension)}
    (J : CenteredDiscreteJohnCertificate
      (gapCoefficientBox
        (selector.chosen R.points R.eligible).progression) Omega)
    (hJohnRank : J.rank = current.dimension)
    {initialCard : ℕ}
    (htau : 0 < tau) (hK : 4 ≤ K)
    (hjohnConstant : 1 ≤ johnConstant)
    (hreductionConstant : 1 ≤ reductionConstant)
    (hconvexScale : 0 < convexScale)
    (hconvexScaleUpper : convexScale ≤ mu₀ ^ tau)
    (hmu₀ : mu₀ ∈ Set.Ioo 0 1)
    (hinitialTwo : 2 ≤ initialCard)
    (hcurrentLe : current.points.card ≤ initialCard)
    (hsameGain : 0 < sameGain)
    (hsameGainUpper :
      sameGain ≤ min 1
        (zeta * tau / 16 * (-Real.log mu₀) /
          Real.log (initialCard : ℝ)))
    (hconstantBudget :
      16 * Real.log
          (sameStepBoxConstant johnConstant reductionConstant (1 / 2) K) ≤
        zeta * tau * (-Real.log mu₀)) :
    (boxExponent J.rank + zeta + (current.excess + sameGain)) *
          Real.log
            (sameStepBoxConstant johnConstant reductionConstant (1 / 2) K) +
        ((boxExponent J.rank + zeta + (current.excess + sameGain)) -
            (convexDensityExponent current.dimension + zeta / 2)) *
          Real.log convexScale +
        ((boxExponent J.rank + zeta + (current.excess + sameGain)) *
            (K : ℝ) - 1) *
          Real.log (replacementStructuralRatio (1 / 2) R current) +
        ((boxExponent J.rank + zeta + (current.excess + sameGain)) *
            (boxExponent current.dimension + zeta + current.excess)⁻¹ - 1) *
          Real.log (current.points.card : ℝ) ≤ 0 := by
  have hcurrentReal : (1 : ℝ) ≤ (current.points.card : ℝ) := by
    exact_mod_cast (show 1 ≤ current.points.card by
      have := State.two_le_points_card current
      omega)
  have hinitialReal : (1 : ℝ) < (initialCard : ℝ) := by
    exact_mod_cast hinitialTwo
  have hlogInitialPos : 0 < Real.log (initialCard : ℝ) :=
    Real.log_pos hinitialReal
  have hcurrentCastLe : (current.points.card : ℝ) ≤
      (initialCard : ℝ) := by exact_mod_cast hcurrentLe
  have hlogCurrentLe :
      Real.log (current.points.card : ℝ) ≤
        Real.log (initialCard : ℝ) :=
    Real.log_le_log
      (by exact_mod_cast current.points_nonempty.card_pos) hcurrentCastLe
  have hgainOne : sameGain ≤ 1 :=
    hsameGainUpper.trans (min_le_left _ _)
  have hgainCap :
      sameGain ≤ zeta * tau / 16 * (-Real.log mu₀) /
          Real.log (initialCard : ℝ) :=
    hsameGainUpper.trans (min_le_right _ _)
  have hgainInitial :
      sameGain * Real.log (initialCard : ℝ) ≤
        zeta * tau / 16 * (-Real.log mu₀) := by
    calc
      sameGain * Real.log (initialCard : ℝ) ≤
          (zeta * tau / 16 * (-Real.log mu₀) /
            Real.log (initialCard : ℝ)) *
              Real.log (initialCard : ℝ) :=
        mul_le_mul_of_nonneg_right hgainCap hlogInitialPos.le
      _ = zeta * tau / 16 * (-Real.log mu₀) := by field_simp
  have hgainCurrent :
      sameGain * Real.log (current.points.card : ℝ) ≤
        zeta * tau / 16 * (-Real.log mu₀) :=
    (mul_le_mul_of_nonneg_left hlogCurrentLe hsameGain.le).trans hgainInitial
  have hstructural := replacementStructuralRatio_mem_Ioc R current le_rfl
    (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : (1 / 2 : ℝ) ≤ 1)
  have hdensityGap :
      zeta / 2 ≤
        (boxExponent J.rank + zeta + (current.excess + sameGain)) -
          (convexDensityExponent current.dimension + zeta / 2) := by
    have hconvex := convexDensityExponent_le_boxExponent current.dimension_pos
    rw [hJohnRank]
    linarith [current.excess_nonneg, hsameGain]
  apply sameRank_halfCore_scalar_budget current.zeta_pos htau
    hmu₀.1 hmu₀.2 hsameGain hgainOne
    (by
      have hbox := one_div_four_le_boxExponent current.dimension_pos
      linarith [current.zeta_pos, current.excess_nonneg])
    current.totalExponent_lt_one (by rw [hJohnRank]; ring) hdensityGap
    (one_le_sameStepBoxConstant hjohnConstant hreductionConstant
      (by norm_num) (by norm_num))
    hconvexScale hconvexScaleUpper hstructural.1
    (replacementStructuralRatio_half_le current R) hK hcurrentReal
    hconstantBudget hgainCurrent

/-! ## The John rank-drop density budget -/

/-- Exact logarithmic algebra for the coarse John estimate in the
lower-active-rank branch.  Here `structuralRatio` is the terminal/current
population ratio before the half-core factor is inserted. -/
theorem johnRankDrop_scalar_log_comparison
    {oldExponent newExponent densityExponent boxConstant convexScale
      structuralRatio boxCard pointCard : ℝ}
    {K : ℕ}
    (hold : 0 < oldExponent) (hnew : 0 < newExponent)
    (hconstant : 0 < boxConstant) (hscale : 0 < convexScale)
    (hratio : 0 < structuralRatio) (hbox : 0 < boxCard)
    (hpoints : 0 < pointCard)
    (hcurrent : oldExponent * Real.log boxCard < Real.log pointCard)
    (hbudget :
      newExponent * Real.log boxConstant -
          densityExponent * Real.log convexScale +
          (newExponent * (K : ℝ) - 1) * Real.log structuralRatio -
          Real.log (1 / 2) +
          (newExponent * oldExponent⁻¹ - 1) * Real.log pointCard ≤ 0) :
    newExponent * Real.log
        (boxConstant * structuralRatio ^ K * boxCard) <
      Real.log
        (convexScale ^ densityExponent * (1 / 2) * structuralRatio *
          pointCard) := by
  have hscaleOld : 0 < newExponent * oldExponent⁻¹ :=
    mul_pos hnew (inv_pos.mpr hold)
  have hscaled := mul_lt_mul_of_pos_left hcurrent hscaleOld
  have hscaled' :
      newExponent * Real.log boxCard <
        (newExponent * oldExponent⁻¹) * Real.log pointCard := by
    calc
      newExponent * Real.log boxCard =
          (newExponent * oldExponent⁻¹) *
            (oldExponent * Real.log boxCard) := by
        field_simp
      _ < (newExponent * oldExponent⁻¹) * Real.log pointCard := hscaled
  rw [Real.log_mul
      (mul_pos hconstant (pow_pos hratio K)).ne' hbox.ne',
    Real.log_mul hconstant.ne' (pow_pos hratio K).ne', Real.log_pow,
    Real.log_mul
      (mul_pos
        (mul_pos (Real.rpow_pos_of_pos hscale _)
          (by norm_num : (0 : ℝ) < 1 / 2)) hratio).ne' hpoints.ne',
    Real.log_mul
      (mul_pos (Real.rpow_pos_of_pos hscale _)
        (by norm_num : (0 : ℝ) < 1 / 2)).ne' hratio.ne',
    Real.log_mul (Real.rpow_pos_of_pos hscale _).ne'
      (by norm_num : (1 / 2 : ℝ) ≠ 0),
    Real.log_rpow hscale]
  nlinarith

/-- A fixed positive rank saving absorbs the coarse John constant and the
slow convex-scale loss.  The ratio term is nonpositive once `K ≥ 4`, since
every positive-dimensional box exponent is at least `1 / 4`. -/
theorem johnRankDrop_scalar_budget
    {saving mu oldExponent newExponent densityExponent densityCeiling
      boxConstant convexScale structuralRatio pointCard : ℝ}
    {K : ℕ}
    (hsaving : 0 < saving)
    (hmu : 0 < mu) (hmuOne : mu < 1)
    (holdQuarter : (1 / 4 : ℝ) ≤ oldExponent)
    (holdOne : oldExponent < 1)
    (hnewQuarter : (1 / 4 : ℝ) ≤ newExponent)
    (hnewSaving : newExponent ≤ oldExponent - saving)
    (hdensity : 0 ≤ densityExponent)
    (hdensityCeiling : densityExponent ≤ densityCeiling)
    (hconstant : 1 ≤ boxConstant)
    (hscale : 0 < convexScale) (hmuScale : mu ≤ convexScale)
    (hscaleOne : convexScale ≤ 1)
    (hratio : 0 < structuralRatio) (hratioOne : structuralRatio ≤ 1)
    (hK : 4 ≤ K) (hpointCard : 1 ≤ pointCard)
    (habsorb :
      Real.log boxConstant + densityCeiling * (-Real.log mu) -
          Real.log (1 / 2) ≤
        saving * Real.log pointCard) :
    newExponent * Real.log boxConstant -
          densityExponent * Real.log convexScale +
          (newExponent * (K : ℝ) - 1) * Real.log structuralRatio -
          Real.log (1 / 2) +
          (newExponent * oldExponent⁻¹ - 1) * Real.log pointCard ≤ 0 := by
  have holdPos : 0 < oldExponent :=
    (by norm_num : (0 : ℝ) < 1 / 4).trans_le holdQuarter
  have hnewPos : 0 < newExponent :=
    (by norm_num : (0 : ℝ) < 1 / 4).trans_le hnewQuarter
  have hnewOne : newExponent ≤ 1 := by linarith
  have hlogConstant : 0 ≤ Real.log boxConstant :=
    Real.log_nonneg hconstant
  have hconstantTerm :
      newExponent * Real.log boxConstant ≤ Real.log boxConstant :=
    mul_le_of_le_one_left hlogConstant hnewOne
  have hlogMuScale : Real.log mu ≤ Real.log convexScale :=
    Real.log_le_log hmu hmuScale
  have hlogScale : Real.log convexScale ≤ 0 :=
    Real.log_nonpos hscale.le hscaleOne
  have hscaleCost :
      -(densityExponent * Real.log convexScale) ≤
        densityCeiling * (-Real.log mu) := by
    have hfirst :
        densityExponent * Real.log mu ≤
          densityExponent * Real.log convexScale :=
      mul_le_mul_of_nonneg_left hlogMuScale hdensity
    have hnegMu : 0 ≤ -Real.log mu := by
      have := Real.log_nonpos hmu.le hmuOne.le
      linarith
    have hsecond :
        densityExponent * (-Real.log mu) ≤
          densityCeiling * (-Real.log mu) :=
      mul_le_mul_of_nonneg_right hdensityCeiling hnegMu
    nlinarith
  have hKCast : (4 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have hcoefficient : 0 ≤ newExponent * (K : ℝ) - 1 := by
    have hmul := mul_le_mul hnewQuarter hKCast
      (by norm_num : (0 : ℝ) ≤ 4) hnewPos.le
    nlinarith [hmul]
  have hratioTerm :
      (newExponent * (K : ℝ) - 1) * Real.log structuralRatio ≤ 0 := by
    exact mul_nonpos_of_nonneg_of_nonpos hcoefficient
      (Real.log_nonpos hratio.le hratioOne)
  have holdInversePos : 0 < oldExponent⁻¹ := inv_pos.mpr holdPos
  have hlastCoefficient :
      newExponent * oldExponent⁻¹ - 1 ≤ -saving := by
    have hscaled := mul_le_mul_of_nonneg_right hnewSaving holdInversePos.le
    have holdInvOne : 1 ≤ oldExponent⁻¹ := by
      rw [one_le_inv₀ holdPos]
      exact holdOne.le
    have hsavingScaled : saving ≤ saving * oldExponent⁻¹ := by
      nlinarith
    have holdCancel : oldExponent * oldExponent⁻¹ = 1 :=
      mul_inv_cancel₀ holdPos.ne'
    rw [sub_mul, holdCancel] at hscaled
    nlinarith
  have hlogPoint : 0 ≤ Real.log pointCard := Real.log_nonneg hpointCard
  have hlastTerm :
      (newExponent * oldExponent⁻¹ - 1) * Real.log pointCard ≤
        -saving * Real.log pointCard :=
    mul_le_mul_of_nonneg_right hlastCoefficient hlogPoint
  linarith

/-- Source-facing density certificate for the lower-rank John alternative.
The coarse John outer-volume estimate and the replacement equal-rank bound
give the box estimate.  The half-core convex population gives the matching
population estimate, and a fixed rank saving absorbs all scalar losses. -/
theorem johnRankDrop_density_of_frozenBudget
    {beta eta zeta changeGain : ℝ}
    {context : Reduction.HigherDimensionalContext beta eta}
    {selector : Reduction.BoundedCFPSelector context}
    (current : State zeta)
    {hA : selector.Eligible
      (Reduction.normalizeSet (toCFPBox current.box) current.points)}
    {epsilon delta gamma : ℝ} {K : ℕ} {reductionConstant : ℝ}
    (R : Reduction.IrreducibleReplacementResult selector
      (toCFPBox current.box) current.points hA epsilon delta gamma K
      reductionConstant)
    (hselectedRank :
      (selector.chosen R.points R.eligible).dimension = current.dimension)
    {mu₀ saving densityCeiling convexScale johnConstant : ℝ}
    (hsaving : 0 < saving)
    (hK : 4 ≤ K)
    (hjohnConstant : 1 ≤ johnConstant)
    (hreductionConstant : 1 ≤ reductionConstant)
    (hmu₀ : mu₀ ∈ Set.Ioo 0 1)
    (hconvexScale : 0 < convexScale)
    (hmu₀Scale : mu₀ ≤ convexScale)
    (hconvexScaleOne : convexScale ≤ 1)
    (hdensityCeiling :
      convexDensityExponent current.dimension + zeta / 2 ≤
        densityCeiling)
    {Omega : Set (ConvexDensity.EuclideanPoint
      (selector.chosen R.points R.eligible).dimension)}
    (J : CenteredDiscreteJohnCertificate
      (gapCoefficientBox
        (selector.chosen R.points R.eligible).progression) Omega)
    (hJrankPos : 0 < J.rank)
    (hconvexPopulation :
      convexScale ^
          (convexDensityExponent current.dimension + zeta / 2) *
            ((selector.chosen R.points R.eligible).identifiedCore.card : ℝ) ≤
        ((latticeRestriction
          (selector.chosen R.points R.eligible).identifiedCore Omega).card : ℝ))
    (hJohnOuter :
      (J.certificate.outer.volume : ℝ) ≤
        johnConstant *
          ((selector.chosen R.points R.eligible).progression.volume : ℝ))
    (hchangeGain : 0 < changeGain)
    (hnewSaving :
      boxExponent J.rank + zeta + (current.excess + changeGain) ≤
        boxExponent current.dimension + zeta + current.excess - saving)
    (habsorb :
      Real.log (johnConstant * reductionConstant) +
          densityCeiling * (-Real.log mu₀) - Real.log (1 / 2) ≤
        saving * Real.log (current.points.card : ℝ)) :
    (boxExponent J.rank + zeta + (current.excess + changeGain)) *
          Real.log (J.certificate.outer.volume : ℝ) <
        Real.log
          ((latticeRestriction
            (selector.chosen R.points R.eligible).identifiedCore Omega).card : ℝ) := by
  let S := selector.chosen R.points R.eligible
  let oldExponent := boxExponent current.dimension + zeta + current.excess
  let newExponent := boxExponent J.rank + zeta +
    (current.excess + changeGain)
  let densityExponent := convexDensityExponent current.dimension + zeta / 2
  let structuralRatio := replacementStructuralRatio 1 R current
  let boxConstant := johnConstant * reductionConstant
  let populationBound :=
    convexScale ^ densityExponent * (1 / 2) * structuralRatio *
      (current.points.card : ℝ)
  let boxBound := boxConstant * structuralRatio ^ K *
    (current.box.carrier.card : ℝ)
  have holdPos : 0 < oldExponent := by
    dsimp only [oldExponent]
    have hbox := boxExponent_pos current.dimension_pos
    linarith [current.zeta_pos, current.excess_nonneg]
  have hnewPos : 0 < newExponent := by
    dsimp only [newExponent]
    have hbox := boxExponent_pos hJrankPos
    linarith [current.zeta_pos, current.excess_nonneg, hchangeGain]
  have hdensityNonneg : 0 ≤ densityExponent := by
    dsimp only [densityExponent]
    have hconvex : 0 ≤ convexDensityExponent current.dimension := by
      unfold convexDensityExponent
      positivity
    linarith [current.zeta_pos]
  have hstructural := replacementStructuralRatio_mem_Ioc R current le_rfl
    (by norm_num : (0 : ℝ) < 1) (le_refl (1 : ℝ))
  have hpoints : (0 : ℝ) < (current.points.card : ℝ) := by
    exact_mod_cast current.points_nonempty.card_pos
  have hboxCard : (0 : ℝ) < (current.box.carrier.card : ℝ) := by
    exact_mod_cast (current.points_nonempty.card_pos.trans_le
      (Finset.card_le_card current.points_subset_box))
  have hpopulation : populationBound ≤
      ((latticeRestriction S.identifiedCore Omega).card : ℝ) := by
    have h := convexPopulation_retained R current le_rfl R.core_half
      (Real.rpow_nonneg hconvexScale.le _) hconvexPopulation
    calc
      populationBound =
          convexScale ^ densityExponent *
              replacementStructuralRatio (1 / 2) R current *
                (current.points.card : ℝ) := by
        dsimp only [populationBound, structuralRatio,
          replacementStructuralRatio]
        ring
      _ ≤ ((latticeRestriction S.identifiedCore Omega).card : ℝ) := by
        simpa only [densityExponent, S] using h
  have hpopulationPos : 0 < populationBound := by
    dsimp only [populationBound]
    exact mul_pos
      (mul_pos
        (mul_pos (Real.rpow_pos_of_pos hconvexScale _)
          (by norm_num : (0 : ℝ) < 1 / 2)) hstructural.1) hpoints
  have hbox : (J.certificate.outer.volume : ℝ) ≤ boxBound := by
    have hequal := R.equal_rank_bound hselectedRank
    calc
      (J.certificate.outer.volume : ℝ) ≤
          johnConstant * (S.progression.volume : ℝ) := by
        simpa only [S] using hJohnOuter
      _ ≤ johnConstant *
          (reductionConstant *
            ((R.points.card : ℝ) / (current.points.card : ℝ)) ^ K *
              (current.box.carrier.card : ℝ)) :=
        mul_le_mul_of_nonneg_left hequal (by linarith)
      _ = boxBound := by
        dsimp only [boxBound, boxConstant, structuralRatio,
          replacementStructuralRatio]
        ring
  have hscalarBudget :
      newExponent * Real.log boxConstant -
            densityExponent * Real.log convexScale +
            (newExponent * (K : ℝ) - 1) * Real.log structuralRatio -
            Real.log (1 / 2) +
            (newExponent * oldExponent⁻¹ - 1) *
              Real.log (current.points.card : ℝ) ≤ 0 := by
    apply johnRankDrop_scalar_budget hsaving hmu₀.1 hmu₀.2
    · dsimp only [oldExponent]
      have hbox := one_div_four_le_boxExponent current.dimension_pos
      linarith [current.zeta_pos, current.excess_nonneg]
    · exact current.totalExponent_lt_one
    · dsimp only [newExponent]
      have hbox := one_div_four_le_boxExponent hJrankPos
      linarith [current.zeta_pos, current.excess_nonneg]
    · simpa only [newExponent, oldExponent] using hnewSaving
    · exact hdensityNonneg
    · simpa only [densityExponent] using hdensityCeiling
    · dsimp only [boxConstant]
      nlinarith [mul_le_mul hjohnConstant hreductionConstant
        (by norm_num : (0 : ℝ) ≤ 1) (by linarith : (0 : ℝ) ≤ johnConstant)]
    · exact hconvexScale
    · exact hmu₀Scale
    · exact hconvexScaleOne
    · exact hstructural.1
    · exact hstructural.2
    · exact hK
    · exact (show (1 : ℝ) ≤ (current.points.card : ℝ) by
        exact_mod_cast Nat.succ_le_iff.mpr current.points_nonempty.card_pos)
    · simpa only [boxConstant] using habsorb
  have hscalar : newExponent * Real.log boxBound <
      Real.log populationBound := by
    exact johnRankDrop_scalar_log_comparison holdPos hnewPos
      (by dsimp only [boxConstant]; positivity) hconvexScale hstructural.1
      hboxCard hpoints current.density_certificate hscalarBudget
  exact densityCertificate_of_population_and_box_bounds
    J.certificate.outer hnewPos hpopulationPos hpopulation hbox
      (by simpa only [newExponent] using hscalar)

end

end Erdos186.PZ.OneStepAssembly
