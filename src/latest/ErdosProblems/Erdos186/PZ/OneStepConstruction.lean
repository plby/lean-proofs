/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.EqualRankStep
import ErdosProblems.Erdos186.PZ.Intersection.SourceHalfCorePostCFP
import ErdosProblems.Erdos186.PZ.Intersection.SourcePowerRangeBoxWeightedPostCFPAssembly
import ErdosProblems.Erdos186.PZ.Reduction.SlowlyVaryingQuantitativeTerminal
import ErdosProblems.Erdos186.PZ.SourceParameterAsymptotics

/-!
# Source parameter selection and the final one-step branch join

This module is downstream of the raw rank-change and equal-rank constructors.
It freezes the source parameters in their actual dependency order and then
joins the terminal rank cases into the power-controlled constructor consumed
by `FinalIteration.Partial.Package`.
-/

namespace Erdos186.PZ.OneStepAssembly

open Finset
open Filter
open scoped Topology
open FinalIteration
open FinalIteration.Partial

noncomputable section

set_option autoImplicit false

/-! ## Harmless normalization of the reduction constant -/

/-- Every terminal replacement result remains valid after increasing its
uniform volume constant.  This lets the final assembly replace the positive
constant returned by the abstract reduction boundary by `max 1 constant`. -/
def Reduction.IrreducibleReplacementResult.enlargeConstant
    {beta eta : ℝ}
    {context : Reduction.HigherDimensionalContext beta eta}
    {selector : Reduction.BoundedCFPSelector context}
    {d : ℕ} {B : CFP.IntegerBox d} {A : Finset (LatticePoint d)}
    {hA : selector.Eligible (Reduction.normalizeSet B A)}
    {epsilon delta gamma constant constant' : ℝ} {K : ℕ}
    (R : Reduction.IrreducibleReplacementResult selector B A hA epsilon
      delta gamma K constant)
    (hconstant : constant ≤ constant') :
    Reduction.IrreducibleReplacementResult selector B A hA epsilon
      delta gamma K constant' where
  ambientDimension := R.ambientDimension
  points := R.points
  eligible := R.eligible
  selector_strong_scale := R.selector_strong_scale
  selector_candidate_closed := R.selector_candidate_closed
  normalized_input_nonaveraging := R.normalized_input_nonaveraging
  input_card_preserved := R.input_card_preserved
  reachable := R.reachable
  nonaveraging := R.nonaveraging
  core_half := R.core_half
  irreducible := R.irreducible
  population_large := R.population_large
  high_rank_bound := by
    intro hrank
    calc
      ((selector.chosen R.points R.eligible).progression.volume : ℝ) ≤
          constant * (A.card : ℝ) ^
              (-(1 - epsilon) *
                ((selector.chosen R.points R.eligible).dimension - d : ℝ)) *
            (B.carrier.card : ℝ) := R.high_rank_bound hrank
      _ ≤ constant' * (A.card : ℝ) ^
              (-(1 - epsilon) *
                ((selector.chosen R.points R.eligible).dimension - d : ℝ)) *
            (B.carrier.card : ℝ) := by gcongr
  equal_rank_bound := by
    intro hrank
    calc
      ((selector.chosen R.points R.eligible).progression.volume : ℝ) ≤
          constant * ((R.points.card : ℝ) / (A.card : ℝ)) ^ K *
            (B.carrier.card : ℝ) := R.equal_rank_bound hrank
      _ ≤ constant' * ((R.points.card : ℝ) / (A.card : ℝ)) ^ K *
            (B.carrier.card : ℝ) := by gcongr
  low_rank_bound := by
    intro hrank
    exact (R.low_rank_bound hrank).trans
      (mul_le_mul_of_nonneg_right hconstant (Nat.cast_nonneg _))

/-- The sharp high-rank terminal estimate prevents the selected rank from
jumping by more than seven once the current population absorbs the fixed
reduction constant.  The bound is uniform because `epsilon < 1/3` and every
state has box cardinality at most the fourth power of its population. -/
theorem exists_replacement_selectedDimension_threshold
    {epsilon constant : ℝ} (hepsilon : epsilon < 1 / 3)
    (hconstant : 0 < constant) :
    ∃ pointThreshold : ℕ, 2 ≤ pointThreshold ∧
      ∀ {zeta beta eta delta gamma : ℝ}
        {context : Reduction.HigherDimensionalContext beta eta}
        {selector : Reduction.BoundedCFPSelector context}
        (current : State zeta)
        {hA : selector.Eligible
          (Reduction.normalizeSet (toCFPBox current.box) current.points)}
        {K : ℕ}
        (R : Reduction.IrreducibleReplacementResult selector
          (toCFPBox current.box) current.points hA epsilon delta gamma K
            constant),
        pointThreshold ≤ current.points.card →
        (selector.chosen R.points R.eligible).dimension ≤
          current.dimension + 7 := by
  obtain ⟨constantThreshold, hconstantThreshold⟩ :=
    exists_nat_gt (max 2 constant)
  refine ⟨constantThreshold, ?_, ?_⟩
  · have htwo : (2 : ℝ) < (constantThreshold : ℝ) :=
      (le_max_left 2 constant).trans_lt hconstantThreshold
    exact_mod_cast htwo.le
  · intro zeta beta eta delta gamma context selector current hA K R hlarge
    by_contra hnot
    have hrankGap : current.dimension + 7 <
        (selector.chosen R.points R.eligible).dimension :=
      Nat.lt_of_not_ge hnot
    have hrank : current.dimension <
        (selector.chosen R.points R.eligible).dimension := by omega
    have hdiffNat : 8 ≤
        (selector.chosen R.points R.eligible).dimension -
          current.dimension := by omega
    have hdiff : (8 : ℝ) ≤
        ((selector.chosen R.points R.eligible).dimension : ℝ) -
          (current.dimension : ℝ) := by
      calc
        (8 : ℝ) = ((8 : ℕ) : ℝ) := rfl
        _ ≤ (((selector.chosen R.points R.eligible).dimension -
            current.dimension : ℕ) : ℝ) := by exact_mod_cast hdiffNat
        _ = ((selector.chosen R.points R.eligible).dimension : ℝ) -
            (current.dimension : ℝ) := Nat.cast_sub hrank.le
    have honeMinus : (2 / 3 : ℝ) < 1 - epsilon := by linarith
    have hexponent :
        -(1 - epsilon) *
              (((selector.chosen R.points R.eligible).dimension : ℝ) -
                (current.dimension : ℝ)) + 4 ≤ -1 := by
      nlinarith
    have hcardTwo : 2 ≤ current.points.card := State.two_le_points_card current
    have hcardOneNat : 1 ≤ current.points.card := (by omega)
    have hcardOne : (1 : ℝ) ≤ (current.points.card : ℝ) := by
      exact_mod_cast hcardOneNat
    have hcardPos : (0 : ℝ) < (current.points.card : ℝ) :=
      zero_lt_one.trans_le hcardOne
    have hbox := State.box_card_le_points_card_rpow_four current
    have hboxRpow : (current.box.carrier.card : ℝ) ≤
        Real.rpow (current.points.card : ℝ) (4 : ℝ) := by
      simpa only [Real.rpow_eq_pow, Real.rpow_natCast] using hbox
    have hvolume :
        ((selector.chosen R.points R.eligible).progression.volume : ℝ) ≤
          constant * Real.rpow (current.points.card : ℝ) (-1 : ℝ) := by
      calc
        ((selector.chosen R.points R.eligible).progression.volume : ℝ) ≤
            constant * Real.rpow (current.points.card : ℝ)
                (-(1 - epsilon) *
                  (((selector.chosen R.points R.eligible).dimension : ℝ) -
                    (current.dimension : ℝ))) *
              (current.box.carrier.card : ℝ) := by
          simpa only [carrier_toCFPBox, Nat.cast_sub hrank.le] using
            R.high_rank_bound hrank
        _ ≤ constant * Real.rpow (current.points.card : ℝ)
                (-(1 - epsilon) *
                  (((selector.chosen R.points R.eligible).dimension : ℝ) -
                    (current.dimension : ℝ))) *
              Real.rpow (current.points.card : ℝ) (4 : ℝ) := by
          apply mul_le_mul_of_nonneg_left hboxRpow
          exact mul_nonneg hconstant.le (by
            rw [Real.rpow_eq_pow]
            exact Real.rpow_nonneg hcardPos.le _)
        _ = constant * Real.rpow (current.points.card : ℝ)
              (-(1 - epsilon) *
                  (((selector.chosen R.points R.eligible).dimension : ℝ) -
                    (current.dimension : ℝ)) + 4) := by
          simpa only [Real.rpow_eq_pow, mul_assoc] using
            congrArg (fun x : ℝ => constant * x)
            (Real.rpow_add hcardPos
              (-(1 - epsilon) *
                (((selector.chosen R.points R.eligible).dimension : ℝ) -
                  (current.dimension : ℝ))) 4).symm
        _ ≤ constant * Real.rpow (current.points.card : ℝ) (-1 : ℝ) := by
          exact mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_exponent_le hcardOne hexponent)
            hconstant.le
    have hconstantCast : constant < (current.points.card : ℝ) :=
      ((le_max_right 2 constant).trans_lt hconstantThreshold).trans_le
        (by exact_mod_cast hlarge)
    have hsmall : constant * Real.rpow (current.points.card : ℝ) (-1 : ℝ) < 1 := by
      have hneg : Real.rpow (current.points.card : ℝ) (-1 : ℝ) =
          (current.points.card : ℝ)⁻¹ := Real.rpow_neg_one _
      rw [hneg]
      calc
        constant * (current.points.card : ℝ)⁻¹ <
            (current.points.card : ℝ) * (current.points.card : ℝ)⁻¹ :=
          mul_lt_mul_of_pos_right hconstantCast (inv_pos.mpr hcardPos)
        _ = 1 := mul_inv_cancel₀ hcardPos.ne'
    have hpositive : (1 : ℝ) ≤
        ((selector.chosen R.points R.eligible).progression.volume : ℝ) := by
      have hvolumePos :
          0 < (selector.chosen R.points R.eligible).progression.volume := by
        rw [GAP.volume]
        exact Finset.prod_pos fun i _ =>
          (selector.chosen R.points R.eligible).progression.width_pos i
      have hvolumeOne : 1 ≤
          (selector.chosen R.points R.eligible).progression.volume := by omega
      exact_mod_cast hvolumeOne
    exact (not_lt_of_ge hpositive) (hvolume.trans_lt hsmall)

/-! ## Fixed source parameters after `C,C'`, `K`, and convex `deltaZero` -/

/-- Choose `mu`, `delta`, and `gamma` in the exact order required jointly by
Theorem 4, irreducible replacement, and convex density.  All parameters are
fixed before the population is seen; only the logarithmic lower bound is
absorbed by a final cardinality threshold. -/
theorem exists_fixed_sourceParameters
    {C C' deltaZero : ℝ} (hC' : 0 < C')
    (hdeltaZero : 0 < deltaZero) (K : ℕ) :
    ∃ mu delta gamma : ℝ, ∃ threshold : ℕ,
      0 < mu ∧ mu < 1 ∧ mu < deltaZero ∧
      0 < delta ∧ delta < 1 ∧ delta ≤ 1 / 8 ∧ delta < mu / 8 ∧
      0 < gamma ∧ gamma < 1 ∧
      gamma ≤ delta ^ C ∧ delta ≤ mu ^ C ∧
      gamma ≤ delta ^ K ∧ 16 ≤ threshold ∧
      ∀ {d : ℕ} (A : Finset (LatticePoint d)),
        threshold ≤ A.card →
        (Real.log (A.card : ℝ)) ^ (-(1 / C')) ≤ gamma := by
  let mu : ℝ := min (deltaZero / 2) (1 / 2)
  have hmu : 0 < mu := by
    dsimp only [mu]
    exact lt_min (half_pos hdeltaZero) (by norm_num)
  have hmuOne : mu < 1 := by
    calc
      mu ≤ 1 / 2 := min_le_right _ _
      _ < 1 := by norm_num
  have hmuDeltaZero : mu < deltaZero := by
    calc
      mu ≤ deltaZero / 2 := min_le_left _ _
      _ < deltaZero := by linarith
  let delta : ℝ := min (min ((mu ^ C) / 2) (mu / 16)) (1 / 16)
  have hmuPow : 0 < mu ^ C := Real.rpow_pos_of_pos hmu C
  have hdelta : 0 < delta := by
    dsimp only [delta]
    exact lt_min (lt_min (half_pos hmuPow) (by positivity)) (by norm_num)
  have hdeltaOne : delta < 1 := by
    calc
      delta ≤ 1 / 16 := min_le_right _ _
      _ < 1 := by norm_num
  have hdeltaEighth : delta ≤ 1 / 8 := by
    calc
      delta ≤ 1 / 16 := min_le_right _ _
      _ ≤ 1 / 8 := by norm_num
  have hdeltaMuEighth : delta < mu / 8 := by
    calc
      delta ≤ mu / 16 := (min_le_left _ _).trans (min_le_right _ _)
      _ < mu / 8 := by linarith
  have hdeltaMu : delta ≤ mu ^ C := by
    calc
      delta ≤ (mu ^ C) / 2 :=
        (min_le_left _ _).trans (min_le_left _ _)
      _ ≤ mu ^ C := by linarith
  let gammaBase : ℝ := min (min (delta ^ C) (delta ^ K)) 1
  let gamma : ℝ := gammaBase / 2
  have hdeltaRealPow : 0 < delta ^ C := Real.rpow_pos_of_pos hdelta C
  have hdeltaNatPow : 0 < delta ^ K := pow_pos hdelta K
  have hgammaBase : 0 < gammaBase := by
    dsimp only [gammaBase]
    exact lt_min (lt_min hdeltaRealPow hdeltaNatPow) zero_lt_one
  have hgamma : 0 < gamma := by
    dsimp only [gamma]
    exact half_pos hgammaBase
  have hgammaOne : gamma < 1 := by
    have hbaseOne : gammaBase ≤ 1 := min_le_right _ _
    dsimp only [gamma]
    linarith
  have hgammaDeltaReal : gamma ≤ delta ^ C := by
    have hbase : gammaBase ≤ delta ^ C :=
      (min_le_left _ _).trans (min_le_left _ _)
    dsimp only [gamma]
    linarith
  have hgammaDeltaNat : gamma ≤ delta ^ K := by
    have hbase : gammaBase ≤ delta ^ K :=
      (min_le_left _ _).trans (min_le_right _ _)
    dsimp only [gamma]
    linarith
  have hlogTendsto :
      Tendsto
        (fun N : ℕ ↦ (Real.log (N : ℝ)) ^ (-(1 / C')))
        atTop (𝓝 0) := by
    exact (tendsto_rpow_neg_atTop (one_div_pos.mpr hC')).comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hlogEventually :
      ∀ᶠ N : ℕ in atTop,
        (Real.log (N : ℝ)) ^ (-(1 / C')) < gamma :=
    hlogTendsto.eventually_lt_const hgamma
  obtain ⟨logThreshold, hlogThreshold⟩ := eventually_atTop.1 hlogEventually
  let threshold := max 16 logThreshold
  refine ⟨mu, delta, gamma, threshold, hmu, hmuOne, hmuDeltaZero,
    hdelta, hdeltaOne, hdeltaEighth, hdeltaMuEighth, hgamma, hgammaOne,
    hgammaDeltaReal, hdeltaMu,
    hgammaDeltaNat, ?_, ?_⟩
  · exact le_max_left _ _
  · intro d A hlarge
    exact (hlogThreshold A.card ((le_max_right 16 logThreshold).trans
      hlarge)).le

/-! ## Slowly varying source parameters -/

/-- The exact pointwise parameter package shared by Theorem 4 and the
irreducible-replacement theorem.  The parameters are evaluated at the
current population, as in the source proof. -/
structure SlowlyVaryingSourceHierarchy
    {d : ℕ} (A : Finset (LatticePoint d))
    (beta C C' kappa deltaZero : ℝ) (M K : ℕ) : Prop where
  theorem4 : Intersection.Theorem4Parameters A beta C C' M
    (Erdos186.delta kappa A.card)
    (Erdos186.gamma kappa (K : ℝ) A.card)
    (Erdos186.mu kappa A.card)
  delta_le_one_eighth : Erdos186.delta kappa A.card ≤ 1 / 8
  delta_lt_mu_div_eight :
    Erdos186.delta kappa A.card < Erdos186.mu kappa A.card / 8
  mu_lt_deltaZero : Erdos186.mu kappa A.card < deltaZero
  gamma_le_delta_nat :
    Erdos186.gamma kappa (K : ℝ) A.card ≤
      Erdos186.delta kappa A.card ^ K
  gamma_log_lower_half :
    (Real.log (A.card : ℝ)) ^ (-(1 / (2 * C'))) ≤
      Erdos186.gamma kappa (K : ℝ) A.card
  cubeRoot_inv_le_gamma :
    (A.card : ℝ) ^ (-(1 / 3 : ℝ)) ≤
      Erdos186.gamma kappa (K : ℝ) A.card

/-! ## Finite-dimensional envelopes for convex density and discrete John -/

/-- A finite nonempty family of positive real constants has a positive
common lower bound, chosen as its literal minimum. -/
theorem exists_pos_lowerBound_fin {n : ℕ} (hn : 0 < n)
    (f : Fin n → ℝ) (hf : ∀ i, 0 < f i) :
    ∃ lower : ℝ, 0 < lower ∧ ∀ i, lower ≤ f i := by
  let values : Finset ℝ := Finset.univ.image f
  have hvalues : values.Nonempty := by
    exact ⟨f ⟨0, hn⟩, Finset.mem_image_of_mem f (Finset.mem_univ _)⟩
  let lower := values.min' hvalues
  have hlowerMem : lower ∈ values := Finset.min'_mem values hvalues
  refine ⟨lower, ?_, ?_⟩
  · obtain ⟨i, _hi, hi⟩ := Finset.mem_image.mp hlowerMem
    rw [← hi]
    exact hf i
  · intro i
    exact Finset.min'_le values (f i)
      (Finset.mem_image_of_mem f (Finset.mem_univ i))

/-- A finite nonempty real family has a common upper bound, chosen as its
literal maximum. -/
theorem exists_upperBound_fin {n : ℕ} (hn : 0 < n) (f : Fin n → ℝ) :
    ∃ upper : ℝ, ∀ i, f i ≤ upper := by
  let values : Finset ℝ := Finset.univ.image f
  have hvalues : values.Nonempty := by
    exact ⟨f ⟨0, hn⟩, Finset.mem_image_of_mem f (Finset.mem_univ _)⟩
  exact ⟨values.max' hvalues, fun i =>
    Finset.le_max' values (f i)
      (Finset.mem_image_of_mem f (Finset.mem_univ i))⟩

/-- Natural-valued finite families likewise have a common upper bound. -/
theorem exists_nat_upperBound_fin {n : ℕ} (hn : 0 < n)
    (f : Fin n → ℕ) : ∃ upper : ℕ, ∀ i, f i ≤ upper := by
  let values : Finset ℕ := Finset.univ.image f
  have hvalues : values.Nonempty := by
    exact ⟨f ⟨0, hn⟩, Finset.mem_image_of_mem f (Finset.mem_univ _)⟩
  exact ⟨values.max' hvalues, fun i =>
    Finset.le_max' values (f i)
      (Finset.mem_image_of_mem f (Finset.mem_univ i))⟩

/-- Convex density and the unconditional rank-sensitive John theorem can be
chosen simultaneously in every positive dimension below a fixed ceiling.
Indexing by `Fin dimensionCeiling` represents the dimensions `i+1`; this
keeps every dependent Euclidean type at its literal dimension while exposing
all constants as finite families that can subsequently be minimized or
maximized. -/
theorem exists_boundedDimension_convexJohnRestrictionData
    (hConvexDensity : ConvexDensity.PZLemmaOneStatement)
    {convexLoss : ℝ} (hconvexLoss : 0 < convexLoss)
    (dimensionCeiling : ℕ) (hdimensionCeiling : 0 < dimensionCeiling) :
    ∃ tau deltaZero : Fin dimensionCeiling → ℝ,
      ∃ factorBound : Fin dimensionCeiling → ℕ,
      ∃ johnConstant : Fin dimensionCeiling → ℝ,
      ∀ i : Fin dimensionCeiling,
        0 < tau i ∧ tau i < 1 ∧ 0 < deltaZero i ∧
        1 ≤ johnConstant i ∧
        ∀ {delta : ℝ}, 0 < delta → delta < 1 →
          delta < deltaZero i →
          ∃ largeEnough : ℕ,
          ∀ (B : IntegerBox (i.1 + 1))
            (A : Finset (BoxPoint (i.1 + 1))),
            ConvexDensity.IsConvexBody (boxRealization B) →
            (Intersection.realImage A :
                Set (ConvexDensity.EuclideanPoint (i.1 + 1))) ⊆
              boxRealization B →
            A.Nonempty → largeEnough ≤ A.card →
            ConvexGeometry.IsDeltaConvexPosition delta
              (Intersection.realImage A) →
            1 ≤ delta * (B.carrier.card : ℝ) →
            ∃ eta : ℝ, eta ∈ Set.Icc delta (delta ^ tau i) ∧
              eta ≤ 1 ∧
              ∃ Omega : Set (ConvexDensity.EuclideanPoint (i.1 + 1)),
                Convex ℝ Omega ∧ Omega ⊆ boxRealization B ∧
                ConvexDensity.relativeVolume Omega (boxRealization B) ≤
                  ENNReal.ofReal eta ∧
                eta ^
                      (convexDensityExponent (i.1 + 1) +
                        convexLoss) * (A.card : ℝ) ≤
                    ((latticeRestriction A Omega).card : ℝ) ∧
                ∃ J : CenteredDiscreteJohnCertificate B Omega,
                  J.factor ≤ factorBound i ∧
                  (J.certificate.outer.volume : ℝ) ≤
                    johnConstant i * (B.carrier.card : ℝ) ∧
                  (J.rank < i.1 + 1 ∨
                    (J.rank = i.1 + 1 ∧
                      (J.certificate.outer.volume : ℝ) ≤
                        johnConstant i * eta *
                          (B.carrier.card : ℝ))) := by
  have hex : ∀ i : Fin dimensionCeiling,
      ∃ tau deltaZero : ℝ, ∃ factorBound : ℕ,
        ∃ johnConstant : ℝ,
        0 < tau ∧ tau < 1 ∧ 0 < deltaZero ∧
        1 ≤ johnConstant ∧
        ∀ {delta : ℝ}, 0 < delta → delta < 1 →
          delta < deltaZero →
          ∃ largeEnough : ℕ,
          ∀ (B : IntegerBox (i.1 + 1))
            (A : Finset (BoxPoint (i.1 + 1))),
            ConvexDensity.IsConvexBody (boxRealization B) →
            (Intersection.realImage A :
                Set (ConvexDensity.EuclideanPoint (i.1 + 1))) ⊆
              boxRealization B →
            A.Nonempty → largeEnough ≤ A.card →
            ConvexGeometry.IsDeltaConvexPosition delta
              (Intersection.realImage A) →
            1 ≤ delta * (B.carrier.card : ℝ) →
            ∃ eta : ℝ, eta ∈ Set.Icc delta (delta ^ tau) ∧
              eta ≤ 1 ∧
              ∃ Omega : Set (ConvexDensity.EuclideanPoint (i.1 + 1)),
                Convex ℝ Omega ∧ Omega ⊆ boxRealization B ∧
                ConvexDensity.relativeVolume Omega (boxRealization B) ≤
                  ENNReal.ofReal eta ∧
                eta ^
                      (convexDensityExponent (i.1 + 1) +
                        convexLoss) * (A.card : ℝ) ≤
                    ((latticeRestriction A Omega).card : ℝ) ∧
                ∃ J : CenteredDiscreteJohnCertificate B Omega,
                  J.factor ≤ factorBound ∧
                  (J.certificate.outer.volume : ℝ) ≤
                    johnConstant * (B.carrier.card : ℝ) ∧
                  (J.rank < i.1 + 1 ∨
                    (J.rank = i.1 + 1 ∧
                      (J.certificate.outer.volume : ℝ) ≤
                        johnConstant * eta *
                          (B.carrier.card : ℝ))) := by
    intro i
    exact exists_convexJohnRestrictionData hConvexDensity pzLemmaSeven
      (by omega : 1 ≤ i.1 + 1) (epsilon := convexLoss) hconvexLoss
  choose tau deltaZero factorBound johnConstant hdata using hex
  exact ⟨tau, deltaZero, factorBound, johnConstant, hdata⟩

/-- Finite-dimensional envelope for the concrete frozen-source reduction.
The context and retained-population exponent are fixed first; the finitely
many dimension-dependent reduction exponents, volume constants, and
thresholds are then replaced by common maxima. -/
theorem exists_boundedDimension_quantitativeTerminal_frozenSlowlyVarying
    (C : Reduction.HigherDimensionalContext
      (2 * ((4 : ℝ) + 1)) (1 / 2 : ℝ))
    (dimensionCeiling : ℕ) (hdimensionCeiling : 0 < dimensionCeiling)
    {epsilon p : ℝ} (hepsilon : 0 < epsilon)
    (hepsilonThird : epsilon < (1 / 3 : ℝ)) (hp : 0 < p) :
    ∃ K0 : ℕ, 1 ≤ K0 ∧
    ∃ reductionConstant : ℝ, 1 ≤ reductionConstant ∧
      ∀ kappa : ℝ, 0 < kappa →
      ∀ K : ℕ, K0 ≤ K →
        ∃ initialThreshold : ℕ, 2 ≤ initialThreshold ∧
          ∀ {zeta : ℝ} {initialCard : ℕ} (current : State zeta),
            current.dimension ≤ dimensionCeiling →
            Real.rpow (initialCard : ℝ) p ≤ (current.points.card : ℝ) →
            current.points.card ≤ initialCard →
            initialThreshold ≤ initialCard →
            ∃ hA : (C.scaleSelector
                (Reduction.guardedScaleExponent epsilon)).Eligible
              (Reduction.normalizeSet
                (toCFPBox current.box) current.points),
              Nonempty (Reduction.IrreducibleReplacementResult
                (C.scaleSelector (Reduction.guardedScaleExponent epsilon))
                (toCFPBox current.box) current.points hA epsilon
                  (Erdos186.delta kappa initialCard)
                  (Erdos186.gamma kappa (K : ℝ) initialCard) K
                  reductionConstant) := by
  have hdimensions : ∀ i : Fin dimensionCeiling,
      ∃ K0 : ℕ, 1 ≤ K0 ∧
      ∃ reductionConstant : ℝ, 0 < reductionConstant ∧
        ∀ kappa : ℝ, 0 < kappa →
        ∀ K : ℕ, K0 ≤ K →
          ∃ threshold : ℕ, 2 ≤ threshold ∧
          ∀ (initialCard : ℕ) (B : CFP.IntegerBox (i.1 + 1))
            (A : Finset (LatticePoint (i.1 + 1))),
            threshold ≤ initialCard →
            Real.rpow (initialCard : ℝ) p ≤ (A.card : ℝ) →
            A.card ≤ initialCard →
            A ⊆ B.carrier →
            (B.carrier.card : ℝ) ≤ Real.rpow (A.card : ℝ) 4 →
            IsBoxNonaveraging A →
            ∃ hA : (C.scaleSelector
                (Reduction.guardedScaleExponent epsilon)).Eligible
              (Reduction.normalizeSet B A),
              Nonempty (Reduction.IrreducibleReplacementResult
                (C.scaleSelector (Reduction.guardedScaleExponent epsilon)) B A
                hA epsilon (Erdos186.delta kappa initialCard)
                  (Erdos186.gamma kappa (K : ℝ) initialCard) K
                  reductionConstant) := by
    intro i
    simpa only [show (1 : ℝ) < 4 by norm_num,
      show (0 : ℝ) < 1 / 2 by norm_num,
      show (1 / 2 : ℝ) < 1 by norm_num] using
      (Reduction.exists_quantitative_terminal_frozenSlowlyVarying_exactSelector
        (i.1 + 1) (4 : ℝ) (1 / 2 : ℝ) C
          (by norm_num) (by norm_num) (by norm_num)
          epsilon hepsilon hepsilonThird p hp)
  choose K0 hK0 reductionConstant hreductionConstant hterminal
    using hdimensions
  obtain ⟨K0Upper, hK0Upper⟩ :=
    exists_nat_upperBound_fin hdimensionCeiling K0
  obtain ⟨constantUpper, hconstantUpper⟩ :=
    exists_upperBound_fin hdimensionCeiling reductionConstant
  let globalK0 := max 1 K0Upper
  let globalConstant := max 1 constantUpper
  have hglobalConstant : 1 ≤ globalConstant := le_max_left _ _
  refine ⟨globalK0, le_max_left _ _, globalConstant, hglobalConstant, ?_⟩
  intro kappa hkappa K hK
  have hthresholds : ∀ i : Fin dimensionCeiling,
      ∃ threshold : ℕ, 2 ≤ threshold ∧
          ∀ (initialCard : ℕ) (B : CFP.IntegerBox (i.1 + 1))
            (A : Finset (LatticePoint (i.1 + 1))),
            threshold ≤ initialCard →
            Real.rpow (initialCard : ℝ) p ≤ (A.card : ℝ) →
            A.card ≤ initialCard →
            A ⊆ B.carrier →
            (B.carrier.card : ℝ) ≤ Real.rpow (A.card : ℝ) 4 →
            IsBoxNonaveraging A →
            ∃ hA : (C.scaleSelector
                (Reduction.guardedScaleExponent epsilon)).Eligible
              (Reduction.normalizeSet B A),
              Nonempty (Reduction.IrreducibleReplacementResult
                (C.scaleSelector (Reduction.guardedScaleExponent epsilon)) B A
                hA epsilon (Erdos186.delta kappa initialCard)
                  (Erdos186.gamma kappa (K : ℝ) initialCard) K
                  (reductionConstant i)) := by
    intro i
    apply hterminal i kappa hkappa K
    exact (hK0Upper i).trans
      ((le_max_right 1 K0Upper).trans hK)
  choose threshold hthresholdTwo hreduce using hthresholds
  obtain ⟨thresholdUpper, hthresholdUpper⟩ :=
    exists_nat_upperBound_fin hdimensionCeiling threshold
  let initialThreshold := max 2 thresholdUpper
  refine ⟨initialThreshold, le_max_left _ _, ?_⟩
  intro zeta initialCard current hdimension hlower hupper hinitial
  have hdimensionPos : 0 < current.dimension := current.dimension_pos
  let i : Fin dimensionCeiling :=
    ⟨current.dimension - 1, by omega⟩
  have hi : i.1 + 1 = current.dimension := by
    dsimp only [i]
    omega
  have hthresholdInitial : threshold i ≤ initialCard :=
    (hthresholdUpper i).trans
      ((le_max_right 2 thresholdUpper).trans hinitial)
  have hsubset : current.points ⊆ (toCFPBox current.box).carrier := by
    simpa only [carrier_toCFPBox] using current.points_subset_box
  have hbox :
      ((toCFPBox current.box).carrier.card : ℝ) ≤
        (current.points.card : ℝ) ^ (4 : ℝ) := by
    simpa only [carrier_toCFPBox, Real.rpow_natCast] using
      State.box_card_le_points_card_rpow_four current
  have hreduceCurrent := hreduce i
  rw [hi] at hreduceCurrent
  obtain ⟨hA, ⟨R⟩⟩ :=
    hreduceCurrent initialCard (toCFPBox current.box) current.points
      hthresholdInitial hlower hupper hsubset hbox current.nonaveraging
  have hconstant : reductionConstant i ≤ globalConstant :=
    (hconstantUpper i).trans (le_max_right 1 constantUpper)
  exact ⟨hA,
    ⟨OneStepAssembly.Reduction.IrreducibleReplacementResult.enlargeConstant
      R hconstant⟩⟩

/-- Choose the slow exponent and an integral reduction exponent in the
correct dependency order after `C` and the reduction lower bound `K0` are
known. -/
theorem exists_kappa_reductionExponent
    {C : ℝ} (hC : 0 < C) (K0 : ℕ) :
    ∃ kappa : ℝ, ∃ K : ℕ,
      0 < kappa ∧ kappa < 1 ∧ kappa * C ≤ 1 ∧
      K0 ≤ K ∧ 1 ≤ K ∧ C ≤ (K : ℝ) := by
  let kappa : ℝ := min (1 / (2 * C)) (1 / 2)
  have hkappa : 0 < kappa := by
    dsimp only [kappa]
    exact lt_min (by positivity) (by norm_num)
  have hkappaOne : kappa < 1 := by
    calc
      kappa ≤ 1 / 2 := min_le_right _ _
      _ < 1 := by norm_num
  have hkappaC : kappa * C ≤ 1 := by
    have hkappaBound : kappa ≤ 1 / (2 * C) := min_le_left _ _
    have hmul := mul_le_mul_of_nonneg_right hkappaBound hC.le
    have hCne : C ≠ 0 := hC.ne'
    calc
      kappa * C ≤ (1 / (2 * C)) * C := hmul
      _ = 1 / 2 := by field_simp
      _ ≤ 1 := by norm_num
  obtain ⟨KC, hKC⟩ := exists_nat_ge C
  let K := max (max K0 1) KC
  have hK0 : K0 ≤ K := (le_max_left K0 1).trans (le_max_left _ KC)
  have hKOne : 1 ≤ K := (le_max_right K0 1).trans (le_max_left _ KC)
  have hKCeil : KC ≤ K := le_max_right _ KC
  have hCK : C ≤ (K : ℝ) := by
    exact hKC.trans (by exact_mod_cast hKCeil)
  exact ⟨kappa, K, hkappa, hkappaOne, hkappaC, hK0, hKOne, hCK⟩

/-- Rank-change scalar selection with an additional strict upper bound on
`epsilon`.  This is used after the frozen horizon has chosen `rho`, ensuring
the power-retention requirement `epsilon < rho`. -/
theorem exists_rankChange_scalarHierarchy_below
    {zeta cap : ℝ} (hzeta : 0 < zeta) (hcap : 0 < cap)
    (dimensionCeiling : ℕ) (hceiling : 0 < dimensionCeiling) :
    ∃ epsilon changeGain slack : ℝ,
      0 < epsilon ∧ epsilon < (1 / 3 : ℝ) ∧ epsilon ≤ 1 ∧
      epsilon < cap ∧ 0 < changeGain ∧ 0 < slack ∧
      epsilon ≤ zeta / (4 * (dimensionCeiling : ℝ)) ∧
      4 * changeGain + slack + epsilon ≤ zeta / 2 ∧
      ∀ {lower upper : ℕ}, 0 < lower → lower < upper →
        upper ≤ dimensionCeiling →
        changeGain + epsilon + slack ≤
          boxExponent upper - boxExponent lower := by
  let reducedZeta : ℝ :=
    min zeta (2 * (dimensionCeiling : ℝ) * cap)
  have hceilingReal : (0 : ℝ) < (dimensionCeiling : ℝ) := by
    exact_mod_cast hceiling
  have hreduced : 0 < reducedZeta := by
    dsimp only [reducedZeta]
    exact lt_min hzeta (by positivity)
  obtain ⟨epsilon, changeGain, slack, hepsilon, hepsilonThird,
      hepsilonOne, hchangeGain, hslack, hepsilonSmall, hbudget, hgap⟩ :=
    exists_rankChange_scalarHierarchy hreduced dimensionCeiling hceiling
  have hreducedZeta : reducedZeta ≤ zeta := min_le_left _ _
  have hreducedCap : reducedZeta ≤
      2 * (dimensionCeiling : ℝ) * cap := min_le_right _ _
  have hepsilonCapHalf : epsilon ≤ cap / 2 := by
    calc
      epsilon ≤ reducedZeta / (4 * (dimensionCeiling : ℝ)) :=
        hepsilonSmall
      _ ≤ (2 * (dimensionCeiling : ℝ) * cap) /
          (4 * (dimensionCeiling : ℝ)) := by
        exact div_le_div_of_nonneg_right hreducedCap (by positivity)
      _ = cap / 2 := by field_simp <;> norm_num
  refine ⟨epsilon, changeGain, slack, hepsilon, hepsilonThird,
    hepsilonOne, ?_, hchangeGain, hslack, ?_, ?_, hgap⟩
  · linarith
  · exact hepsilonSmall.trans (div_le_div_of_nonneg_right hreducedZeta
      (by positivity))
  · exact hbudget.trans (div_le_div_of_nonneg_right hreducedZeta
      (by norm_num))

/-- Freeze the rank-change gain and absorption slack before choosing
`epsilon`.  Every smaller positive epsilon satisfies the same source
hierarchy, removing the apparent cycle between the horizon's `rho` and the
reduction power loss. -/
theorem exists_rankChange_gainSlack_epsilonCap
    {zeta : ℝ} (hzeta : 0 < zeta)
    (dimensionCeiling : ℕ) (hceiling : 0 < dimensionCeiling) :
    ∃ changeGain slack epsilonCap : ℝ,
      0 < changeGain ∧ 0 < slack ∧ 0 < epsilonCap ∧
      ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ epsilonCap →
        epsilon < (1 / 3 : ℝ) ∧ epsilon ≤ 1 ∧
        epsilon ≤ zeta / (4 * (dimensionCeiling : ℝ)) ∧
        4 * changeGain + slack + epsilon ≤ zeta / 2 ∧
        ∀ {lower upper : ℕ}, 0 < lower → lower < upper →
          upper ≤ dimensionCeiling →
          changeGain + epsilon + slack ≤
            boxExponent upper - boxExponent lower := by
  obtain ⟨epsilonCap, changeGain, slack, hepsilonCap, hthird, hone,
      hchangeGain, hslack, hsmall, hbudget, hgap⟩ :=
    exists_rankChange_scalarHierarchy hzeta dimensionCeiling hceiling
  refine ⟨changeGain, slack, epsilonCap, hchangeGain, hslack,
    hepsilonCap, ?_⟩
  intro epsilon hepsilon hepsilonLe
  refine ⟨hepsilonLe.trans_lt hthird, hepsilonLe.trans hone,
    hepsilonLe.trans hsmall, ?_, ?_⟩
  · linarith
  · intro lower upper hlower hlt hupper
    exact (by linarith : changeGain + epsilon + slack ≤
      changeGain + epsilonCap + slack).trans
        (hgap hlower hlt hupper)

/-- Once `kappa` is chosen below one and with `kappa*C ≤ 1`, and `K`
dominates the source exponent `C`, all pointwise source relations hold above
one uniform population threshold.  In particular this proves the strict
separation `delta < mu/8` needed by the half-core intersection constructor. -/
theorem exists_slowlyVaryingSourceHierarchy_threshold
    {beta C C' kappa deltaZero : ℝ} (K : ℕ)
    (hbeta : 1 < beta) (hC : 0 < C) (hC' : 0 < C')
    (hkappa : 0 < kappa) (hkappaOne : kappa < 1)
    (hkappaC : kappa * C ≤ 1) (hCK : C ≤ (K : ℝ))
    (hK : 1 ≤ K) (hdeltaZero : 0 < deltaZero) :
    ∃ M : ℕ, 2 ≤ M ∧
      ∀ {d : ℕ} (A : Finset (LatticePoint d)), M ≤ A.card →
        SlowlyVaryingSourceHierarchy A beta C C' kappa deltaZero M K := by
  have hKreal : (0 : ℝ) < (K : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 1) hK)
  have hfactorExponent : 0 < 1 - kappa := sub_pos.mpr hkappaOne
  have hfactorTendsto : Tendsto
      (fun N : ℕ ↦ Erdos186.delta kappa N ^ (1 - kappa))
      atTop (𝓝 0) := by
    simpa only [Real.zero_rpow hfactorExponent.ne'] using
      (Erdos186.tendsto_delta_zero hkappa).rpow_const
        (Or.inr hfactorExponent.le)
  have hdeltaEighth : ∀ᶠ N : ℕ in atTop,
      Erdos186.delta kappa N < 1 / 8 :=
    (Erdos186.tendsto_delta_zero hkappa).eventually_lt_const (by norm_num)
  have hmuDeltaZero : ∀ᶠ N : ℕ in atTop,
      Erdos186.mu kappa N < deltaZero :=
    (Erdos186.tendsto_mu_zero hkappa).eventually_lt_const hdeltaZero
  have hfactorSmall : ∀ᶠ N : ℕ in atTop,
      Erdos186.delta kappa N ^ (1 - kappa) < 1 / 8 :=
    hfactorTendsto.eventually_lt_const (by norm_num)
  have hgammaLog := Erdos186.eventually_log_rpow_neg_le_gamma
    kappa (K : ℝ) (one_div_pos.mpr hC')
  have hgammaLogHalf := Erdos186.eventually_log_rpow_neg_le_gamma
    kappa (K : ℝ) (by positivity : (0 : ℝ) < 1 / (2 * C'))
  have hdeltaRange := Erdos186.eventually_delta_mem_Ioo hkappa
  have hgammaRange := Erdos186.eventually_gamma_mem_Ioo hkappa hKreal
  have hmuRange := Erdos186.eventually_mu_mem_Ioo hkappa
  have hgammaDelta := Erdos186.eventually_gamma_le_delta_rpow
    hkappa hCK
  have hdeltaMu := Erdos186.eventually_delta_le_mu_rpow hkappa hkappaC
  have hcubeRoot := Erdos186.eventually_cubeRoot_inv_le_gamma
    kappa (K : ℝ)
  have hall : ∀ᶠ N : ℕ in atTop,
      Erdos186.delta kappa N < 1 / 8 ∧
      Erdos186.mu kappa N < deltaZero ∧
      Erdos186.delta kappa N ^ (1 - kappa) < 1 / 8 ∧
      Erdos186.delta kappa N ∈ Set.Ioo (0 : ℝ) 1 ∧
      Erdos186.gamma kappa (K : ℝ) N ∈ Set.Ioo (0 : ℝ) 1 ∧
      Erdos186.mu kappa N ∈ Set.Ioo (0 : ℝ) 1 ∧
      (Real.log (N : ℝ)) ^ (-(1 / C')) ≤
        Erdos186.gamma kappa (K : ℝ) N ∧
      (Real.log (N : ℝ)) ^ (-(1 / (2 * C'))) ≤
        Erdos186.gamma kappa (K : ℝ) N ∧
      Erdos186.gamma kappa (K : ℝ) N ≤
        Erdos186.delta kappa N ^ C ∧
      Erdos186.delta kappa N ≤ Erdos186.mu kappa N ^ C ∧
      (N : ℝ) ^ (-(1 / 3 : ℝ)) ≤
        Erdos186.gamma kappa (K : ℝ) N := by
    filter_upwards [hdeltaEighth, hmuDeltaZero, hfactorSmall,
      hdeltaRange, hgammaRange, hmuRange, hgammaLog, hgammaLogHalf, hgammaDelta,
      hdeltaMu, hcubeRoot] with N hd8 hmu0 hfac hd hg hm hlog hlogHalf
        hgd hdm hc
    exact ⟨hd8, hmu0, hfac, hd, hg, hm, hlog, hlogHalf, hgd, hdm, hc⟩
  obtain ⟨sourceThreshold, hsource⟩ := eventually_atTop.1 hall
  let M := max 2 sourceThreshold
  refine ⟨M, le_max_left _ _, ?_⟩
  intro d A hlarge
  have hs := hsource A.card
    ((le_max_right 2 sourceThreshold).trans hlarge)
  rcases hs with ⟨hd8, hmu0, hfac, hd, hg, hm, hlog, hlogHalf,
    hgd, hdm, hc⟩
  have hdeltaMuEight :
      Erdos186.delta kappa A.card < Erdos186.mu kappa A.card / 8 := by
    have hsplit : Erdos186.delta kappa A.card =
        Erdos186.mu kappa A.card *
          Erdos186.delta kappa A.card ^ (1 - kappa) := by
      calc
        Erdos186.delta kappa A.card =
            Erdos186.delta kappa A.card ^ (1 : ℝ) :=
          (Real.rpow_one _).symm
        _ = Erdos186.delta kappa A.card ^ (kappa + (1 - kappa)) := by
          ring_nf
        _ = Erdos186.delta kappa A.card ^ kappa *
              Erdos186.delta kappa A.card ^ (1 - kappa) :=
          Real.rpow_add hd.1 kappa (1 - kappa)
        _ = Erdos186.mu kappa A.card *
              Erdos186.delta kappa A.card ^ (1 - kappa) := by
          rfl
    rw [hsplit]
    nlinarith [hm.1, hfac]
  have hgammaNat :
      Erdos186.gamma kappa (K : ℝ) A.card =
        Erdos186.delta kappa A.card ^ K := by
    simp [Erdos186.gamma]
  exact {
    theorem4 := {
      beta_gt_one := hbeta
      C_pos := hC
      C'_pos := hC'
      delta_pos := hd.1
      gamma_pos := hg.1
      mu_pos := hm.1
      delta_lt_one := hd.2
      gamma_lt_one := hg.2
      mu_lt_one := hm.2
      gamma_le_delta := hgd
      delta_le_mu := hdm
      gamma_log_lower := hlog
      card_large := hlarge }
    delta_le_one_eighth := hd8.le
    delta_lt_mu_div_eight := hdeltaMuEight
    mu_lt_deltaZero := hmu0
    gamma_le_delta_nat := hgammaNat.le
    gamma_log_lower_half := hlogHalf
    cubeRoot_inv_le_gamma := hc }

/-- The spare half of the logarithmic exponent transports the source lower
bound from the current population to every terminal population retained by
irreducible replacement. -/
theorem exists_terminal_gammaLogLower_threshold
    {epsilon C' : ℝ} (hepsilonOne : epsilon < 1) (hC' : 0 < C') :
    ∃ threshold : ℕ, 2 ≤ threshold ∧
      ∀ {currentCard terminalCard : ℕ} {gamma : ℝ},
        threshold ≤ currentCard →
        (currentCard : ℝ) ^ (1 - epsilon) < (terminalCard : ℝ) →
        (Real.log (currentCard : ℝ)) ^ (-(1 / (2 * C'))) ≤ gamma →
        (Real.log (terminalCard : ℝ)) ^ (-(1 / C')) ≤ gamma := by
  let a : ℝ := 1 - epsilon
  let q : ℝ := 1 / C'
  have ha : 0 < a := sub_pos.mpr hepsilonOne
  have hq : 0 < q := one_div_pos.mpr hC'
  have hqHalf : 0 < q / 2 := half_pos hq
  have hlogPowTendsto : Tendsto
      (fun N : ℕ ↦ Real.log (N : ℝ) ^ (q / 2)) atTop atTop :=
    (tendsto_rpow_atTop hqHalf).comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hconstantEventually : ∀ᶠ N : ℕ in atTop,
      a ^ (-q) ≤ Real.log (N : ℝ) ^ (q / 2) :=
    hlogPowTendsto.eventually_ge_atTop (a ^ (-q))
  have hlogEventually : ∀ᶠ N : ℕ in atTop,
      0 < Real.log (N : ℝ) :=
    (Real.tendsto_log_atTop.comp
      tendsto_natCast_atTop_atTop).eventually_gt_atTop 0
  have hall : ∀ᶠ N : ℕ in atTop,
      a ^ (-q) ≤ Real.log (N : ℝ) ^ (q / 2) ∧
        0 < Real.log (N : ℝ) :=
    hconstantEventually.and hlogEventually
  obtain ⟨growthThreshold, hgrowth⟩ := eventually_atTop.1 hall
  let threshold := max 2 growthThreshold
  refine ⟨threshold, le_max_left _ _, ?_⟩
  intro currentCard terminalCard gamma hlarge hterminal hgamma
  have hgrowthCurrent := hgrowth currentCard
    ((le_max_right 2 growthThreshold).trans hlarge)
  have hcurrentPos : (0 : ℝ) < (currentCard : ℝ) := by
    have htwo : 2 ≤ currentCard :=
      (le_max_left 2 growthThreshold).trans hlarge
    exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2) htwo)
  have hterminalPos : (0 : ℝ) < (terminalCard : ℝ) :=
    (Real.rpow_pos_of_pos hcurrentPos _).trans hterminal
  have hterminalLog :
      a * Real.log (currentCard : ℝ) <
        Real.log (terminalCard : ℝ) := by
    have hlog := Real.log_lt_log
      (Real.rpow_pos_of_pos hcurrentPos _) hterminal
    rw [Real.log_rpow hcurrentPos] at hlog
    exact hlog
  have hbasePos :
      0 < a * Real.log (currentCard : ℝ) :=
    mul_pos ha hgrowthCurrent.2
  have hreverse :
      Real.log (terminalCard : ℝ) ^ (-q) ≤
        (a * Real.log (currentCard : ℝ)) ^ (-q) :=
    Real.rpow_le_rpow_of_nonpos hbasePos hterminalLog.le
      (neg_nonpos.mpr hq.le)
  have hsplit :
      (a * Real.log (currentCard : ℝ)) ^ (-q) =
        a ^ (-q) * Real.log (currentCard : ℝ) ^ (-q) :=
    Real.mul_rpow ha.le hgrowthCurrent.2.le
  have hscale :
      a ^ (-q) * Real.log (currentCard : ℝ) ^ (-q) ≤
        Real.log (currentCard : ℝ) ^ (-(q / 2)) := by
    calc
      a ^ (-q) * Real.log (currentCard : ℝ) ^ (-q) ≤
          Real.log (currentCard : ℝ) ^ (q / 2) *
            Real.log (currentCard : ℝ) ^ (-q) :=
        mul_le_mul_of_nonneg_right hgrowthCurrent.1
          (Real.rpow_nonneg hgrowthCurrent.2.le _)
      _ = Real.log (currentCard : ℝ) ^ (-(q / 2)) := by
        rw [← Real.rpow_add hgrowthCurrent.2]
        congr 1
        ring
  calc
    Real.log (terminalCard : ℝ) ^ (-(1 / C')) =
        Real.log (terminalCard : ℝ) ^ (-q) := by rfl
    _ ≤ (a * Real.log (currentCard : ℝ)) ^ (-q) := hreverse
    _ = a ^ (-q) * Real.log (currentCard : ℝ) ^ (-q) := hsplit
    _ ≤ Real.log (currentCard : ℝ) ^ (-(q / 2)) := hscale
    _ = Real.log (currentCard : ℝ) ^ (-(1 / (2 * C'))) := by
      congr 1
      dsimp only [q]
      field_simp
    _ ≤ gamma := hgamma

/-- The terminal population retained by reduction is eventually large
enough for the half-core mass estimate even though `mu` is evaluated at the
current population. -/
theorem exists_terminal_muPopulation_threshold
    {epsilon kappa : ℝ} (hepsilonOne : epsilon < 1) :
    ∃ threshold : ℕ, 2 ≤ threshold ∧
      ∀ {currentCard terminalCard : ℕ},
        threshold ≤ currentCard →
        (currentCard : ℝ) ^ (1 - epsilon) < (terminalCard : ℝ) →
        32 / Erdos186.mu kappa currentCard ≤ (terminalCard : ℝ) := by
  let a : ℝ := 1 - epsilon
  let q : ℝ := a / 2
  have ha : 0 < a := sub_pos.mpr hepsilonOne
  have hq : 0 < q := half_pos ha
  have hmuLower : ∀ᶠ N : ℕ in atTop,
      (N : ℝ) ^ (-q) ≤ Erdos186.mu kappa N := by
    simpa only [Erdos186.mu, Erdos186.gamma] using
      Erdos186.eventually_nat_rpow_neg_le_gamma kappa kappa hq
  have hgrowth : ∀ᶠ N : ℕ in atTop, (32 : ℝ) ≤ (N : ℝ) ^ q :=
    ((nat_rpow_tendsto_atTop hq).eventually_ge_atTop 32)
  have hall : ∀ᶠ N : ℕ in atTop,
      (N : ℝ) ^ (-q) ≤ Erdos186.mu kappa N ∧
        (32 : ℝ) ≤ (N : ℝ) ^ q ∧ 0 < N :=
    hmuLower.and (hgrowth.and (eventually_gt_atTop 0))
  obtain ⟨growthThreshold, hgrowthThreshold⟩ := eventually_atTop.1 hall
  let threshold := max 2 growthThreshold
  refine ⟨threshold, le_max_left _ _, ?_⟩
  intro currentCard terminalCard hlarge hterminal
  have hbounds := hgrowthThreshold currentCard
    ((le_max_right 2 growthThreshold).trans hlarge)
  have hcurrentPos : (0 : ℝ) < (currentCard : ℝ) := by
    exact_mod_cast hbounds.2.2
  have hmuPos : 0 < Erdos186.mu kappa currentCard :=
    (Real.rpow_pos_of_pos hcurrentPos (-q)).trans_le hbounds.1
  have hmuPower : (32 : ℝ) ≤ Erdos186.mu kappa currentCard *
      (currentCard : ℝ) ^ a := by
    calc
      (32 : ℝ) ≤ (currentCard : ℝ) ^ q := hbounds.2.1
      _ = (currentCard : ℝ) ^ (-q) *
            (currentCard : ℝ) ^ a := by
        rw [← Real.rpow_add hcurrentPos]
        congr 1
        dsimp only [q]
        ring
      _ ≤ Erdos186.mu kappa currentCard *
            (currentCard : ℝ) ^ a :=
        mul_le_mul_of_nonneg_right hbounds.1
          (Real.rpow_nonneg hcurrentPos.le _)
  calc
    32 / Erdos186.mu kappa currentCard ≤
        (currentCard : ℝ) ^ a :=
      (div_le_iff₀ hmuPos).2 (by simpa [mul_comm] using hmuPower)
    _ ≤ (terminalCard : ℝ) := hterminal.le

/-- Slowly varying `delta` absorbs the power gap between `epsilon` and
`rho`, giving the exact controlled rank-change retention estimate. -/
theorem exists_slowlyVarying_rankChangePower_threshold
    {epsilon rho kappa : ℝ} (hepsilonRho : epsilon < rho) :
    ∃ threshold : ℕ, 2 ≤ threshold ∧
      ∀ {currentCard terminalCard : ℕ},
        threshold ≤ currentCard →
        (currentCard : ℝ) ^ (1 - epsilon) < (terminalCard : ℝ) →
        (currentCard : ℝ) ^ (1 - rho) ≤
          Erdos186.delta kappa currentCard * (terminalCard : ℝ) := by
  let q : ℝ := (rho - epsilon) / 2
  have hq : 0 < q := half_pos (sub_pos.mpr hepsilonRho)
  have hdeltaLower : ∀ᶠ N : ℕ in atTop,
      (N : ℝ) ^ (-q) ≤ Erdos186.delta kappa N :=
    Erdos186.eventually_nat_rpow_neg_le_delta kappa hq
  have hall : ∀ᶠ N : ℕ in atTop,
      (N : ℝ) ^ (-q) ≤ Erdos186.delta kappa N ∧ 1 ≤ N :=
    hdeltaLower.and (eventually_ge_atTop 1)
  obtain ⟨growthThreshold, hgrowth⟩ := eventually_atTop.1 hall
  let threshold := max 2 growthThreshold
  refine ⟨threshold, le_max_left _ _, ?_⟩
  intro currentCard terminalCard hlarge hterminal
  have hbounds := hgrowth currentCard
    ((le_max_right 2 growthThreshold).trans hlarge)
  have hcurrentOne : (1 : ℝ) ≤ (currentCard : ℝ) := by
    exact_mod_cast hbounds.2
  have hcurrentPos : (0 : ℝ) < (currentCard : ℝ) :=
    zero_lt_one.trans_le hcurrentOne
  have hdeltaPos : 0 < Erdos186.delta kappa currentCard :=
    (Real.rpow_pos_of_pos hcurrentPos (-q)).trans_le hbounds.1
  have hexponent : 1 - rho ≤ 1 - epsilon - q := by
    dsimp only [q]
    linarith
  calc
    (currentCard : ℝ) ^ (1 - rho) ≤
        (currentCard : ℝ) ^ (1 - epsilon - q) :=
      Real.rpow_le_rpow_of_exponent_le hcurrentOne hexponent
    _ = (currentCard : ℝ) ^ (-q) *
          (currentCard : ℝ) ^ (1 - epsilon) := by
      rw [← Real.rpow_add hcurrentPos]
      congr 1
      ring
    _ ≤ Erdos186.delta kappa currentCard *
          (currentCard : ℝ) ^ (1 - epsilon) :=
      mul_le_mul_of_nonneg_right hbounds.1
        (Real.rpow_nonneg hcurrentPos.le _)
    _ ≤ Erdos186.delta kappa currentCard * (terminalCard : ℝ) :=
      (mul_lt_mul_of_pos_left hterminal hdeltaPos).le

/-- Any logarithmic source cost which is `o(log N)` is uniformly absorbed
by the exact real population floor `N^p ≤ m`.  This is the common numerical
bridge used after the source parameters have been frozen at the initial
population, while the current population ranges over a maximal-run trace. -/
theorem exists_frozen_logBudget_threshold
    (cost : ℕ → ℝ)
    (hcost : Tendsto
      (fun N : ℕ ↦ cost N / Real.log (N : ℝ)) atTop (𝓝 0))
    {p rate : ℝ} (hp : 0 < p) (hrate : 0 < rate) (fixedCost : ℝ) :
    ∃ threshold : ℕ, 2 ≤ threshold ∧
      ∀ {initialCard currentCard : ℕ}, threshold ≤ initialCard →
        (initialCard : ℝ) ^ p ≤ (currentCard : ℝ) →
        fixedCost + cost initialCard ≤
          rate * Real.log (currentCard : ℝ) := by
  let cap : ℝ := rate * p / 2
  have hcap : 0 < cap := by
    dsimp only [cap]
    positivity
  have hratio : ∀ᶠ N : ℕ in atTop,
      cost N / Real.log (N : ℝ) < cap :=
    hcost.eventually_lt_const hcap
  have hfixed : ∀ᶠ N : ℕ in atTop,
      fixedCost ≤ cap * Real.log (N : ℝ) :=
    ((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop
      hcap).eventually_ge_atTop fixedCost
  have hlog : ∀ᶠ N : ℕ in atTop, 0 < Real.log (N : ℝ) :=
    (Real.tendsto_log_atTop.comp
      tendsto_natCast_atTop_atTop).eventually_gt_atTop 0
  obtain ⟨growthThreshold, hgrowth⟩ :=
    eventually_atTop.1 (hratio.and (hfixed.and hlog))
  let threshold := max 2 growthThreshold
  refine ⟨threshold, le_max_left _ _, ?_⟩
  intro initialCard currentCard hinitial hlower
  obtain ⟨hratioN, hfixedN, hlogN⟩ := hgrowth initialCard
    ((le_max_right 2 growthThreshold).trans hinitial)
  have hinitialPos : (0 : ℝ) < (initialCard : ℝ) := by
    have hinitialTwo : 2 ≤ initialCard :=
      (le_max_left 2 growthThreshold).trans hinitial
    exact_mod_cast (show 0 < initialCard by omega)
  have hcurrentPos : (0 : ℝ) < (currentCard : ℝ) :=
    (Real.rpow_pos_of_pos hinitialPos p).trans_le hlower
  have hlogLower :
      p * Real.log (initialCard : ℝ) ≤
        Real.log (currentCard : ℝ) := by
    calc
      p * Real.log (initialCard : ℝ) =
          Real.log ((initialCard : ℝ) ^ p) := by
        rw [Real.log_rpow hinitialPos]
      _ ≤ Real.log (currentCard : ℝ) :=
        Real.log_le_log (Real.rpow_pos_of_pos hinitialPos p) hlower
  have hcostN : cost initialCard < cap * Real.log (initialCard : ℝ) :=
    (div_lt_iff₀ hlogN).mp hratioN
  calc
    fixedCost + cost initialCard ≤
        cap * Real.log (initialCard : ℝ) +
          cap * Real.log (initialCard : ℝ) :=
      add_le_add hfixedN hcostN.le
    _ = rate * (p * Real.log (initialCard : ℝ)) := by
      dsimp only [cap]
      ring
    _ ≤ rate * Real.log (currentCard : ℝ) :=
      mul_le_mul_of_nonneg_left hlogLower hrate.le

/-- A fixed scalar burden is absorbed by any positive multiple of the
current logarithmic population above one natural threshold. -/
theorem exists_fixed_logBudget_threshold
    (fixedCost : ℝ) {rate : ℝ} (hrate : 0 < rate) :
    ∃ threshold : ℕ, 2 ≤ threshold ∧
      ∀ {currentCard : ℕ}, threshold ≤ currentCard →
        fixedCost ≤ rate * Real.log (currentCard : ℝ) := by
  have hgrowth : Tendsto
      (fun N : ℕ ↦ rate * Real.log (N : ℝ)) atTop atTop :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop
      hrate
  obtain ⟨growthThreshold, hgrowthThreshold⟩ := eventually_atTop.1
    (hgrowth.eventually_ge_atTop fixedCost)
  let threshold := max 2 growthThreshold
  refine ⟨threshold, le_max_left _ _, ?_⟩
  intro currentCard hlarge
  exact hgrowthThreshold currentCard
    ((le_max_right 2 growthThreshold).trans hlarge)

/-- Frozen `delta` has logarithmic cost `o(log N)`, so every positive
retained-population exponent absorbs it uniformly. -/
theorem exists_frozen_delta_logBudget_threshold
    (kappa : ℝ) {p rate : ℝ} (hp : 0 < p) (hrate : 0 < rate)
    (fixedCost : ℝ) :
    ∃ threshold : ℕ, 2 ≤ threshold ∧
      ∀ {initialCard currentCard : ℕ}, threshold ≤ initialCard →
        (initialCard : ℝ) ^ p ≤ (currentCard : ℝ) →
        fixedCost - Real.log (Erdos186.delta kappa initialCard) ≤
          rate * Real.log (currentCard : ℝ) := by
  simpa only [sub_eq_add_neg] using
    exists_frozen_logBudget_threshold
      (fun N : ℕ ↦ -Real.log (Erdos186.delta kappa N))
      (Erdos186.PZ.tendsto_neg_log_delta_div_log_zero kappa)
      hp hrate fixedCost

/-- The same frozen power-range bridge for a fixed multiple of
`-log mu`. -/
theorem exists_frozen_mu_logBudget_threshold
    (kappa densityCeiling : ℝ) {p rate : ℝ}
    (hp : 0 < p) (hrate : 0 < rate) (fixedCost : ℝ) :
    ∃ threshold : ℕ, 2 ≤ threshold ∧
      ∀ {initialCard currentCard : ℕ}, threshold ≤ initialCard →
        (initialCard : ℝ) ^ p ≤ (currentCard : ℝ) →
        fixedCost + densityCeiling *
            (-Real.log (Erdos186.mu kappa initialCard)) ≤
          rate * Real.log (currentCard : ℝ) := by
  have hmu : Tendsto
      (fun N : ℕ ↦
        (densityCeiling * (-Real.log (Erdos186.mu kappa N))) /
          Real.log (N : ℝ)) atTop (𝓝 0) := by
    have hbase :=
      (Erdos186.PZ.tendsto_neg_log_mu_div_log_zero kappa).const_mul
        densityCeiling
    simpa only [mul_zero] using hbase.congr'
      (Filter.Eventually.of_forall (fun N : ℕ ↦ by ring))
  exact exists_frozen_logBudget_threshold
    (fun N : ℕ ↦ densityCeiling *
      (-Real.log (Erdos186.mu kappa N))) hmu hp hrate fixedCost

/-- The slowly varying core-retention loss is logarithmically negligible, so
the fixed reduction constant and `-log delta` fit in the rank-change slack
uniformly above one current-state threshold. -/
theorem exists_slowlyVarying_rankChangeAbsorption_threshold
    {zeta changeGain constant slack kappa : ℝ}
    (hchangeGain : 0 < changeGain) (hslack : 0 < slack) :
    ∃ pointThreshold : ℕ, 2 ≤ pointThreshold ∧
      ∀ (current : State zeta) (newDimension : ℕ),
        0 < newDimension → pointThreshold ≤ current.points.card →
        (boxExponent newDimension + zeta +
            (current.excess + changeGain)) * Real.log constant -
              Real.log (Erdos186.delta kappa current.points.card) ≤
          slack * Real.log (current.points.card : ℝ) := by
  let fixedBurden : ℝ :=
    max (2 + zeta + changeGain) 0 * max (Real.log constant) 0
  have hfixedBurden : 0 ≤ fixedBurden := by
    dsimp only [fixedBurden]
    positivity
  have hdeltaEventually : ∀ᶠ N : ℕ in atTop,
      -Real.log (Erdos186.delta kappa N) /
          Real.log (N : ℝ) < slack / 2 :=
    (Erdos186.PZ.tendsto_neg_log_delta_div_log_zero kappa).eventually_lt_const
      (half_pos hslack)
  have hlogEventually : ∀ᶠ N : ℕ in atTop,
      0 < Real.log (N : ℝ) :=
    (Real.tendsto_log_atTop.comp
      tendsto_natCast_atTop_atTop).eventually_gt_atTop 0
  obtain ⟨ratioThreshold, hratioThreshold⟩ :=
    eventually_atTop.1 (hdeltaEventually.and hlogEventually)
  obtain ⟨fixedThreshold, hfixedThreshold⟩ :=
    exists_nat_gt (max 2 (Real.exp (2 * fixedBurden / slack)))
  let pointThreshold := max fixedThreshold ratioThreshold
  refine ⟨pointThreshold, ?_, ?_⟩
  · have htwo : (2 : ℝ) < (fixedThreshold : ℝ) :=
      (le_max_left 2 (Real.exp (2 * fixedBurden / slack))).trans_lt
        hfixedThreshold
    exact (by exact_mod_cast htwo.le : 2 ≤ fixedThreshold).trans
      (le_max_left _ _)
  · intro current newDimension hnewDimension hlarge
    have hlargeFixed : fixedThreshold ≤ current.points.card :=
      (le_max_left fixedThreshold ratioThreshold).trans hlarge
    have hlargeRatio : ratioThreshold ≤ current.points.card :=
      (le_max_right fixedThreshold ratioThreshold).trans hlarge
    have hratio := hratioThreshold current.points.card hlargeRatio
    have hnewExponentPos : 0 < boxExponent newDimension + zeta +
        (current.excess + changeGain) := by
      have hbox := boxExponent_pos hnewDimension
      linarith [current.zeta_pos, current.excess_nonneg]
    have hnewExponentLe : boxExponent newDimension + zeta +
          (current.excess + changeGain) ≤ 2 + zeta + changeGain := by
      have hbox := boxExponent_lt_one hnewDimension
      have hexcess := current.excess_le_one
      linarith
    have hfixedCost :
        (boxExponent newDimension + zeta +
            (current.excess + changeGain)) * Real.log constant ≤
          fixedBurden := by
      have hlogConstant :
          Real.log constant ≤ max (Real.log constant) 0 := le_max_left _ _
      have hmaxLog : 0 ≤ max (Real.log constant) 0 := le_max_right _ _
      dsimp only [fixedBurden]
      calc
        (boxExponent newDimension + zeta +
              (current.excess + changeGain)) * Real.log constant ≤
            (boxExponent newDimension + zeta +
              (current.excess + changeGain)) *
                max (Real.log constant) 0 :=
          mul_le_mul_of_nonneg_left hlogConstant hnewExponentPos.le
        _ ≤ (2 + zeta + changeGain) * max (Real.log constant) 0 :=
          mul_le_mul_of_nonneg_right hnewExponentLe hmaxLog
        _ ≤ max (2 + zeta + changeGain) 0 *
              max (Real.log constant) 0 :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hmaxLog
    have hcardCast : (fixedThreshold : ℝ) ≤
        (current.points.card : ℝ) := by exact_mod_cast hlargeFixed
    have hexpLt : Real.exp (2 * fixedBurden / slack) <
        (current.points.card : ℝ) :=
      ((le_max_right 2 (Real.exp (2 * fixedBurden / slack))).trans_lt
        hfixedThreshold).trans_le hcardCast
    have hcardPos : (0 : ℝ) < (current.points.card : ℝ) :=
      (Real.exp_pos _).trans hexpLt
    have hlogLarge : 2 * fixedBurden / slack <
        Real.log (current.points.card : ℝ) :=
      (Real.lt_log_iff_exp_lt hcardPos).2 hexpLt
    have hfixedAbsorb : fixedBurden <
        slack / 2 * Real.log (current.points.card : ℝ) := by
      have := (div_lt_iff₀ hslack).mp hlogLarge
      nlinarith
    have hdeltaAbsorb :
        -Real.log (Erdos186.delta kappa current.points.card) <
          slack / 2 * Real.log (current.points.card : ℝ) := by
      exact (div_lt_iff₀ hratio.2).mp hratio.1
    linarith

/-- Frozen-parameter version of the rank-change constant absorption.  The
initial source value `delta κ N` is paid from the exact power-range floor
`N^p ≤ |current|`, so the natural stopping threshold remains independent of
the initial counterexample. -/
theorem exists_frozen_rankChangeAbsorption_threshold
    {zeta changeGain constant slack kappa p : ℝ}
    (hchangeGain : 0 < changeGain) (hslack : 0 < slack) (hp : 0 < p) :
    ∃ initialThreshold : ℕ, 2 ≤ initialThreshold ∧
      ∀ {initialCard : ℕ} (current : State zeta) (newDimension : ℕ),
        initialThreshold ≤ initialCard →
        (initialCard : ℝ) ^ p ≤ (current.points.card : ℝ) →
        0 < newDimension →
        (boxExponent newDimension + zeta +
            (current.excess + changeGain)) * Real.log constant -
              Real.log (Erdos186.delta kappa initialCard) ≤
          slack * Real.log (current.points.card : ℝ) := by
  let fixedBurden : ℝ :=
    max (2 + zeta + changeGain) 0 * max (Real.log constant) 0
  obtain ⟨initialThreshold, hthresholdTwo, habsorb⟩ :=
    exists_frozen_delta_logBudget_threshold kappa hp hslack fixedBurden
  refine ⟨initialThreshold, hthresholdTwo, ?_⟩
  intro initialCard current newDimension hinitial hlower hnewDimension
  have hnewExponentPos : 0 < boxExponent newDimension + zeta +
      (current.excess + changeGain) := by
    have hbox := boxExponent_pos hnewDimension
    linarith [current.zeta_pos, current.excess_nonneg]
  have hnewExponentLe : boxExponent newDimension + zeta +
        (current.excess + changeGain) ≤ 2 + zeta + changeGain := by
    have hbox := boxExponent_lt_one hnewDimension
    have hexcess := current.excess_le_one
    linarith
  have hfixedCost :
      (boxExponent newDimension + zeta +
          (current.excess + changeGain)) * Real.log constant ≤
        fixedBurden := by
    have hlogConstant :
        Real.log constant ≤ max (Real.log constant) 0 := le_max_left _ _
    have hmaxLog : 0 ≤ max (Real.log constant) 0 := le_max_right _ _
    dsimp only [fixedBurden]
    calc
      (boxExponent newDimension + zeta +
            (current.excess + changeGain)) * Real.log constant ≤
          (boxExponent newDimension + zeta +
            (current.excess + changeGain)) *
              max (Real.log constant) 0 :=
        mul_le_mul_of_nonneg_left hlogConstant hnewExponentPos.le
      _ ≤ (2 + zeta + changeGain) * max (Real.log constant) 0 :=
        mul_le_mul_of_nonneg_right hnewExponentLe hmaxLog
      _ ≤ max (2 + zeta + changeGain) 0 *
            max (Real.log constant) 0 :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) hmaxLog
  exact (sub_le_sub_right hfixedCost
    (Real.log (Erdos186.delta kappa initialCard))).trans
      (by simpa only [sub_eq_add_neg] using habsorb hinitial hlower)

/-! The optional near-full-loss route remains available below for consumers
which possess a terminal ambient-dimension envelope.  The final branch join
uses `Intersection.highCoefficient_massBudget_of_halfCore` and does not
require one. -/

/-! ## The near-full canonical core supplies the specialized intersection mass -/

/-- After `delta` and `mu` have been frozen with the source separation
`delta < mu / 4`, the canonical CFP loss is uniformly small enough in every
dimension below the global ceiling to supply all three fields of the
source-specialized post-CFP hierarchy. -/
theorem exists_scaleSelector_sourceSpecializedMassHierarchy_threshold
    {beta eta exponent delta mu : ℝ}
    (C : Reduction.HigherDimensionalContext beta eta)
    (dimensionCeiling : ℕ) (hmu : 0 < mu)
    (hdeltaMu : delta < mu / 4) :
    ∃ threshold : ℕ, 16 ≤ threshold ∧
      ∀ {d : ℕ}, d ≤ dimensionCeiling →
      ∀ (A : Finset (LatticePoint d))
        (hA : (C.scaleSelector exponent).Eligible A),
        threshold ≤ A.card →
        Intersection.SourceSpecializedMassHierarchy
          (C.scaleSelector exponent) A hA delta mu := by
  let xi : ℝ := min ((mu - 4 * delta) / (2 * mu)) (1 / 2)
  have hgap : 0 < mu - 4 * delta := by linarith
  have hxi : 0 < xi := by
    dsimp only [xi]
    exact lt_min (div_pos hgap (mul_pos (by norm_num) hmu)) (by norm_num)
  have hxiGap : xi ≤ (mu - 4 * delta) / (2 * mu) :=
    min_le_left _ _
  have hxiHalf : xi ≤ 1 / 2 := min_le_right _ _
  obtain ⟨lossThreshold, hlossThresholdTwo, hloss⟩ :=
    Reduction.exists_scaleSelector_loss_fraction_threshold_boundedDimension
      (exponent := exponent) C dimensionCeiling hxi
  obtain ⟨capThreshold, hcapThreshold⟩ := exists_nat_gt (32 / mu)
  let threshold := max 16 (max lossThreshold capThreshold)
  refine ⟨threshold, le_max_left _ _, ?_⟩
  intro d hd A hA hlarge
  have hlossLarge : lossThreshold ≤ A.card :=
    (le_max_left lossThreshold capThreshold).trans
      ((le_max_right 16 (max lossThreshold capThreshold)).trans hlarge)
  have hcapLarge : capThreshold ≤ A.card :=
    (le_max_right lossThreshold capThreshold).trans
      ((le_max_right 16 (max lossThreshold capThreshold)).trans hlarge)
  have hlossBound :
      (((C.scaleSelector exponent).chosen A hA).loss : ℝ) ≤
        xi * (A.card : ℝ) :=
    hloss hd A hA hlossLarge
  have hcardPos : (0 : ℝ) < (A.card : ℝ) := by
    have hsixteen : 16 ≤ A.card :=
      (le_max_left 16 (max lossThreshold capThreshold)).trans hlarge
    exact_mod_cast (by omega : 0 < A.card)
  have hmuLoss :
      mu * (((C.scaleSelector exponent).chosen A hA).loss : ℝ) ≤
        mu * xi * (A.card : ℝ) := by
    calc
      mu * (((C.scaleSelector exponent).chosen A hA).loss : ℝ) ≤
          mu * (xi * (A.card : ℝ)) :=
        mul_le_mul_of_nonneg_left hlossBound hmu.le
      _ = mu * xi * (A.card : ℝ) := by ring
  have hcapCast : (capThreshold : ℝ) ≤ (A.card : ℝ) := by
    exact_mod_cast hcapLarge
  have hpopulationLarge : 32 / mu < (A.card : ℝ) :=
    hcapThreshold.trans_le hcapCast
  have hsixteen : 16 < mu * (A.card : ℝ) / 2 := by
    have hscaled := (div_lt_iff₀ hmu).mp hpopulationLarge
    nlinarith
  have hcap :
      16 + mu * (((C.scaleSelector exponent).chosen A hA).loss : ℝ) ≤
        mu * (A.card : ℝ) := by
    have hxiScaled : mu * xi ≤ mu / 2 :=
      (mul_le_mul_of_nonneg_left hxiHalf hmu.le).trans_eq (by ring)
    have hxiPopulation : mu * xi * (A.card : ℝ) ≤
        mu * (A.card : ℝ) / 2 := by
      calc
        mu * xi * (A.card : ℝ) ≤
            (mu / 2) * (A.card : ℝ) :=
          mul_le_mul_of_nonneg_right hxiScaled hcardPos.le
        _ = mu * (A.card : ℝ) / 2 := by ring
    linarith
  have hcoefficient : 4 * delta + mu * xi < mu := by
    have hmulGap : mu * xi ≤ (mu - 4 * delta) / 2 := by
      have hmul := mul_le_mul_of_nonneg_left hxiGap hmu.le
      have hmuNe : mu ≠ 0 := hmu.ne'
      calc
        mu * xi ≤ mu * ((mu - 4 * delta) / (2 * mu)) := hmul
        _ = (mu - 4 * delta) / 2 := by field_simp
    linarith
  have hdensity :
      4 * delta * (A.card : ℝ) +
          mu * (((C.scaleSelector exponent).chosen A hA).loss : ℝ) <
        mu * (A.card : ℝ) := by
    have hcoefficientPopulation :=
      mul_lt_mul_of_pos_right hcoefficient hcardPos
    nlinarith
  exact {
    delta_lt_mu_div_four := hdeltaMu
    cap_after_selectedLoss := hcap
    density_after_selectedLoss := hdensity }

/-- The terminal population lower bound in irreducible replacement lifts any
fixed terminal-cardinality threshold to a uniform threshold on the current
state. -/
theorem exists_replacement_terminalPopulation_threshold
    {epsilon : ℝ} (hepsilonOne : epsilon < 1)
    (terminalThreshold : ℕ) :
    ∃ pointThreshold : ℕ, 2 ≤ pointThreshold ∧
      ∀ {beta eta zeta : ℝ}
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
        terminalThreshold ≤ R.points.card := by
  have hexponent : 0 < 1 - epsilon := sub_pos.mpr hepsilonOne
  have heventually : ∀ᶠ m : ℕ in atTop,
      (terminalThreshold : ℝ) ≤ (m : ℝ) ^ (1 - epsilon) :=
    (nat_rpow_tendsto_atTop hexponent).eventually_ge_atTop terminalThreshold
  obtain ⟨growthThreshold, hgrowth⟩ := eventually_atTop.1 heventually
  let pointThreshold := max 2 growthThreshold
  refine ⟨pointThreshold, le_max_left _ _, ?_⟩
  intro beta eta zeta context selector current hA delta gamma K constant R
    hlarge
  have hgrowthLarge : growthThreshold ≤ current.points.card :=
    (le_max_right 2 growthThreshold).trans hlarge
  have hterminalCast : (terminalThreshold : ℝ) < (R.points.card : ℝ) :=
    (hgrowth current.points.card hgrowthLarge).trans_lt R.population_large
  exact_mod_cast hterminalCast.le

/-- Upgrade the slowly varying hierarchy evaluated at the current population
to the literal Theorem 4 parameter record on the terminal replacement set.
Only the cardinal threshold and logarithmic lower bound change; the stronger
half-log field supplies the latter. -/
theorem exists_terminal_theorem4Parameters_threshold
    {epsilon C' : ℝ} (hepsilonOne : epsilon < 1) (hC' : 0 < C')
    (M : ℕ) :
    ∃ pointThreshold : ℕ, 2 ≤ pointThreshold ∧
      ∀ {zeta beta C kappa deltaZero : ℝ} {K : ℕ}
        {contextBeta contextEta constant : ℝ}
        {context : Reduction.HigherDimensionalContext contextBeta contextEta}
        {selector : Reduction.BoundedCFPSelector context}
        (current : State zeta)
        {hA : selector.Eligible
          (Reduction.normalizeSet (toCFPBox current.box) current.points)}
        (H : SlowlyVaryingSourceHierarchy current.points beta C C' kappa
          deltaZero M K)
        (R : Reduction.IrreducibleReplacementResult selector
          (toCFPBox current.box) current.points hA epsilon
            (Erdos186.delta kappa current.points.card)
            (Erdos186.gamma kappa (K : ℝ) current.points.card) K
            constant),
        pointThreshold ≤ current.points.card →
        Intersection.Theorem4Parameters R.points beta C C' M
          (Erdos186.delta kappa current.points.card)
          (Erdos186.gamma kappa (K : ℝ) current.points.card)
          (Erdos186.mu kappa current.points.card) := by
  obtain ⟨logThreshold, hlogThresholdTwo, hlog⟩ :=
    exists_terminal_gammaLogLower_threshold hepsilonOne hC'
  obtain ⟨cardThreshold, hcardThresholdTwo, hcard⟩ :=
    exists_replacement_terminalPopulation_threshold hepsilonOne M
  let pointThreshold := max logThreshold cardThreshold
  refine ⟨pointThreshold, ?_, ?_⟩
  · exact hlogThresholdTwo.trans (le_max_left _ _)
  · intro zeta beta C kappa deltaZero K contextBeta contextEta constant
      context selector current hA H R hlarge
    have hlargeLog : logThreshold ≤ current.points.card :=
      (le_max_left logThreshold cardThreshold).trans hlarge
    have hlargeCard : cardThreshold ≤ current.points.card :=
      (le_max_right logThreshold cardThreshold).trans hlarge
    exact {
      H.theorem4 with
      gamma_log_lower := hlog hlargeLog R.population_large
        H.gamma_log_lower_half
      card_large := hcard current R hlargeCard }

/-- One uniform current-state threshold supplies both intersection budgets
for every terminal replacement result: the public core-retention inequality
and the exact high-coefficient mass budget.  This route uses only `R.core_half`
and therefore has no terminal ambient-dimension dependency. -/
theorem exists_terminal_halfCoreIntersectionBudgets_threshold
    {epsilon delta mu : ℝ} (hepsilonOne : epsilon < 1)
    (hmu : 0 < mu) (hdeltaEighth : delta ≤ 1 / 8)
    (hdeltaMu : delta < mu / 8) :
    ∃ pointThreshold : ℕ, 2 ≤ pointThreshold ∧
      ∀ {beta eta zeta : ℝ}
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
        delta * (R.points.card : ℝ) ≤
            ((((selector.chosen R.points R.eligible).identifiedCore.card - 2) /
              2 : ℕ) : ℝ) ∧
          (R.points.card : ℝ) *
                Intersection.sourceCoefficientThreshold R.points.card +
              delta * (R.points.card : ℝ) *
                (mu *
                  ((selector.chosen R.points R.eligible).identifiedCore.card :
                    ℝ))⁻¹ <
            (1 - 2 *
                (mu *
                  ((selector.chosen R.points R.eligible).identifiedCore.card :
                    ℝ))⁻¹) / 2 := by
  obtain ⟨capThreshold, hcapThreshold⟩ := exists_nat_gt (32 / mu)
  let terminalThreshold := max 16 capThreshold
  obtain ⟨pointThreshold, hpointThresholdTwo, hterminalLarge⟩ :=
    exists_replacement_terminalPopulation_threshold hepsilonOne
      terminalThreshold
  refine ⟨pointThreshold, hpointThresholdTwo, ?_⟩
  intro beta eta zeta context selector current hA gamma K constant R hlarge
  have hterminal : terminalThreshold ≤ R.points.card :=
    hterminalLarge current R hlarge
  have hsixteen : 16 ≤ R.points.card :=
    (le_max_left 16 capThreshold).trans hterminal
  have hcapCard : capThreshold ≤ R.points.card :=
    (le_max_right 16 capThreshold).trans hterminal
  have hcapCast : (capThreshold : ℝ) ≤ (R.points.card : ℝ) := by
    exact_mod_cast hcapCard
  have hpopulationLarge : 32 / mu ≤ (R.points.card : ℝ) :=
    (hcapThreshold.trans_le hcapCast).le
  constructor
  · exact Reduction.density_mul_card_le_half_core_sub_two
      hdeltaEighth hsixteen R.core_half
  · exact Intersection.highCoefficient_massBudget_of_halfCore
      (selector.eligible_nonempty R.eligible).card_pos hmu hdeltaMu
      R.core_half hpopulationLarge

/-- Current-population version of the complete terminal intersection
numerics.  It simultaneously transports the Theorem 4 parameter record and
derives both half-core budgets for the unchanged slowly varying parameters. -/
theorem exists_slowlyVarying_terminalIntersectionBudgets_threshold
    {epsilon C' kappa : ℝ} (hepsilonOne : epsilon < 1) (hC' : 0 < C')
    (M : ℕ) :
    ∃ pointThreshold : ℕ, 2 ≤ pointThreshold ∧
      ∀ {zeta beta C deltaZero : ℝ} {K : ℕ}
        {contextBeta contextEta constant : ℝ}
        {context : Reduction.HigherDimensionalContext contextBeta contextEta}
        {selector : Reduction.BoundedCFPSelector context}
        (current : State zeta)
        {hA : selector.Eligible
          (Reduction.normalizeSet (toCFPBox current.box) current.points)}
        (H : SlowlyVaryingSourceHierarchy current.points beta C C' kappa
          deltaZero M K)
        (R : Reduction.IrreducibleReplacementResult selector
          (toCFPBox current.box) current.points hA epsilon
            (Erdos186.delta kappa current.points.card)
            (Erdos186.gamma kappa (K : ℝ) current.points.card) K constant),
        pointThreshold ≤ current.points.card →
        Intersection.Theorem4Parameters R.points beta C C' M
            (Erdos186.delta kappa current.points.card)
            (Erdos186.gamma kappa (K : ℝ) current.points.card)
            (Erdos186.mu kappa current.points.card) ∧
          Erdos186.delta kappa current.points.card *
              (R.points.card : ℝ) ≤
            ((((selector.chosen R.points R.eligible).identifiedCore.card - 2) /
              2 : ℕ) : ℝ) ∧
          (R.points.card : ℝ) *
                Intersection.sourceCoefficientThreshold R.points.card +
              Erdos186.delta kappa current.points.card *
                (R.points.card : ℝ) *
                (Erdos186.mu kappa current.points.card *
                  ((selector.chosen R.points R.eligible).identifiedCore.card :
                    ℝ))⁻¹ <
            (1 - 2 *
                (Erdos186.mu kappa current.points.card *
                  ((selector.chosen R.points R.eligible).identifiedCore.card :
                    ℝ))⁻¹) / 2 := by
  obtain ⟨theoremThreshold, htheoremThresholdTwo, htheorem⟩ :=
    exists_terminal_theorem4Parameters_threshold hepsilonOne hC' M
  obtain ⟨massThreshold, hmassThresholdTwo, hmassPopulation⟩ :=
    exists_terminal_muPopulation_threshold
      (kappa := kappa) hepsilonOne
  let pointThreshold := max theoremThreshold massThreshold
  refine ⟨pointThreshold, htheoremThresholdTwo.trans (le_max_left _ _), ?_⟩
  intro zeta beta C deltaZero K contextBeta contextEta constant context
    selector current hA H R hlarge
  have hlargeTheorem : theoremThreshold ≤ current.points.card :=
    (le_max_left theoremThreshold massThreshold).trans hlarge
  have hlargeMass : massThreshold ≤ current.points.card :=
    (le_max_right theoremThreshold massThreshold).trans hlarge
  have hparams := htheorem current H R hlargeTheorem
  have hpopulation : 32 / Erdos186.mu kappa current.points.card ≤
      (R.points.card : ℝ) :=
    hmassPopulation hlargeMass R.population_large
  have hmuPos : 0 < Erdos186.mu kappa current.points.card :=
    H.theorem4.mu_pos
  have hthirtytwo : (32 : ℝ) <
      32 / Erdos186.mu kappa current.points.card := by
    rw [lt_div_iff₀ hmuPos]
    nlinarith [H.theorem4.mu_lt_one]
  have hsixteen : 16 ≤ R.points.card := by
    have : (16 : ℝ) < (R.points.card : ℝ) := by
      linarith [hthirtytwo.trans_le hpopulation]
    exact_mod_cast this.le
  refine ⟨hparams, ?_, ?_⟩
  · exact Reduction.density_mul_card_le_half_core_sub_two
      H.delta_le_one_eighth hsixteen R.core_half
  · exact Intersection.highCoefficient_massBudget_of_halfCore
      (selector.eligible_nonempty R.eligible).card_pos hmuPos
      H.delta_lt_mu_div_eight R.core_half hpopulation

/-- The current-state threshold simultaneously supplies the public
core-retention inequality consumed by Theorem 4 and the stronger
source-specialized mass hierarchy for its actual post-CFP construction. -/
theorem exists_terminal_intersectionHierarchies_threshold
    {beta eta exponent epsilon delta mu : ℝ}
    (C : Reduction.HigherDimensionalContext beta eta)
    (dimensionCeiling : ℕ) (hepsilonOne : epsilon < 1)
    (hmu : 0 < mu) (hdeltaEighth : delta ≤ 1 / 8)
    (hdeltaMu : delta < mu / 4) :
    ∃ pointThreshold : ℕ, 2 ≤ pointThreshold ∧
      ∀ {zeta : ℝ} (current : State zeta),
        current.dimension ≤ dimensionCeiling →
        ∀ {hA : (C.scaleSelector exponent).Eligible
          (Reduction.normalizeSet (toCFPBox current.box) current.points)}
          {gamma : ℝ} {K : ℕ} {constant : ℝ}
          (R : Reduction.IrreducibleReplacementResult
            (C.scaleSelector exponent) (toCFPBox current.box) current.points
              hA epsilon delta gamma K constant),
          R.ambientDimension ≤ dimensionCeiling →
          pointThreshold ≤ current.points.card →
          delta * (R.points.card : ℝ) ≤
              (((((C.scaleSelector exponent).chosen R.points R.eligible).identifiedCore.card - 2) /
                2 : ℕ) : ℝ) ∧
            Intersection.SourceSpecializedMassHierarchy
              (C.scaleSelector exponent) R.points R.eligible delta mu := by
  obtain ⟨terminalThreshold, hterminalThresholdSixteen, hsource⟩ :=
    exists_scaleSelector_sourceSpecializedMassHierarchy_threshold
      (exponent := exponent) (delta := delta) C dimensionCeiling hmu hdeltaMu
  obtain ⟨pointThreshold, hpointThresholdTwo, hterminalLarge⟩ :=
    exists_replacement_terminalPopulation_threshold hepsilonOne
      terminalThreshold
  refine ⟨pointThreshold, hpointThresholdTwo, ?_⟩
  intro zeta current _hcurrentDimension hA gamma K constant R
    hterminalDimension hlarge
  have hterminal : terminalThreshold ≤ R.points.card :=
    hterminalLarge current R hlarge
  have hsixteen : 16 ≤ R.points.card :=
    hterminalThresholdSixteen.trans hterminal
  constructor
  · exact Reduction.density_mul_card_le_half_core_sub_two
      hdeltaEighth hsixteen R.core_half
  · exact hsource hterminalDimension R.points R.eligible hterminal

/-! ## The actual terminal-rank branch join -/

/-- The exact analytic data produced by convex density and the unconditional
rank-sensitive John theorem in the terminal equal-selected-rank case.  The
two remaining scalar certificates are stated branchwise because a John rank
drop spends `changeGain`, while full John rank spends `sameGain`. -/
def EqualRankJohnBranchReady
    {beta eta zeta changeGain sameGain rho : ℝ}
    {context : Reduction.HigherDimensionalContext beta eta}
    {selector : Reduction.BoundedCFPSelector context}
    (current : State zeta)
    {hA : selector.Eligible
      (Reduction.normalizeSet (toCFPBox current.box) current.points)}
    {epsilon delta gamma : ℝ} {K : ℕ} {reductionConstant : ℝ}
    (R : Reduction.IrreducibleReplacementResult selector
      (toCFPBox current.box) current.points hA epsilon delta gamma K
        reductionConstant) : Prop :=
  ∃ convexScale johnConstant : ℝ,
    0 < convexScale ∧ convexScale ≤ 1 ∧ 1 ≤ johnConstant ∧
    ∃ Omega : Set (ConvexDensity.EuclideanPoint
        (selector.chosen R.points R.eligible).dimension),
      ∃ J : CenteredDiscreteJohnCertificate
          (gapCoefficientBox
            (selector.chosen R.points R.eligible).progression) Omega,
        2 ≤ (latticeRestriction
            (selector.chosen R.points R.eligible).identifiedCore Omega).card ∧
        convexScale ^
              (convexDensityExponent current.dimension + zeta / 2) *
            ((selector.chosen R.points R.eligible).identifiedCore.card : ℝ) ≤
          ((latticeRestriction
            (selector.chosen R.points R.eligible).identifiedCore Omega).card :
              ℝ) ∧
        (J.rank < (selector.chosen R.points R.eligible).dimension ∨
          (J.rank = (selector.chosen R.points R.eligible).dimension ∧
            (J.certificate.outer.volume : ℝ) ≤
              johnConstant * convexScale *
                ((selector.chosen R.points R.eligible).progression.volume :
                  ℝ))) ∧
        sameStepBoxConstant johnConstant reductionConstant (1 / 2) K *
              convexScale ≤
            convexScale ^ sameRunA current.dimension zeta ∧
        (J.rank < (selector.chosen R.points R.eligible).dimension →
          -((convexDensityExponent current.dimension + zeta / 2) *
                Real.log convexScale +
              Real.log (replacementStructuralRatio (1 / 2) R current)) ≤
            rho * Real.log (current.points.card : ℝ)) ∧
        (J.rank < (selector.chosen R.points R.eligible).dimension →
          (boxExponent J.rank + zeta + (current.excess + changeGain)) *
              Real.log (J.certificate.outer.volume : ℝ) <
            Real.log
              ((latticeRestriction
                (selector.chosen R.points R.eligible).identifiedCore Omega).card :
                ℝ)) ∧
        (J.rank = (selector.chosen R.points R.eligible).dimension →
          (boxExponent J.rank + zeta + (current.excess + sameGain)) *
                Real.log
                  (sameStepBoxConstant johnConstant reductionConstant
                    (1 / 2) K) +
              ((boxExponent J.rank + zeta +
                    (current.excess + sameGain)) -
                  (convexDensityExponent current.dimension + zeta / 2)) *
                Real.log convexScale +
              ((boxExponent J.rank + zeta +
                    (current.excess + sameGain)) * (K : ℝ) - 1) *
                Real.log (replacementStructuralRatio (1 / 2) R current) +
              ((boxExponent J.rank + zeta +
                    (current.excess + sameGain)) *
                    (boxExponent current.dimension + zeta +
                      current.excess)⁻¹ - 1) *
                Real.log (current.points.card : ℝ) ≤ 0)

/-- The source-specialized post-CFP constructor proves convex position
directly from capped convex pools.  This formulation avoids routing the
argument through the obsolete all-purpose `Theorem4Parameters` boundary:
the only scalar premise needed to extract the capped combination is
`0 < mu`, while every source hierarchy is discharged by `hpost`. -/
theorem Reduction.IrreducibleReplacementResult.identifiedCore_isDeltaConvexPosition_of_convexPoolsPost
    {beta eta : ℝ}
    {context : Reduction.HigherDimensionalContext beta eta}
    {selector : Reduction.BoundedCFPSelector context}
    {ell : ℕ} {B : CFP.IntegerBox ell}
    {A : Finset (LatticePoint ell)}
    {hA : selector.Eligible (Reduction.normalizeSet B A)}
    {epsilon delta gamma mu : ℝ} {K : ℕ} {constant : ℝ}
    (R : Reduction.IrreducibleReplacementResult selector B A hA
      epsilon delta gamma K constant)
    (hmu : 0 < mu)
    (hpost :
      ∀ {a₀ : Intersection.realImage
          (selector.chosen R.points R.eligible).identifiedCore}
        {c : Intersection.realImage
          (selector.chosen R.points R.eligible).identifiedCore → ℝ}
        (D : Intersection.ConvexPoolsData
          (selector.chosen R.points R.eligible).identifiedCore a₀ c mu),
        ∃ Dout : Intersection.Theorem4PostCFPData
            (selector.chosen R.points R.eligible).identifiedCore,
          Dout.a = D.a) :
    ConvexGeometry.IsDeltaConvexPosition mu
      (Intersection.realImage
        (selector.chosen R.points R.eligible).identifiedCore) := by
  by_contra hfail
  obtain ⟨a₀, c, hc, hsum, hcenter⟩ :=
    ConvexCombination.exists_capped_centered_combination_of_not_isDeltaConvexPosition
      hmu hfail
  have hc' : ∀ x, 0 ≤ c x ∧
      c x ≤ (mu *
        (selector.chosen R.points R.eligible).identifiedCore.card)⁻¹ := by
    simpa only [Intersection.card_realImage] using hc
  let D := Classical.choice
    (Intersection.exists_convexPoolsData
      (selector.chosen R.points R.eligible).identifiedCore a₀ c mu
        hc' hsum hcenter)
  obtain ⟨Dout, _hanchor⟩ := hpost D
  exact Dout.not_nonaveraging
    ((selector.chosen R.points R.eligible).identifiedCore_nonaveraging
      R.nonaveraging)

/-- The half-core terminal estimate and the source mass threshold force the
convex restriction supplied by Lemma 1 to contain at least two lattice
points. -/
theorem two_le_convexRestriction_of_halfCore
    {beta eta zeta : ℝ}
    {context : Reduction.HigherDimensionalContext beta eta}
    {selector : Reduction.BoundedCFPSelector context}
    (current : State zeta)
    {hA : selector.Eligible
      (Reduction.normalizeSet (toCFPBox current.box) current.points)}
    {epsilon delta gamma mu₀ convexScale : ℝ} {K : ℕ}
    {reductionConstant : ℝ}
    (R : Reduction.IrreducibleReplacementResult selector
      (toCFPBox current.box) current.points hA epsilon delta gamma K
        reductionConstant)
    (hmu₀ : 0 < mu₀)
    (hpopulation : 32 / mu₀ ≤ (R.points.card : ℝ))
    (hscaleLower : mu₀ ≤ convexScale)
    (hscaleOne : convexScale ≤ 1)
    {Omega : Set (ConvexDensity.EuclideanPoint
      (selector.chosen R.points R.eligible).dimension)}
    (hconvexPopulation :
      convexScale ^
            (convexDensityExponent current.dimension + zeta / 2) *
          ((selector.chosen R.points R.eligible).identifiedCore.card : ℝ) ≤
        ((latticeRestriction
          (selector.chosen R.points R.eligible).identifiedCore Omega).card :
            ℝ)) :
    2 ≤ (latticeRestriction
      (selector.chosen R.points R.eligible).identifiedCore Omega).card := by
  have hscale : 0 < convexScale := hmu₀.trans_le hscaleLower
  have hdensityNonneg :
      0 ≤ convexDensityExponent current.dimension + zeta / 2 := by
    have hconvex : 0 ≤ convexDensityExponent current.dimension := by
      unfold convexDensityExponent
      positivity
    linarith [current.zeta_pos]
  have hdensityOne :
      convexDensityExponent current.dimension + zeta / 2 ≤ 1 := by
    have hconvex :=
      convexDensityExponent_le_boxExponent current.dimension_pos
    have htotal := current.totalExponent_lt_one
    linarith [current.zeta_pos, current.excess_nonneg]
  have hscalePower : convexScale ≤
      convexScale ^
        (convexDensityExponent current.dimension + zeta / 2) := by
    calc
      convexScale = convexScale ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ convexScale ^
          (convexDensityExponent current.dimension + zeta / 2) :=
        Real.rpow_le_rpow_of_exponent_ge hscale hscaleOne hdensityOne
  have hmuPopulation : (32 : ℝ) ≤
      mu₀ * (R.points.card : ℝ) := by
    simpa only [mul_comm] using (div_le_iff₀ hmu₀).mp hpopulation
  have hmuCore : (16 : ℝ) ≤
      mu₀ *
        ((selector.chosen R.points R.eligible).identifiedCore.card : ℝ) := by
    have hhalf := mul_le_mul_of_nonneg_left R.core_half hmu₀.le
    nlinarith
  have hscaleCore : (16 : ℝ) ≤
      convexScale *
        ((selector.chosen R.points R.eligible).identifiedCore.card : ℝ) := by
    exact hmuCore.trans (mul_le_mul_of_nonneg_right hscaleLower
      (Nat.cast_nonneg _))
  have hone : (1 : ℝ) <
      convexScale ^
            (convexDensityExponent current.dimension + zeta / 2) *
          ((selector.chosen R.points R.eligible).identifiedCore.card : ℝ) := by
    have hpowCore := mul_le_mul_of_nonneg_right hscalePower
      (Nat.cast_nonneg
        (selector.chosen R.points R.eligible).identifiedCore.card)
    linarith [hscaleCore.trans hpowCore]
  exact two_le_latticeRestriction_of_one_lt_population hone
    hconvexPopulation

/-- The same half-core mass threshold supplies the normalization premise
`1 ≤ mu₀ * |B|` for the coefficient box used by convex density. -/
theorem one_le_mu_mul_gapCoefficientBox_card_of_halfCore
    {beta eta : ℝ}
    {context : Reduction.HigherDimensionalContext beta eta}
    {selector : Reduction.BoundedCFPSelector context}
    {ambient : ℕ} {A : Finset (LatticePoint ambient)}
    {hA : selector.Eligible A} {mu₀ : ℝ}
    (hmu₀ : 0 < mu₀)
    (hhalf : (1 / 2 : ℝ) * (A.card : ℝ) ≤
      ((selector.chosen A hA).identifiedCore.card : ℝ))
    (hpopulation : 32 / mu₀ ≤ (A.card : ℝ)) :
    1 ≤ mu₀ *
      ((gapCoefficientBox
        (selector.chosen A hA).progression).carrier.card : ℝ) := by
  have hmuPopulation : (32 : ℝ) ≤ mu₀ * (A.card : ℝ) :=
    by simpa only [mul_comm] using (div_le_iff₀ hmu₀).mp hpopulation
  have hmuCore : (16 : ℝ) ≤ mu₀ *
      ((selector.chosen A hA).identifiedCore.card : ℝ) := by
    have h := mul_le_mul_of_nonneg_left hhalf hmu₀.le
    nlinarith
  have hcoreBox :
      (selector.chosen A hA).identifiedCore.card ≤
        (gapCoefficientBox
          (selector.chosen A hA).progression).carrier.card :=
    Finset.card_le_card
      (selector.chosen A hA).identifiedCore_subset_coefficientBox
  have hcoreBoxReal :
      ((selector.chosen A hA).identifiedCore.card : ℝ) ≤
        ((gapCoefficientBox
          (selector.chosen A hA).progression).carrier.card : ℝ) := by
    exact_mod_cast hcoreBox
  have hmuBox := mul_le_mul_of_nonneg_left hcoreBoxReal hmu₀.le
  linarith [hmuCore.trans hmuBox]

/-- A small convex scale absorbs a fixed box constant when the target power
is strictly below one.  This is the scalar form of the strengthened
same-step field used by maximal same-dimensional run persistence. -/
theorem boxConstant_mul_scale_le_scale_rpow
    {boxConstant mu tau a convexScale : ℝ}
    (hboxConstant : 0 < boxConstant)
    (hmu : 0 < mu) (hmuOne : mu < 1)
    (htau : 0 < tau) (ha : 0 ≤ a) (haOne : a < 1)
    (hscale : 0 < convexScale)
    (hscaleUpper : convexScale ≤ mu ^ tau)
    (hbudget :
      Real.log boxConstant ≤
        tau * (1 - a) * (-Real.log mu)) :
    boxConstant * convexScale ≤ convexScale ^ a := by
  have hmuPower : 0 < mu ^ tau := Real.rpow_pos_of_pos hmu _
  have hlogScaleUpper :
      Real.log convexScale ≤ tau * Real.log mu := by
    calc
      Real.log convexScale ≤ Real.log (mu ^ tau) :=
        Real.log_le_log hscale hscaleUpper
      _ = tau * Real.log mu := by rw [Real.log_rpow hmu]
  have hlogBudget :
      Real.log boxConstant + Real.log convexScale ≤
        a * Real.log convexScale := by
    have honeMinus : 0 < 1 - a := sub_pos.mpr haOne
    have hscaled := mul_le_mul_of_nonneg_left hlogScaleUpper honeMinus.le
    nlinarith
  have hleft : 0 < boxConstant * convexScale :=
    mul_pos hboxConstant hscale
  have hright : 0 < convexScale ^ a := Real.rpow_pos_of_pos hscale _
  apply (Real.log_le_log_iff hleft hright).mp
  rw [Real.log_mul hboxConstant.ne' hscale.ne', Real.log_rpow hscale]
  exact hlogBudget

/-- The source run exponents satisfy all scalar inequalities needed to
absorb a fixed box constant.  In particular, their exponent gap is uniformly
at least `zeta / 4`, independently of the current dimension. -/
theorem sameRun_parameter_bounds
    {zeta : ℝ} (current : State zeta) :
    0 < sameRunLambda current.dimension zeta ∧
      sameRunLambda current.dimension zeta < 1 ∧
      0 ≤ sameRunA current.dimension zeta ∧
      sameRunA current.dimension zeta < 1 ∧
      zeta / 4 ≤
        1 - sameRunA current.dimension zeta := by
  have hconvexNonneg :
      0 ≤ convexDensityExponent current.dimension := by
    unfold convexDensityExponent
    positivity
  have hconvexBox :=
    convexDensityExponent_le_boxExponent current.dimension_pos
  have hlambda :
      0 < sameRunLambda current.dimension zeta := by
    dsimp [sameRunLambda]
    linarith [current.zeta_pos]
  have hlambdaOne :
      sameRunLambda current.dimension zeta < 1 := by
    dsimp [sameRunLambda]
    linarith [current.totalExponent_lt_one, current.zeta_pos,
      current.excess_nonneg]
  have hq : 0 < sameRunQ current.dimension zeta := by
    dsimp [sameRunQ]
    linarith [current.zeta_pos]
  have hqLambda :
      sameRunQ current.dimension zeta <
        sameRunLambda current.dimension zeta := by
    dsimp [sameRunQ, sameRunLambda]
    linarith [current.zeta_pos]
  have haNonneg :
      0 ≤ sameRunA current.dimension zeta := by
    exact div_nonneg hq.le hlambda.le
  have haOne :
      sameRunA current.dimension zeta < 1 := by
    dsimp [sameRunA]
    exact (div_lt_one hlambda).2 hqLambda
  have honeSub :
      1 - sameRunA current.dimension zeta =
        (zeta / 4) /
          sameRunLambda current.dimension zeta := by
    apply (eq_div_iff hlambda.ne').2
    rw [sub_mul, one_mul]
    dsimp only [sameRunA]
    rw [div_mul_cancel₀ _ hlambda.ne']
    dsimp [sameRunQ, sameRunLambda]
    ring
  have hgapNonneg : 0 ≤ zeta / 4 :=
    div_nonneg current.zeta_pos.le (by norm_num)
  have hgap :
      zeta / 4 ≤
        (zeta / 4) /
          sameRunLambda current.dimension zeta := by
    apply (le_div_iff₀ hlambda).2
    exact mul_le_of_le_one_right hgapNonneg hlambdaOne.le
  exact ⟨hlambda, hlambdaOne, haNonneg, haOne,
    by simpa only [honeSub] using hgap⟩

/-- The paper's frozen same-rank constant budget implies the exact
per-step absorption field consumed by a maximal same-dimensional run. -/
theorem sameRun_boxConstant_mul_scale_le_scale_rpow
    {zeta boxConstant mu tau convexScale : ℝ}
    (current : State zeta)
    (hboxConstant : 0 < boxConstant)
    (hmu : 0 < mu) (hmuOne : mu < 1)
    (htau : 0 < tau)
    (hscale : 0 < convexScale)
    (hscaleUpper : convexScale ≤ mu ^ tau)
    (hbudget :
      16 * Real.log boxConstant ≤
        zeta * tau * (-Real.log mu)) :
    boxConstant * convexScale ≤
      convexScale ^
        sameRunA current.dimension zeta := by
  obtain ⟨_hlambda, _hlambdaOne, haNonneg, haOne, hgap⟩ :=
    sameRun_parameter_bounds current
  have hnegLog : 0 ≤ -Real.log mu := by
    have := Real.log_nonpos hmu.le hmuOne.le
    linarith
  have hcoefficient :
      zeta * tau / 16 ≤
        tau *
          (1 - sameRunA current.dimension zeta) := by
    have hscaled := mul_le_mul_of_nonneg_left hgap htau.le
    nlinarith [mul_pos current.zeta_pos htau]
  have hcoefficientScaled :=
    mul_le_mul_of_nonneg_right hcoefficient hnegLog
  have hlogBudget :
      Real.log boxConstant ≤
        tau *
            (1 - sameRunA current.dimension zeta) *
          (-Real.log mu) := by
    nlinarith
  exact boxConstant_mul_scale_le_scale_rpow hboxConstant hmu hmuOne htau
    haNonneg haOne hscale hscaleUpper hlogBudget

/-- A single fixed convex-density parameter can be chosen below a prescribed
applicability radius while also absorbing the uniform same-step box
constant.  This choice is made before the initial counterexample; only the
gain used to spend the resulting fixed logarithmic budget is chosen later. -/
theorem exists_fixedConvexParameter_sameRunBudget
    {zeta tauLower deltaZero boxConstant : ℝ}
    (hzeta : 0 < zeta) (htauLower : 0 < tauLower)
    (hdeltaZero : 0 < deltaZero) (hboxConstant : 1 ≤ boxConstant) :
    ∃ nu : ℝ, nu ∈ Set.Ioo 0 1 ∧ nu < deltaZero ∧
      16 * Real.log boxConstant ≤
        zeta * tauLower * (-Real.log nu) := by
  let denominator := zeta * tauLower
  have hdenominator : 0 < denominator := mul_pos hzeta htauLower
  let burden := max (16 * Real.log boxConstant / denominator) 1
  have hburden : 0 < burden :=
    zero_lt_one.trans_le (le_max_right _ _)
  let nu := min (deltaZero / 2) (Real.exp (-burden) / 2)
  have hnu : 0 < nu := by
    dsimp only [nu]
    exact lt_min (half_pos hdeltaZero) (half_pos (Real.exp_pos _))
  have hnuDelta : nu < deltaZero := by
    calc
      nu ≤ deltaZero / 2 := min_le_left _ _
      _ < deltaZero := by linarith
  have hnuOne : nu < 1 := by
    have hexpOne : Real.exp (-burden) < 1 := by
      rw [← Real.exp_zero]
      exact Real.exp_lt_exp.mpr (by linarith)
    calc
      nu ≤ Real.exp (-burden) / 2 := min_le_right _ _
      _ < 1 := by linarith
  have hnuExp : nu ≤ Real.exp (-burden) := by
    calc
      nu ≤ Real.exp (-burden) / 2 := min_le_right _ _
      _ ≤ Real.exp (-burden) := by
        linarith [Real.exp_pos (-burden)]
  have hlogNu : Real.log nu ≤ -burden := by
    calc
      Real.log nu ≤ Real.log (Real.exp (-burden)) :=
        Real.log_le_log hnu hnuExp
      _ = -burden := Real.log_exp _
  have hratio : 16 * Real.log boxConstant / denominator ≤ burden :=
    le_max_left _ _
  have hlogBox : 0 ≤ Real.log boxConstant :=
    Real.log_nonneg hboxConstant
  have hbudgetRatio : 16 * Real.log boxConstant ≤ denominator * burden := by
    have := (div_le_iff₀ hdenominator).mp hratio
    simpa only [mul_comm] using this
  refine ⟨nu, ⟨hnu, hnuOne⟩, hnuDelta, ?_⟩
  have hnegLog : burden ≤ -Real.log nu := by linarith
  exact hbudgetRatio.trans
    (mul_le_mul_of_nonneg_left hnegLog hdenominator.le)

/-- Replacement transports a frozen initial-population power floor to the
terminal population, at the expected extra factor `1 - epsilon`. -/
theorem Reduction.IrreducibleReplacementResult.terminal_powerFloor
    {beta eta zeta : ℝ}
    {context : Reduction.HigherDimensionalContext beta eta}
    {selector : Reduction.BoundedCFPSelector context}
    (current : State zeta)
    {hA : selector.Eligible
      (Reduction.normalizeSet (toCFPBox current.box) current.points)}
    {epsilon delta gamma constant p : ℝ} {K initialCard : ℕ}
    (R : Reduction.IrreducibleReplacementResult selector
      (toCFPBox current.box) current.points hA epsilon delta gamma K constant)
    (hlower : (initialCard : ℝ) ^ p ≤ (current.points.card : ℝ))
    (hp : 0 ≤ p) (hepsilon : epsilon ≤ 1) :
    (initialCard : ℝ) ^ (p * (1 - epsilon)) ≤
      (R.points.card : ℝ) := by
  have hinitialNonneg : (0 : ℝ) ≤ (initialCard : ℝ) := by positivity
  have hcurrentNonneg : (0 : ℝ) ≤ (current.points.card : ℝ) := by positivity
  have honeMinus : 0 ≤ 1 - epsilon := sub_nonneg.mpr hepsilon
  calc
    (initialCard : ℝ) ^ (p * (1 - epsilon)) =
        ((initialCard : ℝ) ^ p) ^ (1 - epsilon) := by
      rw [Real.rpow_mul hinitialNonneg]
    _ ≤ (current.points.card : ℝ) ^ (1 - epsilon) :=
      Real.rpow_le_rpow (Real.rpow_nonneg hinitialNonneg _) hlower honeMinus
    _ ≤ (R.points.card : ℝ) := R.population_large.le

/-- Coordinate reachability also transports the frozen upper population
bound to the terminal replacement set. -/
theorem Reduction.IrreducibleReplacementResult.terminal_card_le_initial
    {beta eta zeta : ℝ}
    {context : Reduction.HigherDimensionalContext beta eta}
    {selector : Reduction.BoundedCFPSelector context}
    (current : State zeta)
    {hA : selector.Eligible
      (Reduction.normalizeSet (toCFPBox current.box) current.points)}
    {epsilon delta gamma constant : ℝ} {K initialCard : ℕ}
    (R : Reduction.IrreducibleReplacementResult selector
      (toCFPBox current.box) current.points hA epsilon delta gamma K constant)
    (hupper : current.points.card ≤ initialCard) :
    R.points.card ≤ initialCard := by
  have hterminal : R.points.card ≤ current.points.card := by
    have hreachable := Reduction.card_le_of_coordinateReachable R.reachable
    simpa only [Reduction.card_normalizeSet] using hreachable
  exact hterminal.trans hupper

/-- After the initial population is known, choose the same-dimensional gain
small enough for the fixed convex-scale budget and then choose a finite
contradiction horizon. -/
theorem exists_frozenSameGain_steps
    {zeta changeGain tau nu : ℝ} (initial : State zeta)
    (hchangeGain : 0 < changeGain) (htau : 0 < tau)
    (hnu : nu ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ sameGain : ℝ, ∃ steps : ℕ,
      0 < sameGain ∧
      sameGain ≤ min 1
        (zeta * tau / 16 * (-Real.log nu) /
          Real.log (initial.points.card : ℝ)) ∧
      1 < initial.excess + (steps : ℝ) *
        DensityIteration.Iteration.uniformGain changeGain sameGain := by
  have htwo : 2 ≤ initial.points.card := State.two_le_points_card initial
  have hcardOne : (1 : ℝ) < (initial.points.card : ℝ) := by
    exact_mod_cast htwo
  have hlogCard : 0 < Real.log (initial.points.card : ℝ) :=
    Real.log_pos hcardOne
  have hnegLog : 0 < -Real.log nu := by
    have := Real.log_neg hnu.1 hnu.2
    linarith
  let cap : ℝ := min 1
    (zeta * tau / 16 * (-Real.log nu) /
      Real.log (initial.points.card : ℝ))
  have hcap : 0 < cap := by
    dsimp only [cap]
    exact lt_min zero_lt_one (by
      exact div_pos (mul_pos (div_pos (mul_pos initial.zeta_pos htau)
        (by norm_num)) hnegLog) hlogCard)
  let sameGain := cap / 2
  have hsameGain : 0 < sameGain := half_pos hcap
  have hsameGainCap : sameGain ≤ cap := by
    dsimp only [sameGain]
    linarith
  obtain ⟨steps, hsteps⟩ :=
    Partial.exists_steps_exponent_budget initial hchangeGain hsameGain
  exact ⟨sameGain, steps, hsameGain, by simpa only [cap] using hsameGainCap,
    hsteps⟩

theorem exists_mu_le_fixed_threshold
    {kappa nu : ℝ} (hkappa : 0 < kappa) (hnu : 0 < nu) :
    ∃ threshold : ℕ, 2 ≤ threshold ∧
      ∀ {N : ℕ}, threshold ≤ N → Erdos186.mu kappa N ≤ nu := by
  have heventually : ∀ᶠ N : ℕ in atTop, Erdos186.mu kappa N < nu :=
    (Erdos186.tendsto_mu_zero hkappa).eventually_lt_const hnu
  obtain ⟨growthThreshold, hgrowth⟩ := eventually_atTop.1 heventually
  let threshold := max 2 growthThreshold
  refine ⟨threshold, le_max_left _ _, ?_⟩
  intro N hN
  exact (hgrowth N ((le_max_right 2 growthThreshold).trans hN)).le

theorem core_card_large_of_half
    {population core threshold : ℕ}
    (hlarge : 2 * threshold ≤ population)
    (hhalf : (1 / 2 : ℝ) * (population : ℝ) ≤ (core : ℝ)) :
    threshold ≤ core := by
  have hcast : (threshold : ℝ) ≤ (core : ℝ) := by
    have hlargeCast : (2 : ℝ) * (threshold : ℝ) ≤ (population : ℝ) := by
      exact_mod_cast hlarge
    nlinarith
  exact_mod_cast hcast

/-- Join all three genuine terminal branches into the controlled one-step
output.  No branch is represented by an assumed `StepOutput`: the rank-change
constructor, John rank-drop constructor, and same-rank constructor are each
called directly. -/
theorem exists_branchControlledStepOutput_of_terminalBranches
    {beta eta zeta changeGain sameGain rho : ℝ}
    {context : Reduction.HigherDimensionalContext beta eta}
    {selector : Reduction.BoundedCFPSelector context}
    (current : State zeta)
    {hA : selector.Eligible
      (Reduction.normalizeSet (toCFPBox current.box) current.points)}
    {epsilon delta gamma : ℝ} {K : ℕ}
    {reductionConstant slack : ℝ}
    (R : Reduction.IrreducibleReplacementResult selector
      (toCFPBox current.box) current.points hA epsilon delta gamma K
        reductionConstant)
    (hreductionConstantPos : 0 < reductionConstant)
    (hreductionConstantOne : 1 ≤ reductionConstant)
    (hchangeGain : 0 < changeGain) (hsameGain : 0 < sameGain)
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (hrankPower : (current.points.card : ℝ) ^ (1 - rho) ≤
      delta * (R.points.card : ℝ))
    (hcoreRetention : delta * (R.points.card : ℝ) ≤
      ((((selector.chosen R.points R.eligible).identifiedCore.card - 2) /
        2 : ℕ) : ℝ))
    (hhighExponent : current.dimension <
        (selector.chosen R.points R.eligible).dimension →
      (boxExponent (selector.chosen R.points R.eligible).dimension +
          zeta + (current.excess + changeGain)) *
            ((boxExponent current.dimension + zeta + current.excess)⁻¹ -
              (1 - epsilon) *
                (((selector.chosen R.points R.eligible).dimension : ℝ) -
                  (current.dimension : ℝ))) +
          slack ≤ 1 - epsilon)
    (hlowExponent : (selector.chosen R.points R.eligible).dimension <
        current.dimension →
      (boxExponent (selector.chosen R.points R.eligible).dimension +
          zeta + (current.excess + changeGain)) *
            (boxExponent current.dimension + zeta + current.excess)⁻¹ +
          slack ≤ 1 - epsilon)
    (habsorb :
      (boxExponent (selector.chosen R.points R.eligible).dimension +
          zeta + (current.excess + changeGain)) *
            Real.log reductionConstant - Real.log delta ≤
        slack * Real.log (current.points.card : ℝ))
    (hequalReady : EqualRankJohnBranchReady
      (changeGain := changeGain) (sameGain := sameGain) (rho := rho)
      current R) :
    Nonempty (BranchControlledStepOutput (K := K)
      (changeGain := changeGain) (sameGain := sameGain) (rhoChange := rho)
      current) := by
  by_cases hselectedRank :
      (selector.chosen R.points R.eligible).dimension = current.dimension
  · obtain ⟨convexScale, johnConstant, hconvexScale, hconvexScaleOne,
      hjohnConstant, Omega, J, htwo, hconvexPopulation, hJohnAlternative,
      hsameBox, hpowerBudget, hdropDensity, hsameBudget⟩ := hequalReady
    rcases hJohnAlternative with hJohnDrop | hJohnFull
    · exact exists_johnRankDropStepOutput_of_replacementJohn current R
        hselectedRank R.core_half (by norm_num) (by norm_num)
        hconvexScale hconvexScaleOne J hJohnDrop htwo hconvexPopulation
        (hpowerBudget hJohnDrop) hchangeGain (hdropDensity hJohnDrop)
    · have hJohnRank : J.rank = current.dimension :=
        hJohnFull.1.trans hselectedRank
      exact exists_sameRankStepOutput_of_replacementJohn_halfCore_logBudget
        current R hselectedRank hconvexScale hconvexScaleOne hjohnConstant
        hreductionConstantOne hsameBox J hJohnRank hconvexPopulation
        hJohnFull.2 hsameGain (hsameBudget hJohnFull.1)
  · exact exists_rankChangeStepOutput current R hreductionConstantPos
      hchangeGain hdelta hdeltaOne hrankPower hcoreRetention hselectedRank
      hhighExponent hlowExponent habsorb

/-! ## Uniform construction once the equal-rank analytic branch is ready -/

/-- All quantitative bookkeeping for the unequal-selected-rank branches is
uniform above one current-population threshold.  The only remaining input is
the genuinely geometric equal-rank package.  Thus this theorem already
returns an actual power-controlled step, rather than merely collecting the
rank-change inequalities as hypotheses. -/
theorem exists_slowlyVarying_branchControlledStepOutput_threshold
    {zeta epsilon changeGain sameGain rho slack kappa
      reductionConstant : ℝ}
    (dimensionCeiling : ℕ)
    (hepsilon : 0 < epsilon) (hepsilonOne : epsilon < 1)
    (hepsilonRho : epsilon < rho)
    (hepsilonSmall :
      epsilon ≤ zeta / (4 * (dimensionCeiling : ℝ)))
    (hchangeGain : 0 < changeGain) (hsameGain : 0 < sameGain)
    (hslack : 0 < slack)
    (hbudget : 4 * changeGain + slack + epsilon ≤ zeta / 2)
    (hgap : ∀ {lower upper : ℕ}, 0 < lower → lower < upper →
      upper ≤ dimensionCeiling →
      changeGain + epsilon + slack ≤
        boxExponent upper - boxExponent lower)
    (hreductionConstantPos : 0 < reductionConstant)
    (hreductionConstantOne : 1 ≤ reductionConstant) :
    ∃ pointThreshold : ℕ, 2 ≤ pointThreshold ∧
      ∀ {beta eta : ℝ}
        {context : Reduction.HigherDimensionalContext beta eta}
        {selector : Reduction.BoundedCFPSelector context}
        (current : State zeta)
        {hA : selector.Eligible
          (Reduction.normalizeSet (toCFPBox current.box) current.points)}
        {gamma : ℝ} {K : ℕ}
        (R : Reduction.IrreducibleReplacementResult selector
          (toCFPBox current.box) current.points hA epsilon
            (Erdos186.delta kappa current.points.card) gamma K
            reductionConstant),
        pointThreshold ≤ current.points.card →
        current.dimension ≤ dimensionCeiling →
        (selector.chosen R.points R.eligible).dimension ≤
          dimensionCeiling →
        0 < Erdos186.delta kappa current.points.card →
        Erdos186.delta kappa current.points.card ≤ 1 / 8 →
        EqualRankJohnBranchReady
          (changeGain := changeGain) (sameGain := sameGain) (rho := rho)
          current R →
        Nonempty (BranchControlledStepOutput (K := K)
          (changeGain := changeGain) (sameGain := sameGain)
          (rhoChange := rho)
          current) := by
  obtain ⟨powerThreshold, hpowerThresholdTwo, hpower⟩ :=
    exists_slowlyVarying_rankChangePower_threshold
      (kappa := kappa) hepsilonRho
  obtain ⟨coreThreshold, hcoreThresholdTwo, hterminalSixteen⟩ :=
    exists_replacement_terminalPopulation_threshold
      (epsilon := epsilon) hepsilonOne 16
  obtain ⟨absorptionThreshold, habsorptionThresholdTwo, habsorb⟩ :=
    exists_slowlyVarying_rankChangeAbsorption_threshold
      (zeta := zeta) (changeGain := changeGain)
      (constant := reductionConstant) (slack := slack) (kappa := kappa)
      hchangeGain hslack
  let pointThreshold :=
    max powerThreshold (max coreThreshold absorptionThreshold)
  refine ⟨pointThreshold,
    hpowerThresholdTwo.trans (le_max_left _ _), ?_⟩
  intro beta eta context selector current hA gamma K R hlarge
    hcurrentDimension hselectedDimension hdelta hdeltaEighth hequalReady
  have hlargePower : powerThreshold ≤ current.points.card :=
    (le_max_left powerThreshold (max coreThreshold absorptionThreshold)).trans
      hlarge
  have hlargeCore : coreThreshold ≤ current.points.card :=
    (le_max_left coreThreshold absorptionThreshold).trans
      ((le_max_right powerThreshold
        (max coreThreshold absorptionThreshold)).trans hlarge)
  have hlargeAbsorption : absorptionThreshold ≤ current.points.card :=
    (le_max_right coreThreshold absorptionThreshold).trans
      ((le_max_right powerThreshold
        (max coreThreshold absorptionThreshold)).trans hlarge)
  have hterminalCard : 16 ≤ R.points.card :=
    hterminalSixteen current R hlargeCore
  have hcoreRetention :
      Erdos186.delta kappa current.points.card * (R.points.card : ℝ) ≤
        ((((selector.chosen R.points R.eligible).identifiedCore.card - 2) /
          2 : ℕ) : ℝ) :=
    Reduction.density_mul_card_le_half_core_sub_two hdeltaEighth
      hterminalCard R.core_half
  have hselectedPositive :
      0 < (selector.chosen R.points R.eligible).dimension :=
    Intersection.selectedDimension_pos_of_coreRetention selector hdelta
      hcoreRetention
  have hrankPower :
      (current.points.card : ℝ) ^ (1 - rho) ≤
        Erdos186.delta kappa current.points.card * (R.points.card : ℝ) :=
    hpower hlargePower R.population_large
  have hhighExponent : current.dimension <
        (selector.chosen R.points R.eligible).dimension →
      (boxExponent (selector.chosen R.points R.eligible).dimension +
          zeta + (current.excess + changeGain)) *
            ((boxExponent current.dimension + zeta + current.excess)⁻¹ -
              (1 - epsilon) *
                (((selector.chosen R.points R.eligible).dimension : ℝ) -
                  (current.dimension : ℝ))) +
          slack ≤ 1 - epsilon := by
    intro hrank
    exact highRank_exponent_of_uniform_budget current hrank
      hselectedDimension hepsilon.le hepsilonOne.le hepsilonSmall
      hchangeGain.le hbudget
  have hlowExponent :
      (selector.chosen R.points R.eligible).dimension < current.dimension →
      (boxExponent (selector.chosen R.points R.eligible).dimension +
          zeta + (current.excess + changeGain)) *
            (boxExponent current.dimension + zeta + current.excess)⁻¹ +
          slack ≤ 1 - epsilon := by
    intro hrank
    exact lowRank_exponent_of_gap_budget current
      (add_nonneg hepsilon.le hslack.le)
      (hgap hselectedPositive hrank hcurrentDimension)
  exact exists_branchControlledStepOutput_of_terminalBranches current R
    hreductionConstantPos hreductionConstantOne hchangeGain hsameGain hdelta
    (hdeltaEighth.trans (by norm_num)) hrankPower hcoreRetention
    hhighExponent hlowExponent
    (habsorb current (selector.chosen R.points R.eligible).dimension
      hselectedPositive hlargeAbsorption)
    hequalReady

/-- Frozen-source counterpart of the preceding branch join.  All natural
stopping thresholds are fixed before the initial counterexample, while the
two slowly varying logarithmic losses are paid from the exact real floor
`initialCard^p ≤ |current|`. -/
theorem exists_frozen_branchControlledStepOutput_threshold
    {zeta epsilon changeGain rho slack kappa
      reductionConstant p : ℝ}
    (dimensionCeiling : ℕ)
    (hepsilon : 0 < epsilon) (hepsilonOne : epsilon < 1)
    (hepsilonRho : epsilon < rho)
    (hepsilonSmall :
      epsilon ≤ zeta / (4 * (dimensionCeiling : ℝ)))
    (hchangeGain : 0 < changeGain)
    (hslack : 0 < slack)
    (hbudget : 4 * changeGain + slack + epsilon ≤ zeta / 2)
    (hgap : ∀ {lower upper : ℕ}, 0 < lower → lower < upper →
      upper ≤ dimensionCeiling →
      changeGain + epsilon + slack ≤
        boxExponent upper - boxExponent lower)
    (hreductionConstantPos : 0 < reductionConstant)
    (hreductionConstantOne : 1 ≤ reductionConstant)
    (hp : 0 < p) :
    ∃ initialThreshold pointThreshold : ℕ,
      2 ≤ initialThreshold ∧ 2 ≤ pointThreshold ∧
      ∀ {initialCard : ℕ} {beta eta : ℝ}
        {context : Reduction.HigherDimensionalContext beta eta}
        {selector : Reduction.BoundedCFPSelector context}
        (current : State zeta)
        {hA : selector.Eligible
          (Reduction.normalizeSet (toCFPBox current.box) current.points)}
        {gamma sameGain : ℝ} {K : ℕ}
        (R : Reduction.IrreducibleReplacementResult selector
          (toCFPBox current.box) current.points hA epsilon
            (Erdos186.delta kappa initialCard) gamma K
            reductionConstant),
        initialThreshold ≤ initialCard →
        (initialCard : ℝ) ^ p ≤ (current.points.card : ℝ) →
        pointThreshold ≤ current.points.card →
        current.dimension ≤ dimensionCeiling →
        (selector.chosen R.points R.eligible).dimension ≤
          dimensionCeiling →
        0 < Erdos186.delta kappa initialCard →
        Erdos186.delta kappa initialCard ≤ 1 / 8 →
        0 < sameGain →
        ((selector.chosen R.points R.eligible).dimension = current.dimension →
          EqualRankJohnBranchReady
            (changeGain := changeGain) (sameGain := sameGain) (rho := rho)
            current R) →
        Nonempty (BranchControlledStepOutput (K := K)
          (changeGain := changeGain) (sameGain := sameGain)
          (rhoChange := rho) current) := by
  obtain ⟨powerThreshold, hpowerThresholdTwo, hpowerBudget⟩ :=
    exists_frozen_delta_logBudget_threshold kappa hp
      (sub_pos.mpr hepsilonRho) 0
  obtain ⟨absorptionThreshold, habsorptionThresholdTwo, habsorb⟩ :=
    exists_frozen_rankChangeAbsorption_threshold
      (zeta := zeta) (changeGain := changeGain)
      (constant := reductionConstant) (slack := slack) (kappa := kappa)
      (p := p) hchangeGain hslack hp
  obtain ⟨pointThreshold, hpointThresholdTwo, hterminalSixteen⟩ :=
    exists_replacement_terminalPopulation_threshold
      (epsilon := epsilon) hepsilonOne 16
  let initialThreshold := max powerThreshold absorptionThreshold
  refine ⟨initialThreshold, pointThreshold,
    hpowerThresholdTwo.trans (le_max_left _ _), hpointThresholdTwo, ?_⟩
  intro initialCard beta eta context selector current hA gamma sameGain K R hinitial
    hlower hpoint hcurrentDimension hselectedDimension hdelta hdeltaEighth
    hsameGain hequalReady
  have hlargePower : powerThreshold ≤ initialCard :=
    (le_max_left powerThreshold absorptionThreshold).trans hinitial
  have hlargeAbsorption : absorptionThreshold ≤ initialCard :=
    (le_max_right powerThreshold absorptionThreshold).trans hinitial
  have hterminalCard : 16 ≤ R.points.card :=
    hterminalSixteen current R hpoint
  have hcoreRetention :
      Erdos186.delta kappa initialCard * (R.points.card : ℝ) ≤
        ((((selector.chosen R.points R.eligible).identifiedCore.card - 2) /
          2 : ℕ) : ℝ) :=
    Reduction.density_mul_card_le_half_core_sub_two hdeltaEighth
      hterminalCard R.core_half
  have hselectedPositive :
      0 < (selector.chosen R.points R.eligible).dimension :=
    Intersection.selectedDimension_pos_of_coreRetention selector hdelta
      hcoreRetention
  have hrankPower :
      (current.points.card : ℝ) ^ (1 - rho) ≤
        Erdos186.delta kappa initialCard * (R.points.card : ℝ) := by
    apply rankChange_powerRetention_of_logBudget current R hdelta
    have h := hpowerBudget hlargePower hlower
    simpa only [zero_sub] using h
  have hhighExponent : current.dimension <
        (selector.chosen R.points R.eligible).dimension →
      (boxExponent (selector.chosen R.points R.eligible).dimension +
          zeta + (current.excess + changeGain)) *
            ((boxExponent current.dimension + zeta + current.excess)⁻¹ -
              (1 - epsilon) *
                (((selector.chosen R.points R.eligible).dimension : ℝ) -
                  (current.dimension : ℝ))) +
          slack ≤ 1 - epsilon := by
    intro hrank
    exact highRank_exponent_of_uniform_budget current hrank
      hselectedDimension hepsilon.le hepsilonOne.le hepsilonSmall
      hchangeGain.le hbudget
  have hlowExponent :
      (selector.chosen R.points R.eligible).dimension < current.dimension →
      (boxExponent (selector.chosen R.points R.eligible).dimension +
          zeta + (current.excess + changeGain)) *
            (boxExponent current.dimension + zeta + current.excess)⁻¹ +
          slack ≤ 1 - epsilon := by
    intro hrank
    exact lowRank_exponent_of_gap_budget current
      (add_nonneg hepsilon.le hslack.le)
      (hgap hselectedPositive hrank hcurrentDimension)
  by_cases hselectedRank :
      (selector.chosen R.points R.eligible).dimension = current.dimension
  · exact exists_branchControlledStepOutput_of_terminalBranches current R
      hreductionConstantPos hreductionConstantOne hchangeGain hsameGain hdelta
      (hdeltaEighth.trans (by norm_num)) hrankPower hcoreRetention
      hhighExponent hlowExponent
      (habsorb current (selector.chosen R.points R.eligible).dimension
        hlargeAbsorption hlower hselectedPositive)
      (hequalReady hselectedRank)
  · exact exists_rankChangeStepOutput current R hreductionConstantPos
      hchangeGain hdelta (hdeltaEighth.trans (by norm_num)) hrankPower
      hcoreRetention hselectedRank hhighExponent hlowExponent
      (habsorb current (selector.chosen R.points R.eligible).dimension
        hlargeAbsorption hlower hselectedPositive)


/-! ## Closing the package bookkeeping from a uniform controlled constructor -/

/-- Once the analytic argument supplies one controlled constructor after the
actual counterexample has been fixed, the remaining fields assemble into a
package.  This is the source-faithful quantifier order: the global dimension
ceiling depends only on `zeta`, while the gains, horizon, power loss, and
private population threshold may depend on the frozen initial population. -/
theorem oneStepPackageStatement_of_frozenControlledConstructors
    (hconstruct :
      ∀ d : ℕ, ∀ hd : 0 < d, ∀ zeta : ℝ, ∀ hzeta : 0 < zeta,
        ∀ dimensionCeiling : ℕ,
          0 < dimensionCeiling →
          (∀ current : State zeta,
            current.dimension ≤ dimensionCeiling) →
        ∃ boxThreshold : ℕ, 2 ≤ boxThreshold ∧
          ∀ (B : IntegerBox d) (A : Finset (BoxPoint d))
            (hAB : A ⊆ B.carrier) (hNA : IsBoxNonaveraging A),
            boxThreshold ≤ B.carrier.card →
            ∀ (hBtwo : 2 ≤ B.carrier.card)
              (hcritical :
                (B.carrier.card : ℝ) ^ (boxExponent d + zeta) <
                  (A.card : ℝ)),
            let initial := @Partial.initialState d zeta hd hzeta B A hAB hNA
              hBtwo hcritical
            ∃ pointThreshold steps changeSteps K : ℕ,
              ∃ changeGain sameGain rhoChange : ℝ,
                0 < changeGain ∧ 0 < sameGain ∧
                0 ≤ rhoChange ∧ rhoChange ≤ 1 ∧
                1 ≤ (K : ℝ) * (3 * zeta / 4) ∧
                1 ≤ (changeSteps : ℝ) * changeGain ∧
                1 < initial.excess + (steps : ℝ) *
                  DensityIteration.Iteration.uniformGain changeGain sameGain ∧
                (pointThreshold : ℝ) ≤
                  (initial.points.card : ℝ) ^
                    TracePersistence.persistenceExponent zeta rhoChange
                      changeSteps ∧
                BranchOneStepConstructor dimensionCeiling pointThreshold
                  initial.points.card K zeta changeGain sameGain rhoChange
                    ((initial.points.card : ℝ) ^
                      TracePersistence.persistenceExponent zeta rhoChange
                        changeSteps)) :
    OneStepPackageStatement := by
  intro d hd zeta hzeta
  obtain ⟨rawDimensionCeiling, hrawDimension⟩ :=
    State.exists_uniform_dimensionCeiling hzeta
  let dimensionCeiling := max 1 rawDimensionCeiling
  have hdimensionCeiling : 0 < dimensionCeiling := by
    dsimp only [dimensionCeiling]
    omega
  have hdimension : ∀ current : State zeta,
      current.dimension ≤ dimensionCeiling := by
    intro current
    exact (hrawDimension current).trans (le_max_right 1 rawDimensionCeiling)
  obtain ⟨boxThreshold, hboxThresholdTwo, hfreeze⟩ :=
    hconstruct d hd zeta hzeta dimensionCeiling hdimensionCeiling hdimension
  refine ⟨boxThreshold, hboxThresholdTwo, ?_⟩
  intro B A hAB hNA hlarge hBtwo hcritical
  let initial := @Partial.initialState d zeta hd hzeta B A hAB hNA
    hBtwo hcritical
  obtain ⟨pointThreshold, steps, changeSteps, K, changeGain, sameGain,
      rhoChange, hchangeGain, hsameGain, hrho, hrhoOne, hK,
      hchangeBudget, hexponentBudget, hinitialBudget, honeStep⟩ :=
    hfreeze B A hAB hNA hlarge hBtwo hcritical
  refine ⟨{
    dimensionCeiling := dimensionCeiling
    pointThreshold := pointThreshold
    steps := steps
    changeSteps := changeSteps
    K := K
    changeGain := changeGain
    sameGain := sameGain
    rhoChange := rhoChange
    changeGain_pos := hchangeGain
    sameGain_pos := hsameGain
    rhoChange_nonneg := hrho
    rhoChange_le_one := hrhoOne
    sameRun_K_budget := hK
    change_budget := hchangeBudget
    exponent_budget := ?_
    dimension_persists := ?_
    initial_population_budget := ?_
    oneStep := honeStep }⟩
  · exact hexponentBudget
  · intro length last _hlength _htrace
    exact hdimension last
  · exact hinitialBudget

/-! ## Unconditional source assembly -/

/-- The source-correct CFP corollary, the concrete quantitative replacement
construction, and the proved convex-density theorem assemble into the exact
one-step package consumed by the finite iteration.  The abstract replacement
argument is retained in the public boundary for compatibility, but the proof
uses its stronger concrete quantitative implementation in order to freeze
the slowly varying source parameters at the actual initial population. -/
theorem oneStepAssembly : OneStepAssemblyStatement := by
  intro hCFP _hReplacement hConvexDensity
  apply oneStepPackageStatement_of_frozenControlledConstructors
  intro d hd zeta hzeta dimensionCeiling hdimensionCeiling hdimension
  let context : Reduction.HigherDimensionalContext
      (2 * ((4 : ℝ) + 1)) (1 / 2 : ℝ) :=
    Classical.choice (Reduction.exists_higherDimensionalContext hCFP
      (β := 2 * ((4 : ℝ) + 1)) (η := (1 / 2 : ℝ))
      (by norm_num : (1 : ℝ) < 2 * (4 + 1))
      (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1))
  obtain ⟨tau, deltaZero, factorBound, johnConstant, hconvexData⟩ :=
    exists_boundedDimension_convexJohnRestrictionData hConvexDensity
      (convexLoss := zeta / 2) (half_pos hzeta) dimensionCeiling
      hdimensionCeiling
  obtain ⟨tauLower, htauLower, htauLowerLe⟩ :=
    exists_pos_lowerBound_fin hdimensionCeiling tau
      (fun i ↦ (hconvexData i).1)
  obtain ⟨deltaZeroLower, hdeltaZeroLower, hdeltaZeroLowerLe⟩ :=
    exists_pos_lowerBound_fin hdimensionCeiling deltaZero
      (fun i ↦ (hconvexData i).2.2.1)
  obtain ⟨johnUpperRaw, hjohnUpperRaw⟩ :=
    exists_upperBound_fin hdimensionCeiling johnConstant
  let johnUpper := max 1 johnUpperRaw
  have hjohnUpperOne : 1 ≤ johnUpper := le_max_left _ _
  have hjohnUpper : ∀ i, johnConstant i ≤ johnUpper := fun i ↦
    (hjohnUpperRaw i).trans (le_max_right 1 johnUpperRaw)
  let analyticCeiling := dimensionCeiling + 7
  have hanalyticCeiling : 0 < analyticCeiling := by
    dsimp only [analyticCeiling]
    omega
  obtain ⟨changeGain, slack, epsilonCap, hchangeGain, hslack,
      hepsilonCap, hepsilonHierarchy⟩ :=
    exists_rankChange_gainSlack_epsilonCap hzeta analyticCeiling
      hanalyticCeiling
  let epsilon := epsilonCap / 2
  let rhoChange := 2 * epsilon
  have hepsilon : 0 < epsilon := half_pos hepsilonCap
  have hepsilonLe : epsilon ≤ epsilonCap := by
    dsimp only [epsilon]
    linarith
  obtain ⟨hepsilonThird, hepsilonOne, hepsilonSmall, hchangeBudget,
      hdimensionGap⟩ := hepsilonHierarchy epsilon hepsilon hepsilonLe
  have hepsilonRho : epsilon < rhoChange := by
    dsimp only [rhoChange]
    linarith
  have hrhoNonneg : 0 ≤ rhoChange := by
    dsimp only [rhoChange]
    positivity
  have hrhoOne : rhoChange ≤ 1 := by
    dsimp only [rhoChange]
    linarith
  obtain ⟨changeSteps, hchangeSteps⟩ :=
    TracePersistence.exists_changeSteps_budget hchangeGain
  let persistence :=
    TracePersistence.persistenceExponent zeta rhoChange changeSteps
  have hpersistence : 0 < persistence := by
    exact TracePersistence.persistenceExponent_pos changeSteps hzeta
      (by dsimp only [rhoChange]; linarith)
  obtain ⟨K0, hK0, reductionConstant, hreductionConstant,
      hreduce⟩ :=
    exists_boundedDimension_quantitativeTerminal_frozenSlowlyVarying
      context dimensionCeiling hdimensionCeiling hepsilon hepsilonThird
      hpersistence
  have hreductionConstantPos : 0 < reductionConstant :=
    zero_lt_one.trans_le hreductionConstant
  obtain ⟨sameRunK, hsameRunK⟩ :=
    TracePersistence.exists_K_sameRun_budget hzeta
  let K := max (max K0 4) sameRunK
  have hK0K : K0 ≤ K :=
    (le_max_left K0 4).trans (le_max_left _ sameRunK)
  have hKFour : 4 ≤ K :=
    (le_max_right K0 4).trans (le_max_left _ sameRunK)
  have hKPosNat : 0 < K := by omega
  have hsameRunKFinal : 1 ≤ (K : ℝ) * (3 * zeta / 4) := by
    have hcast : (sameRunK : ℝ) ≤ (K : ℝ) := by
      exact_mod_cast (le_max_right (max K0 4) sameRunK)
    exact hsameRunK.trans
      (mul_le_mul_of_nonneg_right hcast (by positivity))
  let kappa : ℝ := 1 / 2
  have hkappa : 0 < kappa := by norm_num [kappa]
  have hkappaOne : kappa < 1 := by norm_num [kappa]
  let globalBoxConstant :=
    sameStepBoxConstant johnUpper reductionConstant (1 / 2) K
  have hglobalBoxConstant : 1 ≤ globalBoxConstant :=
    one_le_sameStepBoxConstant hjohnUpperOne hreductionConstant
      (by norm_num) (by norm_num)
  obtain ⟨nu, hnu, hnuDeltaZero, hsameRunBudget⟩ :=
    exists_fixedConvexParameter_sameRunBudget hzeta htauLower
      hdeltaZeroLower hglobalBoxConstant
  have hfixedConvexData : ∀ i : Fin dimensionCeiling,
      ∃ largeEnough : ℕ,
      ∀ (B : IntegerBox (i.1 + 1))
        (A : Finset (BoxPoint (i.1 + 1))),
        ConvexDensity.IsConvexBody (boxRealization B) →
        (Intersection.realImage A :
            Set (ConvexDensity.EuclideanPoint (i.1 + 1))) ⊆
          boxRealization B →
        A.Nonempty → largeEnough ≤ A.card →
        ConvexGeometry.IsDeltaConvexPosition nu
          (Intersection.realImage A) →
        1 ≤ nu * (B.carrier.card : ℝ) →
        ∃ eta : ℝ, eta ∈ Set.Icc nu (nu ^ tau i) ∧ eta ≤ 1 ∧
          ∃ Omega : Set (ConvexDensity.EuclideanPoint (i.1 + 1)),
            Convex ℝ Omega ∧ Omega ⊆ boxRealization B ∧
            ConvexDensity.relativeVolume Omega (boxRealization B) ≤
              ENNReal.ofReal eta ∧
            eta ^ (convexDensityExponent (i.1 + 1) + zeta / 2) *
                (A.card : ℝ) ≤
              ((latticeRestriction A Omega).card : ℝ) ∧
            ∃ J : CenteredDiscreteJohnCertificate B Omega,
              J.factor ≤ factorBound i ∧
              (J.certificate.outer.volume : ℝ) ≤
                johnConstant i * (B.carrier.card : ℝ) ∧
              (J.rank < i.1 + 1 ∨
                (J.rank = i.1 + 1 ∧
                  (J.certificate.outer.volume : ℝ) ≤
                    johnConstant i * eta * (B.carrier.card : ℝ))) := by
    intro i
    exact (hconvexData i).2.2.2.2 (delta := nu) hnu.1 hnu.2
      (hnuDeltaZero.trans_le (hdeltaZeroLowerLe i))
  choose convexThreshold hfixedConvex using hfixedConvexData
  obtain ⟨convexThresholdUpper, hconvexThresholdUpper⟩ :=
    exists_nat_upperBound_fin hdimensionCeiling convexThreshold
  let terminalPersistence := persistence * (1 - epsilon)
  have hterminalPersistence : 0 < terminalPersistence :=
    mul_pos hpersistence (sub_pos.mpr (hepsilonThird.trans (by norm_num)))
  obtain ⟨postThreshold, hpost⟩ :=
    Intersection.Theorem4PostCFPData.exists_powerRangeSource_boxWeightedFullCoefficientPostCFP_threshold
      (exponent := Reduction.guardedScaleExponent epsilon)
      context analyticCeiling (by norm_num : (0 : ℝ) < 1 / 2)
      terminalPersistence hterminalPersistence kappa (K : ℝ) hkappa
      hkappaOne (by exact_mod_cast hKPosNat)
  obtain ⟨reductionThreshold, hreductionThresholdTwo, hreduceFrozen⟩ :=
    hreduce kappa hkappa K hK0K
  obtain ⟨branchInitialThreshold, branchPointThreshold,
      hbranchInitialTwo, hbranchPointTwo, hbranch⟩ :=
    exists_frozen_branchControlledStepOutput_threshold analyticCeiling
      (kappa := kappa)
      hepsilon (hepsilonThird.trans (by norm_num)) hepsilonRho
      hepsilonSmall hchangeGain hslack hchangeBudget
      hdimensionGap hreductionConstantPos hreductionConstant hpersistence
  obtain ⟨selectedPointThreshold, hselectedPointTwo,
      hselectedDimension⟩ :=
    exists_replacement_selectedDimension_threshold hepsilonThird
      hreductionConstantPos
  obtain ⟨powerPointThreshold, hpowerPointTwo, hequalPower⟩ :=
    exists_equalRank_powerRetentionBudget_threshold_boundedDimension_scaleFloor
      dimensionCeiling hdimensionCeiling hzeta hnu.1 hepsilonRho
  obtain ⟨nuPopulationTarget, hnuPopulationTarget⟩ :=
    exists_nat_ge (32 / nu)
  let terminalTarget :=
    max 16 (max (2 * convexThresholdUpper) nuPopulationTarget)
  obtain ⟨terminalPointThreshold, hterminalPointTwo, hterminalLarge⟩ :=
    exists_replacement_terminalPopulation_threshold
      (hepsilonThird.trans (by norm_num)) terminalTarget
  let densityCeiling :=
    boxExponent dimensionCeiling + zeta / 2
  let rankSaving := epsilon + slack
  have hrankSaving : 0 < rankSaving := add_pos hepsilon hslack
  let rankDropCost :=
    Real.log (johnUpper * reductionConstant) +
      densityCeiling * (-Real.log nu) - Real.log (1 / 2)
  obtain ⟨rankDropPointThreshold, hrankDropPointTwo,
      hrankDropBudget⟩ :=
    exists_fixed_logBudget_threshold rankDropCost hrankSaving
  have hsourceEventually : ∀ᶠ N : ℕ in atTop,
      0 < Erdos186.delta kappa N ∧
        Erdos186.delta kappa N ≤ 1 / 8 := by
    filter_upwards [Erdos186.eventually_delta_mem_Ioo hkappa,
      (Erdos186.tendsto_delta_zero hkappa).eventually_lt_const
        (by norm_num : (0 : ℝ) < 1 / 8)] with N hdeltaN hsmall
    exact ⟨hdeltaN.1, hsmall.le⟩
  obtain ⟨sourceThreshold, hsourceThreshold⟩ :=
    eventually_atTop.1 hsourceEventually
  obtain ⟨muThreshold, hmuThresholdTwo, hmuLe⟩ :=
    exists_mu_le_fixed_threshold hkappa hnu.1
  let initialThreshold := max reductionThreshold
    (max postThreshold
      (max branchInitialThreshold (max sourceThreshold muThreshold)))
  have hinitialThresholdTwo : 2 ≤ initialThreshold :=
    hreductionThresholdTwo.trans (le_max_left _ _)
  let pointThreshold := max branchPointThreshold
    (max selectedPointThreshold
      (max powerPointThreshold
        (max terminalPointThreshold rankDropPointThreshold)))
  have hpointThresholdTwo : 2 ≤ pointThreshold :=
    hbranchPointTwo.trans (le_max_left _ _)
  have hcriticalExponent : 0 < boxExponent d + zeta := by
    linarith [boxExponent_pos hd]
  obtain ⟨initialBoxThreshold, hinitialBoxTwo, hinitialPopulation⟩ :=
    Partial.exists_box_threshold_for_supercritical_population
      initialThreshold hcriticalExponent
  obtain ⟨persistenceBoxThreshold, hpersistenceBoxTwo,
      hpersistenceBudget⟩ :=
    Partial.exists_box_threshold_persistence_budget pointThreshold
      hcriticalExponent hpersistence
  let boxThreshold := max initialBoxThreshold persistenceBoxThreshold
  refine ⟨boxThreshold,
    hinitialBoxTwo.trans (le_max_left _ _), ?_⟩
  intro B A hAB hNA hboxLarge hBtwo hcritical
  let initial := @Partial.initialState d zeta hd hzeta B A hAB hNA
    hBtwo hcritical
  have hlargeInitialBox : initialBoxThreshold ≤ B.carrier.card :=
    (le_max_left initialBoxThreshold persistenceBoxThreshold).trans hboxLarge
  have hlargePersistenceBox : persistenceBoxThreshold ≤ B.carrier.card :=
    (le_max_right initialBoxThreshold persistenceBoxThreshold).trans hboxLarge
  have hinitialLarge : initialThreshold ≤ initial.points.card := by
    simpa only [initial, Partial.initialState] using
      hinitialPopulation hlargeInitialBox hcritical
  have hinitialBudget : (pointThreshold : ℝ) ≤
      (initial.points.card : ℝ) ^ persistence := by
    simpa only [initial, Partial.initialState] using
      hpersistenceBudget hlargePersistenceBox hcritical
  obtain ⟨sameGain, steps, hsameGain, hsameGainUpper, hsteps⟩ :=
    exists_frozenSameGain_steps initial hchangeGain htauLower hnu
  refine ⟨pointThreshold, steps, changeSteps, K, changeGain, sameGain,
    rhoChange, hchangeGain, hsameGain, hrhoNonneg, hrhoOne,
    hsameRunKFinal, hchangeSteps, hsteps, hinitialBudget, ?_⟩
  intro current happlicable
  rcases happlicable with ⟨⟨hcurrentDimension, hcurrentPoint,
    hcurrentUpper⟩, hcurrentFloor⟩
  have hlargeReduction : reductionThreshold ≤ initial.points.card :=
    (le_max_left reductionThreshold _).trans hinitialLarge
  have hlargePost : postThreshold ≤ initial.points.card :=
    (le_max_left postThreshold
      (max branchInitialThreshold (max sourceThreshold muThreshold))).trans
      ((le_max_right reductionThreshold _).trans hinitialLarge)
  have hlargeBranch : branchInitialThreshold ≤ initial.points.card :=
    (le_max_left branchInitialThreshold (max sourceThreshold muThreshold)).trans
      ((le_max_right postThreshold _).trans
        ((le_max_right reductionThreshold _).trans hinitialLarge))
  have hlargeSource : sourceThreshold ≤ initial.points.card :=
    (le_max_left sourceThreshold muThreshold).trans
      ((le_max_right branchInitialThreshold _).trans
        ((le_max_right postThreshold _).trans
          ((le_max_right reductionThreshold _).trans hinitialLarge)))
  have hlargeMu : muThreshold ≤ initial.points.card :=
    (le_max_right sourceThreshold muThreshold).trans
      ((le_max_right branchInitialThreshold _).trans
        ((le_max_right postThreshold _).trans
          ((le_max_right reductionThreshold _).trans hinitialLarge)))
  obtain ⟨hdelta, hdeltaEighth⟩ :=
    hsourceThreshold initial.points.card hlargeSource
  have hmuLeNu : Erdos186.mu kappa initial.points.card ≤ nu :=
    hmuLe hlargeMu
  obtain ⟨hA, ⟨R⟩⟩ := hreduceFrozen current hcurrentDimension
    hcurrentFloor hcurrentUpper hlargeReduction
  have hlargeBranchPoint : branchPointThreshold ≤ current.points.card :=
    (le_max_left branchPointThreshold _).trans hcurrentPoint
  have hlargeSelectedPoint : selectedPointThreshold ≤ current.points.card :=
    (le_max_left selectedPointThreshold _).trans
      ((le_max_right branchPointThreshold _).trans hcurrentPoint)
  have hlargePowerPoint : powerPointThreshold ≤ current.points.card :=
    (le_max_left powerPointThreshold
      (max terminalPointThreshold rankDropPointThreshold)).trans
      ((le_max_right selectedPointThreshold _).trans
        ((le_max_right branchPointThreshold _).trans hcurrentPoint))
  have hlargeTerminalPoint : terminalPointThreshold ≤ current.points.card :=
    (le_max_left terminalPointThreshold rankDropPointThreshold).trans
      ((le_max_right powerPointThreshold _).trans
        ((le_max_right selectedPointThreshold _).trans
          ((le_max_right branchPointThreshold _).trans hcurrentPoint)))
  have hlargeRankDropPoint : rankDropPointThreshold ≤ current.points.card :=
    (le_max_right terminalPointThreshold rankDropPointThreshold).trans
      ((le_max_right powerPointThreshold _).trans
        ((le_max_right selectedPointThreshold _).trans
          ((le_max_right branchPointThreshold _).trans hcurrentPoint)))
  have hselectedDimensionBound :
      ((context.scaleSelector
          (Reduction.guardedScaleExponent epsilon)).chosen R.points
          R.eligible).dimension ≤ analyticCeiling := by
    have hjump := hselectedDimension current R hlargeSelectedPoint
    exact hjump.trans (by
      dsimp only [analyticCeiling]
      omega)
  apply hbranch (initialCard := initial.points.card) current R hlargeBranch
    hcurrentFloor hlargeBranchPoint
    (hcurrentDimension.trans (by
      dsimp only [analyticCeiling]
      omega)) hselectedDimensionBound hdelta hdeltaEighth hsameGain
  intro hselectedRank
  let S := (context.scaleSelector
    (Reduction.guardedScaleExponent epsilon)).chosen R.points R.eligible
  have hterminalTarget : terminalTarget ≤ R.points.card :=
    hterminalLarge current R hlargeTerminalPoint
  have hterminalSixteen : 16 ≤ R.points.card :=
    (le_max_left 16 _).trans hterminalTarget
  have hcoreRetention : Erdos186.delta kappa initial.points.card *
        (R.points.card : ℝ) ≤
      (((S.identifiedCore.card - 2) / 2 : ℕ) : ℝ) := by
    exact Reduction.density_mul_card_le_half_core_sub_two hdeltaEighth
      hterminalSixteen R.core_half
  have hterminalFloor : (initial.points.card : ℝ) ^ terminalPersistence ≤
      (R.points.card : ℝ) := by
    have hfloor :=
      Erdos186.PZ.OneStepAssembly.Reduction.IrreducibleReplacementResult.terminal_powerFloor
        current R hcurrentFloor hpersistence.le hepsilonOne
    simpa only [terminalPersistence] using hfloor
  have hterminalUpper : R.points.card ≤ initial.points.card :=
    Erdos186.PZ.OneStepAssembly.Reduction.IrreducibleReplacementResult.terminal_card_le_initial
      current R hcurrentUpper
  have hmuPos : 0 < Erdos186.mu kappa initial.points.card := by
    dsimp only [Erdos186.mu]
    exact Real.rpow_pos_of_pos hdelta _
  have hpostForR :
      ∀ {a₀ : Intersection.realImage S.identifiedCore}
        {c : Intersection.realImage S.identifiedCore → ℝ}
        (D : Intersection.ConvexPoolsData S.identifiedCore a₀ c
          (Erdos186.mu kappa initial.points.card)),
        ∃ Dout : Intersection.Theorem4PostCFPData S.identifiedCore,
          Dout.a = D.a := by
    intro a₀ c D
    exact hpost hlargePost R.points R.eligible hterminalFloor
      hterminalUpper hselectedDimensionBound hcoreRetention R.core_half D
      R.irreducible R.selector_candidate_closed
  have hpositionMu : ConvexGeometry.IsDeltaConvexPosition
      (Erdos186.mu kappa initial.points.card)
      (Intersection.realImage S.identifiedCore) := by
    exact
      Erdos186.PZ.OneStepAssembly.Reduction.IrreducibleReplacementResult.identifiedCore_isDeltaConvexPosition_of_convexPoolsPost
        R hmuPos hpostForR
  have hpositionNu : ConvexGeometry.IsDeltaConvexPosition nu
      (Intersection.realImage S.identifiedCore) :=
    hpositionMu.mono hmuLeNu
  let i : Fin dimensionCeiling :=
    ⟨current.dimension - 1, by omega⟩
  have hi : i.1 + 1 = current.dimension := by
    change current.dimension - 1 + 1 = current.dimension
    have hdimPos := current.dimension_pos
    omega
  have hterminalConvexTwice : 2 * convexThresholdUpper ≤ R.points.card :=
    (le_max_left (2 * convexThresholdUpper) nuPopulationTarget).trans
      ((le_max_right 16 _).trans hterminalTarget)
  have hcoreConvex : convexThreshold i ≤ S.identifiedCore.card := by
    apply (hconvexThresholdUpper i).trans
    exact core_card_large_of_half hterminalConvexTwice R.core_half
  have hcoreNonempty : S.identifiedCore.Nonempty := by
    have hcoreCard : 0 < S.identifiedCore.card := by
      have hhalf := R.core_half
      have hterminalPos : (0 : ℝ) < (R.points.card : ℝ) := by
        exact_mod_cast (show 0 < R.points.card by omega)
      have : (0 : ℝ) < (S.identifiedCore.card : ℝ) := by nlinarith
      exact_mod_cast this
    exact Finset.card_pos.mp hcoreCard
  have hpopulationNu : 32 / nu ≤ (R.points.card : ℝ) := by
    calc
      32 / nu ≤ (nuPopulationTarget : ℝ) := hnuPopulationTarget
      _ ≤ (terminalTarget : ℝ) := by
        exact_mod_cast ((le_max_right (2 * convexThresholdUpper)
          nuPopulationTarget).trans (le_max_right 16 _))
      _ ≤ (R.points.card : ℝ) := by exact_mod_cast hterminalTarget
  have hnuBox : 1 ≤ nu *
      ((gapCoefficientBox S.progression).carrier.card : ℝ) :=
    one_le_mu_mul_gapCoefficientBox_card_of_halfCore hnu.1 R.core_half
      hpopulationNu
  have hconvexAt := hfixedConvex i
  rw [hi, ← hselectedRank] at hconvexAt
  obtain ⟨convexScale, hconvexScaleRange, hconvexScaleOne, Omega,
      _hOmegaConvex, _hOmegaSubset, _hOmegaVolume, hconvexPopulation, J,
      _hfactor, hJohnOuter, hJohnAlternative⟩ :=
    hconvexAt (gapCoefficientBox S.progression) S.identifiedCore
      (isConvexBody_boxRealization_gapCoefficientBox S.progression
        (fun j ↦ (S.witness.three_le_width j).trans' (by omega)))
      (realImage_subset_boxRealization_of_subset
        S.identifiedCore_subset_coefficientBox)
      hcoreNonempty hcoreConvex hpositionNu hnuBox
  have hconvexScale : 0 < convexScale := hnu.1.trans_le
    hconvexScaleRange.1
  have htwoRestriction : 2 ≤
      (latticeRestriction S.identifiedCore Omega).card :=
    two_le_convexRestriction_of_halfCore current R hnu.1 hpopulationNu
      hconvexScaleRange.1 hconvexScaleOne (by
        simpa only [S, hselectedRank] using hconvexPopulation)
  let localBoxConstant :=
    sameStepBoxConstant (johnConstant i) reductionConstant (1 / 2) K
  have hlocalBoxOne : 1 ≤ localBoxConstant :=
    one_le_sameStepBoxConstant (hconvexData i).2.2.2.1
      hreductionConstant (by norm_num) (by norm_num)
  have hlocalBoxPos : 0 < localBoxConstant :=
    zero_lt_one.trans_le hlocalBoxOne
  have hlocalBoxLe : localBoxConstant ≤ globalBoxConstant := by
    dsimp only [localBoxConstant, globalBoxConstant, sameStepBoxConstant]
    gcongr
    exact hjohnUpper i
  have hnegLogNu : 0 ≤ -Real.log nu := by
    have := Real.log_nonpos hnu.1.le hnu.2.le
    linarith
  have hlocalBudget : 16 * Real.log localBoxConstant ≤
      zeta * tau i * (-Real.log nu) := by
    have hlogLe : Real.log localBoxConstant ≤
        Real.log globalBoxConstant :=
      Real.log_le_log hlocalBoxPos hlocalBoxLe
    have hleft : 16 * Real.log localBoxConstant ≤
        16 * Real.log globalBoxConstant :=
      mul_le_mul_of_nonneg_left hlogLe (by norm_num)
    have hright : zeta * tauLower * (-Real.log nu) ≤
        zeta * tau i * (-Real.log nu) := by
      have htau := mul_le_mul_of_nonneg_left (htauLowerLe i) hzeta.le
      exact mul_le_mul_of_nonneg_right htau hnegLogNu
    exact hleft.trans (hsameRunBudget.trans hright)
  refine ⟨convexScale, johnConstant i, hconvexScale, hconvexScaleOne,
    (hconvexData i).2.2.2.1, Omega, J, htwoRestriction,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [S, hselectedRank] using hconvexPopulation
  · simpa only [S, hi, gapCoefficientBox_card] using hJohnAlternative
  · exact sameRun_boxConstant_mul_scale_le_scale_rpow current
      hlocalBoxPos hnu.1 hnu.2 (hconvexData i).1 hconvexScale
      hconvexScaleRange.2 hlocalBudget
  · intro hJdrop
    exact hequalPower current R hcurrentDimension hlargePowerPoint
      hconvexScaleRange.1 hconvexScaleOne
  · intro hJdrop
    have hJrankPos : 0 < J.rank :=
      J.rank_pos_of_two_le_restriction_card
        S.identifiedCore_subset_coefficientBox htwoRestriction
    have hnewSaving :
        boxExponent J.rank + zeta + (current.excess + changeGain) ≤
          boxExponent current.dimension + zeta + current.excess -
            rankSaving := by
      have hJdropCurrent : J.rank < current.dimension :=
        hJdrop.trans_le hselectedRank.le
      have hcurrentAnalytic : current.dimension ≤ analyticCeiling :=
        hcurrentDimension.trans (by
          dsimp only [analyticCeiling]
          omega)
      have hgapJ :=
        hdimensionGap hJrankPos hJdropCurrent hcurrentAnalytic
      dsimp only [rankSaving]
      linarith
    have hdensityBound :
        convexDensityExponent current.dimension + zeta / 2 ≤
          densityCeiling := by
      have hconvexBox :=
        convexDensityExponent_le_boxExponent current.dimension_pos
      have hboxMono := boxExponent_mono current.dimension_pos
        hcurrentDimension
      dsimp only [densityCeiling]
      linarith
    have hdropConstantPos : 0 < johnConstant i * reductionConstant :=
      mul_pos (zero_lt_one.trans_le (hconvexData i).2.2.2.1)
        hreductionConstantPos
    have hdropConstantLe : johnConstant i * reductionConstant ≤
        johnUpper * reductionConstant :=
      mul_le_mul_of_nonneg_right (hjohnUpper i)
        hreductionConstantPos.le
    have hdropCost :
        Real.log (johnConstant i * reductionConstant) +
            densityCeiling * (-Real.log nu) - Real.log (1 / 2) ≤
          rankSaving * Real.log (current.points.card : ℝ) := by
      apply le_trans _ (hrankDropBudget hlargeRankDropPoint)
      dsimp only [rankDropCost]
      have hlog := Real.log_le_log hdropConstantPos hdropConstantLe
      linarith
    exact johnRankDrop_density_of_frozenBudget current R hselectedRank
      hrankSaving hKFour (hconvexData i).2.2.2.1 hreductionConstant
      hnu hconvexScale hconvexScaleRange.1 hconvexScaleOne hdensityBound
      J hJrankPos (by simpa only [S, hselectedRank] using hconvexPopulation)
      (by simpa only [S, gapCoefficientBox_card] using hJohnOuter)
      hchangeGain hnewSaving hdropCost
  · intro hJfull
    have hlogInitial : 0 < Real.log (initial.points.card : ℝ) :=
      Real.log_pos (by
        exact_mod_cast (State.two_le_points_card initial))
    have hgainCap : zeta * tauLower / 16 * (-Real.log nu) /
          Real.log (initial.points.card : ℝ) ≤
        zeta * tau i / 16 * (-Real.log nu) /
          Real.log (initial.points.card : ℝ) := by
      apply div_le_div_of_nonneg_right _ hlogInitial.le
      apply mul_le_mul_of_nonneg_right _ hnegLogNu
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (htauLowerLe i) hzeta.le)
        (by norm_num)
    have hsameGainUpperI : sameGain ≤ min 1
        (zeta * tau i / 16 * (-Real.log nu) /
          Real.log (initial.points.card : ℝ)) := by
      exact hsameGainUpper.trans (min_le_min_left 1 hgainCap)
    apply sameRank_halfCore_logBudget_of_frozenParameters
      (tau := tau i) (mu₀ := nu) (initialCard := initial.points.card)
      current R J
    · exact hJfull.trans hselectedRank
    · exact (hconvexData i).1
    · exact hKFour
    · exact (hconvexData i).2.2.2.1
    · exact hreductionConstant
    · exact hconvexScale
    · exact hconvexScaleRange.2
    · exact hnu
    · exact State.two_le_points_card initial
    · exact hcurrentUpper
    · exact hsameGain
    · exact hsameGainUpperI
    · exact hlocalBudget

end

end Erdos186.PZ.OneStepAssembly
