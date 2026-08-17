/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import ErdosProblems.Erdos636.AugmentationExposureCrowd

/-!
# Scalar bookkeeping for the crowded augmentation exposure

The graph-facing crowded exposure naturally produces a candidate family whose
cardinality depends on the particular outer sample.  The quantitative part of
the Kwan--Sudakov argument should not have to inspect that family.  This file
isolates the elementary monotonicity which replaces its cardinality by the
fixed bounds

`s0 - badBudget <= candidates.card <= s0`.

In particular, `CrowdLargeScalarBounds` has the same geometric fields as
`AugmentationExposureCrowd.CrowdLargeBounds`, but its final survivor, Turan,
output, and risk estimates are entirely scalar.  The conversion theorem below
recovers the literal graph-valued record.
-/

open Classical SimpleGraph

namespace Erdos636
namespace AugmentationExposureScalar

open AugmentationExposureAssembly
open AugmentationExposureCrowd

universe u

noncomputable section

variable {V : Type u} [Fintype V] [DecidableEq V]

/-! ## Good-candidate cardinality -/

/-- Deleting at most `badBudget` elements from a finite family leaves at least
`family.card - badBudget` elements.  This spelling is tailored to a good/bad
predicate partition. -/
lemma card_sub_le_card_filter_of_bad_card_le
    {A : Type*} [DecidableEq A] (family : Finset A) (good : A → Prop)
    [DecidablePred good] (badBudget : Nat)
    (hbad : (family.filter fun x => ¬good x).card ≤ badBudget) :
    family.card - badBudget ≤ (family.filter good).card := by
  have hpartition := Finset.card_filter_add_card_filter_not
    (s := family) good
  omega

/-- The `X0` witness in `PartialGood` has at least `s0 - badBudget`
degree-good cells as soon as its displayed real bad-cell estimate is bounded
by `badBudget + 1`. -/
theorem exists_candidate_good_family_card_lower_of_partialGood
    (G : SimpleGraph V) (M : Finset (Finset V)) (D1 : Finset V)
    (s0 badBudget : Nat)
    (diversityThreshold degreeCenter degreeRadius tS tX tCollision : Real)
    (hgood : AugmentationGraphPartial.PartialGood G M s0
      diversityThreshold degreeCenter degreeRadius tS tX tCollision D1)
    (htX : tX ≤ (badBudget : Real) + 1) :
    ∃ rawCandidates : Finset (Finset V),
      rawCandidates ⊆ M ∧ rawCandidates.card = s0 ∧
      s0 - badBudget ≤
        (rawCandidates.filter fun x =>
          AugmentationGraphPartial.DegreeGood G D1 x degreeCenter
            degreeRadius).card := by
  obtain ⟨_S0, X0, _hS0M, hX0M, _hS0card, hX0card, _hdisjoint,
    _hdiverse, _hbadS, hbadX, _hcollision⟩ := hgood
  have hbadReal :
      ((X0.filter fun x =>
        ¬AugmentationGraphPartial.DegreeGood G D1 x degreeCenter
          degreeRadius).card : Real) < (badBudget : Real) + 1 :=
    hbadX.trans_le htX
  have hbadNat :
      (X0.filter fun x =>
        ¬AugmentationGraphPartial.DegreeGood G D1 x degreeCenter
          degreeRadius).card ≤ badBudget := by
    have : (X0.filter fun x =>
        ¬AugmentationGraphPartial.DegreeGood G D1 x degreeCenter
          degreeRadius).card < badBudget + 1 := by
      exact_mod_cast hbadReal
    omega
  refine ⟨X0, hX0M, hX0card, ?_⟩
  rw [← hX0card]
  exact card_sub_le_card_filter_of_bad_card_le X0
    (fun x => AugmentationGraphPartial.DegreeGood G D1 x degreeCenter
      degreeRadius) badBudget hbadNat

/-- A direct bad-candidate-cardinality form for selected switching data. -/
lemma graphSelectedGoodCandidates_card_lower_of_bad_card_le
    (G : SimpleGraph V) (D1 : Finset V)
    (source rawCandidates : Finset (Finset V))
    (degreeCenter degreeRadius : Real) (nS gap badBudget s0 : Nat)
    (selected : AugmentationGraphFullState.GraphSelectedSwitchingData
      source rawCandidates G D1 degreeCenter degreeRadius nS gap badBudget)
    (hrawCard : rawCandidates.card = s0)
    (hbad : (rawCandidates.filter fun x =>
      ¬AugmentationGraphPartial.DegreeGood G D1 x degreeCenter
        degreeRadius).card ≤ badBudget) :
    s0 - badBudget ≤
      (graphSelectedGoodCandidates G D1 source rawCandidates degreeCenter
        degreeRadius nS gap badBudget selected).card := by
  unfold graphSelectedGoodCandidates
  rw [← hrawCard]
  exact card_sub_le_card_filter_of_bad_card_le rawCandidates
    (fun x => AugmentationGraphPartial.DegreeGood G D1 x degreeCenter
      degreeRadius) badBudget hbad

/-! ## Scalar monotonicity -/

/-- The Turan inequality is monotone when the certified lower bound for the
good family is replaced by its actual (larger) cardinality. -/
lemma turan_bound_mono
    {required edgeBudget lower actual : Nat}
    (hlower : lower <= actual)
    (hTuran : required * (lower + 2 * edgeBudget) < lower ^ 2) :
    required * (actual + 2 * edgeBudget) < actual ^ 2 := by
  have hrequired : required < lower := by
    by_contra hnot
    have hle : lower <= required := Nat.le_of_not_gt hnot
    have hsq : lower ^ 2 <= required * (lower + 2 * edgeBudget) := by
      calc
        lower ^ 2 = lower * lower := by rw [pow_two]
        _ <= required * lower := Nat.mul_le_mul_right lower hle
        _ <= required * (lower + 2 * edgeBudget) :=
          Nat.mul_le_mul_left required (Nat.le_add_right lower _)
    exact (Nat.not_lt_of_ge hsq) hTuran
  have hfac1 : (0 : Real) <= (actual : Real) - lower := by
    exact sub_nonneg.mpr (by exact_mod_cast hlower)
  have hfac2 : (0 : Real) <= (actual : Real) + lower - required := by
    exact sub_nonneg.mpr (by exact_mod_cast
      (show required <= actual + lower by omega))
  have hprod := mul_nonneg hfac1 hfac2
  have hTuranReal :
      (required : Real) * ((lower : Real) + 2 * edgeBudget) <
        (lower : Real) ^ 2 := by
    exact_mod_cast hTuran
  have hgoal :
      (required : Real) * ((actual : Real) + 2 * edgeBudget) <
        (actual : Real) ^ 2 := by
    nlinarith
  exact_mod_cast hgoal

/-- A scalar lower/upper sandwich supplies the exact survivor and Turan-piece
inequalities at the actual candidate cardinality. -/
lemma candidate_survivors_and_piece_bound_of_bounds
    {lower upper actual badDegree edgeBudget piece : Nat}
    (hlower : lower <= actual) (hupper : actual <= upper)
    (hsurvivors : badDegree < lower)
    (hpiece : piece * (upper + 2 * edgeBudget) <=
      (lower - badDegree) ^ 2) :
    badDegree < actual /\
      piece * (actual + 2 * edgeBudget) <=
        (actual - badDegree) ^ 2 := by
  constructor
  · exact hsurvivors.trans_le hlower
  · calc
      piece * (actual + 2 * edgeBudget) <=
          piece * (upper + 2 * edgeBudget) := by
        exact Nat.mul_le_mul_left piece (Nat.add_le_add_right hupper _)
      _ <= (lower - badDegree) ^ 2 := hpiece
      _ <= (actual - badDegree) ^ 2 := by
        exact Nat.pow_le_pow_left (Nat.sub_le_sub_right hlower badDegree) 2

lemma graphCollisionRisk_nonneg
    {c theta : Real} {K : Nat} (D1 : Finset V)
    (hc : 0 < c) (htheta : 0 < theta) (hK : 0 < K) :
    0 <= AugmentationGraphFull.graphCollisionRisk c theta K D1 := by
  unfold AugmentationGraphFull.graphCollisionRisk
  apply div_nonneg
  · exact (AntiConcentration.variancePointMassConstant_pos hc
      (by positivity : 0 < theta ^ 2 / 4) hK).le
  · exact Real.sqrt_nonneg _

lemma graphDegreeRisk_nonneg
    (degreeThreshold : Real) (nD K : Nat) :
    0 <= AugmentationGraphFull.graphDegreeRisk degreeThreshold nD K := by
  unfold AugmentationGraphFull.graphDegreeRisk
  positivity

/-- Both candidate-dependent terms in the full-exposure risk budget are
monotone in the candidate cardinality.  The geometric risk is independent of
the candidate family, so it is carried through unchanged. -/
lemma risk_budget_mono_candidate_card_with_geometricRisk
    {actual upper nS K nD badGeom badCollision badDegree : Nat}
    {c theta degreeThreshold meanRadius E qScale kappa geometricRisk : Real}
    (D1 : Finset V) (hactual : actual <= upper)
    (hc : 0 < c) (htheta : 0 < theta) (hK : 0 < K) (hE : 0 < E)
    (hscalar :
      (nS + 1 : Nat) * geometricRisk / (badGeom + 1 : Nat) +
        (nS + 1 : Nat) *
          (upper.choose 2 *
            AugmentationGraphFull.graphCollisionRisk c theta K D1 / E) /
            (badCollision + 1 : Nat) +
        upper *
            AugmentationGraphFull.graphDegreeRisk degreeThreshold nD K /
            (badDegree + 1 : Nat) +
        (nS *
            (Real.sqrt
              (AugmentationGraphFull.graphSwitchVariance K meanRadius nD) /
                qScale)) /
            kappa <= 1 / 6) :
      (nS + 1 : Nat) * geometricRisk / (badGeom + 1 : Nat) +
        (nS + 1 : Nat) *
          (actual.choose 2 *
            AugmentationGraphFull.graphCollisionRisk c theta K D1 / E) /
            (badCollision + 1 : Nat) +
        actual *
            AugmentationGraphFull.graphDegreeRisk degreeThreshold nD K /
            (badDegree + 1 : Nat) +
        (nS *
            (Real.sqrt
              (AugmentationGraphFull.graphSwitchVariance K meanRadius nD) /
                qScale)) /
            kappa <= 1 / 6 := by
  have hcollisionRisk := graphCollisionRisk_nonneg D1 hc htheta hK
  have hdegreeRisk := graphDegreeRisk_nonneg degreeThreshold nD K
  have hchoose : actual.choose 2 <= upper.choose 2 :=
    Nat.choose_le_choose 2 hactual
  have hcollisionTerm :
      (nS + 1 : Real) *
          ((actual.choose 2 : Real) *
            AugmentationGraphFull.graphCollisionRisk c theta K D1 / E) /
            (badCollision + 1 : Nat) <=
        (nS + 1 : Real) *
          ((upper.choose 2 : Real) *
            AugmentationGraphFull.graphCollisionRisk c theta K D1 / E) /
            (badCollision + 1 : Nat) := by
    gcongr
  have hdegreeTerm :
      (actual : Real) *
          AugmentationGraphFull.graphDegreeRisk degreeThreshold nD K /
          (badDegree + 1 : Nat) <=
        (upper : Real) *
          AugmentationGraphFull.graphDegreeRisk degreeThreshold nD K /
          (badDegree + 1 : Nat) := by
    gcongr
  norm_num at hcollisionTerm hdegreeTerm hscalar ⊢
  linarith [hcollisionTerm, hdegreeTerm]

/-- Corrected graph-facing risk monotonicity: the geometric term is the
bounded-difference risk for the union of `nS` cells, each of size at most
`K`. -/
lemma risk_budget_mono_candidate_card
    {actual upper nS K nD badGeom badCollision badDegree : Nat}
    {c theta geometricThreshold degreeThreshold meanRadius E qScale
      kappa : Real}
    (D1 : Finset V) (hactual : actual <= upper)
    (hc : 0 < c) (htheta : 0 < theta) (hK : 0 < K) (hE : 0 < E)
    (hscalar :
      (nS + 1 : Nat) *
          AugmentationGraphFull.graphDegreeRisk geometricThreshold nD
            (K * nS) /
          (badGeom + 1 : Nat) +
        (nS + 1 : Nat) *
          (upper.choose 2 *
            AugmentationGraphFull.graphCollisionRisk c theta K D1 / E) /
            (badCollision + 1 : Nat) +
        upper *
            AugmentationGraphFull.graphDegreeRisk degreeThreshold nD K /
            (badDegree + 1 : Nat) +
        (nS *
            (Real.sqrt
              (AugmentationGraphFull.graphSwitchVariance K meanRadius nD) /
                qScale)) /
            kappa <= 1 / 6) :
      (nS + 1 : Nat) *
          AugmentationGraphFull.graphDegreeRisk geometricThreshold nD
            (K * nS) /
          (badGeom + 1 : Nat) +
        (nS + 1 : Nat) *
          (actual.choose 2 *
            AugmentationGraphFull.graphCollisionRisk c theta K D1 / E) /
            (badCollision + 1 : Nat) +
        actual *
            AugmentationGraphFull.graphDegreeRisk degreeThreshold nD K /
            (badDegree + 1 : Nat) +
        (nS *
            (Real.sqrt
              (AugmentationGraphFull.graphSwitchVariance K meanRadius nD) /
                qScale)) /
            kappa <= 1 / 6 := by
  exact risk_budget_mono_candidate_card_with_geometricRisk D1 hactual hc
    htheta hK hE hscalar

/-- Compatibility form for the former zero geometric-risk interface. -/
lemma risk_budget_mono_candidate_card_zero_geom
    {actual upper nS K nD badGeom badCollision badDegree : Nat}
    {c theta degreeThreshold meanRadius E qScale kappa : Real}
    (D1 : Finset V) (hactual : actual <= upper)
    (hc : 0 < c) (htheta : 0 < theta) (hK : 0 < K) (hE : 0 < E)
    (hscalar :
      (nS + 1 : Nat) * 0 / (badGeom + 1 : Nat) +
        (nS + 1 : Nat) *
          (upper.choose 2 *
            AugmentationGraphFull.graphCollisionRisk c theta K D1 / E) /
            (badCollision + 1 : Nat) +
        upper *
            AugmentationGraphFull.graphDegreeRisk degreeThreshold nD K /
            (badDegree + 1 : Nat) +
        (nS *
            (Real.sqrt
              (AugmentationGraphFull.graphSwitchVariance K meanRadius nD) /
                qScale)) /
            kappa <= 1 / 6) :
      (nS + 1 : Nat) * 0 / (badGeom + 1 : Nat) +
        (nS + 1 : Nat) *
          (actual.choose 2 *
            AugmentationGraphFull.graphCollisionRisk c theta K D1 / E) /
            (badCollision + 1 : Nat) +
        actual *
            AugmentationGraphFull.graphDegreeRisk degreeThreshold nD K /
            (badDegree + 1 : Nat) +
        (nS *
            (Real.sqrt
              (AugmentationGraphFull.graphSwitchVariance K meanRadius nD) /
                qScale)) /
            kappa <= 1 / 6 := by
  exact risk_budget_mono_candidate_card_with_geometricRisk D1 hactual hc
    htheta hK hE hscalar

/-! ## Scalar crowded bounds -/

/-- The crowded-path numerical certificate with candidate-cardinality fields
replaced by uniform scalar bounds. -/
structure CrowdLargeScalarBounds
    {G : SimpleGraph V} {scale nW ell K : Nat}
    {alpha aDisc aDiv b : Real}
    (S : StructuralWitness G scale nW ell K alpha aDisc aDiv b)
    {mu degreeWindow : Nat}
    (path : OuterSwitchingPath.CrowdedPath S mu degreeWindow)
    (time : Nat) (D1 : Finset V)
    (source rawCandidates : Finset (Finset V))
    (nD nS m s0 : Nat) (canonicalCenter : Finset V → Real)
    (degreeCenter degreeRadius c theta pathShift geometricThreshold
      degreeThreshold meanRadius lam E qScale kappa sigma R globalRadius : Real)
    (badGeom badCollision badDegree edgeBudget piece L : Nat)
    (gap badBudget : Nat)
    (selected : AugmentationGraphFullState.GraphSelectedSwitchingData
      source rawCandidates G D1 degreeCenter degreeRadius nS gap badBudget) :
    Prop where
  half : D1.card = 2 * nD
  nD_pos : 0 < nD
  nS_pos : 0 < nS
  c_pos : 0 < c
  c_le_half : c ≤ 1 / 2
  theta_pos : 0 < theta
  selected_balance : c * D1.card ≤ nD
  unselected_balance : c * D1.card ≤ D1.card - nD
  geometricThreshold_nonneg : 0 ≤ geometricThreshold
  degreeThreshold_nonneg : 0 ≤ degreeThreshold
  meanRadius_nonneg : 0 ≤ meanRadius
  qScale_pos : 0 < qScale
  kappa_pos : 0 < kappa
  E_pos : 0 < E
  D1_subset : D1 ⊆ S.U0
  candidate_diverse :
    ∀ x ∈ graphSelectedGoodCandidates G D1 source rawCandidates
        degreeCenter degreeRadius nS gap badBudget selected,
      ∀ y ∈ graphSelectedGoodCandidates G D1 source rawCandidates
        degreeCenter degreeRadius nS gap badBudget selected, x ≠ y →
      theta * D1.card ≤ incidenceDiffMass G D1 x y
  small_degree_window : 2 * degreeRadius < theta / 2 * D1.card
  step_mean : ∀ j < nS,
    |(AugmentationGraphFullIdentity.switchOffsetInt G (path.W time) S.U0
        (graphSelectedStepRest G D1 source rawCandidates degreeCenter
          degreeRadius nS gap badBudget selected j)
        (graphSelectedStepLow G D1 source rawCandidates degreeCenter
          degreeRadius nS gap badBudget selected j)
        (graphSelectedStepHigh G D1 source rawCandidates degreeCenter
          degreeRadius nS gap badBudget selected j) : Real) +
      ((degreeInto G D1
          (graphSelectedStepHigh G D1 source rawCandidates degreeCenter
            degreeRadius nS gap badBudget selected j) : Real) -
        degreeInto G D1
          (graphSelectedStepLow G D1 source rawCandidates degreeCenter
            degreeRadius nS gap badBudget selected j)) / 2| ≤
      meanRadius * Real.sqrt nD
  mean_rise : lam <=
    (AugmentationGraphFullIdentity.endpointOffsetInt G (path.W time) S.U0
      (AugmentationGraphFull.cellUnion
        (graphSelectedReverseState G D1 source rawCandidates degreeCenter
          degreeRadius nS gap badBudget selected 0))
      (AugmentationGraphFull.cellUnion
        (graphSelectedReverseState G D1 source rawCandidates degreeCenter
          degreeRadius nS gap badBudget selected nS)) : Real) +
    ((degreeInto G D1
        (AugmentationGraphFull.cellUnion
          (graphSelectedReverseState G D1 source rawCandidates degreeCenter
            degreeRadius nS gap badBudget selected 0)) : Real) -
      degreeInto G D1
        (AugmentationGraphFull.cellUnion
          (graphSelectedReverseState G D1 source rawCandidates degreeCenter
            degreeRadius nS gap badBudget selected nS))) / 2
  literal_window : ∀ omega : AugmentationFull.Sample D1 nD,
    ∀ j ≤ nS,
      ∀ x ∈ graphSelectedGoodCandidates G D1 source rawCandidates
        degreeCenter degreeRadius nS gap badBudget selected,
    ¬AugmentationGraphFull.degreeDeviationBad G D1 nD degreeThreshold x omega →
      |(Erdos88.inducedEdges G
          (AugmentationGraphFull.exposedBase (path.W time) S.U0
            (AugmentationGraphFullIdentity.halfDeletion D1 nD omega)
            (graphSelectedReverseState G D1 source rawCandidates degreeCenter
              degreeRadius nS gap badBudget selected) j ∪ x) : Real) -
        AugmentationGraphFull.translatedLiteralGraphPath G (path.W time) S.U0
          (AugmentationGraphFullIdentity.halfDeletion D1 nD omega)
          (graphSelectedReverseState G D1 source rawCandidates degreeCenter
            degreeRadius nS gap badBudget selected) pathShift j| ≤ R
  global_window : ∀ omega : AugmentationFull.Sample D1 nD,
    ∀ j ≤ nS,
      ¬ AugmentationGraphFull.degreeDeviationBad G D1 nD geometricThreshold
          (AugmentationGraphFull.cellUnion
            (graphSelectedReverseState G D1 source rawCandidates degreeCenter
              degreeRadius nS gap badBudget selected j)) omega →
      |AugmentationGraphFull.translatedLiteralGraphPath G (path.W time) S.U0
          (AugmentationGraphFullIdentity.halfDeletion D1 nD omega)
          (graphSelectedReverseState G D1 source rawCandidates degreeCenter
            degreeRadius nS gap badBudget selected) pathShift j -
        canonicalCenter
          (AugmentationGraphFullIdentity.halfDeletion D1 nD omega)| + R ≤
        globalRadius
  m_pos : 1 <= m
  sigma_pos : 0 < sigma
  R_small : 2 * R < sigma
  switching_budget : (m : Real) *
      (qScale * Real.sqrt
        (AugmentationGraphFull.graphSwitchVariance K meanRadius nD) + sigma) +
        kappa ≤ lam
  collision_budget : E ≤ edgeBudget + 1
  candidate_survivors : badDegree < s0 - badBudget
  piece_bound : piece * (s0 + 2 * edgeBudget) ≤
    (s0 - badBudget - badDegree) ^ 2
  output_bound : L ≤ ((m + 1) - (badGeom + badCollision)) * piece
  risk_budget :
    (nS + 1 : Nat) *
        AugmentationGraphFull.graphDegreeRisk geometricThreshold nD (K * nS) /
          (badGeom + 1 : Nat) +
      (nS + 1 : Nat) *
      (s0.choose 2 *
          AugmentationGraphFull.graphCollisionRisk c theta K D1 / E) /
          (badCollision + 1 : Nat) +
      s0 * AugmentationGraphFull.graphDegreeRisk degreeThreshold nD K /
          (badDegree + 1 : Nat) +
      (nS *
          (Real.sqrt
            (AugmentationGraphFull.graphSwitchVariance K meanRadius nD) /
              qScale)) /
          kappa ≤ 1 / 6

/-- Uniform scalar bounds imply the graph-valued crowded bounds for the
particular selected candidate family. -/
theorem CrowdLargeScalarBounds.toCrowdLargeBounds
    {G : SimpleGraph V} {scale nW ell K : Nat}
    {alpha aDisc aDiv b : Real}
    {S : StructuralWitness G scale nW ell K alpha aDisc aDiv b}
    {mu degreeWindow : Nat}
    {path : OuterSwitchingPath.CrowdedPath S mu degreeWindow}
    {time : Nat} {D1 : Finset V}
    {source rawCandidates : Finset (Finset V)}
    {nD nS m s0 : Nat} {canonicalCenter : Finset V → Real}
    {degreeCenter degreeRadius c theta pathShift geometricThreshold
      degreeThreshold meanRadius lam E qScale kappa sigma R globalRadius : Real}
    {badGeom badCollision badDegree edgeBudget piece L : Nat}
    {gap badBudget : Nat}
    {selected : AugmentationGraphFullState.GraphSelectedSwitchingData
      source rawCandidates G D1 degreeCenter degreeRadius nS gap badBudget}
    (B : CrowdLargeScalarBounds S path time D1 source rawCandidates
      nD nS m s0 canonicalCenter degreeCenter degreeRadius c theta
      pathShift geometricThreshold degreeThreshold meanRadius lam E qScale
      kappa sigma R globalRadius badGeom badCollision badDegree edgeBudget
      piece L gap badBudget selected)
    (hrawCard : rawCandidates.card = s0) :
    CrowdLargeBounds S path time D1 source rawCandidates nD nS m
      canonicalCenter degreeCenter degreeRadius c theta pathShift
      geometricThreshold degreeThreshold meanRadius lam E qScale kappa sigma R
      globalRadius badGeom badCollision badDegree edgeBudget piece L gap
      badBudget selected := by
  let actual :=
    (graphSelectedGoodCandidates G D1 source rawCandidates degreeCenter
      degreeRadius nS gap badBudget selected).card
  have hlower : s0 - badBudget <= actual := by
    exact graphSelectedGoodCandidates_card_lower G D1 source rawCandidates
      degreeCenter degreeRadius nS gap badBudget s0 selected hrawCard
  have hupper : actual <= s0 := by
    exact graphSelectedGoodCandidates_card_upper G D1 source rawCandidates
      degreeCenter degreeRadius nS gap badBudget s0 selected hrawCard
  have hcandidate := candidate_survivors_and_piece_bound_of_bounds hlower
    hupper B.candidate_survivors B.piece_bound
  refine {
    half := B.half
    nD_pos := B.nD_pos
    nS_pos := B.nS_pos
    c_pos := B.c_pos
    c_le_half := B.c_le_half
    theta_pos := B.theta_pos
    selected_balance := B.selected_balance
    unselected_balance := B.unselected_balance
    geometricThreshold_nonneg := B.geometricThreshold_nonneg
    degreeThreshold_nonneg := B.degreeThreshold_nonneg
    meanRadius_nonneg := B.meanRadius_nonneg
    qScale_pos := B.qScale_pos
    kappa_pos := B.kappa_pos
    E_pos := B.E_pos
    D1_subset := B.D1_subset
    candidate_diverse := B.candidate_diverse
    small_degree_window := B.small_degree_window
    step_mean := B.step_mean
    mean_rise := B.mean_rise
    literal_window := B.literal_window
    global_window := B.global_window
    m_pos := B.m_pos
    sigma_pos := B.sigma_pos
    R_small := B.R_small
    switching_budget := B.switching_budget
    collision_budget := B.collision_budget
    candidate_survivors := hcandidate.1
    piece_bound := hcandidate.2
    output_bound := B.output_bound
    risk_budget := ?_ }
  exact risk_budget_mono_candidate_card D1 hupper B.c_pos B.theta_pos
    (S.k_pos.trans S.k_le) B.E_pos B.risk_budget

end

end AugmentationExposureScalar
end Erdos636
