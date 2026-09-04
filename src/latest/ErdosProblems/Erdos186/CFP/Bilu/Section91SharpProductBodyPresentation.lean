/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.Bilu.Section91SharpProductPresentation
import ErdosProblems.Erdos186.CFP.Bilu.Section91PresentationCubification
import ErdosProblems.Erdos186.CFP.Bilu.MinkowskiUpper
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# The sharp Section 9.1 product as a body presentation

This file finishes the abstract product construction of
`Section91SharpProductPresentation`.  It proves that the coordinate split
preserves Lebesgue measure, computes the volume of the centre cube, supplies
a full independent integral family, and packages the result in the common
`BodyPresentation` interface used by Section 9.2.
-/

namespace Erdos186.CFP.Bilu.Section91SharpProductBodyPresentation

open scoped BigOperators ENNReal Pointwise NNReal
open MeasureTheory Set Module
open Mahler MinkowskiSecond MinkowskiUpper
open Proposition75Data Proposition75Case2 Proposition75Case2Construction
  SubspaceLattice
open Section9NormalizedReplacement Section91InitialPresentation
open Section91InitialPresentation.InitialPresentation
open Section91SharpProductPresentation
open Section92PresentationDescent

noncomputable section

set_option autoImplicit false

variable {r : ℕ} {B : Set (EuclideanSpace ℝ (Fin 1))}
  {a : Fin r → EuclideanSpace ℝ (Fin 1)}
  {D : GeometricData B a}
  {A : Finset ℤ} {coverConstant sigma : ℕ}
  {constant scale : ENNReal}

variable
  (N : CoveredNormalizedReplacement (D := D)
    (K := Section90IntegerInitialization.integerSet A)
    (coverConstant := coverConstant) constant scale sigma)

/-- The measurable version of the literal section/centre coordinate split. -/
def splitMeasurableEquiv :
    (Fin (initialRank N) → ℝ) ≃ᵐ
      (Fin (SectionRank D) → ℝ) × (N.cover.centers → ℝ) :=
  (MeasurableEquiv.piCongrLeft
      (fun _ : Fin (SectionRank D) ⊕ N.cover.centers ↦ ℝ)
      (initialIndexEquiv N))
    -- The family is constant, so after reindexing its displayed domain is
    -- the section/centre sum.
    |>.trans
    (MeasurableEquiv.sumPiEquivProdPi (fun _ ↦ ℝ))

@[simp] theorem splitMeasurableEquiv_apply
    (x : Fin (initialRank N) → ℝ) :
    splitMeasurableEquiv N x = splitLinearEquiv ℝ N x := by
  apply Prod.ext
  · funext i
    change (MeasurableEquiv.piCongrLeft
        (fun _ : Fin (SectionRank D) ⊕ N.cover.centers ↦ ℝ)
        (initialIndexEquiv N) x) (Sum.inl i) = _
    nth_rewrite 1 [← (initialIndexEquiv N).apply_symm_apply (Sum.inl i)]
    rw [MeasurableEquiv.piCongrLeft_apply_apply]
    rw [splitLinearEquiv_apply_fst]
  · funext c
    change (MeasurableEquiv.piCongrLeft
        (fun _ : Fin (SectionRank D) ⊕ N.cover.centers ↦ ℝ)
        (initialIndexEquiv N) x) (Sum.inr c) = _
    nth_rewrite 1 [← (initialIndexEquiv N).apply_symm_apply (Sum.inr c)]
    rw [MeasurableEquiv.piCongrLeft_apply_apply]
    rw [splitLinearEquiv_apply_snd]

/-- The literal coordinate split preserves the standard product Lebesgue
measure. -/
theorem splitMeasurableEquiv_measurePreserving :
    MeasurePreserving (splitMeasurableEquiv N) volume volume := by
  exact
    (volume_measurePreserving_piCongrLeft
      (fun _ : Fin (SectionRank D) ⊕ N.cover.centers ↦ ℝ)
        (initialIndexEquiv N)).trans
      (volume_measurePreserving_sumPiEquivProdPi (fun _ ↦ ℝ))

variable (S : SharpSectionData N)

/-- The sharp product unit ball is the inverse image of the section ball
times the centre cube. -/
theorem sharpProduct_unitBall_eq_preimage :
    {x | sharpProductSeminorm N S x ≤ 1} =
      splitMeasurableEquiv N ⁻¹'
        ({u | S.seminorm u ≤ 1} ×ˢ {v | ‖v‖ ≤ 1}) := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_prod,
    splitMeasurableEquiv_apply, sharpProductSeminorm_apply]
  exact max_le_iff

/-- The centre sup-norm ball is the literal coordinate cube.  This also
covers the zero-dimensional centre block. -/
theorem center_unitBall_eq_Icc :
    {v : N.cover.centers → ℝ | ‖v‖ ≤ 1} =
      Set.Icc (fun _ ↦ (-1 : ℝ)) (fun _ ↦ (1 : ℝ)) := by
  ext v
  simp only [Set.mem_setOf_eq, Set.mem_Icc]
  rw [pi_norm_le_iff_of_nonneg (by norm_num), Pi.le_def, Pi.le_def]
  simp only [Real.norm_eq_abs, abs_le, forall_and]

/-- Exact volume of the centre cube. -/
theorem volume_center_unitBall :
    volume {v : N.cover.centers → ℝ | ‖v‖ ≤ 1} =
      (2 : ENNReal) ^ N.cover.centers.card := by
  rw [center_unitBall_eq_Icc N, Real.volume_Icc_pi]
  norm_num [ENNReal.ofReal_ofNat]

/-- Exact max-product volume formula. -/
theorem volume_sharpProduct_unitBall :
    volume {x | sharpProductSeminorm N S x ≤ 1} =
      volume {u | S.seminorm u ≤ 1} *
        (2 : ENNReal) ^ N.cover.centers.card := by
  rw [sharpProduct_unitBall_eq_preimage N S,
    (splitMeasurableEquiv_measurePreserving N).measure_preimage_emb
      (splitMeasurableEquiv N).measurableEmbedding]
  change (volume.prod volume)
      ({u | S.seminorm u ≤ 1} ×ˢ {v | ‖v‖ ≤ 1}) = _
  rw [Measure.prod_prod, volume_center_unitBall N]

/-! ## Full integral thickness -/

/-- The independent integral family in split coordinates: the supplied
section family, followed by the standard basis in the centre block. -/
def splitIntegralFamily :
    Fin (SectionRank D) ⊕ N.cover.centers →
      IntegralPoint (SectionRank D) × (N.cover.centers → ℤ)
  | Sum.inl i => (S.full.choose i, 0)
  | Sum.inr c => (0, Pi.single c 1)

/-- The same family transported back to the literal standard lattice of
the product presentation. -/
def sharpIndependentFamily (j : Fin (initialRank N)) :
    IntegralPoint (initialRank N) :=
  (splitLinearEquiv ℤ N).symm
    (splitIntegralFamily N S (initialIndexEquiv N j))

/-- Real embedding of the split integral family. -/
def splitRealFamily :
    Fin (SectionRank D) ⊕ N.cover.centers →
      (Fin (SectionRank D) → ℝ) × (N.cover.centers → ℝ)
  | Sum.inl i => (integralEmbed (S.full.choose i), 0)
  | Sum.inr c => (0, Pi.single c 1)

theorem splitLinearEquiv_integralEmbed_sharpIndependentFamily
    (j : Fin (initialRank N)) :
    splitLinearEquiv ℝ N
        (integralEmbed (sharpIndependentFamily N S j)) =
      splitRealFamily N S (initialIndexEquiv N j) := by
  rw [sharpIndependentFamily, splitLinearEquiv_integralEmbed,
    LinearEquiv.apply_symm_apply]
  cases h : initialIndexEquiv N j with
  | inl i =>
      apply Prod.ext
      · simp [splitIntegralFamily, splitRealFamily, h]
      · funext c
        simp [splitIntegralFamily, splitRealFamily, h]
  | inr c =>
      apply Prod.ext
      · simp [splitIntegralFamily, splitRealFamily, h]
      · funext c'
        simp [splitIntegralFamily, splitRealFamily, h, Pi.single_apply]

theorem linearIndependent_splitRealFamily :
    LinearIndependent ℝ (splitRealFamily N S) := by
  have hsection : LinearIndependent ℝ
      (fun i ↦ integralEmbed (S.full.choose i)) :=
    S.full.choose_spec.1
  have hcenter : LinearIndependent ℝ
      (fun c : N.cover.centers ↦ Pi.single c (1 : ℝ)) := by
    convert (Pi.basisFun ℝ N.cover.centers).linearIndependent using 1
    funext c
    rw [Pi.basisFun_apply]
  convert (linearIndependent_inl_union_inr' hsection hcenter) using 1
  funext q
  cases q <;> rfl

theorem linearIndependent_sharpIndependentFamily :
    LinearIndependent ℝ
      (fun j ↦ integralEmbed (sharpIndependentFamily N S j)) := by
  apply LinearIndependent.of_comp (splitLinearEquiv ℝ N).toLinearMap
  have hsplit : LinearIndependent ℝ
      (fun j : Fin (initialRank N) ↦
        splitRealFamily N S (initialIndexEquiv N j)) :=
    (linearIndependent_splitRealFamily N S).comp
      (initialIndexEquiv N) (initialIndexEquiv N).injective
  convert hsplit using 1
  funext j
  exact splitLinearEquiv_integralEmbed_sharpIndependentFamily N S j

theorem sharpIndependentFamily_mem_unitBall
    (j : Fin (initialRank N)) :
    sharpProductSeminorm N S
        (integralEmbed (sharpIndependentFamily N S j)) ≤ 1 := by
  rw [sharpProductSeminorm_apply,
    splitLinearEquiv_integralEmbed_sharpIndependentFamily]
  cases h : initialIndexEquiv N j with
  | inl i =>
      simp only [splitRealFamily, h, max_le_iff, norm_zero]
      exact ⟨S.full.choose_spec.2 i, by norm_num⟩
  | inr c =>
      simp only [splitRealFamily, h, max_le_iff, map_zero]
      refine ⟨by norm_num, ?_⟩
      rw [Pi.norm_single]
      norm_num

/-- The sharp max-product body contains a full independent integral
family at radius one. -/
theorem sharpProductSeminorm_admitsIndependent :
    AdmitsIndependent (sharpProductSeminorm N S) (initialRank N) 1 :=
  ⟨sharpIndependentFamily N S,
    linearIndependent_sharpIndependentFamily N S,
    sharpIndependentFamily_mem_unitBall N S⟩

/-! ## Volume bounds and the common presentation interface -/

/-- A definite seminorm unit ball has positive finite real volume. -/
theorem sharpProduct_volumeReal_pos :
    0 < volume.real {x | sharpProductSeminorm N S x ≤ 1} := by
  have hopen : {x | sharpProductSeminorm N S x < 1} ∈
      nhds (0 : Fin (initialRank N) → ℝ) := by
    exact (continuous_seminorm (sharpProductSeminorm N S)).continuousAt
      (Iio_mem_nhds (by simp))
  have hnhds : {x | sharpProductSeminorm N S x ≤ 1} ∈
      nhds (0 : Fin (initialRank N) → ℝ) :=
    Filter.mem_of_superset hopen (by
      intro x hx
      change sharpProductSeminorm N S x ≤ 1
      change sharpProductSeminorm N S x < 1 at hx
      exact hx.le)
  exact ENNReal.toReal_pos
    (Measure.measure_pos_of_mem_nhds volume hnhds).ne'
    ((isBounded_unitBall (sharpProductSeminorm N S)
      (sharpProductSeminorm_definite N S)).measure_lt_top).ne

/-- Multiplying the sharp section estimate by the centre-cube volume. -/
theorem volume_sharpProduct_le_sectionRatio_mul_centers :
    volume {x | sharpProductSeminorm N S x ≤ 1} ≤
      ((2 : ENNReal) ^ SectionRank D *
          (volume (coordinateB0 D) /
            ENNReal.ofReal
              (ZLattice.covolume (integralPoints (coordinateC0 D))))) *
        (2 : ENNReal) ^ N.cover.centers.card := by
  rw [volume_sharpProduct_unitBall N S]
  exact mul_le_mul_of_nonneg_right S.volume_le bot_le

/-- The two coordinate-block powers combine to the full initial rank. -/
theorem sectionRatio_mul_centers_eq :
    ((2 : ENNReal) ^ SectionRank D *
        (volume (coordinateB0 D) /
          ENNReal.ofReal
            (ZLattice.covolume (integralPoints (coordinateC0 D))))) *
      (2 : ENNReal) ^ N.cover.centers.card =
    (2 : ENNReal) ^ initialRank N *
      (volume (coordinateB0 D) /
        ENNReal.ofReal
          (ZLattice.covolume (integralPoints (coordinateC0 D)))) := by
  rw [initialRank, pow_add]
  ac_rfl

/-- The exact product formula and the sharp section estimate give the
pre-cancellation bound with the literal section-lattice covolume. -/
theorem volume_sharpProduct_le_sectionRatio :
    volume {x | sharpProductSeminorm N S x ≤ 1} ≤
      (2 : ENNReal) ^ initialRank N *
        (volume (coordinateB0 D) /
          ENNReal.ofReal
            (ZLattice.covolume (integralPoints (coordinateC0 D)))) := by
  rw [← sectionRatio_mul_centers_eq N]
  exact volume_sharpProduct_le_sectionRatio_mul_centers N S

/-- The normalized Proposition 7.5 estimate cancels the section-lattice
covolume exactly. -/
theorem volume_sharpProduct_le_normalized :
    volume {x | sharpProductSeminorm N S x ≤ 1} ≤
      (2 : ENNReal) ^ initialRank N *
        (constant * volume B * scale) := by
  let c : ENNReal := ENNReal.ofReal
    (ZLattice.covolume (integralPoints (coordinateC0 D)))
  have hcpos : 0 < c := by
    classical
    dsimp only [c]
    obtain ⟨presentationRank, P, hSat⟩ :=
      exists_saturatedPresentation_coordinateC0 D
    let hdiscRow : DiscreteTopology P.rowLattice := by
      change DiscreteTopology
        (Submodule.span ℤ (Set.range P.rowBasis))
      infer_instance
    let : DiscreteTopology (integralPoints (coordinateC0 D)) :=
      hSat ▸ hdiscRow
    let : IsZLattice ℝ (integralPoints (coordinateC0 D)) :=
      ⟨span_coordinateIntegralPoints_eq_top D⟩
    exact ENNReal.ofReal_pos.mpr
      (ZLattice.covolume_pos (integralPoints (coordinateC0 D)))
  have hratio : volume (coordinateB0 D) / c ≤
      constant * volume B * scale := by
    rw [ENNReal.div_le_iff hcpos.ne' ENNReal.ofReal_ne_top]
    simpa only [c, mul_assoc] using N.normalized.volume_bound
  exact (volume_sharpProduct_le_sectionRatio N S).trans
    (mul_le_mul_of_nonneg_left hratio bot_le)

/-- The large-cardinality source lifts force the product rank to be
positive. -/
theorem initialRank_pos_of_one_lt_card
    (S : SharpSectionData N) (hcard : 1 < A.card) :
    0 < initialRank N := by
  apply Section91PresentationCubification.rank_pos_of_one_lt_card_of_lifts
    (sharpIntegerMap N)
  · intro x hx
    obtain ⟨z, _hz, hmap⟩ := exists_sharpLift N S x hx
    exact ⟨z, hmap⟩
  · exact hcard

/-- The sharp product body in the common fixed-rank presentation
interface. -/
def sharpBodyPresentation (hcard : 1 < A.card) :
    BodyPresentation A (initialRank N) where
  rank_pos := initialRank_pos_of_one_lt_card N S hcard
  seminorm := sharpProductSeminorm N S
  definite := sharpProductSeminorm_definite N S
  full := sharpProductSeminorm_admitsIndependent N S
  map := sharpIntegerMap N
  lifts := exists_sharpLift N S
  bodyVolume_pos := sharpProduct_volumeReal_pos N S

/-- Rank-bundled form of the sharp product presentation. -/
def rankedSharpBodyPresentation (hcard : 1 < A.card) :
    RankedBodyPresentation A :=
  ⟨initialRank N, sharpBodyPresentation N S hcard⟩

@[simp] theorem rank_rankedSharpBodyPresentation (hcard : 1 < A.card) :
    (rankedSharpBodyPresentation N S hcard).1 = initialRank N :=
  rfl

@[simp] theorem bodyVolume_rankedSharpBodyPresentation
    (hcard : 1 < A.card) :
    bodyVolume (rankedSharpBodyPresentation N S hcard) =
      volume.real {x | sharpProductSeminorm N S x ≤ 1} :=
  rfl

/-- Real-valued sharp product estimate.  Finiteness is stated explicitly
because this is the exact form consumed by the Section 4 decay inequality.
-/
theorem bodyVolume_rankedSharpBodyPresentation_le
    (hcard : 1 < A.card)
    (hconstant : constant ≠ ⊤) (hB : volume B ≠ ⊤)
    (hscale : scale ≠ ⊤) :
    bodyVolume (rankedSharpBodyPresentation N S hcard) ≤
      (2 : ℝ) ^ initialRank N *
        (constant.toReal * volume.real B * scale.toReal) := by
  rw [bodyVolume_rankedSharpBodyPresentation]
  have hright :
      (2 : ENNReal) ^ initialRank N * (constant * volume B * scale) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.pow_ne_top (by norm_num))
      (ENNReal.mul_ne_top (ENNReal.mul_ne_top hconstant hB) hscale)
  have hleft : volume {x | sharpProductSeminorm N S x ≤ 1} ≠ ⊤ :=
    ((isBounded_unitBall (sharpProductSeminorm N S)
      (sharpProductSeminorm_definite N S)).measure_lt_top).ne
  have hreal := (ENNReal.toReal_le_toReal hleft hright).mpr
    (volume_sharpProduct_le_normalized N S)
  simpa only [Measure.real, ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_ofNat] using hreal


end

end Erdos186.CFP.Bilu.Section91SharpProductBodyPresentation
