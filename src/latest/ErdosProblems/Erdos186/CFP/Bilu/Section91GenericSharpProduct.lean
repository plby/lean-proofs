/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.Bilu.Section91SharpProductBodyPresentation
import ErdosProblems.Erdos186.CFP.Bilu.Section9PresentationReplacement

/-!
# The generic-rank sharp Section 9.1 product

Unlike the scalar source initializer, a Section 4 replacement starts from
the normalized lift set of a current presentation.  Its head has the current
rank, not rank one.  This module constructs the sharp product in that general
ambient rank and composes its vector-valued presentation map with the inverse
Mahler-coordinate map and the current integer presentation.
-/

namespace Erdos186.CFP.Bilu.Section91GenericSharpProduct

open scoped BigOperators ENNReal Pointwise NNReal
open MeasureTheory Set Module
open CFP.BiluFreiman Mahler MinkowskiSecond MinkowskiUpper
open Proposition75Data Proposition75Case2 Proposition75Case2Construction
  SubspaceLattice
open Section4PresentationLiftSet Section8PresentationNormalization
open Section9NormalizedReplacement Section91InitialPresentation
open Section91CoveringEnlargement
open Section91InitialPresentation.InitialPresentation
open Section91InitialCoordinates.InitialPresentation
open Section92PresentationDescent

noncomputable section

set_option autoImplicit false

variable {A : Finset ℤ} (X : RankedBodyPresentation A)
  {r : ℕ} {a : Fin r → EuclideanSpace ℝ (Fin X.1)}
  {D : GeometricData (normalizedEuclideanBody X) a}
  {coverConstant sigma : ℕ} {constant scale : ENNReal}

variable
  (N : CoveredNormalizedReplacement (D := D)
    (K := normalizedLiftSet X) (coverConstant := coverConstant)
    constant scale sigma)

abbrev GenericSectionRank := finrank ℝ D.C0

/-- The literal section/centre coordinate split in arbitrary head rank. -/
def genericInitialIndexEquiv :
    Fin (initialRank N) ≃
      Fin (GenericSectionRank (D := D)) ⊕ N.cover.centers :=
  Fintype.equivOfCardEq (by
    rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_coe,
      Fintype.card_fin]
    rfl)

def genericSplitLinearEquiv (R : Type*) [Semiring R] :
    (Fin (initialRank N) → R) ≃ₗ[R]
      (Fin (GenericSectionRank (D := D)) → R) ×
        (N.cover.centers → R) :=
  (LinearEquiv.piCongrLeft' (R := R) (φ := fun _ ↦ R)
      (genericInitialIndexEquiv X N)).trans
    (LinearEquiv.sumArrowLequivProdArrow
      (Fin (GenericSectionRank (D := D))) N.cover.centers R R)

@[simp] theorem genericSplitLinearEquiv_apply_fst
    (R : Type*) [Semiring R] (x : Fin (initialRank N) → R)
    (i : Fin (GenericSectionRank (D := D))) :
    (genericSplitLinearEquiv X N R x).1 i =
      x ((genericInitialIndexEquiv X N).symm (Sum.inl i)) := rfl

@[simp] theorem genericSplitLinearEquiv_apply_snd
    (R : Type*) [Semiring R] (x : Fin (initialRank N) → R)
    (c : N.cover.centers) :
    (genericSplitLinearEquiv X N R x).2 c =
      x ((genericInitialIndexEquiv X N).symm (Sum.inr c)) := rfl

theorem genericSplitLinearEquiv_integralEmbed
    (z : IntegralPoint (initialRank N)) :
    genericSplitLinearEquiv X N ℝ (integralEmbed z) =
      (integralEmbed (genericSplitLinearEquiv X N ℤ z).1,
        fun c ↦ ((genericSplitLinearEquiv X N ℤ z).2 c : ℝ)) := by
  ext i <;> rfl

/-- Sharp analytic data on the normalized section in arbitrary head rank. -/
structure GenericSharpSectionData where
  seminorm : Seminorm ℝ (Fin (GenericSectionRank (D := D)) → ℝ)
  definite : IsDefinite seminorm
  full : AdmitsIndependent seminorm (GenericSectionRank (D := D)) 1
  difference_mem : ∀
    (x : {x // x ∈ N.normalized.seed.sourceSlice})
    (y : {y // y ∈ N.normalized.seed.sourceSlice}),
      seminorm (integralEmbed
        ((coordinateIntegralBasis (D := D)).equivFun
          (coordinateLatticeEquiv D
            (Lemma45SectionSeed.differenceLift
              N.normalized.seed x y)))) ≤ 1
  volume_le :
    volume {x | seminorm x ≤ 1} ≤
      (2 : ENNReal) ^ GenericSectionRank (D := D) *
        (volume (coordinateB0 D) /
          ENNReal.ofReal
            (ZLattice.covolume (integralPoints (coordinateC0 D))))

def genericCenterSeminorm : Seminorm ℝ (N.cover.centers → ℝ) :=
  normSeminorm ℝ (N.cover.centers → ℝ)

def genericSharpProductSeminorm (S : GenericSharpSectionData X N) :
    Seminorm ℝ (Fin (initialRank N) → ℝ) :=
  (S.seminorm.comp ((LinearMap.fst ℝ _ _).comp
      (genericSplitLinearEquiv X N ℝ).toLinearMap)) ⊔
    ((genericCenterSeminorm X N).comp ((LinearMap.snd ℝ _ _).comp
      (genericSplitLinearEquiv X N ℝ).toLinearMap))

@[simp] theorem genericSharpProductSeminorm_apply
    (S : GenericSharpSectionData X N)
    (x : Fin (initialRank N) → ℝ) :
    genericSharpProductSeminorm X N S x =
      max (S.seminorm (genericSplitLinearEquiv X N ℝ x).1)
        ‖(genericSplitLinearEquiv X N ℝ x).2‖ := by
  rfl

theorem genericSharpProductSeminorm_definite
    (S : GenericSharpSectionData X N) :
    IsDefinite (genericSharpProductSeminorm X N S) := by
  intro x hx
  rw [genericSharpProductSeminorm_apply] at hx
  have hparts := max_le_iff.mp hx.le
  have hfirstZero : S.seminorm
      (genericSplitLinearEquiv X N ℝ x).1 = 0 :=
    le_antisymm hparts.1 (apply_nonneg S.seminorm _)
  have hsecondZero : ‖(genericSplitLinearEquiv X N ℝ x).2‖ = 0 :=
    le_antisymm hparts.2 (norm_nonneg _)
  have hfirst := S.definite _ hfirstZero
  have hsecond := norm_eq_zero.mp hsecondZero
  apply (genericSplitLinearEquiv X N ℝ).injective
  calc
    genericSplitLinearEquiv X N ℝ x = (0, 0) :=
      Prod.ext hfirst hsecond
    _ = genericSplitLinearEquiv X N ℝ 0 :=
      (map_zero (genericSplitLinearEquiv X N ℝ)).symm

/-- One explicit product-coordinate lift. -/
def genericSharpLift (c : N.cover.centers) (z : D.latticePoints) :
    IntegralPoint (initialRank N) :=
  (genericSplitLinearEquiv X N ℤ).symm
    ((coordinateIntegralBasis (D := D)).equivFun
      (coordinateLatticeEquiv D z), Pi.single c 1)

/-- Vector-valued product presentation map before returning through the
current Mahler coordinates. -/
noncomputable def genericSharpVectorMap :
    IntegralPoint (initialRank N) →+ IntegralPoint X.1 where
  toFun z :=
    oldLatticeMap (D := D)
        ((coordinateIntegralBasis (D := D)).equivFun.symm
          (genericSplitLinearEquiv X N ℤ z).1) +
      centersLinearCombination N
        (genericSplitLinearEquiv X N ℤ z).2
  map_zero' := by simp
  map_add' x y := by
    change oldLatticeMap (D := D)
          ((coordinateIntegralBasis (D := D)).equivFun.symm
            ((genericSplitLinearEquiv X N ℤ x).1 +
              (genericSplitLinearEquiv X N ℤ y).1)) +
        centersLinearCombination N
          ((genericSplitLinearEquiv X N ℤ x).2 +
            (genericSplitLinearEquiv X N ℤ y).2) = _
    rw [map_add, map_add, map_add]
    abel

/-- The current presentation map in normalized Mahler coordinates. -/
noncomputable def normalizedBackMap : IntegralPoint X.1 →+ ℤ :=
  X.2.map.comp (mahlerCoordinates X).symm.toAddMonoidHom

/-- The actual integer-valued replacement presentation. -/
noncomputable def genericSharpIntegerMap :
    IntegralPoint (initialRank N) →+ ℤ :=
  (normalizedBackMap X).comp (genericSharpVectorMap X N)

@[simp] theorem genericSharpVectorMap_genericSharpLift
    (c : N.cover.centers) (z : D.latticePoints) :
    genericSharpVectorMap X N (genericSharpLift X N c z) =
      latticeHead D z + (c : IntegralPoint X.1) := by
  change oldLatticeMap (D := D)
        ((coordinateIntegralBasis (D := D)).equivFun.symm
          (genericSplitLinearEquiv X N ℤ
            (genericSharpLift X N c z)).1) +
      centersLinearCombination N
        (genericSplitLinearEquiv X N ℤ
          (genericSharpLift X N c z)).2 = _
  rw [show genericSplitLinearEquiv X N ℤ (genericSharpLift X N c z) =
      ((coordinateIntegralBasis (D := D)).equivFun
        (coordinateLatticeEquiv D z), Pi.single c 1) by
    exact (genericSplitLinearEquiv X N ℤ).apply_symm_apply _]
  rw [LinearEquiv.symm_apply_apply,
    oldLatticeMap_coordinateLatticeEquiv,
    centersLinearCombination_single]

/-- Each original source element has a normalized selected lift. -/
def sourceNormalizedLift (x : A) : IntegralPoint X.1 :=
  mahlerCoordinates X (presentationLift X x)

theorem sourceNormalizedLift_mem (x : A) :
    sourceNormalizedLift X x ∈ normalizedLiftSet X := by
  exact Finset.mem_image.mpr ⟨presentationLift X x,
    (mem_presentationLiftSet_iff X _).mpr ⟨x, rfl⟩, rfl⟩

@[simp] theorem normalizedBackMap_sourceNormalizedLift (x : A) :
    normalizedBackMap X (sourceNormalizedLift X x) = x := by
  change X.2.map
    ((mahlerCoordinates X).symm (mahlerCoordinates X
      (presentationLift X x))) = x
  rw [(mahlerCoordinates X).symm_apply_apply, map_presentationLift]

theorem exists_genericSharpLift
    (S : GenericSharpSectionData X N) (x : ℤ) (hx : x ∈ A) :
    ∃ z : IntegralPoint (initialRank N),
      genericSharpProductSeminorm X N S (integralEmbed z) ≤ 1 ∧
        genericSharpIntegerMap X N z = x := by
  let x' : A := ⟨x, hx⟩
  obtain ⟨c, hc, u, v, hcover⟩ :=
    N.cover_lift (sourceNormalizedLift X x')
      (sourceNormalizedLift_mem X x')
  let c' : N.cover.centers := ⟨c, hc⟩
  let z : D.latticePoints :=
    Lemma45SectionSeed.differenceLift N.normalized.seed u v
  refine ⟨genericSharpLift X N c' z, ?_, ?_⟩
  · rw [genericSharpProductSeminorm_apply,
      genericSplitLinearEquiv_integralEmbed]
    simp only [genericSharpLift, LinearEquiv.apply_symm_apply, max_le_iff]
    refine ⟨S.difference_mem u v, ?_⟩
    rw [show (fun c => ((Pi.single c' 1 :
      N.cover.centers → ℤ) c : ℝ)) = Pi.single c' (1 : ℝ) by
        ext c
        simp only [Pi.single_apply]
        split <;> simp_all]
    rw [Pi.norm_single]
    norm_num
  · change normalizedBackMap X
      (genericSharpVectorMap X N (genericSharpLift X N c' z)) = x
    rw [genericSharpVectorMap_genericSharpLift]
    change normalizedBackMap X
      (latticeHead D z + (c : IntegralPoint X.1)) = x
    rw [add_comm, ← hcover, normalizedBackMap_sourceNormalizedLift]

/-! ## Measure, thickness, and body-presentation packaging -/

def genericSplitMeasurableEquiv :
    (Fin (initialRank N) → ℝ) ≃ᵐ
      (Fin (GenericSectionRank (D := D)) → ℝ) ×
        (N.cover.centers → ℝ) :=
  (MeasurableEquiv.piCongrLeft
      (fun _ : Fin (GenericSectionRank (D := D)) ⊕ N.cover.centers ↦ ℝ)
      (genericInitialIndexEquiv X N)).trans
    (MeasurableEquiv.sumPiEquivProdPi (fun _ ↦ ℝ))

@[simp] theorem genericSplitMeasurableEquiv_apply
    (x : Fin (initialRank N) → ℝ) :
    genericSplitMeasurableEquiv X N x =
      genericSplitLinearEquiv X N ℝ x := by
  apply Prod.ext
  · funext i
    change (MeasurableEquiv.piCongrLeft
        (fun _ : Fin (GenericSectionRank (D := D)) ⊕ N.cover.centers ↦ ℝ)
        (genericInitialIndexEquiv X N) x) (Sum.inl i) = _
    nth_rewrite 1 [← (genericInitialIndexEquiv X N).apply_symm_apply
      (Sum.inl i)]
    rw [MeasurableEquiv.piCongrLeft_apply_apply,
      genericSplitLinearEquiv_apply_fst]
  · funext c
    change (MeasurableEquiv.piCongrLeft
        (fun _ : Fin (GenericSectionRank (D := D)) ⊕ N.cover.centers ↦ ℝ)
        (genericInitialIndexEquiv X N) x) (Sum.inr c) = _
    nth_rewrite 1 [← (genericInitialIndexEquiv X N).apply_symm_apply
      (Sum.inr c)]
    rw [MeasurableEquiv.piCongrLeft_apply_apply,
      genericSplitLinearEquiv_apply_snd]

theorem genericSplitMeasurableEquiv_measurePreserving :
    MeasurePreserving (genericSplitMeasurableEquiv X N) volume volume := by
  exact
    (volume_measurePreserving_piCongrLeft
      (fun _ : Fin (GenericSectionRank (D := D)) ⊕ N.cover.centers ↦ ℝ)
        (genericInitialIndexEquiv X N)).trans
      (volume_measurePreserving_sumPiEquivProdPi (fun _ ↦ ℝ))

variable (S : GenericSharpSectionData X N)

theorem genericSharpProduct_unitBall_eq_preimage :
    {x | genericSharpProductSeminorm X N S x ≤ 1} =
      genericSplitMeasurableEquiv X N ⁻¹'
        ({u | S.seminorm u ≤ 1} ×ˢ {v | ‖v‖ ≤ 1}) := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_prod,
    genericSplitMeasurableEquiv_apply,
    genericSharpProductSeminorm_apply]
  exact max_le_iff

theorem genericCenter_unitBall_eq_Icc :
    {v : N.cover.centers → ℝ | ‖v‖ ≤ 1} =
      Set.Icc (fun _ ↦ (-1 : ℝ)) (fun _ ↦ (1 : ℝ)) := by
  ext v
  simp only [Set.mem_setOf_eq, Set.mem_Icc]
  rw [pi_norm_le_iff_of_nonneg (by norm_num), Pi.le_def, Pi.le_def]
  simp only [Real.norm_eq_abs, abs_le, forall_and]

theorem volume_genericCenter_unitBall :
    volume {v : N.cover.centers → ℝ | ‖v‖ ≤ 1} =
      (2 : ENNReal) ^ N.cover.centers.card := by
  rw [genericCenter_unitBall_eq_Icc X N, Real.volume_Icc_pi]
  norm_num [ENNReal.ofReal_ofNat]

theorem volume_genericSharpProduct_unitBall :
    volume {x | genericSharpProductSeminorm X N S x ≤ 1} =
      volume {u | S.seminorm u ≤ 1} *
        (2 : ENNReal) ^ N.cover.centers.card := by
  rw [genericSharpProduct_unitBall_eq_preimage X N S,
    (genericSplitMeasurableEquiv_measurePreserving X N).measure_preimage_emb
      (genericSplitMeasurableEquiv X N).measurableEmbedding]
  change (volume.prod volume)
      ({u | S.seminorm u ≤ 1} ×ˢ {v | ‖v‖ ≤ 1}) = _
  rw [Measure.prod_prod, volume_genericCenter_unitBall X N]

def genericSplitIntegralFamily :
    Fin (GenericSectionRank (D := D)) ⊕ N.cover.centers →
      IntegralPoint (GenericSectionRank (D := D)) ×
        (N.cover.centers → ℤ)
  | Sum.inl i => (S.full.choose i, 0)
  | Sum.inr c => (0, Pi.single c 1)

def genericSharpIndependentFamily (j : Fin (initialRank N)) :
    IntegralPoint (initialRank N) :=
  (genericSplitLinearEquiv X N ℤ).symm
    (genericSplitIntegralFamily X N S (genericInitialIndexEquiv X N j))

def genericSplitRealFamily :
    Fin (GenericSectionRank (D := D)) ⊕ N.cover.centers →
      (Fin (GenericSectionRank (D := D)) → ℝ) ×
        (N.cover.centers → ℝ)
  | Sum.inl i => (integralEmbed (S.full.choose i), 0)
  | Sum.inr c => (0, Pi.single c 1)

theorem genericSplitLinearEquiv_integralEmbed_independentFamily
    (j : Fin (initialRank N)) :
    genericSplitLinearEquiv X N ℝ
        (integralEmbed (genericSharpIndependentFamily X N S j)) =
      genericSplitRealFamily X N S (genericInitialIndexEquiv X N j) := by
  rw [genericSharpIndependentFamily,
    genericSplitLinearEquiv_integralEmbed, LinearEquiv.apply_symm_apply]
  cases h : genericInitialIndexEquiv X N j with
  | inl i =>
      apply Prod.ext
      · simp [genericSplitIntegralFamily, genericSplitRealFamily, h]
      · funext c
        simp [genericSplitIntegralFamily, genericSplitRealFamily, h]
  | inr c =>
      apply Prod.ext
      · simp [genericSplitIntegralFamily, genericSplitRealFamily, h]
      · funext c'
        simp [genericSplitIntegralFamily, genericSplitRealFamily, h,
          Pi.single_apply]

theorem linearIndependent_genericSplitRealFamily :
    LinearIndependent ℝ (genericSplitRealFamily X N S) := by
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

theorem linearIndependent_genericSharpIndependentFamily :
    LinearIndependent ℝ
      (fun j ↦ integralEmbed
        (genericSharpIndependentFamily X N S j)) := by
  apply LinearIndependent.of_comp
    (genericSplitLinearEquiv X N ℝ).toLinearMap
  have hsplit : LinearIndependent ℝ
      (fun j : Fin (initialRank N) ↦
        genericSplitRealFamily X N S (genericInitialIndexEquiv X N j)) :=
    (linearIndependent_genericSplitRealFamily X N S).comp
      (genericInitialIndexEquiv X N) (genericInitialIndexEquiv X N).injective
  convert hsplit using 1
  funext j
  exact genericSplitLinearEquiv_integralEmbed_independentFamily X N S j

theorem genericSharpIndependentFamily_mem_unitBall
    (j : Fin (initialRank N)) :
    genericSharpProductSeminorm X N S
        (integralEmbed (genericSharpIndependentFamily X N S j)) ≤ 1 := by
  rw [genericSharpProductSeminorm_apply,
    genericSplitLinearEquiv_integralEmbed_independentFamily]
  cases h : genericInitialIndexEquiv X N j with
  | inl i =>
      simp only [genericSplitRealFamily, h, max_le_iff, norm_zero]
      exact ⟨S.full.choose_spec.2 i, by norm_num⟩
  | inr c =>
      simp only [genericSplitRealFamily, h, max_le_iff, map_zero]
      refine ⟨by norm_num, ?_⟩
      rw [Pi.norm_single]
      norm_num

theorem genericSharpProductSeminorm_admitsIndependent :
    AdmitsIndependent (genericSharpProductSeminorm X N S)
      (initialRank N) 1 :=
  ⟨genericSharpIndependentFamily X N S,
    linearIndependent_genericSharpIndependentFamily X N S,
    genericSharpIndependentFamily_mem_unitBall X N S⟩

theorem genericSharpProduct_volumeReal_pos :
    0 < volume.real {x | genericSharpProductSeminorm X N S x ≤ 1} := by
  have hopen : {x | genericSharpProductSeminorm X N S x < 1} ∈
      nhds (0 : Fin (initialRank N) → ℝ) := by
    exact (continuous_seminorm
      (genericSharpProductSeminorm X N S)).continuousAt
      (Iio_mem_nhds (by simp))
  have hnhds : {x | genericSharpProductSeminorm X N S x ≤ 1} ∈
      nhds (0 : Fin (initialRank N) → ℝ) :=
    Filter.mem_of_superset hopen (by
      intro x hx
      change genericSharpProductSeminorm X N S x ≤ 1
      change genericSharpProductSeminorm X N S x < 1 at hx
      exact hx.le)
  exact ENNReal.toReal_pos
    (Measure.measure_pos_of_mem_nhds volume hnhds).ne'
    ((isBounded_unitBall (genericSharpProductSeminorm X N S)
      (genericSharpProductSeminorm_definite X N S)).measure_lt_top).ne

theorem volume_genericSharpProduct_le_sectionRatio_mul_centers :
    volume {x | genericSharpProductSeminorm X N S x ≤ 1} ≤
      ((2 : ENNReal) ^ GenericSectionRank (D := D) *
          (volume (coordinateB0 D) /
            ENNReal.ofReal
              (ZLattice.covolume (integralPoints (coordinateC0 D))))) *
        (2 : ENNReal) ^ N.cover.centers.card := by
  rw [volume_genericSharpProduct_unitBall X N S]
  exact mul_le_mul_of_nonneg_right S.volume_le bot_le

theorem genericSectionRatio_mul_centers_eq :
    ((2 : ENNReal) ^ GenericSectionRank (D := D) *
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

theorem volume_genericSharpProduct_le_sectionRatio :
    volume {x | genericSharpProductSeminorm X N S x ≤ 1} ≤
      (2 : ENNReal) ^ initialRank N *
        (volume (coordinateB0 D) /
          ENNReal.ofReal
            (ZLattice.covolume (integralPoints (coordinateC0 D)))) := by
  rw [← genericSectionRatio_mul_centers_eq X N]
  exact volume_genericSharpProduct_le_sectionRatio_mul_centers X N S

theorem volume_genericSharpProduct_le_normalized :
    volume {x | genericSharpProductSeminorm X N S x ≤ 1} ≤
      (2 : ENNReal) ^ initialRank N *
        (constant * volume (normalizedEuclideanBody X) * scale) := by
  let c : ENNReal := ENNReal.ofReal
    (ZLattice.covolume (integralPoints (coordinateC0 D)))
  have hcpos : 0 < c := by
    classical
    dsimp only [c]
    obtain ⟨presentationRank, P, hSat⟩ :=
      exists_saturatedPresentation_coordinateC0 D
    letI hdiscRow : DiscreteTopology P.rowLattice := by
      change DiscreteTopology
        (Submodule.span ℤ (Set.range P.rowBasis))
      infer_instance
    letI : DiscreteTopology (integralPoints (coordinateC0 D)) :=
      hSat ▸ hdiscRow
    letI : IsZLattice ℝ (integralPoints (coordinateC0 D)) :=
      ⟨span_coordinateIntegralPoints_eq_top D⟩
    exact ENNReal.ofReal_pos.mpr
      (ZLattice.covolume_pos (integralPoints (coordinateC0 D)))
  have hratio : volume (coordinateB0 D) / c ≤
      constant * volume (normalizedEuclideanBody X) * scale := by
    rw [ENNReal.div_le_iff hcpos.ne' ENNReal.ofReal_ne_top]
    simpa only [c, mul_assoc] using N.normalized.volume_bound
  exact (volume_genericSharpProduct_le_sectionRatio X N S).trans
    (mul_le_mul_of_nonneg_left hratio bot_le)

theorem genericInitialRank_pos_of_one_lt_card
    (S : GenericSharpSectionData X N) (hcard : 1 < A.card) :
    0 < initialRank N := by
  apply Section91PresentationCubification.rank_pos_of_one_lt_card_of_lifts
    (genericSharpIntegerMap X N)
  · intro x hx
    obtain ⟨z, _hz, hmap⟩ := exists_genericSharpLift X N S x hx
    exact ⟨z, hmap⟩
  · exact hcard

def genericSharpBodyPresentation (hcard : 1 < A.card) :
    BodyPresentation A (initialRank N) where
  rank_pos := genericInitialRank_pos_of_one_lt_card X N S hcard
  seminorm := genericSharpProductSeminorm X N S
  definite := genericSharpProductSeminorm_definite X N S
  full := genericSharpProductSeminorm_admitsIndependent X N S
  map := genericSharpIntegerMap X N
  lifts := exists_genericSharpLift X N S
  bodyVolume_pos := genericSharpProduct_volumeReal_pos X N S

def rankedGenericSharpBodyPresentation (hcard : 1 < A.card) :
    RankedBodyPresentation A :=
  ⟨initialRank N, genericSharpBodyPresentation X N S hcard⟩

@[simp] theorem rank_rankedGenericSharpBodyPresentation
    (hcard : 1 < A.card) :
    (rankedGenericSharpBodyPresentation X N S hcard).1 = initialRank N := rfl

@[simp] theorem bodyVolume_rankedGenericSharpBodyPresentation
    (hcard : 1 < A.card) :
    bodyVolume (rankedGenericSharpBodyPresentation X N S hcard) =
      volume.real {x | genericSharpProductSeminorm X N S x ≤ 1} := rfl

theorem bodyVolume_rankedGenericSharpBodyPresentation_le
    (hcard : 1 < A.card)
    (hconstant : constant ≠ ⊤) (hscale : scale ≠ ⊤) :
    bodyVolume (rankedGenericSharpBodyPresentation X N S hcard) ≤
      (2 : ℝ) ^ initialRank N *
        (constant.toReal * volume.real (normalizedEuclideanBody X) *
          scale.toReal) := by
  rw [bodyVolume_rankedGenericSharpBodyPresentation]
  have hB : volume (normalizedEuclideanBody X) ≠ ⊤ :=
    (isCompact_normalizedEuclideanBody X).measure_lt_top.ne
  have hright : (2 : ENNReal) ^ initialRank N *
      (constant * volume (normalizedEuclideanBody X) * scale) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.pow_ne_top (by norm_num))
      (ENNReal.mul_ne_top (ENNReal.mul_ne_top hconstant hB) hscale)
  have hleft :
      volume {x | genericSharpProductSeminorm X N S x ≤ 1} ≠ ⊤ :=
    ((isBounded_unitBall (genericSharpProductSeminorm X N S)
      (genericSharpProductSeminorm_definite X N S)).measure_lt_top).ne
  have hreal := (ENNReal.toReal_le_toReal hleft hright).mpr
    (volume_genericSharpProduct_le_normalized X N S)
  simpa only [Measure.real, ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_ofNat] using hreal

/-- Final source-shaped sharp bound: the old-body factor is explicit. -/
theorem bodyVolume_rankedGenericSharpBodyPresentation_le_oldBody
    (hcard : 1 < A.card)
    (hconstant : constant ≠ ⊤) (hscale : scale ≠ ⊤) :
    bodyVolume (rankedGenericSharpBodyPresentation X N S hcard) ≤
      (2 : ℝ) ^ initialRank N *
        (constant.toReal * ((X.1 : ℝ) ^ X.1 * bodyVolume X) *
          scale.toReal) := by
  have hbound := bodyVolume_rankedGenericSharpBodyPresentation_le X N S
    hcard hconstant hscale
  change bodyVolume (rankedGenericSharpBodyPresentation X N S hcard) ≤
    (2 : ℝ) ^ initialRank N *
      (constant.toReal * (volume (normalizedEuclideanBody X)).toReal *
        scale.toReal) at hbound
  rw [volume_normalizedEuclideanBody,
    volume_normalizedMahlerUnitBall,
    ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (pow_nonneg (by positivity) _)] at hbound
  exact hbound

end

end Erdos186.CFP.Bilu.Section91GenericSharpProduct
