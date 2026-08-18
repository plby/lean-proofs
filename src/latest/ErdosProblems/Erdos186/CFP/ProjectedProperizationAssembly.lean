/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.ProjectedProperizationDescent

/-!
# Assembly of projected properization

This file starts with the centered coefficient body of an enhanced CFP
witness, performs all necessary primitive kernel rank drops at one common
radius, and maps a terminal Mahler outer box into the target lattice.
-/

namespace Erdos186.CFP.ProjectedProperization

open scoped BigOperators
open Module
open NoCarryEmbedding
open Bilu.Mahler Bilu.MahlerBox Bilu.MahlerOuterContainer
open Bilu.MinkowskiSecond Bilu.Section92OuterInjectivityBridge

noncomputable section

/-- The coefficient-body description of a centered GAP dilation, including
the rank-zero case. -/
theorem mem_dilate_carrier_iff_exists_centeredBoxSeminorm_all_rank
    {d r : ℕ} (P : GAP d r) (radii : Fin r → ℕ)
    (hP : P.Centered radii) (hradii : ∀ i, 0 < radii i)
    (k : ℕ) (x : LatticePoint d) :
    x ∈ (P.dilate k).carrier ↔
      ∃ z : IntegralPoint r,
        centeredBoxSeminorm radii (integralEmbed z) ≤ (k : ℝ) ∧
        centeredStepHom P.steps z = x := by
  by_cases hr : r = 0
  · subst r
    constructor
    · intro hx
      have hx0 : x = 0 := by
        obtain ⟨c, hc⟩ := GAP.mem_carrier_iff.mp hx
        rw [(hP.dilate k).coordPoint_eq] at hc
        ext j
        exact congrFun hc.symm j
      subst x
      refine ⟨0, ?_, ?_⟩
      · rw [integralEmbed_zero, map_zero]
        positivity
      · ext j
        simp [centeredStepHom]
    · rintro ⟨z, _hz, rfl⟩
      have hzero : (0 : LatticePoint d) ∈ (P.dilate k).carrier :=
        (hP.dilate k).zero_mem_carrier
      have hstep : centeredStepHom P.steps z = 0 := by
        ext j
        simp [centeredStepHom]
      rw [hstep]
      exact hzero
  · exact mem_dilate_carrier_iff_exists_centeredBoxSeminorm
      (Nat.pos_of_ne_zero hr) P radii hP hradii k x

/-- One-fold GAP dilation is definitionally the same presentation, after
the width arithmetic is normalized. -/
theorem dilate_one_eq {d r : ℕ} (P : GAP d r) : P.dilate 1 = P := by
  rw [GAP.mk.injEq]
  refine ⟨?_, rfl, ?_⟩
  · funext j
    simp
  · funext i
    have hi := P.width_pos i
    simp only [GAP.dilate_widths, one_mul]
    omega

/-- Applying an additive homomorphism to a lattice vector is the displayed
combination of the images of its coordinates in any integral basis. -/
theorem map_eq_sum_basis_repr {n e : ℕ}
    (phi : IntegralPoint n →+ LatticePoint e)
    (b : Basis (Fin n) ℤ (IntegralPoint n)) (z : IntegralPoint n) :
    phi z = fun j ↦ ∑ i, b.repr z i * phi (b i) j := by
  calc
    phi z = phi (∑ i, (b.repr z i) • b i) :=
      congrArg phi (b.sum_repr z).symm
    _ = ∑ i, (b.repr z i) • phi (b i) := by
      rw [map_sum]
      simp only [map_zsmul]
    _ = fun j ↦ ∑ i, b.repr z i * phi (b i) j := by
      funext j
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

/-- Large-scale projected properization for an arbitrary additive target.
The advertised factor depends only on the rank bound `D`. -/
theorem exists_data_of_projectionFactor_le
    {d e s D k loss : ℕ} {H : Finset (LatticePoint d)}
    (f : LatticePoint d →+ LatticePoint e)
    (W : EnhancedCFPWitness H s D k loss)
    (hk : projectionFactor D ≤ k) :
    Nonempty (Data (factor := projectionFactor D) f W) := by
  let p₀ : Seminorm ℝ (Fin W.rank → ℝ) :=
    centeredBoxSeminorm W.symmetryRadii
  let phi₀ : IntegralPoint W.rank →+ LatticePoint e :=
    mappedCenteredStepHom f W.progression.steps
  have hp₀ : IsDefinite p₀ :=
    centeredBoxSeminorm_definite W.symmetryRadii W.symmetryRadii_pos
  have hfull₀ : AdmitsIndependent p₀ W.rank 1 :=
    centeredBoxSeminorm_admitsIndependent W.symmetryRadii W.symmetryRadii_pos
  let X : DescentState (h := projectionTestRadius D k) p₀ phi₀ :=
    DescentState.initial hp₀ hfull₀
  obtain ⟨Y, hYinj⟩ := DescentState.exists_injective_descendant X
  have hYrankW : Y.rank ≤ W.rank := by
    have h := Y.rank_add_drops
    omega
  have hYrankD : Y.rank ≤ D := hYrankW.trans W.rank_le
  have hYdropsD : Y.drops ≤ D := by
    have h := Y.rank_add_drops
    have hdropsW : Y.drops ≤ W.rank := by omega
    exact hdropsW.trans W.rank_le
  obtain ⟨b, hb⟩ := exists_isMahlerBasis Y.seminorm Y.definite
  let Pout : GAP Y.rank Y.rank :=
    centeredBasisGAP b (outerRadius Y.seminorm)
  let Q : GAP e Y.rank := mapGAP Y.map Pout
  let scale := projectionScale D k
  have hscale : 0 < scale := projectionScale_pos hk
  have houter : outerDilationBound Y.rank scale ≤
      (projectionTestRadius D k : ℝ) := by
    exact outerDilationBound_le_projectionTestRadius hYrankD
  have hYinjOuter : Set.InjOn Y.map
      {z : IntegralPoint Y.rank |
        Y.seminorm (integralEmbed z) ≤ outerDilationBound Y.rank scale} :=
    hYinj.mono fun _z hz ↦ hz.trans houter
  have hQscale : (Q.dilate scale).Proper := by
    exact mapped_outerGAP_dilate_proper_of_injOn_ball
      Y.definite Y.full Y.map b hb hYinjOuter
  have hQproper : Q.Proper := by
    exact GAP.SProper.proper (Q.sProper_of_dilate_proper scale hQscale)
      (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hscale))
  have hPoutCentered : Pout.Centered (outerRadius Y.seminorm) :=
    centered_centeredBasisGAP_outerRadius Y.seminorm b
  have hQCentered : Q.Centered (outerRadius Y.seminorm) :=
    mapGAP_centered_of_centered Y.map Pout hPoutCentered
  have hbase : W.progression.carrier.image f ⊆ Q.carrier := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    have hyDilate : y ∈ (W.progression.dilate 1).carrier := by
      simpa only [dilate_one_eq W.progression] using hy
    obtain ⟨z₀, hz₀, hstep⟩ :=
      (mem_dilate_carrier_iff_exists_centeredBoxSeminorm_all_rank
        W.progression W.symmetryRadii W.symmetryCentered
        W.symmetryRadii_pos 1 y).mp hyDilate
    have hz₀' : p₀ (integralEmbed z₀) ≤ 1 := by
      simpa only [p₀, Nat.cast_one] using hz₀
    obtain ⟨z, hz, hmap⟩ := Y.unit_survives z₀ hz₀'
    have hzPout : z ∈ Pout.carrier :=
      unitBall_integral_subset_outerGAP_all_rank
        Y.seminorm Y.definite b hb z hz
    rw [mapGAP_carrier]
    refine Finset.mem_image.mpr ⟨z, hzPout, ?_⟩
    calc
      Y.map z = phi₀ z₀ := hmap
      _ = f y := by
        change f (centeredStepHom W.progression.steps z₀) = f y
        rw [hstep]
  have hcarrier : (Q.dilate scale).carrier ⊆
      (mapGAP f (W.progression.dilate k)).carrier := by
    intro q hq
    have hq' : q ∈ (mapGAP Y.map (Pout.dilate scale)).carrier := by
      simpa only [mapGAP_dilate] using hq
    rw [mapGAP_carrier] at hq'
    obtain ⟨z, hzPout, rfl⟩ := Finset.mem_image.mp hq'
    have hzBound : Y.seminorm (integralEmbed z) ≤
        outerDilationBound Y.rank scale :=
      seminorm_le_outerDilationBound_of_mem_outerGAP
        Y.definite Y.full b hb z hzPout
    have hzTest : Y.seminorm (integralEmbed z) ≤
        (projectionTestRadius D k : ℝ) := hzBound.trans houter
    obtain ⟨z₀, hmap, hz₀⟩ := Y.lift_back
      (projectionTestRadius D k : ℝ) (by positivity) z hzTest
    have hz₀k : p₀ (integralEmbed z₀) ≤ (k : ℝ) := by
      calc
        p₀ (integralEmbed z₀) ≤
            (projectionTestRadius D k : ℝ) +
              (Y.drops : ℝ) * (projectionTestRadius D k : ℝ) := hz₀
        _ = (((Y.drops + 1) * projectionTestRadius D k : ℕ) : ℝ) := by
          push_cast
          ring
        _ ≤ (k : ℝ) := by
          exact_mod_cast succ_mul_projectionTestRadius_le_source hYdropsD
    have hz₀P : centeredStepHom W.progression.steps z₀ ∈
        (W.progression.dilate k).carrier := by
      apply (mem_dilate_carrier_iff_exists_centeredBoxSeminorm_all_rank
        W.progression W.symmetryRadii W.symmetryCentered
        W.symmetryRadii_pos k _).mpr
      exact ⟨z₀, hz₀k, rfl⟩
    rw [mapGAP_carrier]
    refine Finset.mem_image.mpr
      ⟨centeredStepHom W.progression.steps z₀, hz₀P, ?_⟩
    calc
      f (centeredStepHom W.progression.steps z₀) = phi₀ z₀ := rfl
      _ = Y.map z := hmap
  have hcovered : translate (f W.translatePoint) (Q.dilate scale).carrier ⊆
      translate (f W.translatePoint)
        (mapGAP f (W.progression.dilate k)).carrier := by
    intro x hx
    obtain ⟨q, hq, rfl⟩ := mem_translate_iff.mp hx
    exact mem_translate_iff.mpr ⟨q, hcarrier hq, rfl⟩
  have htranslate : ∃ z : IntegralPoint Y.rank,
      Y.map z = f W.translatePoint := by
    obtain ⟨z₀, hz₀⟩ := exists_centeredStepHom_eq_translatePoint W
    obtain ⟨z, hz⟩ := Y.range_survives z₀
    refine ⟨z, ?_⟩
    calc
      Y.map z = phi₀ z₀ := hz
      _ = f W.translatePoint := by
        change f (centeredStepHom W.progression.steps z₀) = _
        rw [hz₀]
  have hhomogeneous : ∃ c : Fin Y.rank → ℤ,
      f W.translatePoint + (Q.dilate scale).offset =
        (fun j ↦ ∑ i, c i * Q.steps i j) := by
    obtain ⟨z, hz⟩ := htranslate
    let c : Fin Y.rank → ℤ := fun i ↦
      b.repr z i - ((scale * outerRadius Y.seminorm i : ℕ) : ℤ)
    refine ⟨c, ?_⟩
    have hzsum : f W.translatePoint =
        fun j ↦ ∑ i, b.repr z i * Q.steps i j := by
      exact hz.symm.trans (map_eq_sum_basis_repr Y.map b z)
    rw [(hQCentered.dilate scale).offset_eq]
    funext j
    have hzj := congrFun hzsum j
    simp only [Pi.add_apply, GAP.dilate_steps, c, sub_mul,
      Finset.sum_sub_distrib]
    linear_combination hzj
  exact ⟨{
    scale := scale
    scale_pos := hscale
    scale_le_source := projectionScale_le_source D k
    source_le_factor_mul_scale := source_le_projectionFactor_mul_scale hk
    rank := Y.rank
    rank_le := hYrankW
    progression := Q
    progression_proper := hQproper
    dilate_proper := hQscale
    progression_symmetric := ⟨outerRadius Y.seminorm, hQCentered⟩
    progression_nondegenerate := by
      exact hQCentered.nondegenerate_iff.mpr
        (outerRadius_pos Y.seminorm Y.definite)
    homogeneous := hQCentered.homogeneous
    base_image_subset := hbase
    translatePoint := f W.translatePoint
    covered_subset := hcovered
    covered_translate_homogeneous := hhomogeneous }⟩

/-- Box-dehomogenization specialization consumed by the Appendix
dimension-reduction theorem. -/
theorem exists_data_boxDehomogenize
    {d s D k loss scaleNum scaleDen : ℕ}
    (B : IntegerBox d) (A : Finset (LatticePoint d))
    (W : FixedScaleWitness
      (AppendixEncoding.homogenizedBoxSet B A)
        s D k loss scaleNum scaleDen)
    (hk : projectionFactor D ≤ k) :
    Nonempty (Data (factor := projectionFactor D)
      (AppendixEncoding.boxDehomogenizeHom B) W.enhanced) :=
  exists_data_of_projectionFactor_le
    (AppendixEncoding.boxDehomogenizeHom B) W.enhanced hk

end

end Erdos186.CFP.ProjectedProperization

#print axioms
  Erdos186.CFP.ProjectedProperization.mem_dilate_carrier_iff_exists_centeredBoxSeminorm_all_rank
#print axioms Erdos186.CFP.ProjectedProperization.map_eq_sum_basis_repr
#print axioms
  Erdos186.CFP.ProjectedProperization.exists_data_of_projectionFactor_le
#print axioms
  Erdos186.CFP.ProjectedProperization.exists_data_boxDehomogenize
