/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.Corollary217ScaleShrink

/-!
# Source-scale contraction in the Corollary 2.17 map-back

The common coordinate box is built at a source scale `h`.  The source proof
divides the radii of the Corollary 2.17 progression by `h`, and compensates
by multiplying the final dilation parameter by `h`.  This module performs
that contraction before mapping the common basis back to the source line.
-/

namespace Erdos186.CFP

open scoped BigOperators
open Module LatticeBasis

noncomputable section

/-- A source point whose centered coordinate belongs to the common lattice
lies in the divided-radius certificate progression.  The key input is that
the `h`-multiple of the centered coordinate lies in the source-scale box. -/
theorem integerCore_subset_mapped_certificateContraction
    {W integerCore : Finset ℤ} {d ell h : ℕ}
    (A : Fin ell → Finset (LatticePoint d))
    (base : Fin ell)
    (P : BoundingBox.BoundingGAP W d) (hproper : P.progression.Proper)
    (hzero : 0 ∈ W) (hh : 0 < h)
    (cert : Corollary217Certificate
      (Preprocessing.centeredCoordinateAxisBox P.progression h) (A base))
    (hcoreW : integerCore ⊆ W)
    (hcoreLattice : ∀ z ∈ integerCore,
      Preprocessing.centeredIdentification P hproper hzero z ∈
        generatedSublattice (A base)) :
    insert 0 (Stability.integerPoints integerCore) ⊆
      (NoCarryEmbedding.mapGAP
        ((sourceLineEvaluation P.progression).comp
          (sublatticeBasisEvaluation cert.basis))
        (symmetricCoordinateGAP (fun i ↦ cert.radius i / h))).carrier := by
  classical
  intro x hx
  rw [NoCarryEmbedding.mapGAP_carrier]
  rcases Finset.mem_insert.mp hx with rfl | hx
  · refine Finset.mem_image.mpr ⟨0, ?_, ?_⟩
    · exact (symmetricCoordinateGAP_centered
        (fun i ↦ cert.radius i / h)).zero_mem_carrier
    · exact ((sourceLineEvaluation P.progression).comp
        (sublatticeBasisEvaluation cert.basis)).map_zero
  · obtain ⟨z, hz, rfl⟩ := Stability.mem_integerPoints_iff.mp hx
    let y := Preprocessing.centeredIdentification P hproper hzero z
    have hyGamma : y ∈ generatedSublattice (A base) := hcoreLattice z hz
    have hhyBox : (fun j ↦ (h : ℤ) * y j) ∈
        (Preprocessing.centeredCoordinateAxisBox P.progression h).carrier := by
      rw [AxisBox.mem_carrier_iff]
      intro i
      let a := P.progression.widths i - 1
      have hyAbs : |y i| ≤ (a : ℤ) := by
        exact Preprocessing.abs_centeredIdentification_apply_le
          P hproper hzero (hcoreW hz) i
      have hscaledAbs : |(h : ℤ) * y i| ≤ (h * a : ℕ) := by
        calc
          |(h : ℤ) * y i| = (h : ℤ) * |y i| := by
            rw [abs_mul]
            simp
          _ ≤ (h : ℤ) * (a : ℤ) :=
            Int.mul_le_mul_of_nonneg_left hyAbs (by positivity)
          _ = (h * a : ℕ) := by norm_num
      change -((h * a : ℕ) : ℤ) ≤ (h : ℤ) * y i ∧
        (h : ℤ) * y i < -((h * a : ℕ) : ℤ) +
          (((P.progression.dilate (2 * h)).widths i : ℕ) : ℤ)
      have hscaledBounds := abs_le.mp hscaledAbs
      have hwidth : (P.progression.dilate (2 * h)).widths i =
          2 * (h * a) + 1 := by
        simp only [GAP.dilate_widths]
        dsimp only [a]
        ring
      rw [hwidth]
      push_cast
      omega
    have hhyGamma : (fun j ↦ (h : ℤ) * y j) ∈
        generatedSublattice (A base) := by
      change (h : ℤ) • y ∈ generatedSublattice (A base)
      exact (generatedSublattice (A base)).zsmul_mem hyGamma (h : ℤ)
    have hhyCert := cert.box_lattice_subset _ hhyBox hhyGamma
    rw [cert.progression_eq] at hhyCert
    have hyContract : y ∈
        (GAP.basisContraction cert.basis cert.radius h).carrier :=
      GAP.mem_basisContraction_of_smul_mem_centeredBasisGAP
        cert.basis cert.radius hh hyGamma hhyCert
    rw [GAP.basisContraction,
      ← mapGAP_symmetricCoordinateGAP_sublatticeBasisEvaluation,
      NoCarryEmbedding.mapGAP_carrier] at hyContract
    obtain ⟨u, hu, huy⟩ := Finset.mem_image.mp hyContract
    refine Finset.mem_image.mpr ⟨u, hu, ?_⟩
    change sourceLineEvaluation P.progression
        (sublatticeBasisEvaluation cert.basis u) = Stability.integerPoint z
    rw [huy]
    exact sourceLineEvaluation_centeredIdentification P hproper hzero
      (hcoreW hz)

/-- Source-facing scaled specialization of the common-basis map-back.

The DenseBox cover and the no-carry injectivity hypothesis are stated at
the original Corollary 2.17 radius and dilation `k`.  The output progression
uses radii divided by `sourceScale` and dilation `sourceScale * k`. -/
theorem preprocessedReserveCertificate_of_scaled_corollary217Certificate
    {W stableCore integerCore : Finset ℤ}
    {d ell sourceScale s D extraLoss scaleNum scaleDen k : ℕ}
    (A : Fin ell → Finset (LatticePoint d))
    (base : Fin ell)
    (reserve : Fin ell → Finset (LatticePoint 1))
    (hgenerated : ∀ i,
      generatedSublattice (A i) = generatedSublattice (A base))
    (P : BoundingBox.BoundingGAP W d) (hproper : P.progression.Proper)
    (hzero : 0 ∈ W) (hsourceScale : 0 < sourceScale)
    (cert : Corollary217Certificate
      (Preprocessing.centeredCoordinateAxisBox P.progression sourceScale)
      (A base))
    (hd : 0 < d)
    (hwidth : 2 ≤
      (Preprocessing.centeredCoordinateAxisBox
        P.progression sourceScale).minWidth)
    (hcovered : ContainsTranslate
      (heterogeneousSumset (fun i ↦
        sublatticeBasisImage cert.basis (A i)
          (subset_sublattice_of_generatedSublattice_eq (hgenerated i))))
      ((symmetricAxisBox cert.radius).dilate k))
    (hevalFamily : ∀ i,
      (A i).image (sourceLineEvaluation P.progression) ⊆
        GAP.subsetSums (reserve i))
    (hinjective : Set.InjOn (sourceLineEvaluation P.progression)
      (cert.progression.dilate k).carrier)
    (hintegerCore : integerCore ⊆ stableCore)
    (hstableCoreLarge : stableCore.card ≤ integerCore.card + extraLoss)
    (hdisjoint : (Set.univ : Set (Fin ell)).PairwiseDisjoint reserve)
    (hreserveCore : ∀ i,
      reserve i ⊆ Stability.integerPoints integerCore)
    (hreserveSmall : (∑ i, (reserve i).card) ≤ s)
    (hcoreW : integerCore ⊆ W)
    (hcoreLattice : ∀ z ∈ integerCore,
      Preprocessing.centeredIdentification P hproper hzero z ∈
        generatedSublattice (A base))
    (hrank : d ≤ D) (hk : 0 < k)
    (hscaleNum : 0 < scaleNum) (hscaleDen : 0 < scaleDen)
    (hscaleLower : scaleNum * s ≤ scaleDen * (sourceScale * k))
    (hscaleUpper : sourceScale * k ≤ s) :
    Nonempty (PreprocessedReserveCertificate stableCore s D extraLoss
      scaleNum scaleDen) := by
  classical
  let dividedRadius : Fin d → ℕ := fun i ↦ cert.radius i / sourceScale
  let family : Fin ell → Finset (LatticePoint d) := fun i ↦
    sublatticeBasisImage cert.basis (A i)
      (subset_sublattice_of_generatedSublattice_eq (hgenerated i))
  have hradius : ∀ i, 0 < dividedRadius i := by
    intro i
    dsimp only [dividedRadius]
    exact Nat.div_pos
      (cert.sourceScale_le_radius hd hsourceScale hwidth i) hsourceScale
  have hcoveredScaled : ContainsTranslate
      (heterogeneousSumset family)
      ((symmetricAxisBox dividedRadius).dilate (sourceScale * k)) := by
    obtain ⟨u, hu⟩ := hcovered
    refine ⟨u, ?_⟩
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Elementary.mem_translate_iff.mp hx
    apply hu
    apply Elementary.mem_translate_iff.mpr
    refine ⟨y, ?_, rfl⟩
    exact symmetricAxisBox_dilate_mul_subset_dilate
      cert.radius sourceScale k hy
  have hinjectiveScaled : Set.InjOn
      ((sourceLineEvaluation P.progression).comp
        (sublatticeBasisEvaluation cert.basis))
      ((symmetricCoordinateGAP dividedRadius).dilate
        (sourceScale * k)).carrier := by
    have hold := injOn_composite_symmetricCoordinateGAP_dilate
      cert (sourceLineEvaluation P.progression) hinjective
    intro x hx y hy hxy
    apply hold
    · exact symmetricCoordinateGAP_dilate_mul_subset_dilate
        cert.radius sourceScale k hx
    · exact symmetricCoordinateGAP_dilate_mul_subset_dilate
        cert.radius sourceScale k hy
    · exact hxy
  have hcore : insert 0 (Stability.integerPoints integerCore) ⊆
      (NoCarryEmbedding.mapGAP
        ((sourceLineEvaluation P.progression).comp
          (sublatticeBasisEvaluation cert.basis))
        (symmetricCoordinateGAP dividedRadius)).carrier := by
    simpa only [dividedRadius] using
      integerCore_subset_mapped_certificateContraction
        A base P hproper hzero hsourceScale cert hcoreW hcoreLattice
  apply preprocessedReserveCertificate_of_commonBasisDenseBox
    dividedRadius family reserve
    ((sourceLineEvaluation P.progression).comp
      (sublatticeBasisEvaluation cert.basis))
  · exact hradius
  · exact hcoveredScaled
  · intro i
    simpa only [family, image_sublatticeBasisImage_composite] using
      hevalFamily i
  · exact hinjectiveScaled
  · exact hintegerCore
  · exact hstableCoreLarge
  · exact hdisjoint
  · exact hreserveCore
  · exact hreserveSmall
  · exact hcore
  · exact hrank
  · exact Nat.mul_pos hsourceScale hk
  · exact hscaleNum
  · exact hscaleDen
  · exact hscaleLower
  · exact hscaleUpper

end

end Erdos186.CFP

#print axioms
  Erdos186.CFP.integerCore_subset_mapped_certificateContraction
#print axioms
  Erdos186.CFP.preprocessedReserveCertificate_of_scaled_corollary217Certificate
