/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.CoordinateCorollary217Witness
import ErdosProblems.Erdos186.CFP.ProjectedFixedScaleWitness
import ErdosProblems.Erdos186.CFP.Corollary217ScaledMapBack

/-!
# Project a scaled Corollary 2.17 coordinate witness

The dense-box and Corollary 2.17 argument lives in coefficient coordinates.
We assemble the proper fixed-scale witness there, and only then evaluate it
on the source line.  Generic projected properization replaces the stronger
(and quantitatively circular) requirement that source evaluation be
injective on the whole covered dilate.
-/

namespace Erdos186.CFP

open scoped BigOperators
open Module LatticeBasis

noncomputable section

/-- An injective additive map commutes exactly with finite subset sums. -/
theorem image_subsetSums_eq_subsetSums_image
    {d e : ℕ} (f : LatticePoint d →+ LatticePoint e)
    (R : Finset (LatticePoint d)) (hinj : Set.InjOn f R) :
    (GAP.subsetSums R).image f = GAP.subsetSums (R.image f) := by
  apply Finset.Subset.antisymm
  · exact image_subsetSums_subset_subsetSums_image f R hinj
  · intro x hx
    obtain ⟨T, hTR, rfl⟩ := GAP.mem_subsetSums_iff.mp hx
    let U := R.filter fun r ↦ f r ∈ T
    have hUR : U ⊆ R := Finset.filter_subset _ _
    have hUT : U.image f = T := by
      ext y
      constructor
      · intro hy
        obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hy
        exact (Finset.mem_filter.mp hr).2
      · intro hy
        obtain ⟨r, hrR, hfr⟩ := Finset.mem_image.mp (hTR hy)
        apply Finset.mem_image.mpr
        refine ⟨r, Finset.mem_filter.mpr ⟨hrR, ?_⟩, hfr⟩
        simpa only [hfr] using hy
    apply Finset.mem_image.mpr
    refine ⟨U.sum id, GAP.mem_subsetSums_iff.mpr ⟨U, hUR, rfl⟩, ?_⟩
    have hsum : (U.image f).sum id = U.sum (fun r ↦ f r) := by
      rw [Finset.sum_image]
      · rfl
      · exact hinj.mono hUR
    calc
      f (U.sum id) = U.sum (fun r ↦ f r) := by rw [map_sum]; rfl
      _ = (U.image f).sum id := hsum.symm
      _ = T.sum id := by rw [hUT]

/-- Evaluation in an integral lattice basis is globally injective. -/
theorem sublatticeBasisEvaluation_injective
    {d : ℕ} {Gamma : Sublattice d}
    (basis : Basis (Fin d) ℤ Gamma) :
    Function.Injective (sublatticeBasisEvaluation basis) := by
  intro x y hxy
  apply (sublatticeBasisEquiv basis).symm.injective
  apply Gamma.subtype_injective
  exact hxy

/-- Basis-coordinate transport takes subset sums into the subset sums of
the transported reserve. -/
theorem sublatticeBasisImage_subsetSums_subset
    {d : ℕ} {Gamma : Sublattice d}
    (basis : Basis (Fin d) ℤ Gamma)
    (R : Finset (LatticePoint d))
    (hR : (R : Set (LatticePoint d)) ⊆ Gamma)
    (hS : (GAP.subsetSums R : Set (LatticePoint d)) ⊆ Gamma) :
    sublatticeBasisImage basis (GAP.subsetSums R) hS ⊆
      GAP.subsetSums (sublatticeBasisImage basis R hR) := by
  intro x hx
  let eval := sublatticeBasisEvaluation basis
  let R' := sublatticeBasisImage basis R hR
  have hxEval : eval x ∈ GAP.subsetSums R := by
    have himage := image_sublatticeBasisImage_evaluation basis
      (GAP.subsetSums R) hS
    rw [← himage]
    exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
  have hRimage : R'.image eval = R := by
    exact image_sublatticeBasisImage_evaluation basis R hR
  have hsumImage : (GAP.subsetSums R').image eval = GAP.subsetSums R := by
    rw [image_subsetSums_eq_subsetSums_image eval R'
      (sublatticeBasisEvaluation_injective basis).injOn, hRimage]
  rw [← hsumImage] at hxEval
  obtain ⟨y, hy, hyx⟩ := Finset.mem_image.mp hxEval
  have : y = x := sublatticeBasisEvaluation_injective basis hyx
  simpa only [this] using hy

/-- The coefficient copy of a source core is contained in the contracted
Corollary 2.17 coordinate progression. -/
theorem sublatticeBasisImage_sourceCore_subset_certificateContraction
    {W B : Finset ℤ} {d ell h : ℕ}
    (A : Fin ell → Finset (LatticePoint d)) (base : Fin ell)
    (P : BoundingBox.BoundingGAP W d) (hproper : P.progression.Proper)
    (hzero : 0 ∈ W) (hh : 0 < h)
    (cert : Corollary217Certificate
      (Preprocessing.centeredCoordinateAxisBox P.progression h) (A base))
    (hBW : B ⊆ W)
    (hcoreLattice : ∀ z ∈ B,
      Preprocessing.centeredIdentification P hproper hzero z ∈
        generatedSublattice (A base)) :
    let phi := Preprocessing.centeredIdentification P hproper hzero
    let coreImage := B.image phi
    let hcoreGamma : (coreImage : Set (LatticePoint d)) ⊆
        generatedSublattice (A base) := by
      intro y hy
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
      exact hcoreLattice z hz
    insert 0 (sublatticeBasisImage cert.basis coreImage hcoreGamma) ⊆
      (symmetricCoordinateGAP (fun i ↦ cert.radius i / h)).carrier := by
  classical
  dsimp only
  intro x hx
  rcases Finset.mem_insert.mp hx with rfl | hx
  · exact (symmetricCoordinateGAP_centered
      (fun i ↦ cert.radius i / h)).zero_mem_carrier
  · let phi := Preprocessing.centeredIdentification P hproper hzero
    let coreImage := B.image phi
    have hcoreGamma : (coreImage : Set (LatticePoint d)) ⊆
        generatedSublattice (A base) := by
      intro y hy
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
      exact hcoreLattice z hz
    have hxEval : sublatticeBasisEvaluation cert.basis x ∈ coreImage := by
      rw [← image_sublatticeBasisImage_evaluation cert.basis coreImage
        hcoreGamma]
      exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
    obtain ⟨z, hz, hzx⟩ := Finset.mem_image.mp hxEval
    let v := Preprocessing.centeredIdentification P hproper hzero z
    have hvGamma : v ∈ generatedSublattice (A base) := hcoreLattice z hz
    have hhvBox : (fun j ↦ (h : ℤ) * v j) ∈
        (Preprocessing.centeredCoordinateAxisBox P.progression h).carrier := by
      rw [AxisBox.mem_carrier_iff]
      intro i
      let a := P.progression.widths i - 1
      have hvAbs : |v i| ≤ (a : ℤ) := by
        exact Preprocessing.abs_centeredIdentification_apply_le
          P hproper hzero (hBW hz) i
      have hscaledAbs : |(h : ℤ) * v i| ≤ (h * a : ℕ) := by
        calc
          |(h : ℤ) * v i| = (h : ℤ) * |v i| := by
            rw [abs_mul]
            simp
          _ ≤ (h : ℤ) * (a : ℤ) :=
            Int.mul_le_mul_of_nonneg_left hvAbs (by positivity)
          _ = (h * a : ℕ) := by norm_num
      change -((h * a : ℕ) : ℤ) ≤ (h : ℤ) * v i ∧
        (h : ℤ) * v i < -((h * a : ℕ) : ℤ) +
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
    have hhvGamma : (fun j ↦ (h : ℤ) * v j) ∈
        generatedSublattice (A base) := by
      change (h : ℤ) • v ∈ generatedSublattice (A base)
      exact (generatedSublattice (A base)).zsmul_mem hvGamma (h : ℤ)
    have hhvCert := cert.box_lattice_subset _ hhvBox hhvGamma
    rw [cert.progression_eq] at hhvCert
    have hvContract : v ∈
        (GAP.basisContraction cert.basis cert.radius h).carrier :=
      GAP.mem_basisContraction_of_smul_mem_centeredBasisGAP
        cert.basis cert.radius hh hvGamma hhvCert
    rw [GAP.basisContraction,
      ← mapGAP_symmetricCoordinateGAP_sublatticeBasisEvaluation,
      NoCarryEmbedding.mapGAP_carrier] at hvContract
    obtain ⟨y, hy, hyeval⟩ := Finset.mem_image.mp hvContract
    have hbasis : sublatticeBasisEvaluation cert.basis y =
        sublatticeBasisEvaluation cert.basis x := hyeval.trans hzx
    have hyx : y = x := sublatticeBasisEvaluation_injective cert.basis hbasis
    simpa only [← hyx] using hy

/-- Assemble the contracted witness in coefficient space and project it to
the source line using Lemma 2.27.  No injectivity on a dilated progression
is assumed. -/
theorem exists_projectedFixedScaleWitness_of_scaled_corollary217Certificate
    {W B : Finset ℤ}
    {d ell sourceScale s D scaleDen k : ℕ}
    (coordinateReserve : Fin ell → Finset (LatticePoint d))
    (base : Fin ell)
    (hgenerated : ∀ i, generatedSublattice (coordinateReserve i) =
      generatedSublattice (coordinateReserve base))
    (P : BoundingBox.BoundingGAP W d) (hproper : P.progression.Proper)
    (hzero : 0 ∈ W) (hsourceScale : 0 < sourceScale)
    (cert : Corollary217Certificate
      (Preprocessing.centeredCoordinateAxisBox P.progression sourceScale)
      (GAP.subsetSums (coordinateReserve base)))
    (hd : 0 < d)
    (hwidth : 2 ≤
      (Preprocessing.centeredCoordinateAxisBox
        P.progression sourceScale).minWidth)
    (hcovered : ContainsTranslate
      (heterogeneousSumset (fun i ↦
        sublatticeBasisImage cert.basis
          (GAP.subsetSums (coordinateReserve i))
          (subset_sublattice_of_generatedSublattice_eq (by
            rw [generatedSublattice_subsetSums,
              generatedSublattice_subsetSums, hgenerated i]))))
      ((symmetricAxisBox cert.radius).dilate k))
    (hBW : B ⊆ W)
    (hreserveCore : ∀ i, coordinateReserve i ⊆
      B.image (Preprocessing.centeredIdentification P hproper hzero))
    (hcoreLattice : ∀ z ∈ B,
      Preprocessing.centeredIdentification P hproper hzero z ∈
        generatedSublattice (coordinateReserve base))
    (hdisjoint : (Set.univ : Set (Fin ell)).PairwiseDisjoint coordinateReserve)
    (hreserveSmall : (∑ i, (coordinateReserve i).card) ≤ s)
    (hrank : d ≤ D) (hk : 0 < k) (hscaleDen : 0 < scaleDen)
    (hscaleLower : s ≤ scaleDen * (sourceScale * k))
    (hscaleUpper : sourceScale * k ≤ s)
    (hproject : ProjectedProperization.projectionFactor D ≤
      sourceScale * k) :
    ∃ k' : ℕ, Nonempty (FixedScaleWitness
      (Stability.integerPoints B) s D k' 0 1
      (scaleDen * ProjectedProperization.projectionFactor D)) := by
  classical
  let phi := Preprocessing.centeredIdentification P hproper hzero
  let Gamma := generatedSublattice (GAP.subsetSums (coordinateReserve base))
  have hreserveGamma : ∀ i, (coordinateReserve i : Set (LatticePoint d)) ⊆
      Gamma := by
    intro i x hx
    simp only [Gamma, generatedSublattice_subsetSums]
    rw [← hgenerated i]
    exact subset_generatedSublattice _ hx
  have hsumGamma : ∀ i,
      (GAP.subsetSums (coordinateReserve i) : Set (LatticePoint d)) ⊆
        Gamma := by
    intro i
    apply subset_sublattice_of_generatedSublattice_eq
    simp only [Gamma, generatedSublattice_subsetSums]
    exact hgenerated i
  let reserve : Fin ell → Finset (LatticePoint d) := fun i ↦
    sublatticeBasisImage cert.basis (coordinateReserve i) (hreserveGamma i)
  let family : Fin ell → Finset (LatticePoint d) := fun i ↦
    sublatticeBasisImage cert.basis (GAP.subsetSums (coordinateReserve i))
      (hsumGamma i)
  let coreImage := B.image phi
  have hcoreGamma : (coreImage : Set (LatticePoint d)) ⊆ Gamma := by
    intro y hy
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
    simp only [Gamma, generatedSublattice_subsetSums]
    exact hcoreLattice z hz
  let H := sublatticeBasisImage cert.basis coreImage hcoreGamma
  have hfamilyReserve : ∀ i, family i ⊆ GAP.subsetSums (reserve i) := by
    intro i
    exact sublatticeBasisImage_subsetSums_subset cert.basis
      (coordinateReserve i) (hreserveGamma i) (hsumGamma i)
  have hreserveH : ∀ i, reserve i ⊆ H := by
    intro i x hx
    have hxEval : sublatticeBasisEvaluation cert.basis x ∈
        coordinateReserve i := by
      rw [← image_sublatticeBasisImage_evaluation cert.basis
        (coordinateReserve i) (hreserveGamma i)]
      exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
    have hxCore : sublatticeBasisEvaluation cert.basis x ∈ coreImage :=
      hreserveCore i hxEval
    rw [← image_sublatticeBasisImage_evaluation cert.basis coreImage
      hcoreGamma] at hxCore
    obtain ⟨y, hy, hyx⟩ := Finset.mem_image.mp hxCore
    have : y = x := sublatticeBasisEvaluation_injective cert.basis hyx
    simpa only [this] using hy
  have hreserveDisjoint :
      (Set.univ : Set (Fin ell)).PairwiseDisjoint reserve := by
    intro i _hi j _hj hij
    change Disjoint (reserve i) (reserve j)
    rw [Finset.disjoint_left]
    intro x hxi hxj
    have hxi' : sublatticeBasisEvaluation cert.basis x ∈
        coordinateReserve i := by
      rw [← image_sublatticeBasisImage_evaluation cert.basis
        (coordinateReserve i) (hreserveGamma i)]
      exact Finset.mem_image.mpr ⟨x, hxi, rfl⟩
    have hxj' : sublatticeBasisEvaluation cert.basis x ∈
        coordinateReserve j := by
      rw [← image_sublatticeBasisImage_evaluation cert.basis
        (coordinateReserve j) (hreserveGamma j)]
      exact Finset.mem_image.mpr ⟨x, hxj, rfl⟩
    exact Finset.disjoint_left.mp (hdisjoint trivial trivial hij) hxi' hxj'
  have hreserveCard : (∑ i, (reserve i).card) ≤ s := by
    simpa only [reserve, card_sublatticeBasisImage] using hreserveSmall
  let dividedRadius : Fin d → ℕ := fun i ↦ cert.radius i / sourceScale
  have hradius : ∀ i, 0 < dividedRadius i := by
    intro i
    exact Nat.div_pos
      (cert.sourceScale_le_radius hd hsourceScale hwidth i) hsourceScale
  have hcoveredScaled : ContainsTranslate (heterogeneousSumset family)
      ((symmetricAxisBox dividedRadius).dilate (sourceScale * k)) := by
    obtain ⟨u, hu⟩ := hcovered
    refine ⟨u, ?_⟩
    intro x hx
    apply hu
    obtain ⟨y, hy, rfl⟩ := Elementary.mem_translate_iff.mp hx
    apply Elementary.mem_translate_iff.mpr
    refine ⟨y, ?_, rfl⟩
    exact symmetricAxisBox_dilate_mul_subset_dilate
      cert.radius sourceScale k hy
  have hcoreProgression : insert 0 H ⊆
      (symmetricCoordinateGAP dividedRadius).carrier := by
    have hcoreLattice' : ∀ z ∈ B,
        Preprocessing.centeredIdentification P hproper hzero z ∈
          generatedSublattice (GAP.subsetSums (coordinateReserve base)) := by
      intro z hz
      rw [generatedSublattice_subsetSums]
      exact hcoreLattice z hz
    simpa only [H, coreImage, phi, dividedRadius, Gamma,
      generatedSublattice_subsetSums] using
      sublatticeBasisImage_sourceCore_subset_certificateContraction
        (fun i ↦ GAP.subsetSums (coordinateReserve i)) base P hproper hzero
        hsourceScale cert hBW hcoreLattice'
  obtain ⟨W⟩ := exists_coordinateFixedScaleWitness_of_commonBasisDenseBox
    (loss := 0) dividedRadius family reserve hradius hcoveredScaled hfamilyReserve
      hreserveDisjoint (Finset.Subset.rfl) hreserveH (by omega) hreserveCard
      hcoreProgression hrank (Nat.mul_pos hsourceScale hk) Nat.zero_lt_one
      hscaleDen (by simpa only [one_mul] using hscaleLower) hscaleUpper
  let f := (sourceLineEvaluation P.progression).comp
    (sublatticeBasisEvaluation cert.basis)
  have hinj : Set.InjOn f H := by
    intro x hx y hy hxy
    apply sublatticeBasisEvaluation_injective cert.basis
    apply ProjectedProperization.sourceLineEvaluation_injOn_image_centeredIdentification
        P hproper hzero hBW
    · change sublatticeBasisEvaluation cert.basis x ∈ coreImage
      rw [← image_sublatticeBasisImage_evaluation cert.basis coreImage
        hcoreGamma]
      exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
    · change sublatticeBasisEvaluation cert.basis y ∈ coreImage
      rw [← image_sublatticeBasisImage_evaluation cert.basis coreImage
        hcoreGamma]
      exact Finset.mem_image.mpr ⟨y, hy, rfl⟩
    · exact hxy
  obtain ⟨k', W'⟩ :=
    ProjectedProperization.exists_projectedFixedScaleWitness f W hinj hproject
  refine ⟨k', ?_⟩
  have himage : H.image f = Stability.integerPoints B := by
    calc
      H.image f = coreImage.image (sourceLineEvaluation P.progression) := by
        exact image_sublatticeBasisImage_composite cert.basis coreImage
          hcoreGamma (sourceLineEvaluation P.progression)
      _ = Stability.integerPoints B := by
        exact ProjectedProperization.image_sourceLineEvaluation_image_centeredIdentification
          P hproper hzero hBW
  simpa only [himage] using W'

end

end Erdos186.CFP

#print axioms Erdos186.CFP.image_subsetSums_eq_subsetSums_image
#print axioms
  Erdos186.CFP.exists_projectedFixedScaleWitness_of_scaled_corollary217Certificate
