/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.Corollary217FamilyTransport
import ErdosProblems.Erdos186.CFP.Corollary217EvaluationInjectivity
import ErdosProblems.Erdos186.CFP.NoCarryEmbedding
import ErdosProblems.Erdos186.CFP.PreprocessedWitness

/-!
# Mapping the common Corollary 2.17 box back to the source line

The common-basis dense-box argument naturally lives in an integral
coefficient space.  This file supplies the finite, deterministic map-back
step.  The only hypothesis that is deliberately left visible is injectivity
of the source evaluation on the covered dilate; this is precisely the
no-carry/properness input supplied by the outer scale hierarchy.
-/

namespace Erdos186.CFP

open scoped BigOperators
open Module LatticeBasis

noncomputable section

/-- The canonical centered GAP whose carrier is the symmetric axis box. -/
def symmetricCoordinateGAP {d : ℕ} (radius : Fin d → ℕ) : GAP d d where
  offset := fun i ↦ -(radius i : ℤ)
  steps := fun i j ↦ if i = j then 1 else 0
  widths := fun i ↦ 2 * radius i + 1
  width_pos := fun _ ↦ Nat.zero_lt_succ _

@[simp]
theorem symmetricCoordinateGAP_widths {d : ℕ} (radius : Fin d → ℕ)
    (i : Fin d) :
    (symmetricCoordinateGAP radius).widths i = 2 * radius i + 1 := rfl

theorem symmetricCoordinateGAP_coordPoint {d : ℕ}
    (radius : Fin d → ℕ) (n : (symmetricCoordinateGAP radius).Coord) :
    (symmetricCoordinateGAP radius).coordPoint n =
      fun i ↦ ((n i : ℕ) : ℤ) - (radius i : ℤ) := by
  funext j
  simp [GAP.coordPoint, symmetricCoordinateGAP]
  ring

@[simp]
theorem symmetricCoordinateGAP_carrier {d : ℕ} (radius : Fin d → ℕ) :
    (symmetricCoordinateGAP radius).carrier =
      (symmetricAxisBox radius).carrier := by
  classical
  ext x
  rw [GAP.mem_carrier_iff, mem_symmetricAxisBox_iff]
  constructor
  · rintro ⟨n, rfl⟩ i
    rw [symmetricCoordinateGAP_coordPoint]
    have hn := (n i).isLt
    simp only [symmetricCoordinateGAP_widths] at hn
    rw [abs_le]
    push_cast at hn ⊢
    omega
  · intro hx
    let n : (symmetricCoordinateGAP radius).Coord := fun i ↦
      ⟨(x i + (radius i : ℤ)).toNat, by
        have hi := abs_le.mp (hx i)
        have hnonneg : 0 ≤ x i + (radius i : ℤ) := by omega
        rw [Int.toNat_lt hnonneg]
        simpa only [symmetricCoordinateGAP_widths] using
          (show x i + (radius i : ℤ) < (2 * radius i + 1 : ℕ) by
            push_cast
            omega)⟩
    refine ⟨n, ?_⟩
    rw [symmetricCoordinateGAP_coordPoint]
    funext i
    dsimp only [n]
    rw [Int.toNat_of_nonneg]
    · ring
    · exact (by have := abs_le.mp (hx i); omega)

/-- The canonical coordinate presentation is proper. -/
theorem symmetricCoordinateGAP_proper {d : ℕ} (radius : Fin d → ℕ) :
    (symmetricCoordinateGAP radius).Proper := by
  intro n m hnm
  rw [symmetricCoordinateGAP_coordPoint,
    symmetricCoordinateGAP_coordPoint] at hnm
  funext i
  apply Fin.ext
  have hi := congrFun hnm i
  omega

/-- The canonical coordinate presentation is centered at zero. -/
theorem symmetricCoordinateGAP_centered {d : ℕ} (radius : Fin d → ℕ) :
    (symmetricCoordinateGAP radius).Centered radius := by
  constructor
  · rfl
  · funext j
    simp [symmetricCoordinateGAP]

theorem symmetricCoordinateGAP_homogeneous {d : ℕ}
    (radius : Fin d → ℕ) :
    (symmetricCoordinateGAP radius).Homogeneous :=
  (symmetricCoordinateGAP_centered radius).homogeneous

theorem symmetricCoordinateGAP_nondegenerate {d : ℕ}
    {radius : Fin d → ℕ} (hradius : ∀ i, 0 < radius i) :
    (symmetricCoordinateGAP radius).Nondegenerate := by
  intro i
  change 2 ≤ 2 * radius i + 1
  have hi := hradius i
  omega

/-- The origin-based axis-box dilation is the translate of the centered GAP
dilation by its radius vector. -/
@[simp]
theorem symmetricCoordinateGAP_dilate_carrier {d k : ℕ}
    (radius : Fin d → ℕ) :
    Elementary.translate (fun i ↦ (k * radius i : ℕ))
        ((symmetricCoordinateGAP radius).dilate k).carrier =
      ((symmetricAxisBox radius).dilate k).carrier := by
  classical
  ext x
  rw [Elementary.mem_translate_iff, AxisBox.mem_carrier_iff]
  constructor
  · rintro ⟨y, hy, rfl⟩ i
    obtain ⟨n, rfl⟩ := GAP.mem_carrier_iff.mp hy
    have hn := (n i).isLt
    simp only [GAP.dilate_widths, symmetricCoordinateGAP_widths] at hn
    rw [((symmetricCoordinateGAP_centered radius).dilate k).coordPoint_eq]
    simp only [GAP.dilate_steps, symmetricCoordinateGAP]
    rw [AxisBox.dilate_lower, AxisBox.dilate_width]
    simp only [symmetricAxisBox, Pi.zero_apply, Pi.add_apply, zero_add]
    have hcoord :
        (∑ j, (((n j : ℕ) : ℤ) - (k * radius j : ℕ)) *
          (if j = i then 1 else 0)) =
          ((n i : ℕ) : ℤ) - (k * radius i : ℕ) := by simp
    rw [hcoord]
    have hwidth : 2 * radius i + 1 - 1 = 2 * radius i := by omega
    have hcancel :
        (k * radius i : ℕ) +
            (((n i : ℕ) : ℤ) - (k * radius i : ℕ)) =
          ((n i : ℕ) : ℤ) := by
      push_cast
      ring
    rw [hcancel]
    constructor
    · exact_mod_cast Nat.zero_le (n i : ℕ)
    · exact_mod_cast (show (n i : ℕ) < k * (2 * radius i) + 1 by
        simpa only [hwidth] using hn)
  · intro hx
    let n : ((symmetricCoordinateGAP radius).dilate k).Coord := fun i ↦
      ⟨(x i).toNat, by
        have hi := hx i
        rw [AxisBox.dilate_lower, AxisBox.dilate_width] at hi
        simp only [symmetricAxisBox, Pi.zero_apply, zero_add] at hi
        simp only [GAP.dilate_widths, symmetricCoordinateGAP_widths]
        rw [Int.toNat_lt hi.1]
        simpa using hi.2⟩
    refine ⟨_, GAP.mem_carrier_iff.mpr ⟨n, rfl⟩, ?_⟩
    rw [((symmetricCoordinateGAP_centered radius).dilate k).coordPoint_eq]
    funext i
    simp only [Pi.add_apply, GAP.dilate_steps, symmetricCoordinateGAP]
    have hsum :
        (∑ j, (((n j : ℕ) : ℤ) - (k * radius j : ℕ)) *
          (if j = i then 1 else 0)) =
          ((n i : ℕ) : ℤ) - (k * radius i : ℕ) := by simp
    rw [hsum]
    dsimp only [n]
    rw [Int.toNat_of_nonneg]
    · ring
    · have hi := hx i
      rw [AxisBox.dilate_lower, AxisBox.dilate_width] at hi
      simpa only [symmetricAxisBox, Pi.zero_apply, zero_add] using hi.1

/-- The coordinate box is proper at every dilation. -/
theorem symmetricCoordinateGAP_dilate_proper {d k : ℕ}
    (radius : Fin d → ℕ) :
    ((symmetricCoordinateGAP radius).dilate k).Proper := by
  intro n m hnm
  rw [((symmetricCoordinateGAP_centered radius).dilate k).coordPoint_eq,
    ((symmetricCoordinateGAP_centered radius).dilate k).coordPoint_eq] at hnm
  funext i
  apply Fin.ext
  have hi := congrFun hnm i
  simp only [GAP.dilate_steps, symmetricCoordinateGAP] at hi
  simpa using hi

/-- The image of a coordinate vector is the corresponding integral
combination of the mapped coordinate directions. -/
theorem map_eq_sum_symmetricCoordinateGAP_steps {d e : ℕ}
    (f : LatticePoint d →+ LatticePoint e) (radius : Fin d → ℕ)
    (x : LatticePoint d) :
    f x = fun j ↦ ∑ i, x i * f ((symmetricCoordinateGAP radius).steps i) j := by
  have hx : x = ∑ i, x i • (symmetricCoordinateGAP radius).steps i := by
    funext j
    simp [symmetricCoordinateGAP]
  calc
    f x = f (∑ i, x i • (symmetricCoordinateGAP radius).steps i) :=
      congrArg f hx
    _ = ∑ i, x i • f ((symmetricCoordinateGAP radius).steps i) := by
      rw [map_sum]
      simp only [map_zsmul]
    _ = fun j ↦ ∑ i, x i *
        f ((symmetricCoordinateGAP radius).steps i) j := by
      funext j
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

/-- Mapping a subset of every summand set maps their heterogeneous sumset
into the heterogeneous sumset of the targets. -/
theorem map_heterogeneousSumset_subset
    {d e ell : ℕ} (f : LatticePoint d →+ LatticePoint e)
    (A : Fin ell → Finset (LatticePoint d))
    (T : Fin ell → Finset (LatticePoint e))
    (hAT : ∀ i, (A i).image f ⊆ T i) :
    (heterogeneousSumset A).image f ⊆ heterogeneousSumset T := by
  rw [image_heterogeneousSumset_addMonoidHom]
  exact heterogeneousSumset_mono hAT

/-- An injective additive map carries subset sums into the subset sums of
the finite image. -/
theorem image_subsetSums_subset_subsetSums_image
    {d e : ℕ} (f : LatticePoint d →+ LatticePoint e)
    (R : Finset (LatticePoint d)) (hinj : Set.InjOn f R) :
    (GAP.subsetSums R).image f ⊆ GAP.subsetSums (R.image f) := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
  obtain ⟨T, hTR, rfl⟩ := GAP.mem_subsetSums_iff.mp hx
  apply GAP.mem_subsetSums_iff.mpr
  refine ⟨T.image f, Finset.image_mono f hTR, ?_⟩
  rw [Finset.sum_image]
  · simp
  · intro a ha b hb hab
    exact hinj (hTR ha) (hTR hb) hab

/-- Step evaluation bundled with the standard embedding of integers into
the one-dimensional lattice. -/
def sourceLineEvaluation {d : ℕ} (P : GAP 1 d) :
    LatticePoint d →+ LatticePoint 1 where
  toFun x := Stability.integerPoint (Preprocessing.stepEvaluation P x)
  map_zero' := by
    funext i
    simp [Stability.integerPoint]
  map_add' x y := by
    funext i
    simp [Stability.integerPoint]

@[simp]
theorem sourceLineEvaluation_apply {d : ℕ} (P : GAP 1 d)
    (x : LatticePoint d) :
    sourceLineEvaluation P x =
      Stability.integerPoint (Preprocessing.stepEvaluation P x) := rfl

/-- The source-line evaluation recovers every integer from its centered
bounding-box coordinate. -/
theorem sourceLineEvaluation_centeredIdentification
    {W : Finset ℤ} {d : ℕ}
    (P : BoundingBox.BoundingGAP W d) (hproper : P.progression.Proper)
    (hzero : 0 ∈ W) {z : ℤ} (hz : z ∈ W) :
    sourceLineEvaluation P.progression
        (Preprocessing.centeredIdentification P hproper hzero z) =
      Stability.integerPoint z := by
  rw [sourceLineEvaluation_apply,
    Preprocessing.stepEvaluation_centeredIdentification P hproper hzero hz]

/-- Injectivity of step evaluation is unchanged by the standard embedding
into the one-dimensional lattice. -/
theorem sourceLineEvaluation_injOn {d : ℕ} (P : GAP 1 d)
    {S : Set (LatticePoint d)}
    (hinj : Set.InjOn (Preprocessing.stepEvaluation P) S) :
    Set.InjOn (sourceLineEvaluation P) S := by
  intro x hx y hy hxy
  apply hinj hx hy
  apply Stability.integerPoint_injective
  exact hxy

/-- The coordinate reserve maps exactly back to its one-dimensional source
reserve. -/
theorem image_centeredCoordinateReserve_sourceLineEvaluation
    {W S : Finset ℤ} {d : ℕ} (hSW : S ⊆ W)
    (P : BoundingBox.BoundingGAP W d) (hproper : P.progression.Proper)
    (hzero : 0 ∈ W) :
    (S.image (Preprocessing.centeredIdentification P hproper hzero)).image
        (sourceLineEvaluation P.progression) =
      Stability.integerPoints S := by
  classical
  rw [Finset.image_image]
  apply Finset.image_congr
  intro z hz
  exact sourceLineEvaluation_centeredIdentification P hproper hzero (hSW hz)

/-- Consequently, all centered coordinate subset sums map into the lattice
subset sums of the original integer reserve. -/
theorem image_centeredCoordinateSubsetSums_subset_sourceSubsetSums
    {W S : Finset ℤ} {d : ℕ} (hSW : S ⊆ W)
    (P : BoundingBox.BoundingGAP W d) (hproper : P.progression.Proper)
    (hzero : 0 ∈ W) :
    (GAP.subsetSums
      (S.image (Preprocessing.centeredIdentification P hproper hzero))).image
        (sourceLineEvaluation P.progression) ⊆
      GAP.subsetSums (Stability.integerPoints S) := by
  let phi := Preprocessing.centeredIdentification P hproper hzero
  let eval := sourceLineEvaluation P.progression
  have hinj : Set.InjOn eval (S.image phi) := by
    intro x hx y hy hxy
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
    have hab : a = b := by
      apply Stability.integerPoint_injective
      simpa only [eval, phi,
        sourceLineEvaluation_centeredIdentification P hproper hzero (hSW ha),
        sourceLineEvaluation_centeredIdentification P hproper hzero (hSW hb)]
        using hxy
    subst b
    rfl
  have hmap := image_subsetSums_subset_subsetSums_image eval (S.image phi) hinj
  simpa only [eval, phi,
    image_centeredCoordinateReserve_sourceLineEvaluation hSW P hproper hzero]
    using hmap

/-- Source-facing specialization for a completed random-greedy reserve in
the centered canonical minimal-box coordinates. -/
theorem image_centeredMinimalCompletedSubsetSums_subset_completedReserveSubsetSums
    {W A : Finset ℤ} {d q steps : ℕ} {relevant : Finset ℕ}
    (hproper : Stability.RelevantBoxesProper W relevant)
    (hd : d ∈ relevant) (hzero : 0 ∈ W)
    (c : {a // a ∈ A} → Fin (q + 1))
    (completion : Fin (q + 1) → Finset ℤ)
    (hcompletedSubset : ∀ i,
      RandomPartition.completedColorSet A c steps completion i ⊆ W)
    (i : Fin (q + 1)) :
    (GAP.subsetSums
      (RandomPartition.coordinateCompletedColorReserve A c steps completion
        (Stability.centeredMinimalIdentificationFamily hproper d) i)).image
      (sourceLineEvaluation
        (BoundingBox.dBoundingBox W d (hproper.positive hd)).progression) ⊆
    GAP.subsetSums
      (RandomPartition.completedGreedyColorReserve A c steps completion i) := by
  let P := BoundingBox.dBoundingBox W d (hproper.positive hd)
  have hphi := Preprocessing.centeredIdentification_eq_centeredMinimalIdentificationFamily
    hproper hd hzero
  have hmap := image_centeredCoordinateSubsetSums_subset_sourceSubsetSums
    (hcompletedSubset i) P (hproper.proper hd) hzero
  rw [hphi] at hmap
  simpa only [P, RandomPartition.coordinateCompletedColorReserve,
    RandomPartition.completedGreedyColorReserve] using hmap

@[simp]
theorem sublatticeBasisEvaluation_symmetricCoordinateGAP_step
    {d : ℕ} {Gamma : Sublattice d}
    (basis : Basis (Fin d) ℤ Gamma) (radius : Fin d → ℕ) (i : Fin d) :
    sublatticeBasisEvaluation basis
        ((symmetricCoordinateGAP radius).steps i) =
      ((basis i : Gamma) : LatticePoint d) := by
  funext j
  simp [sublatticeBasisEvaluation, sublatticeBasisEquiv,
    symmetricCoordinateGAP]

/-- Evaluating the canonical coordinate GAP in a lattice basis recovers the
centered basis GAP used by Corollary 2.17. -/
theorem mapGAP_symmetricCoordinateGAP_sublatticeBasisEvaluation
    {d : ℕ} {Gamma : Sublattice d}
    (basis : Basis (Fin d) ℤ Gamma) (radius : Fin d → ℕ) :
    NoCarryEmbedding.mapGAP (sublatticeBasisEvaluation basis)
        (symmetricCoordinateGAP radius) =
      AdaptedHNF.centeredBasisGAP basis radius := by
  rw [GAP.mk.injEq]
  refine ⟨?_, ?_, rfl⟩
  · change sublatticeBasisEvaluation basis (fun i ↦ -(radius i : ℤ)) =
      fun j ↦ -∑ i, (radius i : ℤ) *
        (((basis i : Gamma) : LatticePoint d) j)
    rw [map_eq_sum_symmetricCoordinateGAP_steps
      (sublatticeBasisEvaluation basis) radius]
    funext j
    simp only [neg_mul, Finset.sum_neg_distrib,
      sublatticeBasisEvaluation_symmetricCoordinateGAP_step]
  · funext i j
    change sublatticeBasisEvaluation basis
        ((symmetricCoordinateGAP radius).steps i) j =
      (((basis i : Gamma) : LatticePoint d) j)
    exact congrFun
      (sublatticeBasisEvaluation_symmetricCoordinateGAP_step
        basis radius i) j

/-- The common-basis coefficient GAP maps exactly to the progression
selected in a Corollary 2.17 certificate. -/
theorem mapGAP_symmetricCoordinateGAP_eq_certificateProgression
    {d : ℕ} {Q : AxisBox d} {S : Finset (LatticePoint d)}
    (cert : Corollary217Certificate Q S) :
    NoCarryEmbedding.mapGAP (sublatticeBasisEvaluation cert.basis)
        (symmetricCoordinateGAP cert.radius) = cert.progression := by
  rw [cert.progression_eq]
  exact mapGAP_symmetricCoordinateGAP_sublatticeBasisEvaluation
    cert.basis cert.radius

/-- Injectivity of an ambient source evaluation on the certificate dilate
pulls back to injectivity of the composite map in common-basis coordinates. -/
theorem injOn_composite_symmetricCoordinateGAP_dilate
    {d e k : ℕ} {Q : AxisBox d} {S : Finset (LatticePoint d)}
    (cert : Corollary217Certificate Q S)
    (eval : LatticePoint d →+ LatticePoint e)
    (hinj : Set.InjOn eval (cert.progression.dilate k).carrier) :
    Set.InjOn (eval.comp (sublatticeBasisEvaluation cert.basis))
      ((symmetricCoordinateGAP cert.radius).dilate k).carrier := by
  intro x hx y hy hxy
  have hmapEq := mapGAP_symmetricCoordinateGAP_eq_certificateProgression cert
  have hx' : sublatticeBasisEvaluation cert.basis x ∈
      (cert.progression.dilate k).carrier := by
    rw [← hmapEq, ← NoCarryEmbedding.mapGAP_dilate,
      NoCarryEmbedding.mapGAP_carrier]
    exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
  have hy' : sublatticeBasisEvaluation cert.basis y ∈
      (cert.progression.dilate k).carrier := by
    rw [← hmapEq, ← NoCarryEmbedding.mapGAP_dilate,
      NoCarryEmbedding.mapGAP_carrier]
    exact Finset.mem_image.mpr ⟨y, hy, rfl⟩
  have heq : sublatticeBasisEvaluation cert.basis x =
      sublatticeBasisEvaluation cert.basis y := hinj hx' hy' hxy
  apply (sublatticeBasisEquiv cert.basis).symm.injective
  apply (generatedSublattice S).subtype_injective
  exact heq

/-- Source core points contained in the common coordinate box and common
generated lattice map into the one-dimensional certificate progression. -/
theorem integerCore_subset_mapped_certificateProgression
    {W integerCore : Finset ℤ} {d ell : ℕ}
    {Q : AxisBox d} (A : Fin ell → Finset (LatticePoint d))
    (base : Fin ell) (cert : Corollary217Certificate Q (A base))
    (P : BoundingBox.BoundingGAP W d) (hproper : P.progression.Proper)
    (hzero : 0 ∈ W) (hcoreW : integerCore ⊆ W)
    (hcoreBox : ∀ z ∈ integerCore,
      Preprocessing.centeredIdentification P hproper hzero z ∈ Q.carrier)
    (hcoreLattice : ∀ z ∈ integerCore,
      Preprocessing.centeredIdentification P hproper hzero z ∈
        generatedSublattice (A base)) :
    insert 0 (Stability.integerPoints integerCore) ⊆
      (NoCarryEmbedding.mapGAP
        ((sourceLineEvaluation P.progression).comp
          (sublatticeBasisEvaluation cert.basis))
        (symmetricCoordinateGAP cert.radius)).carrier := by
  classical
  intro x hx
  rw [NoCarryEmbedding.mapGAP_carrier]
  rcases Finset.mem_insert.mp hx with rfl | hx
  · refine Finset.mem_image.mpr ⟨0, ?_, ?_⟩
    · exact (symmetricCoordinateGAP_centered cert.radius).zero_mem_carrier
    · exact ((sourceLineEvaluation P.progression).comp
        (sublatticeBasisEvaluation cert.basis)).map_zero
  · obtain ⟨z, hz, rfl⟩ := Stability.mem_integerPoints_iff.mp hx
    have hzCert : Preprocessing.centeredIdentification P hproper hzero z ∈
        cert.progression.carrier :=
      cert.box_lattice_subset _ (hcoreBox z hz) (hcoreLattice z hz)
    rw [← mapGAP_symmetricCoordinateGAP_eq_certificateProgression cert,
      NoCarryEmbedding.mapGAP_carrier] at hzCert
    obtain ⟨y, hy, hyeval⟩ := Finset.mem_image.mp hzCert
    refine Finset.mem_image.mpr ⟨y, hy, ?_⟩
    change sourceLineEvaluation P.progression
        (sublatticeBasisEvaluation cert.basis y) = Stability.integerPoint z
    rw [hyeval]
    exact sourceLineEvaluation_centeredIdentification P hproper hzero
      (hcoreW hz)

/-- Evaluating a basis-coordinate image through a further additive map is
the same finite image as evaluating the original ambient set. -/
@[simp]
theorem image_sublatticeBasisImage_composite
    {d e : ℕ} {Gamma : Sublattice d}
    (basis : Basis (Fin d) ℤ Gamma)
    (S : Finset (LatticePoint d))
    (hS : (S : Set (LatticePoint d)) ⊆ Gamma)
    (eval : LatticePoint d →+ LatticePoint e) :
    (sublatticeBasisImage basis S hS).image
        (eval.comp (sublatticeBasisEvaluation basis)) =
      S.image eval := by
  calc
    (sublatticeBasisImage basis S hS).image
        (eval.comp (sublatticeBasisEvaluation basis)) =
        ((sublatticeBasisImage basis S hS).image
          (sublatticeBasisEvaluation basis)).image eval := by
      rw [Finset.image_image]
      rfl
    _ = S.image eval := by
      rw [image_sublatticeBasisImage_evaluation]

/-- Deterministic map-back from a common-basis DenseBox cover to the exact
post-preprocessing certificate.  The source evaluation need only be
injective on the displayed dilate; all translation and homogeneity
bookkeeping is discharged here. -/
theorem preprocessedReserveCertificate_of_commonBasisDenseBox
    {stableCore integerCore : Finset ℤ}
    {d ell s D extraLoss scaleNum scaleDen k : ℕ}
    (radius : Fin d → ℕ)
    (family : Fin ell → Finset (LatticePoint d))
    (reserve : Fin ell → Finset (LatticePoint 1))
    (f : LatticePoint d →+ LatticePoint 1)
    (hradius : ∀ i, 0 < radius i)
    (hcovered : ContainsTranslate (heterogeneousSumset family)
      ((symmetricAxisBox radius).dilate k))
    (hfamilyMap : ∀ i, (family i).image f ⊆ GAP.subsetSums (reserve i))
    (hinjective : Set.InjOn f
      ((symmetricCoordinateGAP radius).dilate k).carrier)
    (hintegerCore : integerCore ⊆ stableCore)
    (hstableCoreLarge : stableCore.card ≤ integerCore.card + extraLoss)
    (hdisjoint : (Set.univ : Set (Fin ell)).PairwiseDisjoint reserve)
    (hreserveCore : ∀ i,
      reserve i ⊆ Stability.integerPoints integerCore)
    (hreserveSmall : (∑ i, (reserve i).card) ≤ s)
    (hcore : insert 0 (Stability.integerPoints integerCore) ⊆
      (NoCarryEmbedding.mapGAP f
        (symmetricCoordinateGAP radius)).carrier)
    (hrank : d ≤ D)
    (hk : 0 < k)
    (hscaleNum : 0 < scaleNum) (hscaleDen : 0 < scaleDen)
    (hscaleLower : scaleNum * s ≤ scaleDen * k)
    (hscaleUpper : k ≤ s) :
    Nonempty (PreprocessedReserveCertificate stableCore s D extraLoss
      scaleNum scaleDen) := by
  classical
  obtain ⟨u, hu⟩ := hcovered
  let P := symmetricCoordinateGAP radius
  let Q := NoCarryEmbedding.mapGAP f P
  let center : LatticePoint d := fun i ↦ (k * radius i : ℕ)
  let t : LatticePoint 1 := f (u + center)
  have hQdilate : (Q.dilate k).Proper := by
    dsimp only [Q]
    rw [← NoCarryEmbedding.mapGAP_dilate]
    exact NoCarryEmbedding.mapGAP_proper_of_injOn_carrier f (P.dilate k)
      (symmetricCoordinateGAP_dilate_proper radius) hinjective
  have hQproper : Q.Proper :=
    GAP.SProper.proper (Q.sProper_of_dilate_proper k hQdilate)
      (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hk))
  have hcentered : Q.Centered radius := by
    constructor
    · rfl
    · change f (fun i ↦ -(radius i : ℤ)) =
        fun j ↦ -∑ i, (radius i : ℤ) * f (P.steps i) j
      rw [map_eq_sum_symmetricCoordinateGAP_steps f radius]
      funext j
      simp only [neg_mul, Finset.sum_neg_distrib]
      rfl
  have hcoveredTarget :
      Elementary.translate t (Q.dilate k).carrier ⊆
        heterogeneousSumset (fun i ↦ GAP.subsetSums (reserve i)) := by
    intro x hx
    obtain ⟨p, hp, hpx⟩ := Elementary.mem_translate_iff.mp hx
    have hp' : p ∈ (NoCarryEmbedding.mapGAP f (P.dilate k)).carrier := by
      rwa [NoCarryEmbedding.mapGAP_dilate]
    rw [NoCarryEmbedding.mapGAP_carrier] at hp'
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hp'
    have hcenterY : center + y ∈
        ((symmetricAxisBox radius).dilate k).carrier := by
      rw [← symmetricCoordinateGAP_dilate_carrier radius]
      exact Elementary.mem_translate_iff.mpr ⟨y, hy, rfl⟩
    have hsource : u + (center + y) ∈ heterogeneousSumset family :=
      hu (Elementary.mem_translate_iff.mpr ⟨center + y, hcenterY, rfl⟩)
    have hmapped : f (u + (center + y)) ∈
        (heterogeneousSumset family).image f :=
      Finset.mem_image.mpr ⟨u + (center + y), hsource, rfl⟩
    have htarget := map_heterogeneousSumset_subset f family
      (fun i ↦ GAP.subsetSums (reserve i)) hfamilyMap hmapped
    rw [← hpx]
    simpa only [t, map_add, add_assoc] using htarget
  refine ⟨{
    integerCore := integerCore
    integerCore_subset := hintegerCore
    stableCore_large := hstableCoreLarge
    ell := ell
    rank := d
    k := k
    reserve := reserve
    progression := Q
    translatePoint := t
    reserve_pairwiseDisjoint := hdisjoint
    rank_le := hrank
    reserve_subset_core := hreserveCore
    reserve_small := hreserveSmall
    core_zero_subset := hcore
    homogeneous := hcentered.homogeneous
    covered := hcoveredTarget
    dilate_proper := hQdilate
    k_pos := hk
    scaleNum_pos := hscaleNum
    scaleDen_pos := hscaleDen
    scale_lower := hscaleLower
    scale_upper := hscaleUpper
    progression_proper := hQproper
    progression_symmetric := ⟨radius, hcentered⟩
    progression_nondegenerate := ?_
    covered_translate_homogeneous := ?_ }⟩
  · intro i
    exact symmetricCoordinateGAP_nondegenerate hradius i
  · refine ⟨u, ?_⟩
    have hoff : (Q.dilate k).offset = f (P.dilate k).offset := by
      rw [← NoCarryEmbedding.mapGAP_dilate]
      rfl
    rw [hoff]
    change f (u + center) + f ((P.dilate k).offset) = _
    rw [← map_add]
    have hcenterOffset : center + (P.dilate k).offset = 0 := by
      funext i
      simp [center, P, symmetricCoordinateGAP]
    rw [add_assoc, hcenterOffset, add_zero]
    simpa only [Q, P, NoCarryEmbedding.mapGAP] using
      map_eq_sum_symmetricCoordinateGAP_steps f radius u

/-- Corollary 2.17-facing specialization of the deterministic map-back.
All blocks are transported through the single basis chosen from their
common generated lattice. -/
theorem preprocessedReserveCertificate_of_corollary217Certificate
    {stableCore integerCore : Finset ℤ}
    {d ell s D extraLoss scaleNum scaleDen k : ℕ}
    {Q : AxisBox d} (A : Fin ell → Finset (LatticePoint d))
    (base : Fin ell)
    (reserve : Fin ell → Finset (LatticePoint 1))
    (hgenerated : ∀ i,
      generatedSublattice (A i) = generatedSublattice (A base))
    (cert : Corollary217Certificate Q (A base))
    (hwidth : 2 ≤ Q.minWidth)
    (hcovered : ContainsTranslate
      (heterogeneousSumset (fun i ↦
        sublatticeBasisImage cert.basis (A i)
          (subset_sublattice_of_generatedSublattice_eq (hgenerated i))))
      ((symmetricAxisBox cert.radius).dilate k))
    (eval : LatticePoint d →+ LatticePoint 1)
    (hevalFamily : ∀ i,
      (A i).image eval ⊆ GAP.subsetSums (reserve i))
    (hinjective : Set.InjOn eval (cert.progression.dilate k).carrier)
    (hintegerCore : integerCore ⊆ stableCore)
    (hstableCoreLarge : stableCore.card ≤ integerCore.card + extraLoss)
    (hdisjoint : (Set.univ : Set (Fin ell)).PairwiseDisjoint reserve)
    (hreserveCore : ∀ i,
      reserve i ⊆ Stability.integerPoints integerCore)
    (hreserveSmall : (∑ i, (reserve i).card) ≤ s)
    (hcore : insert 0 (Stability.integerPoints integerCore) ⊆
      (NoCarryEmbedding.mapGAP
        (eval.comp (sublatticeBasisEvaluation cert.basis))
        (symmetricCoordinateGAP cert.radius)).carrier)
    (hrank : d ≤ D) (hk : 0 < k)
    (hscaleNum : 0 < scaleNum) (hscaleDen : 0 < scaleDen)
    (hscaleLower : scaleNum * s ≤ scaleDen * k)
    (hscaleUpper : k ≤ s) :
    Nonempty (PreprocessedReserveCertificate stableCore s D extraLoss
      scaleNum scaleDen) := by
  apply preprocessedReserveCertificate_of_commonBasisDenseBox
    cert.radius
    (fun i ↦ sublatticeBasisImage cert.basis (A i)
      (subset_sublattice_of_generatedSublattice_eq (hgenerated i)))
    reserve (eval.comp (sublatticeBasisEvaluation cert.basis))
  · intro i
    have hi := cert.radius_lower i
    omega
  · exact hcovered
  · intro i
    simpa only [image_sublatticeBasisImage_composite] using hevalFamily i
  · exact injOn_composite_symmetricCoordinateGAP_dilate
      cert eval hinjective
  · exact hintegerCore
  · exact hstableCoreLarge
  · exact hdisjoint
  · exact hreserveCore
  · exact hreserveSmall
  · exact hcore
  · exact hrank
  · exact hk
  · exact hscaleNum
  · exact hscaleDen
  · exact hscaleLower
  · exact hscaleUpper

end

end Erdos186.CFP

#print axioms Erdos186.CFP.symmetricCoordinateGAP_dilate_carrier
#print axioms Erdos186.CFP.symmetricCoordinateGAP_dilate_proper
#print axioms Erdos186.CFP.preprocessedReserveCertificate_of_commonBasisDenseBox
#print axioms Erdos186.CFP.preprocessedReserveCertificate_of_corollary217Certificate
