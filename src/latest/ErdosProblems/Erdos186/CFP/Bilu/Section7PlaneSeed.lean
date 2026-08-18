/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.Bilu.Section7FreimanMap
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

/-!
# Bilu Section 7.2: extracting the small plane seed

This file turns the finite affine slice delivered by the Freiman dimension
argument into the literal finite family consumed by Proposition 7.4.  The
family is chosen from differences of points in the real floor-coordinate
image.  Consequently every selected vector is integral and belongs to the
distortion body, while its cardinality is exactly the dimension of the
affine span.
-/

namespace Erdos186.CFP.Bilu.Section7PlaneSeed

open Set Module Submodule
open scoped Pointwise RealInnerProductSpace
open Proposition75Data Proposition74Construction SubspaceLattice
open Section7FreimanMap

noncomputable section

/-- Embed the integral product coordinates in Bilu's Euclidean product. -/
def integralProductReal {m r : ℕ} (z : IntegralProduct m r) : Ambient m r :=
  WithLp.toLp 2 (integralReal z.1, integralReal z.2)

/-- The coordinatewise real embedding of the product lattice is
injective. -/
theorem integralProductReal_injective {m r : ℕ} :
    Function.Injective (@integralProductReal m r) := by
  rintro ⟨x₁, y₁⟩ ⟨x₂, y₂⟩ h
  apply Prod.ext
  · ext i
    have hi := congrArg (fun z : Ambient m r ↦ head z i) h
    change ((x₁ i : ℤ) : ℝ) = ((x₂ i : ℤ) : ℝ) at hi
    exact_mod_cast hi
  · ext i
    have hi := congrArg (fun z : Ambient m r ↦ tail z i) h
    change ((y₁ i : ℤ) : ℝ) = ((y₂ i : ℤ) : ℝ) at hi
    exact_mod_cast hi

/-- The product-lattice embedding respects addition. -/
@[simp]
theorem integralProductReal_add {m r : ℕ} (x y : IntegralProduct m r) :
    integralProductReal (x + y) =
      integralProductReal x + integralProductReal y := by
  apply WithLp.ofLp_injective 2
  apply Prod.ext <;> ext i <;> simp [integralProductReal, integralReal]

/-- The real form of the floor-coordinate Freiman map. -/
def freimanRealMap {m r : ℕ}
    (a : Fin r → EuclideanSpace ℝ (Fin m)) (b : Fin r → ℝ)
    (x : Mahler.IntegralPoint m) : Ambient m r :=
  integralProductReal (freimanMap a b x)

/-- The real Freiman map remains injective after the integral embedding. -/
theorem freimanRealMap_injective {m r : ℕ}
    (a : Fin r → EuclideanSpace ℝ (Fin m)) (b : Fin r → ℝ) :
    Function.Injective (freimanRealMap a b) :=
  integralProductReal_injective.comp (freimanMap_injective a b)

@[simp]
theorem head_freimanRealMap {m r : ℕ}
    (a : Fin r → EuclideanSpace ℝ (Fin m)) (b : Fin r → ℝ)
    (x : Mahler.IntegralPoint m) :
    head (freimanRealMap a b x) = integralReal x := rfl

@[simp]
theorem tail_freimanRealMap {m r : ℕ}
    (a : Fin r → EuclideanSpace ℝ (Fin m)) (b : Fin r → ℝ)
    (x : Mahler.IntegralPoint m) :
    tail (freimanRealMap a b x) =
      integralReal (fun i ↦ ⌊phase a b x i⌋) := rfl

/-- The real floor-coordinate image is an ambient lattice point. -/
theorem freimanRealMap_mem_ambientProductIntegralPoints {m r : ℕ}
    (a : Fin r → EuclideanSpace ℝ (Fin m)) (b : Fin r → ℝ)
    (x : Mahler.IntegralPoint m) :
    freimanRealMap a b x ∈ ambientProductIntegralPoints m r := by
  apply Submodule.mem_map.mpr
  refine ⟨(integralReal x,
      integralReal (fun i ↦ ⌊phase a b x i⌋)), ?_, rfl⟩
  constructor
  · exact ⟨x, rfl⟩
  · exact ⟨(fun i ↦ ⌊phase a b x i⌋), rfl⟩

/-- A difference of two real floor-coordinate images. -/
def freimanDifference {m r : ℕ}
    (a : Fin r → EuclideanSpace ℝ (Fin m)) (b : Fin r → ℝ)
    (x y : Mahler.IntegralPoint m) : Ambient m r :=
  freimanRealMap a b x - freimanRealMap a b y

@[simp]
theorem head_freimanDifference {m r : ℕ}
    (a : Fin r → EuclideanSpace ℝ (Fin m)) (b : Fin r → ℝ)
    (x y : Mahler.IntegralPoint m) :
    head (freimanDifference a b x y) = integralReal x - integralReal y :=
  rfl

@[simp]
theorem tail_freimanDifference_apply {m r : ℕ}
    (a : Fin r → EuclideanSpace ℝ (Fin m)) (b : Fin r → ℝ)
    (x y : Mahler.IntegralPoint m) (i : Fin r) :
    tail (freimanDifference a b x y) i =
      ((⌊phase a b x i⌋ : ℤ) : ℝ) - ((⌊phase a b y i⌋ : ℤ) : ℝ) :=
  rfl

/-- Every such difference remains in the product lattice. -/
theorem freimanDifference_mem_ambientProductIntegralPoints {m r : ℕ}
    (a : Fin r → EuclideanSpace ℝ (Fin m)) (b : Fin r → ℝ)
    (x y : Mahler.IntegralPoint m) :
    freimanDifference a b x y ∈ ambientProductIntegralPoints m r := by
  exact Submodule.sub_mem _
    (freimanRealMap_mem_ambientProductIntegralPoints a b x)
    (freimanRealMap_mem_ambientProductIntegralPoints a b y)

/-- Differences of points in a balanced convex body belong to its double. -/
theorem sub_mem_two_smul_of_balanced_convex {E : Type*}
    [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    {B : Set E} (hbalanced : Balanced ℝ B) (hconvex : Convex ℝ B)
    {x y : E} (hx : x ∈ B) (hy : y ∈ B) :
    x - y ∈ (2 : ℝ) • B := by
  have hneg : -y ∈ B := hbalanced.neg_mem_iff.mpr hy
  have hmid : (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • (-y) ∈ B :=
    hconvex hx hneg (by norm_num) (by norm_num) (by norm_num)
  refine ⟨(1 / 2 : ℝ) • x + (1 / 2 : ℝ) • (-y), hmid, ?_⟩
  module

/-- The rounding error in a difference is the difference of two fractional
parts, hence has absolute value at most one. -/
theorem freimanDifference_mem_distortionBody {m r : ℕ}
    {B : Set (EuclideanSpace ℝ (Fin m))}
    (a : Fin r → EuclideanSpace ℝ (Fin m)) (b : Fin r → ℝ)
    (x y : Mahler.IntegralPoint m)
    (hhead : integralReal x - integralReal y ∈ (2 : ℝ) • B) :
    freimanDifference a b x y ∈ distortionBody B a := by
  refine ⟨hhead, ?_⟩
  intro i
  have hphase :
      ⟪integralReal x - integralReal y, a i⟫ =
        phase a b x i - phase a b y i := by
    dsimp only [phase]
    rw [inner_sub_left]
    ring
  have hxfract :
      (((⌊phase a b x i⌋ : ℤ) : ℝ)) =
        phase a b x i - Int.fract (phase a b x i) := by
    rw [Int.fract]
    ring
  have hyfract :
      (((⌊phase a b y i⌋ : ℤ) : ℝ)) =
        phase a b y i - Int.fract (phase a b y i) := by
    rw [Int.fract]
    ring
  change |⟪integralReal x - integralReal y, a i⟫ -
    ((((⌊phase a b x i⌋ : ℤ) : ℝ)) -
      (((⌊phase a b y i⌋ : ℤ) : ℝ)))| ≤ 1
  rw [hphase, hxfract, hyfract]
  apply abs_le.mpr
  constructor <;>
    have hx0 := Int.fract_nonneg (phase a b x i) <;>
    have hy0 := Int.fract_nonneg (phase a b y i) <;>
    have hx1 := Int.fract_lt_one (phase a b x i) <;>
    have hy1 := Int.fract_lt_one (phase a b y i) <;>
    linarith

/-- Specialization to points of a balanced convex body. -/
theorem freimanDifference_mem_distortionBody_of_mem {m r : ℕ}
    {B : Set (EuclideanSpace ℝ (Fin m))}
    (hbalanced : Balanced ℝ B) (hconvex : Convex ℝ B)
    (a : Fin r → EuclideanSpace ℝ (Fin m)) (b : Fin r → ℝ)
    (x y : Mahler.IntegralPoint m)
    (hx : integralReal x ∈ B) (hy : integralReal y ∈ B) :
    freimanDifference a b x y ∈ distortionBody B a := by
  apply freimanDifference_mem_distortionBody a b x y
  exact sub_mem_two_smul_of_balanced_convex hbalanced hconvex hx hy

/-- All pairwise differences of the image of a finite set. -/
def pairDifferenceFinset {m r : ℕ}
    (a : Fin r → EuclideanSpace ℝ (Fin m)) (b : Fin r → ℝ)
    (S : Finset (Mahler.IntegralPoint m)) : Finset (Ambient m r) := by
  classical
  exact S.biUnion fun x ↦ S.image fun y ↦ freimanDifference a b x y

@[simp]
theorem mem_pairDifferenceFinset {m r : ℕ}
    (a : Fin r → EuclideanSpace ℝ (Fin m)) (b : Fin r → ℝ)
    (S : Finset (Mahler.IntegralPoint m)) (z : Ambient m r) :
    z ∈ pairDifferenceFinset a b S ↔
      ∃ x ∈ S, ∃ y ∈ S, freimanDifference a b x y = z := by
  classical
  simp [pairDifferenceFinset]

/-- The pair-difference finset spans exactly the direction of the affine
span of the real Freiman image. -/
theorem span_pairDifferenceFinset_eq_vectorSpan {m r : ℕ}
    (a : Fin r → EuclideanSpace ℝ (Fin m)) (b : Fin r → ℝ)
    (S : Finset (Mahler.IntegralPoint m)) :
    Submodule.span ℝ (pairDifferenceFinset a b S : Set (Ambient m r)) =
      vectorSpan ℝ (freimanRealMap a b '' (S : Set (Mahler.IntegralPoint m))) := by
  rw [vectorSpan_def]
  congr 1
  ext z
  change (z ∈ pairDifferenceFinset a b S) ↔
    z ∈ ((freimanRealMap a b '' (S : Set (Mahler.IntegralPoint m))) -ᵥ
      (freimanRealMap a b '' (S : Set (Mahler.IntegralPoint m))))
  rw [mem_pairDifferenceFinset, Set.mem_vsub]
  simp only [Set.mem_image]
  constructor
  · rintro ⟨x, hx, y, hy, rfl⟩
    exact ⟨freimanRealMap a b x, ⟨x, hx, rfl⟩,
      freimanRealMap a b y, ⟨y, hy, rfl⟩, rfl⟩
  · rintro ⟨_u, ⟨x, hx, rfl⟩, _v, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨x, hx, y, hy, rfl⟩

/-- Extract a basis-sized finite seed from the actual pair differences.
Its cardinality is the affine dimension, not merely bounded by it. -/
theorem exists_planeSeed {m r : ℕ}
    (a : Fin r → EuclideanSpace ℝ (Fin m)) (b : Fin r → ℝ)
    (S : Finset (Mahler.IntegralPoint m)) :
    ∃ planeSeed : Finset (Ambient m r),
      (planeSeed : Set (Ambient m r)) ⊆ pairDifferenceFinset a b S ∧
      planeSeed.card =
        finrank ℝ
          (vectorSpan ℝ
            (freimanRealMap a b '' (S : Set (Mahler.IntegralPoint m)))) ∧
      Submodule.span ℝ (planeSeed : Set (Ambient m r)) =
        vectorSpan ℝ
          (freimanRealMap a b '' (S : Set (Mahler.IntegralPoint m))) := by
  obtain ⟨planeSeed, hsub, hcard, hspan, _hindependent⟩ :=
    Submodule.exists_finset_span_eq_linearIndepOn ℝ
      (pairDifferenceFinset a b S : Set (Ambient m r))
  refine ⟨planeSeed, hsub, ?_, ?_⟩
  · rw [hcard, span_pairDifferenceFinset_eq_vectorSpan]
  · rw [hspan, span_pairDifferenceFinset_eq_vectorSpan]

/-- The extracted seed inherits membership in the distortion body and the
ambient lattice from its representing pairs, and has the exact dimension
bound required by Proposition 7.4. -/
theorem exists_planeSeed_for_proposition74 {m r : ℕ}
    {B : Set (EuclideanSpace ℝ (Fin m))}
    (hbalanced : Balanced ℝ B) (hconvex : Convex ℝ B)
    (a : Fin r → EuclideanSpace ℝ (Fin m)) (b : Fin r → ℝ)
    (S : Finset (Mahler.IntegralPoint m))
    (hS : ∀ x ∈ S, integralReal x ∈ B)
    (hdim : finrank ℝ
      (vectorSpan ℝ
        (freimanRealMap a b '' (S : Set (Mahler.IntegralPoint m)))) < r) :
    ∃ planeSeed : Finset (Ambient m r),
      (∀ z ∈ planeSeed, z ∈ distortionBody B a) ∧
      (∀ z ∈ planeSeed, z ∈ ambientProductIntegralPoints m r) ∧
      planeSeed.card + m < m + r ∧
      Submodule.span ℝ (planeSeed : Set (Ambient m r)) =
        vectorSpan ℝ
          (freimanRealMap a b '' (S : Set (Mahler.IntegralPoint m))) := by
  obtain ⟨planeSeed, hsub, hcard, hspan⟩ := exists_planeSeed a b S
  refine ⟨planeSeed, ?_, ?_, ?_, hspan⟩
  · intro z hz
    obtain ⟨x, hx, y, hy, rfl⟩ :=
      mem_pairDifferenceFinset a b S z |>.mp (hsub hz)
    exact freimanDifference_mem_distortionBody_of_mem
      hbalanced hconvex a b x y (hS x hx) (hS y hy)
  · intro z hz
    obtain ⟨x, hx, y, hy, rfl⟩ :=
      mem_pairDifferenceFinset a b S z |>.mp (hsub hz)
    exact freimanDifference_mem_ambientProductIntegralPoints a b x y
  · rw [hcard]
    omega

/-- If the real Freiman image is contained in an affine plane, its vector
span has dimension at most the direction of that plane. -/
theorem finrank_vectorSpan_lt_of_mem_affineSlice {m r : ℕ}
    (a : Fin r → EuclideanSpace ℝ (Fin m)) (b : Fin r → ℝ)
    (S : Finset (Mahler.IntegralPoint m))
    (C : AffineSubspace ℝ (Ambient m r))
    (hSC : ∀ x ∈ S, freimanRealMap a b x ∈ C)
    (hdim : finrank ℝ C.direction < r) :
    finrank ℝ
      (vectorSpan ℝ
        (freimanRealMap a b '' (S : Set (Mahler.IntegralPoint m)))) < r := by
  have haffine : affineSpan ℝ
      (freimanRealMap a b '' (S : Set (Mahler.IntegralPoint m))) ≤ C := by
    rw [affineSpan_le]
    rintro _z ⟨x, hx, rfl⟩
    exact hSC x hx
  have hdirection :
      vectorSpan ℝ
          (freimanRealMap a b '' (S : Set (Mahler.IntegralPoint m))) ≤
        C.direction := by
    rw [← direction_affineSpan]
    exact AffineSubspace.direction_le haffine
  exact (Submodule.finrank_mono hdirection).trans_lt hdim

/-- Source-facing affine-slice form of the plane-seed construction. -/
theorem exists_planeSeed_of_affineSlice {m r : ℕ}
    {B : Set (EuclideanSpace ℝ (Fin m))}
    (hbalanced : Balanced ℝ B) (hconvex : Convex ℝ B)
    (a : Fin r → EuclideanSpace ℝ (Fin m)) (b : Fin r → ℝ)
    (S : Finset (Mahler.IntegralPoint m))
    (C : AffineSubspace ℝ (Ambient m r))
    (hS : ∀ x ∈ S, integralReal x ∈ B)
    (hSC : ∀ x ∈ S, freimanRealMap a b x ∈ C)
    (hdim : finrank ℝ C.direction < r) :
    ∃ planeSeed : Finset (Ambient m r),
      (∀ z ∈ planeSeed, z ∈ distortionBody B a) ∧
      (∀ z ∈ planeSeed, z ∈ ambientProductIntegralPoints m r) ∧
      planeSeed.card + m < m + r ∧
      Submodule.span ℝ (planeSeed : Set (Ambient m r)) =
        vectorSpan ℝ
          (freimanRealMap a b '' (S : Set (Mahler.IntegralPoint m))) := by
  exact exists_planeSeed_for_proposition74 hbalanced hconvex a b S hS
    (finrank_vectorSpan_lt_of_mem_affineSlice a b S C hSC hdim)

/-- Complete Proposition 7.4 construction from the affine slice produced in
Section 7.2 and the independent integral family produced by the Mahler
chain.  The intermediate `planeSeed` is chosen internally. -/
def geometricDataOfAffineSliceAndIndependentIntegralFamily {m r : ℕ}
    (B : Set (EuclideanSpace ℝ (Fin m)))
    (hbalanced : Balanced ℝ B) (hconvex : Convex ℝ B)
    (a : Fin r → EuclideanSpace ℝ (Fin m)) (b : Fin r → ℝ)
    (S : Finset (Mahler.IntegralPoint m))
    (C : AffineSubspace ℝ (Ambient m r))
    (hS : ∀ x ∈ S, integralReal x ∈ B)
    (hSC : ∀ x ∈ S, freimanRealMap a b x ∈ C)
    (hdim : finrank ℝ C.direction < r)
    (v : Fin m → Mahler.IntegralPoint m)
    (hv_independent : LinearIndependent ℝ (fun i ↦ integralReal (v i)))
    (hv_body : ∀ i, integralReal (v i) ∈ (2 : ℝ) • B) :
    GeometricData B a := by
  let hexists := exists_planeSeed_of_affineSlice
    hbalanced hconvex a b S C hS hSC hdim
  let planeSeed := hexists.choose
  have hbody := hexists.choose_spec.1
  have hlattice := hexists.choose_spec.2.1
  have hcard := hexists.choose_spec.2.2.1
  exact geometricDataOfPlaneAndIndependentIntegralFamily
    B a planeSeed v hv_independent hv_body hbody hlattice hcard

/-- Thick-body specialization of the complete affine-slice construction. -/
def geometricDataOfAffineSliceAndAdmitsIndependent {m r : ℕ}
    (B : Set (EuclideanSpace ℝ (Fin m)))
    (hbalanced : Balanced ℝ B) (hconvex : Convex ℝ B)
    (a : Fin r → EuclideanSpace ℝ (Fin m)) (b : Fin r → ℝ)
    (S : Finset (Mahler.IntegralPoint m))
    (C : AffineSubspace ℝ (Ambient m r))
    (hS : ∀ x ∈ S, integralReal x ∈ B)
    (hSC : ∀ x ∈ S, freimanRealMap a b x ∈ C)
    (hdim : finrank ℝ C.direction < r)
    (p : Seminorm ℝ (Fin m → ℝ))
    (hindependent : Mahler.AdmitsIndependent p m 1)
    (hunit : ∀ x : Mahler.IntegralPoint m,
      p (Mahler.integralEmbed x) ≤ 1 → integralReal x ∈ (2 : ℝ) • B) :
    GeometricData B a := by
  let hexists := exists_planeSeed_of_affineSlice
    hbalanced hconvex a b S C hS hSC hdim
  let planeSeed := hexists.choose
  have hbody := hexists.choose_spec.1
  have hlattice := hexists.choose_spec.2.1
  have hcard := hexists.choose_spec.2.2.1
  exact geometricDataOfPlaneAndAdmitsIndependent
    B a p planeSeed hindependent hunit hbody hlattice hcard

end

end Erdos186.CFP.Bilu.Section7PlaneSeed

#print axioms Erdos186.CFP.Bilu.Section7PlaneSeed.exists_planeSeed
#print axioms Erdos186.CFP.Bilu.Section7PlaneSeed.exists_planeSeed_for_proposition74
#print axioms Erdos186.CFP.Bilu.Section7PlaneSeed.exists_planeSeed_of_affineSlice
#print axioms
  Erdos186.CFP.Bilu.Section7PlaneSeed.geometricDataOfAffineSliceAndIndependentIntegralFamily
#print axioms
  Erdos186.CFP.Bilu.Section7PlaneSeed.geometricDataOfAffineSliceAndAdmitsIndependent
