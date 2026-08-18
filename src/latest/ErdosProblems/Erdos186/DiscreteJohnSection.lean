/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.DiscreteJohnRank
import Mathlib.Analysis.Convex.Measure
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# The full-dimensional real body in active lattice coordinates

The lattice rank reduction is useful geometrically only after the real
span of its intrinsic basis is identified with a full-dimensional
coordinate space.  This file supplies that real linear embedding and its
basic exactness properties.  In particular it makes explicit why the
active rank, rather than the number of fields in a padded certificate, is
the correct rank in the volume branch.
-/

namespace Erdos186
namespace DiscreteJohn
namespace RankReduction

open scoped BigOperators
open CFP.Bilu.Mahler
open CFP.Bilu.SaturatedFlag
open Filter

variable {d : ℕ}

/-- Real synthesis along the intrinsic integral lattice basis. -/
noncomputable def realSectionSynthesis
    (points : Finset (LatticePoint d)) :
    (Fin (sectionRank points) → ℝ) →ₗ[ℝ] (Fin d → ℝ) where
  toFun a := ∑ i, a i • integralEmbed (sectionSteps points i)
  map_add' a b := by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c a := by
    simp only [Pi.smul_apply, RingHom.id_apply, smul_smul,
      Finset.smul_sum]
    rfl

theorem realSectionSynthesis_apply
    (points : Finset (LatticePoint d))
    (a : Fin (sectionRank points) → ℝ) :
    realSectionSynthesis points a =
      ∑ i, a i • integralEmbed (sectionSteps points i) := rfl

/-- Real synthesis is injective because the intrinsic integral basis stays
linearly independent after scalar extension. -/
theorem realSectionSynthesis_injective
    (points : Finset (LatticePoint d)) :
    Function.Injective (realSectionSynthesis points) := by
  intro a b hab
  have hzero : ∑ i, (a i - b i) •
      integralEmbed (sectionSteps points i) = 0 := by
    calc
      (∑ i, (a i - b i) • integralEmbed (sectionSteps points i)) =
          realSectionSynthesis points (a - b) := by
        rfl
      _ = realSectionSynthesis points a - realSectionSynthesis points b := by
        rw [map_sub]
      _ = 0 := sub_eq_zero.mpr hab
  have hLI := sectionSteps_realLinearIndependent points
  rw [Fintype.linearIndependent_iff] at hLI
  funext i
  have hi := hLI (fun i ↦ a i - b i) hzero i
  exact sub_eq_zero.mp hi

/-- The real linear synthesis of integral coordinates agrees with integral
synthesis followed by the standard lattice embedding. -/
theorem realSectionSynthesis_integralEmbed
    (points : Finset (LatticePoint d))
    (a : LatticePoint (sectionRank points)) :
    realSectionSynthesis points (integralEmbed a) =
      integralEmbed (sectionSynthesis points a) := by
  rw [realSectionSynthesis_apply, sectionSynthesis_eq_integerCombination,
    integralEmbed_integerCombination]
  apply Finset.sum_congr rfl
  intro i _hi
  rfl

/-- Pull a real set in ambient coordinates back to the active coordinate
space. -/
def sectionBody (points : Finset (LatticePoint d))
    (K : Set (Fin d → ℝ)) : Set (Fin (sectionRank points) → ℝ) :=
  realSectionSynthesis points ⁻¹' K

@[simp]
theorem integralEmbed_mem_sectionBody_iff
    (points : Finset (LatticePoint d)) (K : Set (Fin d → ℝ))
    (a : LatticePoint (sectionRank points)) :
    integralEmbed a ∈ sectionBody points K ↔
      integralEmbed (sectionSynthesis points a) ∈ K := by
  rw [sectionBody, Set.mem_preimage,
    realSectionSynthesis_integralEmbed]

/-- If `points` is the exact lattice section of `K`, then its intrinsic
coordinate image is the exact lattice section of the pulled-back body. -/
theorem sectionCoordinatePoints_exact
    (points : Finset (LatticePoint d)) (K : Set (Fin d → ℝ))
    (hpoints : ∀ z, z ∈ points ↔ integralEmbed z ∈ K)
    (a : LatticePoint (sectionRank points)) :
    a ∈ sectionCoordinatePoints points ↔
      integralEmbed a ∈ sectionBody points K := by
  rw [mem_sectionCoordinatePoints_iff,
    integralEmbed_mem_sectionBody_iff, hpoints]

/-- Balancedness survives restriction to the active real coordinates. -/
theorem sectionBody_balanced (points : Finset (LatticePoint d))
    {K : Set (Fin d → ℝ)} (hK : Balanced ℝ K) :
    Balanced ℝ (sectionBody points K) := by
  intro a ha y hy
  obtain ⟨x, hx, rfl⟩ := hy
  change realSectionSynthesis points (a • x) ∈ K
  rw [map_smul]
  exact hK a ha (Set.smul_mem_smul_set hx)

/-- Convexity survives restriction to the active real coordinates. -/
theorem sectionBody_convex (points : Finset (LatticePoint d))
    {K : Set (Fin d → ℝ)} (hK : Convex ℝ K) :
    Convex ℝ (sectionBody points K) := by
  exact hK.linear_preimage (realSectionSynthesis points)

/-- Closedness survives restriction to the active real coordinates. -/
theorem sectionBody_isClosed (points : Finset (LatticePoint d))
    {K : Set (Fin d → ℝ)} (hK : IsClosed K) :
    IsClosed (sectionBody points K) := by
  exact hK.preimage (LinearMap.continuous_of_finiteDimensional
    (realSectionSynthesis points))

/-- Boundedness survives restriction along the injective active-coordinate
map. -/
theorem sectionBody_bounded (points : Finset (LatticePoint d))
    {K : Set (Fin d → ℝ)} (hK : Bornology.IsVonNBounded ℝ K) :
    Bornology.IsVonNBounded ℝ (sectionBody points K) := by
  rw [NormedSpace.isVonNBounded_iff] at hK ⊢
  obtain ⟨c, _hc, hcAnti⟩ :=
    (realSectionSynthesis points).injective_iff_antilipschitz.mp
      (realSectionSynthesis_injective points)
  exact hcAnti.isBounded_preimage hK

/-- Casting a rational linear combination of integral points to `ℝ`
places it in their real span. -/
theorem real_of_mem_rationalSpan
    (points : Finset (LatticePoint d)) {q : Fin d → ℚ}
    (hq : q ∈ Submodule.span ℚ
      (rationalEmbed d '' (points : Set (LatticePoint d)))) :
    (fun j ↦ (q j : ℝ)) ∈ Submodule.span ℝ
      (integralEmbed '' (points : Set (LatticePoint d))) := by
  let castQR : (Fin d → ℚ) → (Fin d → ℝ) :=
    fun x j ↦ (x j : ℝ)
  refine Submodule.span_induction
    (p := fun x _ ↦ castQR x ∈ Submodule.span ℝ
      (integralEmbed '' (points : Set (LatticePoint d)))) ?_ ?_ ?_ ?_ hq
  · rintro x ⟨z, hz, rfl⟩
    apply Submodule.subset_span
    exact ⟨z, hz, rfl⟩
  · have hz : castQR 0 = 0 := by
      funext j
      simp [castQR]
    rw [hz]
    exact (Submodule.span ℝ
      (integralEmbed '' (points : Set (LatticePoint d)))).zero_mem
  · intro x y _hx _hy hx hy
    have heq : castQR (x + y) = castQR x + castQR y := by
      funext j
      simp [castQR]
    rw [heq]
    exact Submodule.add_mem _ hx hy
  · intro a x _hx hx
    have heq : castQR (a • x) = (a : ℝ) • castQR x := by
      funext j
      simp [castQR]
    rw [heq]
    exact Submodule.smul_mem _ (a : ℝ) hx

/-- Every intrinsic lattice basis vector lies in the real span of the
original finite lattice set. -/
theorem sectionStep_mem_realSpan_points
    (points : Finset (LatticePoint d)) (i : Fin (sectionRank points)) :
    integralEmbed (sectionSteps points i) ∈
      Submodule.span ℝ
        (integralEmbed '' (points : Set (LatticePoint d))) := by
  have hi := (sectionBasis points i).property
  change rationalEmbed d (sectionSteps points i) ∈
    Submodule.span ℚ
      (rationalEmbed d '' (points : Set (LatticePoint d))) at hi
  have hreal := real_of_mem_rationalSpan points hi
  change (fun j ↦ ((sectionSteps points i j : ℤ) : ℝ)) ∈
    Submodule.span ℝ
      (integralEmbed '' (points : Set (LatticePoint d)))
  exact hreal

/-- Real synthesis maps the standard coordinate basis to the embedded
intrinsic lattice basis. -/
@[simp]
theorem realSectionSynthesis_basisFun
    (points : Finset (LatticePoint d))
    (i : Fin (sectionRank points)) :
    realSectionSynthesis points
        (Pi.basisFun ℝ (Fin (sectionRank points)) i) =
      integralEmbed (sectionSteps points i) := by
  rw [realSectionSynthesis_apply]
  classical
  simp

/-- The ambient real image of `points` is exactly the real synthesis of
the embedded intrinsic coordinate set. -/
theorem integralEmbed_image_points_eq_section
    (points : Finset (LatticePoint d)) :
    integralEmbed '' (points : Set (LatticePoint d)) =
      realSectionSynthesis points ''
        (integralEmbed ''
          (sectionCoordinatePoints points :
            Set (LatticePoint (sectionRank points)))) := by
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    let a := sectionCoordinates points z (mem_sectionLattice hz)
    have ha : a ∈ sectionCoordinatePoints points := by
      rw [mem_sectionCoordinatePoints_iff]
      rw [sectionSynthesis_eq_integerCombination,
        section_synthesis_coordinates]
      exact hz
    refine ⟨integralEmbed a, ⟨a, ha, rfl⟩, ?_⟩
    rw [realSectionSynthesis_integralEmbed,
      sectionSynthesis_eq_integerCombination,
      section_synthesis_coordinates]
  · rintro ⟨_y, ⟨a, ha, rfl⟩, rfl⟩
    rw [realSectionSynthesis_integralEmbed]
    refine ⟨sectionSynthesis points a, ?_, rfl⟩
    exact (mem_sectionCoordinatePoints_iff points a).mp ha

/-- The embedded intrinsic coordinate points span the whole active real
coordinate space. -/
theorem span_integralEmbed_sectionCoordinatePoints_eq_top
    (points : Finset (LatticePoint d)) :
    Submodule.span ℝ
        (integralEmbed ''
          (sectionCoordinatePoints points :
            Set (LatticePoint (sectionRank points)))) = ⊤ := by
  let S : Set (Fin (sectionRank points) → ℝ) :=
    integralEmbed ''
      (sectionCoordinatePoints points :
        Set (LatticePoint (sectionRank points)))
  let f := realSectionSynthesis points
  have hbasis (i : Fin (sectionRank points)) :
      Pi.basisFun ℝ (Fin (sectionRank points)) i ∈ Submodule.span ℝ S := by
    have hstep := sectionStep_mem_realSpan_points points i
    rw [integralEmbed_image_points_eq_section] at hstep
    rw [← Submodule.map_span] at hstep
    obtain ⟨x, hx, hfx⟩ := hstep
    have hfi : f (Pi.basisFun ℝ (Fin (sectionRank points)) i) =
        integralEmbed (sectionSteps points i) := by
      exact realSectionSynthesis_basisFun points i
    have hxi : x = Pi.basisFun ℝ (Fin (sectionRank points)) i := by
      apply realSectionSynthesis_injective points
      rw [hfx, hfi]
    rwa [← hxi]
  apply top_unique
  rw [← (Pi.basisFun ℝ (Fin (sectionRank points))).span_eq]
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  exact hbasis i

/-- The active coordinate body has full affine span whenever the original
finite lattice section is nonempty and exact. -/
theorem affineSpan_sectionBody_eq_top
    (points : Finset (LatticePoint d)) (K : Set (Fin d → ℝ))
    (hbalanced : Balanced ℝ K)
    (hpoints : ∀ z, z ∈ points ↔ integralEmbed z ∈ K)
    (hnonempty : points.Nonempty) :
    affineSpan ℝ (sectionBody points K) = ⊤ := by
  let S : Set (Fin (sectionRank points) → ℝ) :=
    integralEmbed ''
      (sectionCoordinatePoints points :
        Set (LatticePoint (sectionRank points)))
  have hspan : Submodule.span ℝ S = ⊤ := by
    exact span_integralEmbed_sectionCoordinatePoints_eq_top points
  have h0K : (0 : Fin d → ℝ) ∈ K := by
    obtain ⟨z, hz⟩ := hnonempty
    exact hbalanced.zero_mem ⟨integralEmbed z, (hpoints z).mp hz⟩
  have h0body : (0 : Fin (sectionRank points) → ℝ) ∈
      sectionBody points K := by
    change realSectionSynthesis points 0 ∈ K
    simpa using h0K
  have hSbody : S ⊆ sectionBody points K := by
    rintro _ ⟨a, ha, rfl⟩
    exact (sectionCoordinatePoints_exact points K hpoints a).mp ha
  have hsmall : affineSpan ℝ
      ({(0 : Fin (sectionRank points) → ℝ)} ∪
        (fun v ↦ v +ᵥ (0 : Fin (sectionRank points) → ℝ)) '' S) = ⊤ := by
    apply affineSpan_singleton_union_vadd_eq_top_of_span_eq_top
    simpa using hspan
  have hsubset :
      ({(0 : Fin (sectionRank points) → ℝ)} ∪
        (fun v ↦ v +ᵥ (0 : Fin (sectionRank points) → ℝ)) '' S) ⊆
          sectionBody points K := by
    rintro x (hx | hx)
    · simpa only [Set.mem_singleton_iff] using hx ▸ h0body
    · obtain ⟨y, hy, rfl⟩ := hx
      simpa using hSbody hy
  have hle := affineSpan_mono ℝ hsubset
  rw [hsmall] at hle
  exact top_unique hle

/-- A balanced convex active-coordinate body with an exact nonempty lattice
section is a neighbourhood of the origin.  This is the key relative-interior
step absent from the ambient `SymmetricConvexBody` interface. -/
theorem sectionBody_mem_nhds_zero
    (points : Finset (LatticePoint d)) {K : Set (Fin d → ℝ)}
    (hbalanced : Balanced ℝ K) (hconvex : Convex ℝ K)
    (hpoints : ∀ z, z ∈ points ↔ integralEmbed z ∈ K)
    (hnonempty : points.Nonempty) :
    sectionBody points K ∈ nhds 0 := by
  have hconv := sectionBody_convex points hconvex
  have haff := affineSpan_sectionBody_eq_top points K hbalanced
    hpoints hnonempty
  obtain ⟨x, hx⟩ :=
    hconv.interior_nonempty_iff_affineSpan_eq_top.mpr haff
  have hneg : -x ∈ sectionBody points K :=
    (sectionBody_balanced points hbalanced).neg_mem_iff.mpr
      (interior_subset hx)
  have hzero : (0 : Fin (sectionRank points) → ℝ) ∈
      interior (sectionBody points K) := by
    have hmid := hconv.add_smul_sub_mem_interior hneg hx
      (show (1 / 2 : ℝ) ∈ Set.Ioc 0 1 by norm_num)
    convert hmid using 1 <;> module
  exact mem_interior_iff_mem_nhds.mp hzero

/-- The pullback to active lattice coordinates is an honest symmetric
convex body even when the original body has empty ambient interior. -/
theorem sectionBody_isSymmetricConvexBody
    (points : Finset (LatticePoint d)) {K : Set (Fin d → ℝ)}
    (hbalanced : Balanced ℝ K) (hconvex : Convex ℝ K)
    (hclosed : IsClosed K) (hbounded : Bornology.IsVonNBounded ℝ K)
    (hpoints : ∀ z, z ∈ points ↔ integralEmbed z ∈ K)
    (hnonempty : points.Nonempty) :
    SymmetricConvexBody (sectionBody points K) where
  balanced := sectionBody_balanced points hbalanced
  convex := sectionBody_convex points hconvex
  nhds_zero := sectionBody_mem_nhds_zero points hbalanced hconvex
    hpoints hnonempty
  bounded := sectionBody_bounded points hbounded
  isClosed := sectionBody_isClosed points hclosed

variable {r factor : ℕ}

/-- Real synthesis along an arbitrary finite tuple of integral steps. -/
def realStepsSynthesis (steps : Fin r → LatticePoint d) :
    (Fin r → ℝ) →ₗ[ℝ] (Fin d → ℝ) where
  toFun a := ∑ i, a i • integralEmbed (steps i)
  map_add' a b := by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c a := by
    simp only [Pi.smul_apply, RingHom.id_apply, smul_smul,
      Finset.smul_sum]
    rfl

/-- A certificate covering the intrinsic coordinate points cannot have
rank smaller than the active lattice rank. -/
theorem sectionRank_le_certificateRank
    (points : Finset (LatticePoint d))
    (C : Certificate (sectionCoordinatePoints points) r factor) :
    sectionRank points ≤ r := by
  let g := realStepsSynthesis C.steps
  have hcoordRange :
      integralEmbed ''
          (sectionCoordinatePoints points :
            Set (LatticePoint (sectionRank points))) ⊆
        LinearMap.range g := by
    rintro _ ⟨z, hz, rfl⟩
    have hzOuter := C.subset_outer_carrier hz
    change z ∈ (symmetricGAP C.steps C.radii).carrier at hzOuter
    obtain ⟨n, hn⟩ := GAP.mem_carrier_iff.mp hzOuter
    let a : Fin r → ℝ :=
      fun i ↦ ((n i : ℤ) - (C.radii i : ℤ) : ℝ)
    refine ⟨a, ?_⟩
    change (∑ i, a i • integralEmbed (C.steps i)) = integralEmbed z
    simp only [a]
    simp_rw [← Int.cast_sub]
    rw [← integralEmbed_integerCombination]
    rw [symmetricGAP_coordPoint] at hn
    exact congrArg integralEmbed hn
  have hsurj : Function.Surjective g := by
    rw [← LinearMap.range_eq_top]
    apply top_unique
    rw [← span_integralEmbed_sectionCoordinatePoints_eq_top points]
    exact Submodule.span_le.mpr hcoordRange
  have hfin := LinearMap.finrank_le_finrank_of_surjective hsurj
  simpa using hfin

/-! ## Uniform discrete John after passing to the active section -/

/-- A neutral, import-cycle-free form of the effective-rank conclusion.
It applies to a compact symmetric convex set in ambient coordinates even
when that set has empty ambient interior.  The returned certificate has
exactly the rank of the lattice section. -/
def EffectiveSectionDiscreteJohnStatement : Prop :=
  ∀ d : ℕ, ∃ factorBound : ℕ,
    ∀ (K : Set (Fin d → ℝ))
      (hbalanced : Balanced ℝ K) (hconvex : Convex ℝ K)
      (hclosed : IsClosed K) (hbounded : Bornology.IsVonNBounded ℝ K)
      (points : Finset (LatticePoint d)),
      (∀ z, z ∈ points ↔ integralEmbed z ∈ K) →
      points.Nonempty →
        ∃ factor : ℕ, factor ≤ factorBound ∧
          Nonempty (Certificate points (sectionRank points) factor)

/-- The ambient-interior discrete-John statement upgrades to the
rank-sensitive statement by applying it in intrinsic lattice coordinates.
Summing the dimension-specific bounds for ranks `0, ..., d` makes the
resulting factor bound uniform in the original ambient dimension. -/
theorem effectiveSectionDiscreteJohn_of_discreteJohn
    (hJohn : DiscreteJohnStatement) :
    EffectiveSectionDiscreteJohnStatement := by
  classical
  choose rankBound hRankBound using hJohn
  intro d
  refine ⟨∑ e ∈ Finset.range (d + 1), rankBound e, ?_⟩
  intro K hbalanced hconvex hclosed hbounded points hpoints hnonempty
  let e := sectionRank points
  have hBody : SymmetricConvexBody (sectionBody points K) :=
    sectionBody_isSymmetricConvexBody points hbalanced hconvex hclosed
      hbounded hpoints hnonempty
  obtain ⟨rank, factor, hrank, hfactor, C⟩ :=
    hRankBound e (sectionBody points K) hBody
      (sectionCoordinatePoints points)
      (sectionCoordinatePoints_exact points K hpoints)
  have herank : e ≤ rank :=
    sectionRank_le_certificateRank points C.some
  have hrankEq : rank = e := Nat.le_antisymm hrank herank
  subst rank
  refine ⟨factor, ?_, ⟨liftCertificate points C.some⟩⟩
  refine hfactor.trans ?_
  exact Finset.single_le_sum
    (fun _ _ ↦ Nat.zero_le _) (Finset.mem_range.mpr (Nat.lt_succ_of_le
      (sectionRank_le points)))

end RankReduction
end DiscreteJohn
end Erdos186
