/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.ProjectedProperizationExistence
import ErdosProblems.Erdos186.CFP.Bilu.Section92NormalizedProjectedGauge

/-!
# The controlled primitive rank-drop core for projected properization

The primitive-kernel construction is algebraic in its target group, while
the projected-gauge construction is stated for an integer-valued map.  This
file connects the two without changing the chosen primitive direction or
integral complement: a generic primitive step is given a scalar analytic
shadow whose map is zero and whose quotient data is literally copied from
the generic step.

The first application is preservation of a full family of unit-ball lattice
points under rank decrease.  The same shadow is also the coordinate system
used by the controlled lifting estimate below.
-/

namespace Erdos186.CFP.ProjectedProperizationRankDrop

open Module Submodule
open Bilu.Mahler
open Bilu.Section92ShortKernel

noncomputable section

variable {n : ℕ} {H : Type*} [AddCommGroup H]
  {p : Seminorm ℝ (Fin n → ℝ)} {phi : IntegralPoint n →+ H} {T : ℝ}

/-- The scalar quotient with exactly the same primitive and complementary
integral bases as a quotient in an arbitrary target group. -/
def scalarizedQuotient {q : IntegralPoint n}
    (Q : PrimitiveIntegralQuotient phi q) :
    PrimitiveIntegralQuotient (0 : IntegralPoint n →+ ℤ) q where
  complement := Q.complement
  isCompl := Q.isCompl
  direction_le_ker := by
    intro x hx
    simp
  primitiveBasis := Q.primitiveBasis
  complementRank := Q.complementRank
  complementBasis := Q.complementBasis
  rank_eq := Q.rank_eq

/-- A scalar analytic shadow of a primitive step in an arbitrary target.
All lattice and quotient coordinates are definitionally the same. -/
def scalarizedStep (S : PrimitiveKernelStep p phi T) :
    PrimitiveKernelStep p (0 : IntegralPoint n →+ ℤ) T where
  short :=
    { vector := S.short.vector
      ne_zero := S.short.ne_zero
      map_eq_zero := by simp
      seminorm_le := S.short.seminorm_le }
  quotient := scalarizedQuotient S.quotient

@[simp] theorem scalarizedStep_complementRank
    (S : PrimitiveKernelStep p phi T) :
    (scalarizedStep S).quotient.complementRank =
      S.quotient.complementRank := rfl

@[simp] theorem scalarizedStep_complementCoordinates
    (S : PrimitiveKernelStep p phi T) (x : IntegralPoint n) :
    (scalarizedStep S).quotient.complementCoordinates x =
      S.quotient.complementCoordinates x := rfl

/-- Reindex generic reduced coordinates into the definitionally copied
scalar quotient. -/
def scalarizedCoordinateEquiv (S : PrimitiveKernelStep p phi T) :
    IntegralPoint S.quotient.complementRank ≃ₗ[ℤ]
      IntegralPoint (scalarizedStep S).quotient.complementRank :=
  LinearEquiv.piCongrLeft ℤ
    (fun _ : Fin (scalarizedStep S).quotient.complementRank ↦ ℤ)
    (finCongr (scalarizedStep_complementRank S).symm)

/-- The matching real coordinate reindexing. -/
def scalarizedRealCoordinateEquiv (S : PrimitiveKernelStep p phi T) :
    (Fin S.quotient.complementRank → ℝ) ≃ₗ[ℝ]
      (Fin (scalarizedStep S).quotient.complementRank → ℝ) :=
  LinearEquiv.piCongrLeft ℝ
    (fun _ : Fin (scalarizedStep S).quotient.complementRank ↦ ℝ)
    (finCongr (scalarizedStep_complementRank S).symm)

@[simp] theorem scalarizedRealCoordinateEquiv_integralEmbed
    (S : PrimitiveKernelStep p phi T)
    (z : IntegralPoint S.quotient.complementRank) :
    scalarizedRealCoordinateEquiv S (integralEmbed z) =
      integralEmbed (scalarizedCoordinateEquiv S z) := by
  rfl

@[simp] theorem scalarizedCoordinateEquiv_complementCoordinates
    (S : PrimitiveKernelStep p phi T) (x : IntegralPoint n) :
    scalarizedCoordinateEquiv S (S.quotient.complementCoordinates x) =
      (scalarizedStep S).quotient.complementCoordinates x := by
  rfl

theorem complementRank_lt (S : PrimitiveKernelStep p phi T) :
    S.quotient.complementRank < n := by
  have hrank := S.quotient.rank_eq
  omega

/-- The real quotient map underlying the coordinate-projected seminorm. -/
def projectedCoordinateMap (S : PrimitiveKernelStep p phi T) :
    (Fin n → ℝ) →ₗ[ℝ]
      (Fin (scalarizedStep S).quotient.complementRank → ℝ) :=
  let S₀ := scalarizedStep S
  S₀.projectedComplementEquiv.toLinearMap.comp
    (S₀.projectedSpace.orthogonalProjectionOnto.toLinearMap.comp
      (EuclideanSpace.equiv (Fin n) ℝ).symm.toLinearMap)

theorem projectedCoordinateMap_surjective
    (S : PrimitiveKernelStep p phi T) :
    Function.Surjective (projectedCoordinateMap S) := by
  intro y
  let S₀ := scalarizedStep S
  let z : S₀.projectedSpace := S₀.projectedComplementEquiv.symm y
  refine ⟨(EuclideanSpace.equiv (Fin n) ℝ) (z : EuclideanSpace ℝ (Fin n)), ?_⟩
  change S₀.projectedComplementEquiv
      (S₀.projectedSpace.orthogonalProjectionOnto
        ((EuclideanSpace.equiv (Fin n) ℝ).symm
          ((EuclideanSpace.equiv (Fin n) ℝ)
            (z : EuclideanSpace ℝ (Fin n))))) = y
  rw [(EuclideanSpace.equiv (Fin n) ℝ).symm_apply_apply]
  rw [Submodule.orthogonalProjectionOnto_mem_subspace_eq_self z]
  exact S₀.projectedComplementEquiv.apply_symm_apply y

@[simp] theorem projectedCoordinateMap_integralEmbed
    (S : PrimitiveKernelStep p phi T) (x : IntegralPoint n) :
    projectedCoordinateMap S (integralEmbed x) =
      integralEmbed ((scalarizedStep S).quotient.complementCoordinates x) := by
  exact (scalarizedStep S).projectedIntegralCoordinates_eq_integralEmbed x

/-- A full family of integral unit-ball points remains full after quotienting
by a primitive collision.  The new family is selected from the images of
the old family, so its unit-radius bound follows from exact unit-ball
preservation. -/
theorem admitsIndependent_coordinateProjectedSeminorm
    (S : PrimitiveKernelStep p phi T) (hp : IsDefinite p)
    (hfull : AdmitsIndependent p n 1) :
    AdmitsIndependent ((scalarizedStep S).coordinateProjectedSeminorm hp)
      S.quotient.complementRank 1 := by
  let S₀ := scalarizedStep S
  obtain ⟨v, hvli, hvbound⟩ := hfull
  let w : Fin n → (Fin S₀.quotient.complementRank → ℝ) :=
    fun i ↦ integralEmbed (S₀.quotient.complementCoordinates (v i))
  have hvspan : Submodule.span ℝ
      (Set.range (fun i ↦ integralEmbed (v i))) = ⊤ := by
    apply hvli.span_eq_top_of_card_eq_finrank'
    simp
  have hwspan : Submodule.span ℝ (Set.range w) = ⊤ := by
    have hmap : Submodule.map (projectedCoordinateMap S)
        (Submodule.span ℝ (Set.range (fun i ↦ integralEmbed (v i)))) = ⊤ := by
      rw [hvspan, Submodule.map_top]
      exact LinearMap.range_eq_top.mpr (projectedCoordinateMap_surjective S)
    rw [Submodule.map_span, ← Set.range_comp] at hmap
    have hfun :
        (projectedCoordinateMap S) ∘ (fun i ↦ integralEmbed (v i)) = w := by
      funext i
      change projectedCoordinateMap S (integralEmbed (v i)) =
        integralEmbed ((scalarizedStep S).quotient.complementCoordinates (v i))
      exact projectedCoordinateMap_integralEmbed S (v i)
    rwa [hfun] at hmap
  obtain ⟨u, huRange, _huSpan, huLI⟩ :=
    Submodule.exists_fun_fin_finrank_span_eq ℝ (Set.range w)
  have hfinrank : finrank ℝ (Submodule.span ℝ (Set.range w)) =
      S₀.quotient.complementRank := by
    rw [hwspan, finrank_top, finrank_fin_fun]
  let e : Fin S₀.quotient.complementRank ≃
      Fin (finrank ℝ (Submodule.span ℝ (Set.range w))) :=
    finCongr hfinrank.symm
  choose j hj using fun i ↦ huRange (e i)
  let z : Fin S₀.quotient.complementRank →
      IntegralPoint S₀.quotient.complementRank :=
    fun i ↦ S₀.quotient.complementCoordinates (v (j i))
  refine ⟨z, ?_, ?_⟩
  · have huLI' : LinearIndependent ℝ (u ∘ e) :=
      huLI.comp e e.injective
    have hzu : (fun i ↦ integralEmbed (z i)) = u ∘ e := by
      funext i
      simpa only [z, w, Function.comp_apply] using hj i
    exact hzu.symm ▸ huLI'
  · intro i
    exact S₀.coordinateProjectedSeminorm_complementCoordinates_le_one
      hp (v (j i)) (hvbound (j i))

/-- Every real number is within one half of an integer.  We use the
round-to-nearest convention `floor (a + 1/2)`. -/
theorem exists_int_abs_sub_le_half (a : ℝ) :
    ∃ m : ℤ, |a - (m : ℝ)| ≤ 1 / 2 := by
  refine ⟨round a, ?_⟩
  rw [round_eq]
  apply abs_le.mpr
  constructor
  · have hfloor : ((⌊a + 1 / 2⌋ : ℤ) : ℝ) ≤ a + 1 / 2 :=
      Int.floor_le (a + 1 / 2)
    linarith
  · have hfloor : a + 1 / 2 < ((⌊a + 1 / 2⌋ : ℤ) : ℝ) + 1 :=
      Int.lt_floor_add_one (a + 1 / 2)
    linarith

/-- A point in a radius-`t` ball for the quotient seminorm has a real lift
in the old radius-`t` ball. -/
theorem exists_real_lift_of_coordinateProjectedSeminorm_le
    (S : PrimitiveKernelStep p phi T) (hp : IsDefinite p)
    {t : ℝ} (ht : 0 ≤ t)
    (z : IntegralPoint (scalarizedStep S).quotient.complementRank)
    (hz : (scalarizedStep S).coordinateProjectedSeminorm hp
      (integralEmbed z) ≤ t) :
    ∃ x : Fin n → ℝ,
      p x ≤ t ∧ projectedCoordinateMap S x = integralEmbed z := by
  rcases ht.eq_or_lt with rfl | ht
  · have hz0 : integralEmbed z = 0 := by
      apply (scalarizedStep S).isDefinite_coordinateProjectedSeminorm hp
      exact le_antisymm hz (apply_nonneg _ _)
    refine ⟨0, by simp, ?_⟩
    rw [map_zero]
    exact hz0.symm
  · have hinv : 0 < t⁻¹ := inv_pos.mpr ht
    have hscaled : (scalarizedStep S).coordinateProjectedSeminorm hp
        (t⁻¹ • integralEmbed z) ≤ 1 := by
      rw [map_smul_eq_mul]
      rw [Real.norm_eq_abs, abs_of_pos hinv]
      calc
        t⁻¹ * (scalarizedStep S).coordinateProjectedSeminorm hp
            (integralEmbed z) ≤
            t⁻¹ * t := mul_le_mul_of_nonneg_left hz hinv.le
        _ = 1 := inv_mul_cancel₀ ht.ne'
    have hmem : t⁻¹ • integralEmbed z ∈
        (scalarizedStep S).coordinateProjectedBody := by
      rw [← (scalarizedStep S).unitBall_coordinateProjectedSeminorm hp]
      exact hscaled
    obtain ⟨y, ⟨xE, hxE, rfl⟩, hy⟩ := hmem
    let x : Fin n → ℝ :=
      t • (EuclideanSpace.equiv (Fin n) ℝ) xE
    refine ⟨x, ?_, ?_⟩
    · rw [show p x = t * p ((EuclideanSpace.equiv (Fin n) ℝ) xE) by
        simp [x, map_smul_eq_mul, abs_of_pos ht]]
      have hxunit : p ((EuclideanSpace.equiv (Fin n) ℝ) xE) ≤ 1 := by
        rw [Bilu.Section92ProjectedGauge.PrimitiveKernelStep.euclideanUnitBall,
          Seminorm.mem_closedBall] at hxE
        simp only [sub_zero] at hxE
        change p ((EuclideanSpace.equiv (Fin n) ℝ) xE) ≤ 1 at hxE
        exact hxE
      nlinarith [apply_nonneg p ((EuclideanSpace.equiv (Fin n) ℝ) xE)]
    · change (scalarizedStep S).projectedComplementEquiv
        ((scalarizedStep S).projectedSpace.orthogonalProjectionOnto
          ((EuclideanSpace.equiv (Fin n) ℝ).symm x)) = integralEmbed z
      rw [show (EuclideanSpace.equiv (Fin n) ℝ).symm x = t • xE by
        simp [x]]
      rw [map_smul, map_smul]
      rw [hy]
      rw [smul_smul, mul_inv_cancel₀ ht.ne', one_smul]

/-- The real kernel of the projected coordinate map is exactly contained
in the primitive real line. -/
theorem mem_primitiveSpan_of_projectedCoordinateMap_eq_zero
    (S : PrimitiveKernelStep p phi T) {x : Fin n → ℝ}
    (hx : projectedCoordinateMap S x = 0) :
    (EuclideanSpace.equiv (Fin n) ℝ).symm x ∈
      ℝ ∙ (scalarizedStep S).primitiveReal := by
  have hproj : (scalarizedStep S).projectedSpace.orthogonalProjectionOnto
      ((EuclideanSpace.equiv (Fin n) ℝ).symm x) = 0 := by
    change (scalarizedStep S).projectedComplementEquiv
      ((scalarizedStep S).projectedSpace.orthogonalProjectionOnto
        ((EuclideanSpace.equiv (Fin n) ℝ).symm x)) = 0 at hx
    apply (scalarizedStep S).projectedComplementEquiv.injective
    rw [map_zero]
    exact hx
  have horth :=
    (scalarizedStep S).projectedSpace.orthogonalProjectionOnto_eq_zero_iff.mp hproj
  change (EuclideanSpace.equiv (Fin n) ℝ).symm x ∈
    (ℝ ∙ (scalarizedStep S).primitiveReal)ᗮᗮ at horth
  rwa [Submodule.orthogonal_orthogonal] at horth

/-- Controlled integral lifting through one primitive rank drop.  A
reduced lattice point of quotient radius `t` has an old integral lift of
the same group value and old radius at most `t + T`. -/
theorem exists_integral_lift_of_coordinateProjectedSeminorm_le
    (S : PrimitiveKernelStep p phi T) (hp : IsDefinite p)
    {t : ℝ} (ht : 0 ≤ t)
    (z : IntegralPoint S.quotient.complementRank)
    (hz : (scalarizedStep S).coordinateProjectedSeminorm hp
      (integralEmbed (scalarizedCoordinateEquiv S z)) ≤ t) :
    ∃ x : IntegralPoint n,
      phi x = S.quotient.reducedMap z ∧
        p (integralEmbed x) ≤ t + T := by
  obtain ⟨xR, hxR, hxProjection⟩ :=
    exists_real_lift_of_coordinateProjectedSeminorm_le S hp ht
      (scalarizedCoordinateEquiv S z) hz
  let lift : IntegralPoint n := S.quotient.complementLift z
  let generator : IntegralPoint n :=
    Bilu.Section92ProjectedGauge.PrimitiveIntegralQuotient.primitiveGenerator
      (scalarizedStep S).quotient
  have hliftProjection : projectedCoordinateMap S (integralEmbed lift) =
      integralEmbed (scalarizedCoordinateEquiv S z) := by
    rw [projectedCoordinateMap_integralEmbed]
    rw [← scalarizedCoordinateEquiv_complementCoordinates]
    simp [lift]
  have hkernel : projectedCoordinateMap S (integralEmbed lift - xR) = 0 := by
    rw [map_sub, hliftProjection, hxProjection, sub_self]
  have hspan := mem_primitiveSpan_of_projectedCoordinateMap_eq_zero S hkernel
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hspan
  obtain ⟨m, hm⟩ := exists_int_abs_sub_le_half a
  let x : IntegralPoint n := lift - m • generator
  refine ⟨x, ?_, ?_⟩
  · have hgeneratorKernel : phi generator = 0 := by
      change generator ∈ LinearMap.ker phi.toIntLinearMap
      apply S.quotient.direction_le_ker
      exact
        Bilu.Section92ProjectedGauge.PrimitiveIntegralQuotient.primitiveGenerator_mem
          (scalarizedStep S).quotient
    simp only [x, map_sub, map_zsmul, hgeneratorKernel, smul_zero, sub_zero]
    rfl
  · have hline : a • integralEmbed generator = integralEmbed lift - xR := by
      have h := congrArg (EuclideanSpace.equiv (Fin n) ℝ) ha
      rw [map_smul] at h
      change a • (EuclideanSpace.equiv (Fin n) ℝ)
          ((scalarizedStep S).primitiveReal) =
        (EuclideanSpace.equiv (Fin n) ℝ)
          ((EuclideanSpace.equiv (Fin n) ℝ).symm
            (integralEmbed lift - xR)) at h
      have hrhs : (EuclideanSpace.equiv (Fin n) ℝ)
          ((EuclideanSpace.equiv (Fin n) ℝ).symm
            (integralEmbed lift - xR)) = integralEmbed lift - xR :=
        (EuclideanSpace.equiv (Fin n) ℝ).apply_symm_apply _
      rw [hrhs] at h
      have hgenerator : (EuclideanSpace.equiv (Fin n) ℝ)
          ((scalarizedStep S).primitiveReal) = integralEmbed generator := by
        ext i
        rfl
      rwa [hgenerator] at h
    have hembed : integralEmbed x = xR +
        (a - (m : ℝ)) • integralEmbed generator := by
      have hlift : integralEmbed lift = xR + a • integralEmbed generator := by
        calc
          integralEmbed lift = a • integralEmbed generator + xR :=
            (eq_sub_iff_add_eq.mp hline).symm
          _ = xR + a • integralEmbed generator := add_comm _ _
      rw [show integralEmbed x = integralEmbed lift -
          (m : ℝ) • integralEmbed generator by
        ext i
        simp [x, integralEmbed]]
      rw [hlift]
      module
    rw [hembed]
    calc
      p (xR + (a - (m : ℝ)) • integralEmbed generator) ≤
          p xR + p ((a - (m : ℝ)) • integralEmbed generator) :=
        map_add_le_add p _ _
      _ = p xR + |a - (m : ℝ)| * p (integralEmbed generator) := by
        rw [map_smul_eq_mul, Real.norm_eq_abs]
      _ ≤ t + T := by
        have hgenerator : p (integralEmbed generator) ≤ 2 * T := by
          exact
            (Bilu.Section92ProjectedGauge.PrimitiveIntegralQuotient.seminorm_primitiveGenerator_le
              (scalarizedStep S).quotient S.short.ne_zero).trans S.short.seminorm_le
        have hcorrection : |a - (m : ℝ)| * p (integralEmbed generator) ≤ T := by
          calc
            |a - (m : ℝ)| * p (integralEmbed generator) ≤
                (1 / 2 : ℝ) * (2 * T) :=
              mul_le_mul hm hgenerator (apply_nonneg p _) (by norm_num)
            _ = T := by ring
        exact add_le_add hxR hcorrection

/-! ## A cast-free generic-coordinate facade -/

/-- The coordinate-projected seminorm transported back to the literal
generic complement rank. -/
def genericCoordinateProjectedSeminorm
    (S : PrimitiveKernelStep p phi T) (hp : IsDefinite p) :
    Seminorm ℝ (Fin S.quotient.complementRank → ℝ) :=
  ((scalarizedStep S).coordinateProjectedSeminorm hp).comp
    (scalarizedRealCoordinateEquiv S).toLinearMap

theorem isDefinite_genericCoordinateProjectedSeminorm
    (S : PrimitiveKernelStep p phi T) (hp : IsDefinite p) :
    IsDefinite (genericCoordinateProjectedSeminorm S hp) := by
  intro x hx
  apply (scalarizedRealCoordinateEquiv S).injective
  have hzero := (scalarizedStep S).isDefinite_coordinateProjectedSeminorm hp
    (scalarizedRealCoordinateEquiv S x) hx
  rw [map_zero]
  exact hzero

/-- Full independent unit-ball families survive rank decrease, stated in
the generic complement coordinates used by the reduced map. -/
theorem admitsIndependent_genericCoordinateProjectedSeminorm
    (S : PrimitiveKernelStep p phi T) (hp : IsDefinite p)
    (hfull : AdmitsIndependent p n 1) :
    AdmitsIndependent (genericCoordinateProjectedSeminorm S hp)
      S.quotient.complementRank 1 := by
  obtain ⟨v, hvli, hvbound⟩ :=
    admitsIndependent_coordinateProjectedSeminorm S hp hfull
  let u : Fin S.quotient.complementRank →
      IntegralPoint S.quotient.complementRank :=
    fun i ↦ (scalarizedCoordinateEquiv S).symm (v i)
  refine ⟨u, ?_, ?_⟩
  · apply LinearIndependent.of_comp (scalarizedRealCoordinateEquiv S).toLinearMap
    have huv : ((scalarizedRealCoordinateEquiv S).toLinearMap) ∘
        (fun i ↦ integralEmbed (u i)) = fun i ↦ integralEmbed (v i) := by
      funext i
      change scalarizedRealCoordinateEquiv S (integralEmbed (u i)) =
        integralEmbed (v i)
      rw [scalarizedRealCoordinateEquiv_integralEmbed]
      have hui : scalarizedCoordinateEquiv S (u i) = v i := by
        exact (scalarizedCoordinateEquiv S).apply_symm_apply (v i)
      rw [hui]
    rwa [huv]
  · intro i
    change (scalarizedStep S).coordinateProjectedSeminorm hp
      (scalarizedRealCoordinateEquiv S (integralEmbed (u i))) ≤ 1
    rw [scalarizedRealCoordinateEquiv_integralEmbed]
    have hui : scalarizedCoordinateEquiv S (u i) = v i := by
      exact (scalarizedCoordinateEquiv S).apply_symm_apply (v i)
    rw [hui]
    exact hvbound i

/-- Every old integral unit-ball point maps to a generic reduced
unit-ball point. -/
theorem genericCoordinateProjectedSeminorm_complementCoordinates_le_one
    (S : PrimitiveKernelStep p phi T) (hp : IsDefinite p)
    (x : IntegralPoint n) (hx : p (integralEmbed x) ≤ 1) :
    genericCoordinateProjectedSeminorm S hp
        (integralEmbed (S.quotient.complementCoordinates x)) ≤ 1 := by
  change (scalarizedStep S).coordinateProjectedSeminorm hp
    (scalarizedRealCoordinateEquiv S
      (integralEmbed (S.quotient.complementCoordinates x))) ≤ 1
  rw [scalarizedRealCoordinateEquiv_integralEmbed,
    scalarizedCoordinateEquiv_complementCoordinates]
  exact (scalarizedStep S).coordinateProjectedSeminorm_complementCoordinates_le_one
    hp x hx

/-- Cast-free form of the controlled integral lifting theorem. -/
theorem exists_integral_lift_of_genericCoordinateProjectedSeminorm_le
    (S : PrimitiveKernelStep p phi T) (hp : IsDefinite p)
    {t : ℝ} (ht : 0 ≤ t)
    (z : IntegralPoint S.quotient.complementRank)
    (hz : genericCoordinateProjectedSeminorm S hp (integralEmbed z) ≤ t) :
    ∃ x : IntegralPoint n,
      phi x = S.quotient.reducedMap z ∧
        p (integralEmbed x) ≤ t + T := by
  apply exists_integral_lift_of_coordinateProjectedSeminorm_le S hp ht z
  change (scalarizedStep S).coordinateProjectedSeminorm hp
    (scalarizedRealCoordinateEquiv S (integralEmbed z)) ≤ t at hz
  rwa [scalarizedRealCoordinateEquiv_integralEmbed] at hz

/-! ## Proper Mahler outer containers after one rank drop -/

/-- The reduced generic-coordinate seminorm has the complete proper
Mahler outer container used by the scale recursion. -/
theorem exists_genericProjectedMappedOuterContainer
    (S : PrimitiveKernelStep p phi T) (hp : IsDefinite p)
    (hfull : AdmitsIndependent p n 1)
    (hrank : 0 < S.quotient.complementRank) :
    Nonempty
      (Bilu.Section9ContainerIntegration.MappedOuterContainer
        (genericCoordinateProjectedSeminorm S hp)
        (0 : IntegralPoint S.quotient.complementRank →+ ℤ)) := by
  exact Bilu.Section9ContainerIntegration.exists_mappedOuterContainer
    hrank (genericCoordinateProjectedSeminorm S hp)
    (isDefinite_genericCoordinateProjectedSeminorm S hp)
    (admitsIndependent_genericCoordinateProjectedSeminorm S hp hfull) 0

/-- Old unit-ball lattice points project into the reduced Mahler source
GAP. -/
theorem complementCoordinates_mem_genericProjectedOuterSource
    (S : PrimitiveKernelStep p phi T) (hp : IsDefinite p)
    (D : Bilu.Section9ContainerIntegration.MappedOuterContainer
      (genericCoordinateProjectedSeminorm S hp)
      (0 : IntegralPoint S.quotient.complementRank →+ ℤ))
    (x : IntegralPoint n) (hx : p (integralEmbed x) ≤ 1) :
    S.quotient.complementCoordinates x ∈ D.source.carrier := by
  exact D.unitBall_integral_subset _
    (genericCoordinateProjectedSeminorm_complementCoordinates_le_one
      S hp x hx)

/-- Every point of a dilated reduced Mahler source has an old integral
lift with the same target-group image.  Its old seminorm cost is the
dimension-only outer dilation bound plus the primitive correction `T`. -/
theorem exists_old_lift_of_mem_genericProjectedOuterSource_dilate
    (S : PrimitiveKernelStep p phi T) (hp : IsDefinite p)
    (hfull : AdmitsIndependent p n 1)
    (D : Bilu.Section9ContainerIntegration.MappedOuterContainer
      (genericCoordinateProjectedSeminorm S hp)
      (0 : IntegralPoint S.quotient.complementRank →+ ℤ))
    {k : ℕ} {z : IntegralPoint S.quotient.complementRank}
    (hz : z ∈ (D.source.dilate k).carrier) :
    ∃ x : IntegralPoint n,
      phi x = S.quotient.reducedMap z ∧
        p (integralEmbed x) ≤
          Bilu.Section92OuterInjectivityBridge.outerDilationBound
            S.quotient.complementRank k + T := by
  have hzBound : genericCoordinateProjectedSeminorm S hp (integralEmbed z) ≤
      Bilu.Section92OuterInjectivityBridge.outerDilationBound
        S.quotient.complementRank k := by
    exact
      Bilu.Section92OuterInjectivityBridge.seminorm_le_outerDilationBound_of_mem
        D (isDefinite_genericCoordinateProjectedSeminorm S hp)
          (admitsIndependent_genericCoordinateProjectedSeminorm S hp hfull) z hz
  exact exists_integral_lift_of_genericCoordinateProjectedSeminorm_le
    S hp
      (Bilu.Section92OuterInjectivityBridge.outerDilationBound_nonneg
        S.quotient.complementRank k) z hzBound

end

end Erdos186.CFP.ProjectedProperizationRankDrop

#print axioms Erdos186.CFP.ProjectedProperizationRankDrop.admitsIndependent_coordinateProjectedSeminorm
#print axioms Erdos186.CFP.ProjectedProperizationRankDrop.exists_integral_lift_of_coordinateProjectedSeminorm_le
#print axioms Erdos186.CFP.ProjectedProperizationRankDrop.exists_integral_lift_of_genericCoordinateProjectedSeminorm_le
#print axioms Erdos186.CFP.ProjectedProperizationRankDrop.exists_old_lift_of_mem_genericProjectedOuterSource_dilate
