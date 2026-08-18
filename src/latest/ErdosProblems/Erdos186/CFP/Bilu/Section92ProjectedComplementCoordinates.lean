/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.Bilu.Section92ComplementCoordinates
import ErdosProblems.Erdos186.CFP.Bilu.Section92ProjectedGauge

/-!
# Lattice-normalized coordinates for the projected kernel quotient

The analytic quotient is naturally an orthogonal projection, while the
discrete quotient is naturally the integral complement chosen by Smith
normal form.  This file identifies those two models: projections of the
chosen complement basis form a real basis of the projected space.  Its
basis coordinates therefore carry the projected complement lattice to the
literal standard lattice.
-/

namespace Erdos186.CFP.Bilu.Section92ShortKernel.PrimitiveKernelStep

open Module Submodule
open Mahler
open SubspaceLattice
open Section92ProjectedGauge.PrimitiveKernelStep

noncomputable section

variable {n : ℕ} {p : Seminorm ℝ (Fin n → ℝ)}
  {phi : IntegralPoint n →+ ℤ} {T : ℝ}

variable (S : PrimitiveKernelStep p phi T)

/- These aliases place the analytic quotient data in the structure's
namespace, so downstream files can use ordinary dot notation. -/
abbrev primitiveReal : EuclideanSpace ℝ (Fin n) :=
  Section92ProjectedGauge.PrimitiveKernelStep.primitiveReal S

abbrev projectedSpace : Submodule ℝ (EuclideanSpace ℝ (Fin n)) :=
  Section92ProjectedGauge.PrimitiveKernelStep.projectedSpace S

theorem finrank_projectedSpace :
    finrank ℝ S.projectedSpace = S.quotient.complementRank :=
  Section92ProjectedGauge.PrimitiveKernelStep.finrank_projectedSpace S

/-- The primitive/complement integral basis of the old standard lattice. -/
def fullIntegralBasis :
    Basis (Fin 1 ⊕ Fin S.quotient.complementRank) ℤ (IntegralPoint n) :=
  (S.quotient.primitiveBasis.prod S.quotient.complementBasis).map
    ((primitiveDirection S.short.vector).prodEquivOfIsCompl
      S.quotient.complement S.quotient.isCompl)

/-- The same full basis embedded in Euclidean space. -/
def fullRealFamily (i : Fin 1 ⊕ Fin S.quotient.complementRank) :
    EuclideanSpace ℝ (Fin n) :=
  (EuclideanSpace.equiv (Fin n) ℝ).symm
    (integralEmbed (S.fullIntegralBasis i))

/-- The real vectors belonging to the integral complement basis. -/
def complementReal (i : Fin S.quotient.complementRank) :
    EuclideanSpace ℝ (Fin n) :=
  (EuclideanSpace.equiv (Fin n) ℝ).symm
    (integralEmbed
      (S.quotient.complementBasis i : IntegralPoint n))

@[simp] theorem fullIntegralBasis_inl (i : Fin 1) :
    S.fullIntegralBasis (Sum.inl i) =
      (S.quotient.primitiveBasis i : IntegralPoint n) := by
  simp [fullIntegralBasis, Submodule.coe_prodEquivOfIsCompl']

@[simp] theorem fullIntegralBasis_inr
    (i : Fin S.quotient.complementRank) :
    S.fullIntegralBasis (Sum.inr i) =
      (S.quotient.complementBasis i : IntegralPoint n) := by
  simp [fullIntegralBasis, Submodule.coe_prodEquivOfIsCompl']

@[simp] theorem fullRealFamily_inl_zero :
    S.fullRealFamily (Sum.inl 0) = S.primitiveReal := by
  rw [fullRealFamily, fullIntegralBasis_inl]
  rfl

@[simp] theorem fullRealFamily_inr
    (i : Fin S.quotient.complementRank) :
    S.fullRealFamily (Sum.inr i) = S.complementReal i := by
  simp [fullRealFamily, complementReal]

/-- The primitive vector together with the complement vectors remains a
real-linearly independent family. -/
theorem linearIndependent_fullRealFamily :
    LinearIndependent ℝ S.fullRealFamily := by
  have hfun : LinearIndependent ℝ
      (fun i ↦ integralEmbed (S.fullIntegralBasis i)) := by
    change LinearIndependent ℝ (fun i ↦
      algebraMap ℤ ℝ ∘ S.fullIntegralBasis i)
    exact linearIndependent_algebraMap_comp_iff.mpr
      S.fullIntegralBasis.linearIndependent
  exact hfun.map' (EuclideanSpace.equiv (Fin n) ℝ).symm.toLinearMap
    (by simp)

/-- The real complement family alone is linearly independent. -/
theorem linearIndependent_complementReal :
    LinearIndependent ℝ S.complementReal := by
  have h := S.linearIndependent_fullRealFamily.comp
    (fun i : Fin S.quotient.complementRank ↦ Sum.inr i)
    Sum.inr_injective
  change LinearIndependent ℝ
    (fun i ↦ S.fullRealFamily (Sum.inr i)) at h
  simpa only [fullRealFamily_inr] using h

/-- The primitive real line and the real span of the complement basis are
disjoint. -/
theorem disjoint_primitive_complementSpan :
    Disjoint (ℝ ∙ S.primitiveReal)
      (Submodule.span ℝ (Set.range S.complementReal)) := by
  have h :=
    (linearIndependent_sum.mp S.linearIndependent_fullRealFamily).2.2
  have hleft : (S.fullRealFamily ∘ Sum.inl) =
      (fun _ : Fin 1 ↦ S.primitiveReal) := by
    funext i
    fin_cases i
    exact S.fullRealFamily_inl_zero
  have hright : (S.fullRealFamily ∘ Sum.inr) =
      S.complementReal := by
    funext i
    exact S.fullRealFamily_inr i
  rw [hleft, hright] at h
  simpa only [Set.range_unique] using h

/-- Orthogonal projections of the complement basis into the quotient
space. -/
def projectedComplementFamily
    (i : Fin S.quotient.complementRank) : S.projectedSpace :=
  (ℝ ∙ S.primitiveReal)ᗮ.orthogonalProjectionOnto (S.complementReal i)

/-- The orthogonal projection is injective on the real span of the chosen
integral complement. -/
theorem projection_injective_on_complementSpan :
    LinearMap.ker
      (S.projectedSpace.orthogonalProjectionOnto.toLinearMap.comp
        (Submodule.span ℝ (Set.range S.complementReal)).subtype) = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro x hx
  rw [LinearMap.mem_ker] at hx
  have hxline : (x : EuclideanSpace ℝ (Fin n)) ∈ ℝ ∙ S.primitiveReal := by
    have hxorth : (x : EuclideanSpace ℝ (Fin n)) ∈ S.projectedSpaceᗮ :=
      S.projectedSpace.orthogonalProjectionOnto_eq_zero_iff.mp hx
    change (x : EuclideanSpace ℝ (Fin n)) ∈
      (ℝ ∙ S.primitiveReal)ᗮᗮ at hxorth
    rwa [Submodule.orthogonal_orthogonal] at hxorth
  have hxcomp : (x : EuclideanSpace ℝ (Fin n)) ∈
      Submodule.span ℝ (Set.range S.complementReal) := x.property
  have hzero := Submodule.disjoint_def.mp
    S.disjoint_primitive_complementSpan (x : EuclideanSpace ℝ (Fin n))
      hxline hxcomp
  exact Subtype.ext hzero

/-- The projected complement vectors are linearly independent. -/
theorem linearIndependent_projectedComplementFamily :
    LinearIndependent ℝ S.projectedComplementFamily := by
  let C := Submodule.span ℝ (Set.range S.complementReal)
  let f : C →ₗ[ℝ] S.projectedSpace :=
    S.projectedSpace.orthogonalProjectionOnto.toLinearMap.comp C.subtype
  let v : Fin S.quotient.complementRank → C := fun i ↦
    ⟨S.complementReal i, Submodule.subset_span (Set.mem_range_self i)⟩
  have hv : LinearIndependent ℝ v := by
    apply LinearIndependent.of_comp C.subtype
    change LinearIndependent ℝ S.complementReal
    exact S.linearIndependent_complementReal
  have hfker : LinearMap.ker f = ⊥ := by
    exact S.projection_injective_on_complementSpan
  have hout := hv.map' f hfker
  change LinearIndependent ℝ (fun i ↦ f (v i)) at hout
  change LinearIndependent ℝ
    (fun i ↦ S.projectedSpace.orthogonalProjectionOnto
      (S.complementReal i))
  simpa [f, v, C] using hout

/-- The projected complement family is a basis: it has the quotient rank
and is linearly independent. -/
def projectedComplementBasis :
    Basis (Fin S.quotient.complementRank) ℝ S.projectedSpace := by
  let V := Submodule.span ℝ (Set.range S.projectedComplementFamily)
  have hdimV : finrank ℝ V = S.quotient.complementRank := by
    rw [finrank_span_eq_card S.linearIndependent_projectedComplementFamily,
      Fintype.card_fin]
  have hdim : finrank ℝ S.projectedSpace =
      S.quotient.complementRank := S.finrank_projectedSpace
  have htop : V = ⊤ := Submodule.eq_top_of_finrank_eq (hdimV.trans hdim.symm)
  exact Basis.mk S.linearIndependent_projectedComplementFamily htop.ge

theorem projectedComplementBasis_apply
    (i : Fin S.quotient.complementRank) :
    S.projectedComplementBasis i = S.projectedComplementFamily i := by
  simp [projectedComplementBasis]

/-- The lattice-normalizing real coordinate chart on the quotient. -/
def projectedComplementEquiv :
    S.projectedSpace ≃ₗ[ℝ] (Fin S.quotient.complementRank → ℝ) :=
  S.projectedComplementBasis.equivFun

@[simp] theorem projectedComplementEquiv_projectedComplementFamily
    (i : Fin S.quotient.complementRank) :
    S.projectedComplementEquiv (S.projectedComplementFamily i) =
      Pi.single i 1 := by
  ext j
  rw [← projectedComplementBasis_apply]
  by_cases hij : i = j
  · subst j
    simp [projectedComplementEquiv, Pi.single]
  · rw [Pi.single_eq_of_ne (Ne.symm hij)]
    simp [projectedComplementEquiv, hij]

/-- The real coordinate embedding of the reduced standard lattice. -/
def reducedIntegralRealLinear :
    IntegralPoint S.quotient.complementRank →ₗ[ℤ]
      (Fin S.quotient.complementRank → ℝ) :=
  ((EuclideanSpace.equiv (Fin S.quotient.complementRank) ℝ).toLinearMap.restrictScalars ℤ).comp
    (integralRealLinear (n := S.quotient.complementRank))

@[simp] theorem reducedIntegralRealLinear_apply
    (z : IntegralPoint S.quotient.complementRank) :
    S.reducedIntegralRealLinear z = integralEmbed z := by
  rfl

/-- Orthogonal projection followed by the integral-complement coordinate
chart, viewed as an integer-linear map on the old standard lattice. -/
def projectedIntegralCoordinates :
    IntegralPoint n →ₗ[ℤ] (Fin S.quotient.complementRank → ℝ) :=
  (S.projectedComplementEquiv.toLinearMap.restrictScalars ℤ).comp
    ((S.projectedSpace.orthogonalProjectionOnto.toLinearMap.restrictScalars ℤ).comp
      (integralRealLinear (n := n)))

@[simp] theorem projectedIntegralCoordinates_apply (x : IntegralPoint n) :
    S.projectedIntegralCoordinates x =
      S.projectedComplementEquiv
        (S.projectedSpace.orthogonalProjectionOnto (integralReal x)) :=
  rfl

/-- The analytic orthogonal quotient and the algebraic primitive quotient
give exactly the same standard real coordinates on every integral point. -/
theorem projectedIntegralCoordinates_eq :
    S.projectedIntegralCoordinates =
      S.reducedIntegralRealLinear.comp S.quotient.complementCoordinates := by
  apply S.fullIntegralBasis.ext
  intro i
  rcases i with i | i
  · fin_cases i
    simp [projectedIntegralCoordinates, reducedIntegralRealLinear,
      PrimitiveIntegralQuotient.complementCoordinates,
      PrimitiveIntegralQuotient.complementProjection,
      PrimitiveIntegralQuotient.complementCoordinateEquiv,
      fullRealFamily, primitiveReal]
    change S.primitiveReal ∈ S.projectedSpaceᗮ
    change S.primitiveReal ∈ (ℝ ∙ S.primitiveReal)ᗮᗮ
    rw [Submodule.orthogonal_orthogonal]
    exact Submodule.mem_span_singleton_self S.primitiveReal
  · simp [projectedIntegralCoordinates, reducedIntegralRealLinear,
      PrimitiveIntegralQuotient.complementCoordinates,
      PrimitiveIntegralQuotient.complementProjection,
      PrimitiveIntegralQuotient.complementCoordinateEquiv,
      projectedComplementFamily, complementReal]
    have hleft :
        integralRealLinear
            (S.quotient.complementBasis i : IntegralPoint n) =
          S.complementReal i := by
      ext j
      rfl
    rw [hleft]
    change S.projectedComplementEquiv (S.projectedComplementFamily i) = _
    rw [S.projectedComplementEquiv_projectedComplementFamily i]
    ext j
    by_cases hji : j = i
    · subst j
      simp [Pi.single_apply, integralRealLinear, integralReal]
    · simp [Pi.single_apply, integralRealLinear, integralReal, hji]

/-- Pointwise coordinate form of the quotient compatibility.  This is the
key identity used to transport all old integral lifts to the reduced unit
ball. -/
theorem projectedIntegralCoordinates_eq_integralEmbed
    (x : IntegralPoint n) :
    S.projectedComplementEquiv
        (S.projectedSpace.orthogonalProjectionOnto (integralReal x)) =
      integralEmbed (S.quotient.complementCoordinates x) := by
  have h := LinearMap.congr_fun S.projectedIntegralCoordinates_eq x
  simpa using h

end

end Erdos186.CFP.Bilu.Section92ShortKernel.PrimitiveKernelStep

#print axioms Erdos186.CFP.Bilu.Section92ShortKernel.PrimitiveKernelStep.linearIndependent_projectedComplementFamily
#print axioms Erdos186.CFP.Bilu.Section92ShortKernel.PrimitiveKernelStep.projectedComplementEquiv_projectedComplementFamily
