/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.Bilu.Section92NormalizedProjectedGauge
import ErdosProblems.Erdos186.CFP.Bilu.Section92PresentationDescent

/-!
# Primitive-kernel descent for common body presentations

This file packages the analytic and integral primitive quotient as the
rank-decreased `BodyPresentation` consumed by the minimal-rank argument.
-/

namespace Erdos186.CFP.Bilu.Section92BodyPresentationQuotient

open Module Submodule Set MeasureTheory
open Mahler MinkowskiUpper SubspaceLattice
open Section92PresentationDescent Section92ShortKernel

noncomputable section

set_option autoImplicit false

variable {A : Finset ℤ} {n : ℕ} {T : ℝ}
  (X : BodyPresentation A n)
  (S : PrimitiveKernelStep X.seminorm X.map T)

/-- Real-linear coordinate projection underlying the primitive quotient. -/
def coordinateProjectionReal :
    (Fin n → ℝ) →ₗ[ℝ] (Fin S.quotient.complementRank → ℝ) :=
  S.projectedComplementEquiv.toLinearMap.comp
    (S.projectedSpace.orthogonalProjectionOnto.toLinearMap.comp
      (EuclideanSpace.equiv (Fin n) ℝ).symm.toLinearMap)

theorem coordinateProjectionReal_surjective :
    Function.Surjective (coordinateProjectionReal X S) := by
  intro y
  let w : S.projectedSpace := S.projectedComplementEquiv.symm y
  let x : Fin n → ℝ :=
    (EuclideanSpace.equiv (Fin n) ℝ) (w : EuclideanSpace ℝ (Fin n))
  refine ⟨x, ?_⟩
  change S.projectedComplementEquiv
      (S.projectedSpace.orthogonalProjectionOnto
        ((EuclideanSpace.equiv (Fin n) ℝ).symm x)) = y
  rw [show (EuclideanSpace.equiv (Fin n) ℝ).symm x =
      (w : EuclideanSpace ℝ (Fin n)) by
    exact (EuclideanSpace.equiv (Fin n) ℝ).symm_apply_apply
      (w : EuclideanSpace ℝ (Fin n))]
  rw [S.projectedSpace.orthogonalProjectionOnto_mem_subspace_eq_self w]
  exact S.projectedComplementEquiv.apply_symm_apply y

@[simp] theorem coordinateProjectionReal_integralEmbed
    (z : IntegralPoint n) :
    coordinateProjectionReal X S (integralEmbed z) =
      integralEmbed (S.quotient.complementCoordinates z) := by
  rw [coordinateProjectionReal]
  change S.projectedComplementEquiv
      (S.projectedSpace.orthogonalProjectionOnto
        ((EuclideanSpace.equiv (Fin n) ℝ).symm (integralEmbed z))) = _
  rw [show (EuclideanSpace.equiv (Fin n) ℝ).symm (integralEmbed z) =
      integralReal z by
    ext i
    rfl]
  exact S.projectedIntegralCoordinates_eq_integralEmbed z

/-- More than one source value forces the algebraic quotient to retain a
positive rank.  If its rank were zero, factorization through the reduced
map would force every member of `A` to equal zero. -/
theorem complementRank_pos_of_one_lt_card (hA : 1 < A.card) :
    0 < S.quotient.complementRank := by
  by_contra hpos
  have hrank0 : S.quotient.complementRank = 0 := Nat.eq_zero_of_not_pos hpos
  have hsubset : A ⊆ ({0} : Finset ℤ) := by
    intro a ha
    obtain ⟨z, _hzball, hzmap⟩ := X.lifts a ha
    have hfactor := S.quotient.reducedMap_complementCoordinates z
    have hzero : S.quotient.complementCoordinates z = 0 := by
      let : Subsingleton
          (IntegralPoint S.quotient.complementRank) := by
        rw [hrank0]
        infer_instance
      exact Subsingleton.elim _ _
    rw [hzero, map_zero, hzmap] at hfactor
    simpa using hfactor.symm
  have hcard := Finset.card_le_card hsubset
  exact (Nat.not_lt_of_ge (by simpa using hcard)) hA

/-- The old full independent unit-ball family descends to a full
independent family in complement coordinates. -/
theorem coordinateProjectedSeminorm_admitsIndependent
    (hA : 1 < A.card) :
    AdmitsIndependent (S.coordinateProjectedSeminorm X.definite)
      S.quotient.complementRank 1 := by
  obtain ⟨v, hvli, hvunit⟩ := X.full
  let F := coordinateProjectionReal X S
  let vR : Fin n → (Fin n → ℝ) := fun i ↦ integralEmbed (v i)
  let w : Fin n → (Fin S.quotient.complementRank → ℝ) :=
    fun i ↦ F (vR i)
  have hvspan : Submodule.span ℝ (Set.range vR) = ⊤ := by
    exact hvli.span_eq_top_of_card_eq_finrank' (by simp [vR])
  have hFsurj : Function.Surjective F :=
    coordinateProjectionReal_surjective X S
  have hwspan : Submodule.span ℝ (Set.range w) = ⊤ := by
    have hrange : Set.range w = F '' Set.range vR := by
      ext y
      simp only [Set.mem_range, Set.mem_image]
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨vR i, ⟨i, rfl⟩, rfl⟩
      · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
        exact ⟨i, rfl⟩
    rw [hrange, ← Submodule.map_span, hvspan, Submodule.map_top,
      LinearMap.range_eq_top.mpr hFsurj]
  obtain ⟨f, hfRange, _hfSpan, hfli⟩ :=
    Submodule.exists_fun_fin_finrank_span_eq ℝ (Set.range w)
  have hdim : finrank ℝ (Submodule.span ℝ (Set.range w)) =
      S.quotient.complementRank := by
    rw [hwspan]
    simp
  let e : Fin S.quotient.complementRank ≃
      Fin (finrank ℝ (Submodule.span ℝ (Set.range w))) :=
    finCongr hdim.symm
  choose g hg using fun i ↦ hfRange (e i)
  let u : Fin S.quotient.complementRank →
      IntegralPoint S.quotient.complementRank :=
    fun i ↦ S.quotient.complementCoordinates (v (g i))
  refine ⟨u, ?_, ?_⟩
  · have hu : (fun i ↦ integralEmbed (u i)) = fun i ↦ f (e i) := by
      funext i
      rw [show integralEmbed (u i) = w (g i) by
        simp [u, w, vR, F]]
      exact hg i
    rw [hu]
    exact hfli.comp e e.injective
  · intro i
    exact S.coordinateProjectedSeminorm_complementCoordinates_le_one
      X.definite (v (g i)) (hvunit (g i))

/-- A failed enlarged-injectivity test produces the exact smaller common
body presentation used by minimal-rank termination. -/
def quotientBodyPresentation (hA : 1 < A.card) :
    BodyPresentation A S.quotient.complementRank where
  rank_pos := complementRank_pos_of_one_lt_card X S hA
  seminorm := S.coordinateProjectedSeminorm X.definite
  definite := S.isDefinite_coordinateProjectedSeminorm X.definite
  full := coordinateProjectedSeminorm_admitsIndependent X S hA
  map := S.quotient.reducedMap
  lifts := by
    intro a ha
    obtain ⟨z, hzball, hzmap⟩ := X.lifts a ha
    refine ⟨S.quotient.complementCoordinates z,
      S.coordinateProjectedSeminorm_complementCoordinates_le_one
        X.definite z hzball, ?_⟩
    rw [S.quotient.reducedMap_complementCoordinates, hzmap]
  bodyVolume_pos := by
    rw [S.unitBall_coordinateProjectedSeminorm X.definite]
    exact S.coordinateProjectedBody_volumeReal_pos X.definite

theorem quotientBodyPresentation_rank_lt :
    S.quotient.complementRank < n := by
  have hrank := S.quotient.rank_eq
  omega

end

end Erdos186.CFP.Bilu.Section92BodyPresentationQuotient

#print axioms Erdos186.CFP.Bilu.Section92BodyPresentationQuotient.quotientBodyPresentation
#print axioms Erdos186.CFP.Bilu.Section92BodyPresentationQuotient.quotientBodyPresentation_rank_lt
