/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.Bilu.Section93LatticeSectionCoordinates

/-!
# Full integral families in lattice-section coordinates

A finite family of ambient integral points which spans a rational section
and lies in an ambient seminorm unit ball gives a full independent integral
family in the saturated coordinates of that section.
-/

namespace Erdos186.CFP.Bilu.Section93LatticeSectionFullness

open Set Module Submodule
open Mahler SubspaceLattice
open Proposition75Case2Construction
open Section93LatticeSectionCoordinates

noncomputable section

set_option autoImplicit false

variable {n : ℕ}

/-- Integral coordinates of an ambient integral point lying in the
section. -/
noncomputable def integralCoordinatesOfMem
    (L : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (hproper : L ≠ ⊤)
    (hspan : Submodule.span ℝ
      ((integralPoints L : Submodule ℤ L) : Set L) = ⊤)
    (z : IntegralPoint n) (hz : integralReal z ∈ L) :
    IntegralPoint (finrank ℝ L) :=
  (integralBasis L hproper hspan).equivFun
    (integralCoordinateEquiv L ⟨z, hz⟩)

theorem coordinateIntegralEmbedding_integralCoordinatesOfMem
    (L : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (hproper : L ≠ ⊤)
    (hspan : Submodule.span ℝ
      ((integralPoints L : Submodule ℤ L) : Set L) = ⊤)
    (z : IntegralPoint n) (hz : integralReal z ∈ L) :
    coordinateIntegralEmbedding L hproper hspan
        (integralCoordinatesOfMem L hproper hspan z hz) = z := by
  change (((integralCoordinateEquiv L).symm
      ((integralBasis L hproper hspan).equivFun.symm
        ((integralBasis L hproper hspan).equivFun
          (integralCoordinateEquiv L ⟨z, hz⟩))) :
        integralCoordinateLattice L) : Fin n → ℤ) = z
  rw [(integralBasis L hproper hspan).equivFun.symm_apply_apply,
    (integralCoordinateEquiv L).symm_apply_apply]

theorem coordinateEmbedding_integralCoordinatesOfMem
    (L : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (hproper : L ≠ ⊤)
    (hspan : Submodule.span ℝ
      ((integralPoints L : Submodule ℤ L) : Set L) = ⊤)
    (z : IntegralPoint n) (hz : integralReal z ∈ L) :
    coordinateEmbedding L hproper hspan
        (integralEmbed (integralCoordinatesOfMem L hproper hspan z hz)) =
      integralReal z := by
  rw [← integralReal_coordinateIntegralEmbedding]
  congr 1
  exact coordinateIntegralEmbedding_integralCoordinatesOfMem
    L hproper hspan z hz

/-- A spanning finite family in the ambient unit ball gives a full family
in saturated section coordinates. -/
theorem coordinateSeminorm_admitsIndependent_of_span
    (L : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (hproper : L ≠ ⊤)
    (hspan : Submodule.span ℝ
      ((integralPoints L : Submodule ℤ L) : Set L) = ⊤)
    (p : Seminorm ℝ (EuclideanSpace ℝ (Fin n)))
    (K : Finset (IntegralPoint n))
    (hL : L = Submodule.span ℝ ((K.image integralReal : Finset _) : Set _))
    (hunit : ∀ z ∈ K, p (integralReal z) ≤ 1) :
    AdmitsIndependent (coordinateSeminorm L hproper hspan p)
      (finrank ℝ L) 1 := by
  classical
  have hKmem : ∀ z : K, integralReal z.1 ∈ L := by
    intro z
    rw [hL]
    exact Submodule.subset_span (by
      exact Finset.mem_coe.mpr (Finset.mem_image.mpr
        ⟨z.1, z.2, rfl⟩))
  let u : K → IntegralPoint (finrank ℝ L) := fun z ↦
    integralCoordinatesOfMem L hproper hspan z.1 (hKmem z)
  let w : K → (Fin (finrank ℝ L) → ℝ) :=
    fun z ↦ integralEmbed (u z)
  let F := coordinateEmbedding L hproper hspan
  have hF_injective : Function.Injective F := by
    intro x y hxy
    apply (realBasis L hproper hspan).equivFun.symm.injective
    apply L.injective_subtype
    exact hxy
  have hmapTop : Submodule.map F ⊤ = L := by
    ext x
    constructor
    · rintro ⟨y, _hy, rfl⟩
      exact ((realBasis L hproper hspan).equivFun.symm y).property
    · intro hx
      let xL : L := ⟨x, hx⟩
      refine ⟨(realBasis L hproper hspan).equivFun xL, trivial, ?_⟩
      exact congrArg Subtype.val
        ((realBasis L hproper hspan).equivFun.symm_apply_apply xL)
  have hFw : ∀ z : K, F (w z) = integralReal z.1 := by
    intro z
    exact coordinateEmbedding_integralCoordinatesOfMem
      L hproper hspan z.1 (hKmem z)
  have hspanW : Submodule.span ℝ (Set.range w) = ⊤ := by
    apply (Submodule.map_injective_of_injective hF_injective)
    calc
      Submodule.map F (Submodule.span ℝ (Set.range w)) =
          Submodule.span ℝ (F '' Set.range w) :=
        Submodule.map_span F (Set.range w)
      _ = Submodule.span ℝ
          ((K.image integralReal : Finset _) : Set _) := by
        congr 1
        ext x
        constructor
        · rintro ⟨_, ⟨z, rfl⟩, rfl⟩
          rw [hFw z]
          exact Finset.mem_coe.mpr
            (Finset.mem_image.mpr ⟨z.1, z.2, rfl⟩)
        · intro hx
          obtain ⟨z, hzK, rfl⟩ :=
            Finset.mem_image.mp (Finset.mem_coe.mp hx)
          let zK : K := ⟨z, hzK⟩
          exact ⟨w zK, ⟨zK, rfl⟩, hFw zK⟩
      _ = L := hL.symm
      _ = Submodule.map F ⊤ := hmapTop.symm
  obtain ⟨f, hfRange, _hfSpan, hfli⟩ :=
    Submodule.exists_fun_fin_finrank_span_eq ℝ (Set.range w)
  have hdim : finrank ℝ (Submodule.span ℝ (Set.range w)) =
      finrank ℝ L := by rw [hspanW]; simp
  let e : Fin (finrank ℝ L) ≃
      Fin (finrank ℝ (Submodule.span ℝ (Set.range w))) :=
    finCongr hdim.symm
  choose g hg using fun i ↦ hfRange (e i)
  refine ⟨fun i ↦ u (g i), ?_, ?_⟩
  · have hu : (fun i ↦ integralEmbed (u (g i))) =
        fun i ↦ f (e i) := by
      funext i
      exact hg i
    rw [hu]
    exact hfli.comp e e.injective
  · intro i
    change p (F (integralEmbed (u (g i)))) ≤ 1
    rw [hFw (g i)]
    exact hunit (g i).1 (g i).2

end

end Erdos186.CFP.Bilu.Section93LatticeSectionFullness

#print axioms
  Erdos186.CFP.Bilu.Section93LatticeSectionFullness.coordinateSeminorm_admitsIndependent_of_span
