/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.Bilu.Section93LatticeSectionCoordinates
import ErdosProblems.Erdos186.CFP.Bilu.MinkowskiSecond

/-!
# Volume in saturated lattice-section coordinates

The basis selected in `Section93LatticeSectionCoordinates` is a basis of
the full intersection lattice.  Consequently pulling a section body back
to literal standard coordinates divides its intrinsic Haar volume by the
covolume of that intersection lattice, with no hidden lattice index.
-/

namespace Erdos186.CFP.Bilu.Section93LatticeSectionVolume

open Set Module Submodule MeasureTheory
open Mahler MinkowskiSecond SubspaceLattice Proposition75Case2Construction
open Section93LatticeSectionCoordinates

noncomputable section

set_option autoImplicit false

variable {n : ℕ}

/-- The restriction of an ambient seminorm to a real subspace. -/
def subspaceSeminorm
    (L : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (p : Seminorm ℝ (EuclideanSpace ℝ (Fin n))) :
    Seminorm ℝ L :=
  p.comp L.subtype

/-- The coordinate unit ball is exactly the image of the intrinsic
section unit ball under the chosen full-lattice basis coordinates. -/
theorem unitBall_coordinateSeminorm_eq_image
    (L : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (hproper : L ≠ ⊤)
    (hspan : Submodule.span ℝ
      ((integralPoints L : Submodule ℤ L) : Set L) = ⊤)
    (p : Seminorm ℝ (EuclideanSpace ℝ (Fin n))) :
    {x | coordinateSeminorm L hproper hspan p x ≤ 1} =
      (realBasis L hproper hspan).equivFun ''
        {x : L | subspaceSeminorm L p x ≤ 1} := by
  ext x
  constructor
  · intro hx
    refine ⟨(realBasis L hproper hspan).equivFun.symm x, ?_, ?_⟩
    · exact hx
    · exact (realBasis L hproper hspan).equivFun.apply_symm_apply x
  · rintro ⟨y, hy, rfl⟩
    change p
      ((realBasis L hproper hspan).equivFun.symm
        ((realBasis L hproper hspan).equivFun y) : L) ≤ 1
    rw [(realBasis L hproper hspan).equivFun.symm_apply_apply]
    exact hy

/-- Exact covolume-normalized volume formula for the coordinate section
unit ball. -/
theorem volume_unitBall_coordinateSeminorm
    (L : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (hproper : L ≠ ⊤)
    (hspan : Submodule.span ℝ
      ((integralPoints L : Submodule ℤ L) : Set L) = ⊤)
    (p : Seminorm ℝ (EuclideanSpace ℝ (Fin n))) :
    volume {x | coordinateSeminorm L hproper hspan p x ≤ 1} =
      volume {x : L | subspaceSeminorm L p x ≤ 1} /
        ENNReal.ofReal (ZLattice.covolume (integralPoints L)) := by
  classical
  let : DiscreteTopology (integralPoints L) := by
    obtain ⟨s, P, hSat⟩ := exists_saturatedPresentation L hproper hspan
    let hdiscRow : DiscreteTopology P.rowLattice := by
      change DiscreteTopology (Submodule.span ℤ (Set.range P.rowBasis))
      infer_instance
    exact hSat ▸ hdiscRow
  let : IsZLattice ℝ (integralPoints L) := ⟨hspan⟩
  have hpcont : Continuous p := by
    let q : Seminorm ℝ (Fin n → ℝ) :=
      p.comp (EuclideanSpace.equiv (Fin n) ℝ).symm.toLinearMap
    have hq : Continuous q := continuous_seminorm q
    have he : Continuous (EuclideanSpace.equiv (Fin n) ℝ) :=
      (EuclideanSpace.equiv (Fin n) ℝ).continuous
    convert hq.comp he using 1
    funext x
    exact congrArg p ((EuclideanSpace.equiv (Fin n) ℝ).symm_apply_apply x)
  have hsubcont : Continuous (subspaceSeminorm L p) :=
    hpcont.comp continuous_subtype_val
  have hclosed : IsClosed {x : L | subspaceSeminorm L p x ≤ 1} :=
    isClosed_le hsubcont continuous_const
  have h := ZLattice.volume_image_eq_volume_div_covolume'
    (integralPoints L) (integralBasis L hproper hspan)
    hclosed.measurableSet.nullMeasurableSet
  rw [unitBall_coordinateSeminorm_eq_image L hproper hspan p]
  simpa only [show (integralBasis L hproper hspan).ofZLatticeBasis ℝ
      (integralPoints L) = realBasis L hproper hspan by rfl] using h

/-- A full intersection lattice of a proper rational subspace of the
standard integral lattice has Euclidean covolume at least one. -/
theorem one_le_covolume_integralPoints
    (L : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (hproper : L ≠ ⊤)
    (hspan : Submodule.span ℝ
      ((integralPoints L : Submodule ℤ L) : Set L) = ⊤) :
    (1 : ℝ) ≤ ZLattice.covolume (integralPoints L) := by
  obtain ⟨r, P, hSat⟩ := exists_saturatedPresentation L hproper hspan
  obtain ⟨x, hx0, _hxnormal, hxbound⟩ :=
    P.exists_integral_normal_abs_le_integralPoints_covolume hSat
  obtain ⟨j, hxj⟩ : ∃ j, x j ≠ 0 := by
    by_contra h
    push_neg at h
    exact hx0 (funext h)
  have habsInt : (1 : ℤ) ≤ |x j| := by
    have : (0 : ℤ) < |x j| := abs_pos.mpr hxj
    omega
  have habsReal : (1 : ℝ) ≤ ((|x j| : ℤ) : ℝ) := by
    exact_mod_cast habsInt
  exact habsReal.trans (hxbound j)

end

end Erdos186.CFP.Bilu.Section93LatticeSectionVolume

#print axioms
  Erdos186.CFP.Bilu.Section93LatticeSectionVolume.volume_unitBall_coordinateSeminorm
#print axioms
  Erdos186.CFP.Bilu.Section93LatticeSectionVolume.one_le_covolume_integralPoints
