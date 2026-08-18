/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.Bilu.Section92ShortKernel

/-!
# Integral coordinates on a primitive kernel complement

The primitive quotient step chooses an integral complement to its saturated
rank-one kernel direction.  Here that complement is identified with a
literal standard lattice and the original homomorphism is descended to it.
The resulting reduced map has one fewer source coordinate and agrees with
the original map on every point after canonical projection to the chosen
complement.

This is the discrete companion to the projected-gauge construction.
-/

namespace Erdos186.CFP.Bilu.Section92ShortKernel.PrimitiveIntegralQuotient

open Module Submodule
open Mahler

noncomputable section

variable {n : ℕ} {H : Type*} [AddCommGroup H]
  {phi : IntegralPoint n →+ H} {q : IntegralPoint n}

variable (Q : PrimitiveIntegralQuotient phi q)

/-- Integral basis coordinates on the selected complement. -/
def complementCoordinateEquiv :
    Q.complement ≃ₗ[ℤ] IntegralPoint Q.complementRank :=
  Q.complementBasis.equivFun

/-- The integral projection onto the chosen complement along the primitive
kernel direction. -/
def complementProjection :
    IntegralPoint n →ₗ[ℤ] Q.complement :=
  (LinearMap.snd ℤ (primitiveDirection q) Q.complement) ∘ₗ
    ((primitiveDirection q).prodEquivOfIsCompl Q.complement
      Q.isCompl).symm.toLinearMap

/-- Coordinates of the complement component of an original integral
point. -/
def complementCoordinates :
    IntegralPoint n →ₗ[ℤ] IntegralPoint Q.complementRank :=
  Q.complementCoordinateEquiv.toLinearMap.comp Q.complementProjection

/-- Reconstruct a complement lattice point from its standard integral
coordinates. -/
def complementLift :
    IntegralPoint Q.complementRank →ₗ[ℤ] IntegralPoint n :=
  Q.complement.subtype.comp Q.complementCoordinateEquiv.symm.toLinearMap

theorem complementLift_injective :
    Function.Injective Q.complementLift :=
  Subtype.coe_injective.comp
    Q.complementCoordinateEquiv.symm.injective

@[simp] theorem complementCoordinates_complementLift
    (z : IntegralPoint Q.complementRank) :
    Q.complementCoordinates (Q.complementLift z) = z := by
  change Q.complementCoordinateEquiv
    (((primitiveDirection q).prodEquivOfIsCompl Q.complement Q.isCompl).symm
      (Q.complementCoordinateEquiv.symm z : IntegralPoint n)).2 = z
  rw [Submodule.prodEquivOfIsCompl_symm_apply_right]
  exact Q.complementCoordinateEquiv.apply_symm_apply z

@[simp] theorem complementLift_complementCoordinates
    (x : IntegralPoint n) :
    Q.complementLift (Q.complementCoordinates x) =
      (Q.complementProjection x : IntegralPoint n) := by
  simp [complementLift, complementCoordinates,
    complementCoordinateEquiv]

/-- The original homomorphism restricted to the selected complement, in
standard integral coordinates. -/
def reducedMap : IntegralPoint Q.complementRank →+ H :=
  phi.comp Q.complementLift.toAddHom

@[simp] theorem reducedMap_apply (z : IntegralPoint Q.complementRank) :
    Q.reducedMap z = phi (Q.complementLift z) := rfl

/-- Removing the primitive-direction component does not change the value
of the original homomorphism. -/
theorem map_complementProjection (x : IntegralPoint n) :
    phi (Q.complementProjection x) = phi x := by
  let e := (primitiveDirection q).prodEquivOfIsCompl Q.complement Q.isCompl
  let d := e.symm x
  have hx : (d.1 : IntegralPoint n) + (d.2 : IntegralPoint n) = x := by
    exact e.apply_symm_apply x
  have hdir : phi (d.1 : IntegralPoint n) = 0 := by
    change (d.1 : IntegralPoint n) ∈ LinearMap.ker phi.toIntLinearMap
    exact Q.direction_le_ker d.1.property
  have hproj : Q.complementProjection x = d.2 := by
    rfl
  rw [hproj, ← hx, map_add, hdir, zero_add]

/-- The reduced map is a literal factor of the old one on every integral
point.  In particular, all source lifts survive the quotient step. -/
@[simp] theorem reducedMap_complementCoordinates
    (x : IntegralPoint n) :
    Q.reducedMap (Q.complementCoordinates x) = phi x := by
  rw [reducedMap_apply, complementLift_complementCoordinates,
    map_complementProjection]

/-- A lift through the old presentation induces a lift through the
rank-decreased presentation. -/
theorem exists_reducedLift_of_exists_lift {y : H}
    (h : ∃ x : IntegralPoint n, phi x = y) :
    ∃ z : IntegralPoint Q.complementRank, Q.reducedMap z = y := by
  obtain ⟨x, hx⟩ := h
  refine ⟨Q.complementCoordinates x, ?_⟩
  rw [reducedMap_complementCoordinates]
  exact hx

end

end Erdos186.CFP.Bilu.Section92ShortKernel.PrimitiveIntegralQuotient

#print axioms Erdos186.CFP.Bilu.Section92ShortKernel.PrimitiveIntegralQuotient.reducedMap_complementCoordinates
#print axioms Erdos186.CFP.Bilu.Section92ShortKernel.PrimitiveIntegralQuotient.exists_reducedLift_of_exists_lift
