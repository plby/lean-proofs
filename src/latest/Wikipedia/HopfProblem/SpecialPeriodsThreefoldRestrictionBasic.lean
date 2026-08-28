import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Sets.Opens

/-!
# Restricting a filling piece over an open base patch

The restricted space is the literal open inverse image of the smaller
base patch.  Its maps to the ambient base and to the smaller patch are
the actual restrictions of the original continuous projection.
-/

noncomputable section

open Set Topology TopologicalSpace

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Restriction

variable {B X : Type*} [TopologicalSpace B] [TopologicalSpace X]

/-- The actual open inverse image of a smaller base patch. -/
def restrictedPiece (p : C(X, B)) (V : Opens B) : Opens X :=
  ⟨p ⁻¹' (V : Set B), V.isOpen.preimage p.continuous⟩

@[simp] theorem mem_restrictedPiece (p : C(X, B)) (V : Opens B) (x : X) :
    x ∈ restrictedPiece p V ↔ p x ∈ V := Iff.rfl

/-- Projection of the restricted piece to the ambient base. -/
def restrictedProjection (p : C(X, B)) (V : Opens B) : C(restrictedPiece p V, B) where
  toFun x := p x.val
  continuous_toFun := p.continuous.comp continuous_subtype_val

@[simp] theorem restrictedProjection_apply (p : C(X, B)) (V : Opens B)
    (x : restrictedPiece p V) : restrictedProjection p V x = p x.val := rfl

theorem restrictedProjection_mem (p : C(X, B)) (V : Opens B)
    (x : restrictedPiece p V) : restrictedProjection p V x ∈ V := x.property

/-- Projection of the restricted piece to its own base patch. -/
def localProjection (p : C(X, B)) (V : Opens B) : C(restrictedPiece p V, V) where
  toFun x := ⟨p x.val, x.property⟩
  continuous_toFun := (p.continuous.comp continuous_subtype_val).subtype_mk _

@[simp] theorem localProjection_apply_coe (p : C(X, B)) (V : Opens B)
    (x : restrictedPiece p V) : (localProjection p V x : B) = p x.val := rfl

/-- The original projection viewed in a base patch containing its image. -/
def patchProjection (p : C(X, B)) (U : Opens B) (hpU : ∀ x, p x ∈ U) : C(X, U) where
  toFun x := ⟨p x, hpU x⟩
  continuous_toFun := p.continuous.subtype_mk _

@[simp] theorem patchProjection_apply_coe (p : C(X, B)) (U : Opens B)
    (hpU : ∀ x, p x ∈ U) (x : X) : (patchProjection p U hpU x : B) = p x := rfl

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Restriction
