import Wikipedia.NoExoticSixSphere.EndingPathSpace
import Wikipedia.NoExoticSixSphere.HomotopyFiberStrongContraction

/-!
# Restricting the genuine path projection to a subspace

The inverse image of a subspace under evaluation at zero is homeomorphic
to the actual homotopy fiber of its inclusion. A strong contraction of
that subspace to the terminal point therefore gives a homotopy equivalence
with the native loop space, whose inverse is the literal loop inclusion.
-/

noncomputable section

open scoped unitInterval ContinuousMap
open Wikipedia.HopfProblem.OrbitPair

namespace NoExoticSixSphere.EndingPath

variable {Y : Type*} [TopologicalSpace Y]

def inclusion (U : Set Y) : C(U, Y) := ⟨Subtype.val, continuous_subtype_val⟩

def restriction (y₀ : Y) (U : Set Y) : Set (Space y₀) := (source y₀) ⁻¹' U

theorem restriction_isOpen (y₀ : Y) {U : Set Y} (hU : IsOpen U) :
    IsOpen (restriction y₀ U) := hU.preimage (source y₀).continuous

theorem restriction_cover (y₀ : Y) {U V : Set Y} (h : U ∪ V = Set.univ) :
    restriction y₀ U ∪ restriction y₀ V = Set.univ := by
  change (source y₀) ⁻¹' U ∪ (source y₀) ⁻¹' V = Set.univ
  rw [← Set.preimage_union, h, Set.preimage_univ]

def restrictionHomeomorph (y₀ : Y) (U : Set Y) :
    restriction y₀ U ≃ₜ HomotopyFiber.Space (inclusion U) y₀ where
  toFun p := ⟨(⟨source y₀ p.val, p.property⟩, p.val.val), rfl, p.val.property⟩
  invFun p := ⟨⟨p.val.2, p.property.2⟩,
    show p.val.2 0 ∈ U from p.property.1.symm ▸ p.val.1.property⟩
  left_inv _ := rfl
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      exact p.property.1
    · rfl
  continuous_toFun :=
    (((source y₀).continuous.comp continuous_subtype_val).subtype_mk _ |>.prodMk
      (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk _
  continuous_invFun :=
    ((continuous_snd.comp continuous_subtype_val).subtype_mk _).subtype_mk _

def restrictionEquiv (y₀ : Y) (U : Set Y) (hy : y₀ ∈ U)
    (H : (ContinuousMap.id U).HomotopyRel
      (ContinuousMap.const U ⟨y₀, hy⟩) {⟨y₀, hy⟩}) :
    restriction y₀ U ≃ₕ Path y₀ y₀ :=
  (restrictionHomeomorph y₀ U).toHomotopyEquiv.trans
    (HomotopyFiberStrongContraction.equivalence (inclusion U) ⟨y₀, hy⟩ H)

theorem restrictionEquiv_symm_val (y₀ : Y) (U : Set Y) (hy : y₀ ∈ U)
    (H : (ContinuousMap.id U).HomotopyRel
      (ContinuousMap.const U ⟨y₀, hy⟩) {⟨y₀, hy⟩}) (p : Path y₀ y₀) :
    ((restrictionEquiv y₀ U hy H).symm p).val = ofPath p := rfl

end NoExoticSixSphere.EndingPath
