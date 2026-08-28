import Mathlib.Topology.ContinuousMap.Basic

/-!
# The literal topological quotient collapsing a subspace

The relation identifies equal points and all pairs in the specified set.
The topology is the quotient topology, without compactness assumptions.
Continuous maps constant on the specified set descend through this quotient.
-/

noncomputable section

open Topology

namespace NoExoticSixSphere.CollapsedSubspace

variable {X : Type*} (A : Set X)

def relation : Setoid X where
  r x y := x = y ∨ (x ∈ A ∧ y ∈ A)
  iseqv := {
    refl := fun _ ↦ Or.inl rfl
    symm := by
      rintro x y (h | ⟨hx, hy⟩)
      · exact Or.inl h.symm
      · exact Or.inr ⟨hy, hx⟩
    trans := by
      rintro x y z (rfl | ⟨hx, hy⟩) hyz
      · exact hyz
      · rcases hyz with rfl | ⟨_, hz⟩
        · exact Or.inr ⟨hx, hy⟩
        · exact Or.inr ⟨hx, hz⟩ }

abbrev Space := Quotient (relation A)

variable [TopologicalSpace X]

def quotientMap : C(X, Space A) :=
  ⟨Quotient.mk (relation A), continuous_quotient_mk' (s := relation A)⟩

theorem quotientMap_eq_iff (x y : X) :
    quotientMap A x = quotientMap A y ↔ x = y ∨ (x ∈ A ∧ y ∈ A) := Quotient.eq

theorem isQuotientMap : IsQuotientMap (quotientMap A) := isQuotientMap_quotient_mk'

variable {Y : Type*} [TopologicalSpace Y] (f : C(X, Y))
    (hf : ∀ x ∈ A, ∀ y ∈ A, f x = f y)

def lift : C(Space A, Y) :=
  ⟨Quotient.lift f (by
      rintro x y (rfl | ⟨hx, hy⟩)
      · rfl
      · exact hf x hx y hy),
    f.continuous.quotient_lift (by
      rintro x y (rfl | ⟨hx, hy⟩)
      · rfl
      · exact hf x hx y hy)⟩

theorem lift_quotientMap (x : X) : lift A f hf (quotientMap A x) = f x := rfl

end NoExoticSixSphere.CollapsedSubspace
