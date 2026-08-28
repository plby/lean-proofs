import Mathlib.Topology.Constructions
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Topology.Maps.OpenQuotient

/-!
# The actual topological quotient by an involution

Two points are equivalent precisely when they are equal or swapped by the
given involution. The quotient has its quotient topology. For a continuous
involution its projection is an open quotient map, since saturation of an
open set is its union with the inverse image under the involution.
-/

open Set Function Topology

namespace NoExoticSixSphere.InvolutionQuotient

variable {X : Type*}

def orbitSetoid (σ : X → X) (hσ : Involutive σ) : Setoid X where
  r x y := x = y ∨ σ x = y
  iseqv := ⟨fun _ ↦ Or.inl rfl, by
    intro x y h
    rcases h with h | h
    · exact Or.inl h.symm
    · exact Or.inr ((congrArg σ h).symm.trans (hσ x)), by
    intro x y z hxy hyz
    rcases hxy with rfl | hxy
    · exact hyz
    rcases hyz with rfl | hyz
    · exact Or.inr hxy
    · exact Or.inl ((hσ x).symm.trans ((congrArg σ hxy).trans hyz))⟩

abbrev Orbit (σ : X → X) (hσ : Involutive σ) := Quotient (orbitSetoid σ hσ)

def proj (σ : X → X) (hσ : Involutive σ) (x : X) : Orbit σ hσ := Quotient.mk _ x

theorem proj_eq_iff (σ : X → X) (hσ : Involutive σ) (x y : X) :
    proj σ hσ x = proj σ hσ y ↔ x = y ∨ σ x = y := Quotient.eq

theorem proj_swap (σ : X → X) (hσ : Involutive σ) (x : X) :
    proj σ hσ (σ x) = proj σ hσ x :=
  (proj_eq_iff σ hσ (σ x) x).mpr (Or.inr (hσ x))

variable [TopologicalSpace X]

theorem continuous_proj (σ : X → X) (hσ : Involutive σ) : Continuous (proj σ hσ) :=
  continuous_quotient_mk'

omit [TopologicalSpace X] in
theorem preimage_image_proj (σ : X → X) (hσ : Involutive σ) (S : Set X) :
    proj σ hσ ⁻¹' (proj σ hσ '' S) = S ∪ σ ⁻¹' S := by
  ext x
  constructor
  · rintro ⟨y, hy, he⟩
    rcases (proj_eq_iff σ hσ y x).mp he with rfl | he
    · exact Or.inl hy
    · right
      change σ x ∈ S
      rw [← he, hσ]
      exact hy
  · rintro (hx | hx)
    · exact ⟨x, hx, rfl⟩
    · exact ⟨σ x, hx, proj_swap σ hσ x⟩

theorem isOpenQuotientMap_proj (σ : X → X) (hσ : Involutive σ) (hc : Continuous σ) :
    IsOpenQuotientMap (proj σ hσ) := by
  refine ⟨Quotient.mk_surjective, continuous_proj σ hσ, ?_⟩
  intro S hS
  apply isQuotientMap_quotient_mk'.isOpen_preimage.mp
  change IsOpen (proj σ hσ ⁻¹' (proj σ hσ '' S))
  rw [preimage_image_proj]
  exact hS.union (hS.preimage hc)

end NoExoticSixSphere.InvolutionQuotient
