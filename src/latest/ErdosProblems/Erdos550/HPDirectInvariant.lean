import Mathlib
import ErdosProblems.Erdos550.HPMatchingState

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Global invariant for the direct parity-refined matching embedding

The state records the four facts used in the two local extension cases:
processed seeds lie in their head cores, parents of deferred seeds are
retained in a set typical back to the correct head, processed nonseeds remain
inside the matching region, and every matching edge satisfies the
Hladký--Piguet packedness dichotomy.
-/

open Finset

namespace Erdos550

def HPDirectInvariant
    {A V κ : Type*} [DecidableEq A] [DecidableEq V]
    (Sseed : Finset A) (parent : A → Option A)
    (col routeColour : A → Bool)
    (headCore retained : Bool → Finset V)
    (matchingRegion : Bool → Finset V)
    (CLeft CRight : κ → Finset V)
    (leftThreshold rightThreshold : κ → ℝ)
    (margin τ : ℝ)
    (P : Finset A) (f : A → V) : Prop :=
  (∀ s ∈ P, s ∈ Sseed → f s ∈ headCore (col s)) ∧
  (∀ s ∈ Sseed, ∀ x ∈ P, x ∉ Sseed →
    parent s = some x → f x ∈ retained (col s)) ∧
  (∀ x ∈ P, x ∉ Sseed → f x ∈ matchingRegion (routeColour x)) ∧
  HPMatchingPacked P f CLeft CRight
    leftThreshold rightThreshold margin τ

lemma hpDirectInvariant_empty
    {A V κ : Type*} [DecidableEq A] [DecidableEq V]
    (Sseed : Finset A) (parent : A → Option A)
    (col routeColour : A → Bool)
    (headCore retained : Bool → Finset V)
    (matchingRegion : Bool → Finset V)
    (CLeft CRight : κ → Finset V)
    (leftThreshold rightThreshold : κ → ℝ)
    (margin τ : ℝ) (hτ : 0 ≤ τ)
    (f : A → V) :
    HPDirectInvariant Sseed parent col routeColour headCore retained matchingRegion
      CLeft CRight leftThreshold rightThreshold margin τ ∅ f := by
  refine ⟨?_, ?_, ?_, hpMatchingPacked_empty f CLeft CRight
    leftThreshold rightThreshold margin τ hτ⟩ <;> simp

/-- Gluing a seed singleton in its head core preserves the direct invariant
when head cores are disjoint from all matching clusters. -/
lemma hpDirectInvariant_seed_glue
    {A V κ : Type*} [DecidableEq A] [DecidableEq V]
    (Sseed : Finset A) (parent : A → Option A)
    (col routeColour : A → Bool)
    (headCore retained : Bool → Finset V)
    (matchingRegion : Bool → Finset V)
    (CLeft CRight : κ → Finset V)
    (leftThreshold rightThreshold : κ → ℝ)
    (margin τ : ℝ)
    (P : Finset A) (f g : A → V) (a : A)
    (hInv : HPDirectInvariant Sseed parent col routeColour headCore retained matchingRegion
      CLeft CRight leftThreshold rightThreshold margin τ P f)
    (haSeed : a ∈ Sseed)
    (hga : g a ∈ headCore (col a))
    (hBP : Disjoint ({a} : Finset A) P)
    (himg : Disjoint (({a} : Finset A).image g) (P.image f))
    (hleft : ∀ k, Disjoint (({a} : Finset A).image g) (CLeft k))
    (hright : ∀ k, Disjoint (({a} : Finset A).image g) (CRight k)) :
    HPDirectInvariant Sseed parent col routeColour headCore retained matchingRegion
      CLeft CRight leftThreshold rightThreshold margin τ
      (P ∪ {a}) (glueOnBlock {a} f g) := by
  refine ⟨?_, ?_, ?_,
    hpMatchingPacked_glue_outside P {a} f g CLeft CRight
      leftThreshold rightThreshold margin τ hInv.2.2.2
      hBP himg hleft hright⟩
  · intro s hsP hsSeed
    rcases Finset.mem_union.mp hsP with hsOld | hsNew
    · have hsa : s ≠ a := by
        intro h
        subst s
        exact Finset.disjoint_left.mp hBP
          (Finset.mem_singleton_self a) hsOld
      simpa [glueOnBlock, hsa] using! hInv.1 s hsOld hsSeed
    · have hsa : s = a := Finset.mem_singleton.mp hsNew
      subst s
      simpa [glueOnBlock] using! hga
  · intro s hsSeed x hxP hxNotSeed hsx
    rcases Finset.mem_union.mp hxP with hxOld | hxNew
    · have hxa : x ≠ a := by
        intro h
        subst x
        exact Finset.disjoint_left.mp hBP
          (Finset.mem_singleton_self a) hxOld
      simpa [glueOnBlock, hxa] using!
        hInv.2.1 s hsSeed x hxOld hxNotSeed hsx
    · have hxa : x = a := Finset.mem_singleton.mp hxNew
      subst x
      exact False.elim (hxNotSeed haSeed)
  · intro x hxP hxNotSeed
    rcases Finset.mem_union.mp hxP with hxOld | hxNew
    · have hxa : x ≠ a := by
        intro h
        subst x
        exact Finset.disjoint_left.mp hBP
          (Finset.mem_singleton_self a) hxOld
      simpa [glueOnBlock, hxa] using! hInv.2.2.1 x hxOld hxNotSeed
    · have hxa : x = a := Finset.mem_singleton.mp hxNew
      subst x
      exact False.elim (hxNotSeed haSeed)

/-- Gluing a nonseed component preserves the head-core and deferred-contact
parts of the invariant; the caller supplies the exact packedness update proved
from the component's two image cardinalities. -/
lemma hpDirectInvariant_component_glue
    {A V κ : Type*} [DecidableEq A] [DecidableEq V]
    (Sseed : Finset A) (parent : A → Option A)
    (col routeColour : A → Bool)
    (headCore retained : Bool → Finset V)
    (matchingRegion : Bool → Finset V)
    (CLeft CRight : κ → Finset V)
    (leftThreshold rightThreshold : κ → ℝ)
    (margin τ : ℝ)
    (P B : Finset A) (f g : A → V)
    (hInv : HPDirectInvariant Sseed parent col routeColour headCore retained matchingRegion
      CLeft CRight leftThreshold rightThreshold margin τ P f)
    (hBP : Disjoint B P)
    (hBSeed : Disjoint B Sseed)
    (hcontact : ∀ s ∈ Sseed, ∀ x ∈ B,
      parent s = some x → g x ∈ retained (col s))
    (hregion : ∀ x ∈ B, g x ∈ matchingRegion (routeColour x))
    (hpackedNew :
      HPMatchingPacked (P ∪ B) (glueOnBlock B f g)
        CLeft CRight leftThreshold rightThreshold margin τ) :
    HPDirectInvariant Sseed parent col routeColour headCore retained matchingRegion
      CLeft CRight leftThreshold rightThreshold margin τ
      (P ∪ B) (glueOnBlock B f g) := by
  refine ⟨?_, ?_, ?_, hpackedNew⟩
  · intro s hsP hsSeed
    rcases Finset.mem_union.mp hsP with hsOld | hsB
    · have hsNotB : s ∉ B := by
        intro hsB
        exact Finset.disjoint_left.mp hBP hsB hsOld
      simpa [glueOnBlock, hsNotB] using! hInv.1 s hsOld hsSeed
    · exact False.elim
        (Finset.disjoint_left.mp hBSeed hsB hsSeed)
  · intro s hsSeed x hxP hxNotSeed hsx
    rcases Finset.mem_union.mp hxP with hxOld | hxB
    · have hxNotB : x ∉ B := by
        intro hxB
        exact Finset.disjoint_left.mp hBP hxB hxOld
      simpa [glueOnBlock, hxNotB] using!
        hInv.2.1 s hsSeed x hxOld hxNotSeed hsx
    · have hxg := hcontact s hsSeed x hxB hsx
      simpa [glueOnBlock, hxB] using! hxg
  · intro x hxP hxNotSeed
    rcases Finset.mem_union.mp hxP with hxOld | hxB
    · have hxNotB : x ∉ B := by
        intro hxB
        exact Finset.disjoint_left.mp hBP hxB hxOld
      simpa [glueOnBlock, hxNotB] using!
        hInv.2.2.1 x hxOld hxNotSeed
    · simpa [glueOnBlock, hxB] using! hregion x hxB

end Erdos550
