import Wikipedia.NoExoticSixSphere.UnorderedFamilyDoublePoints
import Mathlib.Topology.Order.Compact

/-!
# Actual time windows in the unordered double-point closure

Time is invariant under swapping the sheets, so it descends continuously
to the original orbit quotient. Its closed bounded windows are compact
for compact source, without injectivity of any exterior-time slice.
-/

noncomputable section

open Set Function Topology

namespace NoExoticSixSphere.FamilyEmbedding

variable {E F : Type*} [TopologicalSpace E] (f : ℝ → E → F)

def unorderedTime : C(UnorderedClosedDoublePoints f, ℝ) where
  toFun := Quotient.lift (fun a : closure (doublePoints f) ↦ a.val.1) (by
    intro a b hab
    rcases hab with hab | hab
    · exact congrArg (fun a : closure (doublePoints f) ↦ a.val.1) hab
    · have he := congrArg (fun a : closure (doublePoints f) ↦ a.val.1) hab
      exact he)
  continuous_toFun := continuous_subtype_val.fst.quotient_lift _

theorem unorderedTime_proj (a : closure (doublePoints f)) :
    unorderedTime f (unorderedProj f a) = a.val.1 := rfl

def orderedWindow (u v : ℝ) : Set (ℝ × (E × E)) :=
  closure (doublePoints f) ∩ (Icc u v ×ˢ univ)

def unorderedWindow (u v : ℝ) : Set (UnorderedClosedDoublePoints f) :=
  unorderedTime f ⁻¹' Icc u v

theorem isClosed_unorderedWindow (u v : ℝ) : IsClosed (unorderedWindow f u v) :=
  isClosed_Icc.preimage (unorderedTime f).continuous

variable [CompactSpace E]

theorem isCompact_orderedWindow (u v : ℝ) : IsCompact (orderedWindow f u v) :=
  (isCompact_Icc.prod isCompact_univ).inter_left isClosed_closure

theorem isCompact_unorderedWindow (u v : ℝ) : IsCompact (unorderedWindow f u v) := by
  let : CompactSpace (orderedWindow f u v) :=
    isCompact_iff_compactSpace.mp (isCompact_orderedWindow f u v)
  let j : orderedWindow f u v → closure (doublePoints f) := fun a ↦ ⟨a.val, a.property.1⟩
  have hj : Continuous j := continuous_subtype_val.subtype_mk _
  have hc := (isOpenQuotientMap_unorderedProj f).continuous.comp hj
  have he : range (unorderedProj f ∘ j) = unorderedWindow f u v := by
    ext q
    constructor
    · rintro ⟨a, rfl⟩
      exact a.property.2.1
    · intro hq
      obtain ⟨a, rfl⟩ := (isOpenQuotientMap_unorderedProj f).surjective q
      exact ⟨⟨a.val, a.property, hq, mem_univ _⟩, rfl⟩
  rw [← he]
  exact isCompact_range hc

end NoExoticSixSphere.FamilyEmbedding
