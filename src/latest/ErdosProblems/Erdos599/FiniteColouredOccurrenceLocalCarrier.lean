/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.FiniteColouredOccurrenceNormalization

/-!
# The finite local carrier of one coloured-word extension

At a current vertex, a normalization move first follows the unique finite
`W` owner and then moves backwards on a `Y` owner met by that forward path.
The support of the `W` owner together with the supports of all `Y` owners
meeting it is finite.  This carrier depends only on the current word and the
two warps, not on a fixed terminal witness.
-/

noncomputable section

namespace Erdos599.Alternating.FiniteColouredOccurrenceWord

open Set DirectedPath SwitchingCore

universe u

variable {V : Type u} {Gamma : DWeb V} {W Y : Set Gamma.DPath}

/-- The finite region in which one local forward/backward extension can
live.  `coveredPathSupport` is empty when the displayed vertex is uncovered,
so the definition is total. -/
def localOwnerCarrier (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y)
    (a : V) : Set V :=
  coveredPathSupport hW a ∪
    ⋃ x ∈ coveredPathSupport hW a, coveredPathSupport hY x

theorem localOwnerCarrier_finite
    (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y)
    (hWfin : Gamma.HasFiniteCharacter W)
    (hYfin : Gamma.HasFiniteCharacter Y) (a : V) :
    (localOwnerCarrier hW hY a).Finite := by
  apply (coveredPathSupport_finite hW hWfin a).union
  exact (coveredPathSupport_finite hW hWfin a).biUnion fun x _ ↦
    coveredPathSupport_finite hY hYfin x

/-- A nontrivial finite `W` path starting at `a` lies on the unique `W`
owner through `a`. -/
theorem finiteForward_support_subset_coveredPathSupport
    (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y)
    (p : FinitePath Gamma.graph) (hne : p.start ≠ p.finish)
    (hp : p.edgeSet ⊆ familyEdges W) {a : V} (ha : a = p.start) :
    p.support ⊆ coveredPathSupport hW a := by
  obtain ⟨owner, hownerW, hpOwner⟩ :=
    finitePath_isFragmentOf_of_edgeSet_subset_familyEdges hW p hne hp
  have haOwner : a ∈ owner.support := by
    rw [ha]
    exact hpOwner.1 p.start_mem_support
  have hcovered : coveredPathSupport hW a = owner.support :=
    coveredPathSupport_eq_of_mem hW hownerW haOwner
  intro x hx
  rw [hcovered]
  exact hpOwner.1 hx

/-- The same forward support lies in the complete local owner carrier. -/
theorem finiteForward_support_subset_localOwnerCarrier
    (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y)
    (p : FinitePath Gamma.graph) (hne : p.start ≠ p.finish)
    (hp : p.edgeSet ⊆ familyEdges W) {a : V} (ha : a = p.start) :
    p.support ⊆ localOwnerCarrier hW hY a := by
  intro x hx
  exact Or.inl (finiteForward_support_subset_coveredPathSupport
    hW hY p hne hp ha hx)

/-- A finite reference owner meeting the forward-owner support is wholly
contained in the reference part of the local carrier. -/
theorem referenceOwner_support_subset_localOwnerCarrier
    (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y)
    {a x : V} (hxW : x ∈ coveredPathSupport hW a)
    (owner : FinitePath Gamma.graph)
    (hownerY : (Sum.inl owner : Gamma.DPath) ∈ Y)
    (hxOwner : x ∈ owner.support) :
    owner.support ⊆ localOwnerCarrier hW hY a := by
  intro z hz
  right
  simp only [Set.mem_iUnion]
  refine ⟨x, hxW, ?_⟩
  rw [coveredPathSupport_eq_of_mem hY hownerY hxOwner]
  exact hz

#print axioms localOwnerCarrier_finite
#print axioms finiteForward_support_subset_coveredPathSupport
#print axioms finiteForward_support_subset_localOwnerCarrier
#print axioms referenceOwner_support_subset_localOwnerCarrier

end Erdos599.Alternating.FiniteColouredOccurrenceWord
